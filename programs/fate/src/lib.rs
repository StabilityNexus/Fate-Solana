use anchor_lang::prelude::*;
use anchor_spl::{
    associated_token::AssociatedToken,
    token::{ self, Burn, Mint, MintTo, Token, TokenAccount, Transfer },
};
use std::str::FromStr;

// -------------------------------------------------------------------------------------
// Minimal Chainlink feed reader (no external crate, BPF-safe)
// -------------------------------------------------------------------------------------
//
// What this does:
// - Reads the on-chain Chainlink OCR2 feed account
// - Verifies it's actually owned by the official Chainlink program
// - Parses the latest round's answer + decimals
// - Gives you a scaled u64 price
//
// We inline it so we don't depend on `chainlink_solana` (which drags in crates that
// pull `getrandom`, which the BPF target cannot compile).

mod chainlink {
    use anchor_lang::prelude::Pubkey;
    use borsh::{ BorshDeserialize, BorshSerialize };
    use bytemuck::pod_read_unaligned;
    use std::{ cell::Ref, convert::TryInto, fmt, mem::size_of };

    // This is the official Chainlink OCR2 program ID ("HEvSKofvBgfaexv23kMabbYqxasxU3mQ4ibBMEmJWHny")
    //
    // We'll compare the feed account's owner to this byte array on-chain to make sure
    // nobody passes in a fake account.
    //
    // Decoded from base58 -> 32 bytes:
    // hex: f1 4b f6 5a d5 6b d2 ba 71 5e 45 74 2c 23 1f 27
    //      d6 36 21 cf 5b 77 8f 37 c1 a2 48 95 1d 17 56 02
    const CHAINLINK_PROGRAM_ID_BYTES: [u8; 32] = [
        0xf1, 0x4b, 0xf6, 0x5a, 0xd5, 0x6b, 0xd2, 0xba, 0x71, 0x5e, 0x45, 0x74, 0x2c, 0x23, 0x1f, 0x27,
        0xd6, 0x36, 0x21, 0xcf, 0x5b, 0x77, 0x8f, 0x37, 0xc1, 0xa2, 0x48, 0x95, 0x1d, 0x17, 0x56, 0x02,
    ];

    // 8-byte discriminator at the start of every Chainlink "transmissions" account
    const TRANSMISSIONS_DISCRIMINATOR: [u8; 8] = [96, 179, 69, 66, 128, 129, 73, 117];

    // Size of the "Transmissions" header struct below (after discriminator)
    const HEADER_SIZE: usize = 192;

    // == Account header ==
    #[derive(BorshSerialize, BorshDeserialize, Clone)]
    pub(crate) struct Transmissions {
        pub(crate) version: u8,
        pub(crate) state: u8,
        pub(crate) owner: Pubkey,
        pub(crate) proposed_owner: Pubkey,
        pub(crate) writer: Pubkey,
        pub(crate) description: [u8; 32],
        pub(crate) decimals: u8,
        pub(crate) flagging_threshold: u32,
        pub(crate) latest_round_id: u32,
        pub(crate) granularity: u8,
        pub(crate) live_length: u32,
        pub(crate) live_cursor: u32,
        pub(crate) historical_cursor: u32,
    }

    // == Individual transmission ==
    // Layout taken from Chainlink OCR2 feed account; this is POD/zeroable.
    #[repr(C)]
    #[derive(
        Debug,
        Default,
        Clone,
        Copy,
        PartialEq,
        Eq,
        PartialOrd,
        Ord,
        bytemuck::Pod,
        bytemuck::Zeroable
    )]
    pub(crate) struct Transmission {
        pub(crate) slot: u64,
        pub(crate) timestamp: u32,
        pub(crate) _padding0: u32,
        pub(crate) answer: i128,
        pub(crate) _padding1: u64,
        pub(crate) _padding2: u64,
    }

    pub mod v2 {
        use super::*;
        use std::result::Result as StdResult;

        /// human-friendly view of a round
        #[derive(BorshSerialize, BorshDeserialize)]
        pub struct Round {
            pub round_id: u32,
            pub slot: u64,
            pub timestamp: u32,
            pub answer: i128,
        }

        #[derive(Debug)]
        pub enum ReadError {
            InvalidOwner,
            InvalidDiscriminator,
            InvalidAccount,
            DeserializeFailed,
            FeedLengthInvalid,
            MalformedData,
            TransmissionNotFound,
        }

        impl fmt::Display for ReadError {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self {
                    ReadError::InvalidOwner => write!(f, "Invalid account owner"),
                    ReadError::InvalidDiscriminator => write!(f, "Invalid discriminator"),
                    ReadError::InvalidAccount => write!(f, "Invalid account data"),
                    ReadError::DeserializeFailed => write!(f, "Header deserialize failed"),
                    ReadError::FeedLengthInvalid =>
                        write!(f, "Expected a single live transmission"),
                    ReadError::MalformedData => write!(f, "Malformed feed data"),
                    ReadError::TransmissionNotFound => write!(f, "No latest transmission found"),
                }
            }
        }

        /// Represents the decoded Chainlink feed: header + current "live" transmission.
        pub struct Feed {
            _header: Transmissions,
            _live: Transmission,
        }

        impl Feed {
            pub fn latest_round_data(&self) -> Option<Round> {
                if self._header.latest_round_id == 0 {
                    return None;
                }
                Some(Round {
                    round_id: self._header.latest_round_id,
                    slot: self._live.slot,
                    timestamp: self._live.timestamp,
                    answer: self._live.answer,
                })
            }

            pub fn description(&self) -> [u8; 32] {
                self._header.description
            }

            pub fn decimals(&self) -> u8 {
                self._header.decimals
            }
        }

        /// Read and decode a Chainlink feed account's data (v2 OCR).
        ///
        /// - `data`  : account data (borrowed from AccountInfo::try_borrow_data)
        /// - `owner` : feed_account.owner.to_bytes()
        pub fn read_feed_v2(data: Ref<&mut [u8]>, owner: [u8; 32]) -> StdResult<Feed, ReadError> {
            // Check discriminator
            if !data.starts_with(&TRANSMISSIONS_DISCRIMINATOR) {
                return Err(ReadError::InvalidDiscriminator);
            }

            // Make sure the account is owned by the official Chainlink OCR2 program
            if owner != CHAINLINK_PROGRAM_ID_BYTES {
                return Err(ReadError::InvalidOwner);
            }

            // Parse header right after discriminator (8 bytes)
            let header = Transmissions::deserialize(&mut &data[8..]).map_err(
                |_| ReadError::DeserializeFailed
            )?;

            if header.live_length != 1 {
                return Err(ReadError::FeedLengthInvalid);
            }

            if header.latest_round_id == 0 {
                return Err(ReadError::TransmissionNotFound);
            }

            // Skip discriminator + header to get to the live transmissions ring buffer
            let (_head_bytes, rest) = data.split_at(8 + HEADER_SIZE);

            // Each Transmission is 48 bytes. Read the first one.
            let array: &[u8; 48] = rest
                .get(..size_of::<Transmission>())
                .and_then(|s| s.try_into().ok())
                .ok_or(ReadError::MalformedData)?;

            let live_transmission: Transmission = pod_read_unaligned(array);

            Ok(Feed {
                _header: header,
                _live: live_transmission,
            })
        }
    }
}

// -------------------------------------------------------------------------------------
// Program ID
// -------------------------------------------------------------------------------------

declare_id!("72qYP28onmhJQX1en3hWCphKSer2ksivDEv6PtiYfKcM");

// -------------------------------------------------------------------------------------
// Constants
// -------------------------------------------------------------------------------------

pub const FEE_DENOMINATOR: u64 = 10_000; // fees are in basis points / 10_000
pub const MAX_FEE: u64 = 1_000; // 10%
pub const MIN_PROTOCOL_FEE: u64 = 30; // 0.30%
pub const OUTCOME_TOKEN_DECIMALS: u8 = 9; // SPL norm is 9
pub const PRECISION_SCALE: u64 = 1_000_000_000; // for avg cost math
pub const STABILITY_WALLET: &str = "9JvZLhnbYpz6XJThyU5t8rVgkCjs79p7xH8CkRWniJgV";

pub fn stable_order_address() -> Pubkey {
    Pubkey::from_str(STABILITY_WALLET).unwrap()
}

// -------------------------------------------------------------------------------------
// Errors
// -------------------------------------------------------------------------------------

#[error_code]
pub enum PredictionError {
    #[msg("Invalid amount")]
    InvalidAmount,
    #[msg("Insufficient balance")]
    InsufficientBalance,
    #[msg("Invalid fee")]
    InvalidFee,
    #[msg("Unauthorized")]
    Unauthorized,
    #[msg("Invalid outcome")]
    InvalidOutcome,
    #[msg("Zero total supply")]
    ZeroTotalSupply,
    #[msg("Math overflow / underflow")]
    MathOverflow,
    #[msg("Zero price")]
    ZeroPrice,
    #[msg("Oracle read failed")]
    OracleReadFailed,
}

// -------------------------------------------------------------------------------------
// On-chain State
// -------------------------------------------------------------------------------------

#[account]
pub struct PoolAccount {
    // UI metadata
    pub name: String,
    pub description: String,
    pub bull_name: String,
    pub bull_symbol: String,
    pub bear_name: String,
    pub bear_symbol: String,

    // Which market this pool tracks (your own enum/indexing)
    pub pair_id: u32,

    // Semantic asset reference (can be anything off-chain wants to map to)
    pub asset_address: Pubkey,

    // Mint of the quote token (USDC etc.)
    pub quote_mint: Pubkey,

    // Cached normalized oracle price, scaled to 1_000_000 units
    pub current_price: u64,

    // The Chainlink feed this pool is anchored to
    pub chainlink_feed: Pubkey,

    // Bull & bear SPL token mints
    pub bull_mint: Pubkey,
    pub bear_mint: Pubkey,

    // Vaults that hold quote token for bull/bear
    pub bull_vault: Pubkey,
    pub bear_vault: Pubkey,

    // Fees (basis points out of 10_000)
    pub protocol_fee: u64,
    pub mint_fee: u64,
    pub burn_fee: u64,
    pub pool_creator_fee: u64,

    // Who's allowed to admin + collect creator fees
    pub pool_creator: Pubkey,

    // PDA bump for pool_signer
    pub pool_signer_bump: u8,
}

// === GLOBAL POOL REGISTRY ===
#[account]
pub struct PoolRegistryAccount {
    pub pools: Vec<Pubkey>,
}

pub const MAX_POOLS: usize = 512;

impl PoolRegistryAccount {
    pub const INIT_SPACE: usize = 8 + 4 + 32 * MAX_POOLS;

    pub fn push_unique(&mut self, pool: Pubkey) {
        if !self.pools.iter().any(|p| *p == pool) {
            self.pools.push(pool);
        }
    }
}

// === USER REGISTRY ===
#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub struct UserPosition {
    pub pool: Pubkey,
    pub bull_avg_price: u64,
    pub bear_avg_price: u64,
}

#[account]
pub struct UserRegistryAccount {
    pub user: Pubkey,
    pub positions: Vec<UserPosition>,
}

pub const MAX_USER_POSITIONS: usize = 128;

impl UserRegistryAccount {
    pub const INIT_SPACE: usize =
        8 + // disc
        32 + // user
        4 + // vec len
        MAX_USER_POSITIONS *
            (32 + // pool pubkey
                8 + // bull_avg_price
                8); // bear_avg_price

    pub fn get_position_mut(&mut self, pool: Pubkey) -> Option<&mut UserPosition> {
        self.positions.iter_mut().find(|p| p.pool == pool)
    }

    pub fn insert_new_position(
        &mut self,
        user: Pubkey,
        pool: Pubkey,
        bull_avg: u64,
        bear_avg: u64
    ) {
        if self.user == Pubkey::default() {
            self.user = user;
        }
        if self.positions.iter().any(|p| p.pool == pool) {
            return;
        }
        self.positions.push(UserPosition {
            pool,
            bull_avg_price: bull_avg,
            bear_avg_price: bear_avg,
        });
    }

    pub fn remove_position_if_empty(
        &mut self,
        pool: Pubkey,
        remaining_bull: u64,
        remaining_bear: u64
    ) {
        if remaining_bull == 0 && remaining_bear == 0 {
            if let Some(i) = self.positions.iter().position(|p| p.pool == pool) {
                self.positions.swap_remove(i);
            }
        }
    }
}

// -------------------------------------------------------------------------------------
// Events
// -------------------------------------------------------------------------------------

#[event]
pub struct PoolCreated {
    pub pool: Pubkey,
    pub name: String,
    pub creator: Pubkey,
    pub initial_price: u64, // scaled to 1e6
}

#[event]
pub struct PoolRebalanced {
    pub pool: Pubkey,
    pub old_price: u64,
    pub new_price: u64,
    pub old_bull_reserve: u64,
    pub old_bear_reserve: u64,
    pub new_bull_reserve: u64,
    pub new_bear_reserve: u64,
}

#[event]
pub struct TokensPurchased {
    pub pool: Pubkey,
    pub token_mint: Pubkey,
    pub token_name: String,
    pub token_symbol: String,
    pub buyer: Pubkey,
    pub quote_amount: u64,
    pub tokens_minted: u64,
    pub price_per_token: u64,
}

#[event]
pub struct TokensRedeemed {
    pub pool: Pubkey,
    pub token_mint: Pubkey,
    pub token_name: String,
    pub token_symbol: String,
    pub seller: Pubkey,
    pub tokens_burned: u64,
    pub quote_returned: u64,
}

// -------------------------------------------------------------------------------------
// Math / Pricing Helpers
// -------------------------------------------------------------------------------------

fn weighted_avg_price(
    old_balance: u64,
    old_avg_price: u64,
    added_amount: u64,
    added_price: u64
) -> Result<u64> {
    let total_balance = old_balance.checked_add(added_amount).ok_or(PredictionError::MathOverflow)?;
    if total_balance == 0 {
        return Ok(0);
    }

    let old_val = (old_balance as u128) * (old_avg_price as u128);
    let new_val = (added_amount as u128) * (added_price as u128);

    let sum = old_val.checked_add(new_val).ok_or(PredictionError::MathOverflow)?;

    let avg = sum.checked_div(total_balance as u128).ok_or(PredictionError::MathOverflow)? as u64;

    Ok(avg)
}

fn calculate_mint_amount(
    reserve_before: u64,
    total_supply_before: u64,
    quote_amount_in: u64
) -> Result<(u64, u64)> {
    let mint_amount: u64 = if total_supply_before == 0 {
        quote_amount_in
    } else {
        (quote_amount_in as u128)
            .checked_mul(total_supply_before as u128)
            .ok_or(PredictionError::MathOverflow)?
            .checked_div(reserve_before as u128)
            .ok_or(PredictionError::MathOverflow)? as u64
    };

    let price_per_token = if mint_amount > 0 {
        (quote_amount_in as u128)
            .checked_mul(PRECISION_SCALE as u128)
            .ok_or(PredictionError::MathOverflow)?
            .checked_div(mint_amount as u128)
            .ok_or(PredictionError::MathOverflow)? as u64
    } else {
        0
    };

    Ok((mint_amount, price_per_token))
}

fn calculate_burn_amount(
    reserve_before: u64,
    total_supply_before: u64,
    tokens_to_burn: u64
) -> Result<u64> {
    if total_supply_before == 0 {
        return Ok(0);
    }
    let num = (tokens_to_burn as u128)
        .checked_mul(reserve_before as u128)
        .ok_or(PredictionError::MathOverflow)?;
    let out = num
        .checked_div(total_supply_before as u128)
        .ok_or(PredictionError::MathOverflow)? as u64;
    Ok(out)
}

// Turn raw oracle answer + decimals into a precision-scaled u64.
fn normalize_price(value: u128, decimals: u8, precision: u64) -> u64 {
    // divisor = 10^decimals
    let mut divisor: u128 = 1;
    for _ in 0..decimals {
        divisor = divisor.saturating_mul(10);
    }
    let scaled = value.saturating_mul(precision as u128).saturating_div(divisor);
    scaled as u64
}

// figure target bull/bear vault reserves after a price move
fn calculate_new_reserves(
    old_price: u64,
    new_price: u64,
    bull_reserve: u64,
    bear_reserve: u64
) -> Result<(u64, u64)> {
    require!(old_price > 0, PredictionError::ZeroPrice);
    require!(new_price > 0, PredictionError::ZeroPrice);

    let total_reserve: u128 = (bull_reserve as u128) + (bear_reserve as u128);

    let bull_component = (bull_reserve as u128)
        .checked_mul(new_price as u128)
        .ok_or(PredictionError::MathOverflow)?
        .checked_div(old_price as u128)
        .ok_or(PredictionError::MathOverflow)?;

    let bear_component = (bear_reserve as u128)
        .checked_mul(old_price as u128)
        .ok_or(PredictionError::MathOverflow)?
        .checked_div(new_price as u128)
        .ok_or(PredictionError::MathOverflow)?;

    let total_component = bull_component
        .checked_add(bear_component)
        .ok_or(PredictionError::MathOverflow)?;

    if total_component == 0 {
        return Ok((0, 0));
    }

    let new_bull_reserve = total_reserve
        .checked_mul(bull_component)
        .ok_or(PredictionError::MathOverflow)?
        .checked_div(total_component)
        .ok_or(PredictionError::MathOverflow)? as u64;

    let new_bear_reserve = total_reserve
        .checked_mul(bear_component)
        .ok_or(PredictionError::MathOverflow)?
        .checked_div(total_component)
        .ok_or(PredictionError::MathOverflow)? as u64;

    Ok((new_bull_reserve as u64, new_bear_reserve as u64))
}

// fee breakdown (protocol / specific / creator / net)
fn compute_fee_breakdown(
    amount: u64,
    protocol_fee_bps: u64,
    specific_fee_bps: u64,
    creator_fee_bps: u64
) -> Result<(u64, u64, u64, u64)> {
    let protocol_fee_amt = (amount as u128)
        .checked_mul(protocol_fee_bps as u128)
        .ok_or(PredictionError::MathOverflow)?
        .checked_div(FEE_DENOMINATOR as u128)
        .ok_or(PredictionError::MathOverflow)? as u64;

    let specific_fee_amt = (amount as u128)
        .checked_mul(specific_fee_bps as u128)
        .ok_or(PredictionError::MathOverflow)?
        .checked_div(FEE_DENOMINATOR as u128)
        .ok_or(PredictionError::MathOverflow)? as u64;

    let creator_fee_amt = (amount as u128)
        .checked_mul(creator_fee_bps as u128)
        .ok_or(PredictionError::MathOverflow)?
        .checked_div(FEE_DENOMINATOR as u128)
        .ok_or(PredictionError::MathOverflow)? as u64;

    let net_amount = amount
        .saturating_sub(protocol_fee_amt)
        .saturating_sub(specific_fee_amt)
        .saturating_sub(creator_fee_amt);

    Ok((protocol_fee_amt, specific_fee_amt, creator_fee_amt, net_amount))
}

// -------------------------------------------------------------------------------------
// Chainlink helpers
// -------------------------------------------------------------------------------------

// 1. Safely read and scale the on-chain Chainlink feed price (scaled to 1e6)
fn read_chainlink_price_scaled<'info>(feed_account: &UncheckedAccount<'info>) -> Result<u64> {
    let ai = feed_account.to_account_info();
    let data_ref = ai.try_borrow_data()?;
    let owner_bytes = ai.owner.to_bytes();

    // Decode feed using our embedded reader
    let feed = match chainlink::v2::read_feed_v2(data_ref, owner_bytes) {
        Ok(f) => f,
        Err(_) => {
            return err!(PredictionError::OracleReadFailed);
        }
    };

    // Get latest round
    let round = if let Some(r) = feed.latest_round_data() {
        r
    } else {
        return err!(PredictionError::ZeroPrice);
    };

    // Price must be positive
    require!(round.answer >= 0, PredictionError::ZeroPrice);

    // Scale feed.answer (i128) using feed.decimals()
    let scaled = normalize_price(
        round.answer as u128,
        feed.decimals(),
        1_000_000 // pool price precision
    );

    Ok(scaled)
}

// 2. Sync the pool vaults against current oracle price, shifting quote between them.
fn do_rebalance<'info>(
    pool: &mut Account<'info, PoolAccount>,
    chainlink_feed: &UncheckedAccount<'info>,
    bull_vault: &Account<'info, TokenAccount>,
    bear_vault: &Account<'info, TokenAccount>,
    pool_signer: &UncheckedAccount<'info>,
    token_program: &Program<'info, Token>
) -> Result<()> {
    // Make sure the feed passed into the instruction call is the same feed
    // the pool was initialized with.
    require_keys_eq!(chainlink_feed.key(), pool.chainlink_feed, PredictionError::Unauthorized);

    let new_price = read_chainlink_price_scaled(chainlink_feed)?;

    let old_price = pool.current_price;
    if new_price == old_price {
        return Ok(()); // nothing changed
    }

    let old_bull_reserve = bull_vault.amount;
    let old_bear_reserve = bear_vault.amount;

    let (target_bull, target_bear) = calculate_new_reserves(
        old_price,
        new_price,
        old_bull_reserve,
        old_bear_reserve
    )?;

    let pool_key = pool.key();
    let signer_seeds: &[&[u8]] = &[b"pool_signer", pool_key.as_ref(), &[pool.pool_signer_bump]];

    if target_bull > old_bull_reserve {
        // move from bear_vault -> bull_vault
        let diff = target_bull - old_bull_reserve;
        token::transfer(
            CpiContext::new_with_signer(
                token_program.to_account_info(),
                Transfer {
                    from: bear_vault.to_account_info(),
                    to: bull_vault.to_account_info(),
                    authority: pool_signer.to_account_info(),
                },
                &[signer_seeds]
            ),
            diff
        )?;
    } else if target_bull < old_bull_reserve {
        // move from bull_vault -> bear_vault
        let diff = old_bull_reserve - target_bull;
        token::transfer(
            CpiContext::new_with_signer(
                token_program.to_account_info(),
                Transfer {
                    from: bull_vault.to_account_info(),
                    to: bear_vault.to_account_info(),
                    authority: pool_signer.to_account_info(),
                },
                &[signer_seeds]
            ),
            diff
        )?;
    }

    pool.current_price = new_price;

    emit!(PoolRebalanced {
        pool: pool.key(),
        old_price,
        new_price,
        old_bull_reserve,
        old_bear_reserve,
        new_bull_reserve: target_bull,
        new_bear_reserve: target_bear,
    });

    Ok(())
}

// -------------------------------------------------------------------------------------
// Instruction Args
// -------------------------------------------------------------------------------------

#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub struct InitPoolArgs {
    pub name: String,
    pub description: String,
    pub bull_name: String,
    pub bull_symbol: String,
    pub bear_name: String,
    pub bear_symbol: String,
    pub pair_id: u32,
    pub asset_address: Pubkey,
    pub protocol_fee_param: u64,
    pub mint_fee_param: u64,
    pub burn_fee_param: u64,
    pub pool_creator_fee_param: u64,
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub struct SeedLiquidityArgs {
    pub initial_liquidity: u64,
}

// -------------------------------------------------------------------------------------
// Program Entry
// -------------------------------------------------------------------------------------

#[program]
pub mod fate {
    use super::*;

    // STEP 1: create pool state, vaults, mints, set fees, record Chainlink feed
    pub fn init_pool(ctx: Context<InitPool>, args: InitPoolArgs) -> Result<()> {
        // only payer == pool_creator
        require_keys_eq!(
            ctx.accounts.pool_creator.key(),
            ctx.accounts.payer.key(),
            PredictionError::Unauthorized
        );

        // clamp fees like original logic
        let mut protocol_fee = args.protocol_fee_param;
        let mut pool_creator_fee = args.pool_creator_fee_param;
        let mut mint_fee = args.mint_fee_param;
        let mut burn_fee = args.burn_fee_param;

        pool_creator_fee = pool_creator_fee.min(MAX_FEE);
        protocol_fee = protocol_fee.max(pool_creator_fee).max(MIN_PROTOCOL_FEE).min(MAX_FEE);

        mint_fee = mint_fee.min(MAX_FEE);
        burn_fee = burn_fee.min(MAX_FEE);
        pool_creator_fee = pool_creator_fee.min(MAX_FEE);

        // read initial oracle price from the Chainlink feed
        let initial_price = read_chainlink_price_scaled(&ctx.accounts.chainlink_feed)?;

        let pool = &mut ctx.accounts.pool;

        pool.name = args.name.clone();
        pool.description = args.description.clone();

        pool.bull_name = args.bull_name.clone();
        pool.bull_symbol = args.bull_symbol.clone();
        pool.bear_name = args.bear_name.clone();
        pool.bear_symbol = args.bear_symbol.clone();

        pool.pair_id = args.pair_id;
        pool.asset_address = args.asset_address;

        pool.quote_mint = ctx.accounts.quote_mint.key();
        pool.current_price = initial_price;
        pool.chainlink_feed = ctx.accounts.chainlink_feed.key();

        pool.bull_mint = ctx.accounts.bull_mint.key();
        pool.bear_mint = ctx.accounts.bear_mint.key();
        pool.bull_vault = ctx.accounts.bull_vault.key();
        pool.bear_vault = ctx.accounts.bear_vault.key();

        pool.protocol_fee = protocol_fee;
        pool.mint_fee = mint_fee;
        pool.burn_fee = burn_fee;
        pool.pool_creator_fee = pool_creator_fee;
        pool.pool_creator = ctx.accounts.pool_creator.key();

        pool.pool_signer_bump = ctx.bumps.pool_signer;

        // add pool to global registry list
        ctx.accounts.registry.push_unique(pool.key());

        emit!(PoolCreated {
            pool: pool.key(),
            name: pool.name.clone(),
            creator: ctx.accounts.payer.key(),
            initial_price,
        });

        Ok(())
    }

    // STEP 2: fund the vaults with initial liquidity, mint first bull/bear to creator
    pub fn seed_liquidity(ctx: Context<SeedLiquidity>, args: SeedLiquidityArgs) -> Result<()> {
        require!(args.initial_liquidity > 0, PredictionError::InvalidAmount);
        require!(
            ctx.accounts.funding_ata.amount >= args.initial_liquidity,
            PredictionError::InsufficientBalance
        );

        let pool = &mut ctx.accounts.pool;

        // only pool_creator can seed first liquidity
        require_keys_eq!(
            pool.pool_creator,
            ctx.accounts.payer.key(),
            PredictionError::Unauthorized
        );

        // funding_ata must match the pool's quote mint
        require_keys_eq!(
            ctx.accounts.funding_ata.mint,
            pool.quote_mint,
            PredictionError::Unauthorized
        );

        // 50/50 split initial liquidity across bull_vault / bear_vault
        let bull_seed_amount = args.initial_liquidity / 2;
        let bear_seed_amount = args.initial_liquidity - bull_seed_amount;

        // payer -> bull_vault
        token::transfer(
            CpiContext::new(ctx.accounts.token_program.to_account_info(), Transfer {
                from: ctx.accounts.funding_ata.to_account_info(),
                to: ctx.accounts.bull_vault.to_account_info(),
                authority: ctx.accounts.payer.to_account_info(),
            }),
            bull_seed_amount
        )?;

        // payer -> bear_vault
        token::transfer(
            CpiContext::new(ctx.accounts.token_program.to_account_info(), Transfer {
                from: ctx.accounts.funding_ata.to_account_info(),
                to: ctx.accounts.bear_vault.to_account_info(),
                authority: ctx.accounts.payer.to_account_info(),
            }),
            bear_seed_amount
        )?;

        // how many bull/bear tokens to mint to creator on bootstrap
        let (bull_tokens_minted, bull_price_per_token) = calculate_mint_amount(
            bull_seed_amount,
            0,
            bull_seed_amount
        )?;
        let (bear_tokens_minted, bear_price_per_token) = calculate_mint_amount(
            bear_seed_amount,
            0,
            bear_seed_amount
        )?;

        let pool_key = pool.key();
        let signer_seeds: &[&[u8]] = &[b"pool_signer", pool_key.as_ref(), &[pool.pool_signer_bump]];

        // mint bull -> payer_bull_ata
        token::mint_to(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                MintTo {
                    mint: ctx.accounts.bull_mint.to_account_info(),
                    to: ctx.accounts.payer_bull_ata.to_account_info(),
                    authority: ctx.accounts.pool_signer.to_account_info(),
                },
                &[signer_seeds]
            ),
            bull_tokens_minted
        )?;

        // mint bear -> payer_bear_ata
        token::mint_to(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                MintTo {
                    mint: ctx.accounts.bear_mint.to_account_info(),
                    to: ctx.accounts.payer_bear_ata.to_account_info(),
                    authority: ctx.accounts.pool_signer.to_account_info(),
                },
                &[signer_seeds]
            ),
            bear_tokens_minted
        )?;

        // record creator's avg purchase prices
        let ur = &mut ctx.accounts.user_registry;
        if ur.user == Pubkey::default() {
            ur.user = ctx.accounts.payer.key();
        }

        if let Some(pos) = ur.get_position_mut(pool.key()) {
            pos.bull_avg_price = bull_price_per_token;
            pos.bear_avg_price = bear_price_per_token;
        } else {
            ur.insert_new_position(
                ctx.accounts.payer.key(),
                pool.key(),
                bull_price_per_token,
                bear_price_per_token
            );
        }

        Ok(())
    }

    // manual oracle sync (creator can force)
    pub fn rebalance_pool(ctx: Context<RebalancePool>) -> Result<()> {
        let pool = &mut ctx.accounts.pool;

        // only pool.creator
        require_keys_eq!(
            ctx.accounts.authority.key(),
            pool.pool_creator,
            PredictionError::Unauthorized
        );

        do_rebalance(
            pool,
            &ctx.accounts.chainlink_feed,
            &ctx.accounts.bull_vault,
            &ctx.accounts.bear_vault,
            &ctx.accounts.pool_signer,
            &ctx.accounts.token_program
        )
    }

    // BUY BULL
    pub fn purchase_bull(ctx: Context<PurchaseBull>, quote_amount_in: u64) -> Result<()> {
        require!(quote_amount_in > 0, PredictionError::InvalidAmount);
        let pool = &mut ctx.accounts.pool;

        // fee receivers must match expectations
        require_keys_eq!(
            ctx.accounts.protocol_fee_ata.owner,
            stable_order_address(),
            PredictionError::Unauthorized
        );
        require_keys_eq!(
            ctx.accounts.creator_quote_ata.owner,
            pool.pool_creator,
            PredictionError::Unauthorized
        );

        // sanity mints
        require_keys_eq!(
            ctx.accounts.buyer_quote_ata.mint,
            pool.quote_mint,
            PredictionError::Unauthorized
        );
        require_keys_eq!(
            ctx.accounts.protocol_fee_ata.mint,
            pool.quote_mint,
            PredictionError::Unauthorized
        );
        require_keys_eq!(
            ctx.accounts.creator_quote_ata.mint,
            pool.quote_mint,
            PredictionError::Unauthorized
        );
        require_keys_eq!(
            ctx.accounts.buyer_bull_ata.mint,
            pool.bull_mint,
            PredictionError::Unauthorized
        );

        // sync pool vs oracle before trade
        do_rebalance(
            pool,
            &ctx.accounts.chainlink_feed,
            &ctx.accounts.bull_vault,
            &ctx.accounts.bear_vault,
            &ctx.accounts.pool_signer,
            &ctx.accounts.token_program
        )?;

        // snapshot BEFORE funds move
        let reserve_before = ctx.accounts.bull_vault.amount;
        let total_supply_before = ctx.accounts.bull_mint.supply;
        let user_old_balance = ctx.accounts.buyer_bull_ata.amount;

        // fee breakdown (mint_fee applies on buy)
        let (protocol_fee_amt, fee_amt, creator_fee_amt, net_amount) = compute_fee_breakdown(
            quote_amount_in,
            pool.protocol_fee,
            pool.mint_fee,
            pool.pool_creator_fee
        )?;
        require!(net_amount > 0, PredictionError::InvalidAmount);

        // protocol fee -> protocol_fee_ata
        if protocol_fee_amt > 0 {
            token::transfer(
                CpiContext::new(ctx.accounts.token_program.to_account_info(), Transfer {
                    from: ctx.accounts.buyer_quote_ata.to_account_info(),
                    to: ctx.accounts.protocol_fee_ata.to_account_info(),
                    authority: ctx.accounts.buyer.to_account_info(),
                }),
                protocol_fee_amt
            )?;
        }

        // mint_fee -> OTHER side vault (bear_vault)
        if fee_amt > 0 {
            token::transfer(
                CpiContext::new(ctx.accounts.token_program.to_account_info(), Transfer {
                    from: ctx.accounts.buyer_quote_ata.to_account_info(),
                    to: ctx.accounts.bear_vault.to_account_info(),
                    authority: ctx.accounts.buyer.to_account_info(),
                }),
                fee_amt
            )?;
        }

        // creator fee -> creator_quote_ata
        if creator_fee_amt > 0 {
            token::transfer(
                CpiContext::new(ctx.accounts.token_program.to_account_info(), Transfer {
                    from: ctx.accounts.buyer_quote_ata.to_account_info(),
                    to: ctx.accounts.creator_quote_ata.to_account_info(),
                    authority: ctx.accounts.buyer.to_account_info(),
                }),
                creator_fee_amt
            )?;
        }

        // net trade amount -> bull_vault
        token::transfer(
            CpiContext::new(ctx.accounts.token_program.to_account_info(), Transfer {
                from: ctx.accounts.buyer_quote_ata.to_account_info(),
                to: ctx.accounts.bull_vault.to_account_info(),
                authority: ctx.accounts.buyer.to_account_info(),
            }),
            net_amount
        )?;

        // mint bull tokens based on bonding curve
        let (mint_amount, price_per_token) = calculate_mint_amount(
            reserve_before,
            total_supply_before,
            net_amount
        )?;

        // mint -> buyer_bull_ata
        let pool_key = pool.key();
        let signer_seeds: &[&[u8]] = &[b"pool_signer", pool_key.as_ref(), &[pool.pool_signer_bump]];
        token::mint_to(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                MintTo {
                    mint: ctx.accounts.bull_mint.to_account_info(),
                    to: ctx.accounts.buyer_bull_ata.to_account_info(),
                    authority: ctx.accounts.pool_signer.to_account_info(),
                },
                &[signer_seeds]
            ),
            mint_amount
        )?;

        // update user's avg bull cost
        let ur = &mut ctx.accounts.user_registry;
        if ur.user == Pubkey::default() {
            ur.user = ctx.accounts.buyer.key();
        }

        if let Some(pos) = ur.get_position_mut(pool.key()) {
            let new_avg = weighted_avg_price(
                user_old_balance,
                pos.bull_avg_price,
                mint_amount,
                price_per_token
            )?;
            pos.bull_avg_price = new_avg;
        } else {
            ur.insert_new_position(
                ctx.accounts.buyer.key(),
                pool.key(),
                price_per_token, // bull avg
                0 // bear avg
            );
        }

        emit!(TokensPurchased {
            pool: pool.key(),
            token_mint: ctx.accounts.bull_mint.key(),
            token_name: pool.bull_name.clone(),
            token_symbol: pool.bull_symbol.clone(),
            buyer: ctx.accounts.buyer.key(),
            quote_amount: net_amount,
            tokens_minted: mint_amount,
            price_per_token,
        });

        Ok(())
    }

    // BUY BEAR
    pub fn purchase_bear(ctx: Context<PurchaseBear>, quote_amount_in: u64) -> Result<()> {
        require!(quote_amount_in > 0, PredictionError::InvalidAmount);

        let pool = &mut ctx.accounts.pool;

        require_keys_eq!(
            ctx.accounts.protocol_fee_ata.owner,
            stable_order_address(),
            PredictionError::Unauthorized
        );
        require_keys_eq!(
            ctx.accounts.creator_quote_ata.owner,
            pool.pool_creator,
            PredictionError::Unauthorized
        );

        require_keys_eq!(
            ctx.accounts.buyer_quote_ata.mint,
            pool.quote_mint,
            PredictionError::Unauthorized
        );
        require_keys_eq!(
            ctx.accounts.protocol_fee_ata.mint,
            pool.quote_mint,
            PredictionError::Unauthorized
        );
        require_keys_eq!(
            ctx.accounts.creator_quote_ata.mint,
            pool.quote_mint,
            PredictionError::Unauthorized
        );
        require_keys_eq!(
            ctx.accounts.buyer_bear_ata.mint,
            pool.bear_mint,
            PredictionError::Unauthorized
        );

        do_rebalance(
            pool,
            &ctx.accounts.chainlink_feed,
            &ctx.accounts.bull_vault,
            &ctx.accounts.bear_vault,
            &ctx.accounts.pool_signer,
            &ctx.accounts.token_program
        )?;

        // snapshot
        let reserve_before = ctx.accounts.bear_vault.amount;
        let total_supply_before = ctx.accounts.bear_mint.supply;
        let user_old_balance = ctx.accounts.buyer_bear_ata.amount;

        let (protocol_fee_amt, fee_amt, creator_fee_amt, net_amount) = compute_fee_breakdown(
            quote_amount_in,
            pool.protocol_fee,
            pool.mint_fee,
            pool.pool_creator_fee
        )?;
        require!(net_amount > 0, PredictionError::InvalidAmount);

        // protocol fee -> protocol_fee_ata
        if protocol_fee_amt > 0 {
            token::transfer(
                CpiContext::new(ctx.accounts.token_program.to_account_info(), Transfer {
                    from: ctx.accounts.buyer_quote_ata.to_account_info(),
                    to: ctx.accounts.protocol_fee_ata.to_account_info(),
                    authority: ctx.accounts.buyer.to_account_info(),
                }),
                protocol_fee_amt
            )?;
        }

        // mint_fee portion -> bull_vault
        if fee_amt > 0 {
            token::transfer(
                CpiContext::new(ctx.accounts.token_program.to_account_info(), Transfer {
                    from: ctx.accounts.buyer_quote_ata.to_account_info(),
                    to: ctx.accounts.bull_vault.to_account_info(),
                    authority: ctx.accounts.buyer.to_account_info(),
                }),
                fee_amt
            )?;
        }

        // creator fee -> creator_quote_ata
        if creator_fee_amt > 0 {
            token::transfer(
                CpiContext::new(ctx.accounts.token_program.to_account_info(), Transfer {
                    from: ctx.accounts.buyer_quote_ata.to_account_info(),
                    to: ctx.accounts.creator_quote_ata.to_account_info(),
                    authority: ctx.accounts.buyer.to_account_info(),
                }),
                creator_fee_amt
            )?;
        }

        // net buy -> bear_vault
        token::transfer(
            CpiContext::new(ctx.accounts.token_program.to_account_info(), Transfer {
                from: ctx.accounts.buyer_quote_ata.to_account_info(),
                to: ctx.accounts.bear_vault.to_account_info(),
                authority: ctx.accounts.buyer.to_account_info(),
            }),
            net_amount
        )?;

        let (mint_amount, price_per_token) = calculate_mint_amount(
            reserve_before,
            total_supply_before,
            net_amount
        )?;

        let pool_key = pool.key();
        let signer_seeds: &[&[u8]] = &[b"pool_signer", pool_key.as_ref(), &[pool.pool_signer_bump]];
        token::mint_to(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                MintTo {
                    mint: ctx.accounts.bear_mint.to_account_info(),
                    to: ctx.accounts.buyer_bear_ata.to_account_info(),
                    authority: ctx.accounts.pool_signer.to_account_info(),
                },
                &[signer_seeds]
            ),
            mint_amount
        )?;

        let ur = &mut ctx.accounts.user_registry;
        if ur.user == Pubkey::default() {
            ur.user = ctx.accounts.buyer.key();
        }

        if let Some(pos) = ur.get_position_mut(pool.key()) {
            let new_avg = weighted_avg_price(
                user_old_balance,
                pos.bear_avg_price,
                mint_amount,
                price_per_token
            )?;
            pos.bear_avg_price = new_avg;
        } else {
            ur.insert_new_position(
                ctx.accounts.buyer.key(),
                pool.key(),
                0, // bull avg
                price_per_token // bear avg
            );
        }

        emit!(TokensPurchased {
            pool: pool.key(),
            token_mint: ctx.accounts.bear_mint.key(),
            token_name: pool.bear_name.clone(),
            token_symbol: pool.bear_symbol.clone(),
            buyer: ctx.accounts.buyer.key(),
            quote_amount: net_amount,
            tokens_minted: mint_amount,
            price_per_token,
        });

        Ok(())
    }

    // REDEEM BULL
    pub fn redeem_bull(ctx: Context<RedeemBull>, amount_out_tokens: u64) -> Result<()> {
        require!(amount_out_tokens > 0, PredictionError::InvalidAmount);

        let pool = &mut ctx.accounts.pool;

        require_keys_eq!(
            ctx.accounts.protocol_fee_ata.owner,
            stable_order_address(),
            PredictionError::Unauthorized
        );
        require_keys_eq!(
            ctx.accounts.creator_quote_ata.owner,
            pool.pool_creator,
            PredictionError::Unauthorized
        );

        // quote mint routes must match
        require_keys_eq!(
            ctx.accounts.seller_quote_ata.mint,
            pool.quote_mint,
            PredictionError::Unauthorized
        );
        require_keys_eq!(
            ctx.accounts.protocol_fee_ata.mint,
            pool.quote_mint,
            PredictionError::Unauthorized
        );
        require_keys_eq!(
            ctx.accounts.creator_quote_ata.mint,
            pool.quote_mint,
            PredictionError::Unauthorized
        );

        // burn from seller_bull_ata, must be bull mint
        require_keys_eq!(
            ctx.accounts.seller_bull_ata.mint,
            pool.bull_mint,
            PredictionError::Unauthorized
        );
        // we also peek seller_bear_ata later
        require_keys_eq!(
            ctx.accounts.seller_bear_ata.mint,
            pool.bear_mint,
            PredictionError::Unauthorized
        );

        // sync oracle & vault split before redemption
        do_rebalance(
            pool,
            &ctx.accounts.chainlink_feed,
            &ctx.accounts.bull_vault,
            &ctx.accounts.bear_vault,
            &ctx.accounts.pool_signer,
            &ctx.accounts.token_program
        )?;

        require!(
            ctx.accounts.seller_bull_ata.amount >= amount_out_tokens,
            PredictionError::InsufficientBalance
        );

        let total_supply_before = ctx.accounts.bull_mint.supply;
        require!(total_supply_before > 0, PredictionError::ZeroTotalSupply);
        // don't allow burning 100% of supply
        require!(total_supply_before > amount_out_tokens, PredictionError::InvalidAmount);

        let reserve_before = ctx.accounts.bull_vault.amount;
        let quote_to_return = calculate_burn_amount(
            reserve_before,
            total_supply_before,
            amount_out_tokens
        )?;
        require!(
            ctx.accounts.bull_vault.amount >= quote_to_return,
            PredictionError::InsufficientBalance
        );

        // burn seller's bull
        token::burn(
            CpiContext::new(ctx.accounts.token_program.to_account_info(), Burn {
                mint: ctx.accounts.bull_mint.to_account_info(),
                from: ctx.accounts.seller_bull_ata.to_account_info(),
                authority: ctx.accounts.seller.to_account_info(),
            }),
            amount_out_tokens
        )?;

        // apply redemption fees (burn_fee)
        let (protocol_fee_amt, fee_amt, creator_fee_amt, net_amount) = compute_fee_breakdown(
            quote_to_return,
            pool.protocol_fee,
            pool.burn_fee,
            pool.pool_creator_fee
        )?;
        require!(net_amount > 0, PredictionError::InvalidAmount);

        let pool_key = pool.key();
        let signer_seeds: &[&[u8]] = &[b"pool_signer", pool_key.as_ref(), &[pool.pool_signer_bump]];

        // protocol fee -> protocol_fee_ata
        if protocol_fee_amt > 0 {
            token::transfer(
                CpiContext::new_with_signer(
                    ctx.accounts.token_program.to_account_info(),
                    Transfer {
                        from: ctx.accounts.bull_vault.to_account_info(),
                        to: ctx.accounts.protocol_fee_ata.to_account_info(),
                        authority: ctx.accounts.pool_signer.to_account_info(),
                    },
                    &[signer_seeds]
                ),
                protocol_fee_amt
            )?;
        }

        // burn_fee portion -> other vault (bear_vault)
        if fee_amt > 0 {
            token::transfer(
                CpiContext::new_with_signer(
                    ctx.accounts.token_program.to_account_info(),
                    Transfer {
                        from: ctx.accounts.bull_vault.to_account_info(),
                        to: ctx.accounts.bear_vault.to_account_info(),
                        authority: ctx.accounts.pool_signer.to_account_info(),
                    },
                    &[signer_seeds]
                ),
                fee_amt
            )?;
        }

        // creator fee -> creator_quote_ata
        if creator_fee_amt > 0 {
            token::transfer(
                CpiContext::new_with_signer(
                    ctx.accounts.token_program.to_account_info(),
                    Transfer {
                        from: ctx.accounts.bull_vault.to_account_info(),
                        to: ctx.accounts.creator_quote_ata.to_account_info(),
                        authority: ctx.accounts.pool_signer.to_account_info(),
                    },
                    &[signer_seeds]
                ),
                creator_fee_amt
            )?;
        }

        // net payout -> seller_quote_ata
        token::transfer(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                Transfer {
                    from: ctx.accounts.bull_vault.to_account_info(),
                    to: ctx.accounts.seller_quote_ata.to_account_info(),
                    authority: ctx.accounts.pool_signer.to_account_info(),
                },
                &[signer_seeds]
            ),
            net_amount
        )?;

        // after burn and payout, reload ATAs
        ctx.accounts.seller_bull_ata.reload()?;
        ctx.accounts.seller_bear_ata.reload()?;

        let remaining_bull = ctx.accounts.seller_bull_ata.amount;
        let remaining_bear = ctx.accounts.seller_bear_ata.amount;

        let ur = &mut ctx.accounts.user_registry;
        if let Some(pos) = ur.get_position_mut(pool.key()) {
            if remaining_bull == 0 {
                pos.bull_avg_price = 0;
            }
            if remaining_bear == 0 {
                pos.bear_avg_price = 0;
            }
        }
        ur.remove_position_if_empty(pool.key(), remaining_bull, remaining_bear);

        emit!(TokensRedeemed {
            pool: pool.key(),
            token_mint: ctx.accounts.bull_mint.key(),
            token_name: pool.bull_name.clone(),
            token_symbol: pool.bull_symbol.clone(),
            seller: ctx.accounts.seller.key(),
            tokens_burned: amount_out_tokens,
            quote_returned: net_amount,
        });

        Ok(())
    }

    // REDEEM BEAR
    pub fn redeem_bear(ctx: Context<RedeemBear>, amount_out_tokens: u64) -> Result<()> {
        require!(amount_out_tokens > 0, PredictionError::InvalidAmount);

        let pool = &mut ctx.accounts.pool;

        require_keys_eq!(
            ctx.accounts.protocol_fee_ata.owner,
            stable_order_address(),
            PredictionError::Unauthorized
        );
        require_keys_eq!(
            ctx.accounts.creator_quote_ata.owner,
            pool.pool_creator,
            PredictionError::Unauthorized
        );

        require_keys_eq!(
            ctx.accounts.seller_quote_ata.mint,
            pool.quote_mint,
            PredictionError::Unauthorized
        );
        require_keys_eq!(
            ctx.accounts.protocol_fee_ata.mint,
            pool.quote_mint,
            PredictionError::Unauthorized
        );
        require_keys_eq!(
            ctx.accounts.creator_quote_ata.mint,
            pool.quote_mint,
            PredictionError::Unauthorized
        );

        // bear burn source must be bear mint
        require_keys_eq!(
            ctx.accounts.seller_bear_ata.mint,
            pool.bear_mint,
            PredictionError::Unauthorized
        );
        // we also read bull afterwards for cleanup
        require_keys_eq!(
            ctx.accounts.seller_bull_ata.mint,
            pool.bull_mint,
            PredictionError::Unauthorized
        );

        do_rebalance(
            pool,
            &ctx.accounts.chainlink_feed,
            &ctx.accounts.bull_vault,
            &ctx.accounts.bear_vault,
            &ctx.accounts.pool_signer,
            &ctx.accounts.token_program
        )?;

        require!(
            ctx.accounts.seller_bear_ata.amount >= amount_out_tokens,
            PredictionError::InsufficientBalance
        );

        let total_supply_before = ctx.accounts.bear_mint.supply;
        require!(total_supply_before > 0, PredictionError::ZeroTotalSupply);
        require!(total_supply_before > amount_out_tokens, PredictionError::InvalidAmount);

        let reserve_before = ctx.accounts.bear_vault.amount;
        let quote_to_return = calculate_burn_amount(
            reserve_before,
            total_supply_before,
            amount_out_tokens
        )?;
        require!(
            ctx.accounts.bear_vault.amount >= quote_to_return,
            PredictionError::InsufficientBalance
        );

        // burn seller's bear tokens
        token::burn(
            CpiContext::new(ctx.accounts.token_program.to_account_info(), Burn {
                mint: ctx.accounts.bear_mint.to_account_info(),
                from: ctx.accounts.seller_bear_ata.to_account_info(),
                authority: ctx.accounts.seller.to_account_info(),
            }),
            amount_out_tokens
        )?;

        let (protocol_fee_amt, fee_amt, creator_fee_amt, net_amount) = compute_fee_breakdown(
            quote_to_return,
            pool.protocol_fee,
            pool.burn_fee,
            pool.pool_creator_fee
        )?;
        require!(net_amount > 0, PredictionError::InvalidAmount);

        let pool_key = pool.key();
        let signer_seeds: &[&[u8]] = &[b"pool_signer", pool_key.as_ref(), &[pool.pool_signer_bump]];

        // protocol fee -> protocol_fee_ata
        if protocol_fee_amt > 0 {
            token::transfer(
                CpiContext::new_with_signer(
                    ctx.accounts.token_program.to_account_info(),
                    Transfer {
                        from: ctx.accounts.bear_vault.to_account_info(),
                        to: ctx.accounts.protocol_fee_ata.to_account_info(),
                        authority: ctx.accounts.pool_signer.to_account_info(),
                    },
                    &[signer_seeds]
                ),
                protocol_fee_amt
            )?;
        }

        // burn_fee portion -> bull_vault
        if fee_amt > 0 {
            token::transfer(
                CpiContext::new_with_signer(
                    ctx.accounts.token_program.to_account_info(),
                    Transfer {
                        from: ctx.accounts.bear_vault.to_account_info(),
                        to: ctx.accounts.bull_vault.to_account_info(),
                        authority: ctx.accounts.pool_signer.to_account_info(),
                    },
                    &[signer_seeds]
                ),
                fee_amt
            )?;
        }

        // creator fee -> creator_quote_ata
        if creator_fee_amt > 0 {
            token::transfer(
                CpiContext::new_with_signer(
                    ctx.accounts.token_program.to_account_info(),
                    Transfer {
                        from: ctx.accounts.bear_vault.to_account_info(),
                        to: ctx.accounts.creator_quote_ata.to_account_info(),
                        authority: ctx.accounts.pool_signer.to_account_info(),
                    },
                    &[signer_seeds]
                ),
                creator_fee_amt
            )?;
        }

        // net payout -> seller_quote_ata
        token::transfer(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                Transfer {
                    from: ctx.accounts.bear_vault.to_account_info(),
                    to: ctx.accounts.seller_quote_ata.to_account_info(),
                    authority: ctx.accounts.pool_signer.to_account_info(),
                },
                &[signer_seeds]
            ),
            net_amount
        )?;

        // reload to see balances after exit
        ctx.accounts.seller_bull_ata.reload()?;
        ctx.accounts.seller_bear_ata.reload()?;

        let remaining_bull = ctx.accounts.seller_bull_ata.amount;
        let remaining_bear = ctx.accounts.seller_bear_ata.amount;

        let ur = &mut ctx.accounts.user_registry;
        if let Some(pos) = ur.get_position_mut(pool.key()) {
            if remaining_bull == 0 {
                pos.bull_avg_price = 0;
            }
            if remaining_bear == 0 {
                pos.bear_avg_price = 0;
            }
        }
        ur.remove_position_if_empty(pool.key(), remaining_bull, remaining_bear);

        emit!(TokensRedeemed {
            pool: pool.key(),
            token_mint: ctx.accounts.bear_mint.key(),
            token_name: pool.bear_name.clone(),
            token_symbol: pool.bear_symbol.clone(),
            seller: ctx.accounts.seller.key(),
            tokens_burned: amount_out_tokens,
            quote_returned: net_amount,
        });

        Ok(())
    }
}

// -------------------------------------------------------------------------------------
// Account Contexts
// -------------------------------------------------------------------------------------

// STEP 1: init_pool
#[derive(Accounts)]
pub struct InitPool<'info> {
    #[account(mut)]
    pub payer: Signer<'info>,

    /// CHECK: only used to assert payer == pool_creator
    pub pool_creator: UncheckedAccount<'info>,

    // Global registry PDA (already initialized elsewhere)
    #[account(
        mut,
        seeds = [b"pool_registry"],
        bump
    )]
    pub registry: Account<'info, PoolRegistryAccount>,

    // New pool account
    #[account(
        init,
        payer = payer,
        space = 8 + // disc
        4 +
        64 + // name
        4 +
        256 + // description
        4 +
        32 + // bull_name
        4 +
        10 + // bull_symbol
        4 +
        32 + // bear_name
        4 +
        10 + // bear_symbol
        4 + // pair_id
        32 + // asset_address
        32 + // quote_mint
        8 + // current_price
        32 + // chainlink_feed
        32 + // bull_mint
        32 + // bear_mint
        32 + // bull_vault
        32 + // bear_vault
        8 +
        8 +
        8 +
        8 + // fees
        32 + // pool_creator
        1 // pool_signer_bump
    )]
    pub pool: Account<'info, PoolAccount>,

    /// CHECK: PDA signer that will own vaults/mints
    #[account(seeds = [b"pool_signer", pool.key().as_ref()], bump)]
    pub pool_signer: UncheckedAccount<'info>,

    // Bull & Bear mints (authority = pool_signer)
    #[account(
        init,
        payer = payer,
        seeds = [b"bull_mint", pool.key().as_ref()],
        bump,
        mint::decimals = OUTCOME_TOKEN_DECIMALS,
        mint::authority = pool_signer,
        mint::freeze_authority = pool_signer
    )]
    pub bull_mint: Account<'info, Mint>,

    #[account(
        init,
        payer = payer,
        seeds = [b"bear_mint", pool.key().as_ref()],
        bump,
        mint::decimals = OUTCOME_TOKEN_DECIMALS,
        mint::authority = pool_signer,
        mint::freeze_authority = pool_signer
    )]
    pub bear_mint: Account<'info, Mint>,

    // Quote token mint (USDC/etc)
    pub quote_mint: Account<'info, Mint>,

    // Vaults for each side (hold quote token)
    #[account(
        init,
        payer = payer,
        seeds = [b"bull_vault", pool.key().as_ref()],
        bump,
        token::mint = quote_mint,
        token::authority = pool_signer
    )]
    pub bull_vault: Account<'info, TokenAccount>,

    #[account(
        init,
        payer = payer,
        seeds = [b"bear_vault", pool.key().as_ref()],
        bump,
        token::mint = quote_mint,
        token::authority = pool_signer
    )]
    pub bear_vault: Account<'info, TokenAccount>,

    /// CHECK: Chainlink feed to bind this pool to (e.g. SOL/USD).
    /// We verify owner/format on-chain.
    pub chainlink_feed: UncheckedAccount<'info>,

    pub token_program: Program<'info, Token>,
    pub system_program: Program<'info, System>,
    pub rent: Sysvar<'info, Rent>,
}

// STEP 2: seed_liquidity
#[derive(Accounts)]
pub struct SeedLiquidity<'info> {
    #[account(mut)]
    pub payer: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, PoolAccount>,

    /// CHECK: PDA signer
    #[account(seeds = [b"pool_signer", pool.key().as_ref()], bump = pool.pool_signer_bump)]
    pub pool_signer: UncheckedAccount<'info>,

    #[account(mut)]
    pub bull_mint: Account<'info, Mint>,

    #[account(mut)]
    pub bear_mint: Account<'info, Mint>,

    #[account(mut)]
    pub bull_vault: Account<'info, TokenAccount>,

    #[account(mut)]
    pub bear_vault: Account<'info, TokenAccount>,

    #[account(
        mut,
        constraint = funding_ata.owner == payer.key()
    )]
    pub funding_ata: Account<'info, TokenAccount>,

    // payer receives bull tokens here
    #[account(
        init,
        payer = payer,
        associated_token::mint = bull_mint,
        associated_token::authority = payer
    )]
    pub payer_bull_ata: Account<'info, TokenAccount>,

    // payer receives bear tokens here
    #[account(
        init,
        payer = payer,
        associated_token::mint = bear_mint,
        associated_token::authority = payer
    )]
    pub payer_bear_ata: Account<'info, TokenAccount>,

    // creator's registry record
    #[account(
        mut,
        seeds=[b"user_registry", payer.key().as_ref()],
        bump
    )]
    pub user_registry: Account<'info, UserRegistryAccount>,

    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, System>,
    pub rent: Sysvar<'info, Rent>,
}

// Manual oracle sync / rebalance
#[derive(Accounts)]
pub struct RebalancePool<'info> {
    #[account(mut)]
    pub authority: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, PoolAccount>,

    /// CHECK: PDA signer
    #[account(seeds = [b"pool_signer", pool.key().as_ref()], bump = pool.pool_signer_bump)]
    pub pool_signer: UncheckedAccount<'info>,

    #[account(mut)]
    pub bull_vault: Account<'info, TokenAccount>,

    #[account(mut)]
    pub bear_vault: Account<'info, TokenAccount>,

    /// CHECK: Chainlink feed (must match pool.chainlink_feed)
    pub chainlink_feed: UncheckedAccount<'info>,

    pub token_program: Program<'info, Token>,
}

// BUY BULL
#[derive(Accounts)]
pub struct PurchaseBull<'info> {
    #[account(mut)]
    pub buyer: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, PoolAccount>,

    /// CHECK: PDA signer for vault/mint authority
    #[account(seeds = [b"pool_signer", pool.key().as_ref()], bump = pool.pool_signer_bump)]
    pub pool_signer: UncheckedAccount<'info>,

    #[account(mut)]
    pub bull_mint: Account<'info, Mint>,

    #[account(mut)]
    pub bull_vault: Account<'info, TokenAccount>,

    #[account(mut)]
    pub bear_vault: Account<'info, TokenAccount>,

    #[account(
        mut,
        constraint = buyer_quote_ata.owner == buyer.key(),
    )]
    pub buyer_quote_ata: Account<'info, TokenAccount>,

    #[account(mut)]
    pub protocol_fee_ata: Account<'info, TokenAccount>,

    #[account(mut)]
    pub creator_quote_ata: Account<'info, TokenAccount>,

    #[account(
        mut,
        constraint = buyer_bull_ata.owner == buyer.key(),
    )]
    pub buyer_bull_ata: Account<'info, TokenAccount>,

    #[account(
        mut,
        seeds=[b"user_registry", buyer.key().as_ref()],
        bump
    )]
    pub user_registry: Account<'info, UserRegistryAccount>,

    /// CHECK: Chainlink feed
    pub chainlink_feed: UncheckedAccount<'info>,

    pub token_program: Program<'info, Token>,
}

// BUY BEAR
#[derive(Accounts)]
pub struct PurchaseBear<'info> {
    #[account(mut)]
    pub buyer: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, PoolAccount>,

    /// CHECK
    #[account(seeds = [b"pool_signer", pool.key().as_ref()], bump = pool.pool_signer_bump)]
    pub pool_signer: UncheckedAccount<'info>,

    #[account(mut)]
    pub bear_mint: Account<'info, Mint>,

    #[account(mut)]
    pub bull_vault: Account<'info, TokenAccount>,

    #[account(mut)]
    pub bear_vault: Account<'info, TokenAccount>,

    #[account(
        mut,
        constraint = buyer_quote_ata.owner == buyer.key(),
    )]
    pub buyer_quote_ata: Account<'info, TokenAccount>,

    #[account(mut)]
    pub protocol_fee_ata: Account<'info, TokenAccount>,

    #[account(mut)]
    pub creator_quote_ata: Account<'info, TokenAccount>,

    #[account(
        mut,
        constraint = buyer_bear_ata.owner == buyer.key(),
    )]
    pub buyer_bear_ata: Account<'info, TokenAccount>,

    #[account(
        mut,
        seeds=[b"user_registry", buyer.key().as_ref()],
        bump
    )]
    pub user_registry: Account<'info, UserRegistryAccount>,

    /// CHECK: Chainlink feed
    pub chainlink_feed: UncheckedAccount<'info>,

    pub token_program: Program<'info, Token>,
}

// REDEEM BULL
#[derive(Accounts)]
pub struct RedeemBull<'info> {
    #[account(mut)]
    pub seller: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, PoolAccount>,

    /// CHECK
    #[account(seeds = [b"pool_signer", pool.key().as_ref()], bump = pool.pool_signer_bump)]
    pub pool_signer: UncheckedAccount<'info>,

    #[account(mut)]
    pub bull_mint: Account<'info, Mint>,

    #[account(mut)]
    pub bull_vault: Account<'info, TokenAccount>,

    #[account(mut)]
    pub bear_vault: Account<'info, TokenAccount>,

    #[account(
        mut,
        constraint = seller_quote_ata.owner == seller.key(),
    )]
    pub seller_quote_ata: Account<'info, TokenAccount>,

    #[account(mut)]
    pub protocol_fee_ata: Account<'info, TokenAccount>,

    #[account(mut)]
    pub creator_quote_ata: Account<'info, TokenAccount>,

    #[account(
        mut,
        constraint = seller_bull_ata.owner == seller.key(),
    )]
    pub seller_bull_ata: Account<'info, TokenAccount>,

    #[account(
        mut,
        constraint = seller_bear_ata.owner == seller.key(),
    )]
    pub seller_bear_ata: Account<'info, TokenAccount>,

    #[account(
        mut,
        seeds=[b"user_registry", seller.key().as_ref()],
        bump
    )]
    pub user_registry: Account<'info, UserRegistryAccount>,

    /// CHECK
    pub chainlink_feed: UncheckedAccount<'info>,

    pub token_program: Program<'info, Token>,
}

// REDEEM BEAR
#[derive(Accounts)]
pub struct RedeemBear<'info> {
    #[account(mut)]
    pub seller: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, PoolAccount>,

    /// CHECK
    #[account(seeds = [b"pool_signer", pool.key().as_ref()], bump = pool.pool_signer_bump)]
    pub pool_signer: UncheckedAccount<'info>,

    #[account(mut)]
    pub bear_mint: Account<'info, Mint>,

    #[account(mut)]
    pub bull_vault: Account<'info, TokenAccount>,

    #[account(mut)]
    pub bear_vault: Account<'info, TokenAccount>,

    #[account(
        mut,
        constraint = seller_quote_ata.owner == seller.key(),
    )]
    pub seller_quote_ata: Account<'info, TokenAccount>,

    #[account(mut)]
    pub protocol_fee_ata: Account<'info, TokenAccount>,

    #[account(mut)]
    pub creator_quote_ata: Account<'info, TokenAccount>,

    #[account(
        mut,
        constraint = seller_bull_ata.owner == seller.key(),
    )]
    pub seller_bull_ata: Account<'info, TokenAccount>,

    #[account(
        mut,
        constraint = seller_bear_ata.owner == seller.key(),
    )]
    pub seller_bear_ata: Account<'info, TokenAccount>,

    #[account(
        mut,
        seeds=[b"user_registry", seller.key().as_ref()],
        bump
    )]
    pub user_registry: Account<'info, UserRegistryAccount>,

    /// CHECK
    pub chainlink_feed: UncheckedAccount<'info>,

    pub token_program: Program<'info, Token>,
}
