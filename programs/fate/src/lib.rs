use anchor_lang::prelude::*;
use anchor_spl::{
    associated_token::AssociatedToken,
    token::{ self, Burn, Mint, MintTo, Token, TokenAccount, Transfer },
};
use chainlink_solana as chainlink;
use std::str::FromStr;

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
pub const PRECISION_SCALE: u64 = 1_000_000_000; // same role as in Sui
pub const STABILITY_WALLET: &str = "9JvZLhnbYpz6XJThyU5t8rVgkCjs79p7xH8CkRWniJg";

// Chainlink OCR2 program on Solana
// (this is the canonical Chainlink program ID published in Chainlink docs)
pub const CHAINLINK_PROGRAM_ID_STR: &str = "HEvSKofvBgfaexv23kMabbYqxasxU3mQ4ibBMEmJWHny";

pub fn chainlink_program_pubkey() -> Pubkey {
    Pubkey::from_str(CHAINLINK_PROGRAM_ID_STR).unwrap()
}

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
}

// -------------------------------------------------------------------------------------
// On-chain State
// -------------------------------------------------------------------------------------

// === POOL ===
#[account]
pub struct PoolAccount {
    pub name: String,
    pub description: String,
    pub bull_name: String,
    pub bull_symbol: String,
    pub bear_name: String,
    pub bear_symbol: String,
    pub pair_id: u32,
    pub asset_address: Pubkey,
    pub quote_mint: Pubkey,
    pub current_price: u64, // scaled to 1_000_000 internal precision
    pub bull_mint: Pubkey,
    pub bear_mint: Pubkey,
    pub bull_vault: Pubkey,
    pub bear_vault: Pubkey,

    // NEW: Chainlink oracle binding
    pub chainlink_feed: Pubkey,
    pub chainlink_program: Pubkey,

    pub protocol_fee: u64,
    pub mint_fee: u64,
    pub burn_fee: u64,
    pub pool_creator_fee: u64,
    pub pool_creator: Pubkey,
    pub pool_signer_bump: u8,
}

// === GLOBAL POOL REGISTRY ===
// One PDA that tracks all pool pubkeys.
#[account]
pub struct PoolRegistryAccount {
    pub pools: Vec<Pubkey>,
}

// Allow up to this many pools tracked without realloc.
// You can adjust this up/down and recreate the registry PDA on testnet/dev.
pub const MAX_POOLS: usize = 512;

impl PoolRegistryAccount {
    pub const INIT_SPACE: usize =
        8 + // discriminator
        4 + // Vec len
        32 * MAX_POOLS; // pool pubkeys

    pub fn push_unique(&mut self, pool: Pubkey) {
        if !self.pools.iter().any(|p| *p == pool) {
            self.pools.push(pool);
        }
    }
}

// === PER-USER REGISTRY ===
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

// how many pools we let a single wallet track without realloc
pub const MAX_USER_POSITIONS: usize = 128;

impl UserRegistryAccount {
    pub const INIT_SPACE: usize =
        8 + // disc
        32 + // user pubkey
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
    pub initial_price: u64,
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
// Math / Pricing / Fee Helpers
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

// Convert Chainlink price feed answer to our internal scaled u64 price (6 decimal places).
fn normalize_chainlink_price(
    answer: i128,
    feed_decimals: u32,
    precision: u64 // e.g. 1_000_000 to store price * 10^6
) -> Result<u64> {
    // Chainlink answers should be >= 0 for normal market pairs
    require!(answer >= 0, PredictionError::ZeroPrice);

    // cast safely
    let unsigned_answer = answer as u128;

    // compute 10^feed_decimals
    let mut divisor: u128 = 1;
    for _ in 0..feed_decimals {
        divisor = divisor.saturating_mul(10);
    }

    // scale into our precision
    let scaled = unsigned_answer.saturating_mul(precision as u128).saturating_div(divisor);

    Ok(scaled as u64)
}

// compute how pool should redistribute reserves based on price move
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

// fee split logic
fn compute_fee_breakdown(
    amount: u64,
    protocol_fee_bps: u64,
    specific_fee_bps: u64, // mint_fee when buying, burn_fee when selling
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

// called by multiple instructions to re-sync bull_vault/bear_vault if price moved
fn do_rebalance<'info>(
    pool: &mut Account<'info, PoolAccount>,

    // NEW: Chainlink oracle accounts
    chainlink_program: &UncheckedAccount<'info>,
    chainlink_feed: &UncheckedAccount<'info>,

    // vaults
    bull_vault: &Account<'info, TokenAccount>,
    bear_vault: &Account<'info, TokenAccount>,

    // signer + token program
    pool_signer: &UncheckedAccount<'info>,
    token_program: &Program<'info, Token>
) -> Result<()> {
    // safety: enforce canonical oracle for this pool
    require_keys_eq!(
        chainlink_program.key(),
        pool.chainlink_program,
        PredictionError::Unauthorized
    );
    require_keys_eq!(chainlink_feed.key(), pool.chainlink_feed, PredictionError::Unauthorized);

    // fetch latest Chainlink round data for this feed
    let round = chainlink::latest_round_data(
        chainlink_program.to_account_info(),
        chainlink_feed.to_account_info()
    )?;
    let decimals = chainlink::decimals(
        chainlink_program.to_account_info(),
        chainlink_feed.to_account_info()
    )?;

    // normalize into our 6-decimal fixed point
    let new_price = normalize_chainlink_price(round.answer, u32::from(decimals), 1_000_000)?;

    let old_price = pool.current_price;
    if new_price == old_price {
        // no change
        return Ok(());
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

    // shift funds bear -> bull or bull -> bear to match new target split
    if target_bull > old_bull_reserve {
        // pull from bear_vault -> bull_vault
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
        // pull from bull_vault -> bear_vault
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

// Step 1 of pool creation (no liquidity yet).
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

// Step 2 of pool creation: seed initial liquidity and mint initial bull/bear.
#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub struct SeedLiquidityArgs {
    pub initial_liquidity: u64,
}

// -------------------------------------------------------------------------------------
// Program entrypoints
// -------------------------------------------------------------------------------------

#[program]
pub mod fate {
    use super::*;

    // === POOL CREATION: STEP 1 ===
    // Initializes the PoolAccount, vaults, mints, sets fees, records pool in registry.
    // Does NOT move funds or mint initial bull/bear yet.
    pub fn init_pool(ctx: Context<InitPool>, args: InitPoolArgs) -> Result<()> {
        // pool_creator must match payer
        require_keys_eq!(
            ctx.accounts.pool_creator.key(),
            ctx.accounts.payer.key(),
            PredictionError::Unauthorized
        );

        // clamp fees like Sui logic
        let mut protocol_fee = args.protocol_fee_param;
        let mut pool_creator_fee = args.pool_creator_fee_param;
        let mut mint_fee = args.mint_fee_param;
        let mut burn_fee = args.burn_fee_param;

        pool_creator_fee = pool_creator_fee.min(MAX_FEE);
        protocol_fee = protocol_fee.max(pool_creator_fee).max(MIN_PROTOCOL_FEE).min(MAX_FEE);

        mint_fee = mint_fee.min(MAX_FEE);
        burn_fee = burn_fee.min(MAX_FEE);
        pool_creator_fee = pool_creator_fee.min(MAX_FEE);

        // safety: supplied Chainlink program should be canonical
        require_keys_eq!(
            ctx.accounts.chainlink_program.key(),
            chainlink_program_pubkey(),
            PredictionError::Unauthorized
        );

        // read initial price from Chainlink
        let round = chainlink::latest_round_data(
            ctx.accounts.chainlink_program.to_account_info(),
            ctx.accounts.chainlink_feed.to_account_info()
        )?;
        let decimals = chainlink::decimals(
            ctx.accounts.chainlink_program.to_account_info(),
            ctx.accounts.chainlink_feed.to_account_info()
        )?;

        let initial_price = normalize_chainlink_price(
            round.answer,
            u32::from(decimals),
            1_000_000
        )?;

        let pool = &mut ctx.accounts.pool;

        // fill metadata
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

        pool.bull_mint = ctx.accounts.bull_mint.key();
        pool.bear_mint = ctx.accounts.bear_mint.key();
        pool.bull_vault = ctx.accounts.bull_vault.key();
        pool.bear_vault = ctx.accounts.bear_vault.key();

        // bind oracle
        pool.chainlink_feed = ctx.accounts.chainlink_feed.key();
        pool.chainlink_program = ctx.accounts.chainlink_program.key();

        pool.protocol_fee = protocol_fee;
        pool.mint_fee = mint_fee;
        pool.burn_fee = burn_fee;
        pool.pool_creator_fee = pool_creator_fee;
        pool.pool_creator = ctx.accounts.pool_creator.key();

        pool.pool_signer_bump = ctx.bumps.pool_signer;

        // register pool globally
        ctx.accounts.registry.push_unique(pool.key());

        // Emit creation event
        emit!(PoolCreated {
            pool: pool.key(),
            name: pool.name.clone(),
            creator: ctx.accounts.payer.key(),
            initial_price,
        });

        Ok(())
    }

    // === POOL CREATION: STEP 2 ===
    // Seeds the vaults with initial liquidity and mints initial bull/bear tokens to creator.
    // Also bootstraps that creator's UserRegistryAccount position.
    pub fn seed_liquidity(ctx: Context<SeedLiquidity>, args: SeedLiquidityArgs) -> Result<()> {
        require!(args.initial_liquidity > 0, PredictionError::InvalidAmount);
        require!(
            ctx.accounts.funding_ata.amount >= args.initial_liquidity,
            PredictionError::InsufficientBalance
        );

        let pool = &mut ctx.accounts.pool;

        // only the pool.creator can seed first liquidity
        require_keys_eq!(
            pool.pool_creator,
            ctx.accounts.payer.key(),
            PredictionError::Unauthorized
        );

        // sanity: funding_ata must be quote mint of the pool
        require_keys_eq!(
            ctx.accounts.funding_ata.mint,
            pool.quote_mint,
            PredictionError::Unauthorized
        );

        // split liquidity half-half between bull_vault and bear_vault
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

        // calculate how many bull/bear tokens to mint to creator
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

        // sign with pool_signer PDA
        let pool_key = pool.key();
        let signer_seeds: &[&[u8]] = &[b"pool_signer", pool_key.as_ref(), &[pool.pool_signer_bump]];

        // mint bull tokens to payer
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

        // mint bear tokens to payer
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

        // record creator's position + avg prices
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

    // === MANUAL REBALANCE ===
    // Creator can manually poke oracle sync / reserve rebalance.
    pub fn rebalance_pool(ctx: Context<RebalancePool>) -> Result<()> {
        let pool = &mut ctx.accounts.pool;

        // only pool.creator allowed to do manual rebalance
        require_keys_eq!(
            ctx.accounts.authority.key(),
            pool.pool_creator,
            PredictionError::Unauthorized
        );

        do_rebalance(
            pool,
            &ctx.accounts.chainlink_program,
            &ctx.accounts.chainlink_feed,
            &ctx.accounts.bull_vault,
            &ctx.accounts.bear_vault,
            &ctx.accounts.pool_signer,
            &ctx.accounts.token_program
        )
    }

    // === BUY BULL ===
    // User sends quote into bull_vault, pays fees, and receives bull tokens.
    pub fn purchase_bull(ctx: Context<PurchaseBull>, quote_amount_in: u64) -> Result<()> {
        require!(quote_amount_in > 0, PredictionError::InvalidAmount);
        let pool = &mut ctx.accounts.pool;

        // sanity checks: protocol fee destination + creator fee destination
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

        // rebalance before trading
        do_rebalance(
            pool,
            &ctx.accounts.chainlink_program,
            &ctx.accounts.chainlink_feed,
            &ctx.accounts.bull_vault,
            &ctx.accounts.bear_vault,
            &ctx.accounts.pool_signer,
            &ctx.accounts.token_program
        )?;

        // snapshot BEFORE we move funds
        let reserve_before = ctx.accounts.bull_vault.amount;
        let total_supply_before = ctx.accounts.bull_mint.supply;
        let user_old_balance = ctx.accounts.buyer_bull_ata.amount;

        // fee split (mint_fee applies here)
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

        // mint_fee portion -> bear_vault
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

        // figure out how many bull tokens to mint
        let (mint_amount, price_per_token) = calculate_mint_amount(
            reserve_before,
            total_supply_before,
            net_amount
        )?;

        // mint bull tokens -> buyer_bull_ata, signed by pool_signer PDA
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

        // update buyer's avg cost in UserRegistryAccount
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

    // === BUY BEAR ===
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
            ctx.accounts.buyer_bear_ata.mint,
            pool.bear_mint,
            PredictionError::Unauthorized
        );

        do_rebalance(
            pool,
            &ctx.accounts.chainlink_program,
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

        // mint_fee portion -> bull_vault (other side)
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

        // net -> bear_vault
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

    // === REDEEM BULL ===
    pub fn redeem_bull(ctx: Context<RedeemBull>, amount_out_tokens: u64) -> Result<()> {
        require!(amount_out_tokens > 0, PredictionError::InvalidAmount);
        let pool = &mut ctx.accounts.pool;

        // required fee receivers
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

        // sanity: quote destinations must match pool.quote_mint
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

        // sanity: burning from seller_bull_ata must be bull mint
        require_keys_eq!(
            ctx.accounts.seller_bull_ata.mint,
            pool.bull_mint,
            PredictionError::Unauthorized
        );

        // we also read seller_bear_ata later to know if user fully exited
        require_keys_eq!(
            ctx.accounts.seller_bear_ata.mint,
            pool.bear_mint,
            PredictionError::Unauthorized
        );

        // rebalance before redemption
        do_rebalance(
            pool,
            &ctx.accounts.chainlink_program,
            &ctx.accounts.chainlink_feed,
            &ctx.accounts.bull_vault,
            &ctx.accounts.bear_vault,
            &ctx.accounts.pool_signer,
            &ctx.accounts.token_program
        )?;

        // seller must have enough bull to burn
        require!(
            ctx.accounts.seller_bull_ata.amount >= amount_out_tokens,
            PredictionError::InsufficientBalance
        );

        // can't burn 100% of supply
        let total_supply_before = ctx.accounts.bull_mint.supply;
        require!(total_supply_before > 0, PredictionError::ZeroTotalSupply);
        require!(total_supply_before > amount_out_tokens, PredictionError::InvalidAmount);

        // compute payout
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

        // burn user's bull tokens
        token::burn(
            CpiContext::new(ctx.accounts.token_program.to_account_info(), Burn {
                mint: ctx.accounts.bull_mint.to_account_info(),
                from: ctx.accounts.seller_bull_ata.to_account_info(),
                authority: ctx.accounts.seller.to_account_info(),
            }),
            amount_out_tokens
        )?;

        // fee breakdown for redemption (burn_fee applies here)
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

        // burn_fee portion -> bear_vault (other side)
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

        // pool_creator_fee -> creator_quote_ata
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

        // now reload ATAs to see how much user still holds
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

    // === REDEEM BEAR ===
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

        // burning from bear side
        require_keys_eq!(
            ctx.accounts.seller_bear_ata.mint,
            pool.bear_mint,
            PredictionError::Unauthorized
        );
        // also check seller_bull_ata to know if user exited fully
        require_keys_eq!(
            ctx.accounts.seller_bull_ata.mint,
            pool.bull_mint,
            PredictionError::Unauthorized
        );

        do_rebalance(
            pool,
            &ctx.accounts.chainlink_program,
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

        // reload to see balances after burn/transfer
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
//
// Note: registry PDA and user_registry PDA are NOT created here.
// You need to create & fund them in separate setup instructions using `INIT_SPACE`.
#[derive(Accounts)]
pub struct InitPool<'info> {
    #[account(mut)]
    pub payer: Signer<'info>,

    /// CHECK: only used for key equality with payer
    pub pool_creator: UncheckedAccount<'info>,

    // Global registry PDA (already initialized elsewhere).
    #[account(
        mut,
        seeds = [b"pool_registry"],
        bump
    )]
    pub registry: Account<'info, PoolRegistryAccount>,

    // New pool account.
    #[account(
        init,
        payer = payer,
        space = 8 + // discriminator
        4 +
        64 + // name string prefix+data (Anchor: 4 + len)
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
        4 + // pair_id u32
        32 + // asset_address Pubkey
        32 + // quote_mint Pubkey
        8 + // current_price u64
        32 + // bull_mint Pubkey
        32 + // bear_mint Pubkey
        32 + // bull_vault Pubkey
        32 + // bear_vault Pubkey
        32 + // chainlink_feed Pubkey
        32 + // chainlink_program Pubkey
        8 + // protocol_fee u64
        8 + // mint_fee u64
        8 + // burn_fee u64
        8 + // pool_creator_fee u64
        32 + // pool_creator Pubkey
        1 // pool_signer_bump u8
    )]
    pub pool: Account<'info, PoolAccount>,

    /// CHECK: PDA authority for vaults/mints
    #[account(seeds = [b"pool_signer", pool.key().as_ref()], bump)]
    pub pool_signer: UncheckedAccount<'info>,

    // Bull and bear mints (created here, authority = pool_signer)
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

    // Quote token mint (USDC/wSOL/etc.)
    pub quote_mint: Account<'info, Mint>,

    // Vaults for each side (created here, owned by pool_signer, hold quote token)
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

    // NEW: Chainlink oracle feed account (e.g. SOL/USD feed)
    /// CHECK: we only read it via Chainlink CPI, don't write to it
    pub chainlink_feed: UncheckedAccount<'info>,

    // NEW: Chainlink OCR2 program (must equal CHAINLINK_PROGRAM_ID_STR)
    /// CHECK: verified in handler
    pub chainlink_program: UncheckedAccount<'info>,

    pub token_program: Program<'info, Token>,
    pub system_program: Program<'info, System>,
    pub rent: Sysvar<'info, Rent>,
}

// STEP 2: seed_liquidity
// Seeds bull_vault & bear_vault from payer, mints initial bull/bear to payer,
// and records payer's position in user_registry.
#[derive(Accounts)]
pub struct SeedLiquidity<'info> {
    #[account(mut)]
    pub payer: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, PoolAccount>,

    /// CHECK: same PDA signer as in init_pool
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

    // payer receives bull tokens here; we create the ATA now
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

    // creator's user registry (must already exist / be initialized externally)
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

// Manual oracle sync / reserve rebalance
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

    /// CHECK: Chainlink feed account (must match pool.chainlink_feed)
    pub chainlink_feed: UncheckedAccount<'info>,

    /// CHECK: Chainlink OCR2 program (must match pool.chainlink_program)
    pub chainlink_program: UncheckedAccount<'info>,

    pub token_program: Program<'info, Token>,
}

// BUY BULL
#[derive(Accounts)]
pub struct PurchaseBull<'info> {
    #[account(mut)]
    pub buyer: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, PoolAccount>,

    /// CHECK: PDA signer that can move vault funds and mint bull/bear
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

    /// CHECK: Chainlink feed (must equal pool.chainlink_feed)
    pub chainlink_feed: UncheckedAccount<'info>,

    /// CHECK: Chainlink OCR2 program (must equal pool.chainlink_program)
    pub chainlink_program: UncheckedAccount<'info>,

    pub token_program: Program<'info, Token>,
}

// BUY BEAR
#[derive(Accounts)]
pub struct PurchaseBear<'info> {
    #[account(mut)]
    pub buyer: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, PoolAccount>,

    /// CHECK: PDA signer
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

    /// CHECK: Chainlink OCR2 program
    pub chainlink_program: UncheckedAccount<'info>,

    pub token_program: Program<'info, Token>,
}

// REDEEM BULL
#[derive(Accounts)]
pub struct RedeemBull<'info> {
    #[account(mut)]
    pub seller: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, PoolAccount>,

    /// CHECK: PDA signer
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

    /// CHECK: Chainlink feed
    pub chainlink_feed: UncheckedAccount<'info>,

    /// CHECK: Chainlink OCR2 program
    pub chainlink_program: UncheckedAccount<'info>,

    pub token_program: Program<'info, Token>,
}

// REDEEM BEAR
#[derive(Accounts)]
pub struct RedeemBear<'info> {
    #[account(mut)]
    pub seller: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, PoolAccount>,

    /// CHECK: PDA signer
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

    /// CHECK: Chainlink feed
    pub chainlink_feed: UncheckedAccount<'info>,

    /// CHECK: Chainlink OCR2 program
    pub chainlink_program: UncheckedAccount<'info>,

    pub token_program: Program<'info, Token>,
}
