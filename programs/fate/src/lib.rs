use anchor_lang::prelude::*;
use anchor_spl::{
    associated_token::AssociatedToken,
    token::{self, Burn, Mint, MintTo, Token, TokenAccount, Transfer},
};
use std::cmp::{max, min};

// =======================================================
// ================ Constants & Errors ===================
// =======================================================

pub const MAX_FEE: u64 = 1000;            // 10.00% assuming 1e4 denom
pub const MIN_PROTOCOL_FEE: u64 = 30;     // 0.30%
pub const FEE_DENOMINATOR: u64 = 10_000;  // basis points denominator
pub const PRECISION_SCALE: u64 = 1_000_000_000; // 1e9, same as Sui code
pub const OUTCOME_TOKEN_DECIMALS: u8 = 9; // you can change this if you want
pub const USER_POOLS_INIT_CAPACITY: usize = 32;
pub const POOLS_PER_PAGE: usize = 50;

// Hardcoded protocol fee receiver address, equivalent to
// STABLE_ORDER_ADDRESS in Sui.
pub const STABLE_ORDER_BYTES: [u8; 32] = [
    0x3c, 0x89, 0x3e, 0xb6, 0x8f, 0xfd, 0x85, 0x77,
    0xe7, 0xe6, 0x9d, 0x2c, 0x4a, 0x62, 0xfe, 0xb9,
    0xea, 0xba, 0xf7, 0x5e, 0x39, 0x35, 0xb7, 0x7a,
    0x19, 0xbb, 0x21, 0x85, 0xd7, 0xcd, 0x6d, 0xfa,
];
pub fn stable_order_address() -> Pubkey {
    Pubkey::new_from_array(STABLE_ORDER_BYTES)
}

#[error_code]
pub enum PredictionError {
    #[msg("Invalid amount")]
    InvalidAmount,
    #[msg("Insufficient balance")]
    InsufficientBalance,
    #[msg("Invalid fee")]
    InvalidFee,
    #[msg("Not owner")]
    NotOwner,
    #[msg("Invalid outcome")]
    InvalidOutcome,
    #[msg("Zero total supply")]
    ZeroTotalSupply,
    #[msg("Unauthorized")]
    Unauthorized,
    #[msg("Zero price")]
    ZeroPrice,
    #[msg("Math overflow")]
    MathOverflow,
}

// =======================================================
// ===================== Accounts ========================
// =======================================================

#[account]
pub struct Pool {
    // Human metadata
    pub name: String,          // <= 64 bytes recommended
    pub description: String,   // <= 256 bytes recommended

    pub bull_name: String,     // e.g. "BTC Bull"
    pub bull_symbol: String,   // e.g. "BTC↑"
    pub bear_name: String,     // e.g. "BTC Bear"
    pub bear_symbol: String,   // e.g. "BTC↓"

    // Oracle info
    pub pair_id: u32,
    pub asset_address: Pubkey, // arbitrary asset ref (like underlying)
    pub quote_mint: Pubkey,    // SPL mint used as quote unit (like USDC)
    pub current_price: u64,    // normalized oracle price (scaled by 1_000_000)

    // Outcome token mints
    pub bull_mint: Pubkey,
    pub bear_mint: Pubkey,

    // Vaults (token accounts holding quote_mint)
    pub bull_vault: Pubkey,
    pub bear_vault: Pubkey,

    // Fees (basis points)
    pub protocol_fee: u64,
    pub mint_fee: u64,
    pub burn_fee: u64,
    pub pool_creator_fee: u64,

    // Where creator fee is sent
    pub pool_creator: Pubkey,

    // PDA bump for pool_signer
    pub pool_signer_bump: u8,
}

// Sizing hint so we can `init` with enough space up front.
impl Pool {
    pub const NAME_MAX: usize = 64;
    pub const DESC_MAX: usize = 256;
    pub const OUTCOME_NAME_MAX: usize = 32;
    pub const OUTCOME_SYMBOL_MAX: usize = 10;

    // discriminator (8)
    // + name (4 + 64)
    // + desc (4 + 256)
    // + bull_name (4 + 32)
    // + bull_symbol (4 + 10)
    // + bear_name (4 + 32)
    // + bear_symbol (4 + 10)
    // + pair_id (4)
    // + asset_address (32)
    // + quote_mint (32)
    // + current_price (8)
    // + bull_mint (32)
    // + bear_mint (32)
    // + bull_vault (32)
    // + bear_vault (32)
    // + protocol_fee (8)
    // + mint_fee (8)
    // + burn_fee (8)
    // + pool_creator_fee (8)
    // + pool_creator (32)
    // + pool_signer_bump (1)
    pub const INIT_SPACE: usize = 8
        + 4 + Self::NAME_MAX
        + 4 + Self::DESC_MAX
        + 4 + Self::OUTCOME_NAME_MAX
        + 4 + Self::OUTCOME_SYMBOL_MAX
        + 4 + Self::OUTCOME_NAME_MAX
        + 4 + Self::OUTCOME_SYMBOL_MAX
        + 4
        + 32
        + 32
        + 8
        + 32
        + 32
        + 32
        + 32
        + 8
        + 8
        + 8
        + 8
        + 32
        + 1;
}

// Per (user, pool) info that Move tracked in dynamic fields:
// - average purchase price per outcome
//   (so you can show effective entry price / PnL)
#[account]
pub struct UserPosition {
    pub pool: Pubkey,
    pub user: Pubkey,

    pub bull_avg_price: u64, // scaled by PRECISION_SCALE
    pub bear_avg_price: u64,
}

impl UserPosition {
    pub const INIT_SPACE: usize = 8 // disc
        + 32 // pool
        + 32 // user
        + 8  // bull_avg_price
        + 8; // bear_avg_price
}

// A lightweight "which pools is this user in?" list,
// replacing your paginated UserRegistry.
#[account]
pub struct UserPools {
    pub user: Pubkey,
    pub pools: Vec<Pubkey>, // we'll cap initial space, you can realloc later
}

impl UserPools {
    pub const INIT_SPACE: usize = 8 // disc
        + 32 // user pubkey
        + 4  // vec len prefix
        + 32 * USER_POOLS_INIT_CAPACITY; // room for N pool keys

    pub fn push_unique(&mut self, pool: Pubkey) {
        if !self.pools.contains(&pool) {
            self.pools.push(pool);
        }
    }

    pub fn remove_if_present(&mut self, pool: Pubkey) {
        if let Some(idx) = self.pools.iter().position(|p| *p == pool) {
            self.pools.swap_remove(idx);
        }
    }
}

// Global-ish registry of pools. Mirrors PoolRegistry + paging idea.
// We're keeping it to a single vector for now (capacity ~50).
#[account]
pub struct PoolRegistry {
    pub pools: Vec<Pubkey>,
}

impl PoolRegistry {
    pub const INIT_SPACE: usize = 8  // disc
        + 4                          // vec len
        + 32 * POOLS_PER_PAGE;       // reserve room for ~50 pools
}

// Oracle feed stand-in for Supra. In practice you'd read whatever layout
// Supra exposes on Solana and validate signatures / slots.
#[account]
pub struct OraclePriceFeed {
    pub pair_id: u32,
    pub value: u128,   // raw oracle value
    pub decimals: u8,  // how many decimal places in `value`
    // you could also store round_id, last_update_slot, etc.
}

// =======================================================
// ====================== Events =========================
// =======================================================

#[event]
pub struct PoolCreated {
    pub pool: Pubkey,
    pub name: String,
    pub creator: Pubkey,
    pub initial_price: u64,
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
pub struct TokensSold {
    pub pool: Pubkey,
    pub token_mint: Pubkey,
    pub token_name: String,
    pub token_symbol: String,
    pub seller: Pubkey,
    pub tokens_burned: u64,
    pub quote_returned: u64,
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

// =======================================================
// ==================== The Program ======================
// =======================================================

#[program]
pub mod prediction_market {
    use super::*;

    // ---------------------------------------------------
    // create_pool
    //
    // Sui analog: prediction_pool::create_pool
    // - creates the Pool account
    // - creates bull & bear SPL mints
    // - creates bull & bear vault token accounts (quote token vaults)
    // - seeds initial liquidity
    // - mints initial outcome tokens to the creator
    // - registers pool in PoolRegistry
    // - adds pool to pool_creator's UserPools
    // ---------------------------------------------------
    #[allow(clippy::too_many_arguments)]
    pub fn create_pool(
        ctx: Context<CreatePool>,
        name: String,
        description: String,
        bull_name: String,
        bull_symbol: String,
        bear_name: String,
        bear_symbol: String,
        pair_id: u32,
        asset_address: Pubkey,
        protocol_fee_param: u64,
        mint_fee_param: u64,
        burn_fee_param: u64,
        pool_creator_fee_param: u64,
        initial_liquidity: u64, // how many quote tokens we seed
    ) -> Result<()> {
        require!(initial_liquidity > 0, PredictionError::InvalidAmount);
        require!(
            ctx.accounts.funding_ata.amount >= initial_liquidity,
            PredictionError::InsufficientBalance
        );

        // Fee clamping:
        // protocol_fee = min(max(max(protocol_fee, pool_creator_fee), MIN_PROTOCOL_FEE), MAX_FEE)
        let mut protocol_fee = protocol_fee_param;
        let mut pool_creator_fee = pool_creator_fee_param;
        let mut mint_fee = mint_fee_param;
        let mut burn_fee = burn_fee_param;

        pool_creator_fee = min(pool_creator_fee, MAX_FEE);
        protocol_fee = min(
            max(max(protocol_fee, pool_creator_fee), MIN_PROTOCOL_FEE),
            MAX_FEE,
        );

        mint_fee = min(mint_fee, MAX_FEE);
        burn_fee = min(burn_fee, MAX_FEE);
        pool_creator_fee = min(pool_creator_fee, MAX_FEE);

        // Get normalized oracle price
        require!(ctx.accounts.oracle_feed.pair_id == pair_id, PredictionError::Unauthorized);

        let initial_price = normalize_price(
            ctx.accounts.oracle_feed.value,
            ctx.accounts.oracle_feed.decimals,
            1_000_000, // same precision as in Move
        );

        // Initialize pool fields
        let pool = &mut ctx.accounts.pool;
        pool.name = name.clone();
        pool.description = description.clone();
        pool.bull_name = bull_name.clone();
        pool.bull_symbol = bull_symbol.clone();
        pool.bear_name = bear_name.clone();
        pool.bear_symbol = bear_symbol.clone();

        pool.pair_id = pair_id;
        pool.asset_address = asset_address;
        pool.quote_mint = ctx.accounts.quote_mint.key();
        pool.current_price = initial_price;

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

        // === seed initial liquidity ===
        // Split 50/50 between bull_vault and bear_vault
        let bull_seed_amount = initial_liquidity / 2;
        let bear_seed_amount = initial_liquidity - bull_seed_amount;

        // transfer from funding_ata -> bull_vault
        token::transfer(
            CpiContext::new(
                ctx.accounts.token_program.to_account_info(),
                Transfer {
                    from: ctx.accounts.funding_ata.to_account_info(),
                    to: ctx.accounts.bull_vault.to_account_info(),
                    authority: ctx.accounts.payer.to_account_info(),
                },
            ),
            bull_seed_amount,
        )?;

        // transfer from funding_ata -> bear_vault
        token::transfer(
            CpiContext::new(
                ctx.accounts.token_program.to_account_info(),
                Transfer {
                    from: ctx.accounts.funding_ata.to_account_info(),
                    to: ctx.accounts.bear_vault.to_account_info(),
                    authority: ctx.accounts.payer.to_account_info(),
                },
            ),
            bear_seed_amount,
        )?;

        // === Mint initial bull & bear outcome tokens to the pool creator (payer)
        // follows Move:
        //   amount = reserve_amount
        //   price_per_token ~ 1:1 at bootstrap
        let (bull_tokens_minted, bull_price_per_token) =
            calculate_mint_amount(bull_seed_amount, 0, bull_seed_amount)?;
        let (bear_tokens_minted, bear_price_per_token) =
            calculate_mint_amount(bear_seed_amount, 0, bear_seed_amount)?;

        let signer_seeds: &[&[u8]] = &[
            b"pool_signer",
            ctx.accounts.pool.key().as_ref(),
            &[pool.pool_signer_bump],
        ];

        // mint bull outcome tokens
        token::mint_to(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                MintTo {
                    mint: ctx.accounts.bull_mint.to_account_info(),
                    to: ctx.accounts.payer_bull_ata.to_account_info(),
                    authority: ctx.accounts.pool_signer.to_account_info(),
                },
                &[signer_seeds],
            ),
            bull_tokens_minted,
        )?;

        // mint bear outcome tokens
        token::mint_to(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                MintTo {
                    mint: ctx.accounts.bear_mint.to_account_info(),
                    to: ctx.accounts.payer_bear_ata.to_account_info(),
                    authority: ctx.accounts.pool_signer.to_account_info(),
                },
                &[signer_seeds],
            ),
            bear_tokens_minted,
        )?;

        // Initialize UserPosition for payer (creator gets first tokens)
        let up = &mut ctx.accounts.user_position;
        up.pool = pool.key();
        up.user = ctx.accounts.payer.key();
        up.bull_avg_price = bull_price_per_token;
        up.bear_avg_price = bear_price_per_token;

        // Update PoolRegistry
        let registry = &mut ctx.accounts.registry;
        if !registry.pools.contains(&pool.key()) {
            registry.pools.push(pool.key());
        }

        // Add this pool to the designated pool_creator's UserPools
        let creator_user_pools = &mut ctx.accounts.creator_user_pools;
        if creator_user_pools.user == Pubkey::default() {
            creator_user_pools.user = ctx.accounts.pool_creator.key();
        }
        creator_user_pools.push_unique(pool.key());

        emit!(PoolCreated {
            pool: pool.key(),
            name: pool.name.clone(),
            creator: ctx.accounts.payer.key(),
            initial_price,
        });

        Ok(())
    }

    // ---------------------------------------------------
    // rebalance_pool_entry
    //
    // Mirrors Sui's public entry that only pool_creator can call.
    // This is optional, since purchase_token / redeem_token already
    // internally rebalance before doing economic actions.
    // ---------------------------------------------------
    pub fn rebalance_pool_entry(ctx: Context<RebalancePoolEntry>) -> Result<()> {
        let pool = &mut ctx.accounts.pool;

        require_keys_eq!(
            ctx.accounts.authority.key(),
            pool.pool_creator,
            PredictionError::Unauthorized
        );

        // Perform the same reserve rebalance math we use in trades.
        do_rebalance(
            pool,
            &ctx.accounts.oracle_feed,
            &ctx.accounts.bull_vault,
            &ctx.accounts.bear_vault,
            &ctx.accounts.pool_signer,
            &ctx.accounts.token_program,
        )?;

        Ok(())
    }

    // ---------------------------------------------------
    // purchase_token
    //
    // Mirrors Sui's purchase_token:
    // - Rebalance pool to oracle
    // - Take user's quote tokens
    // - Split protocol fee, mint_fee, creator fee
    // - Send net into chosen side vault
    // - Mint Bull or Bear tokens to buyer
    // - Update avg purchase price in UserPosition
    // - If this is the first time user touches the pool,
    //   add pool to UserPools.
    // ---------------------------------------------------
    pub fn purchase_token(
        ctx: Context<PurchaseToken>,
        is_bull: bool,
        quote_amount_in: u64,
    ) -> Result<()> {
        require!(quote_amount_in > 0, PredictionError::InvalidAmount);

        let pool = &mut ctx.accounts.pool;

        // Sanity checks for fee payout targets
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

        // === 1. Rebalance based on oracle
        do_rebalance(
            pool,
            &ctx.accounts.oracle_feed,
            &ctx.accounts.bull_vault,
            &ctx.accounts.bear_vault,
            &ctx.accounts.pool_signer,
            &ctx.accounts.token_program,
        )?;

        // figure out which side we're buying
        // chosen_* are the side user wants exposure to
        // other_*  is the opposite side
        let (chosen_vault, other_vault, chosen_mint, chosen_user_ata, other_user_ata,
             chosen_name, chosen_symbol, chosen_is_bull) = if is_bull {
            (
                &ctx.accounts.bull_vault,
                &ctx.accounts.bear_vault,
                &ctx.accounts.bull_mint,
                &ctx.accounts.buyer_bull_ata,
                &ctx.accounts.buyer_bear_ata,
                pool.bull_name.clone(),
                pool.bull_symbol.clone(),
                true,
            )
        } else {
            (
                &ctx.accounts.bear_vault,
                &ctx.accounts.bull_vault,
                &ctx.accounts.bear_mint,
                &ctx.accounts.buyer_bear_ata,
                &ctx.accounts.buyer_bull_ata,
                pool.bear_name.clone(),
                pool.bear_symbol.clone(),
                false,
            )
        };

        // snapshot reserves & supply BEFORE we move money
        let reserve_before = chosen_vault.amount;
        let total_supply_before = chosen_mint.supply;

        // user balances (before mint)
        let user_old_balance = chosen_user_ata.amount;
        let other_old_balance = other_user_ata.amount;

        // 2. Fee breakdown
        let (protocol_fee_amt, fee_amt, creator_fee_amt, net_amount) =
            compute_fee_breakdown(
                quote_amount_in,
                pool.protocol_fee,
                pool.mint_fee,          // mint_fee because this is buy
                pool.pool_creator_fee,
            )?;
        require!(net_amount > 0, PredictionError::InvalidAmount);

        // 3. Move user's quote tokens into all destinations:
        // protocol_fee -> protocol_fee_ata
        if protocol_fee_amt > 0 {
            token::transfer(
                CpiContext::new(
                    ctx.accounts.token_program.to_account_info(),
                    Transfer {
                        from: ctx.accounts.buyer_quote_ata.to_account_info(),
                        to: ctx.accounts.protocol_fee_ata.to_account_info(),
                        authority: ctx.accounts.buyer.to_account_info(),
                    },
                ),
                protocol_fee_amt,
            )?;
        }

        // specific fee -> other_vault
        if fee_amt > 0 {
            token::transfer(
                CpiContext::new(
                    ctx.accounts.token_program.to_account_info(),
                    Transfer {
                        from: ctx.accounts.buyer_quote_ata.to_account_info(),
                        to: other_vault.to_account_info(),
                        authority: ctx.accounts.buyer.to_account_info(),
                    },
                ),
                fee_amt,
            )?;
        }

        // creator fee -> creator_quote_ata
        if creator_fee_amt > 0 {
            token::transfer(
                CpiContext::new(
                    ctx.accounts.token_program.to_account_info(),
                    Transfer {
                        from: ctx.accounts.buyer_quote_ata.to_account_info(),
                        to: ctx.accounts.creator_quote_ata.to_account_info(),
                        authority: ctx.accounts.buyer.to_account_info(),
                    },
                ),
                creator_fee_amt,
            )?;
        }

        // net amount -> chosen_vault
        token::transfer(
            CpiContext::new(
                ctx.accounts.token_program.to_account_info(),
                Transfer {
                    from: ctx.accounts.buyer_quote_ata.to_account_info(),
                    to: chosen_vault.to_account_info(),
                    authority: ctx.accounts.buyer.to_account_info(),
                },
            ),
            net_amount,
        )?;

        // 4. Figure out how many outcome tokens to mint
        let (mint_amount, price_per_token) =
            calculate_mint_amount(reserve_before, total_supply_before, net_amount)?;

        // 5. Mint Bull or Bear SPL tokens to buyer
        let signer_seeds: &[&[u8]] = &[
            b"pool_signer",
            pool.key().as_ref(),
            &[pool.pool_signer_bump],
        ];

        token::mint_to(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                MintTo {
                    mint: chosen_mint.to_account_info(),
                    to: chosen_user_ata.to_account_info(),
                    authority: ctx.accounts.pool_signer.to_account_info(),
                },
                &[signer_seeds],
            ),
            mint_amount,
        )?;

        // 6. Update UserPosition avg price for this side
        let user_position = &mut ctx.accounts.user_position;
        if user_position.pool == Pubkey::default() {
            user_position.pool = pool.key();
            user_position.user = ctx.accounts.buyer.key();
            user_position.bull_avg_price = 0;
            user_position.bear_avg_price = 0;
        }

        if chosen_is_bull {
            let old_avg = user_position.bull_avg_price;
            let new_avg = weighted_avg_price(
                user_old_balance,
                old_avg,
                mint_amount,
                price_per_token,
            )?;
            user_position.bull_avg_price = new_avg;
        } else {
            let old_avg = user_position.bear_avg_price;
            let new_avg = weighted_avg_price(
                user_old_balance,
                old_avg,
                mint_amount,
                price_per_token,
            )?;
            user_position.bear_avg_price = new_avg;
        }

        // 7. If this is the user's first exposure to this pool
        // (both balances were 0 before this trade), add to UserPools.
        if user_old_balance == 0 && other_old_balance == 0 {
            let user_pools = &mut ctx.accounts.user_pools;
            if user_pools.user == Pubkey::default() {
                user_pools.user = ctx.accounts.buyer.key();
            }
            user_pools.push_unique(pool.key());
        }

        emit!(TokensPurchased {
            pool: pool.key(),
            token_mint: chosen_mint.key(),
            token_name: chosen_name,
            token_symbol: chosen_symbol,
            buyer: ctx.accounts.buyer.key(),
            quote_amount: net_amount,
            tokens_minted: mint_amount,
            price_per_token,
        });

        Ok(())
    }

    // ---------------------------------------------------
    // redeem_token
    //
    // Mirrors Sui's redeem_token:
    // - Rebalance pool
    // - Burn user's Bull or Bear tokens
    // - Calculate how many quote tokens they should get back
    // - Split protocol fee / burn_fee / creator fee
    // - Send net back to the seller
    // - Update avg purchase price if they fully exited that side
    // - If user no longer has *any* bull/bear in this pool,
    //   remove pool from their UserPools.
    // ---------------------------------------------------
    pub fn redeem_token(
        ctx: Context<RedeemToken>,
        is_bull: bool,
        amount_out_tokens: u64,
    ) -> Result<()> {
        require!(amount_out_tokens > 0, PredictionError::InvalidAmount);

        let pool = &mut ctx.accounts.pool;

        // Sanity checks
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

        // Rebalance pool first (same as purchase path)
        do_rebalance(
            pool,
            &ctx.accounts.oracle_feed,
            &ctx.accounts.bull_vault,
            &ctx.accounts.bear_vault,
            &ctx.accounts.pool_signer,
            &ctx.accounts.token_program,
        )?;

        // Choose which side we're redeeming
        let (chosen_mint, chosen_user_ata, chosen_vault,
             other_vault, chosen_name, chosen_symbol, chosen_is_bull) = if is_bull {
            (
                &ctx.accounts.bull_mint,
                &ctx.accounts.seller_bull_ata,
                &ctx.accounts.bull_vault,
                &ctx.accounts.bear_vault,
                pool.bull_name.clone(),
                pool.bull_symbol.clone(),
                true,
            )
        } else {
            (
                &ctx.accounts.bear_mint,
                &ctx.accounts.seller_bear_ata,
                &ctx.accounts.bear_vault,
                &ctx.accounts.bull_vault,
                pool.bear_name.clone(),
                pool.bear_symbol.clone(),
                false,
            )
        };

        // seller must have enough tokens
        require!(
            chosen_user_ata.amount >= amount_out_tokens,
            PredictionError::InsufficientBalance
        );

        // We can't burn the entire supply (Move assert)
        let total_supply_before = chosen_mint.supply;
        require!(total_supply_before > 0, PredictionError::ZeroTotalSupply);
        require!(
            total_supply_before > amount_out_tokens,
            PredictionError::InvalidAmount
        );

        let reserve_before = chosen_vault.amount;

        // Calculate how many quote tokens we owe them *before fees*
        let quote_to_return =
            calculate_burn_amount(reserve_before, total_supply_before, amount_out_tokens)?;

        require!(
            chosen_vault.amount >= quote_to_return,
            PredictionError::InsufficientBalance
        );

        // Burn user's outcome tokens
        token::burn(
            CpiContext::new(
                ctx.accounts.token_program.to_account_info(),
                Burn {
                    mint: chosen_mint.to_account_info(),
                    from: chosen_user_ata.to_account_info(),
                    authority: ctx.accounts.seller.to_account_info(),
                },
            ),
            amount_out_tokens,
        )?;

        // Fee breakdown (burn path uses burn_fee)
        let (protocol_fee_amt, fee_amt, creator_fee_amt, net_amount) =
            compute_fee_breakdown(
                quote_to_return,
                pool.protocol_fee,
                pool.burn_fee,
                pool.pool_creator_fee,
            )?;
        require!(net_amount > 0, PredictionError::InvalidAmount);

        // We'll now pay out from chosen_vault using the pool_signer PDA.
        let signer_seeds: &[&[u8]] = &[
            b"pool_signer",
            pool.key().as_ref(),
            &[pool.pool_signer_bump],
        ];

        // protocol fee -> protocol_fee_ata
        if protocol_fee_amt > 0 {
            token::transfer(
                CpiContext::new_with_signer(
                    ctx.accounts.token_program.to_account_info(),
                    Transfer {
                        from: chosen_vault.to_account_info(),
                        to: ctx.accounts.protocol_fee_ata.to_account_info(),
                        authority: ctx.accounts.pool_signer.to_account_info(),
                    },
                    &[signer_seeds],
                ),
                protocol_fee_amt,
            )?;
        }

        // burn_fee portion -> other_vault
        if fee_amt > 0 {
            token::transfer(
                CpiContext::new_with_signer(
                    ctx.accounts.token_program.to_account_info(),
                    Transfer {
                        from: chosen_vault.to_account_info(),
                        to: other_vault.to_account_info(),
                        authority: ctx.accounts.pool_signer.to_account_info(),
                    },
                    &[signer_seeds],
                ),
                fee_amt,
            )?;
        }

        // creator_fee -> creator_quote_ata
        if creator_fee_amt > 0 {
            token::transfer(
                CpiContext::new_with_signer(
                    ctx.accounts.token_program.to_account_info(),
                    Transfer {
                        from: chosen_vault.to_account_info(),
                        to: ctx.accounts.creator_quote_ata.to_account_info(),
                        authority: ctx.accounts.pool_signer.to_account_info(),
                    },
                    &[signer_seeds],
                ),
                creator_fee_amt,
            )?;
        }

        // net_amount -> seller_quote_ata
        token::transfer(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                Transfer {
                    from: chosen_vault.to_account_info(),
                    to: ctx.accounts.seller_quote_ata.to_account_info(),
                    authority: ctx.accounts.pool_signer.to_account_info(),
                },
                &[signer_seeds],
            ),
            net_amount,
        )?;

        // Reload token accounts so we see post-burn balances
        ctx.accounts.seller_bull_ata.reload()?;
        ctx.accounts.seller_bear_ata.reload()?;

        let remaining_bull = ctx.accounts.seller_bull_ata.amount;
        let remaining_bear = ctx.accounts.seller_bear_ata.amount;

        // Update avg price in UserPosition:
        let user_position = &mut ctx.accounts.user_position;
        if chosen_is_bull {
            if remaining_bull == 0 {
                user_position.bull_avg_price = 0;
            }
        } else {
            if remaining_bear == 0 {
                user_position.bear_avg_price = 0;
            }
        }

        // If user has fully exited both bull and bear, remove pool from their UserPools
        if remaining_bull == 0 && remaining_bear == 0 {
            ctx.accounts.user_pools.remove_if_present(pool.key());
        }

        emit!(TokensSold {
            pool: pool.key(),
            token_mint: chosen_mint.key(),
            token_name: chosen_name,
            token_symbol: chosen_symbol,
            seller: ctx.accounts.seller.key(),
            tokens_burned: amount_out_tokens,
            quote_returned: net_amount,
        });

        Ok(())
    }
}

// =======================================================
// ================= Account Contexts ====================
// =======================================================

#[derive(Accounts)]
pub struct CreatePool<'info> {
    // Signer funding pool creation and receiving initial bull/bear tokens
    #[account(mut)]
    pub payer: Signer<'info>,

    /// The address that earns "pool_creator_fee" on trades.
    /// (Can be same as payer or different, like in your Sui code.)
    /// CHECK: we only store this pubkey, payout is enforced via runtime checks.
    pub pool_creator: UncheckedAccount<'info>,

    // Global registry (init if first pool)
    #[account(
        init_if_needed,
        payer = payer,
        space = PoolRegistry::INIT_SPACE,
        seeds = [b"pool_registry"],
        bump
    )]
    pub registry: Account<'info, PoolRegistry>,

    // The Pool account itself (not a PDA, just a normal init account)
    #[account(
        init,
        payer = payer,
        space = Pool::INIT_SPACE,
    )]
    pub pool: Account<'info, Pool>,

    // PDA signer that will own vaults and mint authority for outcome tokens
    /// CHECK: this PDA doesn't need lamports; it's just a signer seed.
    #[account(
        seeds = [b"pool_signer", pool.key().as_ref()],
        bump
    )]
    pub pool_signer: UncheckedAccount<'info>,

    // Outcome token mints (Bull / Bear)
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

    // Quote token mint (USDC / wSOL / etc)
    pub quote_mint: Account<'info, Mint>,

    // Vault token accounts, owned by pool_signer, holding quote_mint
    #[account(
        init,
        payer = payer,
        seeds = [b"bull_vault", pool.key().as_ref()],
        bump,
        token::mint = quote_mint,
        token::authority = pool_signer,
    )]
    pub bull_vault: Account<'info, TokenAccount>,

    #[account(
        init,
        payer = payer,
        seeds = [b"bear_vault", pool.key().as_ref()],
        bump,
        token::mint = quote_mint,
        token::authority = pool_signer,
    )]
    pub bear_vault: Account<'info, TokenAccount>,

    // Payer's source of initial liquidity (quote token)
    #[account(
        mut,
        constraint = funding_ata.owner == payer.key(),
        constraint = funding_ata.mint == quote_mint.key(),
    )]
    pub funding_ata: Account<'info, TokenAccount>,

    // Payer's outcome token ATAs to receive initial bull/bear
    #[account(
        init,
        payer = payer,
        associated_token::mint = bull_mint,
        associated_token::authority = payer
    )]
    pub payer_bull_ata: Account<'info, TokenAccount>,

    #[account(
        init,
        payer = payer,
        associated_token::mint = bear_mint,
        associated_token::authority = payer
    )]
    pub payer_bear_ata: Account<'info, TokenAccount>,

    // Track payer's avg prices, etc.
    #[account(
        init,
        payer = payer,
        space = UserPosition::INIT_SPACE,
        seeds = [b"user_position", pool.key().as_ref(), payer.key().as_ref()],
        bump
    )]
    pub user_position: Account<'info, UserPosition>,

    // Track which pools the pool_creator is in (creator might differ from payer).
    #[account(
        init_if_needed,
        payer = payer,
        space = UserPools::INIT_SPACE,
        seeds = [b"user_pools", pool_creator.key().as_ref()],
        bump
    )]
    pub creator_user_pools: Account<'info, UserPools>,

    // Price feed account (Supra-equivalent)
    pub oracle_feed: Account<'info, OraclePriceFeed>,

    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, System>,
    pub rent: Sysvar<'info, Rent>,
}

// Manual external rebalance (pool_creator only)
#[derive(Accounts)]
pub struct RebalancePoolEntry<'info> {
    #[account(mut)]
    pub authority: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, Pool>,

    /// CHECK: signer PDA
    #[account(
        seeds = [b"pool_signer", pool.key().as_ref()],
        bump = pool.pool_signer_bump
    )]
    pub pool_signer: UncheckedAccount<'info>,

    #[account(mut)]
    pub bull_vault: Account<'info, TokenAccount>,

    #[account(mut)]
    pub bear_vault: Account<'info, TokenAccount>,

    pub oracle_feed: Account<'info, OraclePriceFeed>,

    pub token_program: Program<'info, Token>,
}

// Buy flow
#[derive(Accounts)]
pub struct PurchaseToken<'info> {
    #[account(mut)]
    pub buyer: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, Pool>,

    /// CHECK: PDA signer
    #[account(
        seeds = [b"pool_signer", pool.key().as_ref()],
        bump = pool.pool_signer_bump
    )]
    pub pool_signer: UncheckedAccount<'info>,

    #[account(mut)]
    pub bull_mint: Account<'info, Mint>,
    #[account(mut)]
    pub bear_mint: Account<'info, Mint>,

    // Vaults holding quote tokens
    #[account(mut)]
    pub bull_vault: Account<'info, TokenAccount>,
    #[account(mut)]
    pub bear_vault: Account<'info, TokenAccount>,

    pub quote_mint: Account<'info, Mint>,

    // Buyer pays with this
    #[account(
        mut,
        constraint = buyer_quote_ata.owner == buyer.key(),
        constraint = buyer_quote_ata.mint == quote_mint.key(),
    )]
    pub buyer_quote_ata: Account<'info, TokenAccount>,

    // Protocol fee receiver (must be STABLE_ORDER_ADDRESS)
    #[account(
        mut,
        constraint = protocol_fee_ata.mint == quote_mint.key(),
    )]
    pub protocol_fee_ata: Account<'info, TokenAccount>,

    // Pool creator fee receiver
    #[account(
        mut,
        constraint = creator_quote_ata.mint == quote_mint.key(),
    )]
    pub creator_quote_ata: Account<'info, TokenAccount>,

    // Buyer's outcome ATAs (created if needed)
    #[account(
        init_if_needed,
        payer = buyer,
        associated_token::mint = bull_mint,
        associated_token::authority = buyer
    )]
    pub buyer_bull_ata: Account<'info, TokenAccount>,

    #[account(
        init_if_needed,
        payer = buyer,
        associated_token::mint = bear_mint,
        associated_token::authority = buyer
    )]
    pub buyer_bear_ata: Account<'info, TokenAccount>,

    // UserPosition PDA (init if first time this buyer touches this pool)
    #[account(
        init_if_needed,
        payer = buyer,
        space = UserPosition::INIT_SPACE,
        seeds = [b"user_position", pool.key().as_ref(), buyer.key().as_ref()],
        bump
    )]
    pub user_position: Account<'info, UserPosition>,

    // UserPools PDA (track pools buyer is in)
    #[account(
        init_if_needed,
        payer = buyer,
        space = UserPools::INIT_SPACE,
        seeds = [b"user_pools", buyer.key().as_ref()],
        bump
    )]
    pub user_pools: Account<'info, UserPools>,

    pub oracle_feed: Account<'info, OraclePriceFeed>,

    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, System>,
    pub rent: Sysvar<'info, Rent>,
}

// Sell / redeem flow
#[derive(Accounts)]
pub struct RedeemToken<'info> {
    #[account(mut)]
    pub seller: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, Pool>,

    /// CHECK: PDA signer
    #[account(
        seeds = [b"pool_signer", pool.key().as_ref()],
        bump = pool.pool_signer_bump
    )]
    pub pool_signer: UncheckedAccount<'info>,

    #[account(mut)]
    pub bull_mint: Account<'info, Mint>,
    #[account(mut)]
    pub bear_mint: Account<'info, Mint>,

    #[account(mut)]
    pub bull_vault: Account<'info, TokenAccount>,
    #[account(mut)]
    pub bear_vault: Account<'info, TokenAccount>,

    pub quote_mint: Account<'info, Mint>,

    // Seller receives payout here
    #[account(
        mut,
        constraint = seller_quote_ata.owner == seller.key(),
        constraint = seller_quote_ata.mint == quote_mint.key(),
    )]
    pub seller_quote_ata: Account<'info, TokenAccount>,

    // protocol fee destination (stable order)
    #[account(
        mut,
        constraint = protocol_fee_ata.mint == quote_mint.key(),
    )]
    pub protocol_fee_ata: Account<'info, TokenAccount>,

    // creator fee destination
    #[account(
        mut,
        constraint = creator_quote_ata.mint == quote_mint.key(),
    )]
    pub creator_quote_ata: Account<'info, TokenAccount>,

    // Seller's outcome balances (must already exist)
    #[account(
        mut,
        constraint = seller_bull_ata.owner == seller.key(),
        constraint = seller_bull_ata.mint == bull_mint.key(),
    )]
    pub seller_bull_ata: Account<'info, TokenAccount>,

    #[account(
        mut,
        constraint = seller_bear_ata.owner == seller.key(),
        constraint = seller_bear_ata.mint == bear_mint.key(),
    )]
    pub seller_bear_ata: Account<'info, TokenAccount>,

    // UserPosition PDA
    #[account(
        mut,
        seeds = [b"user_position", pool.key().as_ref(), seller.key().as_ref()],
        bump
    )]
    pub user_position: Account<'info, UserPosition>,

    // UserPools PDA
    #[account(
        mut,
        seeds = [b"user_pools", seller.key().as_ref()],
        bump
    )]
    pub user_pools: Account<'info, UserPools>,

    pub oracle_feed: Account<'info, OraclePriceFeed>,

    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, System>,
    pub rent: Sysvar<'info, Rent>,
}

// =======================================================
// ================= Helper Functions ====================
// =======================================================

fn weighted_avg_price(
    old_balance: u64,
    old_avg_price: u64,
    added_amount: u64,
    added_price: u64,
) -> Result<u64> {
    // new_avg = (old_balance*old_avg_price + added_amount*added_price)
    //           / (old_balance + added_amount)
    let total_balance = old_balance
        .checked_add(added_amount)
        .ok_or(PredictionError::MathOverflow)?;

    if total_balance == 0 {
        return Ok(0);
    }

    let old_total_value = (old_balance as u128) * (old_avg_price as u128);
    let new_total_value = (added_amount as u128) * (added_price as u128);
    let sum = old_total_value
        .checked_add(new_total_value)
        .ok_or(PredictionError::MathOverflow)?;

    let avg = sum
        .checked_div(total_balance as u128)
        .ok_or(PredictionError::MathOverflow)? as u64;

    Ok(avg)
}

// (reserve, total_supply, quote_amount) -> (mint_amount, price_per_token_scaled)
fn calculate_mint_amount(
    reserve: u64,
    total_supply: u64,
    quote_amount: u64,
) -> Result<(u64, u64)> {
    let amount: u64 = if total_supply == 0 {
        quote_amount
    } else {
        ((quote_amount as u128)
            .checked_mul(total_supply as u128)
            .ok_or(PredictionError::MathOverflow)?)
            .checked_div(reserve as u128)
            .ok_or(PredictionError::MathOverflow)? as u64
    };

    let price_per_token = if amount > 0 {
        ((quote_amount as u128)
            .checked_mul(PRECISION_SCALE as u128)
            .ok_or(PredictionError::MathOverflow)?)
            .checked_div(amount as u128)
            .ok_or(PredictionError::MathOverflow)? as u64
    } else {
        0
    };

    Ok((amount, price_per_token))
}

// How much quote you get back when burning tokens_to_burn
fn calculate_burn_amount(
    reserve: u64,
    total_supply: u64,
    tokens_to_burn: u64,
) -> Result<u64> {
    if total_supply == 0 {
        return Ok(0);
    }
    let num = (tokens_to_burn as u128)
        .checked_mul(reserve as u128)
        .ok_or(PredictionError::MathOverflow)?;
    let out = num
        .checked_div(total_supply as u128)
        .ok_or(PredictionError::MathOverflow)? as u64;
    Ok(out)
}

// Rebalance math from your Move code
fn calculate_new_reserves(
    old_price: u64,
    new_price: u64,
    bull_reserve: u64,
    bear_reserve: u64,
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

    Ok((new_bull_reserve, new_bear_reserve))
}

// Normalize oracle price like your normalize_price(value, decimal, precision)
fn normalize_price(value: u128, decimals: u8, precision: u64) -> u64 {
    let mut divisor: u128 = 1;
    for _ in 0..decimals {
        divisor = divisor.saturating_mul(10);
    }
    let scaled = value
        .saturating_mul(precision as u128)
        .saturating_div(divisor);
    scaled as u64
}

// Extract fee breakdown the same way Sui's deduct_fees() did,
// but we don't actually move tokens here. We just compute the numbers.
fn compute_fee_breakdown(
    amount: u64,
    protocol_fee_bps: u64,
    specific_fee_bps: u64, // mint_fee or burn_fee
    creator_fee_bps: u64,
) -> Result<(u64, u64, u64, u64)> {
    let protocol_fee_amt = (amount as u128)
        .checked_mul(protocol_fee_bps as u128)
        .ok_or(PredictionError::MathOverflow)?
        .checked_div(FEE_DENOMINATOR as u128)
        .ok_or(PredictionError::MathOverflow)? as u64;

    let fee_amt = (amount as u128)
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
        .saturating_sub(fee_amt)
        .saturating_sub(creator_fee_amt);

    Ok((protocol_fee_amt, fee_amt, creator_fee_amt, net_amount))
}

// Core rebalance logic used in purchase/sell and manual rebalance.
// - Reads oracle
// - Computes target reserves
// - Moves tokens between bull_vault and bear_vault so they match target
// - Updates pool.current_price
// - Emits PoolRebalanced
fn do_rebalance(
    pool: &mut Account<Pool>,
    oracle_feed: &Account<OraclePriceFeed>,
    bull_vault: &Account<TokenAccount>,
    bear_vault: &Account<TokenAccount>,
    pool_signer: &AccountInfo,
    token_program: &Program<Token>,
) -> Result<()> {
    // Normalize new price
    let new_price = normalize_price(oracle_feed.value, oracle_feed.decimals, 1_000_000);

    let old_price = pool.current_price;
    if new_price == old_price {
        // no-op
        return Ok(());
    }

    // snapshot current reserves
    let old_bull_reserve = bull_vault.amount;
    let old_bear_reserve = bear_vault.amount;

    // compute targets
    let (target_bull, target_bear) = calculate_new_reserves(
        old_price,
        new_price,
        old_bull_reserve,
        old_bear_reserve,
    )?;

    // move the delta
    let signer_seeds: &[&[u8]] = &[
        b"pool_signer",
        pool.key().as_ref(),
        &[pool.pool_signer_bump],
    ];

    if target_bull > old_bull_reserve {
        let diff = target_bull - old_bull_reserve;
        // transfer `diff` from bear_vault -> bull_vault
        token::transfer(
            CpiContext::new_with_signer(
                token_program.to_account_info(),
                Transfer {
                    from: bear_vault.to_account_info(),
                    to: bull_vault.to_account_info(),
                    authority: pool_signer.clone(),
                },
                &[signer_seeds],
            ),
            diff,
        )?;
    } else if target_bull < old_bull_reserve {
        let diff = old_bull_reserve - target_bull;
        // transfer `diff` from bull_vault -> bear_vault
        token::transfer(
            CpiContext::new_with_signer(
                token_program.to_account_info(),
                Transfer {
                    from: bull_vault.to_account_info(),
                    to: bear_vault.to_account_info(),
                    authority: pool_signer.clone(),
                },
                &[signer_seeds],
            ),
            diff,
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
