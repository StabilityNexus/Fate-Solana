use anchor_lang::prelude::*;
use anchor_spl::{
    token::{self, Burn, Mint, MintTo, Token, TokenAccount, Transfer},
    associated_token::AssociatedToken,
};
use crate::{
    FEE_DENOMINATOR,
    MAX_FEE,
    MIN_PROTOCOL_FEE,
    OUTCOME_TOKEN_DECIMALS,
    PRECISION_SCALE,
    PredictionError,
    PoolRegistryAccount,
    UserRegistryAccount,
    stable_order_address,
};

// =========================
// ====== Accounts =========
// =========================

// Equivalent to your PredictionPool struct in Sui.
#[account]
pub struct PoolAccount {
    // Human-readable fields
    pub name: String,
    pub description: String,

    pub bull_name: String,
    pub bull_symbol: String,
    pub bear_name: String,
    pub bear_symbol: String,

    // Oracle + underlying asset reference
    pub pair_id: u32,
    pub asset_address: Pubkey,
    pub quote_mint: Pubkey, // the SPL mint used as settlement (USDC, wSOL, etc.)

    pub current_price: u64, // normalized oracle price, scaled 1_000_000 same as Move

    // Outcome token mints
    pub bull_mint: Pubkey,
    pub bear_mint: Pubkey,

    // Vaults holding quote tokens
    pub bull_vault: Pubkey,
    pub bear_vault: Pubkey,

    // Fees (in basis points / 10_000)
    pub protocol_fee: u64,
    pub mint_fee: u64,
    pub burn_fee: u64,
    pub pool_creator_fee: u64,

    // Fee receiver
    pub pool_creator: Pubkey,

    // PDA bump for the pool_signer authority
    pub pool_signer_bump: u8,
}

// Rough sizing: discriminator (8)
// + name, description, bull/bear names/symbols (Strings)
// + a bunch of Pubkeys/u64/u32/u8.
// We won't recalc INIT_SPACE here because we allocate it manually in CreatePool.

#[account]
pub struct OraclePriceFeedAccount {
    pub pair_id: u32,
    pub value: u128,   // raw oracle value
    pub decimals: u8,  // decimal places of `value`
    // you'd typically also store last update slot, confidence, etc.
}

// =========================
// ======== Events =========
// =========================

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

// =========================
// ===== Helper math =======
// =========================

fn weighted_avg_price(
    old_balance: u64,
    old_avg_price: u64,
    added_amount: u64,
    added_price: u64,
) -> Result<u64> {
    // new_avg = (old_balance*old_avg_price + added_amount*added_price)
    //         / (old_balance + added_amount)
    let total_balance = old_balance
        .checked_add(added_amount)
        .ok_or(PredictionError::MathOverflow)?;
    if total_balance == 0 {
        return Ok(0);
    }

    let old_total_value =
        (old_balance as u128) * (old_avg_price as u128);
    let new_total_value =
        (added_amount as u128) * (added_price as u128);

    let sum = old_total_value
        .checked_add(new_total_value)
        .ok_or(PredictionError::MathOverflow)?;

    let avg = sum
        .checked_div(total_balance as u128)
        .ok_or(PredictionError::MathOverflow)? as u64;

    Ok(avg)
}

// how many outcome tokens to mint for a deposit
fn calculate_mint_amount(
    reserve_before: u64,
    total_supply_before: u64,
    quote_amount_in: u64,
) -> Result<(u64, u64)> {
    // if no supply yet: 1:1
    let mint_amount: u64 = if total_supply_before == 0 {
        quote_amount_in
    } else {
        ((quote_amount_in as u128)
            .checked_mul(total_supply_before as u128)
            .ok_or(PredictionError::MathOverflow)?)
            .checked_div(reserve_before as u128)
            .ok_or(PredictionError::MathOverflow)? as u64
    };

    // price_per_token = quote_amount_in / minted, scaled up for precision
    let price_per_token = if mint_amount > 0 {
        ((quote_amount_in as u128)
            .checked_mul(PRECISION_SCALE as u128)
            .ok_or(PredictionError::MathOverflow)?)
            .checked_div(mint_amount as u128)
            .ok_or(PredictionError::MathOverflow)? as u64
    } else {
        0
    };

    Ok((mint_amount, price_per_token))
}

// how many quote tokens you get back for burning outcome tokens
fn calculate_burn_amount(
    reserve_before: u64,
    total_supply_before: u64,
    tokens_to_burn: u64,
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

// oracle price normalization (like normalize_price in Move)
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

// adjust reserves when oracle price changes
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

// fee math from your deduct_fees()
fn compute_fee_breakdown(
    amount: u64,
    protocol_fee_bps: u64,
    specific_fee_bps: u64, // mint_fee when buying, burn_fee when selling
    creator_fee_bps: u64,
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

// Internal utility: do_rebalance before trading or on manual call.
fn do_rebalance<'info>(
    pool: &mut Account<'info, PoolAccount>,
    oracle_feed: &Account<'info, OraclePriceFeedAccount>,
    bull_vault: &Account<'info, TokenAccount>,
    bear_vault: &Account<'info, TokenAccount>,
    pool_signer: &AccountInfo<'info>,
    token_program: &Program<'info, Token>,
) -> Result<()> {
    // Fetch normalized oracle price
    let new_price = normalize_price(
        oracle_feed.value,
        oracle_feed.decimals,
        1_000_000, // keep same precision as Move code
    );

    let old_price = pool.current_price;
    if new_price == old_price {
        // no change, nothing to shift
        return Ok(());
    }

    let old_bull_reserve = bull_vault.amount;
    let old_bear_reserve = bear_vault.amount;

    let (target_bull, target_bear) = calculate_new_reserves(
        old_price,
        new_price,
        old_bull_reserve,
        old_bear_reserve,
    )?;

    let signer_seeds: &[&[u8]] = &[
        b"pool_signer",
        pool.key().as_ref(),
        &[pool.pool_signer_bump],
    ];

    if target_bull > old_bull_reserve {
        let diff = target_bull - old_bull_reserve;
        // move diff from bear_vault -> bull_vault
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
        // move diff from bull_vault -> bear_vault
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

// =========================
// ===== Instruction args ==
// =========================

// Bundle the pool creation params so Anchor's IDL stays clean.
#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub struct CreatePoolArgs {
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
    pub initial_liquidity: u64,
}

// =========================
// ===== Instructions ======
// =========================

pub fn create_pool(
    ctx: Context<CreatePool>,
    args: CreatePoolArgs,
) -> Result<()> {
    require!(args.initial_liquidity > 0, PredictionError::InvalidAmount);
    require!(
        ctx.accounts.funding_ata.amount >= args.initial_liquidity,
        PredictionError::InsufficientBalance
    );

    // For simplicity in this skeleton, we assume the payer funding
    // the pool is also the pool_creator who will receive creator fees.
    require_keys_eq!(
        ctx.accounts.pool_creator.key(),
        ctx.accounts.payer.key(),
        PredictionError::Unauthorized
    );

    // Fee clamping (mirrors Move):
    let mut protocol_fee = args.protocol_fee_param;
    let mut pool_creator_fee = args.pool_creator_fee_param;
    let mut mint_fee = args.mint_fee_param;
    let mut burn_fee = args.burn_fee_param;

    pool_creator_fee = pool_creator_fee.min(MAX_FEE);
    protocol_fee = protocol_fee
        .max(pool_creator_fee)
        .max(MIN_PROTOCOL_FEE)
        .min(MAX_FEE);

    mint_fee = mint_fee.min(MAX_FEE);
    burn_fee = burn_fee.min(MAX_FEE);
    pool_creator_fee = pool_creator_fee.min(MAX_FEE);

    // pull price from oracle
    require!(
        ctx.accounts.oracle_feed.pair_id == args.pair_id,
        PredictionError::Unauthorized
    );
    let initial_price = normalize_price(
        ctx.accounts.oracle_feed.value,
        ctx.accounts.oracle_feed.decimals,
        1_000_000,
    );

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

    pool.bull_mint = ctx.accounts.bull_mint.key();
    pool.bear_mint = ctx.accounts.bear_mint.key();
    pool.bull_vault = ctx.accounts.bull_vault.key();
    pool.bear_vault = ctx.accounts.bear_vault.key();

    pool.protocol_fee = protocol_fee;
    pool.mint_fee = mint_fee;
    pool.burn_fee = burn_fee;
    pool.pool_creator_fee = pool_creator_fee;
    pool.pool_creator = ctx.accounts.pool_creator.key();

    pool.pool_signer_bump = *ctx.bumps.get("pool_signer").unwrap();

    // === Seed initial liquidity ===
    let bull_seed_amount = args.initial_liquidity / 2;
    let bear_seed_amount = args.initial_liquidity - bull_seed_amount;

    // payer -> bull_vault
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

    // payer -> bear_vault
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

    // === Mint initial Bull/Bear outcome tokens to creator (payer) ===
    let (bull_tokens_minted, bull_price_per_token) =
        calculate_mint_amount(bull_seed_amount, 0, bull_seed_amount)?;
    let (bear_tokens_minted, bear_price_per_token) =
        calculate_mint_amount(bear_seed_amount, 0, bear_seed_amount)?;

    let signer_seeds: &[&[u8]] = &[
        b"pool_signer",
        pool.key().as_ref(),
        &[pool.pool_signer_bump],
    ];

    // mint bull
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

    // mint bear
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

    // === Add pool to global registry ===
    ctx.accounts.registry.push_unique(pool.key());

    // === Update creator's user registry ===
    let ur = &mut ctx.accounts.user_registry;
    if ur.user == Pubkey::default() {
        ur.user = ctx.accounts.payer.key();
    }

    // If already exists, overwrite avg prices. Otherwise push.
    if let Some(pos) = ur.get_position_mut(pool.key()) {
        pos.bull_avg_price = bull_price_per_token;
        pos.bear_avg_price = bear_price_per_token;
    } else {
        ur.insert_new_position(
            ctx.accounts.payer.key(),
            pool.key(),
            bull_price_per_token,
            bear_price_per_token,
        );
    }

    emit!(PoolCreated {
        pool: pool.key(),
        name: pool.name.clone(),
        creator: ctx.accounts.payer.key(),
        initial_price,
    });

    Ok(())
}

pub fn rebalance_pool_entry(
    ctx: Context<RebalancePoolEntry>,
) -> Result<()> {
    let pool = &mut ctx.accounts.pool;
    // Only pool_creator can manually poke the rebalance, same as Move `EUnauthorized`.
    require_keys_eq!(
        ctx.accounts.authority.key(),
        pool.pool_creator,
        PredictionError::Unauthorized
    );

    do_rebalance(
        pool,
        &ctx.accounts.oracle_feed,
        &ctx.accounts.bull_vault,
        &ctx.accounts.bear_vault,
        &ctx.accounts.pool_signer,
        &ctx.accounts.token_program,
    )
}

pub fn purchase_token(
    ctx: Context<PurchaseToken>,
    is_bull: bool,
    quote_amount_in: u64,
) -> Result<()> {
    require!(quote_amount_in > 0, PredictionError::InvalidAmount);

    let pool = &mut ctx.accounts.pool;

    // sanity: protocol_fee_ata must be owned by protocol treasury signer
    require_keys_eq!(
        ctx.accounts.protocol_fee_ata.owner,
        stable_order_address(),
        PredictionError::Unauthorized
    );
    // sanity: creator fee receiver must match pool_creator
    require_keys_eq!(
        ctx.accounts.creator_quote_ata.owner,
        pool.pool_creator,
        PredictionError::Unauthorized
    );

    // 1. rebalance pool to oracle
    do_rebalance(
        pool,
        &ctx.accounts.oracle_feed,
        &ctx.accounts.bull_vault,
        &ctx.accounts.bear_vault,
        &ctx.accounts.pool_signer,
        &ctx.accounts.token_program,
    )?;

    // figure out which side buyer is minting
    let (
        chosen_vault,
        other_vault,
        chosen_mint,
        chosen_user_ata,
        other_user_ata,
        chosen_name,
        chosen_symbol,
        chosen_is_bull,
    ) = if is_bull {
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

    // snapshot balances before we do anything
    let reserve_before = chosen_vault.amount;
    let total_supply_before = chosen_mint.supply;
    let user_old_balance = chosen_user_ata.amount;
    let other_old_balance = other_user_ata.amount;

    // 2. fee breakdown
    let (protocol_fee_amt, fee_amt, creator_fee_amt, net_amount) = compute_fee_breakdown(
        quote_amount_in,
        pool.protocol_fee,
        pool.mint_fee,          // mint_fee on purchase
        pool.pool_creator_fee,
    )?;
    require!(net_amount > 0, PredictionError::InvalidAmount);

    // 3. collect user's quote tokens and route fees
    // protocol fee -> protocol_fee_ata
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

    // mint_fee portion -> other_vault
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

    // creator_fee -> creator_quote_ata
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

    // net into chosen_vault (the side I'm buying)
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

    // 4. calculate how many outcome tokens to mint
    let (mint_amount, price_per_token) = calculate_mint_amount(
        reserve_before,
        total_supply_before,
        net_amount,
    )?;

    // 5. mint them to buyer
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

    // 6. update buyer's UserRegistryAccount (avg cost basis!)
    let ur = &mut ctx.accounts.user_registry;
    if ur.user == Pubkey::default() {
        ur.user = ctx.accounts.buyer.key();
    }

    if let Some(pos) = ur.get_position_mut(pool.key()) {
        if chosen_is_bull {
            // new avg for bull side
            let new_avg = weighted_avg_price(
                user_old_balance,
                pos.bull_avg_price,
                mint_amount,
                price_per_token,
            )?;
            pos.bull_avg_price = new_avg;
        } else {
            let new_avg = weighted_avg_price(
                user_old_balance,
                pos.bear_avg_price,
                mint_amount,
                price_per_token,
            )?;
            pos.bear_avg_price = new_avg;
        }
    } else {
        // first time user touches this pool
        // if they bought bull: bull price set, bear avg 0
        // if they bought bear: bear price set, bull avg 0
        let (bull_avg, bear_avg) = if chosen_is_bull {
            (price_per_token, 0u64)
        } else {
            (0u64, price_per_token)
        };
        ur.insert_new_position(
            ctx.accounts.buyer.key(),
            pool.key(),
            bull_avg,
            bear_avg,
        );
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

pub fn redeem_token(
    ctx: Context<RedeemToken>,
    is_bull: bool,
    amount_out_tokens: u64,
) -> Result<()> {
    require!(amount_out_tokens > 0, PredictionError::InvalidAmount);

    let pool = &mut ctx.accounts.pool;

    // sanity on fee receivers
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

    // rebalance first
    do_rebalance(
        pool,
        &ctx.accounts.oracle_feed,
        &ctx.accounts.bull_vault,
        &ctx.accounts.bear_vault,
        &ctx.accounts.pool_signer,
        &ctx.accounts.token_program,
    )?;

    // choose which side we're burning
    let (
        chosen_mint,
        chosen_user_ata,
        chosen_vault,
        other_vault,
        chosen_name,
        chosen_symbol,
        chosen_is_bull,
    ) = if is_bull {
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

    // seller must have enough to burn
    require!(
        chosen_user_ata.amount >= amount_out_tokens,
        PredictionError::InsufficientBalance
    );

    // can't burn 100% of supply (same semantics as Move)
    let total_supply_before = chosen_mint.supply;
    require!(total_supply_before > 0, PredictionError::ZeroTotalSupply);
    require!(
        total_supply_before > amount_out_tokens,
        PredictionError::InvalidAmount
    );

    let reserve_before = chosen_vault.amount;
    let quote_to_return = calculate_burn_amount(
        reserve_before,
        total_supply_before,
        amount_out_tokens,
    )?;
    require!(
        chosen_vault.amount >= quote_to_return,
        PredictionError::InsufficientBalance
    );

    // burn the user's outcome tokens
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

    // fees on redemption (burn_fee)
    let (protocol_fee_amt, fee_amt, creator_fee_amt, net_amount) = compute_fee_breakdown(
        quote_to_return,
        pool.protocol_fee,
        pool.burn_fee,
        pool.pool_creator_fee,
    )?;
    require!(net_amount > 0, PredictionError::InvalidAmount);

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

    // creator fee -> creator_quote_ata
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

    // net payout -> seller_quote_ata
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

    // reload seller's ATAs to get final balances *after* burn
    ctx.accounts.seller_bull_ata.reload()?;
    ctx.accounts.seller_bear_ata.reload()?;

    let remaining_bull = ctx.accounts.seller_bull_ata.amount;
    let remaining_bear = ctx.accounts.seller_bear_ata.amount;

    // update user's avg price tracking in UserRegistryAccount
    let ur = &mut ctx.accounts.user_registry;
    if let Some(pos) = ur.get_position_mut(pool.key()) {
        if chosen_is_bull {
            if remaining_bull == 0 {
                pos.bull_avg_price = 0;
            }
        } else {
            if remaining_bear == 0 {
                pos.bear_avg_price = 0;
            }
        }
    }

    // remove pool from user's registry if they fully exited both sides
    ur.remove_position_if_empty(pool.key(), remaining_bull, remaining_bear);

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

// =========================
// ===== Contexts ==========
// =========================
//
// Note: seeds/bump logic mirrors how Anchor PDAs are usually set up.
// We enforce ownership / mint matches using `constraint = ...`
// where it's important. That keeps your invariants on-chain.

// Create a brand new prediction pool.
#[derive(Accounts)]
pub struct CreatePool<'info> {
    // The wallet actually creating/funding the pool and receiving the initial bull/bear.
    #[account(mut)]
    pub payer: Signer<'info>,

    /// The fee receiver for pool_creator_fee. For simplicity we assume this == payer.
    /// CHECK: we only read the pubkey and compare it to payer.
    pub pool_creator: UncheckedAccount<'info>,

    // Global registry of all pools (init first time).
    #[account(
        init_if_needed,
        payer = payer,
        space = PoolRegistryAccount::INIT_SPACE,
        seeds = [b"pool_registry"],
        bump
    )]
    pub registry: Account<'info, PoolRegistryAccount>,

    // The pool account itself (new account).
    #[account(
        init,
        payer = payer,
        // we give ourselves generous space for strings + fields.
        space = 8
            + 4 + 64        // name
            + 4 + 256       // description
            + 4 + 32        // bull_name
            + 4 + 10        // bull_symbol
            + 4 + 32        // bear_name
            + 4 + 10        // bear_symbol
            + 4             // pair_id
            + 32            // asset_address
            + 32            // quote_mint
            + 8             // current_price
            + 32            // bull_mint
            + 32            // bear_mint
            + 32            // bull_vault
            + 32            // bear_vault
            + 8 + 8 + 8 + 8 // fees
            + 32            // pool_creator
            + 1             // bump
    )]
    pub pool: Account<'info, PoolAccount>,

    // PDA signer that will control vaults + have mint authority over bull_mint & bear_mint
    /// CHECK: PDA, no lamports needed.
    #[account(
        seeds = [b"pool_signer", pool.key().as_ref()],
        bump
    )]
    pub pool_signer: UncheckedAccount<'info>,

    // Outcome token mints (Bull & Bear)
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

    // The quote token mint for settlement (USDC/wSOL/etc).
    pub quote_mint: Account<'info, Mint>,

    // Vault accounts that hold the quote token, authority is pool_signer PDA.
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

    // Payer's quote token ATA funding initial liquidity
    #[account(
        mut,
        constraint = funding_ata.owner == payer.key(),
        constraint = funding_ata.mint == quote_mint.key(),
    )]
    pub funding_ata: Account<'info, TokenAccount>,

    // Payer's Bull/Bear ATAs to receive initial minted outcome tokens
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

    // Per-user registry (positions + avg prices).
    #[account(
        init_if_needed,
        payer = payer,
        space = UserRegistryAccount::INIT_SPACE,
        seeds = [b"user_registry", payer.key().as_ref()],
        bump
    )]
    pub user_registry: Account<'info, UserRegistryAccount>,

    // Oracle feed account (Supra-style)
    pub oracle_feed: Account<'info, OraclePriceFeedAccount>,

    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, System>,
    pub rent: Sysvar<'info, Rent>,
}

// Manual admin-triggered rebalance call
#[derive(Accounts)]
pub struct RebalancePoolEntry<'info> {
    #[account(mut)]
    pub authority: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, PoolAccount>,

    /// CHECK: PDA signer for pool
    #[account(
        seeds = [b"pool_signer", pool.key().as_ref()],
        bump = pool.pool_signer_bump
    )]
    pub pool_signer: UncheckedAccount<'info>,

    #[account(mut)]
    pub bull_vault: Account<'info, TokenAccount>,

    #[account(mut)]
    pub bear_vault: Account<'info, TokenAccount>,

    pub oracle_feed: Account<'info, OraclePriceFeedAccount>,

    pub token_program: Program<'info, Token>,
}

// Buy flow
#[derive(Accounts)]
pub struct PurchaseToken<'info> {
    #[account(mut)]
    pub buyer: Signer<'info>,

    #[account(mut)]
    pub pool: Account<'info, PoolAccount>,

    /// CHECK: PDA authority
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

    // Buyer pays from here (quote token ATA)
    #[account(
        mut,
        constraint = buyer_quote_ata.owner == buyer.key(),
        constraint = buyer_quote_ata.mint == quote_mint.key(),
    )]
    pub buyer_quote_ata: Account<'info, TokenAccount>,

    // Protocol fee receiver (must belong to stable_order_address())
    #[account(
        mut,
        constraint = protocol_fee_ata.mint == quote_mint.key(),
    )]
    pub protocol_fee_ata: Account<'info, TokenAccount>,

    // Creator fee receiver (must belong to pool_creator)
    #[account(
        mut,
        constraint = creator_quote_ata.mint == quote_mint.key(),
    )]
    pub creator_quote_ata: Account<'info, TokenAccount>,

    // Buyer's Bull/Bear ATAs (auto-create)
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

    // User's registry (avg prices + which pools they're in)
    #[account(
        init_if_needed,
        payer = buyer,
        space = UserRegistryAccount::INIT_SPACE,
        seeds = [b"user_registry", buyer.key().as_ref()],
        bump
    )]
    pub user_registry: Account<'info, UserRegistryAccount>,

    pub oracle_feed: Account<'info, OraclePriceFeedAccount>,

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
    pub pool: Account<'info, PoolAccount>,

    /// CHECK: PDA authority
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

    // protocol fee receiver
    #[account(
        mut,
        constraint = protocol_fee_ata.mint == quote_mint.key(),
    )]
    pub protocol_fee_ata: Account<'info, TokenAccount>,

    // creator fee receiver
    #[account(
        mut,
        constraint = creator_quote_ata.mint == quote_mint.key(),
    )]
    pub creator_quote_ata: Account<'info, TokenAccount>,

    // Seller's outcome balances
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

    // User registry for this seller (to update avg cost + remove pool if fully exited)
    #[account(
        mut,
        seeds = [b"user_registry", seller.key().as_ref()],
        bump
    )]
    pub user_registry: Account<'info, UserRegistryAccount>,

    pub oracle_feed: Account<'info, OraclePriceFeedAccount>,

    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, System>,
    pub rent: Sysvar<'info, Rent>,
}
