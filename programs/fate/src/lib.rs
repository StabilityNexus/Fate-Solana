use anchor_lang::prelude::*;

pub mod pool;
pub mod pool_registry;
pub mod user_registry;

// Re-export types so callers can import from crate root if they want.
pub use pool::{
    CreatePool,
    CreatePoolArgs,
    PurchaseToken,
    RedeemToken,
    RebalancePoolEntry,
    PoolAccount,
    OraclePriceFeedAccount,
};
pub use pool_registry::PoolRegistryAccount;
pub use user_registry::{UserRegistryAccount, PositionEntry};

declare_id!("Predict11111111111111111111111111111111111");

// ===== Constants shared across modules =====

pub const MAX_FEE: u64 = 1000;            // 10.00% (basis points / 10_000)
pub const MIN_PROTOCOL_FEE: u64 = 30;     // 0.30%
pub const FEE_DENOMINATOR: u64 = 10_000;  // basis points denominator
pub const PRECISION_SCALE: u64 = 1_000_000_000; // 1e9, used in price_per_token math
pub const OUTCOME_TOKEN_DECIMALS: u8 = 9; // You can tweak this
pub const USER_REGISTRY_INIT_CAPACITY: usize = 32; // preallocated positions
pub const POOLS_PER_PAGE: usize = 50; // registry prealloc

// Hardcoded address for protocol fee receiver (maps to STABLE_ORDER_ADDRESS in Sui).
pub const STABLE_ORDER_BYTES: [u8; 32] = [
    0x3c, 0x89, 0x3e, 0xb6, 0x8f, 0xfd, 0x85, 0x77,
    0xe7, 0xe6, 0x9d, 0x2c, 0x4a, 0x62, 0xfe, 0xb9,
    0xea, 0xba, 0xf7, 0x5e, 0x39, 0x35, 0xb7, 0x7a,
    0x19, 0xbb, 0x21, 0x85, 0xd7, 0xcd, 0x6d, 0xfa,
];

pub fn stable_order_address() -> Pubkey {
    Pubkey::new_from_array(STABLE_ORDER_BYTES)
}

// ===== Errors shared across modules =====

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

// ===== Program entrypoints =====
// These just forward to functions implemented in pool.rs.

#[program]
pub mod prediction_market {
    use super::*;

    pub fn create_pool(
        ctx: Context<CreatePool>,
        args: CreatePoolArgs,
    ) -> Result<()> {
        pool::create_pool(ctx, args)
    }

    pub fn rebalance_pool_entry(
        ctx: Context<RebalancePoolEntry>,
    ) -> Result<()> {
        pool::rebalance_pool_entry(ctx)
    }

    pub fn purchase_token(
        ctx: Context<PurchaseToken>,
        is_bull: bool,
        quote_amount_in: u64,
    ) -> Result<()> {
        pool::purchase_token(ctx, is_bull, quote_amount_in)
    }

    pub fn redeem_token(
        ctx: Context<RedeemToken>,
        is_bull: bool,
        amount_out_tokens: u64,
    ) -> Result<()> {
        pool::redeem_token(ctx, is_bull, amount_out_tokens)
    }
}
