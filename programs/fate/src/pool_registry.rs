use anchor_lang::prelude::*;
use crate::POOLS_PER_PAGE;

#[account]
pub struct PoolRegistryAccount {
    pub pools: Vec<Pubkey>,
}

impl PoolRegistryAccount {
    // discriminator (8) + vec len (4) + up to 50 pool pubkeys (50 * 32)
    pub const INIT_SPACE: usize = 8 + 4 + 32 * POOLS_PER_PAGE;

    pub fn push_unique(&mut self, pool: Pubkey) {
        if !self.pools.contains(&pool) {
            self.pools.push(pool);
        }
    }
}
