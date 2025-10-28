use anchor_lang::prelude::*;
use crate::{USER_REGISTRY_INIT_CAPACITY};

// This is like (pool -> {bull_avg, bear_avg}) for one user.
#[derive(AnchorSerialize, AnchorDeserialize, Clone, Copy, Default)]
pub struct PositionEntry {
    pub pool: Pubkey,
    pub bull_avg_price: u64, // scaled by PRECISION_SCALE
    pub bear_avg_price: u64,
}

#[account]
pub struct UserRegistryAccount {
    pub user: Pubkey,
    pub positions: Vec<PositionEntry>,
}

impl UserRegistryAccount {
    // Rough sizing: discriminator (8)
    // + user (32)
    // + vec len (4)
    // + positions capacity (~32 entries * 48 bytes each)
    //   PositionEntry ~ 32 + 8 + 8 = 48 bytes
    pub const INIT_SPACE: usize = 8 + 32 + 4 + (USER_REGISTRY_INIT_CAPACITY * (32 + 8 + 8));

    pub fn get_position_mut(&mut self, pool: Pubkey) -> Option<&mut PositionEntry> {
        self.positions.iter_mut().find(|p| p.pool == pool)
    }

    pub fn get_position(&self, pool: Pubkey) -> Option<&PositionEntry> {
        self.positions.iter().find(|p| p.pool == pool)
    }

    // Called during create_pool to seed creator's position, or if we ever need to insert fresh.
    pub fn insert_new_position(
        &mut self,
        user: Pubkey,
        pool: Pubkey,
        bull_avg_price: u64,
        bear_avg_price: u64,
    ) {
        if self.user == Pubkey::default() {
            self.user = user;
        }
        self.positions.push(PositionEntry {
            pool,
            bull_avg_price,
            bear_avg_price,
        });
    }

    // If both balances in the pool are zero after redemption, we fully remove the pool.
    pub fn remove_position_if_empty(
        &mut self,
        pool: Pubkey,
        remaining_bull: u64,
        remaining_bear: u64,
    ) {
        if remaining_bull == 0 && remaining_bear == 0 {
            if let Some(idx) = self.positions.iter().position(|p| p.pool == pool) {
                self.positions.swap_remove(idx);
            }
        }
    }
}
