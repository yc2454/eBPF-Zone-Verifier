// src/analysis/pruning.rs
use std::collections::HashMap;
use crate::dbm::Dbm;
use crate::domain::{Reg, TypeState};

/// A snapshot of a verification state (Registers + Types).
#[derive(Clone, Debug)]
pub struct VerifiedState {
    pub dbm: Dbm,
    pub reg_types: TypeState,
}

impl VerifiedState {
    pub fn new(dbm: Dbm, reg_types: TypeState) -> Self {
        VerifiedState { dbm, reg_types }
    }

    /// Checks if 'self' covers 'other'.
    /// Corresponds to `states_equal` / `regsafe` in kernel.
    fn covers(&self, other: &VerifiedState) -> bool {
        // 1. Check Types: Must be compatible (exact match for now)
        if self.reg_types != other.reg_types {
            return false;
        }

        // 2. Check Values: 'other' must be a subset of 'self'
        // If we proved [0, 100] is safe, then [0, 10] is also safe.
        self.dbm.contains(&other.dbm)
    }
}

pub struct PruningContext {
    // Map from PC -> List of states proven safe at that PC
    visited: HashMap<usize, Vec<VerifiedState>>,
}

impl PruningContext {
    pub fn new() -> Self {
        PruningContext {
            visited: HashMap::new(),
        }
    }

    /// The main pruning function.
    /// Returns TRUE if we can prune (stop analysis).
    /// Returns FALSE if we must continue (and adds current state to history).
    pub fn is_state_visited(&mut self, pc: usize, dbm: &Dbm, types: &TypeState) -> bool {
        let current = VerifiedState::new(dbm.clone(), types.clone());
        let history = self.visited.entry(pc).or_default();

        // 1. Search for a state that covers the current one
        for old_state in history.iter() {
            if old_state.covers(&current) {
                // Prune! We've seen a superset of this state before.
                return true; 
            }
        }

        // 2. If not found, record this state for future pruning
        history.push(current);
        false
    }
}