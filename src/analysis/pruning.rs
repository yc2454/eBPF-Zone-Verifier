// src/analysis/pruning.rs
use crate::analysis::env::VerifierEnv;
use crate::analysis::state::State;
use crate::analysis::reg_types::RegType;
use crate::misc::config::VerifierConfig;
use crate::zone::domain::Reg;

/// Returns TRUE if the current state is covered by a previously explored state.
/// If TRUE, we can safely prune (stop analyzing this path).
pub fn is_state_visited(env: &mut VerifierEnv, state: &State, config: &VerifierConfig) -> bool {
    let pc = state.pc;

    // 1. Optimization: Only check history at Pruning Points (Loop Heads / Branch Targets)
    if pc < env.insn_aux_data.len() && !env.insn_aux_data[pc].prune_point {
        return false;
    }

    let live_regs = &env.insn_aux_data[pc].live_regs;
    
    // 2. Search History for a covering state
    if let Some(history) = env.explored_states.get(&pc) {
        for old_state in history {
            if states_equal(old_state, state, live_regs, config) {
                return true;
            }
        }
    }

    // 3. No match found. Record this state for future pruning.
    // LIMIT: Only keep the most recent max_states_per_pc states.
    let history = env.explored_states.entry(pc).or_default();
    
    if history.len() >= config.max_states_per_pc {
        history.remove(0);
    }
    
    history.push(state.clone());
    
    false
}

/// Checks if `old` covers `cur` (i.e., cur ⊆ old).
fn states_equal(
    old: &State, 
    cur: &State, 
    live_regs: &std::collections::HashSet<Reg>,
    config: &VerifierConfig,
) -> bool {
    // 1. Check Registers (Only LIVE ones)
    for &r in live_regs {
        if !reg_safe(old.types.get(r), cur.types.get(r)) {
            return false;
        }
    }

    // 2. Check Stack
    if !stack_safe(old, cur) {
        return false;
    }

    // 3. Check DBM (Values) - OPTIONAL based on config
    if !config.skip_dbm_check {
        if !dbm_safe_relaxed(&old.dbm, &cur.dbm, live_regs) {
            return false;
        }
    }
    // If skip_dbm_check is true, we skip numeric comparison entirely.
    // This is safe because type checking ensures pointer validity.

    true
}

/// Checks if register types are compatible.
/// Returns true if `cur` is covered by `old`.
fn reg_safe(old_ty: RegType, cur_ty: RegType) -> bool {
    match (old_ty, cur_ty) {
        // SCALARS - always compatible
        (RegType::ScalarValue, RegType::ScalarValue) => true,
        
        // NOT_INIT - covers anything
        (RegType::NotInit, _) => true,
        
        // If cur is NOT_INIT but old was typed, we can't prune
        (_, RegType::NotInit) => false,
        
        // POINTERS TO PACKET
        (RegType::PtrToPacket { id: id1, range: r1, is_base: _, off: off1 }, 
         RegType::PtrToPacket { id: id2, range: r2, is_base: _, off: off2 }) => {
            id1 == id2 && r1 <= r2 && off1 == off2
        },

        // POINTERS TO MAP VALUES
        (RegType::PtrToMapValue { offset: off1, map_idx: m1 }, RegType::PtrToMapValue { offset: off2, map_idx: m2 }) => {
            if m1 != m2 { return false; }
            match (off1, off2) {
                (None, _) => true,
                (Some(_), None) => false,
                (Some(o1), Some(o2)) => o1 == o2,
            }
        },

        (RegType::PtrToSocket { id: id1 }, RegType::PtrToSocket { id: id2 }) => id1 == id2,
        (RegType::PtrToSocketOrNull { id: id1 }, RegType::PtrToSocketOrNull { id: id2 }) => id1 == id2,
        (RegType::PtrToSockCommon { id: id1 }, RegType::PtrToSockCommon { id: id2 }) => id1 == id2,
        (RegType::PtrToSockCommonOrNull { id: id1 }, RegType::PtrToSockCommonOrNull { id: id2 }) => id1 == id2,
        (RegType::PtrToTcpSock { id: id1 }, RegType::PtrToTcpSock { id: id2 }) => id1 == id2,
        (RegType::PtrToTcpSockOrNull { id: id1 }, RegType::PtrToTcpSockOrNull { id: id2 }) => id1 == id2,
        
        // EXACT MATCH FOR OTHERS
        _ => old_ty == cur_ty,
    }
}

/// Checks if stack slots are compatible.
fn stack_safe(old: &State, cur: &State) -> bool {
    for (off, old_ty) in &old.types.stack {
         let cur_ty = cur.types.get_stack(*off);
         if !reg_safe(*old_ty, cur_ty) {
             return false;
         }
    }
    true
}

/// RELAXED DBM comparison for pruning.
fn dbm_safe_relaxed(
    old_dbm: &crate::zone::dbm::Dbm, 
    cur_dbm: &crate::zone::dbm::Dbm, 
    live_regs: &std::collections::HashSet<Reg>
) -> bool {
    let zero_idx = 0;
    
    for r in live_regs {
        let r_idx = r.idx();
        
        let old_upper = old_dbm.get_idx(r_idx, zero_idx);
        let cur_upper = cur_dbm.get_idx(r_idx, zero_idx);
        
        let old_lower = old_dbm.get_idx(zero_idx, r_idx);
        let cur_lower = cur_dbm.get_idx(zero_idx, r_idx);
        
        const INF_THRESHOLD: i64 = 1_000_000_000;
        const TOLERANCE: i64 = 64;
        
        let old_bounded = old_upper < INF_THRESHOLD && old_lower < INF_THRESHOLD;
        let cur_bounded = cur_upper < INF_THRESHOLD && cur_lower < INF_THRESHOLD;
        
        if old_bounded && cur_bounded {
            if cur_upper > old_upper + TOLERANCE || cur_lower > old_lower + TOLERANCE {
                return false;
            }
        } else if old_bounded && !cur_bounded {
            return false;
        }
    }
    
    true
}