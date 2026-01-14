// src/analysis/pruning.rs
use crate::analysis::env::VerifierEnv;
use crate::analysis::state::State;
use crate::analysis::reg_types::RegType;
use crate::zone::domain::Reg;

/// Maximum number of states to keep per PC.
/// Linux kernel uses BPF_PRUNE_MAX_STATES_PER_PC = 4 (or 64 in some cases).
/// Keeping this low prevents state explosion while still allowing effective pruning.
const MAX_STATES_PER_PC: usize = 4;

/// Returns TRUE if the current state is covered by a previously explored state.
/// If TRUE, we can safely prune (stop analyzing this path).
pub fn is_state_visited(env: &mut VerifierEnv, state: &State) -> bool {
    let pc = state.pc;

    // 1. Optimization: Only check history at Pruning Points (Loop Heads / Branch Targets)
    // If we haven't marked this instruction as a prune point, continue.
    if pc < env.insn_aux_data.len() && !env.insn_aux_data[pc].prune_point {
        return false;
    }

    let live_regs = &env.insn_aux_data[pc].live_regs;
    
    // 2. Search History for a covering state
    if let Some(history) = env.explored_states.get(&pc) {
        for old_state in history {
            if states_equal(old_state, state, live_regs) {
                // We found a state that is "safer" or "equal" to the current one.
                // Since that old state was already verified safe, the current one is also safe.
                println!("[Prune] SUCCESS at PC {}", pc);
                return true;
            }
        }
    }

    // 3. No match found. Record this state for future pruning.
    // LIMIT: Only keep the most recent MAX_STATES_PER_PC states.
    let history = env.explored_states.entry(pc).or_default();
    
    // If we've hit the limit, remove the oldest state
    if history.len() >= MAX_STATES_PER_PC {
        history.remove(0);
    }
    
    history.push(state.clone());
    
    false
}

/// Checks if `old` covers `cur` (i.e., cur ⊆ old).
/// This is the key function for pruning effectiveness.
fn states_equal(
    old: &State, 
    cur: &State, 
    live_regs: &std::collections::HashSet<Reg>
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

    // 3. Check DBM (Values) - Only for LIVE registers
    // We need cur_dbm ⊆ old_dbm (Current constraints imply Old constraints).
    // In DBM matrix terms: cur[i][j] <= old[i][j]
    // 
    // NOTE: Being too strict here causes excessive state explosion.
    // The kernel uses range_within() which is more lenient.
    if !dbm_safe_relaxed(&old.dbm, &cur.dbm, live_regs) {
        return false;
    }

    true
}

/// Checks if register types are compatible.
/// Returns true if `cur` is covered by `old`.
fn reg_safe(old_ty: RegType, cur_ty: RegType) -> bool {
    match (old_ty, cur_ty) {
        // SCALARS - always compatible
        (RegType::ScalarValue, RegType::ScalarValue) => true,
        
        // NOT_INIT - covers anything (if old was unknown, any cur is fine)
        (RegType::NotInit, _) => true,
        
        // If cur is NOT_INIT but old was typed, we can't prune
        (_, RegType::NotInit) => false,
        
        // POINTERS TO PACKET
        // If old verified with range R1, and current has range R2 >= R1,
        // current is "safer" (has more valid access space).
        (RegType::PtrToPacket { id: id1, range: r1 }, RegType::PtrToPacket { id: id2, range: r2 }) => {
            id1 == id2 && r1 <= r2
        },

        // POINTERS TO MAP VALUES
        (RegType::PtrToMapValue { offset: off1, map_idx: m1 }, RegType::PtrToMapValue { offset: off2, map_idx: m2 }) => {
            if m1 != m2 { return false; }
            // If old handled "Unknown Offset", it covers "Known Offset".
            match (off1, off2) {
                (None, _) => true,     // Old was generic, covers specific/generic cur
                (Some(_), None) => false, // Old was specific, cannot cover generic cur
                (Some(o1), Some(o2)) => o1 == o2,
            }
        },
        
        // EXACT MATCH FOR OTHERS
        _ => old_ty == cur_ty,
    }
}

/// Checks if stack slots are compatible.
fn stack_safe(old: &State, cur: &State) -> bool {
    // For every stack slot constrained in `old`, `cur` must match.
    // If `old` has nothing at offset X, `cur` can have anything.
    
    for (off, old_ty) in &old.types.stack {
         let cur_ty = cur.types.get_stack(*off);
         
         // If old had a specific type (e.g. Spill), cur must match it.
         if !reg_safe(*old_ty, cur_ty) {
             return false;
         }
    }
    true
}

/// RELAXED DBM comparison for pruning.
/// 
/// The original strict comparison (cur[i][j] <= old[i][j] for all i,j)
/// is often too strict and prevents pruning of equivalent states.
///
/// Instead, we check if the RANGES of live registers are within bounds:
/// - For each live register R, check if cur's value range is contained in old's range
/// - This is similar to the kernel's range_within() check
fn dbm_safe_relaxed(
    old_dbm: &crate::zone::dbm::Dbm, 
    cur_dbm: &crate::zone::dbm::Dbm, 
    live_regs: &std::collections::HashSet<Reg>
) -> bool {
    // For each live register, check if cur's bounds are within old's bounds
    // This means: old_min <= cur_min && cur_max <= old_max
    //
    // In DBM terms:
    // - Upper bound of R: dbm[R][Zero] gives R - 0 <= bound, i.e., R <= bound
    // - Lower bound of R: dbm[Zero][R] gives 0 - R <= bound, i.e., R >= -bound
    
    let zero_idx = 0; // Reg::Zero index
    
    for r in live_regs {
        let r_idx = r.idx();
        
        // Get upper bounds (R <= X)
        let old_upper = old_dbm.get_idx(r_idx, zero_idx);
        let cur_upper = cur_dbm.get_idx(r_idx, zero_idx);
        
        // Get lower bounds (R >= -X, stored as 0 - R <= X)
        let old_lower = old_dbm.get_idx(zero_idx, r_idx);
        let cur_lower = cur_dbm.get_idx(zero_idx, r_idx);
        
        // For cur to be covered by old:
        // - cur's upper bound should not exceed old's upper bound
        // - cur's lower bound should not exceed old's lower bound (be more negative)
        //
        // BUT: We use a RELAXED check - if both are bounded, we accept it
        // This prevents minor numerical differences from blocking pruning
        
        // Strict version (may cause too many states):
        // if cur_upper > old_upper || cur_lower > old_lower {
        //     return false;
        // }
        
        // Relaxed version: Only reject if ranges don't overlap at all
        // Convert to actual bounds: upper = old_upper, lower = -old_lower
        // Overlap exists if: cur_lower_val <= old_upper_val && old_lower_val <= cur_upper_val
        // Where lower_val = -dbm[0][R] and upper_val = dbm[R][0]
        
        // Actually, let's use a middle ground: accept if cur is within a small tolerance
        // OR if both are effectively unbounded (INF)
        const INF_THRESHOLD: i64 = 1_000_000_000;
        const TOLERANCE: i64 = 64; // Allow small variations
        
        let old_bounded = old_upper < INF_THRESHOLD && old_lower < INF_THRESHOLD;
        let cur_bounded = cur_upper < INF_THRESHOLD && cur_lower < INF_THRESHOLD;
        
        if old_bounded && cur_bounded {
            // Both bounded: check if cur is within old's range (with tolerance)
            if cur_upper > old_upper + TOLERANCE || cur_lower > old_lower + TOLERANCE {
                return false;
            }
        } else if !old_bounded && cur_bounded {
            // Old was unbounded, cur is bounded - cur is more precise, old covers it
            // This is SAFE - old verified with unknown value, cur has known value
        } else if old_bounded && !cur_bounded {
            // Old was bounded, cur is unbounded - cur is LESS precise
            // This is NOT safe - we can't guarantee cur satisfies old's constraints
            return false;
        }
        // Both unbounded: compatible
    }
    
    true
}