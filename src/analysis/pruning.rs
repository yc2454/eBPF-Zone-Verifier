// src/analysis/pruning.rs
use crate::analysis::env::VerifierEnv;
use crate::analysis::state::State;
use crate::analysis::reg_types::RegType;
use crate::zone::domain::Reg;

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
                return true;
            }
        }
    }

    // 3. No match found. Record this state for future pruning.
    // Note: In a production verifier, we might limit the history size (e.g., keep only last 4 states).
    env.explored_states.entry(pc).or_default().push(state.clone());
    
    false
}

/// Checks if `old` covers `cur` (i.e., cur ⊆ old).
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

    // 3. Check DBM (Values)
    // We need cur_dbm ⊆ old_dbm (Current constraints imply Old constraints).
    // In DBM matrix terms: cur[i][j] <= old[i][j]
    if !dbm_safe(&old.dbm, &cur.dbm, live_regs) {
        return false;
    }

    true
}

/// Checks if register types are compatible.
fn reg_safe(old_ty: RegType, cur_ty: RegType) -> bool {
    match (old_ty, cur_ty) {
        // SCALARS
        (RegType::ScalarValue, RegType::ScalarValue) => true,
        
        // POINTERS TO PACKET
        // If old state verified with range R1, and current state has range R2 >= R1,
        // current is "safer" (has more valid access space), so it's covered.
        // Wait, NO. If `old` verified with range R1, it means "As long as you have R1, you are safe".
        // If `cur` has R2 < R1, `cur` might fail where `old` succeeded.
        // So we need `old.range <= cur.range`.
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
    // If `old` has nothing at offset X, `cur` can have anything (we assume old didn't read X).
    
    for (off, old_ty) in &old.types.stack {
         let cur_ty = cur.types.get_stack(*off);
         
         // If old had a specific type (e.g. Spill), cur must match it.
         // Scalar on stack is treated same as Register Scalar.
         if !reg_safe(*old_ty, cur_ty) {
             return false;
         }
    }
    true
}

/// Checks if `cur_dbm` is a subset of `old_dbm` for live registers.
fn dbm_safe(
    old_dbm: &crate::zone::dbm::Dbm, 
    cur_dbm: &crate::zone::dbm::Dbm, 
    live_regs: &std::collections::HashSet<Reg>
) -> bool {
    // 1. Identify relevant DBM indices (Zero + Live Regs)
    // We treat Reg::Zero as always live/relevant because bounds relative to 0 are critical (e.g. x < 100).
    let mut indices = vec![0]; // 0 is Reg::Zero's index in DBM
    for r in live_regs {
        // Reg::idx() returns the DBM index (Zero=0, R0=1, etc.)
        indices.push(r.idx());
    }

    // 2. Element-wise comparison
    // We need: cur[i][j] <= old[i][j]
    for &i in &indices {
        for &j in &indices {
             let c_cur = cur_dbm.get_idx(i, j);
             let c_old = old_dbm.get_idx(i, j);
             
             // If cur's bound is looser (larger) than old's, we are NOT a subset.
             if c_cur > c_old {
                 return false;
             }
        }
    }
    true
}
