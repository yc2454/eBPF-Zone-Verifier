use std::collections::{HashMap, HashSet};
use log::info;

use crate::analysis::state::State;
use crate::analysis::reg_types::{RegType, TypeState};
use crate::zone::dbm::{Dbm, INF};
use crate::analysis::env::VerifierEnv;
use crate::common::config::VerifierConfig;
use crate::zone::domain::Reg;

/// Widening threshold - start widening after this many visits
const WIDEN_THRESHOLD: u32 = 2;

/// State tracking info for a single PC
struct PcStateInfo {
    /// The canonical state (widened over time)
    canonical: State,
    /// Number of times we've visited this PC
    visit_count: u32,
}

/// Manages pruning decisions with widening support
pub struct PruningManager {
    /// Tracked states per PC
    pc_states: HashMap<usize, PcStateInfo>,
}

impl PruningManager {
    pub fn new() -> Self {
        Self {
            pc_states: HashMap::new(),
        }
    }
}

/// Returns TRUE if the current state is covered by a previously explored state.
/// If TRUE, we can safely prune (stop analyzing this path).
pub fn is_state_visited(
    env: &mut VerifierEnv,
    state: &State,
    config: &VerifierConfig,
    pruning_mgr: &mut PruningManager,
) -> bool {
    let pc = state.pc;

    // 1. Only check at prune points (loop heads / branch targets)
    if pc < env.insn_aux_data.len() && !env.insn_aux_data[pc].prune_point {
        return false;
    }

    let aux_data = env.insn_aux_data.get(pc);
    if aux_data.is_none() {
        return false;
    }

    let live_regs = &env.insn_aux_data[pc].live_regs;

    // 2. Check against tracked state for this PC
    match pruning_mgr.pc_states.get_mut(&pc) {
        Some(info) => {
            info.visit_count += 1;

            // Check if we're in a loop iteration (PC already on current path)
            let in_loop = state.history_idx
                .map(|idx| env.history.path_contains_pc(idx, pc))
                .unwrap_or(false);

            if in_loop {
                // Don't prune loop iterations - let instruction limit catch infinite loops
                return false;
            }

            // Check if current state is subsumed by canonical state
            if state_subsumes(&info.canonical, state, live_regs, config) {
                info!("Pruning happened at pc {}.\nOld state: {:?}\nNew state: {:?}", pc, info.canonical.types, state.types);
                return true; // Prune
            }

            // Not subsumed - widen if we've visited enough times
            if config.use_widening && info.visit_count >= WIDEN_THRESHOLD {
                widen_state(&mut info.canonical, state, live_regs);
            }

            false
        }
        None => {
            // First visit - store state
            pruning_mgr.pc_states.insert(pc, PcStateInfo {
                canonical: state.clone(),
                visit_count: 1,
            });
            false
        }
    }
}

// For debugging: log why subsumption failed
#[allow(dead_code)]
fn log_subsumption_failure(
    old: &State,
    cur: &State,
    live_regs: &HashSet<Reg>,
    pc: usize,
) {
    eprintln!("[DEBUG] Subsumption failed at PC {}", pc);
    
    // Check types first
    for r in live_regs {
        let old_ty = old.types.get(*r);
        let cur_ty = cur.types.get(*r);
        
        if !type_subsumes(&old_ty, &cur_ty) {
            eprintln!("  {:?}: type mismatch", r);
            eprintln!("    old: {:?}", old_ty);
            eprintln!("    cur: {:?}", cur_ty);
        }
    }
    
    // If types match, check DBM
    if types_subsume(&old.types, &cur.types, live_regs) {
        eprintln!("  Types OK, checking DBM...");
        let zero_idx = 0;
        
        for r in live_regs {
            let r_idx = r.idx();
            
            let old_upper = old.dbm.get_idx(r_idx, zero_idx);
            let cur_upper = cur.dbm.get_idx(r_idx, zero_idx);
            let old_lower = old.dbm.get_idx(zero_idx, r_idx);
            let cur_lower = cur.dbm.get_idx(zero_idx, r_idx);
            
            if old_upper < cur_upper {
                eprintln!("  {:?}: upper bound mismatch (old={}, cur={})", 
                         r, old_upper, cur_upper);
            }
            if old_lower < cur_lower {
                eprintln!("  {:?}: lower bound mismatch (old={}, cur={})", 
                         r, old_lower, cur_lower);
            }
        }
    }
}

// ============================================================================
// Subsumption Checking
// ============================================================================

/// Check if `old` state subsumes `cur` state.
/// Returns true if every concrete state represented by `cur` is also in `old`.
fn state_subsumes(
    old: &State,
    cur: &State,
    live_regs: &HashSet<Reg>,
    config: &VerifierConfig,
) -> bool {
    // Skip DBM check if configured (for debugging)
    if config.skip_dbm_check {
        return types_subsume(&old.types, &cur.types, live_regs);
    }

    types_subsume(&old.types, &cur.types, live_regs)
        && dbm_subsumes(&old.dbm, &cur.dbm, live_regs)
}

/// Check if old types subsume current types for live registers
fn types_subsume(
    old: &TypeState,
    cur: &TypeState,
    live_regs: &HashSet<Reg>,
) -> bool {
    for r in live_regs {
        if !type_subsumes(&old.get(*r), &cur.get(*r)) {
            return false;
        }
    }
    true
}

/// Check if old_ty subsumes cur_ty (old is at least as general)
fn type_subsumes(old_ty: &RegType, cur_ty: &RegType) -> bool {
    use RegType::*;

    match (old_ty, cur_ty) {
        // Identical simple types
        (ScalarValue, ScalarValue) => true,
        (NotInit, NotInit) => true,
        (PtrToCtx, PtrToCtx) => true,
        (PtrToPacketEnd, PtrToPacketEnd) => true,

        // Anything subsumes NotInit (dead register)
        (_, NotInit) => true,

        // Packet pointers: old must have >= range (allows more accesses)
        (
            PtrToPacket { id: _id1, range: r1, is_base: b1, off: o1 },
            PtrToPacket { id: _id2, range: r2, is_base: b2, off: o2 },
        ) => b1 == b2 && o1 == o2 && r1 >= r2,

        // Mem pointers: old must have >= range
        (
            PtrToMem { region: reg1, range: r1 },
            PtrToMem { region: reg2, range: r2 },
        ) => reg1 == reg2 && r1 >= r2,

        // PtrToMapValue (known non-null)
        (
            PtrToMapValue { offset: o1, map_idx: m1 },
            PtrToMapValue { offset: o2, map_idx: m2 },
        ) => {
            m1 == m2 && match (o1, o2) {
                (None, _) => true,             // Unknown offset subsumes all
                (Some(a), Some(b)) => a == b,  // Must match exactly  
                (Some(_), None) => false,      // Known doesn't subsume unknown
            }
        }

        // PtrToMapValueOrNull (result of map lookup, may be null)
        (
            PtrToMapValueOrNull { id: id1, map_idx: m1 },
            PtrToMapValueOrNull { id: id2, map_idx: m2 },
        ) => {
            // Same map, same lookup ID
            m1 == m2 && id1 == id2
        }

        (PtrToSocket { id: id1 }, PtrToSocket { id: id2 }) => id1 == id2,
        (PtrToSocketOrNull { id: id1 }, PtrToSocketOrNull { id: id2 }) => id1 == id2,

        // Stack pointers
        (
            PtrToStack { offset: o1 },
            PtrToStack { offset: o2 },
        ) => match (o1, o2) {
            (None, _) => true,             // Unknown subsumes all
            (Some(a), Some(b)) => a == b,  // Must match exactly
            (Some(_), None) => false,      // Known doesn't subsume unknown
        },

        // Different types - no subsumption
        _ => false,
    }
}

/// Check if old DBM subsumes current DBM for live registers.
/// old subsumes cur iff old is LESS constrained (allows more values).
fn dbm_subsumes(old: &Dbm, cur: &Dbm, live_regs: &HashSet<Reg>) -> bool {
    let zero_idx = 0;

    for r in live_regs {
        let r_idx = r.idx();

        // Upper bound: r - 0 ≤ c  means  r ≤ c
        // old subsumes cur if old_upper >= cur_upper
        let old_upper = old.get_idx(r_idx, zero_idx);
        let cur_upper = cur.get_idx(r_idx, zero_idx);
        if old_upper < cur_upper {
            return false; // old has tighter upper bound
        }

        // Lower bound: 0 - r ≤ c  means  r ≥ -c
        // old subsumes cur if old_lower >= cur_lower
        let old_lower = old.get_idx(zero_idx, r_idx);
        let cur_lower = cur.get_idx(zero_idx, r_idx);
        if old_lower < cur_lower {
            return false; // old has tighter lower bound
        }
    }

    true
}

// ============================================================================
// Widening
// ============================================================================

/// Widen the stored state to cover the current state.
/// After widening, stored will subsume both its old value and current.
fn widen_state(stored: &mut State, current: &State, live_regs: &HashSet<Reg>) {
    // Widen DBM
    widen_dbm(&mut stored.dbm, &current.dbm, live_regs);

    // Widen types
    widen_types(&mut stored.types, &current.types, live_regs);
}

/// Widen DBM: if current is less constrained, go to infinity
fn widen_dbm(stored: &mut Dbm, current: &Dbm, live_regs: &HashSet<Reg>) {
    let zero_idx = 0;

    for r in live_regs {
        let r_idx = r.idx();

        // Upper bound
        let stored_upper = stored.get_idx(r_idx, zero_idx);
        let current_upper = current.get_idx(r_idx, zero_idx);
        if current_upper > stored_upper {
            // Current allows larger values - widen to infinity
            stored.set_idx(r_idx, zero_idx, INF);
        }

        // Lower bound
        let stored_lower = stored.get_idx(zero_idx, r_idx);
        let current_lower = current.get_idx(zero_idx, r_idx);
        if current_lower > stored_lower {
            // Current allows smaller values - widen to infinity
            stored.set_idx(zero_idx, r_idx, INF);
        }
    }
}

/// Widen types: generalize to cover both states
fn widen_types(
    stored: &mut TypeState,
    current: &TypeState,
    live_regs: &HashSet<Reg>,
) {
    for r in live_regs {
        let stored_ty = stored.get(*r);
        let current_ty = current.get(*r);

        if let Some(widened) = widen_type(&stored_ty, &current_ty) {
            stored.set(*r, widened);
        }
    }
}

/// Widen two types, returning a type that covers both.
/// Returns None if types are incompatible (shouldn't happen at same PC).
fn widen_type(stored: &RegType, current: &RegType) -> Option<RegType> {
    use RegType::*;

    match (stored, current) {
        // Already subsumed - no change needed
        _ if type_subsumes(stored, current) => None,

        // Packet pointers - take minimum range
        (
            PtrToPacket { id: _, range: r1, is_base: b1, off: o1 },
            PtrToPacket { id: _, range: r2, is_base: b2, off: o2 },
        ) if b1 == b2 && o1 == o2 => {
            // Take minimum range (conservative)
            Some(PtrToPacket {
                id: 0,  // an arbitrary ID
                range: (*r1).min(*r2),
                is_base: *b1,
                off: *o1,
            })
        }

        // Mem pointers - take minimum range
        (
            PtrToMem { region: reg1, range: r1 },
            PtrToMem { region: reg2, range: r2 },
        ) if reg1 == reg2 => {
            Some(PtrToMem {
                region: *reg1,
                range: (*r1).min(*r2),
            })
        }

        // Stack pointers - widen to unknown offset
        (
            PtrToStack { offset: Some(_) },
            PtrToStack { offset: Some(_) },
        ) => Some(PtrToStack { offset: None }),

        (
            PtrToStack { offset: Some(_) },
            PtrToStack { offset: None },
        ) => Some(PtrToStack { offset: None }),

        // Incompatible types - can't widen
        // This shouldn't happen if program is well-formed
        _ => None,
    }
}