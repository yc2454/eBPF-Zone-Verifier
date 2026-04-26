// src/analysis/transfer/branch/refinement.rs

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::ast::{CmpOp, Instr, Operand};
/// Promote a pointer type across all stack frames by ref/ptr id.
/// `should_promote` checks if a slot's type matches, `promote` returns the new type.
fn promote_stack_slots_all_frames(
    state: &mut State,
    should_promote: impl Fn(&RegType) -> bool,
    promote: impl Fn(&RegType) -> RegType,
) {
    for frame in state.frames.iter_mut() {
        let offsets: Vec<i16> = frame.stack.slot_offsets();
        for k in offsets {
            let ty = frame.stack.get_slot_type(k);
            if should_promote(&ty) {
                frame.stack.set_slot_type(k, promote(&ty), None);
            }
        }
    }
}

/// After `apply_jmp_constraints` tightens bounds on `left` in both branch
/// states, propagate those same refinements to every register and stack slot
/// that shares `left`'s scalar id.  Called once per branch in `transfer_if`.
pub(crate) fn propagate_scalar_links(then_s: &mut State, else_s: &mut State, left: Reg) {
    fanout_scalar_bounds(then_s, left);
    fanout_scalar_bounds(else_s, left);
}

/// Tighten every scalar-linked register/slot in `state` to the bounds that
/// `left` has *after* the branch constraint was applied.
fn fanout_scalar_bounds(state: &mut State, left: Reg) {
    let id = match state.scalar_id(left) {
        Some(id) => id,
        None => return,
    };

    let linked: Vec<Reg> = state
        .regs_with_scalar_id(id)
        .into_iter()
        .filter(|&r| r != left && r != Reg::Zero)
        .collect();

    let (lo, hi) = state.domain.get_interval(left);
    let tnum = state.get_tnum(left);

    // ── Registers ───────────────────────────────────────────────────────────
    for r in &linked {
        let r = *r;
        // Skip registers that have since become pointers: the zone domain
        // stores packet-pointer offsets as huge sentinel values in its DBM,
        // and intersecting them with scalar bounds corrupts the domain.
        if state.types.get(r) != RegType::ScalarValue {
            continue;
        }
        let (r_lo, r_hi) = state.domain.get_interval(r);
        // Guard: skip if the new bound would make this register's
        // interval empty.  That can happen when the zone domain has
        // accumulated anchor-relative constraints that manifest as
        // large sentinel values in the scalar interval.  In those
        // cases the fan-out is either a no-op (if IDs are stale) or
        // would produce a false inconsistency.  A future pass
        // (W2.1d) will clean up stale IDs at merge points; for now
        // we be conservative and only tighten when it's safe.
        if lo > r_hi || hi < r_lo {
            continue;
        }
        // Tighten (intersect) only.
        if lo > r_lo {
            state.domain.assume_ge_imm(r, lo);
        }
        if hi < r_hi {
            state.domain.assume_le_imm(r, hi);
        }
        let r_tnum = state.get_tnum(r);
        if let Some(t) = r_tnum.intersect(tnum) {
            state.set_tnum(r, t);
        }
    }

    // ── Stack slots ──────────────────────────────────────────────────────────
    // Only propagate to scalar slots; apply the same consistency guard as for
    // registers so that a subsequent fill_at doesn't load inconsistent bounds.
    for frame in state.frames.iter_mut() {
        for (_, slot) in frame.stack.slots.iter_mut() {
            if slot.scalar_id != Some(id) {
                continue;
            }
            if slot.reg_type != RegType::ScalarValue {
                continue;
            }
            if lo > slot.bounds.max || hi < slot.bounds.min {
                continue;
            }
            let new_min = if lo > slot.bounds.min { lo } else { slot.bounds.min };
            let new_max = if hi < slot.bounds.max { hi } else { slot.bounds.max };
            if new_min > new_max {
                continue; // Would make bounds inconsistent — skip
            }
            slot.bounds.min = new_min;
            slot.bounds.max = new_max;
            if let Some(t) = slot.tnum.intersect(tnum) {
                slot.tnum = t;
            }
        }
    }
}

/// Refines register types based on the outcome of a conditional branch.
pub(crate) fn refine_branch(state: &mut State, instr: &Instr, branch_taken: bool) {
    if let Instr::If {
        op,
        left,
        right: Operand::Imm(0),
        ..
    } = instr
    {
        // Determine if this path implies reg is non-null
        let is_non_null = match op {
            CmpOp::Ne => branch_taken,  // if (reg != 0) goto => taken means non-null
            CmpOp::Eq => !branch_taken, // if (reg == 0) goto => fallthrough means non-null
            CmpOp::SGe | CmpOp::UGe | CmpOp::SGt | CmpOp::UGt => branch_taken,
            CmpOp::SLe | CmpOp::ULe | CmpOp::SLt | CmpOp::ULt => !branch_taken,
            CmpOp::Test => branch_taken,
        };

        // Existing map value promotion
        if is_non_null {
            maybe_promote_map_val(state, *left);
            maybe_promote_btf_id(state, *left);
            maybe_promote_mem(state, *left);
        }

        // refine acquired references (handles both paths)
        maybe_refine_acquired_ref(state, *left, is_non_null);
    }
}

/// Promotes a Nullable Map Pointer to a Safe Map Pointer.
fn maybe_promote_map_val(state: &mut State, reg: Reg) {
    let (target_id, _target_map_idx) = match state.types.get(reg) {
        RegType::PtrToMapValueOrNull { id, map_idx } => (id, map_idx),
        _ => return,
    };
    for r in Reg::ALL {
        if let RegType::PtrToMapValueOrNull { id, map_idx } = state.types.get(r)
            && id == target_id
        {
            state.types.set(
                r,
                RegType::PtrToMapValue {
                    id,
                    offset: Some(0),
                    map_idx,
                },
            );
            // Initialize PtrOffset tracking for interval domain
            state.domain.init_map_value_ptr(r);
        }
    }
    promote_stack_slots_all_frames(
        state,
        |ty| matches!(ty, RegType::PtrToMapValueOrNull { id, .. } if *id == target_id),
        |ty| match ty {
            RegType::PtrToMapValueOrNull { id, map_idx } => RegType::PtrToMapValue {
                id: *id,
                offset: Some(0),
                map_idx: *map_idx,
            },
            _ => unreachable!(),
        },
    );
}

fn maybe_promote_btf_id(state: &mut State, reg: Reg) {
    let target_id = match state.types.get(reg) {
        RegType::PtrToBtfIdOrNull { id, .. } => id,
        _ => return,
    };
    for r in Reg::ALL {
        if let RegType::PtrToBtfIdOrNull {
            id,
            type_name,
            flags,
        } = state.types.get(r)
            && id == target_id
        {
            state
                .types
                .set(r, RegType::PtrToBtfId { type_name, flags });
        }
    }
    promote_stack_slots_all_frames(
        state,
        |ty| matches!(ty, RegType::PtrToBtfIdOrNull { id, .. } if *id == target_id),
        |ty| match ty {
            RegType::PtrToBtfIdOrNull {
                id: _,
                type_name,
                flags,
            } => RegType::PtrToBtfId {
                type_name,
                flags: *flags,
            },
            _ => unreachable!(),
        },
    );
}

fn maybe_promote_mem(state: &mut State, reg: Reg) {
    let (target_id, _) = match state.types.get(reg) {
        RegType::PtrToAllocMemOrNull { id, mem_size } => (id, mem_size),
        _ => return,
    };
    for r in Reg::ALL {
        if let RegType::PtrToAllocMemOrNull { id, mem_size } = state.types.get(r)
            && id == target_id
        {
            state.types.set(r, RegType::PtrToAllocMem { id, mem_size });
        }
    }
    promote_stack_slots_all_frames(
        state,
        |ty| matches!(ty, RegType::PtrToAllocMemOrNull { id, .. } if *id == target_id),
        |ty| match ty {
            RegType::PtrToAllocMemOrNull { id, mem_size } => RegType::PtrToAllocMem {
                id: *id,
                mem_size: *mem_size,
            },
            _ => unreachable!(),
        },
    );
}

/// True if two reg types are the same nullable acquire-tracked
/// pointer family with the same ref_id — i.e. a null check on one
/// should refine the other along the same branch. Covers all
/// acquire-style RegTypes (sockets / cpumask / arena / owned-kptr).
fn same_acquired_pointer(t1: &RegType, t2: &RegType) -> bool {
    match (t1, t2) {
        (
            RegType::PtrToSocketOrNull { ref_id: id1 },
            RegType::PtrToSocketOrNull { ref_id: id2 },
        ) => id1 == id2,
        (
            RegType::PtrToSockCommonOrNull { ref_id: id1 },
            RegType::PtrToSockCommonOrNull { ref_id: id2 },
        ) => id1 == id2,
        (RegType::PtrToTcpSockOrNull { id: id1 }, RegType::PtrToTcpSockOrNull { id: id2 }) => {
            id1 == id2
        }
        (
            RegType::PtrToCpumaskOrNull { ref_id: id1 },
            RegType::PtrToCpumaskOrNull { ref_id: id2 },
        ) => id1 == id2,
        (
            RegType::PtrToArenaOrNull { ref_id: id1, .. },
            RegType::PtrToArenaOrNull { ref_id: id2, .. },
        ) => id1 == id2,
        (
            RegType::PtrToOwnedKptrOrNull { ref_id: id1 },
            RegType::PtrToOwnedKptrOrNull { ref_id: id2 },
        ) => id1 == id2,
        _ => false,
    }
}

/// On the non-NULL path: promotes PtrToSocketOrNull → PtrToSocket (ref stays active).
/// On the NULL path: releases the reference from tracking.
fn maybe_refine_acquired_ref(state: &mut State, reg: Reg, is_non_null: bool) {
    let reg_type = state.types.get(reg);
    let target_ref_id = match reg_type {
        RegType::PtrToSocketOrNull { ref_id }
        | RegType::PtrToSockCommonOrNull { ref_id }
        | RegType::PtrToTcpSockOrNull { id: ref_id }
        | RegType::PtrToCpumaskOrNull { ref_id }
        | RegType::PtrToArenaOrNull { ref_id, .. }
        | RegType::PtrToOwnedKptrOrNull { ref_id } => ref_id,
        _ => return,
    };

    if is_non_null {
        for r in Reg::ALL {
            let ty = state.types.get(r);
            if same_acquired_pointer(&reg_type, &ty) {
                state.types.set(r, ty.to_non_null().unwrap());
            }
        }
        promote_stack_slots_all_frames(
            state,
            |ty| same_acquired_pointer(&reg_type, ty),
            |ty| ty.to_non_null().unwrap_or(RegType::ScalarValue),
        );
    } else {
        if target_ref_id.is_some() {
            state.release_ref(target_ref_id.unwrap());
        }
        for r in Reg::ALL {
            let ty = state.types.get(r);
            if same_acquired_pointer(&reg_type, &ty) {
                state.types.set(r, RegType::ScalarValue);
            }
        }
        promote_stack_slots_all_frames(
            state,
            |ty| same_acquired_pointer(&reg_type, ty),
            |_ty| RegType::ScalarValue,
        );
    }
}
