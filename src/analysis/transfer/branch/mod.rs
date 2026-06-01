use crate::analysis::machine::error::VerificationError;
// src/analysis/transfer/branch/mod.rs

pub mod constraints;
pub mod interval_packet;
pub mod outcome;
pub mod refinement;

use either::Either::{Left, Right};
use log::warn;

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::analysis::transfer::alu::helpers::bcf_reg_bounds;
use crate::ast::{CmpOp, Instr, Operand, Width};
use crate::refinement::bcf::{BPF_AND, BPF_JEQ, BPF_JNE};
use crate::refinement::symbolic::RegBounds;

use self::constraints::apply_jmp_constraints;
use self::interval_packet::refine_packet_bounds_on_branch;
use self::outcome::condition_outcome;
use self::refinement::{propagate_scalar_links, refine_branch};
use super::common::{check_operand_readable, check_reg_readable};

/// Map an AST `CmpOp` to the (taken, not-taken) BCF/BPF jump-op byte pair.
/// Returns `None` for ops we don't yet symbolically model (JSET — encoded
/// as `(x & y) ≠ 0`, special-cased in BCF; deferred to Phase 2).
fn cmp_op_to_bcf_pair(op: CmpOp) -> Option<(u8, u8)> {
    use crate::refinement::bcf::{
        BPF_JEQ, BPF_JGE, BPF_JGT, BPF_JLE, BPF_JLT, BPF_JNE, BPF_JSGE, BPF_JSGT,
        BPF_JSLE, BPF_JSLT,
    };
    Some(match op {
        CmpOp::Eq => (BPF_JEQ, BPF_JNE),
        CmpOp::Ne => (BPF_JNE, BPF_JEQ),
        CmpOp::UGt => (BPF_JGT, BPF_JLE),
        CmpOp::UGe => (BPF_JGE, BPF_JLT),
        CmpOp::ULt => (BPF_JLT, BPF_JGE),
        CmpOp::ULe => (BPF_JLE, BPF_JGT),
        CmpOp::SGt => (BPF_JSGT, BPF_JSLE),
        CmpOp::SGe => (BPF_JSGE, BPF_JSLT),
        CmpOp::SLt => (BPF_JSLT, BPF_JSGE),
        CmpOp::SLe => (BPF_JSLE, BPF_JSGT),
        CmpOp::Test => return None,
    })
}

/// Kernel-mirror of `record_path_cond` (verifier.c:21072) for one branch
/// successor. Builds the branch's predicate in `state`'s own bcf DAG and
/// appends it to that state's `path_conds`. Called once per side from
/// `transfer_if` after `refine_branch` has finalized the side's reg
/// types (which is when the kernel runs `record_path_cond`, at the next
/// insn's prologue — by then any `mark_ptr_or_null_reg` demote/promote
/// has already happened).
///
/// `op_byte_for_side` is the BPF jump-op encoding for this side's
/// predicate (taken op for state_then, reversed for state_else). For
/// JSET, the side's pred wraps `AND(dst,src)` in a JEQ/JNE against 0
/// per verifier.c:20917-20927.
///
/// `narrow_for_side` carries the K==K-rewrite metadata for this side
/// (None on the side where LHS doesn't collapse to a const). See
/// `try_prove_unreachable` rewrite gate.
///
/// `src_pc` tags emitted path_conds (and lazy bound preds) for the
/// kernel's `bcf_track` suffix-only filter at refinement time.
fn record_path_cond_for_side(
    state: &mut State,
    width: Width,
    left: Reg,
    op: CmpOp,
    op_byte_for_side: u8,
    right: &Operand,
    src_pc: usize,
    narrow_for_side: Option<(u64, u8, bool, Option<usize>)>,
    // Pre-narrow LHS bounds (the reg's range as of ENTERING this branch,
    // before reg_set_min_max narrows it on the taken/not-taken side).
    // The discharge faithful-fold uses this to mirror the kernel's
    // bcf_reg_expr, which materializes a reg at its first reference with
    // the range BEFORE the current insn's narrowing (so a reload narrowed
    // to ==6 stays a VAR{JLE0xff}+JEQ6 rather than folding to `K6 JEQ K6`).
    pre_lhs_bounds: RegBounds,
) {
    if state.bcf.is_none() {
        return;
    }
    let Some(l_idx) = left.bcf_idx() else {
        return;
    };
    // Mirror kernel `record_path_cond` (verifier.c:21104): skip
    // emission when either operand isn't a SCALAR_VALUE. Checked
    // per-side because OR_NULL pointers demote to SCALAR_VALUE only
    // on the null branch (`mark_ptr_or_null_reg`, verifier.c:17318),
    // so kernel records the path_cond on the null side and skips
    // the non-null side. Without per-side checks, zovia missed the
    // null-branch conjunct (inspektor-gadget seccomp PC 142, PC 89
    // `if r0 != 0` fall-through after map_lookup_elem).
    if !state.types.get(left).is_scalar() {
        return;
    }
    if let Operand::Reg(r) = right
        && !state.types.get(*r).is_scalar()
    {
        return;
    }
    let jmp32 = width == Width::W32;
    let lhs_bounds = bcf_reg_bounds(state, left);
    let rhs_bounds = match right {
        Operand::Reg(r) => Some(bcf_reg_bounds(state, *r)),
        _ => None,
    };
    let bcf = state.bcf.as_mut().expect("checked above");
    bcf.set_current_pc(src_pc);
    // Snapshot LHS's bcf_expr materialization PC before reg_expr lazy-
    // materializes (see K==K rewrite gate in
    // feedback_kernel_probe_record_path_cond_2026-05-23.md).
    let lhs_materialize_pc: Option<usize> = bcf.get_reg_pc(l_idx);
    let cmp_l = bcf.reg_expr(l_idx, &lhs_bounds, jmp32);
    let cmp_r = match right {
        Operand::Imm(c) => {
            let v = if jmp32 { (*c as u32) as u64 } else { *c as u64 };
            bcf.add_val(v, jmp32)
        }
        Operand::Reg(r) => match r.bcf_idx() {
            Some(ri) => bcf.reg_expr(ri, &rhs_bounds.unwrap(), jmp32),
            None => bcf.add_val(0, jmp32),
        },
    };
    let pred = if op != CmpOp::Test {
        bcf.add_pred(op_byte_for_side, cmp_l, cmp_r)
    } else {
        // JSET: kernel record_path_cond (verifier.c:20917-20927).
        // The op_byte_for_side is already BPF_JNE (taken) or BPF_JEQ
        // (not-taken) per cmp_op_to_side_pair's special-cased pair below.
        let bits: u16 = if jmp32 { 32 } else { 64 };
        let and_expr = bcf.add_alu(BPF_AND, cmp_l, cmp_r, bits);
        let zero_expr = bcf.add_val(0, jmp32);
        bcf.add_pred(op_byte_for_side, and_expr, zero_expr)
    };
    // Re-tag narrow_for_side's lhs_materialize_pc with this side's
    // freshly-captured pre-reg_expr value (per-side bcf may have a
    // different cached PC than the originator).
    let narrow_now = narrow_for_side.map(|(k, op_b, j32, _)| (k, op_b, j32, lhs_materialize_pc));
    bcf.add_cond_at_narrowed(pred, src_pc, narrow_now, Some((l_idx, lhs_materialize_pc, jmp32, lhs_bounds.clone(), pre_lhs_bounds.clone())));
}

/// Transfer function for conditional branch instructions.
pub(crate) fn transfer_if(
    env: &mut VerifierEnv,
    mut state: State,
    width: Width,
    left: Reg,
    op: CmpOp,
    right: Operand,
    target: usize,
) -> Vec<State> {
    // Check operand readability
    if !check_reg_readable(env, &mut state, left) {
        return vec![];
    }
    if !check_operand_readable(env, &mut state, &right) {
        return vec![];
    }

    // Kernel `collect_linked_regs` + `push_insn_history(...,
    // linked_regs_pack(...))` (verifier.c check_cond_jmp_op L16497-16505):
    // record, on THIS conditional jump's breadcrumb, the scalar registers
    // sharing the compared register's scalar id, so the backward precision
    // walk's `bt_sync_linked_regs` can propagate precision across the
    // class. Kernel collects for src->id (BPF_X) and dst->id, and only
    // records when the class has > 1 member. Done from the pre-refinement
    // incoming `state` (kernel collects from `this_branch` before
    // `push_stack`/`reg_set_min_max`).
    if let Some(hidx) = env.current_step_idx {
        use crate::analysis::machine::reg_types::RegType;
        let mut linked: Vec<Reg> = Vec::new();
        let mut class_regs: Vec<Reg> = Vec::new();
        if let Operand::Reg(r) = right
            && state.types.get(r) == RegType::ScalarValue
            && let Some(id) = state.scalar_id(r)
        {
            class_regs.extend(state.regs_with_scalar_id(id));
        }
        if state.types.get(left) == RegType::ScalarValue
            && let Some(id) = state.scalar_id(left)
        {
            class_regs.extend(state.regs_with_scalar_id(id));
        }
        for lr in class_regs {
            if !linked.contains(&lr) {
                linked.push(lr);
            }
        }
        if linked.len() > 1 {
            env.history.set_linked_regs(hidx, linked);
        }
    }

    // --- STEP 1: Abstract Interpretation (Constraint Refinement) ---
    let mut state_then = state.clone();
    let mut state_else = state.clone();

    state_then.pc = target;
    state_else.pc = state.pc + 1;

    // Apply constraints to refine the DBM in the destination states
    match &right {
        Operand::Imm(imm) => apply_jmp_constraints(
            &mut state_then,
            &mut state_else,
            left,
            op,
            width,
            Right(*imm),
        ),
        Operand::Reg(r) => {
            apply_jmp_constraints(&mut state_then, &mut state_else, left, op, width, Left(*r));
            // Interval-specific: refine packet bounds from pointer comparisons
            refine_packet_bounds_on_branch(&mut state_then, &mut state_else, left, *r, op);
        }
    }

    // Scalar ID fan-out: propagate the constraint just applied to `left` to
    // every register and stack slot sharing its scalar id.
    propagate_scalar_links(&mut state_then, &mut state_else, left);

    // Precision sink at conditional branches. Kernel
    // `check_cond_jmp_op` (verifier.c v6.15 L16450-L16462) calls
    // `mark_chain_precision` ONLY when `is_branch_taken` resolves
    // (pred >= 0, one side dead). Firing on every conditional —
    // including the previous `back_edge_imm` heuristic for unresolved
    // back-edge compare-to-imm — eagerly over-marks loop counters and
    // accumulators precise, blocking subsumption across iterations and
    // multiplying calico-class visit counts. short_loop1 stays
    // kernel-REJECT without back_edge_imm: its JSET (`if r7 & 0x702000
    // goto head`) statically resolves (high bits of r7's tnum are
    // known after `r7 += 0x1ab064b9` from a u16 load), so the
    // static_resolves arm catches it.
    if let Some(hidx) = state.history_idx
        && condition_outcome(&state, width, left, op, &right).is_some()
    {
        let pcid = state.parent_cache_id;
        crate::analysis::flow::precision::mark_chain_precision_backward(env, hidx, pcid, left);
        if let Operand::Reg(r) = right {
            crate::analysis::flow::precision::mark_chain_precision_backward(env, hidx, pcid, r);
        }
    }

    // Branch Type Refinement (For map and socket pointers)
    let instr = Instr::If {
        width,
        left,
        op,
        right,
        target,
    };
    refine_branch(&mut state_then, &instr, true);
    refine_branch(&mut state_else, &instr, false);

    // --- BCF symbolic mirror: append the branch predicate to each side's
    // path_conds. Mirrors kernel `record_path_cond` (verifier.c:21072),
    // which fires at the NEXT insn's prologue — i.e. AFTER
    // mark_ptr_or_null_reg has demoted OR_NULL → SCALAR_VALUE on the
    // null branch (and promoted to non-null pointer on the other side).
    // Per-side asymmetric emission: the function checks each state's
    // own LHS/RHS types and skips emission when either isn't a SCALAR.
    // This is what lets the IG seccomp PC 89 `if r0 != 0` fall-through
    // contribute its `K0 == K0` conjunct (state_else's r0 was demoted
    // to scalar(0) by `maybe_demote_or_null_to_scalar`) while skipping
    // the taken side (state_then's r0 is non-null PtrToMapValue).
    // Pre-narrow LHS bounds: the reg's range BEFORE this branch's
    // reg_set_min_max narrowing (captured from the pre-split `state`,
    // which apply_jmp_constraints did NOT mutate). Threaded to the
    // discharge faithful-fold so reload/null regs materialize at their
    // first-reference range (kernel bcf_reg_expr), not the post-narrow
    // const that wrongly folds them to literals.
    let pre_lhs_bounds = bcf_reg_bounds(&state, left);
    if let Some((op_then, op_else)) = cmp_op_to_bcf_pair(op) {
        let jmp32 = width == Width::W32;
        let imm_k: Option<u64> = match &right {
            Operand::Imm(c) => Some(if jmp32 { (*c as u32) as u64 } else { *c as u64 }),
            _ => None,
        };
        // Pre-compute K==K rewrite metadata per side. Per
        // feedback_kernel_probe_record_path_cond_2026-05-23.md, the side
        // whose LHS narrows to const K on entry gets the rewrite
        // candidate; lhs_materialize_pc is filled in per-side inside
        // record_path_cond_for_side.
        let (narrow_then, narrow_else): (
            Option<(u64, u8, bool, Option<usize>)>,
            Option<(u64, u8, bool, Option<usize>)>,
        ) = match (op, imm_k) {
            (CmpOp::Eq, Some(k)) => (Some((k, op_then, jmp32, None)), None),
            (CmpOp::Ne, Some(k)) => (None, Some((k, op_else, jmp32, None))),
            _ => (None, None),
        };
        record_path_cond_for_side(
            &mut state_then, width, left, op, op_then, &right, state.pc, narrow_then,
            pre_lhs_bounds.clone(),
        );
        record_path_cond_for_side(
            &mut state_else, width, left, op, op_else, &right, state.pc, narrow_else,
            pre_lhs_bounds.clone(),
        );
    } else if matches!(op, CmpOp::Test) {
        // JSET — per-side wrap into AND(dst,src) JNE/JEQ 0.
        record_path_cond_for_side(
            &mut state_then, width, left, op, BPF_JNE, &right, state.pc, None,
            pre_lhs_bounds.clone(),
        );
        record_path_cond_for_side(
            &mut state_else, width, left, op, BPF_JEQ, &right, state.pc, None,
            pre_lhs_bounds.clone(),
        );
    }

    let backward_jump_forbidden = |st: &State| -> bool {
        if target >= st.pc {
            return false;
        }
        let on_path = st
            .history_idx
            .map(|idx| env.history.is_on_path(idx, target))
            .unwrap_or(false);
        let already_explored = env.explored_states.contains_key(&target);
        !on_path && !already_explored
    };

    // Check for statically determined branches
    if let Some(outcome) = condition_outcome(&state, width, left, op, &right) {
        // The dead side is unreachable in zovia's view. If the kernel
        // would explore that side and reject (e.g. unreachable_arsh's
        // PC 5: zovia statically rules out "w1 == 0xffffff78" but the
        // kernel's tnum loses precision on the ARSH+AND chain and
        // still explores it, hitting R2 !read_ok at PC 6), speculate
        // by attempting cvc5 unsat of the dead side's path_cond and
        // emitting a kind=UNREACHABLE bundle entry. This is the
        // matching half of kernel commit 39f5104ed029
        // (bcf_bundle_try_discharge's refine_cond=-1 → path_cond
        // fallback).
        // Pre-compute backward_jump check (uses env immutably via closure)
        // before the speculation call (uses env mutably).
        let then_backward_forbidden = outcome && backward_jump_forbidden(&state_then);
        let dead_state = if outcome { &state_else } else { &state_then };
        // Eager path-unreachable speculation is NOT a BCF mechanism:
        // every `bcf_prove_unreachable` call site in BCF (set1/0014) is
        // reactive — at a real mem-access / check_reg_arg rejection,
        // never on a statically-dead branch side. This site exists only
        // because zone/DBM makes zovia more precise than the kernel
        // (ruling out branches the kernel explores), so the single-pass
        // design pre-emitted proofs "in case". In kernel mode zovia
        // hits the *same* rejections as the kernel, so path-unreachable
        // is handled reactively (conflict-eq at the load/!read_ok sites
        // + refine_*). Restrict eager speculation to zone mode (legacy,
        // unchanged); kernel mode is reactive-only, faithful to BCF.
        if dead_state.domain.is_zone() {
            try_emit_path_unreachable_entry(env, dead_state);
        }
        return if outcome {
            if then_backward_forbidden {
                env.fail(VerificationError::BackEdge {
                    pc: state.pc,
                    target,
                });
                vec![]
            } else {
                vec![state_then]
            }
        } else {
            vec![state_else]
        };
    }

    if backward_jump_forbidden(&state_then) {
        env.fail(VerificationError::BackEdge {
            pc: state.pc,
            target,
        });
        return vec![];
    }

    // Speculatively emit a path-unreachable BCF bundle entry for any
    // branch state that zovia's abstract domain proves infeasible but
    // the kernel would explore (typically because the kernel's tnum
    // tracking loses precision across the ALU chain — see
    // `unreachable_arsh` for the ARSH+AND example). The kernel
    // ultimately rejects the dead path via `bcf_prove_unreachable` and
    // attempts a bundle discharge keyed on the path_cond's canonical
    // hash (verifier.c:24561 → bcf_bundle_try_discharge → path_cond
    // fallback, commit 39f5104ed029). If cvc5 can prove our path_cond
    // unsat, the resulting kind=UNREACHABLE entry will match the
    // kernel's hash and the kernel discharge succeeds.
    // Zone-only (same rationale as the condition_outcome site above):
    // `is_inconsistent()`-gated speculation is a DBM-ism — zone
    // manufactures branch-side contradictions the kernel smears, so
    // this is not faithful to BCF (which never speculates on
    // domain-inconsistent sides; it refines reactively at rejections).
    // Kernel mode = reactive-only. The inconsistent side is still
    // dropped below (consistent-only filter) regardless of mode.
    let zone_mode = state_then.domain.is_zone();
    if zone_mode && state_else.domain.is_inconsistent() {
        warn!("Else branch is inconsistent");
        try_emit_path_unreachable_entry(env, &state_else);
    }
    if zone_mode && state_then.domain.is_inconsistent() {
        warn!("Then branch is inconsistent");
        try_emit_path_unreachable_entry(env, &state_then);
    }

    // Return only consistent states
    let mut out = Vec::new();
    let else_ok = !state_else.domain.is_inconsistent();
    let then_ok = !state_then.domain.is_inconsistent();
    if crate::analysis::trace_pc_in_range(state.pc) {
        eprintln!(
            "[BRANCH] pc={} else_ok={} then_ok={} (else_target={} then_target={})",
            state.pc, else_ok, then_ok, state_else.pc, state_then.pc,
        );
    }
    if else_ok {
        out.push(state_else);
    }
    if then_ok {
        out.push(state_then);
    }
    out
}

/// Mirror the kernel's `bcf_refine` reg_masks=0 auto-fill for
/// `bcf_prove_unreachable` (verifier.c:24525-24534): every R0..R9 that
/// is not NOT_INIT and not a const non-scalar, then the backtrack
/// suffix base PC over that set. The kernel's `bcf_track` emits
/// br_conds only for that suffix; without this filter zovia's
/// path_cond goal carries spurious leading conditions (from its full
/// abstract-interpretation path) and its canonical hash misses the
/// kernel's bundle lookup. `None` ⇒ keep all (sound, just not as tight).
fn unreachable_base_pc(env: &VerifierEnv, state: &State) -> Option<usize> {
    use crate::analysis::machine::reg_types::RegType;
    const VARREGS: [Reg; 10] = [
        Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4,
        Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::R9,
    ];
    let mut targets: Vec<Reg> = Vec::new();
    for &r in &VARREGS {
        let ty = state.types.get(r);
        if matches!(ty, RegType::NotInit) {
            continue;
        }
        // Kernel `bcf_refine` auto-fill (verifier.c): skip every reg with
        // `type != SCALAR_VALUE && tnum_is_const(reg->var_off)` — i.e. a
        // non-scalar whose *offset* has no variable component. The kernel
        // models that offset uniformly in `reg->var_off`; zovia splits it
        // across the `RegType` enum, so the faithful mirror is
        // per-representation: most pointer offsets ride the value-tnum
        // (`get_tnum().is_const()` already captures them), but a
        // `PtrToMapValue` carries its constant offset in the *type*
        // (`offset: Some(k)`, with `None` = unknown/variable), and a
        // `*OrNull` map pointer is offset-0 by construction — neither is
        // reflected in the value-tnum. Without these, a constant-offset
        // map_value pointer (kernel-excluded) is wrongly backtracked,
        // exploding the precision suffix (calico_tc_main R7 = map_value
        // +0x4c → ~115-clause over-walk vs the kernel's 9). This is
        // additive: it only ever *excludes* more, tightening toward the
        // kernel's reg_masks — never widens the tracked set.
        // Per-pointer-kind const-offset detection. Kernel's
        // `tnum_is_const(reg->var_off)` captures every fresh non-scalar
        // pointer because the kernel uses a single `var_off` field for
        // offset across all ptr types. Zovia splits that representation
        // across the `RegType` enum; for kernel-faithful exclusion we
        // need an explicit case per ptr kind whose offset is structurally
        // constant (i.e. not modeled in the value-tnum). Calico-trace
        // 2026-05-20: missing `PtrToCtx` here caused R9 to leak into
        // `target_regs` at every BCF discharge, the walker could never
        // drain R9 (its definition is the caller's frame, not any
        // in-program insn), and `bcf_suffix_base_pc` always returned
        // `None` → full-lineage `children_unsafe` marking → 26× cache
        // invalidation → 1M-insn TIMEOUT. The kernel-side `[ZK]` probe
        // confirmed kernel `reg_masks=0x73` (excludes R9=PtrToCtx);
        // matching it brings the suffix base from None to a tight pc.
        let const_offset = state.get_tnum(r).is_const()
            || matches!(ty, RegType::PtrToMapValue { offset: Some(_), .. })
            || matches!(ty, RegType::PtrToMapValueOrNull { .. })
            // Below: ptr types whose "offset" component is structurally 0
            // (no variable-offset arithmetic possible in normal use).
            // PtrToPacket is the only ptr type with variable offset
            // (`ptr += scalar`) and is deliberately NOT excluded.
            || matches!(ty, RegType::PtrToCtx)
            || matches!(ty, RegType::PtrToPacketEnd)
            || matches!(ty, RegType::PtrToSocket { .. })
            || matches!(ty, RegType::PtrToSocketOrNull { .. })
            || matches!(ty, RegType::PtrToSockCommon { .. })
            || matches!(ty, RegType::PtrToSockCommonOrNull { .. })
            || matches!(ty, RegType::PtrToTcpSock { .. })
            || matches!(ty, RegType::PtrToTcpSockOrNull { .. })
            || matches!(ty, RegType::PtrToCpumask { .. })
            || matches!(ty, RegType::PtrToCpumaskOrNull { .. })
            || matches!(ty, RegType::PtrToArena { .. })
            || matches!(ty, RegType::PtrToArenaOrNull { .. })
            || matches!(ty, RegType::PtrToCgroup { .. })
            || matches!(ty, RegType::PtrToCgroupOrNull { .. })
            || matches!(ty, RegType::PtrToBtfId { .. })
            || matches!(ty, RegType::PtrToOwnedKptr { .. })
            || matches!(ty, RegType::PtrToMapKptr { .. });
        if !matches!(ty, RegType::ScalarValue) && const_offset {
            continue;
        }
        targets.push(r);
    }
    // Start the backtrack at the *rejecting* insn's breadcrumb (kernel
    // `backtrack_states` `last_idx = cur->insn_idx` with skip_first),
    // not the in-flight state's parent `history_idx` — the latter skips
    // one insn too early (fatal when the skipped predecessor is a
    // helper-call argument's only definition).
    let hidx = env.current_step_idx.or(state.history_idx)?;
    let targets = filter_live_unknown_targets(env, state, Some(hidx), targets);
    crate::analysis::flow::precision::bcf_suffix_base_pc(env, hidx, state.parent_cache_id, &targets)
}

/// Kernel-faithful `reg_masks` tightening (cont.20): drop a reject `reg_masks`
/// target iff it is a fully-unknown `ScalarValue` (tnum carries no constraint)
/// AND dead at the reject PC (absent from `live_regs`). Such a register holds
/// no symbolic information and the kernel never seeds it into `reg_masks`;
/// zovia's existing const-offset / `NotInit` filter misses it (it looks like a
/// live unknown scalar), so the suffix base walk over-extends.
///
/// MEASURED (from_nat_no_log pc735, proto==6 arm): R2 is a fully-unknown dead
/// scalar there → targets `0x32f`, base 529; the kernel's `reg_masks` is
/// `0x32b` (base 559, the `78171d` obligation). This filter drops exactly R2:
/// liveness is applied ONLY to unconstrained scalars, so a constrained-but-
/// dead reg (R1, kept by the kernel) and live unknowns (R8/R9, kept) are
/// untouched — reproducing `0x32b` on every arrival. See
/// project_no_log_subsumption_arc.md cont.20.
///
/// Always-on (faithful, no-regress: gated VM run was repr-19 19/19 + cilium-17
/// 17/17, bundles byte-identical on the default-config gate). ⚠️ zovia's
/// `live_regs` is per-PC, not per-path, so on a multi-arm `_no_log` program
/// the same drop applies to every arm; it has a live effect only in the lean
/// (no-shotgun) config, where it can change which obligations are emitted.
fn filter_live_unknown_targets(
    env: &VerifierEnv,
    state: &State,
    hidx: Option<usize>,
    targets: Vec<Reg>,
) -> Vec<Reg> {
    use crate::analysis::machine::reg_types::RegType;
    let live = hidx
        .and_then(|h| env.history.get(h))
        .map(|h| h.pc)
        .and_then(|pc| env.insn_aux_data.get(pc));
    let Some(live) = live else { return targets };
    targets
        .into_iter()
        .filter(|&r| {
            let unk = state.get_tnum(r).mask == u64::MAX
                && matches!(state.types.get(r), RegType::ScalarValue);
            let dead = !live.live_regs.contains(&r);
            !(unk && dead)
        })
        .collect()
}

/// Attempt path-unreachable speculation on a zovia-infeasible state and
/// push the resulting `kind=BCF_BUNDLE_KIND_UNREACHABLE` bundle entry on
/// success. Returns `true` iff an entry was emitted. Mirrors the pattern
/// in `try_bcf_refine_stack` / `try_bcf_refine_map`.
///
/// Called from two places: (a) the zone-only branch-side eager
/// speculation here, and (b) reactively from the generic-load (scalar)
/// rejection site (`memory::access`), mirroring the kernel's
/// `bcf_prove_unreachable` at verifier.c:8224→8255.
pub(crate) fn try_emit_path_unreachable_entry(env: &mut VerifierEnv, state: &State) -> bool {
    use crate::refinement::bundle::{RefineEntry, BCF_BUNDLE_KIND_UNREACHABLE};
    use crate::refinement::refine_unreachable::try_prove_unreachable;
    use log::info;

    if state.bcf.is_none() {
        return false;
    }
    let base_pc = unreachable_base_pc(env, state);
    // Mirror kernel's `vstate->last_insn_idx` retrieval at bcf_track
    // replay start: look up the prev_insn PC of the cached state AT
    // base_pc (the cache the suffix walk landed on, not the immediate
    // parent_cache_id of cur — they can differ). The filter uses this
    // to identify the immediate-predecessor branch cond (the kernel's
    // record_path_cond push at insn=base_pc, verifier.c:21117).
    let (prev_insn_pc, base_cid_dbg) = {
        use crate::analysis::machine::reg::Reg;
        use crate::analysis::machine::reg_types::RegType;
        const VARREGS: [Reg; 10] = [
            Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4,
            Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::R9,
        ];
        let targets: Vec<Reg> = VARREGS.iter().copied()
            .filter(|&r| !matches!(state.types.get(r), RegType::NotInit))
            .filter(|&r| {
                let ty = state.types.get(r);
                let const_off = state.get_tnum(r).is_const()
                    || matches!(ty, RegType::PtrToMapValue { offset: Some(_), .. })
                    || matches!(ty, RegType::PtrToMapValueOrNull { .. })
                    || matches!(ty, RegType::PtrToCtx)
                    || matches!(ty, RegType::PtrToPacketEnd)
                    || matches!(ty, RegType::PtrToSocket { .. })
                    || matches!(ty, RegType::PtrToSocketOrNull { .. })
                    || matches!(ty, RegType::PtrToSockCommon { .. })
                    || matches!(ty, RegType::PtrToSockCommonOrNull { .. })
                    || matches!(ty, RegType::PtrToTcpSock { .. })
                    || matches!(ty, RegType::PtrToTcpSockOrNull { .. })
                    || matches!(ty, RegType::PtrToCpumask { .. })
                    || matches!(ty, RegType::PtrToCpumaskOrNull { .. })
                    || matches!(ty, RegType::PtrToArena { .. })
                    || matches!(ty, RegType::PtrToArenaOrNull { .. })
                    || matches!(ty, RegType::PtrToCgroup { .. })
                    || matches!(ty, RegType::PtrToCgroupOrNull { .. })
                    || matches!(ty, RegType::PtrToBtfId { .. })
                    || matches!(ty, RegType::PtrToOwnedKptr { .. })
                    || matches!(ty, RegType::PtrToMapKptr { .. });
                !(!matches!(ty, RegType::ScalarValue) && const_off)
            })
            .collect();
        let hidx = env.current_step_idx.or(state.history_idx);
        let targets = filter_live_unknown_targets(env, state, hidx, targets);
        // KERNEL-FAITHFUL PRECISION (no_log proto-arm fix, 2026-05-31):
        // mirror bcf_prove_unreachable → backtrack_states(reg_masks)'s
        // precision side-effect. The kernel marks the reject's live,
        // non-const "reg_masks" registers precise along the suffix; that
        // precision keeps sibling paths (the proto≤5 / ==6 / ≥7 arms of an
        // IP-proto switch) DISTINCT in is_state_visited, so each reaches the
        // reject and gets its own discharge. zovia computes the same
        // `targets` for the base walk but never marked them precise, so its
        // imprecise-scalar wildcard rule (regsafe NOT_EXACT: a non-precise
        // scalar is skipped) MERGED the arms — only a subset of the reject's
        // discharges were produced, leaving kernel MISSes on the unmerged
        // siblings' hashes (from_nat_no_log pc735: 618296 etc.). Marking here
        // makes the cached ancestor states carry the precision, so a later
        // sibling's is_state_visited sees range_within over disjoint proto
        // ranges ([0,5] vs [7,255]) and stays distinct. Replaces the blunt
        // ZOVIA_NO_PRUNE_WINDOW experiment knob with a targeted, kernel-shaped
        // change. Default-OFF until VM-gated (repr-19 + cilium-17 loads, watch
        // state-count). See project_no_log_subsumption_arc.md.
        if std::env::var("ZOVIA_BCF_REJECT_PRECISE").ok().as_deref() == Some("1") {
            if let Some(h) = hidx {
                for &r in &targets {
                    crate::analysis::flow::precision::mark_chain_precision_backward(env, h, state.parent_cache_id, r);
                }
            }
        }
        let landed = hidx.and_then(|hidx| {
            crate::analysis::flow::precision::bcf_suffix_base_pc_and_cache_id(env, hidx, state.parent_cache_id, &targets)
        });
        // Use only the immediate cache the suffix walker landed on (no
        // chain-skip). A previous attempt walked back through
        // parent_cache_id to find the first branch-target cache, but
        // that over-eagerly added upstream conds to trajectories whose
        // kernel-faithful prev_insn was actually NOT a scalar branch,
        // changing their hash and breaking the byte-match for existing
        // kernel-matched entries (e.g. anchor calico_tc_main hash
        // 0xd13031db2681349e flipped to MISS). Closing this requires
        // also aligning cache topology (sparse caching), not just
        // walker logic.
        let pp = landed.and_then(|(_base_pc, base_cid)| env.cached_prev_insn_pc(base_cid));
        let cid = landed.map(|(_, cid)| cid);
        (pp, cid)
    };
    if std::env::var("ZOVIA_DUMP_DISCHARGE").ok().as_deref() == Some("1") {
        eprintln!("[disc] reject@pc={} base_pc={:?} prev_insn_pc={:?} parent_cid={:?} base_cid={:?}",
                  state.pc, base_pc, prev_insn_pc, state.parent_cache_id, base_cid_dbg);
    }
    let Some(ok) = try_prove_unreachable(state, base_pc, prev_insn_pc) else {
        return false;
    };
    let entry = RefineEntry::new(
        ok.goal_root,
        ok.sym.exprs,
        ok.proof_bytes,
        BCF_BUNDLE_KIND_UNREACHABLE,
    );
    info!(
        target: "app",
        "[bcf] path-unreachable speculation: cvc5 proof {} bytes (hash {:016x})",
        entry.proof_bytes.len(),
        entry.cond_hash
    );
    if let Ok(prefix) = std::env::var("ZOVIA_BCF_DUMP_PROOF") {
        let idx = env.bcf_proofs.len();
        let path = format!("{}.{}.bcf", prefix, idx);
        match std::fs::write(&path, &entry.proof_bytes) {
            Ok(_) => info!(target: "app", "[bcf] dumped raw proof to {}", path),
            Err(e) => log::warn!(target: "app", "[bcf] proof dump to {} failed: {}", path, e),
        }
    }
    env.bcf_proofs.push(entry);
    // Also push the un-rewritten (aliased-VAR) form so previously-
    // matched hashes that happened to be the aliased shape stay in the
    // bundle alongside the kernel-shape rewrites. Without this, the
    // fresh-VAR rewrite is destructive for programs whose discharge
    // hash the kernel queries via the aliased form (calico-19
    // regressed 19/19 → 9/19 when only the rewritten form was pushed,
    // 2026-05-27).
    if let Some(ok_no_rw) = crate::refinement::refine_unreachable::try_prove_unreachable_no_rewrite(state, base_pc, prev_insn_pc) {
        let entry_no_rw = RefineEntry::new(
            ok_no_rw.goal_root,
            ok_no_rw.sym.exprs,
            ok_no_rw.proof_bytes,
            BCF_BUNDLE_KIND_UNREACHABLE,
        );
        let already_have = env.bcf_proofs.iter().any(|e| e.cond_hash == entry_no_rw.cond_hash);
        if !already_have {
            info!(
                target: "app",
                "[bcf] path-unreachable (no-rewrite): cvc5 proof {} bytes (hash {:016x})",
                entry_no_rw.proof_bytes.len(),
                entry_no_rw.cond_hash
            );
            env.bcf_proofs.push(entry_no_rw);
        }
    }

    // Register-filtered discharge (provenance-seeded, mirrors the kernel's
    // bcf_reg_expr data-dependency closure). DEFAULT-ON; set
    // ZOVIA_BCF_REGFILTER=0 as a kill-switch.
    //
    // After the immediate + ancestor PC-suffix discharges above, also emit
    // provenance-seeded register-filtered discharges: seed = the suffix's
    // most-recent branch reg, grown 1-2 def-use hops through the
    // value-expression DAG via the var_origin map, then keep only that
    // register set's branches + the bound preds materializing their VARs.
    // This synthesizes the kernel's small multi-register reject
    // conjunctions (bcf_reg_expr data-dependency closure) that the
    // PC-suffix filter alone can't isolate. Emitted at hop depths {1,2} ×
    // {rewrite, no-rewrite}; ADDITIVE + deduped by cond_hash, so it never
    // perturbs already-matched hashes — only adds.
    //
    // VM-load ground truth (2026-05-29): this flips the to_hep_*_co-re_v6
    // family (calico_tc_main reject) from -EACCES to full-load. NOTE: an
    // offline (regset × PC-window) probe earlier FAILED to reproduce the
    // needed deep hash and wrongly concluded it unreachable — the LIVE
    // discharge (real base_pc + K==K/fresh-VAR rewrite firing in ancestor
    // context) produces what the kernel needs. The VM load is the oracle.
    // See feedback_byte_level_decode_first §2026-05-29 cont.5/cont.6.
    //
    // Soundness: only cvc5-PROVEN sub-conjunctions are emitted; the kernel
    // re-checks every proof on load, so a full-load = all proofs valid
    // (FA=0 floor preserved). Risk is bundle bloat, bounded by dedup +
    // the small per-anchor goal set.
    //
    // THOROUGH-MODE ONLY: this is a coverage-widening enhancement that
    // belongs to thorough multi-pass analysis (where the calico wins
    // live). Thorough mode spawns single-pass children (each
    // --no-bcf-thorough) that do the actual analysis + discharge, marked
    // with ZOVIA_BCF_THOROUGH_PASS=1 by the parent (main.rs). We key on
    // that marker — NOT config.bcf_thorough, which is false in the
    // children where the work happens. A standalone `--no-bcf-thorough`
    // run (the cilium 60s-budget recipe) lacks the marker, so reg-filter
    // stays off there and its bundle is byte-identical to HEAD — the
    // tight time budget isn't spent on extra cvc5 solves. Kill-switch:
    // ZOVIA_BCF_REGFILTER=0.
    if std::env::var("ZOVIA_BCF_THOROUGH_PASS").ok().as_deref() == Some("1")
        && std::env::var("ZOVIA_BCF_REGFILTER").ok().as_deref() != Some("0")
    {
        use crate::refinement::refine_unreachable as ru;
        for &hops in &[1usize, 2usize] {
            for &use_rewrite in &[true, false] {
                let ok_opt = if use_rewrite {
                    ru::try_prove_unreachable_reg_filtered(state, hops)
                } else {
                    ru::try_prove_unreachable_reg_filtered_no_rewrite(state, hops)
                };
                if let Some(ok) = ok_opt {
                    let rf_entry = RefineEntry::new(
                        ok.goal_root, ok.sym.exprs, ok.proof_bytes,
                        BCF_BUNDLE_KIND_UNREACHABLE,
                    );
                    if !env.bcf_proofs.iter().any(|e| e.cond_hash == rf_entry.cond_hash) {
                        info!(target: "app",
                            "[bcf] reg-filtered (expt): {} bytes (hash {:016x}, hops={}, rw={})",
                            rf_entry.proof_bytes.len(), rf_entry.cond_hash, hops, use_rewrite);
                        env.bcf_proofs.push(rf_entry);
                    }
                }
            }
        }
    }

    // Synthetic ancestor-discharge emission. After the immediate-cache
    // discharge succeeds, walk the parent_cache_id chain backward and
    // emit additional discharges anchored at each ancestor cache. The
    // kernel sometimes queries a hash whose suffix base is DEEPER than
    // zovia's walker reaches in one segment of jmp_history — zovia's
    // jmp_history is segmented per-cache-event, so a single walker
    // call can only collect predicates within one segment; the kernel's
    // walker traverses one long history. Example: calico
    // from_nat_debug_co-re reject_pc=1732, kernel demands 8-conj hash
    // 0x673434f3469c3018 that requires base anchored pre-1562; zovia
    // walker stops at base_pc=1680. Anchoring at each chain ancestor
    // produces the kernel-needed deeper hashes.
    //
    // ADDITIVE only: keeps the immediate-cache discharge (so existing
    // matched hashes preserve their byte-for-byte alignment) and dedup
    // by cond_hash before pushing. Validated 2026-05-27 against the
    // calico-19 + cilium-17 + collected-9 VM-load gate.
    //
    // Note the existing comment above (`A previous attempt walked back
    // through parent_cache_id…`) — that attempt REPLACED the immediate
    // discharge with a chain-walked one and broke matched hashes. This
    // is the additive variant that closes the same case without that
    // regression class.
    {
        // Lean-bundle investigation (no_log 2026-05-30): the depth-64 ancestor
        // shotgun is the dominant over-emission source (~1183 proto shapes vs
        // the kernel's 22). Knob to measure/cap it. Default 64 (unchanged).
        let max_ancestor_depth: usize = std::env::var("ZOVIA_BCF_ANCESTOR_DEPTH")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(64);
        let mut cur_cid_opt = base_cid_dbg;
        let mut depth = 0;
        while depth < max_ancestor_depth {
            let Some(cur_cid) = cur_cid_opt else { break };
            let Some(&(cur_pc, cur_idx)) = env.cache_loc_by_id.get(&cur_cid) else { break };
            let Some(parent_cid) = env
                .explored_states
                .get(&cur_pc)
                .and_then(|v| v.get(cur_idx))
                .and_then(|s| s.parent_cache_id)
            else { break };
            let Some(&(ancestor_pc, _)) = env.cache_loc_by_id.get(&parent_cid) else { break };
            let ancestor_prev_pc = env.cached_prev_insn_pc(parent_cid);
            // Per-ancestor PC-suffix discharges (rewrite + no-rewrite).
            // Register-filtered discharges are PC-independent and emitted
            // once at top level, NOT per ancestor. All ADDITIVE + deduped.
            for &use_rewrite in &[true, false] {
                let ok_opt = if use_rewrite {
                    try_prove_unreachable(state, Some(ancestor_pc), ancestor_prev_pc)
                } else {
                    crate::refinement::refine_unreachable::try_prove_unreachable_no_rewrite(
                        state, Some(ancestor_pc), ancestor_prev_pc)
                };
                if let Some(ok) = ok_opt {
                    let extra_entry = RefineEntry::new(
                        ok.goal_root,
                        ok.sym.exprs,
                        ok.proof_bytes,
                        BCF_BUNDLE_KIND_UNREACHABLE,
                    );
                    let already_have = env.bcf_proofs.iter().any(|e| e.cond_hash == extra_entry.cond_hash);
                    if std::env::var("ZOVIA_DUMP_DISCHARGE").ok().as_deref() == Some("1") {
                        eprintln!(
                            "[disc-ancestor] depth={} anchor_pc={} anchor_cid={} prev_pc={:?} rw={} hash={:016x} dup={}",
                            depth, ancestor_pc, parent_cid, ancestor_prev_pc, use_rewrite,
                            extra_entry.cond_hash, already_have,
                        );
                    }
                    if !already_have {
                        info!(
                            target: "app",
                            "[bcf] ancestor-discharge: cvc5 proof {} bytes (hash {:016x}, depth={}, rw={})",
                            extra_entry.proof_bytes.len(),
                            extra_entry.cond_hash,
                            depth,
                            use_rewrite,
                        );
                        env.bcf_proofs.push(extra_entry);
                    }
                }
            }
            cur_cid_opt = Some(parent_cid);
            depth += 1;
        }
    }

    // Mirror kernel bcf_refine (verifier.c:24580-81): cached
    // ancestors on the backtrack suffix of this path-unreachable
    // refinement are no longer prune-safe — a later arrival they'd
    // subsume may reach the same reject via a different path needing
    // its own path-unreachable bundle entry (cilium bpf_wireguard
    // pc246 route-B). Scoped to the same suffix base as the
    // path_conds (kernel parents[0..vstate_cnt-1]).
    crate::analysis::flow::pruning::cache::mark_path_children_unsafe(env, state, base_pc);
    true
}
