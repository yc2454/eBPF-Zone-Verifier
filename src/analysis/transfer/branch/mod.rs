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
    bcf.add_cond_at_narrowed(pred, src_pc, narrow_now, Some((l_idx, lhs_materialize_pc, jmp32, lhs_bounds.clone())));
}

/// Legacy entry point — kept for symmetric callers. Splits to
/// per-side calls; see `record_path_cond_for_side` for semantics.
fn record_branch_path_conds(
    state_then: &mut State,
    state_else: &mut State,
    width: Width,
    left: Reg,
    op: CmpOp,
    right: &Operand,
    src_pc: usize,
) {
    if state_then.bcf.is_none() {
        return;
    }
    // For standard ops look up the taken/not-taken pair early so we can
    // bail before doing any work.  JSET (CmpOp::Test) is handled specially
    // below: it decomposes to AND(dst,src) JNE/JEQ 0, mirroring the kernel's
    // record_path_cond JSET path (verifier.c:20917-20927).
    let std_ops: Option<(u8, u8)> = if op != CmpOp::Test {
        let Some(pair) = cmp_op_to_bcf_pair(op) else {
            return;
        };
        Some(pair)
    } else {
        None
    };
    let Some(l_idx) = left.bcf_idx() else {
        return;
    };
    // Mirror kernel `record_path_cond` (verifier.c:20893): skip
    // emission when either operand isn't a SCALAR_VALUE. Pointer
    // comparisons (`if r1 == NULL` after a map_lookup, etc.) don't
    // produce a br_cond on the kernel side, so zovia must skip them
    // too — otherwise the bundle's canonical_hash carries spurious
    // path_conds the kernel never emits, missing the bundle lookup.
    if !state_then.types.get(left).is_scalar() {
        return;
    }
    if let Operand::Reg(r) = right
        && !state_then.types.get(*r).is_scalar()
    {
        return;
    }
    // Kernel-shape: when the JMP class is JMP32, both operands are read in
    // 32-bit form via bcf_reg_expr(reg, true) — which peels a cached
    // ZEXT_32_to_64 if present. When JMP class is 64-bit, both stay at
    // 64-bit width (no extra EXTRACT wrapping). Mirrors
    // do_check_cond_jmp_op at verifier.c:20880-20922.
    let jmp32 = width == Width::W32;
    let lhs_bounds = bcf_reg_bounds(state_then, left);
    let rhs_bounds = match right {
        Operand::Reg(r) => Some(bcf_reg_bounds(state_then, *r)),
        _ => None,
    };
    let then_bcf = state_then.bcf.as_mut().expect("checked above");
    // Set current_pc *before* reg_expr to tag any bound preds emitted
    // during lazy materialization with this JMP's source PC.
    then_bcf.set_current_pc(src_pc);
    // Snapshot the PC at which LHS's bcf_expr was most recently
    // materialized (`None` iff uncached) BEFORE the reg_expr call (which
    // may lazy-materialize and set the PC to `src_pc`). At refinement
    // time, the rewrite to `K op K` is gated on `would the LHS be
    // uncached in a fresh kernel bcf_track replay starting at base_pc?`
    // — true iff this captured PC is None or < base_pc. Kernel's
    // `bcf_reg_expr` returns a `bcf_val(K)` literal only when the
    // reg's bcf_expr is `-1` on entry (verifier.c:902 `tnum_is_const`
    // path); when cached (spill/fill propagation, prior materialize),
    // the cached var is returned and the predicate stays `VAR op K`.
    // Ground-truth probe 2026-05-23.
    let lhs_materialize_pc: Option<usize> = then_bcf.get_reg_pc(l_idx);
    let cmp_l = then_bcf.reg_expr(l_idx, &lhs_bounds, jmp32);
    let cmp_r = match right {
        Operand::Imm(c) => {
            let v = if jmp32 { (*c as u32) as u64 } else { *c as u64 };
            then_bcf.add_val(v, jmp32)
        }
        Operand::Reg(r) => match r.bcf_idx() {
            Some(ri) => then_bcf.reg_expr(ri, &rhs_bounds.unwrap(), jmp32),
            None => then_bcf.add_val(0, jmp32),
        },
    };
    let (pred_then, pred_else) = if let Some((op_then, op_else)) = std_ops {
        (
            then_bcf.add_pred(op_then, cmp_l, cmp_r),
            then_bcf.add_pred(op_else, cmp_l, cmp_r),
        )
    } else {
        // JSET: mirror kernel record_path_cond (verifier.c:20917-20927).
        // Taken  side: (dst & src) != 0
        // Not-taken side: (dst & src) == 0
        let bits: u16 = if jmp32 { 32 } else { 64 };
        let and_expr = then_bcf.add_alu(BPF_AND, cmp_l, cmp_r, bits);
        let zero_expr = then_bcf.add_val(0, jmp32);
        (
            then_bcf.add_pred(BPF_JNE, and_expr, zero_expr),
            then_bcf.add_pred(BPF_JEQ, and_expr, zero_expr),
        )
    };

    // Kernel-mirror narrowed-LHS-to-const detection. For the side that
    // takes a JEQ-K (taken side) or skips a JNE-K (not-taken side), LHS
    // narrows to const K. We pre-compute K (the imm) and the op-byte +
    // jmp32 width so canonical-hash time can rewrite `VAR op K` to
    // `K op K`, matching kernel's fresh-replay `bcf_reg_expr` const-path
    // (verifier.c:902 `tnum_is_const(reg->var_off)` → `bcf_val`). Only
    // populated when `right` is BPF_K (`Operand::Imm`); reg-reg branches
    // never produce K==K in kernel. Ground-truth probe 2026-05-23 — see
    // feedback_kernel_probe_record_path_cond_2026-05-23.md.
    let imm_k: Option<u64> = match right {
        Operand::Imm(c) => Some(if jmp32 { (*c as u32) as u64 } else { *c as u64 }),
        _ => None,
    };
    // Emit K==K-rewrite metadata for the side whose narrowing collapses
    // LHS to a const K. The rewrite-gate decision is deferred to
    // refinement time (where base_pc is known): we record the LHS's
    // materialization PC here, and `try_prove_unreachable` rewrites iff
    // that PC is None or < base_pc (i.e. uncached in a fresh replay
    // starting at base_pc).
    let (narrow_then, narrow_else): (
        Option<(u64, u8, bool, Option<usize>)>,
        Option<(u64, u8, bool, Option<usize>)>,
    ) = match (op, imm_k, std_ops) {
        (CmpOp::Eq, Some(k), Some((op_then, _))) => {
            (Some((k, op_then, jmp32, lhs_materialize_pc)), None)
        }
        (CmpOp::Ne, Some(k), Some((_, op_else))) => {
            (None, Some((k, op_else, jmp32, lhs_materialize_pc)))
        }
        _ => (None, None),
    };

    // Now mirror the **whole post-hook DAG** into state_else's bcf. The
    // pre-hook DAGs were identical (state_else.bcf was cloned from state
    // before the hook), so a wholesale replace keeps both sides
    // consistent. Then append only the not-taken pred to state_else's
    // path_conds (state_then gets the taken pred).
    let snapshot = (**then_bcf).clone();
    let lhs_meta = Some((l_idx, lhs_materialize_pc, jmp32, lhs_bounds.clone()));
    then_bcf.add_cond_at_narrowed(pred_then, src_pc, narrow_then, lhs_meta.clone());
    if let Some(else_bcf) = state_else.bcf.as_mut() {
        **else_bcf = snapshot;
        else_bcf.add_cond_at_narrowed(pred_else, src_pc, narrow_else, lhs_meta);
    }
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
        env.mark_chain_precision_backward(hidx, pcid, left);
        if let Operand::Reg(r) = right {
            env.mark_chain_precision_backward(hidx, pcid, r);
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
        );
        record_path_cond_for_side(
            &mut state_else, width, left, op, op_else, &right, state.pc, narrow_else,
        );
    } else if matches!(op, CmpOp::Test) {
        // JSET — per-side wrap into AND(dst,src) JNE/JEQ 0.
        record_path_cond_for_side(
            &mut state_then, width, left, op, BPF_JNE, &right, state.pc, None,
        );
        record_path_cond_for_side(
            &mut state_else, width, left, op, BPF_JEQ, &right, state.pc, None,
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
        // Drop the closure before mutably borrowing env.
        drop(backward_jump_forbidden);
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
    env.bcf_suffix_base_pc(hidx, state.parent_cache_id, &targets)
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
        let landed = hidx.and_then(|hidx| {
            env.bcf_suffix_base_pc_and_cache_id(hidx, state.parent_cache_id, &targets)
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
    // bcf_reg_expr data-dependency closure) is DORMANT — the supporting
    // primitives (var_origin provenance map, filter_path_conds_by_regs,
    // provenance_goal_set, try_prove_unreachable_reg_filtered) are landed
    // and tested, but no live emission is wired here.
    //
    // Why: the 2026-05-29 cascade-verify experiment showed that the
    // combined (PC-window × register-filter) mechanism reproduces the
    // shallow cascade hashes byte-exact (A 0xfe23, B 0x4eeecf via
    // regs={1,7} × base_pc∈(1512,1954]), but the DEEP hashes the program
    // actually needs to load (0x5edc, and the load-blocking 8-conj
    // 0x673434 with its 0==2 K==K literal) are NOT subsets of zovia's
    // merged trajectory — they carry the kernel's distinct per-path state
    // (cache-topology divergence). So an L-seeded selector emits near-miss
    // bloat (e.g. {6,7}→0x42a4) without loading the program. The real
    // blocker is trajectory/cache topology, not goal-set selection.
    // See feedback_byte_level_decode_first §2026-05-29 cont.5.

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
        const MAX_ANCESTOR_DEPTH: usize = 64;
        let mut cur_cid_opt = base_cid_dbg;
        let mut depth = 0;
        while depth < MAX_ANCESTOR_DEPTH {
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
    env.mark_path_children_unsafe(state, base_pc);
    true
}
