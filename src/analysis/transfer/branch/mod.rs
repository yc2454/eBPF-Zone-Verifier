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
use super::common::check_operand_readable;

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
    // PATH B: was the LHS reg uncached entering THIS branch? (kernel
    // `bcf_pre == -1` → `bcf_bound_reg` emits its bound conjuncts; cached →
    // none). Captured before reg_expr materializes it.
    let lhs_was_uncached = lhs_materialize_pc.is_none();
    // ZOVIA_BCF_LHS_EQ_PRENARROW (from_nat_fib 92e8d190, default-OFF, NON-default
    // because it's NOT additive on its own — it flips equality branches
    // folded→VAR globally, dropping the kernel's FOLDED forms like c1dae923; use
    // ONLY for a run-twice + bundle-UNION with the default folded run): for an
    // EQUALITY (`==`/`!=`) branch whose LHS enters as a NON-const range but
    // narrows to const, materialize from the PRE-narrow range so it stays
    // `VAR{JLE0xff} + JEQ K` instead of folding to `(K==K)` — the kernel's VAR
    // form (92e8d190 reload `v<=0xff, v==6`). Dual of LHS_BOUND_AT_BRANCH
    // (inequality → POST-narrow bound `u>=6`). Takes 92e8 from symdiff=6 → 1
    // (residual = base-placement JSLE5, see memory).
    let eq_prenarrow = std::env::var("ZOVIA_BCF_LHS_EQ_PRENARROW").ok().as_deref() == Some("1")
        && matches!(op, CmpOp::Eq | CmpOp::Ne)
        && lhs_was_uncached
        && lhs_bounds.const_val.is_some()
        && pre_lhs_bounds.const_val.is_none();
    let mat_l_bounds = if eq_prenarrow { &pre_lhs_bounds } else { &lhs_bounds };
    let cmp_l = bcf.reg_expr(l_idx, mat_l_bounds, jmp32);
    let rhs_idx: Option<usize> = match right {
        Operand::Reg(r) => r.bcf_idx(),
        _ => None,
    };
    let rhs_was_uncached = rhs_idx.map(|ri| bcf.get_reg_pc(ri).is_none()).unwrap_or(false);
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
    // PATH B (ZOVIA_BCF_REPLAY): mirror the kernel's `bcf_bound_reg`, which
    // emits an operand's bound conjuncts INSIDE `record_path_cond` — BEFORE the
    // branch cond is pushed, in umin/umax/smin/smax order, and ONLY when the reg
    // was freshly materialized this branch (`bcf_pre == -1`). Emitting the block
    // here (before `add_cond_at_narrowed`) reproduces the kernel's
    // [u>=K, u<=M, …] block-then-branch ORDER and per-reg first-ref dedup that
    // the post-branch replay arm (and the recording BOUND_SYNC arm) get wrong.
    // calico from_nat_fib pc748 d53387e3: V0's [u>=6, u<=0xff] precede `s>5`.
    // Const-materialized operands carry no VAR → no bound block (their value is
    // emitted directly via the K==K rewrite).
    // ZOVIA_BCF_REPLAY_FIRSTREF (default-ON) disables this deferred (branch-only)
    // arm — bounds are emitted at first materialization in materialize_reg
    // instead (kernel bcf_reg_expr→bcf_bound_reg, read OR branch).
    let replay_firstref = crate::common::config::bcf_mirror_knob("ZOVIA_BCF_REPLAY_FIRSTREF", true);
    if bcf.replay_emit_bounds && !replay_firstref {
        if lhs_was_uncached && lhs_bounds.const_val.is_none() {
            for bp in bcf.bound_reg_emit_preds(cmp_l, &lhs_bounds, jmp32) {
                bcf.add_cond(bp);
            }
        }
        if rhs_was_uncached
            && let Some(rb) = rhs_bounds.as_ref()
            && rb.const_val.is_none()
        {
            for bp in bcf.bound_reg_emit_preds(cmp_r, rb, jmp32) {
                bcf.add_cond(bp);
            }
        }
    }
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
    // Mirror the kernel's `bcf_bound_reg` (emitted per `record_path_cond`):
    // zovia's cached-VAR `reg_expr` only emits operand bounds at a reg's FIRST
    // (pre-narrow) reference, so later branches never re-emit the kernel's
    // `u>= K` conjunct (from_nat_fib pc748 d53387e3 = reconstruction goal +
    // v0 `u>= 6`). The REPLAY block is emitted BEFORE the pred above; this
    // recording-mode arm (default-OFF) is the non-replay BOUND_SYNC dedup:
    if !bcf.replay_emit_bounds
        && std::env::var("ZOVIA_BCF_BOUND_SYNC").ok().as_deref() == Some("1")
    {
        // RECORDING (additive on top of the normal first-ref bounds): re-emit
        // ONLY the tightened post-narrow UMIN when this branch raised it (proto
        // `s> 5`: pre umin=0 → post umin=6), minimizing over-emission. Reaches
        // symdiff=1 on d53387e3 (residual = one extra u>=6, see
        // project_from_nat_fib_chase: the exploration-order tail).
        // PATH A dedup: emit only when the post-narrow umin RAISED on this branch
        // (vs entering it) AND strictly exceeds the highest umin THIS path has
        // already additively emitted for the reg — so a reg crossing 0→6 emits
        // `u>= 6` once, even though both the `==6` and `!=6` branches raise it.
        let mut ub = RegBounds::unknown();
        if jmp32 {
            if lhs_bounds.u32_min > pre_lhs_bounds.u32_min
                && lhs_bounds.u32_min > bcf.bcf_sync_u32min_emitted[l_idx]
            {
                ub.u32_min = lhs_bounds.u32_min;
                bcf.bcf_sync_u32min_emitted[l_idx] = lhs_bounds.u32_min;
            }
        } else if lhs_bounds.umin > pre_lhs_bounds.umin
            && lhs_bounds.umin > bcf.bcf_sync_umin_emitted[l_idx]
        {
            ub.umin = lhs_bounds.umin;
            bcf.bcf_sync_umin_emitted[l_idx] = lhs_bounds.umin;
        }
        if ub.umin != 0 || ub.u32_min != 0 {
            for bp in bcf.bound_reg_emit_preds(cmp_l, &ub, jmp32) {
                bcf.add_cond(bp);
            }
        }
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
    // Check operand readability. Under ZOVIA_BCF_LHS_BOUND_AT_BRANCH, DEFER
    // the branch LHS's bcf_expr materialization (don't bind+bound it here at
    // its PRE-narrow range); record_path_cond_for_side then materializes it
    // POST-narrow per side, mirroring the kernel's bcf_bound_reg-in-
    // record_path_cond emission (from_nat_fib pc748 d53387e3: V0 `u>=6` must
    // precede `u<=0xff` and `s>5`, which only happens post-narrow).
    let lhs_defer_bounds = std::env::var("ZOVIA_BCF_LHS_BOUND_AT_BRANCH")
        .ok()
        .as_deref()
        == Some("1");
    if !crate::analysis::transfer::common::check_reg_readable_ex(
        env,
        &mut state,
        left,
        !lhs_defer_bounds,
    ) {
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
        if linked.len() > 1 && !env.replay_mode {
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

    // Faithful-discharge replay: return BOTH sides (recording already ran
    // for each above) so the replay driver can follow the dead edge at the
    // reject branch. Skips the static-fold and the discharge speculation —
    // the replay only needs the per-side path_cond, not exploration.
    if env.replay_mode {
        return vec![state_then, state_else];
    }

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
/// Kernel `bcf_refine` auto-fill `reg_masks` (verifier.c:24611-24620): the
/// live, non-const registers a reject backtracks to find its base. Shared by
/// `unreachable_base_pc` (base/anchor) AND the prev/cache-id computation so
/// the two `bcf_suffix_base_pc*` walks use an IDENTICAL mask. A drift here is
/// fatal: with the `pkt_const_off` exclusion missing on one side (pc274 keeps
/// R2=pkt → mask 0x2f6→wider), that walk empties at a DIFFERENT insn (pc99 vs
/// 207) → `parent_loc=None` → `base_cid=None` → the faithful REPLAY is skipped
/// and the 190-path family MISSes. See the per-clause rationale (PtrToCtx R9
/// drain, pkt_const_off) inline below.
fn unreachable_target_regs(
    env: &VerifierEnv,
    state: &State,
    hidx: Option<usize>,
) -> Vec<Reg> {
    use crate::analysis::machine::reg_types::RegType;
    const VARREGS: [Reg; 10] = [
        Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4,
        Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::R9,
    ];
    let excl_pkt_end =
        std::env::var("ZOVIA_BCF_EXCLUDE_PKT_END").ok().as_deref() == Some("1");
    let mut targets: Vec<Reg> = Vec::new();
    for &r in &VARREGS {
        let ty = state.types.get(r);
        if matches!(ty, RegType::NotInit) {
            continue;
        }
        // Skip a reg with `type != SCALAR_VALUE && tnum_is_const(var_off)`.
        // zovia splits the offset across the RegType enum, so exclude
        // per-pointer-kind (const-offset map_value / *OrNull / structurally-0
        // ptrs). Missing `PtrToCtx` once let R9 leak → base=None → 1M timeout.
        let const_offset = state.get_tnum(r).is_const()
            || matches!(ty, RegType::PtrToMapValue { offset: Some(_), .. })
            || matches!(ty, RegType::PtrToMapValueOrNull { .. })
            || matches!(ty, RegType::PtrToCtx)
            || (excl_pkt_end && matches!(ty, RegType::PtrToPacketEnd))
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
        // A PtrToPacket whose var_off is fully const (no `ptr += scalar`
        // contributor) matches the kernel's `tnum_is_const(var_off)` drop
        // (pc274 R2=pkt const-offset → kernel reg_masks 0x17b excludes it).
        // Gated `ZOVIA_BCF_PKT_CONST_REGMASK`.
        let pkt_const_off = matches!(ty, RegType::PtrToPacket)
            && !state.var_off_contributor.contains_key(&r)
            && std::env::var("ZOVIA_BCF_PKT_CONST_REGMASK").ok().as_deref() == Some("1");
        if (!matches!(ty, RegType::ScalarValue) && const_offset) || pkt_const_off {
            continue;
        }
        targets.push(r);
    }
    filter_live_unknown_targets(env, state, hidx, targets)
}

fn unreachable_base_pc(env: &VerifierEnv, state: &State) -> Option<usize> {
    // Start the backtrack at the *rejecting* insn's breadcrumb (kernel
    // `backtrack_states` `last_idx = cur->insn_idx` with skip_first), and
    // return the faithful `base->insn_idx` (parent_loc at bt-empty).
    let hidx = env.current_step_idx.or(state.history_idx)?;
    let targets = unreachable_target_regs(env, state, Some(hidx));
    let base = crate::analysis::flow::precision::bcf_suffix_base_pc(env, hidx, state.parent_cache_id, &targets);
    if std::env::var("ZOVIA_DUMP_REGMASK").ok().as_deref() == Some("1") {
        let mut mask: u32 = 0;
        for &r in &targets { mask |= 1u32 << (r as u32); }
        eprintln!("[regmask] reject_pc={} mask=0x{:x} targets={:?} base={:?}",
            state.pc, mask, targets, base);
    }
    base
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
/// Faithful discharge via base→reject replay (mirrors kernel `bcf_track`,
/// verifier.c:24633). Instead of reconstructing the goal from the live
/// state's recorded path_conds (which can include branches off the kernel's
/// actual replay path, and mis-cache pre-window materializations — see
/// from_wep_fib_dsr_debug 034f37), this re-executes the instruction path
/// from the cached base state to the reject, with a fresh bcf, so
/// `state.bcf.path_conds` is rebuilt exactly as the kernel's re-execution
/// would. Gated by `ZOVIA_BCF_REPLAY=1`. Returns the proven goal or None
/// (no base cache, path divergence, or cvc5 declined).
fn try_prove_unreachable_via_replay(
    env: &mut VerifierEnv,
    reject_state: &State,
    base_cid: u32,
) -> Vec<crate::refinement::refine_unreachable::UnreachableOk> {

    let empty = Vec::new();
    // 1. Retrieve the cached base State (with its register/domain state).
    let Some((bpc, bidx)) = env.cache_loc_by_id.get(&base_cid).copied() else { return empty };
    let Some(base_state) = env.explored_states.get(&bpc).and_then(|v| v.get(bidx)).cloned()
        else { return empty };
    let base_hidx = base_state.history_idx;

    // 2. Recover the forward base→reject instruction path by walking the
    //    Breadcrumb parent chain from the reject insn's breadcrumb.
    let Some(reject_bc) = env.current_step_idx else { return empty };
    let mut path: Vec<(usize, Instr)> = Vec::new();
    let mut cur = Some(reject_bc);
    let mut budget: usize = 200_000;
    while let Some(idx) = cur {
        if Some(idx) == base_hidx { break; }
        match budget.checked_sub(1) { Some(b) => budget = b, None => return empty }
        let Some(bc) = env.history.get(idx) else { return empty };
        path.push((bc.pc, bc.instr.clone()));
        cur = bc.parent_idx;
    }
    let dbg = std::env::var("ZOVIA_BCF_REPLAY_DEBUG").ok().as_deref() == Some("1");
    if path.is_empty() { return empty; }
    path.reverse(); // forward order: base_pc .. reject branch

    let dead_target = reject_state.pc;
    let Some(reject_pc) = env.history.get(reject_bc).map(|b| b.pc) else { return empty };
    let is_branch_reject = reject_state.pc != reject_pc;
    let n_exec = if is_branch_reject { path.len() } else { path.len() - 1 };
    if n_exec == 0 { return empty; }
    if dbg {
        eprintln!("[replay] STRUCT reject_pc={} reject_state.pc={} is_branch={} path[0]={} path[last]={} len={} n_exec={}",
            reject_pc, reject_state.pc, is_branch_reject, path[0].0, path[path.len()-1].0, path.len(), n_exec);
    }

    // 3. Reset points: None = the plain replay (bcf reset at the suffix base).
    //    NARROWBASE (default-ON) adds one per CONDITIONAL branch step k whose
    //    LHS reg NARROWS on the taken side — re-anchoring the bcf base PAST the
    //    narrowing so the LHS materializes POST-narrow (kernel bcf_track base =
    //    st->parent past the narrowing branch). Emitted ADDITIVELY (caller
    //    dedups by cond_hash). from_nat_fib pc748: the `s>5`@523 reset point
    //    yields d53387e3 (proto `[u>=6,u<=0xff]`) the plain replay misses
    //    (it re-executes 523 → proto pre-narrow = 2af13624 shape).
    let narrowbase = crate::common::config::bcf_mirror_knob("ZOVIA_BCF_REPLAY_NARROWBASE", true);
    let mut reset_points: Vec<Option<usize>> = vec![None];
    if narrowbase {
        for i in 0..n_exec {
            if matches!(path[i].1, Instr::If { .. }) {
                reset_points.push(Some(i));
            }
        }
    }

    let mut goals = Vec::new();
    for reset_after_idx in reset_points {
        let mut base_state = base_state.clone();
        base_state.reset_bcf_for_replay();
        env.replay_mode = true;
        let mut holder: Option<State> = Some(base_state);
        for i in 0..n_exec {
            let pc = path[i].0;
            let instr = path[i].1.clone();
            let st = match holder.take() { Some(s) => s, None => break };
            let mut st = st;
            st.pc = pc;
            let succ = crate::analysis::transfer::transfer(env, st, &instr);
            let next_pc = if i + 1 < path.len() { path[i + 1].0 } else { dead_target };
            holder = succ.into_iter().find(|s| s.pc == next_pc);
            if holder.is_none() { break; }
            if Some(i) == reset_after_idx {
                if let (Some(h), Instr::If { width, left, op, right, target }) =
                    (holder.as_mut(), &instr)
                {
                    if let Some((op_then, op_else)) = cmp_op_to_bcf_pair(*op) {
                        h.reset_bcf_for_replay();
                        let taken = next_pc == *target;
                        let op_byte = if taken { op_then } else { op_else };
                        let pre_b =
                            crate::analysis::transfer::alu::helpers::bcf_reg_bounds(h, *left);
                        record_path_cond_for_side(
                            h, *width, *left, *op, op_byte, right, pc, None, pre_b,
                        );
                    }
                }
            }
        }
        env.replay_mode = false;
        if let Some(mut final_state) = holder {
            if let Some(symb) = final_state.bcf.take() {
                if let Some(g) = crate::refinement::refine_unreachable::build_unreachable_from_replay(*symb) {
                    goals.push(g);
                }
            }
        }
    }
    goals
}

pub(crate) fn try_emit_path_unreachable_entry(env: &mut VerifierEnv, state: &State) -> bool {
    use crate::refinement::bundle::{RefineEntry, BCF_BUNDLE_KIND_UNREACHABLE};
    use crate::refinement::refine_unreachable::try_prove_unreachable;
    use log::info;

    // No re-entrant discharge during a replay: the replay re-executes a
    // suffix only to rebuild the path condition; it must not itself attempt
    // to discharge (which would recurse and pollute the bundle).
    if env.replay_mode {
        return false;
    }
    if state.bcf.is_none() {
        return false;
    }
    // FAITHFUL base (Phase 2, 2026-07-01). The kernel's ONE `base` from
    // backtrack_states gives BOTH the goal anchor (`base->insn_idx`, the
    // replay start) AND the marking bound (parents[] = the chain up to base).
    // `base_pc` = `base->insn_idx` (anchor, for the prove/goal calls). The
    // marking below uses `base_cid_dbg` (the base cache_id) to mark exactly
    // the `parents[]` chain — no split, no bcidx/EXCLUDE_BASE pc-window.
    let base_pc = unreachable_base_pc(env, state);
    let loop_suffix_on =
        std::env::var("ZOVIA_EXP_LOOP_SUFFIX_BASE").ok().as_deref() == Some("1");
    let flag_skip_on =
        std::env::var("ZOVIA_EXP_FLAG_SKIP_BASE").ok().as_deref() == Some("1");
    let loop_entry_on =
        std::env::var("ZOVIA_EXP_LOOP_ENTRY_BASE").ok().as_deref() == Some("1");
    // Mirror kernel's `vstate->last_insn_idx` retrieval at bcf_track
    // replay start: look up the prev_insn PC of the cached state AT
    // base_pc (the cache the suffix walk landed on, not the immediate
    // parent_cache_id of cur — they can differ). The filter uses this
    // to identify the immediate-predecessor branch cond (the kernel's
    // record_path_cond push at insn=base_pc, verifier.c:21117).
    let (prev_insn_pc, base_cid_dbg) = {
        // Shared target mask — IDENTICAL to unreachable_base_pc via the
        // common helper. A drift here (e.g. missing the pkt_const_off drop)
        // empties the cache-id walk at a different insn than the pc walk,
        // leaving base_cid=None → the faithful REPLAY is skipped and the
        // pc274 190-path family MISSes.
        let hidx = env.current_step_idx.or(state.history_idx);
        let targets = unreachable_target_regs(env, state, hidx);
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
    // Faithful base→reject replay (ZOVIA_BCF_REPLAY=1), ADDITIVE: push the
    // replay-derived entry alongside the reconstruction discharges (merge
    // dedups by cond_hash). Lets us validate replay coverage without
    // disturbing the existing path.
    // REPLAY = faithful base→reject re-execution (kernel bcf_track mirror).
    // DEFAULT-ON (kill-switch ZOVIA_BCF_REPLAY=0); ADDITIVE alongside the
    // reconstruction discharge (merge dedups by cond_hash). Pairs with
    // ZOVIA_BCF_REPLAY_FIRSTREF (also default-ON) for kernel-faithful first-ref
    // bound emission.
    if crate::common::config::bcf_mirror_knob("ZOVIA_BCF_REPLAY", true) {
        if std::env::var("ZOVIA_BCF_REPLAY_DEBUG").ok().as_deref() == Some("1") {
            eprintln!("[replay] CALL reject@pc={} base_cid={:?}", state.pc, base_cid_dbg);
        }
        if let Some(cid) = base_cid_dbg {
            for rok in try_prove_unreachable_via_replay(env, state, cid) {
                let rentry = RefineEntry::new(
                    rok.goal_root,
                    rok.sym.exprs,
                    rok.proof_bytes,
                    BCF_BUNDLE_KIND_UNREACHABLE,
                );
                if std::env::var("ZOVIA_BCF_REPLAY_DEBUG").ok().as_deref() == Some("1") {
                    eprintln!("[replay] HASH reject@pc={} hash={:016x}", state.pc, rentry.cond_hash);
                }
                if env.bcf_proofs.iter().any(|e| e.cond_hash == rentry.cond_hash) {
                    continue;
                }
                info!(target: "app",
                    "[bcf] REPLAY path-unreachable: proof {} bytes (hash {:016x})",
                    rentry.proof_bytes.len(), rentry.cond_hash);
                env.bcf_proofs.push(rentry);
            }
        }
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
    // Is this reject's PRIMARY route (its natural path-unreachable hash) one
    // we've not seen before? A duplicate route is already covered; re-marking
    // its lineage children_unsafe only re-opens convergence points and feeds
    // the route-explosion cascade (accepted_entrypoint pc274). EXP gate below.
    let primary_was_new = !env.bcf_proofs.iter().any(|e| e.cond_hash == entry.cond_hash);
    env.bcf_proofs.push(entry);
    // DEBUG (parent-hop validation, 2026-06-19): eagerly flush the
    // accumulated bcf_proofs to a path after every discharge push, so the
    // on-disk bundle reflects current proofs even when the run is killed by
    // a wall-clock timeout before analyze() reaches its write_bundle. Lets
    // us capture the accepted_entrypoint 21f06b60 entry despite the no_log
    // non-termination. Writes atomically (tmp+rename). Default-OFF.
    if let Ok(flush_path) = std::env::var("ZOVIA_BCF_EAGER_FLUSH") {
        let tmp = format!("{}.tmp", flush_path);
        if crate::refinement::bundle::write_bundle(std::path::Path::new(&tmp), &env.bcf_proofs).is_ok() {
            let _ = std::fs::rename(&tmp, &flush_path);
        }
    }
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

    // EXPERIMENT both-folds (ZOVIA_BCF_BOTH_FOLDS=1, all-faithful mirror
    // 2026-06-11): when FAITHFUL_FOLD is on, ALSO emit the legacy-fold form of
    // the same obligation. The kernel folds per-site based on ITS state; one
    // of the two forms hash-matches (from_nat 5edc48ab = legacy n=5 form;
    // faithful emits the n=4 fold). ADDITIVE + deduped.
    if crate::common::config::bcf_mirror_knob("ZOVIA_BCF_BOTH_FOLDS", true) {
        if let Some(ok_lf) = crate::refinement::refine_unreachable::try_prove_unreachable_fold_legacy(
            state, base_pc, prev_insn_pc,
        ) {
            let entry_lf = RefineEntry::new(
                ok_lf.goal_root, ok_lf.sym.exprs, ok_lf.proof_bytes,
                BCF_BUNDLE_KIND_UNREACHABLE,
            );
            if !env.bcf_proofs.iter().any(|e| e.cond_hash == entry_lf.cond_hash) {
                info!(
                    target: "app",
                    "[bcf] path-unreachable (legacy-fold): cvc5 proof {} bytes (hash {:016x})",
                    entry_lf.proof_bytes.len(), entry_lf.cond_hash
                );
                env.bcf_proofs.push(entry_lf);
            }
        }
    }

    // EXPERIMENT trajectory-suffix twins of the NATURAL discharge (additive,
    // gated by BOTH_FOLDS like the legacy twin): the natural base may not be
    // a path-cond pc, so the anchor-union below never re-anchors exactly
    // there — emit the traj-window forms at (base_pc, prev_insn_pc) too.
    if crate::common::config::bcf_mirror_knob("ZOVIA_BCF_BOTH_FOLDS", true) && base_pc.is_some() {
        for okv in [
            crate::refinement::refine_unreachable::try_prove_unreachable_traj(
                state, base_pc, prev_insn_pc,
            ),
            crate::refinement::refine_unreachable::try_prove_unreachable_traj_fold_legacy(
                state, base_pc, prev_insn_pc,
            ),
            crate::refinement::refine_unreachable::try_prove_unreachable_traj_no_rewrite(
                state, base_pc, prev_insn_pc,
            ),
        ] {
            if let Some(ok_t) = okv {
                let entry_t = RefineEntry::new(
                    ok_t.goal_root, ok_t.sym.exprs, ok_t.proof_bytes,
                    BCF_BUNDLE_KIND_UNREACHABLE,
                );
                if !env.bcf_proofs.iter().any(|e| e.cond_hash == entry_t.cond_hash) {
                    info!(
                        target: "app",
                        "[bcf] path-unreachable (traj-natural): cvc5 proof {} bytes (hash {:016x})",
                        entry_t.proof_bytes.len(), entry_t.cond_hash
                    );
                    env.bcf_proofs.push(entry_t);
                }
            }
        }
    }

    // anchor-union (2026-06-11 → RETIRED 2026-06-30, now DEFAULT-OFF;
    // kill-switch ZOVIA_BCF_ANCHOR_UNION=1 to restore for A/B).
    // This was a guess-sweep that re-emitted the obligation at every later
    // path-cond pc × 18 fold/prev variants because zovia's base was WRONG:
    // it returned a cache first_insn (146) where the kernel anchors at
    // `base->insn_idx` (190/207). The INSNIDX base (default-ON above) now
    // computes that faithfully, so the ONE natural obligation matches the
    // kernel — the sweep is redundant over-emission (18×|anchors| per reject
    // = the dominant bundle bloat / E2BIG driver + the debug-program non-
    // termination). Box-verified vs #15 base_insn probe; from_nat_fib pc748
    // 28/28 + pc274 24/24 with it OFF. See project_from_nat_fib_pc521_*.md.
    if crate::common::config::bcf_mirror_knob("ZOVIA_BCF_ANCHOR_UNION", false) {
        if let Some(bcfst) = state.bcf.as_ref() {
            // Candidates = EVERY distinct path-cond pc later than the current
            // base (not just narrowed-const branches): the kernel's bcf_track
            // base can sit at any checkpoint, including jump-edge targets
            // whose surrounding cond stretch (e.g. from_hep 2586-2597 port
            // bounds) is exactly what narrower anchor sets exclude.
            //
            // PLUS a bounded LOOKBACK of path-cond pcs at/below the natural
            // base: the kernel's checkpoint can also sit EARLIER than zovia's
            // cached base (to_wep reject 1783: zovia base=1633, kernel
            // base=1599 → window [1602..] = the c70002dc/588b0338/5bc713f6/
            // 86ac8cbf quartet, 2 path-cond pcs before zovia's base). Earlier
            // anchors give superset windows — still cvc5-proven, additive.
            let mut all_pcs: Vec<usize> = bcfst.path_cond_pcs.clone();
            all_pcs.sort_unstable();
            all_pcs.dedup();
            let lookback: usize = std::env::var("ZOVIA_BCF_ANCHOR_LOOKBACK")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(8);
            let anchors: Vec<usize> = match base_pc {
                None => all_pcs,
                Some(bp) => {
                    let idx = all_pcs.partition_point(|&q| q <= bp);
                    all_pcs[idx.saturating_sub(lookback)..].to_vec()
                }
            };
            for p in anchors {
                // prev for a re-anchored replay = the last path-cond pc below
                // the anchor (the actual preceding cond on the path — mirrors
                // record_path_cond at bcf_track replay start; for a jump-edge
                // anchor this is the jump source, e.g. 2586's prev = 1484).
                let prev_for_p = bcfst
                    .path_cond_pcs
                    .iter()
                    .filter(|&&q| q < p)
                    .copied()
                    .max();
                // mode: 0 = current fold (faithful when env set), 1 = legacy
                // fold, 2 = NO-REWRITE (aliased-VAR form — the Class-A loop
                // emits rw=false per anchor and the kernel queries it, e.g.
                // 673434f3 on the to_hep/to_lo co-re_v6 pair).
                // prev=p-1 mirrors the kernel's vstate->last_insn_idx: the
                // replay-start prev is the INSN preceding the base, which need
                // not be a recorded cond pc (prev-push then SYNTHESIZES that
                // branch's cond — e.g. the (0x0 != 0x2)-prefixed forms).
                let prev_insn = p.checked_sub(1);
                for (mode, prev_v) in [
                    (0, prev_for_p),
                    (1, prev_for_p),
                    (2, prev_for_p),
                    (0, prev_insn),
                    (1, prev_insn),
                    (2, prev_insn),
                    // prev=None variants: some kernel bases push NO prev
                    // branch cond at replay start.
                    (0, None),
                    (1, None),
                    (2, None),
                    // TRAJECTORY-suffix window modes (3 = env fold, 4 =
                    // legacy fold, 5 = no-rewrite): kernel replay is a
                    // linear trajectory suffix; when the path crossed
                    // higher-pc code before the base the numeric window
                    // keeps carried conds the kernel never replays
                    // (from_l3_co-re_v6 fe23e625).
                    (3, prev_for_p),
                    (4, prev_for_p),
                    (5, prev_for_p),
                    (3, prev_insn),
                    (4, prev_insn),
                    (5, prev_insn),
                    (3, None),
                    (4, None),
                    (5, None),
                ] {
                    if prev_v.is_none() && prev_for_p.is_none() && mode != 0 {
                        continue; // avoid exact duplicates of the Some-prev rows
                    }
                    if prev_v == prev_insn && prev_insn == prev_for_p && mode != 0 {
                        continue; // p-1 row duplicates the computed-prev row
                    }
                    let okv = match mode {
                        1 => crate::refinement::refine_unreachable::try_prove_unreachable_fold_legacy(
                            state, Some(p), prev_v,
                        ),
                        2 => crate::refinement::refine_unreachable::try_prove_unreachable_no_rewrite(
                            state, Some(p), prev_v,
                        ),
                        3 => crate::refinement::refine_unreachable::try_prove_unreachable_traj(
                            state, Some(p), prev_v,
                        ),
                        4 => crate::refinement::refine_unreachable::try_prove_unreachable_traj_fold_legacy(
                            state, Some(p), prev_v,
                        ),
                        5 => crate::refinement::refine_unreachable::try_prove_unreachable_traj_no_rewrite(
                            state, Some(p), prev_v,
                        ),
                        _ => try_prove_unreachable(state, Some(p), prev_v),
                    };
                    if let Some(ok_au) = okv {
                        let entry_au = RefineEntry::new(
                            ok_au.goal_root, ok_au.sym.exprs, ok_au.proof_bytes,
                            BCF_BUNDLE_KIND_UNREACHABLE,
                        );
                        if !env.bcf_proofs.iter().any(|e| e.cond_hash == entry_au.cond_hash) {
                            info!(
                                target: "app",
                                "[bcf] path-unreachable (anchor-union@{} mode={}): cvc5 proof {} bytes (hash {:016x})",
                                p, mode, entry_au.proof_bytes.len(), entry_au.cond_hash
                            );
                            env.bcf_proofs.push(entry_au);
                        }
                    }
                }
            }
        }
    }

    // Loop-suffix-base discharge (additive). When the reject's recorded path
    // crossed an unrolled bounded loop, re-anchor the goal at the loop exit
    // (the kernel's bcf_track base) so only the exit branch + post-loop suffix
    // survive — produces the kernel's post-loop obligation (accepted_entrypoint
    // 0x11cc) that the pre-loop-anchored discharges above miss. ADDITIVE +
    // deduped: returns None when the path crossed no loop, so it never drops
    // another reject's obligation.
    if loop_suffix_on {
        if let Some(ok_ls) = crate::refinement::refine_unreachable::try_prove_unreachable_loop_suffix(
            state, base_pc, prev_insn_pc,
        ) {
            let entry_ls = RefineEntry::new(
                ok_ls.goal_root, ok_ls.sym.exprs, ok_ls.proof_bytes,
                BCF_BUNDLE_KIND_UNREACHABLE,
            );
            if !env.bcf_proofs.iter().any(|e| e.cond_hash == entry_ls.cond_hash) {
                info!(
                    target: "app",
                    "[bcf] path-unreachable (loop-suffix): cvc5 proof {} bytes (hash {:016x})",
                    entry_ls.proof_bytes.len(), entry_ls.cond_hash
                );
                env.bcf_proofs.push(entry_ls);
            }
        }
    }

    // Flag-skip-base discharge (additive). Re-anchors past the loop exit at
    // the proto-switch "flag" branch's flag-clear (`0==0`) side, dropping the
    // loop and the flag's `!=0x400` conjunct — produces the kernel's
    // flag-bypass obligations (accepted_entrypoint 0x2f5796f3… family) that
    // the loop-suffix + pre-loop discharges miss. ADDITIVE + deduped: returns
    // None when the path crossed no loop / has no post-loop foldable branch.
    if flag_skip_on {
        for ok_fs in crate::refinement::refine_unreachable::try_prove_unreachable_flag_skip_multi(
            state, base_pc, prev_insn_pc,
        ) {
            let entry_fs = RefineEntry::new(
                ok_fs.goal_root, ok_fs.sym.exprs, ok_fs.proof_bytes,
                BCF_BUNDLE_KIND_UNREACHABLE,
            );
            if !env.bcf_proofs.iter().any(|e| e.cond_hash == entry_fs.cond_hash) {
                info!(
                    target: "app",
                    "[bcf] path-unreachable (flag-skip): cvc5 proof {} bytes (hash {:016x})",
                    entry_fs.proof_bytes.len(), entry_fs.cond_hash
                );
                env.bcf_proofs.push(entry_fs);
            }
        }
    }

    // Loop-entry-base discharge (additive). Re-anchors at a loop-header bound
    // check on the zero-iteration route, reproducing the kernel's `u>=`-anchored
    // proto-switch obligations (the second engine-shape family) that flag-skip
    // (== anchors) and the loop-suffix/pre-loop discharges miss. ADDITIVE +
    // deduped.
    if loop_entry_on && !env.loop_exit_branch_pcs.is_empty() {
        let headers = env.loop_exit_branch_pcs.clone();
        for ok_le in crate::refinement::refine_unreachable::try_prove_unreachable_loop_entry_multi(
            state, base_pc, prev_insn_pc, &headers,
        ) {
            let entry_le = RefineEntry::new(
                ok_le.goal_root, ok_le.sym.exprs, ok_le.proof_bytes,
                BCF_BUNDLE_KIND_UNREACHABLE,
            );
            if !env.bcf_proofs.iter().any(|e| e.cond_hash == entry_le.cond_hash) {
                info!(
                    target: "app",
                    "[bcf] path-unreachable (loop-entry): cvc5 proof {} bytes (hash {:016x})",
                    entry_le.proof_bytes.len(), entry_le.cond_hash
                );
                env.bcf_proofs.push(entry_le);
            }
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
    if crate::common::config::bcf_mirror_knob("ZOVIA_BCF_THOROUGH_PASS", true)
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
            // Faithful base→reject replay re-anchored at THIS ancestor
            // (ZOVIA_BCF_REPLAY=1). Re-executes from the ancestor's cached
            // state, so the goal is the kernel's exact bcf_track path cond
            // for a replay starting here. Additive + deduped by cond_hash.
            if crate::common::config::bcf_mirror_knob("ZOVIA_BCF_REPLAY", true) {
                for rok in try_prove_unreachable_via_replay(env, state, parent_cid) {
                    let rentry = RefineEntry::new(
                        rok.goal_root, rok.sym.exprs, rok.proof_bytes,
                        BCF_BUNDLE_KIND_UNREACHABLE,
                    );
                    if std::env::var("ZOVIA_BCF_REPLAY_DEBUG").ok().as_deref() == Some("1") {
                        eprintln!("[replay] ANCESTOR depth={} anchor_cid={} hash={:016x}",
                            depth, parent_cid, rentry.cond_hash);
                    }
                    if !env.bcf_proofs.iter().any(|e| e.cond_hash == rentry.cond_hash) {
                        env.bcf_proofs.push(rentry);
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
    let mark_if_new = std::env::var("ZOVIA_EXP_MARK_IF_NEW").ok().as_deref() == Some("1");
    if !mark_if_new || primary_was_new {
        // Deeper bcidx base (NOT the INSNIDX goal anchor): the marking must
        // reach pc521 for d53. See the split at the top of this fn.
        crate::analysis::flow::pruning::cache::mark_path_children_unsafe(env, state, base_cid_dbg);
    }
    true
}
