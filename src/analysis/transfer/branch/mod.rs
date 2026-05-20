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

/// Append the taken/not-taken predicates to each side's `path_conds`.
/// Skips the hook entirely when symbolic tracking is off or when either
/// side can't be materialized as a tracked register (anchor regs, etc.).
///
/// `src_pc` is the PC of the JMP insn — used to tag each emitted
/// path_cond (and any bound preds emitted by `reg_expr`'s lazy
/// materialization). The refine-time filter
/// (`SymbolicState::filter_path_conds_from_pc`) keeps path_conds with
/// `pc >= base_pc` (the kernel's bcf_track suffix-only emission rule).
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

    // Now mirror the **whole post-hook DAG** into state_else's bcf. The
    // pre-hook DAGs were identical (state_else.bcf was cloned from state
    // before the hook), so a wholesale replace keeps both sides
    // consistent. Then append only the not-taken pred to state_else's
    // path_conds (state_then gets the taken pred).
    let snapshot = (**then_bcf).clone();
    then_bcf.add_cond_at(pred_then, src_pc);
    if let Some(else_bcf) = state_else.bcf.as_mut() {
        **else_bcf = snapshot;
        else_bcf.add_cond_at(pred_else, src_pc);
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

    // --- BCF symbolic mirror: append the branch predicate to each side's
    // path_conds (taken op on `state_then`, reversed op on `state_else`).
    // Mirrors BCF's `record_path_cond` (kernel patches set1, cheat-sheet §2).
    // Test (JSET) is skipped for Phase 1; ALU/JMP comparisons cover
    // shift_constraint's `if r1 > 4` (UGt) path-cond requirement. ---
    record_branch_path_conds(&mut state_then, &mut state_else, width, left, op, &right, state.pc);

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

    // a back-edge compare-to-imm is a precision sink for
    // the compared register. The kernel's `mark_chain_precision` walks
    // backward from such sinks; without it, the loop counter widens at
    // intermediate may_goto sites, the bounds derived from this compare
    // don't propagate to downstream pointer arithmetic, and accumulator-
    // style loops (test1: `*R2=R1; R2+=8; R1++`) run away in abstract
    // interp because R1 widens before the next iteration's compare.
    //
    // Gate on **back-edge** (target < state.pc) to differentiate the
    // loop-back-to-head pattern from forward-exit conditionals. A
    // forward `if r < N goto exit` doesn't need the precision (the
    // loop head's re-refinement on entry handles each iteration), and
    // marking precise there blocks widening at the may_goto inside the
    // body (cond_break1's pattern). A backward `if r != K goto head`
    // (test1) does need it.
    // Precision sink at conditional branches. Kernel
    // `check_cond_jmp_op` calls `mark_chain_precision` only after
    // `is_branch_taken` decides the branch (one side is dead). Marking
    // precise on every conditional causes precision-mark blow-up that
    // `propagate_precision` then spreads further (bits_iter
    // state-explosion).
    if let Some(hidx) = state.history_idx {
        let static_resolves = condition_outcome(&state, width, left, op, &right).is_some();
        // Back-edge compare-to-imm catches tight scalar loops where the
        // exit predicate is `if r & C goto head` — the conditional
        // doesn't statically resolve (r is imprecise), but without
        // marking r precise the back-jump's precision contract isn't
        // tracked and convergence happily prunes the loop after one
        // iteration even when the kernel rejects via complexity limit
        // (verifier_search_pruning.c::short_loop1). Suppress this
        // sink when an iter slot is active on the stack — iter loops
        // get their convergence proof from iter-id mechanics, and
        // marking the conditional reg precise causes precision blow-up
        // on bits_iter / iter_nested_deeply_iters.
        let back_edge_imm = matches!(right, Operand::Imm(_)) && target < state.pc;
        // Previously gated on `!in_iter_loop` to dodge precision-mark
        // blow-up on bits_iter / iter_nested_deeply_iters. With SCC
        // bookkeeping (`State.branches/dfs_depth/loop_entry_cache_id`)
        // and `force_exact` subsumption gating, iter-loop convergence
        // now uses RANGE_WITHIN strictness while open — kernel-faithful,
        // and the precision marks INSIDE iter loops are needed for the
        // RANGE_WITHIN check to distinguish iterations (loop_state_deps1/2).
        let fire = static_resolves || back_edge_imm;
        if fire {
            let pcid = state.parent_cache_id;
            env.mark_chain_precision_backward(hidx, pcid, left);
            if let Operand::Reg(r) = right {
                env.mark_chain_precision_backward(hidx, pcid, r);
            }
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
    if !state_else.domain.is_inconsistent() {
        out.push(state_else);
    }
    if !state_then.domain.is_inconsistent() {
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
    if std::env::var("ZOVIA_DUMP_DISCHARGE").ok().as_deref() == Some("1") {
        eprintln!("[disc] reject@pc={} base_pc={:?}", state.pc, base_pc);
    }
    let Some(ok) = try_prove_unreachable(state, base_pc) else {
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
