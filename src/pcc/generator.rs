use std::collections::BTreeMap;

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, Instr, MemSize, Operand, Program};
use crate::common::constants;
use crate::domains::dbm::{Dbm, INF};
use crate::domains::numeric::NumericDomain;
use crate::parsing::elf::BpfMapDef;
use log::debug;

use super::checker::{derive_guard_constraint_from_branch, distance_upper_bound};
use super::model::{AnnotationEntry, PcAnnotation, ProgramCertificate, ProofStep};
use super::program_hash;

// ---------------------------------------------------------------------------
// Bound-query helpers (Step 5)
// ---------------------------------------------------------------------------

/// For a Load instruction, returns (base_reg, offset, size_bytes).
/// The required bound is computed by the caller via `access_anchor_and_bound`.
fn load_info(instr: &Instr) -> Option<(Reg, i16, MemSize)> {
    let Instr::Load {
        size, base, off, ..
    } = instr
    else {
        return None;
    };
    Some((*base, *off, *size))
}

/// Determine the anchor register and required bound for a load instruction
/// based on the base register's pointer type.
///
/// Returns `(anchor_end, required_bound)` where the access is safe iff
/// `base - anchor_end <= required_bound`.
///
/// - Packet: `base - @data_end <= -(off + size)` ⟹ `base + off + size <= @data_end`
/// - Stack:  `base - R10 <= -(off + size)`       ⟹ `base + off + size <= R10 = 0`
/// - Map:    `base - Zero <= limit - off - size`  ⟹ `base + off + size <= limit`
fn access_anchor_and_bound(
    state: &State,
    base: Reg,
    off: i64,
    size: i64,
    map_defs: &[BpfMapDef],
) -> Option<(Reg, i64)> {
    match state.types.get(base) {
        RegType::PtrToPacket => Some((Reg::AnchorDataEnd, -(off + size))),
        RegType::PtrToStack { .. } => Some((Reg::R10, -(off + size))),
        RegType::PtrToMapValue { map_idx, .. } => {
            let limit = map_defs.get(map_idx)?.value_size as i64;
            Some((Reg::Zero, limit - off - size))
        }
        _ => None,
    }
}

/// Check whether the interval domain already proves the access is safe
/// (i.e. PCC is not needed for this load).
fn interval_already_proves_access(
    state: &State,
    base: Reg,
    off: i64,
    size: i64,
    map_defs: &[BpfMapDef],
) -> bool {
    match state.types.get(base) {
        RegType::PtrToPacket => {
            let (s, e) = state.domain.verify_packet_bounds(base, off, size);
            s && e
        }
        RegType::PtrToStack { .. } => {
            let (lo, hi) = state.domain.get_distance_interval(base, Reg::R10);
            lo != i64::MIN
                && hi != i64::MAX
                && lo + off >= constants::BPF_STACK_MIN
                && hi + off + size <= constants::BPF_STACK_MAX
        }
        RegType::PtrToMapValue { map_idx, .. } => {
            if let NumericDomain::Interval(ref ivl) = state.domain {
                if let Some(po) = ivl.get_ptr_offset(base) {
                    let min = po.min_offset() + off;
                    let max = po.max_offset() + off + size;
                    let limit = map_defs
                        .get(map_idx)
                        .map(|d| d.value_size as i64)
                        .unwrap_or(0);
                    return min >= 0 && max <= limit;
                }
            }
            false
        }
        _ => false,
    }
}

/// Zone upper bound for `i - j` from a DBM. Returns None if unbounded.
fn zone_upper_bound(dbm: &Dbm, i: Reg, j: Reg) -> Option<i64> {
    let v = dbm.get(i, j);
    if v >= INF { None } else { Some(v) }
}

/// Interval upper bound for `i - j` from an interval State.
/// Wraps the checker's distance_upper_bound; returns None if unbounded.
fn interval_upper_bound(state: &State, i: Reg, j: Reg) -> Option<i64> {
    let ub = distance_upper_bound(state, i, j)?;
    if ub == i64::MAX { None } else { Some(ub) }
}

// ---------------------------------------------------------------------------
// Same-map anchor search (Step 5b)
// ---------------------------------------------------------------------------

/// For a map-value base register, find another register `k` from the same map
/// such that `zone_upper_bound(dbm, base, k) + k.type_offset <= required`.
///
/// This enables PCC for variable map accesses: zone tracks `base - k` relationally
/// (e.g., from a branch comparing two same-map pointers), and `k.type_offset` is
/// the constant buffer offset from the interval state's type info.
///
/// Returns `(k, zone_ub(base, k))` on success.
fn find_same_map_anchor(
    state: &State,
    dbm: &Dbm,
    base: Reg,
    base_map_idx: usize,
    required: i64,
) -> Option<(Reg, i64)> {
    for k in Reg::ALL {
        if k == base || k == Reg::Zero {
            continue;
        }
        // k must be PtrToMapValue from the same map with a known constant offset.
        if let RegType::PtrToMapValue {
            map_idx,
            offset: Some(k_off),
            ..
        } = state.types.get(k)
        {
            if map_idx != base_map_idx {
                continue;
            }
            // Check: zone_ub(base, k) + k_off <= required
            if let Some(ub) = zone_upper_bound(dbm, base, k) {
                if let Some(composed) = ub.checked_add(k_off) {
                    if composed <= required {
                        return Some((k, ub));
                    }
                }
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Backward tracing (Step 6)
// ---------------------------------------------------------------------------

/// A backward-traced step before it is reversed into the forward chain.
///
/// During backward tracing the generator walks from the target load toward the divergence
/// point, calling [`backward_transfer`] at each instruction to invert the instruction's
/// semantics: given the post-state constraint, what must the pre-state constraint be?
///
/// Each `BackwardStep` stores the forward-Transfer data (i.e. the same `delta` and
/// register mapping that would appear in a [`ProofStep::Transfer`]) even though it was
/// discovered by walking backward. When the divergence point is found, the accumulated
/// `BackwardStep`s are reversed into [`ProofStep::Transfer`] entries in forward order.
///
/// Field names follow the forward Transfer convention:
/// `pre_left_reg/pre_right_reg` is the constraint pair **before** the instruction,
/// `post_left_reg/post_right_reg` is the pair **after** it, and `delta` is the
/// forward bound shift (`post_bound = pre_bound + delta`).
struct BackwardStep {
    pc: usize,
    pre_left_reg: usize,
    pre_right_reg: usize,
    post_left_reg: usize,
    post_right_reg: usize,
    delta: i64,
    /// Human-readable description of why `delta` is what it is (see `backward_transfer`).
    hint: Option<String>,
}

/// Trace backward from `target_pc` to find the divergence point where the
/// interval state agrees with the zone on the tracked constraint.
///
/// Returns `Some((guard_pc, guard_i, guard_j, guard_c, steps))` on success,
/// where `steps` is in **forward** order (ready for the certificate).
/// Returns `None` if tracing fails (unsupported instruction, etc.).
fn backward_trace(
    prog: &Program,
    zone_dbms: &[Dbm],
    interval_states: &[State],
    target_pc: usize,
    target_i: Reg,
    target_j: Reg,
    target_bound: i64,
) -> Option<(usize, usize, usize, i64, Vec<ProofStep>)> {
    let mut cur_i = target_i;
    let mut cur_j = target_j;
    let mut cur_bound = target_bound;
    let mut backward_steps: Vec<BackwardStep> = Vec::new();

    // Walk backward from target_pc - 1 (the instruction before the load).
    let mut pc = target_pc.checked_sub(1)?;

    loop {
        // First, compute the backward transfer through the instruction at this PC.
        // This tells us what the constraint looks like BEFORE this instruction.
        let instr = &prog.instrs[pc];
        let (prev_i, prev_j, delta, hint) =
            backward_transfer(instr, cur_i, cur_j, zone_dbms, pc)?;
        let pre_bound = cur_bound.checked_sub(delta)?;

        // Record this as a backward step (instruction transforms constraint).
        backward_steps.push(BackwardStep {
            pc,
            pre_left_reg: prev_i.idx(),
            pre_right_reg: prev_j.idx(),
            post_left_reg: cur_i.idx(),
            post_right_reg: cur_j.idx(),
            delta,
            hint,
        });

        // Now check: does the interval agree on the PRE-instruction constraint?
        // Two paths: (1) state-derived, (2) branch-derived.
        if pc < interval_states.len() {
            // Path 1: State-derived — interval state directly proves the constraint.
            let mut guard_found = false;
            let mut guard_c = 0i64;

            if let Some(ivl_ub) = interval_upper_bound(&interval_states[pc], prev_i, prev_j) {
                if ivl_ub <= pre_bound {
                    guard_found = true;
                    guard_c = ivl_ub;
                }
            }

            // Path 2: Branch-derived — if the instruction at this PC is a branch
            // whose fall-through condition matches the tracked constraint pair,
            // derive the guard from the branch semantics. This handles the case
            // where a branch refines a variable AFTER a variable add (e.g., stack
            // variable-offset access where zone's closure captures the refinement
            // but the interval's var_off is not retroactively tightened).
            if !guard_found {
                if let Some(branch_guard) =
                    derive_guard_constraint_from_branch(instr, pc, pc + 1)
                {
                    if branch_guard.left_reg == prev_i.idx()
                        && branch_guard.right_reg == prev_j.idx()
                        && branch_guard.c <= pre_bound
                    {
                        guard_found = true;
                        guard_c = branch_guard.c;
                    }
                }
            }

            if guard_found {
                let mut proof = Vec::with_capacity(1 + backward_steps.len());
                proof.push(ProofStep::Guard {
                    pc,
                    left_reg: prev_i.idx(),
                    right_reg: prev_j.idx(),
                    c: guard_c,
                });

                // Reverse backward steps into forward order as Transfer steps
                for bs in backward_steps.into_iter().rev() {
                    proof.push(ProofStep::Transfer {
                        pc: bs.pc,
                        pre_left_reg: bs.pre_left_reg,
                        pre_right_reg: bs.pre_right_reg,
                        post_left_reg: bs.post_left_reg,
                        post_right_reg: bs.post_right_reg,
                        delta: bs.delta,
                        hint: bs.hint,
                    });
                }

                return Some((pc, prev_i.idx(), prev_j.idx(), guard_c, proof));
            }
        }

        // If we've reached pc 0 without finding the divergence, give up.
        if pc == 0 {
            debug!(
                target: "pcc-gen",
                "[PCC-GEN] target={}: backward trace reached pc=0 without finding divergence",
                target_pc,
            );
            return None;
        }

        cur_i = prev_i;
        cur_j = prev_j;
        cur_bound = pre_bound;
        pc -= 1;
    }
}

/// Compute the backward transfer through a single instruction.
///
/// Given that after the instruction at `pc`, the constraint `cur_i - cur_j <= cur_bound`
/// holds (the post-state), returns `(prev_i, prev_j, delta)` such that the pre-state
/// constraint `prev_i - prev_j <= cur_bound - delta` is a valid backward implication.
///
/// Equivalently, `delta` is the *forward* bound shift: when `prev_i - prev_j <= pre_bound`
/// holds before the instruction, then `cur_i - cur_j <= pre_bound + delta` holds after it.
/// The caller computes `pre_bound = cur_bound - delta`.
///
/// The derivations for each supported case (let `L = cur_i`, `R = cur_j`):
///
/// - **`mov dst, src`** (`cur_i == dst`):
///   Post: `dst - R <= b`. Since `dst_post == src_pre`, pre: `src - R <= b`. `delta = 0`.
///
/// - **`add dst, imm`** (`cur_i == dst`):
///   Post: `(dst_old+imm) - R <= b`  ⟺  `dst_old - R <= b - imm`. `delta = imm`.
///
/// - **`add dst, imm`** (`cur_j == dst`):
///   Post: `L - (dst_old+imm) <= b`  ⟺  `L - dst_old <= b + imm`. `delta = -imm`.
///
/// - **`add dst, src_reg`** (`cur_i == dst`):
///   Post: `(dst_old+src) - R <= b`  ⟺  `dst_old - R <= b - src`.
///   The tightest conservative pre-bound uses `src <= ub(src)` (worst case: src is largest):
///   `dst_old - R <= b - ub(src)`. `delta = ub(src)` from the zone DBM at `pc`.
///
/// - **`add dst, src_reg`** (`cur_j == dst`):
///   Post: `L - (dst_old+src) <= b`  ⟺  `L - dst_old <= b + src`.
///   The tightest conservative pre-bound uses `src >= lb(src)` (worst case: src is smallest):
///   `L - dst_old <= b + lb(src)`. `delta = -lb(src)` from the zone DBM at `pc`.
///
/// - **Passthrough** (`dst` ∉ {`cur_i`, `cur_j`}): constraint unchanged. `delta = 0`.
///
/// Returns `None` for unsupported instructions that write to a tracked register in a way
/// the generator cannot invert.
fn backward_transfer(
    instr: &Instr,
    cur_i: Reg,
    cur_j: Reg,
    zone_dbms: &[Dbm],
    pc: usize,
) -> Option<(Reg, Reg, i64, Option<String>)> {
    match instr {
        // mov dst, src  →  dst_post = src_pre.
        // If cur_i == dst, the value now in dst came from src before the move.
        // Pre-constraint: src - cur_j <= b (same bound, delta = 0).
        // Symmetric for cur_j.
        Instr::Alu {
            op: AluOp::Mov,
            dst,
            src: Operand::Reg(src),
            ..
        } => {
            let prev_i = if cur_i == *dst { *src } else { cur_i };
            let prev_j = if cur_j == *dst { *src } else { cur_j };
            // Build a hint only when a register rename actually happens.
            let hint = if cur_i == *dst && cur_j != *dst {
                Some(format!(
                    "{} = {}  [{} renamed to {}; tracking {} now]",
                    dst.name(),
                    src.name(),
                    src.name(),
                    dst.name(),
                    dst.name(),
                ))
            } else if cur_j == *dst && cur_i != *dst {
                Some(format!(
                    "{} = {}  [{} renamed to {}; tracking {} now]",
                    dst.name(),
                    src.name(),
                    src.name(),
                    dst.name(),
                    dst.name(),
                ))
            } else {
                None // passthrough (dst ∉ {cur_i, cur_j})
            };
            Some((prev_i, prev_j, 0, hint))
        }

        // add dst, imm  →  dst_post = dst_pre + imm.
        // cur_i == dst: (dst_pre+imm) - cur_j <= b  ⟺  dst_pre - cur_j <= b - imm.
        //   delta = imm (pre_bound = cur_bound - imm).
        // cur_j == dst: cur_i - (dst_pre+imm) <= b  ⟺  cur_i - dst_pre <= b + imm.
        //   delta = -imm (pre_bound = cur_bound + imm).
        Instr::Alu {
            op: AluOp::Add,
            dst,
            src: Operand::Imm(imm),
            ..
        } => {
            if *dst == cur_i {
                // Left side shifts: L += imm  →  L-R bound increases by imm.
                let hint = if *imm >= 0 {
                    Some(format!("{} += {}", dst.name(), imm))
                } else {
                    Some(format!("{} -= {}", dst.name(), -imm))
                };
                Some((cur_i, cur_j, *imm, hint))
            } else if *dst == cur_j {
                // Right side shifts: R += imm  →  L-R bound decreases by imm.
                let hint = if *imm >= 0 {
                    Some(format!(
                        "{} += {}  (right side grows; {}-{} tightens by {})",
                        dst.name(),
                        imm,
                        cur_i.name(),
                        cur_j.name(),
                        imm,
                    ))
                } else {
                    Some(format!(
                        "{} -= {}  (right side shrinks; {}-{} relaxes by {})",
                        dst.name(),
                        -imm,
                        cur_i.name(),
                        cur_j.name(),
                        -imm,
                    ))
                };
                Some((cur_i, cur_j, -(*imm), hint))
            } else {
                // Passthrough: dst doesn't affect the tracked pair.
                Some((cur_i, cur_j, 0, None))
            }
        }

        // add dst, src_reg  →  dst_post = dst_pre + src_reg.
        // cur_i == dst: (dst_pre+src) - cur_j <= b  ⟺  dst_pre - cur_j <= b - src.
        //   Worst case (largest src): src = ub(src).  Pre-bound = b - ub(src). delta = ub(src).
        // cur_j == dst: cur_i - (dst_pre+src) <= b  ⟺  cur_i - dst_pre <= b + src.
        //   Worst case (smallest src): src = lb(src). Pre-bound = b + lb(src). delta = -lb(src).
        //   lb(src) = -ub(Zero - src) = -zone_upper_bound(dbm, Zero, src).
        Instr::Alu {
            op: AluOp::Add,
            dst,
            src: Operand::Reg(src),
            ..
        } => {
            if *dst == cur_i {
                let dbm = zone_dbms.get(pc)?;
                let src_ub = zone_upper_bound(dbm, *src, Reg::Zero)?;
                // Left side increases by at most src_ub.
                let hint = Some(format!(
                    "{} += {}  ({} <= {}, worst case)",
                    dst.name(),
                    src.name(),
                    src.name(),
                    src_ub,
                ));
                Some((cur_i, cur_j, src_ub, hint))
            } else if *dst == cur_j {
                let dbm = zone_dbms.get(pc)?;
                let src_lb = {
                    // lb(src) = -ub(Zero - src)
                    let neg_lb = zone_upper_bound(dbm, Reg::Zero, *src)?;
                    -neg_lb
                };
                // Right side increases by at least src_lb.
                let hint = Some(format!(
                    "{} += {}  ({} >= {}, worst case)",
                    dst.name(),
                    src.name(),
                    src.name(),
                    src_lb,
                ));
                Some((cur_i, cur_j, -src_lb, hint))
            } else {
                Some((cur_i, cur_j, 0, None))
            }
        }

        // Any other instruction: check if it writes to a tracked register.
        _ => {
            let writes_to = |r: Reg| -> bool {
                match instr {
                    Instr::Alu { dst, .. }
                    | Instr::Endian { dst, .. }
                    | Instr::Load { dst, .. }
                    | Instr::LoadMap { dst, .. } => *dst == r,
                    Instr::Call { .. } | Instr::LoadPacket { .. } => r == Reg::R0,
                    _ => false,
                }
            };
            if writes_to(cur_i) || writes_to(cur_j) {
                // Unsupported: instruction modifies tracked register
                None
            } else {
                // Passthrough: instruction does not touch cur_i or cur_j.
                Some((cur_i, cur_j, 0, None))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Certificate generation entry point
// ---------------------------------------------------------------------------

/// Generate a certificate using backward tracing from zone analysis.
///
/// For each candidate load instruction, traces backward to the divergence
/// point where zone and interval first disagree, emitting a proof chain
/// of [Guard, Transfer, ..., Transfer].
pub fn generate_certificate(
    prog: &Program,
    zone_dbms: &[Dbm],
    interval_states: &[State],
    map_defs: &[BpfMapDef],
) -> ProgramCertificate {
    let mut cert = ProgramCertificate::empty(program_hash(prog));
    if prog.instrs.is_empty() {
        return cert;
    }

    let mut by_pc: BTreeMap<usize, Vec<AnnotationEntry>> = BTreeMap::new();

    for target_pc in 0..prog.instrs.len() {
        let instr = &prog.instrs[target_pc];
        let Some((base, off, size)) = load_info(instr) else {
            continue;
        };

        let off_i64 = off as i64;
        let size_i64 = size.bytes() as i64;

        // Determine anchor and required bound from the base register's pointer type.
        // Use the interval state's type info (available at the load PC).
        let state = if target_pc < interval_states.len() {
            &interval_states[target_pc]
        } else {
            continue;
        };
        let Some((anchor_end, required)) =
            access_anchor_and_bound(state, base, off_i64, size_i64, map_defs)
        else {
            continue;
        };

        // Query zone: does the zone prove the access is safe?
        // Use the DBM at the target PC (the pre-state just before the load executes).
        let Some(dbm) = zone_dbms.get(target_pc) else {
            continue;
        };

        // Try direct anchor first (works for packet/stack where zone tracks base-anchor).
        // For maps, zone doesn't track base-Zero as a buffer offset, so the direct path
        // typically returns Some but too large (255 from AND mask, not buffer-relative).
        // Fall through to the transitive path: find a same-map register k where zone
        // tracks base-k and k has a known type-level offset from the map buffer start.
        let direct_ok = zone_upper_bound(dbm, base, anchor_end)
            .filter(|&ub| ub <= required);
        let (effective_anchor, zone_ub) = if let Some(ub) = direct_ok {
            (anchor_end, ub)
        } else if let RegType::PtrToMapValue { map_idx, .. } = state.types.get(base) {
            // Transitive: scan for a same-map register k with finite zone_ub(base, k)
            // such that zone_ub(base, k) + k.type_offset <= required.
            match find_same_map_anchor(state, dbm, base, map_idx, required) {
                Some(pair) => pair,
                None => continue,
            }
        } else if zone_upper_bound(dbm, base, anchor_end).is_some() {
            continue; // zone has a bound but it's not tight enough
        } else {
            continue; // zone doesn't track this pair
        };

        // Query interval: does the interval verifier already prove it?
        if interval_already_proves_access(state, base, off_i64, size_i64, map_defs) {
            continue; // interval already sufficient, no PCC needed
        }

        debug!(
            target: "pcc-gen",
            "[PCC-GEN] target={}: candidate load {} anchor={} effective={} (zone_ub={}, required={})",
            target_pc, base.name(), anchor_end.name(), effective_anchor.name(), zone_ub, required,
        );

        // Backward trace to find the divergence point.
        // Use effective_anchor (may differ from anchor_end for maps).
        let Some((_, _, _, _, proof)) = backward_trace(
            prog,
            zone_dbms,
            interval_states,
            target_pc,
            base,
            effective_anchor,
            zone_ub,
        ) else {
            debug!(
                target: "pcc-gen",
                "[PCC-GEN] target={}: backward trace failed, skipping",
                target_pc,
            );
            continue;
        };

        // Compute the entry bound from the proof chain.
        let bound: i64 = proof.iter().map(|s| s.bound_contribution()).sum();

        by_pc.entry(target_pc).or_default().push(AnnotationEntry {
            left_reg: base.idx(),
            right_reg: effective_anchor.idx(),
            bound,
            proof,
        });
    }

    cert.pc_annotations = by_pc
        .into_iter()
        .map(|(pc, entries)| PcAnnotation { pc, entries })
        .collect();
    cert
}

/// Legacy generator (Guard-only, no Transfer steps) — kept for backward compatibility.
#[allow(dead_code)]
pub fn generate_prototype_certificate_from_zone(
    prog: &Program,
    zone_dbms: &[Dbm],
) -> ProgramCertificate {
    let mut cert = ProgramCertificate::empty(program_hash(prog));
    if prog.instrs.len() < 2 {
        return cert;
    }

    let mut by_pc: BTreeMap<usize, Vec<AnnotationEntry>> = BTreeMap::new();

    for pred_pc in 0..(prog.instrs.len() - 1) {
        let Some(Instr::Alu {
            op: AluOp::Add,
            dst,
            src: Operand::Reg(src),
            ..
        }) = prog.instrs.get(pred_pc)
        else {
            continue;
        };
        let succ_pc = pred_pc + 1;
        let Some(Instr::Load {
            size, base, off, ..
        }) = prog.instrs.get(succ_pc)
        else {
            continue;
        };
        if base != dst {
            continue;
        }
        let Some(dbm) = zone_dbms.get(pred_pc) else {
            continue;
        };

        let d_dst_data = dbm.get(*dst, Reg::AnchorData);
        let d_data_end = dbm.get(Reg::AnchorData, Reg::AnchorDataEnd);
        let src_umax = dbm.get(*src, Reg::Zero);
        if d_dst_data >= INF || d_data_end >= INF || src_umax >= INF {
            continue;
        }

        let Some(step1_c) = d_dst_data.checked_add(src_umax) else {
            continue;
        };
        let step2_c = d_data_end;
        let Some(target_c) = step1_c.checked_add(step2_c) else {
            continue;
        };

        let access_need = -((*off as i64) + size.bytes() as i64);
        if target_c > access_need {
            continue;
        }

        by_pc.entry(succ_pc).or_default().push(AnnotationEntry {
            left_reg: dst.idx(),
            right_reg: Reg::AnchorDataEnd.idx(),
            bound: target_c,
            proof: vec![ProofStep::Guard {
                pc: pred_pc,
                left_reg: dst.idx(),
                right_reg: Reg::AnchorDataEnd.idx(),
                c: target_c,
            }],
        });
    }

    cert.pc_annotations = by_pc
        .into_iter()
        .map(|(pc, entries)| PcAnnotation { pc, entries })
        .collect();
    cert
}
