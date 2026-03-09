use std::collections::HashMap;

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, CmpOp, Instr, Operand, Program, Width};
use crate::domains::numeric::NumericDomain;
use log::{debug, info};

use super::model::{AnnotationEntry, ProofStep};

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy)]
pub struct VerifiedEntry {
    pub i: usize,
    pub j: usize,
    pub bound: i64,
}

// ---------------------------------------------------------------------------
// Internal proof-check state (separate from verifier State)
// ---------------------------------------------------------------------------

/// Tracks progress through a single proof chain during replay verification.
/// This is NOT the verifier's abstract state — it is purely proof-tracking data.
struct ProofCheckState {
    current_i: usize,
    current_j: usize,
    accumulated_bound: i64,
}

// ---------------------------------------------------------------------------
// Interval-state queries (reused from v1)
// ---------------------------------------------------------------------------

fn distance_upper_bound(state: &State, i: Reg, j: Reg) -> Option<i64> {
    if !matches!(state.domain, NumericDomain::Interval(_)) {
        return Some(state.domain.get_distance_interval(i, j).1);
    }
    let direct = state.domain.get_distance_interval(i, j).1;
    if direct != i64::MAX {
        return Some(direct);
    }

    // Interval mode can still prove finite upper bounds against packet anchors
    // using packet-size lower bounds and per-register packet offsets.
    let ivl = state.domain.as_interval()?;
    if i == Reg::AnchorData && j == Reg::AnchorDataEnd {
        return ivl
            .get_packet_size_bound()
            .map(|n| -(i64::try_from(n).unwrap_or(i64::MAX)));
    }
    if j == Reg::AnchorDataEnd {
        if let Some(pkt_lb) = ivl.get_packet_size_bound()
            && let Some(po) = ivl.get_ptr_offset(i)
            && po.anchor == Reg::AnchorData
        {
            let lb = i64::try_from(pkt_lb).unwrap_or(i64::MAX);
            return Some(po.max_offset().saturating_sub(lb));
        }
    }

    Some(direct)
}

// ---------------------------------------------------------------------------
// Guard verification
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
struct Constraint {
    i: usize,
    j: usize,
    c: i64,
}

fn derive_guard_constraint_from_branch(
    pred_instr: &Instr,
    pred_pc: usize,
    succ_pc: usize,
) -> Option<Constraint> {
    let Instr::If {
        width,
        left,
        op,
        right: Operand::Reg(right),
        target,
    } = pred_instr
    else {
        return None;
    };
    if *width != Width::W64 {
        return None;
    }
    let branch_taken = if succ_pc == *target {
        true
    } else if succ_pc == pred_pc + 1 {
        false
    } else {
        return None;
    };
    let (i, j, c) = match (*op, branch_taken) {
        (CmpOp::ULe | CmpOp::SLe, true) | (CmpOp::UGt | CmpOp::SGt, false) => {
            (left.idx(), right.idx(), 0)
        }
        (CmpOp::ULt | CmpOp::SLt, true) | (CmpOp::UGe | CmpOp::SGe, false) => {
            (left.idx(), right.idx(), -1)
        }
        (CmpOp::UGe | CmpOp::SGe, true) | (CmpOp::ULt | CmpOp::SLt, false) => {
            (right.idx(), left.idx(), 0)
        }
        (CmpOp::UGt | CmpOp::SGt, true) | (CmpOp::ULe | CmpOp::SLe, false) => {
            (right.idx(), left.idx(), -1)
        }
        _ => return None,
    };
    Some(Constraint { i, j, c })
}

/// Verify a Guard step against the interval pre-state at its PC.
///
/// Two verification paths:
/// 1. Branch-derived: the instruction at guard_pc is a branch and the guard
///    matches the branch condition (for the edge leading to guard_pc + 1).
/// 2. State-derived: `distance_upper_bound(state, i, j) <= c` holds directly
///    in the interval state at guard_pc. This covers the divergence-point case
///    where zone and interval agree on the constraint.
fn verify_guard(
    guard_pc: usize,
    i_idx: usize,
    j_idx: usize,
    c: i64,
    state: &State,
    prog: &Program,
    target_pc: usize,
) -> bool {
    let Some(i) = Reg::idx_to_reg(i_idx) else {
        return false;
    };
    let Some(j) = Reg::idx_to_reg(j_idx) else {
        return false;
    };

    // Path 1: branch-derived guard.
    // Check if the instruction at guard_pc is a branch and the guard matches
    // the condition on the edge toward the target.
    let instr = &prog.instrs[guard_pc];
    if let Some(branch_guard) =
        derive_guard_constraint_from_branch(instr, guard_pc, guard_pc + 1)
    {
        if i_idx == branch_guard.i && j_idx == branch_guard.j && c == branch_guard.c {
            debug!(
                target: "pcc",
                "[PCC] target={} Guard(pc={}, {}, {}, {}): branch-derived — OK",
                target_pc, guard_pc, i.name(), j.name(), c,
            );
            return true;
        }
    }

    // Path 2: state-derived guard.
    // The interval state at guard_pc directly proves i - j <= c.
    if let Some(ub) = distance_upper_bound(state, i, j) {
        if ub <= c {
            debug!(
                target: "pcc",
                "[PCC] target={} Guard(pc={}, {}, {}, {}): state-derived (ub={}) — OK",
                target_pc, guard_pc, i.name(), j.name(), c, ub,
            );
            return true;
        }
        debug!(
            target: "pcc",
            "[PCC] target={} Guard(pc={}, {}, {}, {}): state ub={} > {} — REJECTED",
            target_pc, guard_pc, i.name(), j.name(), c, ub, c,
        );
    } else {
        debug!(
            target: "pcc",
            "[PCC] target={} Guard(pc={}, {}, {}, {}): cannot compute distance — REJECTED",
            target_pc, guard_pc, i.name(), j.name(), c,
        );
    }
    false
}

// ---------------------------------------------------------------------------
// Transfer verification
// ---------------------------------------------------------------------------

/// Verify a Transfer step against the interval pre-state and instruction at its PC.
///
/// Returns true if the claimed (from_i, from_j) -> (to_i, to_j, delta) transformation
/// is sound for the instruction at `step_pc`.
fn verify_transfer(
    step_pc: usize,
    from_i: usize,
    from_j: usize,
    to_i: usize,
    to_j: usize,
    delta: i64,
    state: &State,
    instr: &Instr,
    target_pc: usize,
) -> bool {
    let reg_name = |idx: usize| Reg::idx_to_reg(idx).map(|r| r.name()).unwrap_or("?");

    match instr {
        // mov dst, src (register)
        Instr::Alu {
            op: AluOp::Mov,
            dst,
            src: Operand::Reg(src),
            ..
        } => {
            // After mov dst, src: dst gets src's old value.
            // If from_i tracks src, then to_i should be dst (src's value is now in dst).
            // If from_j tracks src, symmetric.
            // If neither from_i nor from_j is dst, passthrough.
            let expected_to_i = if from_i == src.idx() && *dst != Reg::idx_to_reg(from_j).unwrap_or(Reg::Zero) {
                dst.idx()
            } else {
                from_i
            };
            let expected_to_j = if from_j == src.idx() && *dst != Reg::idx_to_reg(from_i).unwrap_or(Reg::Zero) {
                dst.idx()
            } else {
                from_j
            };

            // If dst overwrites a tracked register and we're not substituting, fail.
            if (*dst == Reg::idx_to_reg(from_i).unwrap_or(Reg::Zero)
                || *dst == Reg::idx_to_reg(from_j).unwrap_or(Reg::Zero))
                && to_i == from_i
                && to_j == from_j
                && from_i != src.idx()
                && from_j != src.idx()
            {
                debug!(
                    target: "pcc",
                    "[PCC] target={} Transfer(pc={}) mov {}<-{}: dst overwrites tracked reg — REJECTED",
                    target_pc, step_pc, dst.name(), src.name(),
                );
                return false;
            }

            if to_i != expected_to_i || to_j != expected_to_j || delta != 0 {
                debug!(
                    target: "pcc",
                    "[PCC] target={} Transfer(pc={}) mov: expected ({},{},0) got ({},{},{}) — REJECTED",
                    target_pc, step_pc,
                    reg_name(expected_to_i), reg_name(expected_to_j),
                    reg_name(to_i), reg_name(to_j), delta,
                );
                return false;
            }
            true
        }

        // add dst, imm
        Instr::Alu {
            op: AluOp::Add,
            dst,
            src: Operand::Imm(imm),
            ..
        } => {
            let di = dst.idx();
            if di == from_i && from_i == to_i && from_j == to_j {
                // dst is the i-side: bound shifts by +imm
                if delta != *imm {
                    debug!(
                        target: "pcc",
                        "[PCC] target={} Transfer(pc={}) add imm: delta={} != imm={} — REJECTED",
                        target_pc, step_pc, delta, imm,
                    );
                    return false;
                }
                true
            } else if di == from_j && from_i == to_i && from_j == to_j {
                // dst is the j-side: bound shifts by -imm
                if delta != -(*imm) {
                    debug!(
                        target: "pcc",
                        "[PCC] target={} Transfer(pc={}) add imm j-side: delta={} != -{} — REJECTED",
                        target_pc, step_pc, delta, imm,
                    );
                    return false;
                }
                true
            } else if di != from_i && di != from_j {
                // dst doesn't touch tracked registers: passthrough
                if from_i != to_i || from_j != to_j || delta != 0 {
                    debug!(
                        target: "pcc",
                        "[PCC] target={} Transfer(pc={}) add imm passthrough mismatch — REJECTED",
                        target_pc, step_pc,
                    );
                    return false;
                }
                true
            } else {
                debug!(
                    target: "pcc",
                    "[PCC] target={} Transfer(pc={}) add imm: register pair mismatch — REJECTED",
                    target_pc, step_pc,
                );
                false
            }
        }

        // add dst, src_reg
        Instr::Alu {
            op: AluOp::Add,
            dst,
            src: Operand::Reg(src),
            ..
        } => {
            let di = dst.idx();
            if di == from_i && from_i == to_i && from_j == to_j {
                // dst is the i-side: bound shifts by ub(src) from interval state
                let (_src_min, src_max) = state.domain.get_interval(*src);
                if delta < src_max {
                    debug!(
                        target: "pcc",
                        "[PCC] target={} Transfer(pc={}) add reg: delta={} < ub(src)={} — REJECTED",
                        target_pc, step_pc, delta, src_max,
                    );
                    return false;
                }
                true
            } else if di == from_j && from_i == to_i && from_j == to_j {
                // dst is the j-side: bound shifts by -lb(src)
                let (src_min, _src_max) = state.domain.get_interval(*src);
                if delta < -src_min {
                    debug!(
                        target: "pcc",
                        "[PCC] target={} Transfer(pc={}) add reg j-side: delta={} < -lb(src)={} — REJECTED",
                        target_pc, step_pc, delta, -src_min,
                    );
                    return false;
                }
                true
            } else if di != from_i && di != from_j {
                // Passthrough
                if from_i != to_i || from_j != to_j || delta != 0 {
                    return false;
                }
                true
            } else {
                false
            }
        }

        // Instructions that don't write to tracked registers: passthrough
        _ => {
            // Check if this instruction writes to from_i or from_j
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
            let fi = Reg::idx_to_reg(from_i).unwrap_or(Reg::Zero);
            let fj = Reg::idx_to_reg(from_j).unwrap_or(Reg::Zero);

            if writes_to(fi) || writes_to(fj) {
                debug!(
                    target: "pcc",
                    "[PCC] target={} Transfer(pc={}) unsupported write to tracked reg — REJECTED",
                    target_pc, step_pc,
                );
                return false;
            }

            // Passthrough: constraint unchanged
            if from_i != to_i || from_j != to_j || delta != 0 {
                debug!(
                    target: "pcc",
                    "[PCC] target={} Transfer(pc={}) passthrough mismatch — REJECTED",
                    target_pc, step_pc,
                );
                return false;
            }
            true
        }
    }
}

// ---------------------------------------------------------------------------
// Replay verification: the v2 checker entry point
// ---------------------------------------------------------------------------

/// Verify a proof chain by replaying each step against the interval pre-state
/// stored in `explored_states` at each step's PC.
///
/// Fail-closed: returns None if any step fails or required state is missing.
pub fn verify_proof_chain_replay(
    entry: &AnnotationEntry,
    target_pc: usize,
    explored_states: &HashMap<usize, Vec<State>>,
    prog: &Program,
) -> Option<VerifiedEntry> {
    if entry.proof.is_empty() {
        return None;
    }

    let reg_name = |idx: usize| Reg::idx_to_reg(idx).map(|r| r.name()).unwrap_or("?");

    debug!(
        target: "pcc",
        "[PCC] target={}: replaying {}-step proof for [{} - {} <= {}]",
        target_pc, entry.proof.len(),
        reg_name(entry.i), reg_name(entry.j), entry.bound,
    );

    // Step 0: Verify Guard (must be proof[0])
    let ProofStep::Guard {
        pc: guard_pc,
        i: gi,
        j: gj,
        c: gc,
    } = &entry.proof[0]
    else {
        debug!(target: "pcc", "[PCC] target={}: proof[0] is not Guard — REJECTED", target_pc);
        return None;
    };

    // Look up the interval pre-state at the guard's PC
    let guard_state = get_unique_state(explored_states, *guard_pc, target_pc)?;

    // Only verify in interval mode
    if !matches!(guard_state.domain, NumericDomain::Interval(_)) {
        return None;
    }

    if !verify_guard(*guard_pc, *gi, *gj, *gc, guard_state, prog, target_pc) {
        return None;
    }

    // Initialize proof-check state
    let mut pcs = ProofCheckState {
        current_i: *gi,
        current_j: *gj,
        accumulated_bound: *gc,
    };

    // Steps 1..n: Verify Transfer steps
    for (sidx, step) in entry.proof.iter().enumerate().skip(1) {
        let ProofStep::Transfer {
            pc: step_pc,
            from_i,
            from_j,
            to_i,
            to_j,
            delta,
        } = step
        else {
            debug!(
                target: "pcc",
                "[PCC] target={} step {}: expected Transfer, got Guard — REJECTED",
                target_pc, sidx,
            );
            return None;
        };

        // Connectivity check
        if *from_i != pcs.current_i || *from_j != pcs.current_j {
            debug!(
                target: "pcc",
                "[PCC] target={} step {}: chain disconnected ({},{}) != ({},{}) — REJECTED",
                target_pc, sidx,
                reg_name(*from_i), reg_name(*from_j),
                reg_name(pcs.current_i), reg_name(pcs.current_j),
            );
            return None;
        }

        // Look up interval pre-state at this step's PC
        let step_state = get_unique_state(explored_states, *step_pc, target_pc)?;

        // Look up instruction at this step's PC
        if *step_pc >= prog.instrs.len() {
            return None;
        }
        let instr = &prog.instrs[*step_pc];

        if !verify_transfer(
            *step_pc, *from_i, *from_j, *to_i, *to_j, *delta, step_state, instr, target_pc,
        ) {
            return None;
        }

        // Advance proof-check state
        pcs.current_i = *to_i;
        pcs.current_j = *to_j;
        pcs.accumulated_bound = pcs.accumulated_bound.checked_add(*delta)?;
    }

    // Final checks
    if pcs.current_i != entry.i || pcs.current_j != entry.j {
        debug!(
            target: "pcc",
            "[PCC] target={}: final ({},{}) != entry ({},{}) — REJECTED",
            target_pc,
            reg_name(pcs.current_i), reg_name(pcs.current_j),
            reg_name(entry.i), reg_name(entry.j),
        );
        return None;
    }
    if pcs.accumulated_bound != entry.bound {
        debug!(
            target: "pcc",
            "[PCC] target={}: accumulated bound {} != entry bound {} — REJECTED",
            target_pc, pcs.accumulated_bound, entry.bound,
        );
        return None;
    }

    info!(
        target: "pcc",
        "[PCC] target={}: proof verified [{} - {} <= {}]",
        target_pc, reg_name(entry.i), reg_name(entry.j), entry.bound,
    );
    Some(VerifiedEntry {
        i: entry.i,
        j: entry.j,
        bound: entry.bound,
    })
}

/// Look up the unique interval pre-state at a PC from explored_states.
/// Fail-closed: returns None if missing or if multiple states exist (non-straightline).
fn get_unique_state<'a>(
    explored_states: &'a HashMap<usize, Vec<State>>,
    pc: usize,
    target_pc: usize,
) -> Option<&'a State> {
    let states = explored_states.get(&pc)?;
    if states.len() != 1 {
        debug!(
            target: "pcc",
            "[PCC] target={}: expected 1 state at pc={}, found {} — REJECTED (non-straightline?)",
            target_pc, pc, states.len(),
        );
        return None;
    }
    Some(&states[0])
}
