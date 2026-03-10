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
    pub left_reg: usize,
    pub right_reg: usize,
    pub bound: i64,
}

// ---------------------------------------------------------------------------
// Internal proof-check state (separate from verifier State)
// ---------------------------------------------------------------------------

/// Tracks progress through a single proof chain during replay verification.
///
/// This is **not** the verifier's abstract state — it is purely proof-chain bookkeeping,
/// kept entirely separate from [`State`] to make it clear that the checker only reads
/// interval states and never modifies them.
///
/// **Invariant:** after processing step `k` of the chain,
/// `current_left - current_right <= accumulated_bound` is the bound derivable
/// from all steps seen so far. The chain starts from the Guard's `c` (the base fact
/// independently verified against the interval state at the divergence point) and
/// accumulates each Transfer's `delta`. At the end of the chain,
/// `accumulated_bound` must equal `entry.bound`.
struct ProofCheckState {
    /// The left register of the currently tracked constraint pair.
    current_left: usize,
    /// The right register of the currently tracked constraint pair.
    current_right: usize,
    /// Running upper bound: `current_left - current_right <= accumulated_bound`.
    accumulated_bound: i64,
}

// ---------------------------------------------------------------------------
// Interval-state queries
// ---------------------------------------------------------------------------

pub fn distance_upper_bound(state: &State, i: Reg, j: Reg) -> Option<i64> {
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
    left_reg: usize,
    right_reg: usize,
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
    let (left_reg, right_reg, c) = match (*op, branch_taken) {
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
    Some(Constraint {
        left_reg,
        right_reg,
        c,
    })
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
    left_idx: usize,
    right_idx: usize,
    c: i64,
    state: &State,
    prog: &Program,
    target_pc: usize,
) -> bool {
    let Some(i) = Reg::idx_to_reg(left_idx) else {
        return false;
    };
    let Some(j) = Reg::idx_to_reg(right_idx) else {
        return false;
    };

    // Path 1: branch-derived guard.
    // Check if the instruction at guard_pc is a branch and the guard matches
    // the condition on the edge toward the target.
    let instr = &prog.instrs[guard_pc];
    if let Some(branch_guard) = derive_guard_constraint_from_branch(instr, guard_pc, guard_pc + 1) {
        if left_idx == branch_guard.left_reg
            && right_idx == branch_guard.right_reg
            && c == branch_guard.c
        {
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
/// A Transfer step claims: if `pre_left - pre_right <= b` holds in the pre-state of
/// the instruction at `step_pc`, then `post_left - post_right <= b + delta` holds in
/// the post-state. This function checks whether the claimed `(post_left, post_right, delta)`
/// is a sound consequence of the instruction's semantics.
///
/// Let `L = pre_left`, `R = pre_right`. The four supported cases and their soundness
/// arguments (all using the fact that `L - R <= b` holds before the instruction):
///
/// - **`add dst, imm`** (`dst == L`, `post_left == L`, `post_right == R`):
///   `(L+imm) - R = (L-R) + imm <= b + imm`. Requires `delta == imm` exactly.
///
/// - **`add dst, imm`** (`dst == R`, `post_left == L`, `post_right == R`):
///   `L - (R+imm) = (L-R) - imm <= b - imm`. Requires `delta == -imm` exactly.
///
/// - **`add dst, src_reg`** (`dst == L`, `post_left == L`, `post_right == R`):
///   `(L+src) - R = (L-R) + src`. Since `src <= ub(src)` (from the interval pre-state),
///   the result is `<= b + ub(src)`. Requires `delta >= ub(src)`; the generator uses
///   the tightest value (`delta == ub(src)`), but the checker accepts any sound overestimate.
///
/// - **`add dst, src_reg`** (`dst == R`, `post_left == L`, `post_right == R`):
///   `L - (R+src) = (L-R) - src`. Since `src >= lb(src)`, the result is `<= b - lb(src)`.
///   Requires `delta >= -lb(src)`.
///
/// - **`mov dst, src`** (`src == L`, `post_left == dst.idx()`, `post_right == R`):
///   After the move, `dst` holds the old value of `L`. The constraint `L - R <= b` becomes
///   `dst - R <= b` with the same bound. Requires `delta == 0` and `post_left == dst.idx()`.
///
/// - **Passthrough** (`dst ∉ {L, R}`): the constraint registers are untouched.
///   Requires `post_left == pre_left`, `post_right == pre_right`, `delta == 0`.
///
/// - **Unsupported write to `L` or `R`**: returns `false` (chain fails, fail-closed).
fn verify_transfer(
    step_pc: usize,
    pre_left: usize,
    pre_right: usize,
    post_left: usize,
    post_right: usize,
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
            // If pre_left tracks src, then post_left should be dst (src's value is now in dst).
            // If pre_right tracks src, symmetric.
            // If neither pre_left nor pre_right is dst, passthrough.
            let expected_post_left = if pre_left == src.idx()
                && *dst != Reg::idx_to_reg(pre_right).unwrap_or(Reg::Zero)
            {
                dst.idx()
            } else {
                pre_left
            };
            let expected_post_right = if pre_right == src.idx()
                && *dst != Reg::idx_to_reg(pre_left).unwrap_or(Reg::Zero)
            {
                dst.idx()
            } else {
                pre_right
            };

            // If dst overwrites a tracked register and we're not substituting, fail.
            if (*dst == Reg::idx_to_reg(pre_left).unwrap_or(Reg::Zero)
                || *dst == Reg::idx_to_reg(pre_right).unwrap_or(Reg::Zero))
                && post_left == pre_left
                && post_right == pre_right
                && pre_left != src.idx()
                && pre_right != src.idx()
            {
                debug!(
                    target: "pcc",
                    "[PCC] target={} Transfer(pc={}) mov {}<-{}: dst overwrites tracked reg — REJECTED",
                    target_pc, step_pc, dst.name(), src.name(),
                );
                return false;
            }

            if post_left != expected_post_left || post_right != expected_post_right || delta != 0 {
                debug!(
                    target: "pcc",
                    "[PCC] target={} Transfer(pc={}) mov: expected ({},{},0) got ({},{},{}) — REJECTED",
                    target_pc, step_pc,
                    reg_name(expected_post_left), reg_name(expected_post_right),
                    reg_name(post_left), reg_name(post_right), delta,
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
            if di == pre_left && pre_left == post_left && pre_right == post_right {
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
            } else if di == pre_right && pre_left == post_left && pre_right == post_right {
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
            } else if di != pre_left && di != pre_right {
                // dst doesn't touch tracked registers: passthrough
                if pre_left != post_left || pre_right != post_right || delta != 0 {
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
            if di == pre_left && pre_left == post_left && pre_right == post_right {
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
            } else if di == pre_right && pre_left == post_left && pre_right == post_right {
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
            } else if di != pre_left && di != pre_right {
                // Passthrough
                if pre_left != post_left || pre_right != post_right || delta != 0 {
                    return false;
                }
                true
            } else {
                false
            }
        }

        // Instructions that don't write to tracked registers: passthrough
        _ => {
            // Check if this instruction writes to pre_left or pre_right
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
            let fl = Reg::idx_to_reg(pre_left).unwrap_or(Reg::Zero);
            let fr = Reg::idx_to_reg(pre_right).unwrap_or(Reg::Zero);

            if writes_to(fl) || writes_to(fr) {
                debug!(
                    target: "pcc",
                    "[PCC] target={} Transfer(pc={}) unsupported write to tracked reg — REJECTED",
                    target_pc, step_pc,
                );
                return false;
            }

            // Passthrough: constraint unchanged
            if pre_left != post_left || pre_right != post_right || delta != 0 {
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
// Replay verification
// ---------------------------------------------------------------------------

/// Verify a proof chain by replaying each step against the interval pre-states
/// stored in `explored_states` at each step's PC.
///
/// The chain must begin with a [`ProofStep::Guard`] and be followed by zero or more
/// [`ProofStep::Transfer`] steps. Replay maintains the running invariant:
/// `current_left - current_right <= accumulated_bound`, starting from the Guard's
/// independently verified base case and accumulating `delta` from each Transfer.
///
/// Returns `Some(VerifiedEntry)` only when **all** of the following hold:
/// 1. `proof[0]` is a Guard whose claimed constraint is verified against the interval
///    pre-state at the guard's PC (state-derived or branch-derived — see [`verify_guard`]).
/// 2. Every subsequent Transfer is connected (its `pre_*` matches the previous step's
///    output) and sound for the instruction and interval pre-state at its PC.
/// 3. The chain endpoint `(current_left, current_right)` matches `entry.(left_reg, right_reg)`.
/// 4. The final `accumulated_bound` equals `entry.bound`.
///
/// Fail-closed: returns `None` if any check fails or a required state is missing.
/// The caller skips this entry; the interval verifier proceeds without refinement.
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
        reg_name(entry.left_reg), reg_name(entry.right_reg), entry.bound,
    );

    // Step 0: Verify Guard (must be proof[0])
    let ProofStep::Guard {
        pc: guard_pc,
        left_reg: g_left,
        right_reg: g_right,
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

    if !verify_guard(
        *guard_pc,
        *g_left,
        *g_right,
        *gc,
        guard_state,
        prog,
        target_pc,
    ) {
        return None;
    }

    // Initialize proof-check state
    let mut pcs = ProofCheckState {
        current_left: *g_left,
        current_right: *g_right,
        accumulated_bound: *gc,
    };

    // Steps 1..n: Verify Transfer steps
    for (sidx, step) in entry.proof.iter().enumerate().skip(1) {
        let ProofStep::Transfer {
            pc: step_pc,
            pre_left_reg,
            pre_right_reg,
            post_left_reg,
            post_right_reg,
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
        if *pre_left_reg != pcs.current_left || *pre_right_reg != pcs.current_right {
            debug!(
                target: "pcc",
                "[PCC] target={} step {}: chain disconnected ({},{}) != ({},{}) — REJECTED",
                target_pc, sidx,
                reg_name(*pre_left_reg), reg_name(*pre_right_reg),
                reg_name(pcs.current_left), reg_name(pcs.current_right),
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
            *step_pc,
            *pre_left_reg,
            *pre_right_reg,
            *post_left_reg,
            *post_right_reg,
            *delta,
            step_state,
            instr,
            target_pc,
        ) {
            return None;
        }

        // Advance proof-check state
        pcs.current_left = *post_left_reg;
        pcs.current_right = *post_right_reg;
        pcs.accumulated_bound = pcs.accumulated_bound.checked_add(*delta)?;
    }

    // Final checks
    if pcs.current_left != entry.left_reg || pcs.current_right != entry.right_reg {
        debug!(
            target: "pcc",
            "[PCC] target={}: final ({},{}) != entry ({},{}) — REJECTED",
            target_pc,
            reg_name(pcs.current_left), reg_name(pcs.current_right),
            reg_name(entry.left_reg), reg_name(entry.right_reg),
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
        target_pc, reg_name(entry.left_reg), reg_name(entry.right_reg), entry.bound,
    );
    Some(VerifiedEntry {
        left_reg: entry.left_reg,
        right_reg: entry.right_reg,
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
