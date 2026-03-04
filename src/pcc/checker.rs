use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, CmpOp, Instr, Operand, Width};
use crate::domains::numeric::NumericDomain;
use std::hash::{Hash, Hasher};

use super::model::{Constraint, EdgeObligation, ObligationKind, ProgramCertificate, ProofStep};
use super::v1::{compute_v1_pred_fingerprint_from_interval, prestate_bound};

fn checked_sum(weights: impl Iterator<Item = i64>) -> Option<i64> {
    let mut sum = 0i64;
    for w in weights {
        sum = sum.checked_add(w)?;
    }
    Some(sum)
}

fn apply_add_reg_transfer_to_bound(
    pre_state: &State,
    pred_instr: &Instr,
    i: Reg,
    j: Reg,
    pre_bound: i64,
) -> Option<i64> {
    match pred_instr {
        Instr::Alu {
            op: AluOp::Add,
            dst,
            src: Operand::Reg(src),
            ..
        } => {
            if *dst == i {
                let src_umax = pre_state.domain.as_interval()?.get_bounds(*src).umax as i64;
                pre_bound.checked_add(src_umax)
            } else if *dst == j {
                let src_umin = pre_state.domain.as_interval()?.get_bounds(*src).umin as i64;
                pre_bound.checked_sub(src_umin)
            } else {
                Some(pre_bound)
            }
        }
        _ => Some(pre_bound),
    }
}

fn apply_verified_packet_end_fact(succ_state: &mut State, target: &Constraint) {
    let Some(i) = Reg::idx_to_reg(target.i) else {
        return;
    };
    let Some(j) = Reg::idx_to_reg(target.j) else {
        return;
    };
    if j != Reg::AnchorDataEnd {
        return;
    }
    let Some(ivl) = succ_state.domain.as_interval_mut() else {
        return;
    };
    let Some(po) = ivl.get_ptr_offset(i).copied() else {
        return;
    };
    if po.anchor != Reg::AnchorData {
        return;
    }
    // From i - @data_end <= c  ==>  @data_end - i >= -c.
    let proven_end_from_i = (-target.c).max(0);
    let proven_range = proven_end_from_i.saturating_sub(po.off);
    let reg = ivl.get_mut(i);
    if let Some(ref mut ptr_off) = reg.ptr_offset {
        ptr_off.range = Some(ptr_off.range.unwrap_or(proven_range).max(proven_range));
    }
}

fn hash_branch_pred_context(
    pred_pc: usize,
    width: Width,
    left: Reg,
    op: CmpOp,
    right: Reg,
    branch_taken: bool,
) -> u64 {
    fn width_tag(w: Width) -> u8 {
        match w {
            Width::W32 => 32,
            Width::W64 => 64,
        }
    }
    fn cmp_tag(op: CmpOp) -> u8 {
        match op {
            CmpOp::UGe => 1,
            CmpOp::ULe => 2,
            CmpOp::UGt => 3,
            CmpOp::ULt => 4,
            CmpOp::Eq => 5,
            CmpOp::Ne => 6,
            CmpOp::SLt => 7,
            CmpOp::SGt => 8,
            CmpOp::SLe => 9,
            CmpOp::SGe => 10,
            CmpOp::Test => 11,
        }
    }
    let mut h = std::collections::hash_map::DefaultHasher::new();
    pred_pc.hash(&mut h);
    width_tag(width).hash(&mut h);
    left.idx().hash(&mut h);
    cmp_tag(op).hash(&mut h);
    right.idx().hash(&mut h);
    branch_taken.hash(&mut h);
    h.finish()
}

fn derive_guard_constraint_from_branch(
    pred_instr: &Instr,
    pred_pc: usize,
    succ_pc: usize,
) -> Option<(bool, Constraint)> {
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
    let i;
    let j;
    let c;
    match (*op, branch_taken) {
        // taken path
        (CmpOp::ULe | CmpOp::SLe, true) | (CmpOp::UGt | CmpOp::SGt, false) => {
            i = left.idx();
            j = right.idx();
            c = 0;
        }
        (CmpOp::ULt | CmpOp::SLt, true) | (CmpOp::UGe | CmpOp::SGe, false) => {
            i = left.idx();
            j = right.idx();
            c = -1;
        }
        (CmpOp::UGe | CmpOp::SGe, true) | (CmpOp::ULt | CmpOp::SLt, false) => {
            i = right.idx();
            j = left.idx();
            c = 0;
        }
        (CmpOp::UGt | CmpOp::SGt, true) | (CmpOp::ULe | CmpOp::SLe, false) => {
            i = right.idx();
            j = left.idx();
            c = -1;
        }
        _ => return None,
    }
    Some((branch_taken, Constraint { i, j, c }))
}

fn compute_branch_pred_fingerprint(
    pre_state: &State,
    pred_instr: &Instr,
    succ_pc: usize,
) -> Option<u64> {
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
    let branch_taken = if succ_pc == *target {
        true
    } else if succ_pc == pre_state.pc + 1 {
        false
    } else {
        return None;
    };
    Some(hash_branch_pred_context(
        pre_state.pc,
        *width,
        *left,
        *op,
        *right,
        branch_taken,
    ))
}

fn apply_add_reg_packet_bound_obligation(
    ob: &EdgeObligation,
    pre_state: &State,
    pred_instr: &Instr,
    succ_state: &mut State,
) {
    let Some(pre_fp) = compute_v1_pred_fingerprint_from_interval(pre_state, pred_instr, ob) else {
        return;
    };
    if ob.pred_fingerprint != pre_fp {
        return;
    }
    let Some(i) = Reg::idx_to_reg(ob.target.i) else {
        return;
    };
    let Some(j) = Reg::idx_to_reg(ob.target.j) else {
        return;
    };
    if ob.proof.is_empty() {
        return;
    }
    if ob.proof[0].i() != ob.target.i || ob.proof[ob.proof.len() - 1].j() != ob.target.j {
        return;
    }
    for w in ob.proof.windows(2) {
        if w[0].j() != w[1].i() {
            return;
        }
    }

    let Some(ivl) = pre_state.domain.as_interval() else {
        return;
    };
    for step in &ob.proof {
        match step {
            ProofStep::PreStateStep { i, j, c } => {
                let Some(from) = Reg::idx_to_reg(*i) else {
                    return;
                };
                let Some(to) = Reg::idx_to_reg(*j) else {
                    return;
                };
                let Some(actual) = prestate_bound(ivl, from, to) else {
                    return;
                };
                if actual > *c {
                    return;
                }
            }
            ProofStep::GuardStep { .. } => {
                // Guard-based proofs are not enabled in this checker path yet.
                return;
            }
        }
    }

    let Some(pre_sum) = checked_sum(ob.proof.iter().map(ProofStep::c)) else {
        return;
    };
    let Some(post_bound) = apply_add_reg_transfer_to_bound(pre_state, pred_instr, i, j, pre_sum)
    else {
        return;
    };
    if post_bound != ob.target.c {
        return;
    }
    apply_verified_packet_end_fact(succ_state, &ob.target);
}

fn apply_branch_guard_bound_obligation(
    ob: &EdgeObligation,
    pre_state: &State,
    pred_instr: &Instr,
    succ_state: &mut State,
) {
    let Some(ob_taken) = ob.branch_taken else {
        return;
    };
    let Some(pre_fp) = compute_branch_pred_fingerprint(pre_state, pred_instr, succ_state.pc) else {
        return;
    };
    if ob.pred_fingerprint != pre_fp {
        return;
    }
    let Some((actual_taken, implied_guard)) =
        derive_guard_constraint_from_branch(pred_instr, pre_state.pc, succ_state.pc)
    else {
        return;
    };
    if actual_taken != ob_taken {
        return;
    }
    if ob.proof.is_empty() {
        return;
    }
    if ob.proof[0].i() != ob.target.i || ob.proof[ob.proof.len() - 1].j() != ob.target.j {
        return;
    }
    for w in ob.proof.windows(2) {
        if w[0].j() != w[1].i() {
            return;
        }
    }

    let Some(ivl) = pre_state.domain.as_interval() else {
        return;
    };
    for step in &ob.proof {
        match step {
            ProofStep::PreStateStep { i, j, c } => {
                let Some(from) = Reg::idx_to_reg(*i) else {
                    return;
                };
                let Some(to) = Reg::idx_to_reg(*j) else {
                    return;
                };
                let Some(actual) = prestate_bound(ivl, from, to) else {
                    return;
                };
                if actual > *c {
                    return;
                }
            }
            ProofStep::GuardStep { i, j, c } => {
                if *i != implied_guard.i || *j != implied_guard.j || *c != implied_guard.c {
                    return;
                }
            }
        }
    }
    let Some(sum) = checked_sum(ob.proof.iter().map(ProofStep::c)) else {
        return;
    };
    if sum != ob.target.c {
        return;
    }
    apply_verified_packet_end_fact(succ_state, &ob.target);
}

/// Applies certificate-aided refinement on a single CFG edge.
///
/// This function is called after transfer creates a successor state. It verifies
/// all matching edge obligations against the predecessor state + instruction
/// semantics, and applies only narrow packet-range refinements when proofs are valid.
///
/// Fail-closed behavior:
/// - Any malformed or unsupported obligation is ignored.
/// - Analysis continues with baseline semantics.
pub fn apply_certificate_aided_refinement(
    cert: &ProgramCertificate,
    pre_state: &State,
    pred_instr: &Instr,
    succ_state: &mut State,
) {
    if !matches!(succ_state.domain, NumericDomain::Interval(_)) {
        return;
    }
    for ob in &cert.obligations {
        if ob.pred_pc != pre_state.pc || ob.succ_pc != succ_state.pc {
            continue;
        }
        match ob.kind {
            ObligationKind::AddRegPacketBound => {
                apply_add_reg_packet_bound_obligation(ob, pre_state, pred_instr, succ_state);
            }
            ObligationKind::BranchGuardBound => {
                apply_branch_guard_bound_obligation(ob, pre_state, pred_instr, succ_state);
            }
        }
    }
}
