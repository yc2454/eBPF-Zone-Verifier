use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, Instr, Operand};
use crate::domains::numeric::NumericDomain;

use super::model::{Constraint, EdgeObligation, ObligationKind, ProgramCertificate, ProofSource};
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
    if ob.proof[0].from != ob.target.i || ob.proof[ob.proof.len() - 1].to != ob.target.j {
        return;
    }
    for w in ob.proof.windows(2) {
        if w[0].to != w[1].from {
            return;
        }
    }

    let Some(ivl) = pre_state.domain.as_interval() else {
        return;
    };
    for step in &ob.proof {
        match step.source {
            ProofSource::PreState => {
                let Some(from) = Reg::idx_to_reg(step.from) else {
                    return;
                };
                let Some(to) = Reg::idx_to_reg(step.to) else {
                    return;
                };
                let Some(actual) = prestate_bound(ivl, from, to) else {
                    return;
                };
                if actual > step.weight {
                    return;
                }
            }
            ProofSource::Guard => {
                // Guard-based proofs are not enabled in this checker path yet.
                return;
            }
        }
    }

    let Some(pre_sum) = checked_sum(ob.proof.iter().map(|s| s.weight)) else {
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
                // Reserved for v2 guard semantics.
                continue;
            }
        }
    }
}
