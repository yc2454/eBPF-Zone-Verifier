use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, CmpOp, Instr, Operand, Width};
use crate::domains::numeric::NumericDomain;

use super::model::{
    checked_sum, AnnotationEntry, ProgramCertificate, ProofStep, MAX_STEPS_PER_ENTRY,
};

#[derive(Clone, Copy)]
struct Constraint {
    i: usize,
    j: usize,
    c: i64,
}

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

fn transfer_upper_bound_for_constraint(
    pre_state: &State,
    pred_instr: &Instr,
    i: Reg,
    j: Reg,
) -> Option<i64> {
    let base = |x: Reg, y: Reg| distance_upper_bound(pre_state, x, y);
    match pred_instr {
        Instr::Alu {
            op: AluOp::Mov,
            dst,
            src: Operand::Reg(src),
            ..
        } => {
            if *dst == i {
                base(*src, j)
            } else if *dst == j {
                base(i, *src)
            } else {
                base(i, j)
            }
        }
        Instr::Alu {
            op: AluOp::Mov,
            dst,
            src: Operand::Imm(imm),
            ..
        } => {
            if *dst == i {
                base(Reg::Zero, j)?.checked_add(*imm)
            } else if *dst == j {
                base(i, Reg::Zero)?.checked_sub(*imm)
            } else {
                base(i, j)
            }
        }
        Instr::Alu {
            op: AluOp::Add,
            dst,
            src: Operand::Imm(imm),
            ..
        } => {
            let ub = base(i, j)?;
            if *dst == i {
                ub.checked_add(*imm)
            } else if *dst == j {
                ub.checked_sub(*imm)
            } else {
                Some(ub)
            }
        }
        Instr::Alu {
            op: AluOp::Add,
            dst,
            src: Operand::Reg(src),
            ..
        } => {
            let ub = base(i, j)?;
            let (src_min, src_max) = pre_state.domain.get_interval(*src);
            if *dst == i {
                ub.checked_add(src_max)
            } else if *dst == j {
                ub.checked_sub(src_min)
            } else {
                Some(ub)
            }
        }
        Instr::Alu {
            op: AluOp::And,
            dst,
            ..
        } => {
            if *dst == i || *dst == j {
                None
            } else {
                base(i, j)
            }
        }
        Instr::Alu { .. }
        | Instr::Endian { .. }
        | Instr::Load { .. }
        | Instr::LoadMap { .. }
        | Instr::Call { .. }
        | Instr::LoadPacket { .. } => {
            let writes_i_or_j = match pred_instr {
                Instr::Alu { dst, .. }
                | Instr::Endian { dst, .. }
                | Instr::Load { dst, .. }
                | Instr::LoadMap { dst, .. } => *dst == i || *dst == j,
                Instr::Call { .. } | Instr::LoadPacket { .. } => i == Reg::R0 || j == Reg::R0,
                _ => false,
            };
            if writes_i_or_j { None } else { base(i, j) }
        }
        _ => base(i, j),
    }
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

fn apply_verified_packet_end_fact(succ_state: &mut State, i_idx: usize, j_idx: usize, c: i64) {
    let Some(i) = Reg::idx_to_reg(i_idx) else {
        return;
    };
    let Some(j) = Reg::idx_to_reg(j_idx) else {
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
    let proven_end_from_i = (-c).max(0);
    let proven_range = proven_end_from_i.saturating_sub(po.off);
    let reg = ivl.get_mut(i);
    if let Some(ref mut ptr_off) = reg.ptr_offset {
        ptr_off.range = Some(ptr_off.range.unwrap_or(proven_range).max(proven_range));
    }
}

fn verify_pc_annotation_entry(
    entry: &AnnotationEntry,
    pre_state: &State,
    pred_instr: &Instr,
    guard: Option<Constraint>,
) -> bool {
    if entry.proof.is_empty() || entry.proof.len() > MAX_STEPS_PER_ENTRY {
        return false;
    }
    if entry.proof[0].i() != entry.i || entry.proof[entry.proof.len() - 1].j() != entry.j {
        return false;
    }
    for w in entry.proof.windows(2) {
        if w[0].j() != w[1].i() {
            return false;
        }
    }
    for step in &entry.proof {
        let Some(i) = Reg::idx_to_reg(step.i()) else {
            return false;
        };
        let Some(j) = Reg::idx_to_reg(step.j()) else {
            return false;
        };
        match step {
            ProofStep::GuardStep { i, j, c } => {
                let Some(g) = guard else {
                    return false;
                };
                if *i != g.i || *j != g.j || *c != g.c {
                    return false;
                }
            }
            ProofStep::PreStateStep { c, .. } => {
                let Some(post_ub) =
                    transfer_upper_bound_for_constraint(pre_state, pred_instr, i, j)
                else {
                    return false;
                };
                if post_ub > *c {
                    return false;
                }
            }
        }
    }
    let Some(sum) = checked_sum(entry.proof.iter().map(ProofStep::c)) else {
        return false;
    };
    sum == entry.bound
}

/// Applies certificate-aided refinement on a single CFG edge.
///
/// This is the semantic checker phase for the prototype pc-annotation model.
/// Fail-closed: any invalid entry is ignored and baseline analysis continues.
pub fn apply_certificate_aided_refinement(
    cert: &ProgramCertificate,
    pre_state: &State,
    pred_instr: &Instr,
    succ_state: &mut State,
) {
    if !matches!(succ_state.domain, NumericDomain::Interval(_)) {
        return;
    }
    let guard = derive_guard_constraint_from_branch(pred_instr, pre_state.pc, succ_state.pc);
    for ann in &cert.pc_annotations {
        if ann.pc != succ_state.pc {
            continue;
        }
        for entry in &ann.entries {
            if verify_pc_annotation_entry(entry, pre_state, pred_instr, guard) {
                apply_verified_packet_end_fact(succ_state, entry.i, entry.j, entry.bound);
            }
        }
    }
}
