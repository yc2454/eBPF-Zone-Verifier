use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, CmpOp, Instr, Operand, Width};
use crate::domains::numeric::NumericDomain;
use log::{debug, info};

use super::model::{AnnotationEntry, ProgramCertificate};

// Used by derive_guard_constraint_from_branch; will be reused in Step 3.
#[allow(dead_code)]
#[derive(Clone, Copy)]
struct Constraint {
    i: usize,
    j: usize,
    c: i64,
}

#[derive(Debug, Clone, Copy)]
pub struct VerifiedEntry {
    pub i: usize,
    pub j: usize,
    pub bound: i64,
}

#[allow(dead_code)]
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

#[allow(dead_code)]
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

#[allow(dead_code)]
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

/// V1 single-edge checker — stubbed out pending v2 replay implementation (Step 3).
/// Fail-closed: always returns false for v2 certificates.
fn verify_pc_annotation_entry(
    _entry: &AnnotationEntry,
    _pre_state: &State,
    _pred_instr: &Instr,
    _guard: Option<Constraint>,
    succ_pc: usize,
) -> bool {
    debug!(
        target: "pcc",
        "[PCC] pc={}: v1 single-edge checker disabled for v2 certificates",
        succ_pc,
    );
    false
}

/// Verifies certificate entries on a single CFG edge.
///
/// This is the semantic checker phase for the prototype pc-annotation model.
/// Fail-closed: any invalid entry is skipped and baseline analysis continues.
pub fn verify_certificate_entries_for_edge(
    cert: &ProgramCertificate,
    pre_state: &State,
    pred_instr: &Instr,
    succ_state: &State,
) -> Vec<VerifiedEntry> {
    let mut verified = Vec::new();
    if !matches!(succ_state.domain, NumericDomain::Interval(_)) {
        return verified;
    }
    let succ_pc = succ_state.pc;
    let guard = derive_guard_constraint_from_branch(pred_instr, pre_state.pc, succ_pc);
    for ann in &cert.pc_annotations {
        if ann.pc != succ_pc {
            continue;
        }
        debug!(
            target: "pcc",
            "[PCC] pc={}: checking {} annotation entr{} (edge from pc={})",
            succ_pc,
            ann.entries.len(),
            if ann.entries.len() == 1 { "y" } else { "ies" },
            pre_state.pc,
        );
        for (eidx, entry) in ann.entries.iter().enumerate() {
            let i_name = Reg::idx_to_reg(entry.i).map(|r| r.name()).unwrap_or("?");
            let j_name = Reg::idx_to_reg(entry.j).map(|r| r.name()).unwrap_or("?");
            debug!(
                target: "pcc",
                "[PCC] pc={} entry {}: [{} - {} ≤ {}] ({}-step proof)",
                succ_pc, eidx, i_name, j_name, entry.bound, entry.proof.len(),
            );
            if verify_pc_annotation_entry(entry, pre_state, pred_instr, guard, succ_pc) {
                info!(
                    target: "pcc",
                    "[PCC] pc={} entry {}: proof verified [{} - {} ≤ {}]",
                    succ_pc, eidx, i_name, j_name, entry.bound,
                );
                verified.push(VerifiedEntry {
                    i: entry.i,
                    j: entry.j,
                    bound: entry.bound,
                });
            } else {
                // Visible at default verbosity so users know the cert entry was rejected
                // and can re-run with -v to see the per-step rejection reason.
                info!(
                    target: "pcc",
                    "[PCC] pc={} entry {}: [{} - {} ≤ {}] proof REJECTED (run with -v for details)",
                    succ_pc, eidx, i_name, j_name, entry.bound,
                );
            }
        }
    }
    verified
}
