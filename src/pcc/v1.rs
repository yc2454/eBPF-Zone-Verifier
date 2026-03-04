use std::hash::{Hash, Hasher};

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, Instr, MemSize, Operand, Program};
use crate::domains::dbm::{Dbm, INF};
use crate::domains::interval::IntervalState;

use super::model::{Constraint, EdgeObligation, ObligationKind, ProofStep};

fn mem_size_bytes(sz: MemSize) -> i64 {
    match sz {
        MemSize::U8 => 1,
        MemSize::U16 => 2,
        MemSize::U32 => 4,
        MemSize::U64 => 8,
    }
}

pub(crate) fn hash_v1_pred_context(
    pred_pc: usize,
    dst: Reg,
    src: Reg,
    d_dst_data: i64,
    d_data_end: i64,
    src_umax: i64,
) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    pred_pc.hash(&mut h);
    dst.idx().hash(&mut h);
    src.idx().hash(&mut h);
    d_dst_data.hash(&mut h);
    d_data_end.hash(&mut h);
    src_umax.hash(&mut h);
    h.finish()
}

pub(crate) fn prestate_bound(ivl: &IntervalState, i: Reg, j: Reg) -> Option<i64> {
    if i == j {
        return Some(0);
    }
    // reg - anchor <= off + var_off
    if j.is_anchor()
        && let Some(po) = ivl.get_ptr_offset(i)
        && po.anchor == j
    {
        return Some(po.off.saturating_add(po.var_off as i64));
    }
    // @data - @data_end <= -packet_size_lower_bound
    if i == Reg::AnchorData
        && j == Reg::AnchorDataEnd
        && let Some(min_pkt) = ivl.get_packet_size_bound()
    {
        return Some(-(min_pkt as i64));
    }
    None
}

pub(crate) fn compute_v1_pred_fingerprint_from_interval(
    pre_state: &State,
    pred_instr: &Instr,
    ob: &EdgeObligation,
) -> Option<u64> {
    let Instr::Alu {
        op: AluOp::Add,
        dst,
        src: Operand::Reg(src),
        ..
    } = pred_instr
    else {
        return None;
    };
    let target_i = Reg::idx_to_reg(ob.target.i)?;
    let target_j = Reg::idx_to_reg(ob.target.j)?;
    if target_i != *dst || target_j != Reg::AnchorDataEnd {
        return None;
    }
    let ivl = pre_state.domain.as_interval()?;
    let d_dst_data = prestate_bound(ivl, *dst, Reg::AnchorData)?;
    let d_data_end = prestate_bound(ivl, Reg::AnchorData, Reg::AnchorDataEnd)?;
    let src_umax = ivl.get_bounds(*src).umax as i64;
    Some(hash_v1_pred_context(
        pre_state.pc,
        *dst,
        *src,
        d_dst_data,
        d_data_end,
        src_umax,
    ))
}

/// v1 producer: derive obligations from zone DBM on edges shaped as
/// `dst += src` followed by `load [dst + off]`.
pub fn generate_v1_obligations_from_zone(prog: &Program, dbms: &[Dbm]) -> Vec<EdgeObligation> {
    let mut out = Vec::new();
    if prog.instrs.len() < 2 {
        return out;
    }
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
        let Some(dbm) = dbms.get(pred_pc) else {
            continue;
        };
        let d_dst_data = dbm.get(*dst, Reg::AnchorData);
        let d_data_end = dbm.get(Reg::AnchorData, Reg::AnchorDataEnd);
        let src_umax = dbm.get(*src, Reg::Zero);
        if d_dst_data >= INF || d_data_end >= INF || src_umax >= INF {
            continue;
        }
        let Some(pre_sum) = d_dst_data.checked_add(d_data_end) else {
            continue;
        };
        let Some(target_c) = pre_sum.checked_add(src_umax) else {
            continue;
        };
        // Emit only obligations that are immediately useful for this load.
        let access_need = -((*off as i64) + mem_size_bytes(*size));
        if target_c > access_need {
            continue;
        }
        out.push(EdgeObligation {
            kind: ObligationKind::AddRegPacketBound,
            pred_pc,
            succ_pc,
            pred_fingerprint: hash_v1_pred_context(
                pred_pc, *dst, *src, d_dst_data, d_data_end, src_umax,
            ),
            target: Constraint {
                i: dst.idx(),
                j: Reg::AnchorDataEnd.idx(),
                c: target_c,
            },
            proof: vec![
                ProofStep::PreStateStep {
                    i: dst.idx(),
                    j: Reg::AnchorData.idx(),
                    c: d_dst_data,
                },
                ProofStep::PreStateStep {
                    i: Reg::AnchorData.idx(),
                    j: Reg::AnchorDataEnd.idx(),
                    c: d_data_end,
                },
            ],
        });
    }
    out
}
