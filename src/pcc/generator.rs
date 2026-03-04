use std::collections::BTreeMap;

use crate::analysis::machine::reg::Reg;
use crate::ast::{AluOp, Instr, MemSize, Operand, Program};
use crate::domains::dbm::{Dbm, INF};

use super::model::{AnnotationEntry, PcAnnotation, ProgramCertificate, ProofStep};
use super::program_hash;

fn mem_size_bytes(sz: MemSize) -> i64 {
    match sz {
        MemSize::U8 => 1,
        MemSize::U16 => 2,
        MemSize::U32 => 4,
        MemSize::U64 => 8,
    }
}

/// Generate the prototype pc-annotation certificate from zone artifacts.
///
/// v0.1 scope: emit entries for edges shaped as `dst += src` followed by
/// `load [dst + off]`, when zone proves enough packet-end precision.
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

        // Only emit entries that are immediately useful for the load at succ_pc.
        let access_need = -((*off as i64) + mem_size_bytes(*size));
        if target_c > access_need {
            continue;
        }

        by_pc.entry(succ_pc).or_default().push(AnnotationEntry {
            i: dst.idx(),
            j: Reg::AnchorDataEnd.idx(),
            bound: target_c,
            proof: vec![ProofStep::PreStateStep {
                i: dst.idx(),
                j: Reg::AnchorDataEnd.idx(),
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
