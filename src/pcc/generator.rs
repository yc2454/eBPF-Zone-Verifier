use std::collections::BTreeMap;

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, Instr, MemSize, Operand, Program};
use crate::domains::dbm::{Dbm, INF};
use log::debug;

use super::checker::distance_upper_bound;
use super::model::{AnnotationEntry, PcAnnotation, ProgramCertificate, ProofStep};
use super::program_hash;

// ---------------------------------------------------------------------------
// Bound-query helpers (Step 5)
// ---------------------------------------------------------------------------

/// For a Load instruction, returns (base_reg, offset, size_bytes, required_bound) where
/// required_bound = -(off + size). The access is safe iff
/// base - @data_end <= required_bound.
fn required_access_bound(instr: &Instr) -> Option<(Reg, i16, MemSize, i64)> {
    let Instr::Load { size, base, off, .. } = instr else {
        return None;
    };
    Some((*base, *off, *size, -((*off as i64) + size.bytes() as i64)))
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
// Backward tracing (Step 6)
// ---------------------------------------------------------------------------

/// A backward-traced step before it is reversed into the forward chain.
struct BackwardStep {
    pc: usize,
    from_i: usize,
    from_j: usize,
    to_i: usize,
    to_j: usize,
    delta: i64,
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
        let (prev_i, prev_j, delta) = backward_transfer(instr, cur_i, cur_j, zone_dbms, pc)?;
        let pre_bound = cur_bound.checked_sub(delta)?;

        // Record this as a backward step (instruction transforms constraint).
        backward_steps.push(BackwardStep {
            pc,
            from_i: prev_i.idx(),
            from_j: prev_j.idx(),
            to_i: cur_i.idx(),
            to_j: cur_j.idx(),
            delta,
        });

        // Now check: does the interval agree on the PRE-instruction constraint?
        // The Guard checks the constraint at the pre-state of this PC.
        if pc < interval_states.len() {
            if let Some(ivl_ub) = interval_upper_bound(&interval_states[pc], prev_i, prev_j) {
                if ivl_ub <= pre_bound {
                    // Divergence point found: interval agrees on the pre-instruction
                    // constraint at this PC.
                    let guard_c = ivl_ub;
                    let mut proof = Vec::with_capacity(1 + backward_steps.len());
                    proof.push(ProofStep::Guard {
                        pc,
                        i: prev_i.idx(),
                        j: prev_j.idx(),
                        c: guard_c,
                    });

                    // Reverse backward steps into forward order as Transfer steps
                    for bs in backward_steps.into_iter().rev() {
                        proof.push(ProofStep::Transfer {
                            pc: bs.pc,
                            from_i: bs.from_i,
                            from_j: bs.from_j,
                            to_i: bs.to_i,
                            to_j: bs.to_j,
                            delta: bs.delta,
                        });
                    }

                    return Some((pc, prev_i.idx(), prev_j.idx(), guard_c, proof));
                }
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
/// Given the post-instruction constraint `(cur_i, cur_j)`, returns
/// `(prev_i, prev_j, delta)` where the pre-instruction constraint is
/// `(prev_i, prev_j)` and `delta` is the forward bound shift.
///
/// Returns None for unsupported instructions that write to tracked registers.
fn backward_transfer(
    instr: &Instr,
    cur_i: Reg,
    cur_j: Reg,
    zone_dbms: &[Dbm],
    pc: usize,
) -> Option<(Reg, Reg, i64)> {
    match instr {
        // mov dst, src: after mov, dst has src's value.
        // If cur_i == dst, then before the mov the value was in src.
        Instr::Alu {
            op: AluOp::Mov,
            dst,
            src: Operand::Reg(src),
            ..
        } => {
            let prev_i = if cur_i == *dst { *src } else { cur_i };
            let prev_j = if cur_j == *dst { *src } else { cur_j };
            Some((prev_i, prev_j, 0))
        }

        // add dst, imm: after add, dst = dst_old + imm.
        // If cur_i == dst: bound shifted by +imm forward, so delta = imm.
        // Before: prev_i = dst (same register), bound was tighter by imm.
        Instr::Alu {
            op: AluOp::Add,
            dst,
            src: Operand::Imm(imm),
            ..
        } => {
            if *dst == cur_i {
                Some((cur_i, cur_j, *imm))
            } else if *dst == cur_j {
                Some((cur_i, cur_j, -(*imm)))
            } else {
                // Passthrough
                Some((cur_i, cur_j, 0))
            }
        }

        // add dst, src_reg: after add, dst = dst_old + src_reg.
        // delta = ub(src_reg) from the zone DBM at this PC.
        Instr::Alu {
            op: AluOp::Add,
            dst,
            src: Operand::Reg(src),
            ..
        } => {
            if *dst == cur_i {
                let dbm = zone_dbms.get(pc)?;
                let src_ub = zone_upper_bound(dbm, *src, Reg::Zero)?;
                Some((cur_i, cur_j, src_ub))
            } else if *dst == cur_j {
                let dbm = zone_dbms.get(pc)?;
                let src_lb = {
                    // lb(src) = -ub(Zero - src) = -dbm[Zero][src]
                    let neg_lb = zone_upper_bound(dbm, Reg::Zero, *src)?;
                    -neg_lb
                };
                Some((cur_i, cur_j, -src_lb))
            } else {
                Some((cur_i, cur_j, 0))
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
                // Passthrough
                Some((cur_i, cur_j, 0))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Certificate generation entry point
// ---------------------------------------------------------------------------

/// Generate a v2 certificate using backward tracing from zone analysis.
///
/// For each candidate load instruction, traces backward to the divergence
/// point where zone and interval first disagree, emitting a proof chain
/// of [Guard, Transfer, ..., Transfer].
pub fn generate_certificate(
    prog: &Program,
    zone_dbms: &[Dbm],
    interval_states: &[State],
) -> ProgramCertificate {
    let mut cert = ProgramCertificate::empty(program_hash(prog));
    if prog.instrs.is_empty() {
        return cert;
    }

    let mut by_pc: BTreeMap<usize, Vec<AnnotationEntry>> = BTreeMap::new();

    for target_pc in 0..prog.instrs.len() {
        let instr = &prog.instrs[target_pc];
        let Some((base, off, size, required)) = required_access_bound(instr) else {
            continue;
        };

        // Query zone: does the zone prove the access is safe?
        // Use the DBM at the target PC (the pre-state just before the load executes).
        let Some(dbm) = zone_dbms.get(target_pc) else {
            continue;
        };
        let Some(zone_ub) = zone_upper_bound(dbm, base, Reg::AnchorDataEnd) else {
            continue;
        };
        if zone_ub > required {
            continue; // zone doesn't prove it
        }

        // Query interval: does the interval verifier already prove it?
        // Use the actual verify_packet_bounds check (not distance_upper_bound,
        // which can be tighter than what the verifier uses).
        if target_pc < interval_states.len() {
            let (start_ok, end_ok) = interval_states[target_pc]
                .domain
                .verify_packet_bounds(base, off as i64, size.bytes() as i64);
            if start_ok && end_ok {
                continue; // interval already sufficient, no PCC needed
            }
        }

        debug!(
            target: "pcc-gen",
            "[PCC-GEN] target={}: candidate load {} + {} (zone_ub={}, required={})",
            target_pc, base.name(), required, zone_ub, required,
        );

        // Backward trace to find the divergence point.
        let Some((_, _, _, _, proof)) = backward_trace(
            prog,
            zone_dbms,
            interval_states,
            target_pc,
            base,
            Reg::AnchorDataEnd,
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
            i: base.idx(),
            j: Reg::AnchorDataEnd.idx(),
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

/// Legacy v1 generator — kept for backward compatibility during migration.
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
            i: dst.idx(),
            j: Reg::AnchorDataEnd.idx(),
            bound: target_c,
            proof: vec![ProofStep::Guard {
                pc: pred_pc,
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
