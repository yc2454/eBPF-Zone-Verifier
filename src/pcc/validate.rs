use anyhow::Result;

use crate::analysis::machine::reg::Reg;
use crate::ast::Program;

use super::model::{
    ProgramCertificate, ProofStep, MAX_ENTRIES_PER_PC, MAX_STEPS_PER_ENTRY,
};

/// Structural validation for the prototype pc-annotation certificate schema.
pub fn validate_certificate_for_program(cert: &ProgramCertificate, prog: &Program) -> Result<()> {
    if cert.version != ProgramCertificate::VERSION {
        anyhow::bail!(
            "unsupported certificate version {} (expected {})",
            cert.version,
            ProgramCertificate::VERSION
        );
    }

    for (pc_idx, ann) in cert.pc_annotations.iter().enumerate() {
        if ann.pc >= prog.instrs.len() {
            anyhow::bail!(
                "pc_annotation #{} has pc={} out of bounds (program len={})",
                pc_idx,
                ann.pc,
                prog.instrs.len()
            );
        }
        if ann.entries.len() > MAX_ENTRIES_PER_PC {
            anyhow::bail!(
                "pc_annotation #{} exceeds max entries per pc ({} > {})",
                pc_idx,
                ann.entries.len(),
                MAX_ENTRIES_PER_PC
            );
        }
        for (eidx, e) in ann.entries.iter().enumerate() {
            let Some(i) = Reg::idx_to_reg(e.i) else {
                anyhow::bail!(
                    "pc_annotation #{} entry #{} has invalid i={}",
                    pc_idx,
                    eidx,
                    e.i
                );
            };
            let Some(j) = Reg::idx_to_reg(e.j) else {
                anyhow::bail!(
                    "pc_annotation #{} entry #{} has invalid j={}",
                    pc_idx,
                    eidx,
                    e.j
                );
            };
            if i.is_anchor() && j.is_anchor() && i == j {
                anyhow::bail!(
                    "pc_annotation #{} entry #{} is degenerate anchor constraint",
                    pc_idx,
                    eidx
                );
            }
            if e.proof.is_empty() {
                anyhow::bail!("pc_annotation #{} entry #{} has empty proof", pc_idx, eidx);
            }
            if e.proof.len() > MAX_STEPS_PER_ENTRY {
                anyhow::bail!(
                    "pc_annotation #{} entry #{} exceeds max steps ({} > {})",
                    pc_idx,
                    eidx,
                    e.proof.len(),
                    MAX_STEPS_PER_ENTRY
                );
            }

            // proof[0] must be a Guard
            let ProofStep::Guard { .. } = &e.proof[0] else {
                anyhow::bail!(
                    "pc_annotation #{} entry #{} proof must start with a Guard step",
                    pc_idx,
                    eidx
                );
            };

            // Validate register indices in all steps
            for (sidx, step) in e.proof.iter().enumerate() {
                let indices = match step {
                    ProofStep::Guard { i, j, .. } => vec![*i, *j],
                    ProofStep::Transfer {
                        from_i,
                        from_j,
                        to_i,
                        to_j,
                        ..
                    } => vec![*from_i, *from_j, *to_i, *to_j],
                };
                for idx in indices {
                    if Reg::idx_to_reg(idx).is_none() {
                        anyhow::bail!(
                            "pc_annotation #{} entry #{} step #{} has invalid register index {}",
                            pc_idx,
                            eidx,
                            sidx,
                            idx
                        );
                    }
                }
            }

            // Chain connectivity: Transfer[k].from == prev.output
            for w in e.proof.windows(2) {
                let ProofStep::Transfer { from_i, from_j, .. } = &w[1] else {
                    anyhow::bail!(
                        "pc_annotation #{} entry #{} has non-Transfer step after Guard",
                        pc_idx,
                        eidx
                    );
                };
                if w[0].output_i() != *from_i || w[0].output_j() != *from_j {
                    anyhow::bail!(
                        "pc_annotation #{} entry #{} proof chain disconnected",
                        pc_idx,
                        eidx
                    );
                }
            }

            // Last step output matches entry target
            let last = e.proof.last().unwrap();
            if last.output_i() != e.i || last.output_j() != e.j {
                anyhow::bail!(
                    "pc_annotation #{} entry #{} proof endpoints mismatch entry target",
                    pc_idx,
                    eidx
                );
            }

            // PC monotonicity: non-decreasing, all < ann.pc.
            // The Guard and its immediately following Transfer may share the same PC
            // (Guard establishes the fact before the instruction; Transfer processes it).
            // After the first Transfer, PCs must be strictly increasing.
            let mut prev_pc = None;
            for (sidx, step) in e.proof.iter().enumerate() {
                let step_pc = step.pc();
                if step_pc >= ann.pc {
                    anyhow::bail!(
                        "pc_annotation #{} entry #{} step #{} pc={} >= target pc={}",
                        pc_idx,
                        eidx,
                        sidx,
                        step_pc,
                        ann.pc
                    );
                }
                if let Some(prev) = prev_pc {
                    if sidx == 1 {
                        // Guard → first Transfer: allow same PC (non-decreasing)
                        if step_pc < prev {
                            anyhow::bail!(
                                "pc_annotation #{} entry #{} step #{} pc={} < guard pc={}",
                                pc_idx, eidx, sidx, step_pc, prev
                            );
                        }
                    } else {
                        // Transfer → Transfer: strictly increasing
                        if step_pc <= prev {
                            anyhow::bail!(
                                "pc_annotation #{} entry #{} step #{} pc={} not strictly increasing (prev={})",
                                pc_idx, eidx, sidx, step_pc, prev
                            );
                        }
                    }
                }
                prev_pc = Some(step_pc);
            }

            // Step PCs must be in program bounds
            for (sidx, step) in e.proof.iter().enumerate() {
                if step.pc() >= prog.instrs.len() {
                    anyhow::bail!(
                        "pc_annotation #{} entry #{} step #{} pc={} out of bounds",
                        pc_idx,
                        eidx,
                        sidx,
                        step.pc()
                    );
                }
            }

            // Sum: Guard.c + sum(Transfer.delta) == entry.bound
            let mut sum = 0i64;
            for step in &e.proof {
                sum = match sum.checked_add(step.bound_contribution()) {
                    Some(s) => s,
                    None => anyhow::bail!(
                        "pc_annotation #{} entry #{} proof weight sum overflows i64",
                        pc_idx,
                        eidx
                    ),
                };
            }
        }
    }

    Ok(())
}
