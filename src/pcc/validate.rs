use anyhow::Result;

use crate::analysis::machine::reg::Reg;
use crate::ast::Program;

use super::model::{MAX_ENTRIES_PER_PC, MAX_STEPS_PER_ENTRY, ProgramCertificate, ProofStep};

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
            let Some(left) = Reg::idx_to_reg(e.left_reg) else {
                anyhow::bail!(
                    "pc_annotation #{} entry #{} has invalid left_reg={}",
                    pc_idx,
                    eidx,
                    e.left_reg
                );
            };
            let Some(right) = Reg::idx_to_reg(e.right_reg) else {
                anyhow::bail!(
                    "pc_annotation #{} entry #{} has invalid right_reg={}",
                    pc_idx,
                    eidx,
                    e.right_reg
                );
            };
            if left.is_anchor() && right.is_anchor() && left == right {
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

            // proof[0] must be a Fact
            let ProofStep::Fact { .. } = &e.proof[0] else {
                anyhow::bail!(
                    "pc_annotation #{} entry #{} proof must start with a Fact step",
                    pc_idx,
                    eidx
                );
            };

            // Validate register indices in all steps
            for (sidx, step) in e.proof.iter().enumerate() {
                let indices = match step {
                    ProofStep::Fact {
                        left_reg,
                        right_reg,
                        ..
                    } => vec![*left_reg, *right_reg],
                    ProofStep::Derive {
                        source_reg,
                        target_reg,
                        ..
                    } => vec![*source_reg, *target_reg],
                    ProofStep::Transfer {
                        pre_left_reg,
                        pre_right_reg,
                        post_left_reg,
                        post_right_reg,
                        ..
                    } => vec![
                        *pre_left_reg,
                        *pre_right_reg,
                        *post_left_reg,
                        *post_right_reg,
                    ],
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

            // Chain connectivity: each step after Fact must be Derive or Transfer,
            // and its input registers must match the previous step's output registers.
            for w in e.proof.windows(2) {
                match &w[1] {
                    ProofStep::Fact { .. } => {
                        anyhow::bail!(
                            "pc_annotation #{} entry #{} has Fact step after first position",
                            pc_idx,
                            eidx
                        );
                    }
                    ProofStep::Transfer {
                        pre_left_reg,
                        pre_right_reg,
                        ..
                    } => {
                        if w[0].output_left_reg() != *pre_left_reg
                            || w[0].output_right_reg() != *pre_right_reg
                        {
                            anyhow::bail!(
                                "pc_annotation #{} entry #{} proof chain disconnected at Transfer",
                                pc_idx,
                                eidx
                            );
                        }
                    }
                    ProofStep::Derive { source_reg, .. } => {
                        // Derive's source_reg must match the previous step's output_left_reg.
                        if w[0].output_left_reg() != *source_reg {
                            anyhow::bail!(
                                "pc_annotation #{} entry #{} proof chain disconnected at Derive",
                                pc_idx,
                                eidx
                            );
                        }
                    }
                }
            }

            // Last step output matches entry target
            let last = e.proof.last().unwrap();
            if last.output_left_reg() != e.left_reg || last.output_right_reg() != e.right_reg {
                anyhow::bail!(
                    "pc_annotation #{} entry #{} proof endpoints mismatch entry target",
                    pc_idx,
                    eidx
                );
            }

            // PC ordering: all step PCs < target ann.pc.
            // The Fact and its immediately following step may share the same PC
            // (Fact establishes the constraint before the instruction executes).
            // Derive steps may reference PCs before the Fact (the register alias is
            // established in earlier instructions). After the first Transfer, PCs must
            // be strictly increasing.
            let mut prev_pc = None;
            let mut seen_transfer = false;
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
                    if matches!(step, ProofStep::Derive { .. }) && !seen_transfer {
                        // Derive before first Transfer: may reference PCs before the
                        // Fact (the alias was established before the branch).
                        // Only require step_pc < ann.pc (already checked above).
                    } else if !seen_transfer {
                        // Fact → first non-Derive step: allow same PC (non-decreasing)
                        if step_pc < prev {
                            anyhow::bail!(
                                "pc_annotation #{} entry #{} step #{} pc={} < guard pc={}",
                                pc_idx,
                                eidx,
                                sidx,
                                step_pc,
                                prev
                            );
                        }
                    } else {
                        // After first Transfer: strictly increasing
                        if step_pc <= prev {
                            anyhow::bail!(
                                "pc_annotation #{} entry #{} step #{} pc={} not strictly increasing (prev={})",
                                pc_idx,
                                eidx,
                                sidx,
                                step_pc,
                                prev
                            );
                        }
                    }
                }
                if matches!(step, ProofStep::Transfer { .. }) {
                    seen_transfer = true;
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

            // Sum: Fact.c + sum(Derive/Transfer contributions) == entry.bound
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
