use anyhow::Result;

use crate::analysis::machine::reg::Reg;
use crate::ast::Program;

use super::model::{ProgramCertificate, ProofStep};

const MAX_STEPS_PER_ENTRY: usize = 3;
const MAX_ENTRIES_PER_PC: usize = 8;

fn checked_sum(weights: impl Iterator<Item = i64>) -> Option<i64> {
    let mut sum = 0i64;
    for w in weights {
        sum = sum.checked_add(w)?;
    }
    Some(sum)
}

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
            if e.proof[0].i() != e.i || e.proof[e.proof.len() - 1].j() != e.j {
                anyhow::bail!(
                    "pc_annotation #{} entry #{} proof endpoints mismatch entry target",
                    pc_idx,
                    eidx
                );
            }
            for w in e.proof.windows(2) {
                if w[0].j() != w[1].i() {
                    anyhow::bail!(
                        "pc_annotation #{} entry #{} proof chain disconnected at {} -> {}",
                        pc_idx,
                        eidx,
                        w[0].j(),
                        w[1].i()
                    );
                }
            }
            let Some(_sum) = checked_sum(e.proof.iter().map(ProofStep::c)) else {
                anyhow::bail!(
                    "pc_annotation #{} entry #{} proof weight sum overflows i64",
                    pc_idx,
                    eidx
                );
            };
        }
    }

    Ok(())
}
