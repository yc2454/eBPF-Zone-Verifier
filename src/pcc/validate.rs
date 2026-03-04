use anyhow::Result;

use crate::analysis::machine::reg::Reg;
use crate::ast::Program;

use super::model::{ObligationKind, ProgramCertificate, ProofStep};

fn checked_sum(weights: impl Iterator<Item = i64>) -> Option<i64> {
    let mut sum = 0i64;
    for w in weights {
        sum = sum.checked_add(w)?;
    }
    Some(sum)
}

/// Validates certificate structure against the current program.
///
/// This is a structural gate, not a semantic proof. Semantic proof still happens
/// per edge during certificate-aided refinement.
pub fn validate_certificate_for_program(cert: &ProgramCertificate, prog: &Program) -> Result<()> {
    if cert.version != ProgramCertificate::VERSION_V1
        && cert.version != ProgramCertificate::VERSION_V2
    {
        anyhow::bail!(
            "unsupported certificate version {} (expected {} or {})",
            cert.version,
            ProgramCertificate::VERSION_V1,
            ProgramCertificate::VERSION_V2
        );
    }

    for (idx, ob) in cert.obligations.iter().enumerate() {
        if !matches!(ob.kind, ObligationKind::AddRegPacketBound) {
            anyhow::bail!("obligation #{} has unsupported kind {:?}", idx, ob.kind);
        }
        if ob.pred_pc >= prog.instrs.len() {
            anyhow::bail!(
                "obligation #{} has pred_pc={} out of bounds (program len={})",
                idx,
                ob.pred_pc,
                prog.instrs.len()
            );
        }
        if ob.succ_pc >= prog.instrs.len() {
            anyhow::bail!(
                "obligation #{} has succ_pc={} out of bounds (program len={})",
                idx,
                ob.succ_pc,
                prog.instrs.len()
            );
        }
        if ob.succ_pc != ob.pred_pc + 1 {
            anyhow::bail!(
                "obligation #{} has unsupported non-fallthrough edge {} -> {}",
                idx,
                ob.pred_pc,
                ob.succ_pc
            );
        }
        let Some(i) = Reg::idx_to_reg(ob.target.i) else {
            anyhow::bail!(
                "obligation #{} has invalid target.i register index {}",
                idx,
                ob.target.i
            );
        };
        let Some(j) = Reg::idx_to_reg(ob.target.j) else {
            anyhow::bail!(
                "obligation #{} has invalid target.j register index {}",
                idx,
                ob.target.j
            );
        };
        if j != Reg::AnchorDataEnd {
            anyhow::bail!(
                "obligation #{} has unsupported target anchor {:?} (only @data_end supported)",
                idx,
                j
            );
        }
        if i.is_anchor() {
            anyhow::bail!(
                "obligation #{} has unsupported target register {:?} (anchor cannot be lhs)",
                idx,
                i
            );
        }
        if ob.proof.is_empty() {
            anyhow::bail!("obligation #{} has empty proof", idx);
        }
        if ob.proof[0].i() != ob.target.i || ob.proof[ob.proof.len() - 1].j() != ob.target.j {
            anyhow::bail!(
                "obligation #{} proof endpoints do not match target ({} -> {})",
                idx,
                ob.target.i,
                ob.target.j
            );
        }
        for w in ob.proof.windows(2) {
            if w[0].j() != w[1].i() {
                anyhow::bail!(
                    "obligation #{} proof chain is disconnected at {} -> {}",
                    idx,
                    w[0].j(),
                    w[1].i()
                );
            }
        }
        let Some(_sum) = checked_sum(ob.proof.iter().map(ProofStep::c)) else {
            anyhow::bail!("obligation #{} proof weight sum overflows i64", idx);
        };
        for (step_idx, step) in ob.proof.iter().enumerate() {
            if Reg::idx_to_reg(step.i()).is_none() || Reg::idx_to_reg(step.j()).is_none() {
                anyhow::bail!(
                    "obligation #{} step #{} uses invalid register indices {} -> {}",
                    idx,
                    step_idx,
                    step.i(),
                    step.j()
                );
            }
            if matches!(step, ProofStep::GuardStep { .. }) {
                anyhow::bail!(
                    "obligation #{} step #{} uses unsupported GuardStep",
                    idx,
                    step_idx
                );
            }
        }
    }
    Ok(())
}
