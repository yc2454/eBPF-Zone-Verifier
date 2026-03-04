use anyhow::Result;

use crate::analysis::machine::reg::Reg;
use crate::ast::{CmpOp, Instr, Operand, Program, Width};

use super::model::{ObligationKind, ProgramCertificate, ProofStep};

fn checked_sum(weights: impl Iterator<Item = i64>) -> Option<i64> {
    let mut sum = 0i64;
    for w in weights {
        sum = sum.checked_add(w)?;
    }
    Some(sum)
}

/// Structural certificate validation against a concrete program.
///
/// Scope of this phase:
/// - version compatibility;
/// - obligation shape and register-index sanity;
/// - per-kind static constraints (edge form, required fields, allowed ops).
///
/// Non-scope:
/// - no abstract-state-dependent reasoning;
/// - no transfer-equation checking;
/// - no refinement application.
///
/// Those are handled in `checker::apply_certificate_aided_refinement`.
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
        if matches!(ob.kind, ObligationKind::AddRegPacketBound) && ob.succ_pc != ob.pred_pc + 1 {
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
            if matches!(ob.kind, ObligationKind::AddRegPacketBound)
                && matches!(step, ProofStep::GuardStep { .. })
            {
                anyhow::bail!(
                    "obligation #{} step #{} uses unsupported GuardStep",
                    idx,
                    step_idx
                );
            }
        }

        match ob.kind {
            ObligationKind::AddRegPacketBound => {}
            ObligationKind::BranchGuardBound => {
                let Some(branch_taken) = ob.branch_taken else {
                    anyhow::bail!(
                        "obligation #{} missing branch_taken for BranchGuardBound",
                        idx
                    );
                };
                let Instr::If {
                    width,
                    left: _,
                    op,
                    right,
                    target,
                } = prog.instrs[ob.pred_pc]
                else {
                    anyhow::bail!(
                        "obligation #{} BranchGuardBound requires pred instruction to be If",
                        idx
                    );
                };

                let expected_succ = if branch_taken { target } else { ob.pred_pc + 1 };
                if ob.succ_pc != expected_succ {
                    anyhow::bail!(
                        "obligation #{} has succ_pc={} inconsistent with branch_taken={} (expected {})",
                        idx,
                        ob.succ_pc,
                        branch_taken,
                        expected_succ
                    );
                }
                if !matches!(
                    op,
                    CmpOp::ULe
                        | CmpOp::UGe
                        | CmpOp::ULt
                        | CmpOp::UGt
                        | CmpOp::SLe
                        | CmpOp::SGe
                        | CmpOp::SLt
                        | CmpOp::SGt
                ) {
                    anyhow::bail!(
                        "obligation #{} uses unsupported branch op {:?} for BranchGuardBound",
                        idx,
                        op
                    );
                }
                if !matches!(right, Operand::Reg(_)) {
                    anyhow::bail!(
                        "obligation #{} requires register-vs-register branch for BranchGuardBound",
                        idx
                    );
                }
                if !matches!(width, Width::W64) {
                    anyhow::bail!(
                        "obligation #{} requires 64-bit branch width for BranchGuardBound",
                        idx
                    );
                }
                if !ob
                    .proof
                    .iter()
                    .any(|s| matches!(s, ProofStep::GuardStep { .. }))
                {
                    anyhow::bail!(
                        "obligation #{} BranchGuardBound requires at least one GuardStep",
                        idx
                    );
                }
            }
        }
    }
    Ok(())
}
