use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;
use std::hash::{Hash, Hasher};

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, Instr, MemSize, Operand, Program};
use crate::domains::dbm::{Dbm, INF};
use crate::domains::interval::IntervalState;
use crate::domains::numeric::NumericDomain;

/// Top-level PCC certificate container.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ProgramCertificate {
    pub version: u32,
    pub program_hash: String,
    pub obligations: Vec<EdgeObligation>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct EdgeObligation {
    pub pred_pc: usize,
    pub succ_pc: usize,
    pub pred_fingerprint: u64,
    pub target: Constraint,
    pub proof: Vec<ProofStep>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Constraint {
    pub i: usize,
    pub j: usize,
    pub c: i64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum ProofSource {
    Guard,
    PreState,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ProofStep {
    pub from: usize,
    pub to: usize,
    pub weight: i64,
    pub source: ProofSource,
}

impl ProgramCertificate {
    #[allow(dead_code)]
    pub const VERSION_V1: u32 = 1;

    #[allow(dead_code)]
    pub fn empty(program_hash: String) -> Self {
        Self {
            version: Self::VERSION_V1,
            program_hash,
            obligations: Vec::new(),
        }
    }

    pub fn load_from_path(path: &str) -> Result<Self> {
        let raw = fs::read_to_string(path)
            .with_context(|| format!("failed to read certificate file '{}'", path))?;
        serde_json::from_str(&raw)
            .with_context(|| format!("failed to parse certificate JSON '{}'", path))
    }

    #[allow(dead_code)]
    pub fn save_to_path(&self, path: &str) -> Result<()> {
        let raw =
            serde_json::to_string_pretty(self).context("failed to serialize certificate JSON")?;
        fs::write(path, raw).with_context(|| format!("failed to write certificate file '{}'", path))
    }
}

/// Validates certificate structure against the current program for the v1 checker.
///
/// This is a structural gate, not a semantic proof. Semantic proof still happens
/// per edge during certificate-aided refinement.
pub fn validate_certificate_for_program(cert: &ProgramCertificate, prog: &Program) -> Result<()> {
    if cert.version != ProgramCertificate::VERSION_V1 {
        anyhow::bail!(
            "unsupported certificate version {} (expected {})",
            cert.version,
            ProgramCertificate::VERSION_V1
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
        if ob.proof[0].from != ob.target.i || ob.proof[ob.proof.len() - 1].to != ob.target.j {
            anyhow::bail!(
                "obligation #{} proof endpoints do not match target ({} -> {})",
                idx,
                ob.target.i,
                ob.target.j
            );
        }
        for w in ob.proof.windows(2) {
            if w[0].to != w[1].from {
                anyhow::bail!(
                    "obligation #{} proof chain is disconnected at {} -> {}",
                    idx,
                    w[0].to,
                    w[1].from
                );
            }
        }
        let Some(_sum) = checked_sum(ob.proof.iter().map(|s| s.weight)) else {
            anyhow::bail!("obligation #{} proof weight sum overflows i64", idx);
        };
        for (step_idx, step) in ob.proof.iter().enumerate() {
            if Reg::idx_to_reg(step.from).is_none() || Reg::idx_to_reg(step.to).is_none() {
                anyhow::bail!(
                    "obligation #{} step #{} uses invalid register indices {} -> {}",
                    idx,
                    step_idx,
                    step.from,
                    step.to
                );
            }
            if !matches!(step.source, ProofSource::PreState) {
                anyhow::bail!(
                    "obligation #{} step #{} uses unsupported proof source {:?}",
                    idx,
                    step_idx,
                    step.source
                );
            }
        }
    }
    Ok(())
}

pub fn program_hash(prog: &Program) -> String {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    prog.instrs.len().hash(&mut hasher);
    for insn in &prog.instrs {
        format!("{insn:?}").hash(&mut hasher);
    }
    let mut invalid: Vec<usize> = prog.invalid_pc_set.iter().copied().collect();
    invalid.sort_unstable();
    invalid.hash(&mut hasher);
    format!("{:016x}", hasher.finish())
}

fn mem_size_bytes(sz: MemSize) -> i64 {
    match sz {
        MemSize::U8 => 1,
        MemSize::U16 => 2,
        MemSize::U32 => 4,
        MemSize::U64 => 8,
    }
}

fn hash_v1_pred_context(
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

fn compute_v1_pred_fingerprint_from_interval(
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
                ProofStep {
                    from: dst.idx(),
                    to: Reg::AnchorData.idx(),
                    weight: d_dst_data,
                    source: ProofSource::PreState,
                },
                ProofStep {
                    from: Reg::AnchorData.idx(),
                    to: Reg::AnchorDataEnd.idx(),
                    weight: d_data_end,
                    source: ProofSource::PreState,
                },
            ],
        });
    }
    out
}

fn checked_sum(weights: impl Iterator<Item = i64>) -> Option<i64> {
    let mut sum = 0i64;
    for w in weights {
        sum = sum.checked_add(w)?;
    }
    Some(sum)
}

fn prestate_bound(ivl: &IntervalState, i: Reg, j: Reg) -> Option<i64> {
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

fn apply_add_reg_transfer_to_bound(
    pre_state: &State,
    pred_instr: &Instr,
    i: Reg,
    j: Reg,
    pre_bound: i64,
) -> Option<i64> {
    match pred_instr {
        Instr::Alu {
            op: AluOp::Add,
            dst,
            src: Operand::Reg(src),
            ..
        } => {
            if *dst == i {
                let src_umax = pre_state.domain.as_interval()?.get_bounds(*src).umax as i64;
                pre_bound.checked_add(src_umax)
            } else if *dst == j {
                let src_umin = pre_state.domain.as_interval()?.get_bounds(*src).umin as i64;
                pre_bound.checked_sub(src_umin)
            } else {
                Some(pre_bound)
            }
        }
        _ => Some(pre_bound),
    }
}

fn apply_verified_packet_end_fact(succ_state: &mut State, target: &Constraint) {
    let Some(i) = Reg::idx_to_reg(target.i) else {
        return;
    };
    let Some(j) = Reg::idx_to_reg(target.j) else {
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
    // From i - @data_end <= c  ==>  @data_end - i >= -c.
    let proven_end_from_i = (-target.c).max(0);
    let proven_range = proven_end_from_i.saturating_sub(po.off);
    let reg = ivl.get_mut(i);
    if let Some(ref mut ptr_off) = reg.ptr_offset {
        ptr_off.range = Some(ptr_off.range.unwrap_or(proven_range).max(proven_range));
    }
}

/// Applies certificate-aided refinement on a single CFG edge.
///
/// This function is called after transfer creates a successor state. It verifies
/// all matching edge obligations against the predecessor state + instruction
/// semantics, and applies only the narrow packet-range refinement when proofs
/// are valid.
///
/// Fail-closed behavior:
/// - Any malformed or unsupported obligation is ignored.
/// - Analysis continues with baseline semantics.
pub fn apply_certificate_aided_refinement(
    cert: &ProgramCertificate,
    pre_state: &State,
    pred_instr: &Instr,
    succ_state: &mut State,
) {
    // v1 checker only runs in interval mode.
    if !matches!(succ_state.domain, NumericDomain::Interval(_)) {
        return;
    }
    for ob in &cert.obligations {
        if ob.pred_pc != pre_state.pc || ob.succ_pc != succ_state.pc {
            continue;
        }
        let Some(pre_fp) = compute_v1_pred_fingerprint_from_interval(pre_state, pred_instr, ob)
        else {
            continue;
        };
        if ob.pred_fingerprint != pre_fp {
            continue;
        }
        let Some(i) = Reg::idx_to_reg(ob.target.i) else {
            continue;
        };
        let Some(j) = Reg::idx_to_reg(ob.target.j) else {
            continue;
        };
        if ob.proof.is_empty() {
            continue;
        }
        // Check chain shape.
        if ob.proof[0].from != ob.target.i || ob.proof[ob.proof.len() - 1].to != ob.target.j {
            continue;
        }
        let mut chain_ok = true;
        for w in ob.proof.windows(2) {
            if w[0].to != w[1].from {
                chain_ok = false;
                break;
            }
        }
        if !chain_ok {
            continue;
        }

        // Validate each step against predecessor state facts.
        let Some(ivl) = pre_state.domain.as_interval() else {
            continue;
        };
        let mut all_steps_ok = true;
        for step in &ob.proof {
            match step.source {
                ProofSource::PreState => {
                    let Some(from) = Reg::idx_to_reg(step.from) else {
                        all_steps_ok = false;
                        break;
                    };
                    let Some(to) = Reg::idx_to_reg(step.to) else {
                        all_steps_ok = false;
                        break;
                    };
                    let Some(actual) = prestate_bound(ivl, from, to) else {
                        all_steps_ok = false;
                        break;
                    };
                    if actual > step.weight {
                        all_steps_ok = false;
                        break;
                    }
                }
                ProofSource::Guard => {
                    // Guard-based proofs are not enabled in v1 checker.
                    all_steps_ok = false;
                    break;
                }
            }
        }
        if !all_steps_ok {
            continue;
        }

        let Some(pre_sum) = checked_sum(ob.proof.iter().map(|s| s.weight)) else {
            continue;
        };
        let Some(post_bound) =
            apply_add_reg_transfer_to_bound(pre_state, pred_instr, i, j, pre_sum)
        else {
            continue;
        };
        if post_bound != ob.target.c {
            continue;
        }
        apply_verified_packet_end_fact(succ_state, &ob.target);
    }
}
