use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;
use std::hash::{Hash, Hasher};

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, Instr, MemSize, Operand, Program};
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

/// v1 producer for a single motivating pattern.
pub fn generate_v1_obligations_for_program(prog: &Program) -> Vec<EdgeObligation> {
    // Match the motivating shape:
    // pc9:  r5 += r4
    // pc10: *(u32 *)(r5 + 0)
    if prog.instrs.len() <= 10 {
        return Vec::new();
    }
    let Some(Instr::Alu {
        op: AluOp::Add,
        dst,
        src,
        ..
    }) = prog.instrs.get(9)
    else {
        return Vec::new();
    };
    let Some(Instr::Load {
        size: MemSize::U32,
        base,
        off: 0,
        ..
    }) = prog.instrs.get(10)
    else {
        return Vec::new();
    };
    let Operand::Reg(src_reg) = src else {
        return Vec::new();
    };
    if *dst != Reg::R5 || *src_reg != Reg::R4 || *base != Reg::R5 {
        return Vec::new();
    }

    // Pre-state chain:
    // r5 - @data <= 0
    // @data - @data_end <= -8
    // pre-sum => r5 - @data_end <= -8
    // transfer through r5 += r4 with umax(r4)=3 => post <= -5
    vec![EdgeObligation {
        pred_pc: 9,
        succ_pc: 10,
        pred_fingerprint: 0, // wildcard for v1
        target: Constraint {
            i: Reg::R5.idx(),
            j: Reg::AnchorDataEnd.idx(),
            c: -5,
        },
        proof: vec![
            ProofStep {
                from: Reg::R5.idx(),
                to: Reg::AnchorData.idx(),
                weight: 0,
                source: ProofSource::PreState,
            },
            ProofStep {
                from: Reg::AnchorData.idx(),
                to: Reg::AnchorDataEnd.idx(),
                weight: -8,
                source: ProofSource::PreState,
            },
        ],
    }]
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
    let pre_fp = state_fingerprint(pre_state);

    for ob in &cert.obligations {
        if ob.pred_pc != pre_state.pc || ob.succ_pc != succ_state.pc {
            continue;
        }
        if ob.pred_fingerprint != 0 && ob.pred_fingerprint != pre_fp {
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

pub fn state_fingerprint(state: &State) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    state.pc.hash(&mut hasher);
    for reg in Reg::ALL {
        format!("{:?}", state.types.get(reg)).hash(&mut hasher);
        format!("{:?}", state.get_tnum(reg)).hash(&mut hasher);
        let (lo, hi) = state.domain.get_interval(reg);
        lo.hash(&mut hasher);
        hi.hash(&mut hasher);
    }
    if let Some(ivl) = state.domain.as_interval() {
        for reg in Reg::ALL {
            if let Some(po) = ivl.get_ptr_offset(reg) {
                reg.idx().hash(&mut hasher);
                po.anchor.idx().hash(&mut hasher);
                po.off.hash(&mut hasher);
                po.var_off.hash(&mut hasher);
                po.range.hash(&mut hasher);
            }
        }
        ivl.get_packet_size_bound().hash(&mut hasher);
        ivl.get_meta_size_bound().hash(&mut hasher);
    }
    hasher.finish()
}
