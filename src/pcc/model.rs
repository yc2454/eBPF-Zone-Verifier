use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;

/// Top-level PCC certificate container for the prototype pipeline.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ProgramCertificate {
    pub version: u32,
    pub program_hash: String,
    #[serde(default)]
    pub pc_annotations: Vec<PcAnnotation>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct PcAnnotation {
    pub pc: usize,
    pub entries: Vec<AnnotationEntry>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct AnnotationEntry {
    pub i: usize,
    pub j: usize,
    pub bound: i64,
    pub proof: Vec<ProofStep>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind")]
pub enum ProofStep {
    /// Base fact: the interval state at `pc` proves `i - j <= c`.
    /// Placed at the divergence point where zone and interval agree.
    #[serde(rename = "Guard")]
    Guard {
        pc: usize,
        i: usize,
        j: usize,
        c: i64,
    },
    /// Transfer: if `from_i - from_j <= b` before instruction at `pc`,
    /// then `to_i - to_j <= b + delta` after that instruction.
    #[serde(rename = "Transfer")]
    Transfer {
        pc: usize,
        from_i: usize,
        from_j: usize,
        to_i: usize,
        to_j: usize,
        delta: i64,
    },
}

impl ProofStep {
    /// The PC this step refers to.
    pub fn pc(&self) -> usize {
        match self {
            ProofStep::Guard { pc, .. } | ProofStep::Transfer { pc, .. } => *pc,
        }
    }

    /// The output register index `i` after this step.
    /// Guard: `i`; Transfer: `to_i`.
    pub fn output_i(&self) -> usize {
        match self {
            ProofStep::Guard { i, .. } => *i,
            ProofStep::Transfer { to_i, .. } => *to_i,
        }
    }

    /// The output register index `j` after this step.
    /// Guard: `j`; Transfer: `to_j`.
    pub fn output_j(&self) -> usize {
        match self {
            ProofStep::Guard { j, .. } => *j,
            ProofStep::Transfer { to_j, .. } => *to_j,
        }
    }

    /// The bound contribution of this step.
    /// Guard: `c`; Transfer: `delta`.
    pub fn bound_contribution(&self) -> i64 {
        match self {
            ProofStep::Guard { c, .. } => *c,
            ProofStep::Transfer { delta, .. } => *delta,
        }
    }
}

/// Maximum proof steps allowed per annotation entry.
/// Shared between the validator and checker to ensure they agree.
pub const MAX_STEPS_PER_ENTRY: usize = 16;

/// Maximum annotation entries allowed per PC.
/// Enforced by the validator; checker iterates all entries that pass validation.
pub const MAX_ENTRIES_PER_PC: usize = 8;

/// Overflow-safe sum of step bounds.
#[allow(dead_code)]
pub fn checked_sum(weights: impl Iterator<Item = i64>) -> Option<i64> {
    let mut sum = 0i64;
    for w in weights {
        sum = sum.checked_add(w)?;
    }
    Some(sum)
}

impl ProgramCertificate {
    /// Prototype certificate schema version.
    pub const VERSION: u32 = 2;

    #[allow(dead_code)]
    pub fn empty(program_hash: String) -> Self {
        Self {
            version: Self::VERSION,
            program_hash,
            pc_annotations: Vec::new(),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_step_guard_json_round_trip() {
        let step = ProofStep::Guard {
            pc: 5,
            i: 6,
            j: 14,
            c: -8,
        };
        let json = serde_json::to_string(&step).unwrap();
        assert!(json.contains("\"kind\":\"Guard\""));
        assert!(json.contains("\"pc\":5"));
        let back: ProofStep = serde_json::from_str(&json).unwrap();
        assert_eq!(step, back);
    }

    #[test]
    fn proof_step_transfer_json_round_trip() {
        let step = ProofStep::Transfer {
            pc: 9,
            from_i: 6,
            from_j: 14,
            to_i: 6,
            to_j: 14,
            delta: 3,
        };
        let json = serde_json::to_string(&step).unwrap();
        assert!(json.contains("\"kind\":\"Transfer\""));
        assert!(json.contains("\"from_i\":6"));
        assert!(json.contains("\"delta\":3"));
        let back: ProofStep = serde_json::from_str(&json).unwrap();
        assert_eq!(step, back);
    }

    #[test]
    fn certificate_v2_round_trip() {
        let cert = ProgramCertificate {
            version: 2,
            program_hash: "abc123".to_string(),
            pc_annotations: vec![PcAnnotation {
                pc: 10,
                entries: vec![AnnotationEntry {
                    i: 6,
                    j: 14,
                    bound: -5,
                    proof: vec![
                        ProofStep::Guard {
                            pc: 5,
                            i: 6,
                            j: 14,
                            c: -8,
                        },
                        ProofStep::Transfer {
                            pc: 9,
                            from_i: 6,
                            from_j: 14,
                            to_i: 6,
                            to_j: 14,
                            delta: 3,
                        },
                    ],
                }],
            }],
        };
        let json = serde_json::to_string_pretty(&cert).unwrap();
        let back: ProgramCertificate = serde_json::from_str(&json).unwrap();
        assert_eq!(cert, back);
    }

    #[test]
    fn proof_step_accessors() {
        let guard = ProofStep::Guard {
            pc: 5,
            i: 6,
            j: 14,
            c: -8,
        };
        assert_eq!(guard.pc(), 5);
        assert_eq!(guard.output_i(), 6);
        assert_eq!(guard.output_j(), 14);
        assert_eq!(guard.bound_contribution(), -8);

        let transfer = ProofStep::Transfer {
            pc: 9,
            from_i: 5,
            from_j: 14,
            to_i: 6,
            to_j: 14,
            delta: 3,
        };
        assert_eq!(transfer.pc(), 9);
        assert_eq!(transfer.output_i(), 6);
        assert_eq!(transfer.output_j(), 14);
        assert_eq!(transfer.bound_contribution(), 3);
    }
}
