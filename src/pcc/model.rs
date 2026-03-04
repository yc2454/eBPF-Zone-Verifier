use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;

/// Top-level PCC certificate container.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ProgramCertificate {
    pub version: u32,
    pub program_hash: String,
    pub obligations: Vec<EdgeObligation>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct EdgeObligation {
    /// Explicit typed semantics for checker dispatch in v2+.
    #[serde(default)]
    pub kind: ObligationKind,
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
#[serde(tag = "kind")]
pub enum ProofStep {
    #[serde(rename = "GuardStep")]
    GuardStep { i: usize, j: usize, c: i64 },
    #[serde(rename = "PreStateStep")]
    PreStateStep { i: usize, j: usize, c: i64 },
}

impl ProofStep {
    pub fn i(&self) -> usize {
        match self {
            ProofStep::GuardStep { i, .. } | ProofStep::PreStateStep { i, .. } => *i,
        }
    }

    pub fn j(&self) -> usize {
        match self {
            ProofStep::GuardStep { j, .. } | ProofStep::PreStateStep { j, .. } => *j,
        }
    }

    pub fn c(&self) -> i64 {
        match self {
            ProofStep::GuardStep { c, .. } | ProofStep::PreStateStep { c, .. } => *c,
        }
    }
}

/// Typed obligation semantics.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum ObligationKind {
    /// v1/v2 baseline: prove `dst - @data_end <= c` around an `add dst, src` edge.
    #[default]
    AddRegPacketBound,
    /// Reserved for v2 guard-driven facts; not yet enabled in checker.
    BranchGuardBound,
}

impl ProgramCertificate {
    pub const VERSION_V1: u32 = 1;
    pub const VERSION_V2: u32 = 2;

    #[allow(dead_code)]
    pub fn empty(program_hash: String) -> Self {
        Self {
            version: Self::VERSION_V2,
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
