use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;

/// Top-level PCC annotation container.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ProgramAnnotation {
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
pub enum ProofStep {
    GuardStep { i: usize, j: usize, c: i64 },
    PreStateStep { i: usize, j: usize, c: i64 },
}

impl ProgramAnnotation {
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
            .with_context(|| format!("failed to read annotation file '{}'", path))?;
        serde_json::from_str(&raw)
            .with_context(|| format!("failed to parse annotation JSON '{}'", path))
    }

    #[allow(dead_code)]
    pub fn save_to_path(&self, path: &str) -> Result<()> {
        let raw = serde_json::to_string_pretty(self)
            .context("failed to serialize annotation JSON")?;
        fs::write(path, raw)
            .with_context(|| format!("failed to write annotation file '{}'", path))
    }
}
