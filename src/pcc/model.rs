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

impl ProgramCertificate {
    /// Prototype certificate schema version.
    pub const VERSION: u32 = 1;

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
