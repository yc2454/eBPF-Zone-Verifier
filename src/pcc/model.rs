use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;

/// Top-level PCC certificate container.
///
/// `program_hash` binds this certificate to one exact lowered program.
/// `obligations` are local edge claims checked independently.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ProgramCertificate {
    pub version: u32,
    pub program_hash: String,
    /// Inductive per-PC annotations (current prototype path).
    #[serde(default)]
    pub pc_annotations: Vec<PcAnnotation>,
    /// Edge-obligation format kept for compatibility during migration.
    #[serde(default)]
    pub obligations: Vec<EdgeObligation>,
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
pub struct EdgeObligation {
    /// Explicit theorem template.
    ///
    /// This is the primary semantic tag used by the checker. It defines:
    /// - what the target constraint means,
    /// - which proof-step patterns are legal,
    /// - and which refinement (if any) may be applied on success.
    #[serde(default)]
    pub kind: ObligationKind,
    /// Program counter of predecessor instruction for this edge claim.
    pub pred_pc: usize,
    /// Program counter of successor state for this edge claim.
    pub succ_pc: usize,
    /// Required for branch obligations; ignored for non-branch obligations.
    #[serde(default)]
    pub branch_taken: Option<bool>,
    /// Fingerprint over predecessor transition context.
    ///
    /// The checker recomputes this value and requires exact match before
    /// considering proof steps.
    pub pred_fingerprint: u64,
    /// Claimed post-edge bound `target.i - target.j <= target.c`.
    pub target: Constraint,
    /// Proof chain whose sum must justify `target`.
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
    /// Constraint directly implied by branch condition + edge polarity.
    #[serde(rename = "GuardStep")]
    GuardStep { i: usize, j: usize, c: i64 },
    /// Constraint read from predecessor abstract state.
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

/// Typed obligation semantics (theorem templates).
///
/// This is intentionally separate from `ProofStep`:
/// - `ObligationKind` says what claim is being proved and how a success can
///   refine the successor state.
/// - `ProofStep` says where individual inequalities come from.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum ObligationKind {
    /// Proves packet-end bound around `add dst, src` style pointer update.
    ///
    /// Current checker semantics:
    /// - verifies chain and transfer-consistency,
    /// - then refines only packet pointer range metadata.
    #[default]
    AddRegPacketBound,
    /// Proves packet-end bound using branch-implied guard + prestate facts.
    ///
    /// Current checker semantics:
    /// - validates branch edge polarity (`branch_taken`) and derived guard,
    /// - validates proof chain,
    /// - then applies same narrow packet-range refinement sink.
    BranchGuardBound,
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
