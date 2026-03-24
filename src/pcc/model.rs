use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fmt;
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

/// A single annotation at a load instruction.
///
/// Claims that `left_reg - right_reg <= bound` holds in the pre-state of the annotated
/// instruction, and carries a proof chain ([`ProofStep`]) that the interval checker
/// can replay to independently verify the claim.
///
/// The constraint follows DBM convention: a negative `bound` means the left register
/// is at least `|bound|` units below the right register. For packet-safety annotations,
/// `right_reg` is always `@data_end` (index 14) and `bound <= -(offset + access_size)`.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct AnnotationEntry {
    pub left_reg: usize,
    pub right_reg: usize,
    pub bound: i64,
    pub proof: Vec<ProofStep>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind")]
pub enum ProofStep {
    /// Base fact: the interval state at `pc` proves `left_reg - right_reg <= c`.
    /// Placed at the divergence point where zone and interval agree.
    #[serde(rename = "Guard")]
    Guard {
        pc: usize,
        left_reg: usize,
        right_reg: usize,
        c: i64,
    },
    /// Inductive step: the instruction at `pc` transforms the pre-state constraint
    /// `pre_left_reg - pre_right_reg <= b` into the post-state constraint
    /// `post_left_reg - post_right_reg <= b + delta`.
    ///
    /// The claimed `delta` is sound only for specific instruction shapes. Let
    /// `L = pre_left_reg` and `R = pre_right_reg`. The algebraic derivations are:
    ///
    /// | Instruction          | Condition   | Derivation                                                          | Required `delta`    |
    /// |----------------------|-------------|---------------------------------------------------------------------|---------------------|
    /// | `add dst, imm`       | `dst == L`  | `(L+imm) - R = (L-R) + imm <= b + imm`                              | exactly `imm`       |
    /// | `add dst, imm`       | `dst == R`  | `L - (R+imm) = (L-R) - imm <= b - imm`                              | exactly `-imm`      |
    /// | `add dst, src`       | `dst == L`  | `(L+src) - R <= b + ub(src)` since `src <= ub(src)`                 | `>= ub(src)`        |
    /// | `add dst, src`       | `dst == R`  | `L - (R+src) = (L-R) - src <= b - lb(src)` since `src >= lb(src)`   | `>= -lb(src)`       |
    /// | `mov dst, src`       | `src == L`  | value copied; track in `dst`: `post_left = dst`, bound unchanged    | exactly 0           |
    /// | passthrough          | `dst` ∉ {L,R} | constraint registers untouched                                    | exactly 0           |
    ///
    /// Here `ub(src)` and `lb(src)` are the interval upper/lower bounds of `src`
    /// read from the interval pre-state at `pc`.
    ///
    /// The optional `hint` is a human-readable description of the instruction and why
    /// it causes `delta` to be what it is (e.g. `"r5 += r4  (r4 <= 3)"`).
    /// It carries no semantic weight — the checker ignores it — but makes the proof
    /// chain much easier to read.
    #[serde(rename = "Transfer")]
    Transfer {
        pc: usize,
        pre_left_reg: usize,
        pre_right_reg: usize,
        post_left_reg: usize,
        post_right_reg: usize,
        delta: i64,
        /// Human-readable explanation of why `delta` is what it is.
        /// Informational only; omitted from JSON when absent.
        #[serde(skip_serializing_if = "Option::is_none", default)]
        hint: Option<String>,
    },
}

impl ProofStep {
    /// The PC this step refers to.
    pub fn pc(&self) -> usize {
        match self {
            ProofStep::Guard { pc, .. } | ProofStep::Transfer { pc, .. } => *pc,
        }
    }

    /// The output left register index after this step.
    /// Guard: `left_reg`; Transfer: `post_left_reg`.
    pub fn output_left_reg(&self) -> usize {
        match self {
            ProofStep::Guard { left_reg, .. } => *left_reg,
            ProofStep::Transfer { post_left_reg, .. } => *post_left_reg,
        }
    }

    /// The output right register index after this step.
    /// Guard: `right_reg`; Transfer: `post_right_reg`.
    pub fn output_right_reg(&self) -> usize {
        match self {
            ProofStep::Guard { right_reg, .. } => *right_reg,
            ProofStep::Transfer { post_right_reg, .. } => *post_right_reg,
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
///
/// This is a **defensive cap** on the checker side, not a reflection of what the
/// generator currently produces. The generator emits at most one entry per PC
/// (one constraint per load instruction). The cap exists to bound the work an
/// adversarial certificate could force the checker to perform.
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

// ---------------------------------------------------------------------------
// Human-readable display
// ---------------------------------------------------------------------------

/// Maps a register index to its canonical name.
/// Mirrors `Reg::name()` without importing the analysis crate to avoid cycles.
fn reg_name(idx: usize) -> &'static str {
    match idx {
        0 => "0",
        1 => "r0",
        2 => "r1",
        3 => "r2",
        4 => "r3",
        5 => "r4",
        6 => "r5",
        7 => "r6",
        8 => "r7",
        9 => "r8",
        10 => "r9",
        11 => "r10",
        12 => "@data_meta",
        13 => "@data",
        14 => "@data_end",
        _ => "?",
    }
}

impl fmt::Display for ProgramCertificate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Certificate v{}  |  hash: {}  |  {} annotated PC(s)",
            self.version,
            self.program_hash,
            self.pc_annotations.len()
        )?;

        for ann in &self.pc_annotations {
            writeln!(f)?;
            writeln!(
                f,
                "  pc {:>4}:  {} constraint(s)",
                ann.pc,
                ann.entries.len()
            )?;

            for (ei, entry) in ann.entries.iter().enumerate() {
                let lname = reg_name(entry.left_reg);
                let rname = reg_name(entry.right_reg);
                writeln!(
                    f,
                    "    [entry {}]  {} - {} <= {}   ({} proof step(s))",
                    ei,
                    lname,
                    rname,
                    entry.bound,
                    entry.proof.len(),
                )?;

                let mut running: i64 = 0;
                for (si, step) in entry.proof.iter().enumerate() {
                    match step {
                        ProofStep::Guard {
                            pc,
                            left_reg,
                            right_reg,
                            c,
                        } => {
                            running += c;
                            writeln!(
                                f,
                                "      [{si}] Guard    @ pc {:>3}:  {} - {} <= {}",
                                pc,
                                reg_name(*left_reg),
                                reg_name(*right_reg),
                                c,
                            )?;
                        }
                        ProofStep::Transfer {
                            pc,
                            pre_left_reg,
                            pre_right_reg,
                            post_left_reg,
                            post_right_reg,
                            delta,
                            hint,
                        } => {
                            let prev_running = running;
                            running += delta;

                            // Describe what the instruction did to the tracked pair.
                            // Use the hint (filled in by the generator) when available;
                            // fall back to a raw constraint-pair display otherwise.
                            let constraint_str =
                                if pre_left_reg != post_left_reg || pre_right_reg != post_right_reg
                                {
                                    format!(
                                        "{}-{}  ->  {}-{}",
                                        reg_name(*pre_left_reg),
                                        reg_name(*pre_right_reg),
                                        reg_name(*post_left_reg),
                                        reg_name(*post_right_reg),
                                    )
                                } else {
                                    format!(
                                        "{}-{}",
                                        reg_name(*pre_left_reg),
                                        reg_name(*pre_right_reg),
                                    )
                                };
                            let desc = if let Some(h) = hint {
                                h.clone()
                            } else if *delta != 0 {
                                format!("{}  delta={:+}", constraint_str, delta)
                            } else {
                                format!("{}  [passthrough]", constraint_str)
                            };

                            // Show the running-bound arithmetic explicitly so the
                            // reader can follow the proof without mental arithmetic.
                            // e.g. "-8 + 3 = -5" rather than "-8 +3 = -5".
                            let arith = if *delta == 0 {
                                format!("bound: {} (unchanged)", prev_running)
                            } else {
                                let sign = if *delta >= 0 { "+" } else { "-" };
                                format!(
                                    "bound: {} {} {} = {}",
                                    prev_running,
                                    sign,
                                    delta.abs(),
                                    running,
                                )
                            };

                            writeln!(
                                f,
                                "      [{si}] Transfer @ pc {:>3}:  {}   =>  {}",
                                pc, desc, arith,
                            )?;
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_step_guard_json_round_trip() {
        let step = ProofStep::Guard {
            pc: 5,
            left_reg: 6,
            right_reg: 14,
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
            pre_left_reg: 6,
            pre_right_reg: 14,
            post_left_reg: 6,
            post_right_reg: 14,
            delta: 3,
            hint: None,
        };
        let json = serde_json::to_string(&step).unwrap();
        assert!(json.contains("\"kind\":\"Transfer\""));
        assert!(json.contains("\"pre_left_reg\":6"));
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
                    left_reg: 6,
                    right_reg: 14,
                    bound: -5,
                    proof: vec![
                        ProofStep::Guard {
                            pc: 5,
                            left_reg: 6,
                            right_reg: 14,
                            c: -8,
                        },
                        ProofStep::Transfer {
                            pc: 9,
                            pre_left_reg: 6,
                            pre_right_reg: 14,
                            post_left_reg: 6,
                            post_right_reg: 14,
                            delta: 3,
                            hint: None,
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
            left_reg: 6,
            right_reg: 14,
            c: -8,
        };
        assert_eq!(guard.pc(), 5);
        assert_eq!(guard.output_left_reg(), 6);
        assert_eq!(guard.output_right_reg(), 14);
        assert_eq!(guard.bound_contribution(), -8);

        let transfer = ProofStep::Transfer {
            pc: 9,
            pre_left_reg: 5,
            pre_right_reg: 14,
            post_left_reg: 6,
            post_right_reg: 14,
            delta: 3,
            hint: None,
        };
        assert_eq!(transfer.pc(), 9);
        assert_eq!(transfer.output_left_reg(), 6);
        assert_eq!(transfer.output_right_reg(), 14);
        assert_eq!(transfer.bound_contribution(), 3);
    }
}
