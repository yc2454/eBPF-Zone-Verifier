use crate::{ast::Instr};

/// A lightweight record of a single step in the execution path.
pub struct Breadcrumb {
    pub pc: usize,
    /// We format the instruction string eagerly so we don't hold references to the Program
    pub instr_str: String,
    /// The index of the previous step in the `History` vector
    pub parent_idx: Option<usize>,
    pub reg_types_str: String,
}

pub struct History {
    steps: Vec<Breadcrumb>,
}

impl History {
    pub fn new() -> Self {
        Self {
            // Pre-allocate space to avoid frequent reallocations during analysis
            steps: Vec::with_capacity(10_000), 
        }
    }

    /// Record a step and return its index (which acts as the ID).
    pub fn record(&mut self, pc: usize, instr: &Instr, reg_types_str: String, parent_idx: Option<usize>) -> usize {
        let idx = self.steps.len();
        self.steps.push(Breadcrumb {
            pc,
            instr_str: format!("{:?}", instr),
            reg_types_str,
            parent_idx,
        });
        idx
    }

    /// Walk backwards from the crash point to the start to reconstruct the trace.
    pub fn get_trace(&self, crash_idx: usize) -> Vec<&Breadcrumb> {
        let mut trace = Vec::new();
        let mut current = Some(crash_idx);

        while let Some(idx) = current {
            if let Some(step) = self.steps.get(idx) {
                trace.push(step);
                current = step.parent_idx;
            } else {
                break;
            }
        }

        // Reverse to get chronological order (Entry -> Crash)
        trace.reverse();
        trace
    }

    /// Check if `target_pc` was visited on the path leading to `from_idx`
    pub fn path_contains_pc(&self, from_idx: usize, target_pc: usize) -> bool {
        let mut current = Some(from_idx);
        while let Some(idx) = current {
            if let Some(step) = self.steps.get(idx) {
                if step.pc == target_pc {
                    return true;
                }
                current = step.parent_idx;
            } else {
                break;
            }
        }
        false
    }
}