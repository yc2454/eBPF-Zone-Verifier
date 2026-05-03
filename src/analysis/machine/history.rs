use crate::ast::Instr;

/// A lightweight record of a single step in the execution path.
pub struct Breadcrumb {
    pub pc: usize,
    /// We format the instruction string eagerly so we don't hold references to the Program
    pub instr_str: String,
    /// The actual instruction at `pc` at the time of execution. Cloned so
    /// `mark_chain_precision_backward` can walk the history without
    /// re-borrowing `Program`. Cheap (Instr is a small enum); cost is
    /// outweighed by the simplification at the walk site.
    pub instr: Instr,
    /// The index of the previous step in the `History` vector
    pub parent_idx: Option<usize>,
    pub reg_types_str: String,
    /// Compact per-register interval snapshot at the time of execution.
    /// Formatted by `State::reg_ranges_str()`.
    pub reg_ranges_str: String,
    pub depth: usize,
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
    pub fn record(
        &mut self,
        pc: usize,
        instr: &Instr,
        reg_types_str: String,
        reg_ranges_str: String,
        depth: usize,
        parent_idx: Option<usize>,
    ) -> usize {
        let idx = self.steps.len();
        self.steps.push(Breadcrumb {
            pc,
            instr_str: format!("{:?}", instr),
            instr: instr.clone(),
            reg_types_str,
            reg_ranges_str,
            depth,
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

    /// Collect all PCs visited on the path from `from_idx` back to (but not including)
    /// the first occurrence of `target_pc`. These are the PCs in the loop body.
    ///
    /// If `frame_depth` is Some, only collects PCs at that specific call depth.
    /// This filters out callee PCs when analyzing loops that contain BPF-to-BPF calls.
    pub fn loop_body_pcs(
        &self,
        from_idx: usize,
        target_pc: usize,
        frame_depth: Option<usize>,
    ) -> Vec<usize> {
        let mut pcs = Vec::new();
        let mut current = Some(from_idx);
        while let Some(idx) = current {
            if let Some(step) = self.steps.get(idx) {
                if step.pc == target_pc {
                    break;
                }
                // Only include PCs at the target frame depth (if specified)
                if frame_depth.is_none_or(|d| step.depth == d) {
                    pcs.push(step.pc);
                }
                current = step.parent_idx;
            } else {
                break;
            }
        }
        pcs
    }

    /// Check if `target_pc` was visited ANYWHERE on the path leading to `from_idx`.
    pub fn is_on_path(&self, from_idx: usize, target_pc: usize) -> bool {
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

    /// Check if `target_pc` was visited at the SAME stack depth on the path leading to `from_idx`.
    /// A PC is considered a back-edge only if the depth never dropped below current_depth.
    pub fn is_back_edge(&self, from_idx: usize, target_pc: usize, current_depth: usize) -> bool {
        let mut current = Some(from_idx);
        while let Some(idx) = current {
            if let Some(step) = self.steps.get(idx) {
                if step.depth < current_depth {
                    // We returned to a caller, so any PC further back is not a same-frame back-edge
                    return false;
                }
                if step.pc == target_pc && step.depth == current_depth {
                    return true;
                }
                current = step.parent_idx;
            } else {
                break;
            }
        }
        false
    }

    /// Get a step by index.
    pub fn get(&self, idx: usize) -> Option<&Breadcrumb> {
        self.steps.get(idx)
    }
}
