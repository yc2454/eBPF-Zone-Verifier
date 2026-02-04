// src/analysis/flow/subprog.rs
//
// Subprogram analysis: structure validation and stack overflow checking

use std::collections::{BTreeMap, BTreeSet, HashSet};
use crate::ast::{Instr, Program};
use crate::common::constants;
use crate::zone::domain::Reg;

const MAX_BPF_STACK: u16 = 512;

#[derive(Debug, Clone)]
pub struct SubprogInfo {
    pub start_pc: usize,
    pub end_pc: usize,
    pub max_stack_depth: u16,
}

#[derive(Debug, Clone)]
pub enum SubprogError {
    JumpOutOfRange { pc: usize, target: usize, start: usize, end: usize },
    CallOutOfBounds { pc: usize, target: usize },
    InvalidTerminator { pc: usize },
    StackOverflow { pc: usize, combined: u16 },
    CallDepthExceeded { pc: usize, depth: usize },
}

impl std::fmt::Display for SubprogError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SubprogError::JumpOutOfRange { pc, target, start, end } => {
                write!(f, "jump out of range at pc {}: target {} is outside function scope [{}, {})", pc, target, start, end)
            }
            SubprogError::CallOutOfBounds { pc, target } => {
                write!(f, "call out of bounds at pc {}: target {}", pc, target)
            }
            SubprogError::InvalidTerminator { pc } => {
                write!(f, "last insn at pc {} is not an exit or jmp", pc)
            }
            SubprogError::StackOverflow { pc, combined } => {
                write!(f, "combined stack size of {} at pc {} exceeds {}", combined, pc, MAX_BPF_STACK)
            }
            SubprogError::CallDepthExceeded { pc, depth } => {
                write!(f, "call depth of {} at pc {} exceeds maximum of 8", depth, pc)
            }
        }
    }
}

/// Analyze all subprograms and compute their max stack depths.
pub fn analyze_subprograms(instrs: &[Instr]) -> BTreeMap<usize, SubprogInfo> {
    let mut entries: Vec<usize> = vec![0];

    for insn in instrs {
        if let Instr::CallRel { target } = insn {
            if !entries.contains(target) {
                entries.push(*target);
            }
        }
    }
    entries.sort();

    let mut subprogs = BTreeMap::new();

    for (i, &start_pc) in entries.iter().enumerate() {
        let end_pc = entries.get(i + 1).copied().unwrap_or(instrs.len());
        let max_stack_depth = compute_max_stack_depth(&instrs[start_pc..end_pc]);

        subprogs.insert(start_pc, SubprogInfo {
            start_pc,
            end_pc,
            max_stack_depth,
        });
    }

    subprogs
}

/// Compute the maximum stack depth accessed by a sequence of Instrs.
fn compute_max_stack_depth(instrs: &[Instr]) -> u16 {
    let mut max_depth: u16 = 0;

    for insn in instrs {
        let off = match insn {
            Instr::Store { base, off, .. } if *base == Reg::R10 => *off,
            Instr::Load { base, off, .. } if *base == Reg::R10 => *off,
            Instr::Atomic { base, off, .. } if *base == Reg::R10 => *off,
            _ => continue,
        };

        if off < 0 {
            let depth = (-off) as u16;
            max_depth = max_depth.max(depth);
        }
    }

    max_depth
}

/// Validate subprogram structure: jump bounds and terminators.
/// Moved from cfg.rs
pub fn check_subprogs(prog: &Program) -> Result<(), SubprogError> {
    // 1. Identify all function entry points
    let mut func_starts = BTreeSet::new();
    func_starts.insert(0);

    for insn in &prog.instrs {
        if let Instr::CallRel { target } = insn {
            func_starts.insert(*target);
        }
    }

    let starts: Vec<usize> = func_starts.into_iter().collect();

    // 2. Validate each function
    for (i, &start) in starts.iter().enumerate() {
        let end = starts.get(i + 1).cloned().unwrap_or(prog.instrs.len());

        // A. Validate Instrs within the function
        for pc in start..end {
            let insn = &prog.instrs[pc];
            let is_local = |t: usize| t >= start && t < end;

            match insn {
                Instr::Jmp { target } => {
                    if !is_local(*target) {
                        return Err(SubprogError::JumpOutOfRange {
                            pc, target: *target, start, end,
                        });
                    }
                }
                Instr::If { target, .. } => {
                    if !is_local(*target) {
                        return Err(SubprogError::JumpOutOfRange {
                            pc, target: *target, start, end,
                        });
                    }
                }
                Instr::CallRel { target } => {
                    if *target >= prog.instrs.len() {
                        return Err(SubprogError::CallOutOfBounds {
                            pc, target: *target,
                        });
                    }
                }
                _ => {}
            }
        }

        // B. Validate the function terminator
        if end > 0 {
            let last_pc = end - 1;
            let last_insn = &prog.instrs[last_pc];

            let is_terminator = matches!(
                last_insn,
                Instr::Jmp { .. } | Instr::Exit
            );

            if !is_terminator {
                return Err(SubprogError::InvalidTerminator { pc: last_pc });
            }
        }
    }

    Ok(())
}

/// Check that no call chain would cause stack overflow.
pub fn check_stack_overflow(prog: &Program) -> Result<(), SubprogError> {
    let subprogs = analyze_subprograms(&prog.instrs);

    if subprogs.is_empty() {
        return Ok(());
    }

    check_call_chain(prog, &subprogs, 0, 0, 1, &mut HashSet::new())
}

fn check_call_chain(
    prog: &Program,
    subprogs: &BTreeMap<usize, SubprogInfo>,
    entry_pc: usize,
    depth_so_far: u16,
    call_depth: usize,  // NEW: number of frames
    visiting: &mut HashSet<usize>,
) -> Result<(), SubprogError> {
    // Check call depth first
    if call_depth > constants::BPF_MAX_CALL_FRAMES {
        return Err(SubprogError::CallDepthExceeded {
            pc: entry_pc,
            depth: call_depth,
        });
    }

    if !visiting.insert(entry_pc) {
        return Ok(());
    }

    let info = match subprogs.get(&entry_pc) {
        Some(info) => info,
        None => {
            visiting.remove(&entry_pc);
            return Ok(());
        }
    };

    let new_depth = depth_so_far + info.max_stack_depth;

    if new_depth > MAX_BPF_STACK {
        return Err(SubprogError::StackOverflow {
            pc: entry_pc,
            combined: new_depth,
        });
    }

    for pc in info.start_pc..info.end_pc {
        if let Instr::CallRel { target } = &prog.instrs[pc] {
            check_call_chain(prog, subprogs, *target, new_depth, call_depth + 1, visiting)?;
        }
    }

    visiting.remove(&entry_pc);
    Ok(())
}
