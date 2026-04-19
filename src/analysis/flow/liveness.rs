// src/analysis/flow/liveness.rs
//
// Liveness analysis for registers AND stack slots.
//
// Key design decisions:
//   1. Per-subprogram scoping: each subprogram's liveness is computed independently.
//      CallRel is treated as an opaque call that uses R1-R5, defs R0-R5, and does
//      NOT follow into the callee. This prevents callee liveness from leaking into
//      the caller's frame.
//   2. Stack slot tracking: Store to [R10+off] defines slot `off`, Load from [R10+off]
//      uses slot `off`. Helper Calls do NOT affect the caller's stack slots. CallRel
//      operates on a separate frame and also does not affect the caller's stack slots.
//   3. Cross-frame propagation (Phase 2): At each CallRel site, callee-saved registers
//      (R6-R9) that are live in the caller's continuation (at PC+1) are propagated
//      into the callee's entry AND throughout the callee body. This ensures the
//      pruner at any point in the callee can distinguish invocations that differ in
//      registers the caller depends on after the call returns.
//   4. Standard backward dataflow with reverse-iteration fixed-point computation.

use crate::analysis::flow::subprog::{self, SubprogInfo};
use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::ast::{Instr, Operand, Program};
use std::collections::{BTreeMap, HashSet};

// ---------- Internal Live-Set Representation ----------

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct LiveSet {
    regs: HashSet<Reg>,
    /// Stack slot offsets (typically negative, relative to R10) that are live.
    slots: HashSet<i16>,
}

impl LiveSet {
    fn union_from(&mut self, other: &LiveSet) {
        self.regs.extend(other.regs.iter().cloned());
        self.slots.extend(other.slots.iter().cloned());
    }
}

fn is_callee_saved(r: Reg) -> bool {
    matches!(r, Reg::R6 | Reg::R7 | Reg::R8 | Reg::R9 | Reg::R10)
}

// ---------- Public API ----------

/// Computes liveness analysis per-subprogram with cross-frame propagation.
/// Populates `env.insn_aux_data[pc].live_regs` and `env.insn_aux_data[pc].live_slots`.
pub fn compute_liveness(prog: &Program, env: &mut VerifierEnv) {
    let subprogs = subprog::analyze_subprograms(&prog.instrs);

    // Phase 1: Compute per-subprogram local liveness.
    // Each subprogram is analyzed in isolation. CallRel → PC+1 only.
    for info in subprogs.values() {
        compute_subprog_liveness(prog, env, info.start_pc, info.end_pc);
    }

    // Phase 2: Cross-frame propagation.
    // For each CallRel, propagate callee-saved registers that are live in the
    // caller's continuation into the callee's body. Iterate to handle nested calls.
    propagate_cross_frame_liveness(prog, env, &subprogs);
}

// ---------- Phase 2: Cross-Frame Propagation ----------

/// Propagate caller-live callee-saved registers into callees.
///
/// For each `CallRel { target }` at PC `c`:
///   - The caller's continuation is at PC `c+1`.
///   - `live_regs[c+1]` tells us which registers the caller needs after the call.
///   - The intersection with callee-saved registers (R6-R9, R10) gives us registers
///     that pass through the call unchanged AND are needed by the caller.
///   - These must be added to every instruction in the callee's subprogram so the
///     pruner can distinguish invocations with different caller contexts.
///
/// We iterate until fixed point to handle nested calls (A calls B calls C:
/// registers live in A's continuation must propagate through B into C).
fn propagate_cross_frame_liveness(
    prog: &Program,
    env: &mut VerifierEnv,
    subprogs: &BTreeMap<usize, SubprogInfo>,
) {
    let mut changed = true;

    while changed {
        changed = false;

        for (pc, instr) in prog.instrs.iter().enumerate() {
            if let Instr::CallRel { target } = instr {
                let return_pc = pc + 1;
                if return_pc >= prog.instrs.len() {
                    continue;
                }

                // Gather callee-saved registers that are live at the return point.
                let caller_live_at_return = &env.insn_aux_data[return_pc].live_regs;
                let propagated: HashSet<Reg> = caller_live_at_return
                    .iter()
                    .filter(|r| is_callee_saved(**r))
                    .cloned()
                    .collect();

                if propagated.is_empty() {
                    continue;
                }

                // Find the callee's subprogram boundaries.
                if let Some(info) = subprogs.get(target) {
                    // Add propagated registers to EVERY instruction in the callee.
                    // Since these registers are never def'd or used by the callee,
                    // they are uniformly live throughout the callee's body.
                    for callee_pc in info.start_pc..info.end_pc {
                        for &r in &propagated {
                            if env.insn_aux_data[callee_pc].live_regs.insert(r) {
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
    }
}

// ---------- Phase 1: Per-Subprogram Fixed-Point Solver ----------

fn compute_subprog_liveness(prog: &Program, env: &mut VerifierEnv, start: usize, end: usize) {
    let len = end - start;
    if len == 0 {
        return;
    }

    let mut live_in: Vec<LiveSet> = vec![LiveSet::default(); len];
    let mut changed = true;

    // Iterate in reverse order until fixed point.
    // A single reverse pass often converges immediately for DAGs.
    // Loops (back-edges) may require a few more iterations.
    while changed {
        changed = false;

        for idx in (0..len).rev() {
            let pc = start + idx;
            let instr = &prog.instrs[pc];

            // 1. Compute live_out = ∪ { live_in[succ] | succ ∈ successors(pc) }
            let mut live_out = LiveSet::default();
            for succ in get_local_successors(pc, instr, start, end) {
                let succ_idx = succ - start;
                live_out.union_from(&live_in[succ_idx]);
            }

            // 2. Compute live_in = use ∪ (live_out − def)
            let ud = get_use_def(instr);

            let mut new_live_in = live_out;

            // Remove defs
            for d in &ud.def_regs {
                new_live_in.regs.remove(d);
            }
            for d in &ud.def_slots {
                new_live_in.slots.remove(d);
            }

            // Add uses
            new_live_in.regs.extend(ud.use_regs.iter());
            new_live_in.slots.extend(ud.use_slots.iter());

            // 3. Check convergence
            if new_live_in != live_in[idx] {
                live_in[idx] = new_live_in;
                changed = true;
            }
        }
    }

    // 4. Write results into env
    for idx in 0..len {
        let pc = start + idx;
        env.insn_aux_data[pc].live_regs = live_in[idx].regs.clone();
        env.insn_aux_data[pc].live_slots = live_in[idx].slots.clone();
    }
}

// ---------- Successor Calculation (subprogram-local) ----------

/// Returns successors of `pc` that are WITHIN the same subprogram [start, end).
/// CallRel is NOT followed into the callee — it returns to pc+1.
fn get_local_successors(pc: usize, instr: &Instr, start: usize, end: usize) -> Vec<usize> {
    let mut succs = Vec::new();
    let next = pc + 1;
    let is_local = |t: usize| t >= start && t < end;

    match instr {
        Instr::Exit => {
            // No successors — function return.
        }
        Instr::Jmp { target } => {
            if is_local(*target) {
                succs.push(*target);
            }
        }
        Instr::If { target, .. } => {
            if is_local(next) {
                succs.push(next); // fallthrough
            }
            if is_local(*target) {
                succs.push(*target); // branch
            }
        }
        Instr::CallRel { .. } => {
            // CallRel returns to the next instruction in the CALLER.
            // Do NOT follow into the callee's subprogram.
            if is_local(next) {
                succs.push(next);
            }
        }
        _ => {
            // All other instructions fall through to pc+1.
            if is_local(next) {
                succs.push(next);
            }
        }
    }

    succs
}

// ---------- Use/Def Analysis ----------

struct UseDef {
    use_regs: HashSet<Reg>,
    def_regs: HashSet<Reg>,
    use_slots: HashSet<i16>,
    def_slots: HashSet<i16>,
}

impl UseDef {
    fn new() -> Self {
        Self {
            use_regs: HashSet::new(),
            def_regs: HashSet::new(),
            use_slots: HashSet::new(),
            def_slots: HashSet::new(),
        }
    }
}

fn get_use_def(instr: &Instr) -> UseDef {
    let mut ud = UseDef::new();

    match instr {
        Instr::Alu { op, dst, src, .. } => {
            use crate::ast::AluOp;
            // `Mov X, X` is a NOP — no use, no def for liveness purposes.
            // Without this, `Mov R0, R0` would make R0 live even though its
            // value is unchanged, preventing valid pruning at merge points.
            let is_self_mov =
                matches!(op, AluOp::Mov) && matches!(src, Operand::Reg(r) if *r == *dst);

            if is_self_mov {
                // Skip — NOP
            } else if matches!(op, AluOp::Mov) {
                // Mov overwrites dst completely
                ud.def_regs.insert(*dst);
                if let Operand::Reg(r) = src {
                    ud.use_regs.insert(*r);
                }
            } else {
                // Other ALU ops read-then-write dst
                ud.use_regs.insert(*dst);
                ud.def_regs.insert(*dst);
                if let Operand::Reg(r) = src {
                    ud.use_regs.insert(*r);
                }
            }
        }

        Instr::Endian { dst, .. } => {
            ud.use_regs.insert(*dst);
            ud.def_regs.insert(*dst);
        }

        Instr::If { left, right, .. } => {
            ud.use_regs.insert(*left);
            if let Operand::Reg(r) = right {
                ud.use_regs.insert(*r);
            }
        }

        Instr::Jmp { .. } | Instr::MayGoto { .. } => {
            // No register use/def.
        }

        Instr::Load {
            size,
            dst,
            base,
            off,
        } => {
            ud.use_regs.insert(*base);
            ud.def_regs.insert(*dst);
            // If loading from stack (R10-based), the slot is "used" (read).
            if *base == Reg::R10 {
                let byte_count = size.bytes();
                for i in 0..byte_count {
                    ud.use_slots.insert(*off + i as i16);
                }
            }
        }

        Instr::Store {
            size,
            base,
            off,
            src,
        } => {
            ud.use_regs.insert(*base);
            if let Operand::Reg(r) = src {
                ud.use_regs.insert(*r);
            }
            // If storing to stack (R10-based), the slot is "defined" (written).
            if *base == Reg::R10 {
                let byte_count = size.bytes();
                for i in 0..byte_count {
                    ud.def_slots.insert(*off + i as i16);
                }
            }
        }

        Instr::Atomic {
            base,
            src,
            off,
            size,
            ..
        } => {
            ud.use_regs.insert(*base);
            ud.use_regs.insert(*src);
            // Atomic ops read-modify-write the memory location.
            if *base == Reg::R10 {
                let byte_count = size.bytes();
                for i in 0..byte_count {
                    ud.use_slots.insert(*off + i as i16);
                    ud.def_slots.insert(*off + i as i16);
                }
            }
        }

        Instr::Call { .. } => {
            // Helper calls: use R1-R5 as arguments, clobber R0-R5 on return.
            for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
                ud.use_regs.insert(r);
            }
            for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
                ud.def_regs.insert(r);
            }
        }

        Instr::CallRel { .. } => {
            // BPF-to-BPF call: same register convention as helper calls.
            // The callee operates in its OWN stack frame; the caller's stack
            // slots are unaffected. Callee-saved registers (R6-R9) are preserved
            // by convention — they are NOT listed as defs so they pass through
            // in the liveness analysis.
            for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
                ud.use_regs.insert(r);
            }
            for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
                ud.def_regs.insert(r);
            }
        }

        Instr::Exit => {}

        Instr::LoadPacket { src, .. } => {
            if let Some(r) = src {
                ud.use_regs.insert(*r);
            }
        }

        Instr::LoadMap { dst, .. } => {
            ud.def_regs.insert(*dst);
        }

        Instr::LoadSx {
            size,
            dst,
            base,
            off,
        } => {
            ud.use_regs.insert(*base);
            ud.def_regs.insert(*dst);
            if *base == Reg::R10 {
                let byte_count = size.bytes();
                for i in 0..byte_count {
                    ud.use_slots.insert(*off + i as i16);
                }
            }
        }

        Instr::MovSx { dst, src, .. } => {
            ud.def_regs.insert(*dst);
            if let Operand::Reg(r) = src {
                ud.use_regs.insert(*r);
            }
        }

        Instr::LoadAcq {
            size,
            dst,
            base,
            off,
        } => {
            ud.use_regs.insert(*base);
            ud.def_regs.insert(*dst);
            if *base == Reg::R10 {
                let byte_count = size.bytes();
                for i in 0..byte_count {
                    ud.use_slots.insert(*off + i as i16);
                }
            }
        }

        Instr::StoreRel {
            size,
            base,
            off,
            src,
        } => {
            ud.use_regs.insert(*base);
            ud.use_regs.insert(*src);
            if *base == Reg::R10 {
                let byte_count = size.bytes();
                for i in 0..byte_count {
                    ud.def_slots.insert(*off + i as i16);
                }
            }
        }
    }

    ud
}
