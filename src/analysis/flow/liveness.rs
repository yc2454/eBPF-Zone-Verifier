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
//   3. Standard backward dataflow with reverse-iteration fixed-point computation.

use crate::ast::{Instr, Operand, Program};
use crate::zone::domain::Reg;
use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::flow::subprog;
use std::collections::HashSet;

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

// ---------- Public API ----------

/// Computes liveness analysis per-subprogram and populates
/// `env.insn_aux_data[pc].live_regs` and `env.insn_aux_data[pc].live_slots`.
pub fn compute_liveness(prog: &Program, env: &mut VerifierEnv) {
    let subprogs = subprog::analyze_subprograms(&prog.instrs);

    for (_entry, info) in &subprogs {
        compute_subprog_liveness(prog, env, info.start_pc, info.end_pc);
    }
}

// ---------- Per-Subprogram Fixed-Point Solver ----------

fn compute_subprog_liveness(
    prog: &Program,
    env: &mut VerifierEnv,
    start: usize,
    end: usize,
) {
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
fn get_local_successors(
    pc: usize,
    instr: &Instr,
    start: usize,
    end: usize,
) -> Vec<usize> {
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
        Instr::MovArg0 { dst } => {
            ud.def_regs.insert(*dst);
        }

        Instr::Alu { op, dst, src, .. } => {
            use crate::ast::AluOp;
            if matches!(op, AluOp::Mov) {
                // Mov overwrites dst completely
                ud.def_regs.insert(*dst);
            } else {
                // Other ALU ops read-then-write dst
                ud.use_regs.insert(*dst);
                ud.def_regs.insert(*dst);
            }
            if let Operand::Reg(r) = src {
                ud.use_regs.insert(*r);
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

        Instr::Jmp { .. } => {
            // No register use/def.
        }

        Instr::Load { size, dst, base, off } => {
            ud.use_regs.insert(*base);
            ud.def_regs.insert(*dst);
            // If loading from stack (R10-based), the slot is "used" (read).
            if *base == Reg::R10 {
                // Track every byte-aligned sub-slot that this load touches.
                let byte_count = mem_size_bytes(size);
                for i in 0..byte_count {
                    ud.use_slots.insert(*off + i as i16);
                }
            }
        }

        Instr::Store { size, base, off, src } => {
            ud.use_regs.insert(*base);
            if let Operand::Reg(r) = src {
                ud.use_regs.insert(*r);
            }
            // If storing to stack (R10-based), the slot is "defined" (written).
            if *base == Reg::R10 {
                let byte_count = mem_size_bytes(size);
                for i in 0..byte_count {
                    ud.def_slots.insert(*off + i as i16);
                }
            }
        }

        Instr::Atomic { base, src, off, size, .. } => {
            ud.use_regs.insert(*base);
            ud.use_regs.insert(*src);
            // Atomic ops read-modify-write the memory location.
            if *base == Reg::R10 {
                let byte_count = mem_size_bytes(size);
                for i in 0..byte_count {
                    ud.use_slots.insert(*off + i as i16);
                    ud.def_slots.insert(*off + i as i16);
                }
            }
        }

        Instr::Call { .. } => {
            // Helper calls: use R1-R5 as arguments, clobber R0-R5 on return.
            // Stack is PRESERVED across helper calls (helpers may read from it
            // via pointers, but that's handled by the type system, not liveness).
            for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
                ud.use_regs.insert(r);
            }
            for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
                ud.def_regs.insert(r);
            }
            // No stack slot use/def — helpers don't directly touch the BPF stack
            // in a way that liveness needs to model.
        }

        Instr::CallRel { .. } => {
            // BPF-to-BPF call: same register convention as helper calls.
            // The callee operates in its OWN stack frame; the caller's stack
            // slots are unaffected. Callee-saved registers (R6-R9) are preserved
            // by convention but NOT modeled as defs here — they pass through.
            for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
                ud.use_regs.insert(r);
            }
            for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
                ud.def_regs.insert(r);
            }
            // No stack slot use/def — callee has a separate frame.
        }

        Instr::Exit => {
            // Return value is in R0.
            ud.use_regs.insert(Reg::R0);
        }

        Instr::LoadPacket { src, .. } => {
            if let Some(r) = src {
                ud.use_regs.insert(*r);
            }
        }

        Instr::LoadMap { dst, .. } => {
            ud.def_regs.insert(*dst);
        }
    }

    ud
}

// ---------- Utilities ----------

fn mem_size_bytes(size: &crate::ast::MemSize) -> u8 {
    use crate::ast::MemSize;
    match size {
        MemSize::U8 => 1,
        MemSize::U16 => 2,
        MemSize::U32 => 4,
        MemSize::U64 => 8,
    }
}
