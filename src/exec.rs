// src/exec.rs
use std::collections::VecDeque;

use crate::ast::{AluOp, CmpOp, Instr, MemSize, Operand, Program, Width, EndianKind};
use crate::dbm::Dbm;
use crate::domain::{
    Var, VAR_ENV,
    // --- assignment / forget ---
    assign_eq, assign_zero,
    assign_add_imm, assign_add_reg,
    assign_and_mask,
    forget,
    // --- assume/guards ---
    assume_ge_const, assume_le_const, assume_less_than, assume_eq_const,
    assume_ge_var, assume_le_var, assume_gt_var, assume_le_var_plus_const,
};
use crate::utils::{dbm_equals}; // if you have this; otherwise keep your existing helper

#[derive(Clone, Copy)]
pub struct ExecContext {
    pub zero: Var,
    pub r10: Var,
    pub stack_min: i64,
    pub stack_max: i64,
}

fn check_stack_load(ctx: &ExecContext, dbm: &Dbm, base: Var) {
    use crate::dbm::INF;

    let ub = dbm.get(base, ctx.zero);      // base - 0 <= ub
    let lb_c = dbm.get(ctx.zero, base);   // 0 - base <= lb_c  ≡ base >= -lb_c

    let lb_str;
    let ub_str;

    let mut has_lb = false;
    let mut has_ub = false;
    let mut lb_val = 0i64;
    let mut ub_val = 0i64;

    if lb_c != INF {
        has_lb = true;
        lb_val = -lb_c;
        lb_str = lb_val.to_string();
    } else {
        lb_str = "-∞".to_string();
    }

    if ub != INF {
        has_ub = true;
        ub_val = ub;
        ub_str = ub_val.to_string();
    } else {
        ub_str = "+∞".to_string();
    }

    println!(
        "Load check: {} (offset) ∈ [{}, {}]",
        base.name(),
        lb_str,
        ub_str
    );

    // Only say "SAFE" if we actually have both finite bounds
    if has_lb && has_ub
        && lb_val >= ctx.stack_min
        && ub_val <= ctx.stack_max
    {
        println!(
            "  => SAFE: within stack [{}, {}]",
            ctx.stack_min, ctx.stack_max
        );
    } else {
        println!(
            "  => VIOLATION (or unknown): not fully within stack [{}, {}]",
            ctx.stack_min, ctx.stack_max
        );
    }
}

fn proven_u32_range(dbm: &Dbm, v: Var, zero: Var) -> bool {
    // requires: (v - 0) <= 0xffff_ffff  AND  (0 - v) <= 0
    let vi = VAR_ENV.index(v);
    let zi = VAR_ENV.index(zero);
    let ub = dbm.raw(vi, zi); // v - 0
    let lb = dbm.raw(zi, vi); // 0 - v  (<= 0 means v >= 0)
    ub <= 0xffff_ffff && lb <= 0
}

fn transfer_mov_arg0(dbm_in: &Dbm, pc: usize, dst: Var) -> Vec<(usize, Dbm)> {
    let mut dbm = dbm_in.clone();
    forget(&mut dbm, dst);
    vec![(pc + 1, dbm)]
}

fn transfer_alu(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    width: Width,
    op: AluOp,
    dst: Var,
    src: Operand,
) -> Vec<(usize, Dbm)> {
    let mut dbm = dbm_in.clone();

    match op {
        AluOp::Mov => {
            match src {
                Operand::Reg(r) => {
                    if width == Width::W32 {
                        // mov32 reg: result is in [0, 0xffff_ffff], but we can't express
                        // dst = (r mod 2^32) relationally in zones. Stay sound:
                        forget(&mut dbm, dst);
                        assume_ge_const(&mut dbm, dst, ctx.zero, 0);
                        assume_le_const(&mut dbm, dst, ctx.zero, 0xffff_ffff);
                    } else {
                        // mov64 reg (existing behavior)
                        if r == ctx.r10 {
                            // dst = r10  ⇒ treat as "offset from fp is 0"
                            assign_zero(&mut dbm, dst, ctx.zero);
                        } else {
                            assign_eq(&mut dbm, dst, r);
                        }
                    }
                }
                Operand::Imm(c) => {
                    // mov32 imm: immediate is u32 then zero-extended
                    let c = if width == Width::W32 { (c as u32) as i64 } else { c };

                    // dst = c
                    assign_zero(&mut dbm, dst, ctx.zero);
                    assume_le_const(&mut dbm, dst, ctx.zero, c);
                    assume_ge_const(&mut dbm, dst, ctx.zero, c);
                }
            }
        }

        AluOp::Add => {
            match src {
                Operand::Imm(c) => assign_add_imm(&mut dbm, dst, c),
                Operand::Reg(r) => assign_add_reg(&mut dbm, dst, r, ctx.zero),
            }
        }

        AluOp::Sub => {
            match src {
                Operand::Imm(c) => {
                    // dst -= c  ==  dst += (-c)
                    assign_add_imm(&mut dbm, dst, -c);
                }
                Operand::Reg(_r) => {
                    // dst -= reg is nonlinear in zones (x := x - y).
                    // For now, stay sound and just forget dst.
                    forget(&mut dbm, dst);
                }
            }
        }

        AluOp::And => {
            match src {
                Operand::Imm(mask) => {
                    let mask = if width == Width::W32 {
                        (mask as u32) as i64
                    } else {
                        mask
                    };
                    assign_and_mask(&mut dbm, dst, mask, ctx.zero)
                }
                Operand::Reg(_r) => {
                    // dst &= unknown ⇒ dst becomes unknown
                    forget(&mut dbm, dst);
                }
            }
        }

        AluOp::Or => {
            match src {
                Operand::Imm(_mask) => {
                    if width == Width::W32 {
                        // w_dst |= mask: result is a 32-bit value, but relation to old dst is nonlinear.
                        // MVP: forget dst, then enforce 0 <= dst <= 0xffff_ffff (like other W32 ops).
                        forget(&mut dbm, dst);
                        assume_ge_const(&mut dbm, dst, ctx.zero, 0);
                        assume_le_const(&mut dbm, dst, ctx.zero, 0xffff_ffff);
                    } else {
                        // OR64 imm: we can't model it usefully in zones; just forget dst.
                        forget(&mut dbm, dst);
                    }
                }
                Operand::Reg(_r) => {
                    // dst |= reg: nonlinear, just forget.
                    forget(&mut dbm, dst);
                }
            }
        }

        AluOp::Shl => {
            // Nonlinear bit op; MVP: forget
            forget(&mut dbm, dst);
        }

        AluOp::Shr => {
            match src {
                Operand::Imm(k) => {
                    let bits = if width == Width::W32 { 32u32 } else { 64u32 };
                    let k = (k as u32).min(bits); // clamp defensively

                    // result is unsigned logical shift => 0 <= dst <= 2^(bits-k)-1
                    forget(&mut dbm, dst);
                    assume_ge_const(&mut dbm, dst, ctx.zero, 0);

                    if k < bits {
                        let ub: i64 = ((1u128 << (bits - k)) - 1) as i64;
                        assume_le_const(&mut dbm, dst, ctx.zero, ub);
                    } else {
                        // shift by >= bits => result 0 in real semantics; MVP just set to 0
                        assume_eq_const(&mut dbm, dst, ctx.zero, 0);
                    }
                }
                Operand::Reg(_) => {
                    // shift-by-reg: not modeling yet
                    forget(&mut dbm, dst);
                }
            }
        }

        // Not needed yet; keep sound default
        AluOp::Sub | AluOp::Or | AluOp::Xor => {
            forget(&mut dbm, dst);
        }
    }

    if dbm.is_inconsistent() {
        vec![]
    } else {
        vec![(pc + 1, dbm)]
    }
}

fn transfer_endian(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    dst: Var,
    kind: EndianKind,
) -> Vec<(usize, Dbm)> {
    let mut dbm = dbm_in.clone();

    // Endian ops are nonlinear bit permutations; we cannot track the relation
    // to the old value. MVP: forget, then approximate the guaranteed range.
    forget(&mut dbm, dst);

    let (lo, hi) = match kind {
        EndianKind::Be16 => (0i64, 0x0000_ffff),
        EndianKind::Be32 => (0i64, 0xffff_ffff),
        EndianKind::Be64 => {
            // Byteswap64 preserves full 64-bit domain; no useful bound.
            return vec![(pc + 1, dbm)];
        }
    };

    assume_ge_const(&mut dbm, dst, ctx.zero, lo);
    assume_le_const(&mut dbm, dst, ctx.zero, hi);

    vec![(pc + 1, dbm)]
}

fn transfer_if(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    width: Width,
    left: Var,
    op: CmpOp,
    right: Operand,
    target: usize,
) -> Vec<(usize, Dbm)> {
    let mut out = Vec::new();

    // THEN branch: condition holds
    let mut dbm_then = dbm_in.clone();
    // ELSE branch: condition does not hold
    let mut dbm_else = dbm_in.clone();

    // For JMP32 Eq/Ne with imm, only refine if left is already known to be u32-range.
    if width == Width::W32 {
        if let Operand::Imm(_c) = right {
            if matches!(
                op,
                CmpOp::Eq
                    | CmpOp::Ne
                    | CmpOp::UGe
                    | CmpOp::ULe
                    | CmpOp::UGt
                    | CmpOp::ULt
            ) && !proven_u32_range(dbm_in, left, ctx.zero)
            {
                // Can't model low32 comparison safely -> fork without refinement.
                return vec![(pc + 1, dbm_in.clone()), (target, dbm_in.clone())];
            }
        } else {
            // Reg comparisons in JMP32: too tricky with low32 semantics, don't refine.
            return vec![(pc + 1, dbm_in.clone()), (target, dbm_in.clone())];
        }
    }

    match (op, right) {
        // ---------- left >= imm ----------
        (CmpOp::UGe, Operand::Imm(c)) => {
            assume_ge_const(&mut dbm_then, left, ctx.zero, c);
            assume_less_than(&mut dbm_else, left, ctx.zero, c);
        }

        // ---------- left <= imm ----------
        (CmpOp::ULe, Operand::Imm(c)) => {
            assume_le_const(&mut dbm_then, left, ctx.zero, c);
            assume_ge_const(&mut dbm_else, left, ctx.zero, c + 1);
        }

        // ---------- left > imm ----------
        (CmpOp::UGt, Operand::Imm(c)) => {
            // then: left > c  => left >= c + 1
            assume_ge_const(&mut dbm_then, left, ctx.zero, c + 1);
            // else: left <= c
            assume_le_const(&mut dbm_else, left, ctx.zero, c);
        }

        // ---------- left < imm ----------
        (CmpOp::ULt, Operand::Imm(c)) => {
            // then: left < c  => left <= c - 1
            assume_less_than(&mut dbm_then, left, ctx.zero, c);
            // else: left >= c
            assume_ge_const(&mut dbm_else, left, ctx.zero, c);
        }

        (CmpOp::Ne, Operand::Imm(imm)) => {
            // then: left != imm  (DBM can't express disequality => no refinement)
            // else: left == imm
            assume_eq_const(&mut dbm_else, left, ctx.zero, imm);
            // keep dbm_then unchanged
        }

        // ---------- left >= reg ----------
        (CmpOp::UGe, Operand::Reg(r)) => {
            // left >= r  <=>  r - left <= 0
            assume_ge_var(&mut dbm_then, left, r);

            // else: left < r  <=> left <= r - 1  <=> left - r <= -1
            assume_le_var_plus_const(&mut dbm_else, left, r, -1);
        }

        // ---------- left <= reg ----------
        (CmpOp::ULe, Operand::Reg(r)) => {
            // left <= r
            assume_le_var(&mut dbm_then, left, r);
            // else: left > r
            assume_gt_var(&mut dbm_else, left, r);
        }

        // ---------- left > reg ----------
        (CmpOp::UGt, Operand::Reg(r)) => {
            // then: left > r
            assume_gt_var(&mut dbm_then, left, r);
            // else: left <= r
            assume_le_var(&mut dbm_else, left, r);
        }

        // ---------- left < reg ----------
        (CmpOp::ULt, Operand::Reg(r)) => {
            // then: left < r  => left <= r - 1
            assume_le_var_plus_const(&mut dbm_then, left, r, -1);
            // else: left >= r
            assume_ge_var(&mut dbm_else, left, r);
        }

        // Eq/Ne not needed yet: stay sound (no refinement)
        (CmpOp::Eq, _) | (CmpOp::Ne, _) => {
            // Conservative: no constraints; just fork
        }
    }

    if !dbm_then.is_inconsistent() {
        out.push((target, dbm_then));
    }
    if !dbm_else.is_inconsistent() {
        out.push((pc + 1, dbm_else));
    }
    out
}

fn transfer_load(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    size: MemSize,
    dst: Var,
    base: Var,
    off: i16,
) -> Vec<(usize, Dbm)> {
    // For now, we only “verify” stack loads (base is an offset-from-fp var).
    // Effective address offset = base + off
    let (lo, hi) = crate::domain::get_bounds(dbm_in, base, ctx.zero);

    let eff_lo = lo.map(|x| x + off as i64);
    let eff_hi = hi.map(|x| x + off as i64);

    // require fully within stack range
    let ok = match (eff_lo, eff_hi) {
        (Some(l), Some(h)) => l >= ctx.stack_min && h <= ctx.stack_max,
        _ => false, // unknown ⇒ reject (verifier-style)
    };

    if !ok {
        println!(
            "Load check failed at pc {}: {:?} from base {:?}+{} not provably within [{}, {}] (bounds: {:?}..{:?})",
            pc, size, base, off, ctx.stack_min, ctx.stack_max, eff_lo, eff_hi
        );
        return vec![];
    }

    let mut dbm = dbm_in.clone();
    forget(&mut dbm, dst);
    vec![(pc + 1, dbm)]
}

fn transfer_store(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    size: MemSize,
    base: Var,
    off: i16,
    _src: Var,
) -> Vec<(usize, Dbm)> {
    let (lo, hi) = crate::domain::get_bounds(dbm_in, base, ctx.zero);
    let eff_lo = lo.map(|x| x + off as i64);
    let eff_hi = hi.map(|x| x + off as i64);

    let ok = match (eff_lo, eff_hi) {
        (Some(l), Some(h)) => l >= ctx.stack_min && h <= ctx.stack_max,
        _ => false,
    };

    if !ok {
        println!(
            "Store check failed at pc {}: {:?} to base {:?}+{} not provably within [{}, {}] (bounds: {:?}..{:?})",
            pc, size, base, off, ctx.stack_min, ctx.stack_max, eff_lo, eff_hi
        );
        return vec![];
    }

    vec![(pc + 1, dbm_in.clone())]
}

fn transfer_call(dbm_in: &Dbm, pc: usize, _helper: u32) -> Vec<(usize, Dbm)> {
    let mut dbm = dbm_in.clone();

    // MVP ABI model for helper calls:
    // - r0 is return value (clobbered)
    // - r1..r5 are argument regs (treat as clobbered)
    // - r6..r10 preserved (r10 is fp)
    for v in [Var::R0, Var::R1, Var::R2, Var::R3, Var::R4, Var::R5] {
        forget(&mut dbm, v);
    }

    vec![(pc + 1, dbm)]
}

/// Single-step semantic transfer: from (pc, dbm_in) to successors
pub fn transfer_instr(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    instr: &Instr,
) -> Vec<(usize, Dbm)> {
    match instr {
        Instr::MovArg0 { dst } => transfer_mov_arg0(dbm_in, pc, *dst),
        Instr::Alu { width, op, dst, src } => 
            transfer_alu(ctx, dbm_in, pc, *width, *op, *dst, *src),
        Instr::Endian { dst, kind } => 
            transfer_endian(ctx, dbm_in, pc, *dst, *kind),
        Instr::If { width, left, op, right, target } => 
            transfer_if(ctx, dbm_in, pc, *width, *left, *op, *right, *target),
        Instr::Load { size, dst, base, off } => 
            transfer_load(ctx, dbm_in, pc, *size, *dst, *base, *off),
        Instr::Store { size, base, off, src } => 
            transfer_store(ctx, dbm_in, pc, *size, *base, *off, *src),
        Instr::Call { helper } => transfer_call(dbm_in, pc, *helper),
        Instr::Jmp { target } => vec![(*target, dbm_in.clone())],
        Instr::Exit => vec![],
    }
}


pub fn analyze_program(ctx: &ExecContext, prog: &Program, entry_dbm: Dbm) -> Vec<Dbm> {
    let n = prog.instrs.len();
    let mut states: Vec<Option<Dbm>> = vec![None; n];
    let mut worklist = VecDeque::new();

    states[0] = Some(entry_dbm);
    worklist.push_back(0);

    while let Some(pc) = worklist.pop_front() {
        let instr = &prog.instrs[pc];
        let in_dbm = states[pc].as_ref().unwrap();

        println!("=== PC {} ===", pc);
        println!("Instr: {}", instr);

        // 1) Print *input* state to this instruction
        println!("IN:");
        in_dbm.dump_matrix();

        // 2) Compute successors *once* so we can both print and propagate
        let succs = transfer_instr(ctx, in_dbm, pc, instr);

        // 3) Print *output* states for each successor
        for (succ_pc, succ_dbm) in &succs {
            println!("OUT → PC {}:", succ_pc);
            succ_dbm.dump_matrix();
        }

        // 4) Dataflow propagation as before
        for (succ_pc, succ_dbm) in succs {
            if succ_pc >= n {
                continue;
            }
            match &mut states[succ_pc] {
                None => {
                    states[succ_pc] = Some(succ_dbm);
                    worklist.push_back(succ_pc);
                }
                Some(existing) => {
                    let joined = existing.join(&succ_dbm);
                    if !dbm_equals(existing, &joined) {
                        *existing = joined;
                        worklist.push_back(succ_pc);
                    }
                }
            }
        }
    }

    states
        .into_iter()
        .map(|opt| opt.unwrap_or_else(|| Dbm::new(VAR_ENV.len())))
        .collect()
}
