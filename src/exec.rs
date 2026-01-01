// src/exec.rs
use std::collections::VecDeque;

use crate::ast::{AluOp, CmpOp, Instr, MemSize, Operand, Program, Width, EndianKind};
use crate::dbm::Dbm;
use crate::domain::{
    Reg, REG_ENV,
    // assignment / forget
    assign_eq, assign_zero,
    assign_add_imm, assign_add_reg,
    assign_and_mask, assign_mul_imm,
    forget,
    // assume / guards
    assume_ge_const, assume_le_const, assume_less_than, assume_eq_const,
    assume_ge_var, assume_le_var, assume_gt_var, assume_le_var_plus_const,
    // new: register types
    RegType, RegTypeState, reg_to_index, join_reg_type,
};
use crate::utils::{dbm_equals, load_program_from_elf};
use crate::stats::AnalysisStats;

#[derive(Clone, Copy)]
pub struct ExecContext {
    pub zero: Reg,
    pub r10: Reg,
    pub stack_min: i64,
    pub stack_max: i64,
}

/// Is v provably in [0, 0xffffffff] as a 32-bit unsigned value?
fn proven_u32_range(dbm: &Dbm, v: Reg, zero: Reg) -> bool {
    // requires: (v - 0) <= 0xffff_ffff  AND  (0 - v) <= 0
    let vi = REG_ENV.index(v);
    let zi = REG_ENV.index(zero);
    let ub = dbm.raw(vi, zi); // v - 0
    let lb = dbm.raw(zi, vi); // 0 - v  (<= 0 means v >= 0)
    ub <= 0xffff_ffff && lb <= 0
}

fn transfer_mov_arg0(dbm_in: &Dbm, pc: usize, dst: Reg) -> Vec<(usize, Dbm)> {
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
    dst: Reg,
    src: Operand,
    stats: &mut AnalysisStats,
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
                    forget(&mut dbm, dst);
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

        AluOp::Arsh => {
            // Arithmetic right shift (sign-propagating).
            // Zones don’t track bit-level sign; modeling this precisely would
            // require case-splitting on sign. MVP: sound but coarse — just forget.
            forget(&mut dbm, dst);
        }

        AluOp::Mul => {
            match src {
                Operand::Imm(c) => {
                    // Try to keep an interval when multiplying by constant.
                    assign_mul_imm(&mut dbm, dst, c, ctx.zero);
                }
                Operand::Reg(_r) => {
                    // dst *= reg: product of two unknowns; interval logic gets messy
                    // and likely not worth it for now. Stay sound and conservative.
                    forget(&mut dbm, dst);
                }
            }
        }

        AluOp::Mod => {
            match src {
                Operand::Imm(c) => {
                    if c <= 0 {
                        // avoid divide-by-zero / negative nonsense: just forget
                        forget(&mut dbm, dst);
                    } else {
                        // dst %= c  ⇒  0 <= dst <= c-1
                        forget(&mut dbm, dst);
                        assume_ge_const(&mut dbm, dst, ctx.zero, 0);
                        assume_le_const(&mut dbm, dst, ctx.zero, c - 1);
                    }
                }
                Operand::Reg(_r) => {
                    // dst %= reg: result in [0, reg-1], but reg is unknown.
                    // To stay simple & sound, just forget dst for now.
                    forget(&mut dbm, dst);
                }
            }
        }

        // Not needed yet; keep sound default
        AluOp::Xor => {
            forget(&mut dbm, dst);
        }
    }

    if dbm.is_inconsistent() {
        println!("ERROR: ");
        println!("ALU transfer led to inconsistent state at pc {}", pc);
        dbm.dump_matrix();
        stats.mark_dbm_inconsistent();
        vec![]
    } else {
        vec![(pc + 1, dbm)]
    }
}

fn transfer_endian(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    dst: Reg,
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
    left: Reg,
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
    dst: Reg,
    base: Reg,
    base_type: RegType,
    off: i16,
    stats: &mut AnalysisStats,
) -> Vec<(usize, Dbm)> {
    use RegType::*;

    let mut dbm = dbm_in.clone();

    match base_type {
        PtrToStack => {
            // Old stack logic, unchanged
            let (lo, hi) = crate::domain::get_bounds(dbm_in, base, ctx.zero);

            let eff_lo = lo.map(|x| x + off as i64);
            let eff_hi = hi.map(|x| x + off as i64);

            let stack_ok = match (eff_lo, eff_hi) {
                (Some(l), Some(h)) => match size {
                    MemSize::U8  => l >= ctx.stack_min && h <= ctx.stack_max,
                    MemSize::U16 => l >= ctx.stack_min && h + 1 <= ctx.stack_max,
                    MemSize::U32 => l >= ctx.stack_min && h + 3 <= ctx.stack_max,
                    MemSize::U64 => l >= ctx.stack_min && h + 7 <= ctx.stack_max,
                },
                _ => false,
            };

            if stack_ok {
                // Proven-safe stack load.
                // (Optional debug: check_stack_load(ctx, dbm_in, base);)
                forget(&mut dbm, dst);
                return vec![(pc + 1, dbm)];
            }

            println!(
                "Stack load not proven safe at pc {}: base {:?}+{}",
                pc, base, off
            );
            stats.mark_unsafe_load();
            // Model result as unknown scalar; still continue for now.
            forget(&mut dbm, dst);
            vec![(pc + 1, dbm)]
        }

        PtrToCtx => {
            // This is a context pointer like kernel PTR_TO_CTX.
            // We don't yet model the exact layout (is_valid_access),
            // but we *know* it's not a stack access. For now:
            //  - treat it as allowed
            //  - do NOT mark unsafe_load
            //  - result is an unknown scalar
            println!(
                "CTX load at pc {}: dst {:?} = *(...)(base {:?}+{})",
                pc, dst, base, off
            );
            forget(&mut dbm, dst);
            vec![(pc + 1, dbm)]
        }

        _ => {
            // Any other base type: non-stack, non-ctx pointer (or scalar / unknown).
            // Keep previous "non-stack load" behavior: mark as unsafe.
            println!(
                "Non-stack, non-ctx load at pc {} from base {:?}+{} (reg_type={:?})",
                pc, base, off, base_type
            );
            stats.mark_unsafe_load();

            forget(&mut dbm, dst);
            vec![(pc + 1, dbm)]
        }
    }
}

fn transfer_store(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    size: MemSize,
    base: Reg,
    _base_type: RegType,
    off: i16,
    _src: Reg,
    stats: &mut AnalysisStats,
) -> Vec<(usize, Dbm)> {
    let (lo, hi) = crate::domain::get_bounds(dbm_in, base, ctx.zero);
    let eff_lo = lo.map(|x| x + off as i64);
    let eff_hi = hi.map(|x| x + off as i64);

    // Take store width into account
    let bytes: i64 = match size {
        MemSize::U8  => 1,
        MemSize::U16 => 2,
        MemSize::U32 => 4,
        MemSize::U64 => 8,
    };

    let is_stack_store = match (eff_lo, eff_hi) {
        (Some(l), Some(h)) => {
            // We want [l, h + bytes - 1] fully inside [stack_min, stack_max]
            let last = h + (bytes - 1);
            l >= ctx.stack_min && last <= ctx.stack_max
        }
        _ => false,
    };

    if is_stack_store {
        // Verified stack store: this is the one we actually certify.
        // No change to DBM (we don't track memory), just continue.
        return vec![(pc + 1, dbm_in.clone())];
    }

    // Otherwise: treat as non-stack store (ctx, map, packet, heap, etc.)
    // We don't try to prove anything about it in this certificate.
    println!(
        "Non-stack store at pc {}: {:?} to base {:?}+{} (bounds {:?}..{:?})",
        pc, size, base, off, eff_lo, eff_hi
    );
    stats.mark_unsafe_store();

    vec![(pc + 1, dbm_in.clone())]
}

fn transfer_call(dbm_in: &Dbm, pc: usize, _helper: u32) -> Vec<(usize, Dbm)> {
    let mut dbm = dbm_in.clone();

    // MVP ABI model for helper calls:
    // - r0 is return value (clobbered)
    // - r1..r5 are argument regs (treat as clobbered)
    // - r6..r10 preserved (r10 is fp)
    for v in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
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
    stats: &mut AnalysisStats,
    reg_types: &RegTypeState,
) -> Vec<(usize, Dbm)> {
    match instr {
        Instr::MovArg0 { dst } =>
            transfer_mov_arg0(dbm_in, pc, *dst),
        Instr::Alu { width, op, dst, src } =>
            transfer_alu(ctx, dbm_in, pc, *width, *op, *dst, *src, stats),
        Instr::Endian { dst, kind } =>
            transfer_endian(ctx, dbm_in, pc, *dst, *kind),
        Instr::If { width, left, op, right, target } =>
            transfer_if(ctx, dbm_in, pc, *width, *left, *op, *right, *target),
        Instr::Load { size, dst, base, off } =>
            {
                let base_ty = reg_types.get(*base);
                transfer_load(ctx, dbm_in, pc, *size, *dst, *base, base_ty, *off, stats)
            },
        Instr::Store { size, base, off, src } =>
            {
                let base_ty = reg_types.get(*base);
                transfer_store(ctx, dbm_in, pc, *size, *base, base_ty, *off, *src, stats)
            },
        Instr::Call { helper } =>
            transfer_call(dbm_in, pc, *helper),
        Instr::Jmp { target } =>
            vec![(*target, dbm_in.clone())],
        Instr::Exit =>
            vec![],
    }
}

/// Track register types (RegType) alongside DBM state.
/// This mirrors the kernel's bpf_reg_type tracking conceptually.
fn update_reg_types_for_instr(
    _ctx: &ExecContext,
    instr: &Instr,
    types: &mut RegTypeState,
) {
    use Instr::*;
    use RegType::*;

    match instr {
        MovArg0 { dst } => {
            types.set(*dst, ScalarValue);
        }

        Alu { op, dst, src, .. } => {
            use crate::ast::AluOp;
            use RegType::*;

            let old_ty = types.get(*dst);

            match op {
                AluOp::Mov => {
                    match src {
                        Operand::Reg(r) => {
                            types.set(*dst, types.get(*r));
                        }
                        Operand::Imm(_) => {
                            types.set(*dst, ScalarValue);
                        }
                    }
                }

                AluOp::Add | AluOp::Sub => {
                    // Model pointer arithmetic:
                    //
                    // - pointer + scalar  => pointer   (same kind)
                    // - pointer + pointer => we give up (ScalarValue)
                    // - scalar + anything => ScalarValue
                    match src {
                        Operand::Imm(_) => {
                            // dst = dst +/- imm
                            if old_ty.is_pointer() {
                                // keep pointer type
                                // e.g., PtrToStack stays PtrToStack, PtrToCtx stays PtrToCtx
                            } else {
                                types.set(*dst, ScalarValue);
                            }
                        }
                        Operand::Reg(r) => {
                            let src_ty = types.get(*r);
                            if old_ty.is_pointer() && !src_ty.is_pointer() {
                                // pointer +/- scalar ⇒ still pointer
                                // (kernel also insists src must be SCALAR_VALUE, but
                                // for now we approximate: "not a pointer" = scalar-ish)
                            } else if !old_ty.is_pointer() {
                                // scalar +/- anything ⇒ scalar
                                types.set(*dst, ScalarValue);
                            } else {
                                // pointer +/- pointer ⇒ we give up
                                types.set(*dst, ScalarValue);
                            }
                        }
                    }
                }

                // Bitwise ops, mul, mod, shifts etc. typically break pointer structure.
                _ => {
                    types.set(*dst, ScalarValue);
                }
            }
        }

        Endian { dst, .. } => {
            types.set(*dst, ScalarValue);
        }

        If { .. } => {
            // No direct effect on types.
        }

        Load { dst, .. } => {
            // For now: loads always produce scalars unless we special-case helpers later.
            types.set(*dst, ScalarValue);
        }

        Store { .. } => {
            // Stores don't change register types.
        }

        Call { .. } => {
            // Simple ABI model: r0..r5 clobbered as unknown, r6..r10 preserved.
            for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
                types.set(r, Unknown);
            }
        }

        Jmp { .. } | Exit => {
            // No direct effect on types.
        }
    }
}

pub fn analyze_program(
    ctx: &ExecContext,
    prog: &Program,
    entry_dbm: Dbm,
    stats: &mut AnalysisStats,
) -> Vec<Dbm> {
    let n = prog.instrs.len();

    // Numeric state per PC
    let mut states: Vec<Option<Dbm>> = vec![None; n];
    // Register-type state per PC
    let mut type_states: Vec<Option<RegTypeState>> = vec![None; n];

    // Entry register types, loosely mirroring kernel:
    let mut entry_types = RegTypeState::new_not_init();

    // R1 is PTR_TO_CTX at entry
    entry_types.set(Reg::R1, RegType::PtrToCtx);

    // R10 is frame pointer / stack base
    entry_types.set(ctx.r10, RegType::PtrToStack);

    // R0 as scalar return value placeholder
    entry_types.set(Reg::R0, RegType::ScalarValue);

    let mut worklist = VecDeque::new();

    states[0] = Some(entry_dbm);
    type_states[0] = Some(entry_types);
    worklist.push_back(0);

    while let Some(pc) = worklist.pop_front() {
        if stats.abort {
            println!("Analysis aborted due to previous errors.");
            break;
        }

        let instr = &prog.instrs[pc];
        let in_dbm = states[pc].as_ref().unwrap();
        let in_types = type_states[pc].expect("type state must exist when DBM state exists");

        println!("=== PC {} ===", pc);
        println!("Instr: {}", instr);

        // 1) Print *input* DBM state
        println!("IN:");
        in_dbm.dump_matrix();

        // 1b) Print *input* register types
        println!("RegTypes IN:");
        for (r, ty) in in_types.iter_regs() {
            println!("  {:>3}: {:?}", r.name(), ty);
        }
        println!();

        // 2) Numeric transfer: note we pass &in_types into transfer_instr
        let succs = transfer_instr(ctx, in_dbm, pc, instr, stats, &in_types);

        if stats.abort {
            println!("Analysis aborted due to previous errors.");
            break;
        }

        // 3) Print *output* numeric states for each successor
        for (succ_pc, succ_dbm) in &succs {
            println!("OUT → PC {}:", succ_pc);
            succ_dbm.dump_matrix();
        }

        // 4) Dataflow propagation: DBM + RegType
        for (succ_pc, succ_dbm) in succs {
            if succ_pc >= n {
                continue;
            }

            // Compute edge types after this instruction starting from in_types.
            let mut edge_types = in_types;
            update_reg_types_for_instr(ctx, instr, &mut edge_types);

            match (&mut states[succ_pc], &mut type_states[succ_pc]) {
                (slot_dbm @ None, slot_types @ None) => {
                    // First time reaching this pc
                    *slot_dbm = Some(succ_dbm);
                    *slot_types = Some(edge_types);
                    worklist.push_back(succ_pc);
                }
                (Some(existing_dbm), Some(existing_types)) => {
                    let joined_dbm = existing_dbm.join(&succ_dbm);
                    let dbm_changed = !dbm_equals(existing_dbm, &joined_dbm);
                    *existing_dbm = joined_dbm;

                    let types_changed = existing_types.join_in_place(&edge_types);

                    if dbm_changed || types_changed {
                        worklist.push_back(succ_pc);
                    }
                }
                _ => {
                    // Invariant: DBM and type state presence must match.
                    panic!(
                        "Inconsistent state: DBM and type state presence differ at pc {}",
                        succ_pc
                    );
                }
            }
        }
    }

    states
        .into_iter()
        .map(|opt| opt.unwrap_or_else(|| Dbm::new(REG_ENV.len())))
        .collect()
}


pub fn analyze_program_for_file(
    path: &std::path::Path,
) -> Result<AnalysisStats, Box<dyn std::error::Error>> {
    let prog = load_program_from_elf(
        path.to_str().ok_or("Invalid path")?,
        ".text",
    );

    let mut stats = AnalysisStats::default();

    let ctx = ExecContext {
        zero: Reg::Zero,
        r10: Reg::R10,
        stack_min: -512,
        stack_max: -1,
    };

    let mut entry = Dbm::new(REG_ENV.len());
    crate::domain::assign_zero(&mut entry, ctx.r10, ctx.zero);

    analyze_program(&ctx, &prog, entry, &mut stats);

    Ok(stats)
}
