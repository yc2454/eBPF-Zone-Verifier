// src/kernel_semantics.rs

use crate::ast::{AluOp, CmpOp, Instr, Operand, Width, EndianKind};
use crate::dbm::{Dbm, INF};
use crate::domain::REG_ENV;
use crate::exec::ExecContext;
use crate::utils::{clamped_add, clamped_add3};

pub fn inconsistent(dbm: &Dbm) -> bool {
    let n = dbm.dim();
    for i in 0..n {
        if dbm.raw(i, i) < 0 {
            return true;
        }
    }
    false
}

// --- local saturation machinery ---

fn saturate_one_edge(dbm: &mut Dbm, u: usize, v: usize, c: i64) {
    let n = dbm.dim();

    for i in 0..n {
        let diu = dbm.raw(i, u);
        if diu >= INF {
            continue;
        }

        for j in 0..n {
            let dvj = dbm.raw(v, j);
            if dvj >= INF {
                continue;
            }

            let via = clamped_add3(diu, c, dvj);
            if via < dbm.raw(i, j) {
                dbm.set_raw(i, j, via);
            }
        }
    }
}

fn add_edge_and_saturate(dbm: &mut Dbm, u: usize, v: usize, c: i64) {
    if c < dbm.raw(u, v) {
        dbm.set_raw(u, v, c);
        saturate_one_edge(dbm, u, v, c);
    }
}

fn forget_var_by_index(dbm: &mut Dbm, x: usize) {
    let n = dbm.dim();
    for i in 0..n {
        dbm.set_raw(x, i, INF);
        dbm.set_raw(i, x, INF);
    }
    dbm.set_raw(x, x, 0);
}

fn proven_u32_range(dbm: &Dbm, v: crate::domain::Reg, zero: crate::domain::Reg) -> bool {
    // Need: 0 <= v <= 0xffff_ffff
    let vi = REG_ENV.index(v);
    let zi = REG_ENV.index(zero);

    let ub = dbm.raw(vi, zi); // v - 0 <= ub
    let lb = dbm.raw(zi, vi); // 0 - v <= lb  (lb <= 0 => v >= 0)

    ub <= 0xffff_ffff && lb <= 0
}

// --- tiny top-level dispatcher ---

pub fn transfer_one_kernel(
    ctx: &ExecContext,
    pc: usize,
    instr: &Instr,
    pre: &Dbm,
) -> Vec<(usize, Dbm)> {
    match instr {
        Instr::MovArg0 { dst } => transfer_mov_arg0(ctx, pc, *dst, pre),
        Instr::Alu { op, dst, src, width } => 
            transfer_alu(ctx, pc, *op, *width, *dst, *src, pre),
        Instr::Endian { dst, kind } => 
            transfer_endian(ctx, pc, *dst, *kind, pre),
        Instr::If { width, left, op, right, target } => 
            transfer_if(ctx, pc, *width, *left, *op, *right, *target, pre),
        Instr::Jmp { target } => vec![(*target, pre.clone())],
        Instr::Load { dst, .. } => transfer_load(pc, *dst, pre),
        Instr::Store { .. } => vec![(pc + 1, pre.clone())],
        Instr::Call { helper } => transfer_call(pc, *helper, pre),
        Instr::Exit => vec![],
    }
}

// --- per-instruction helpers ---

fn transfer_mov_arg0(ctx: &ExecContext, pc: usize, dst: crate::domain::Reg, pre: &Dbm) -> Vec<(usize, Dbm)> {
    let mut d = pre.clone();
    let x = REG_ENV.index(dst);
    let _zero_i = REG_ENV.index(ctx.zero);

    forget_var_by_index(&mut d, x);

    if inconsistent(&d) { vec![] } else { vec![(pc + 1, d)] }
}

fn transfer_alu(
    ctx: &ExecContext,
    pc: usize,
    op: AluOp,
    width: Width,
    dst: crate::domain::Reg,
    src: Operand,
    pre: &Dbm,
) -> Vec<(usize, Dbm)> {
    match op {
        AluOp::Mov => transfer_mov(ctx, pc, width, dst, src, pre),
        AluOp::Add => transfer_add(ctx, pc, dst, src, pre),
        AluOp::Sub => transfer_sub(ctx, pc, width, dst, src, pre),
        AluOp::And => transfer_and(ctx, pc, width, dst, src, pre),
        AluOp::Shr => transfer_shr(ctx, pc, width, dst, src, pre),
        AluOp::Shl => transfer_shl(pc, dst, pre),
        AluOp::Or  => transfer_or(ctx, pc, width, dst, src, pre),
        AluOp::Arsh => {
            // Arithmetic right shift (sign-propagating).
            // Zones don’t track bit-level sign; modeling this precisely would
            // require case-splitting on sign. MVP: sound but coarse — just forget.
            transfer_forget_dst(pc, dst, pre)
        }
        AluOp::Mul => {
            // Multiplication is nonlinear; we just forget dst.
            transfer_forget_dst(pc, dst, pre)
        }
        AluOp::Mod => {
            // Modulo is nonlinear; we just forget dst.
            transfer_forget_dst(pc, dst, pre)
        }

        // MVP: conservative for the rest
        AluOp::Xor => transfer_forget_dst(pc, dst, pre),
    }
}

fn transfer_sub(
    _ctx: &ExecContext,
    pc: usize,
    _width: Width,
    dst: crate::domain::Reg,
    src: Operand,
    pre: &Dbm,
) -> Vec<(usize, Dbm)> {
    let mut d = pre.clone();
    let x = REG_ENV.index(dst);

    // Kill old info about dst
    forget_var_by_index(&mut d, x);

    match src {
        Operand::Imm(_c) => {
            // dst -= c  ==  dst += (-c)
            // If you already have a transfer_add helper, you could reuse it.
            // Here we just say nothing beyond "dst is some integer".
            // (Optional) You could keep this as pure forget; nothing more to add.
        }
        Operand::Reg(_r) => {
            // dst -= reg: nonlinear; we keep it as "unknown".
        }
    }

    if inconsistent(&d) {
        vec![]
    } else {
        vec![(pc + 1, d)]
    }
}

fn transfer_shr(ctx: &ExecContext, pc: usize, width: Width, dst: crate::domain::Reg, src: Operand, pre: &Dbm) -> Vec<(usize, Dbm)> {
    let mut d = pre.clone();
    let x = REG_ENV.index(dst);
    let z = REG_ENV.index(ctx.zero);

    forget_var_by_index(&mut d, x);

    if let Operand::Imm(k) = src {
        let bits = if width == Width::W32 { 32u32 } else { 64u32 };
        let k = (k as u32).min(bits);

        // 0 <= dst
        add_edge_and_saturate(&mut d, z, x, 0);

        if k < bits {
            let ub: i64 = ((1u128 << (bits - k)) - 1) as i64;
            add_edge_and_saturate(&mut d, x, z, ub);
        } else {
            // shift by >= bits => 0
            add_edge_and_saturate(&mut d, x, z, 0);
            add_edge_and_saturate(&mut d, z, x, 0);
        }
    }

    if inconsistent(&d) { vec![] } else { vec![(pc + 1, d)] }
}

fn transfer_shl(pc: usize, dst: crate::domain::Reg, pre: &Dbm) -> Vec<(usize, Dbm)> {
    let mut d = pre.clone();
    let x = REG_ENV.index(dst);
    forget_var_by_index(&mut d, x);
    if inconsistent(&d) { vec![] } else { vec![(pc + 1, d)] }
}

fn transfer_mov(ctx: &ExecContext, pc: usize, width: Width, dst: crate::domain::Reg, src: Operand, pre: &Dbm) -> Vec<(usize, Dbm)> {
    let zero_i = REG_ENV.index(ctx.zero);
    let mut d = pre.clone();
    let x = REG_ENV.index(dst);
    let n = d.dim();

    forget_var_by_index(&mut d, x);

    match src {
        Operand::Reg(r) => {
            if r == ctx.r10 {
                // dst := r10  ==> offset-from-frame = 0
                add_edge_and_saturate(&mut d, x, zero_i, 0);
                add_edge_and_saturate(&mut d, zero_i, x, 0);
            } else if width == Width::W32 {
                // mov32 reg: can't express low32 copy; stay sound with range bound
                add_edge_and_saturate(&mut d, x, zero_i, 0xffff_ffff);
                add_edge_and_saturate(&mut d, zero_i, x, 0);
            } else {
                // mov64 reg: Copy row/col from src in the *pre* DBM (closed).
                let y = REG_ENV.index(r);
                for i in 0..n {
                    d.set_raw(x, i, pre.raw(y, i)); // x - i
                    d.set_raw(i, x, pre.raw(i, y)); // i - x
                }
                d.set_raw(x, x, 0);
            }
        }
        Operand::Imm(c) => {
            // mov32 imm: u32 then zero-extend
            let c = if width == Width::W32 { (c as u32) as i64 } else { c };

            // dst := c  ==> dst == c
            add_edge_and_saturate(&mut d, x, zero_i, c);
            add_edge_and_saturate(&mut d, zero_i, x, -c);
        }
    }

    if inconsistent(&d) { vec![] } else { vec![(pc + 1, d)] }
}

fn transfer_add(ctx: &ExecContext, pc: usize, dst: crate::domain::Reg, src: Operand, pre: &Dbm) -> Vec<(usize, Dbm)> {
    match src {
        Operand::Imm(imm) => transfer_add_imm(pc, dst, imm, pre),
        Operand::Reg(r) => transfer_add_reg_mvp(ctx, pc, dst, r, pre),
    }
}

fn transfer_or(ctx: &ExecContext, pc: usize, width: Width,
    dst: crate::domain::Reg, src: Operand, pre: &Dbm) -> Vec<(usize, Dbm)> {
    let x = REG_ENV.index(dst);
    let z = REG_ENV.index(ctx.zero);
    let mut d = pre.clone();

    forget_var_by_index(&mut d, x);

    match src {
        Operand::Imm(_mask) => {
            if width == Width::W32 {
                // w_dst |= C : 0 <= dst <= 0xffff_ffff
                add_edge_and_saturate(&mut d, x, z, 0xffff_ffff);
                add_edge_and_saturate(&mut d, z, x, 0);
            }
            // For W64, or reg: nothing more to say beyond forget.
        }
        Operand::Reg(_r) => {
            // Just forget; nothing else.
        }
    }

    if inconsistent(&d) {
        vec![]
    } else {
        vec![(pc + 1, d)]
    }
}

fn transfer_endian(
    ctx: &ExecContext,
    pc: usize,
    dst: crate::domain::Reg,
    kind: EndianKind,
    pre: &Dbm,
) -> Vec<(usize, Dbm)> {
    let mut d = pre.clone();
    let x = REG_ENV.index(dst);
    let z = REG_ENV.index(ctx.zero);

    // Forget old value of dst.
    forget_var_by_index(&mut d, x);

    match kind {
        EndianKind::Be16 => {
            // 0 <= dst <= 0xffff
            add_edge_and_saturate(&mut d, x, z, 0x0000_ffff);
            add_edge_and_saturate(&mut d, z, x, 0);
        }
        EndianKind::Be32 => {
            // 0 <= dst <= 0xffff_ffff
            add_edge_and_saturate(&mut d, x, z, 0xffff_ffff);
            add_edge_and_saturate(&mut d, z, x, 0);
        }
        EndianKind::Be64 => {
            // Byteswap64 doesn't give a useful range; leave dst unconstrained
            // beyond the forget().
        }
    }

    if inconsistent(&d) {
        vec![]
    } else {
        vec![(pc + 1, d)]
    }
}

fn transfer_add_imm(pc: usize, dst: crate::domain::Reg, imm: i64, pre: &Dbm) -> Vec<(usize, Dbm)> {
    let mut d = pre.clone();
    let x = REG_ENV.index(dst);
    let n = d.dim();

    // dst := dst + imm, closure preserved by row/col shift
    for i in 0..n {
        let xv = pre.raw(x, i);
        d.set_raw(x, i, clamped_add(xv, imm));

        let vx = pre.raw(i, x);
        d.set_raw(i, x, clamped_add(vx, -imm));
    }
    d.set_raw(x, x, 0);

    if inconsistent(&d) { vec![] } else { vec![(pc + 1, d)] }
}

fn transfer_add_reg_mvp(ctx: &ExecContext, pc: usize, dst: crate::domain::Reg, src: crate::domain::Reg, pre: &Dbm) -> Vec<(usize, Dbm)> {
    // MVP rule (same as your current):
    // - if dst is provably constant, keep exact relation: dst := src + c
    // - else: forget dst
    let zero_i = REG_ENV.index(ctx.zero);
    let mut d = pre.clone();
    let x = REG_ENV.index(dst);
    let y = REG_ENV.index(src);

    let ub = pre.raw(x, zero_i);
    let lb_neg = pre.raw(zero_i, x);
    let is_const = ub < INF && lb_neg < INF && ub == -lb_neg;

    forget_var_by_index(&mut d, x);

    if is_const {
        let c = ub;
        add_edge_and_saturate(&mut d, x, y, c);
        add_edge_and_saturate(&mut d, y, x, -c);
    }

    if inconsistent(&d) { vec![] } else { vec![(pc + 1, d)] }
}

fn transfer_and(ctx: &ExecContext, pc: usize, width: Width,
    dst: crate::domain::Reg, src: Operand, pre: &Dbm) -> Vec<(usize, Dbm)> {
    // We only model AND with immediate masks for now.
    let zero_i = REG_ENV.index(ctx.zero);
    let mut d = pre.clone();
    let x = REG_ENV.index(dst);

    forget_var_by_index(&mut d, x);

    if let Operand::Imm(mask) = src {
        let mask = if width == Width::W32 { (mask as u32) as i64 } else { mask };
        // sound approximation for unsigned mask:
        // 0 <= dst <= mask
        add_edge_and_saturate(&mut d, x, zero_i, mask);
        add_edge_and_saturate(&mut d, zero_i, x, 0);
    }

    if inconsistent(&d) { vec![] } else { vec![(pc + 1, d)] }
}

fn transfer_forget_dst(pc: usize, dst: crate::domain::Reg, pre: &Dbm) -> Vec<(usize, Dbm)> {
    let mut d = pre.clone();
    let x = REG_ENV.index(dst);
    forget_var_by_index(&mut d, x);
    if inconsistent(&d) { vec![] } else { vec![(pc + 1, d)] }
}

fn transfer_if(
    ctx: &ExecContext,
    pc: usize,
    width: Width,
    left: crate::domain::Reg,
    op: CmpOp,
    right: Operand,
    target: usize,
    pre: &Dbm,
) -> Vec<(usize, Dbm)> {
    // Semantics: if cond true -> goto target else -> fallthrough pc+1
    let zero_i = REG_ENV.index(ctx.zero);
    let l = REG_ENV.index(left);

    // JMP32 compares only low 32 bits. Zones don't model low32(x) relationally.
    // MVP policy:
    // - For Eq/Ne with imm: refine only if left already known in [0, 0xffff_ffff],
    //   in which case low32(left)==k <=> left==k (with k zero-extended).
    // - Otherwise: no refinement, just fork.
    let (op, right) = if width == Width::W32 {
        match (op, right) {
            (CmpOp::Eq,  Operand::Imm(imm))
            | (CmpOp::Ne,  Operand::Imm(imm))
            | (CmpOp::UGe, Operand::Imm(imm))
            | (CmpOp::ULe, Operand::Imm(imm))
            | (CmpOp::UGt, Operand::Imm(imm))
            | (CmpOp::ULt, Operand::Imm(imm)) => {
                if !proven_u32_range(pre, left, ctx.zero) {
                    // Can't safely interpret low32 comparison as full-width; fork.
                    return vec![(target, pre.clone()), (pc + 1, pre.clone())];
                }
                // Normalize imm to zero-extended u32.
                (op, Operand::Imm((imm as u32) as i64))
            }
            _ => {
                // JMP32 with reg RHS, or other ops: fork without refinement.
                return vec![(target, pre.clone()), (pc + 1, pre.clone())];
            }
        }
    } else {
        (op, right)
    };

    let mut out = Vec::new();

    match (op, right) {
        // ======= Eq/Ne immediate (W64, or W32 gated+normalized above) =======
        (CmpOp::Eq, Operand::Imm(imm)) => {
            // then: left == imm
            let mut dt = pre.clone();
            add_edge_and_saturate(&mut dt, l, zero_i, imm);
            add_edge_and_saturate(&mut dt, zero_i, l, -imm);
            if !inconsistent(&dt) { out.push((target, dt)); }

            // else: left != imm  (DBM can't express disequality; no refinement)
            out.push((pc + 1, pre.clone()));
        }

        (CmpOp::Ne, Operand::Imm(imm)) => {
            // then: left != imm  (DBM can't express disequality => no refinement)
            out.push((target, pre.clone()));

            // else: left == imm
            let mut de = pre.clone();
            add_edge_and_saturate(&mut de, l, zero_i, imm);
            add_edge_and_saturate(&mut de, zero_i, l, -imm);
            if !inconsistent(&de) { out.push((pc + 1, de)); }
        }

        // ======= Existing UGe/ULe cases (W64 only in MVP; W32 returns earlier) =======
        (CmpOp::UGe, Operand::Imm(imm)) => {
            // then: left >= imm  <=> 0 - left <= -imm
            let mut dt = pre.clone();
            add_edge_and_saturate(&mut dt, zero_i, l, -imm);
            if !inconsistent(&dt) { out.push((target, dt)); }

            // else: 0 <= left <= imm-1
            let mut de = pre.clone();
            add_edge_and_saturate(&mut de, l, zero_i, imm - 1);
            add_edge_and_saturate(&mut de, zero_i, l, 0);
            if !inconsistent(&de) { out.push((pc + 1, de)); }
        }

        (CmpOp::ULe, Operand::Imm(imm)) => {
            // then: 0 <= left <= imm
            let mut dt = pre.clone();
            add_edge_and_saturate(&mut dt, l, zero_i, imm);
            add_edge_and_saturate(&mut dt, zero_i, l, 0);
            if !inconsistent(&dt) { out.push((target, dt)); }

            // else: left >= imm+1  <=> 0 - left <= -(imm+1)
            let mut de = pre.clone();
            add_edge_and_saturate(&mut de, zero_i, l, -(imm + 1));
            if !inconsistent(&de) { out.push((pc + 1, de)); }
        }

        // ---------- left > imm ----------
        (CmpOp::UGt, Operand::Imm(imm)) => {
            // then: left > imm  => left >= imm+1  <=> 0 - left <= -(imm+1)
            let mut dt = pre.clone();
            add_edge_and_saturate(&mut dt, zero_i, l, -(imm + 1));
            if !inconsistent(&dt) { out.push((target, dt)); }

            // else: left <= imm, and 0 <= left
            let mut de = pre.clone();
            add_edge_and_saturate(&mut de, l, zero_i, imm);
            add_edge_and_saturate(&mut de, zero_i, l, 0);
            if !inconsistent(&de) { out.push((pc + 1, de)); }
        }

        // ---------- left < imm ----------
        (CmpOp::ULt, Operand::Imm(imm)) => {
            // then: left < imm  => 0 <= left <= imm-1
            let mut dt = pre.clone();
            add_edge_and_saturate(&mut dt, l, zero_i, imm - 1);
            add_edge_and_saturate(&mut dt, zero_i, l, 0);
            if !inconsistent(&dt) { out.push((target, dt)); }

            // else: left >= imm  <=> 0 - left <= -imm
            let mut de = pre.clone();
            add_edge_and_saturate(&mut de, zero_i, l, -imm);
            if !inconsistent(&de) { out.push((pc + 1, de)); }
        }

        (CmpOp::UGe, Operand::Reg(r)) => {
            let rr = REG_ENV.index(r);

            // then: left >= r  <=> r - left <= 0
            let mut dt = pre.clone();
            add_edge_and_saturate(&mut dt, rr, l, 0);
            if !inconsistent(&dt) { out.push((target, dt)); }

            // else: left < r  <=> left - r <= -1
            let mut de = pre.clone();
            add_edge_and_saturate(&mut de, l, rr, -1);
            if !inconsistent(&de) { out.push((pc + 1, de)); }
        }

        (CmpOp::ULe, Operand::Reg(r)) => {
            let rr = REG_ENV.index(r);

            // then: left <= r  <=> left - r <= 0
            let mut dt = pre.clone();
            add_edge_and_saturate(&mut dt, l, rr, 0);
            if !inconsistent(&dt) { out.push((target, dt)); }

            // else: left > r  <=> r - left <= -1
            let mut de = pre.clone();
            add_edge_and_saturate(&mut de, rr, l, -1);
            if !inconsistent(&de) { out.push((pc + 1, de)); }
        }

        // ---------- left > r ----------
        (CmpOp::UGt, Operand::Reg(r)) => {
            let rr = REG_ENV.index(r);

            // then: left > r  <=> r - left <= -1
            let mut dt = pre.clone();
            add_edge_and_saturate(&mut dt, rr, l, -1);
            if !inconsistent(&dt) { out.push((target, dt)); }

            // else: left <= r  <=> left - r <= 0
            let mut de = pre.clone();
            add_edge_and_saturate(&mut de, l, rr, 0);
            if !inconsistent(&de) { out.push((pc + 1, de)); }
        }

        // ---------- left < r ----------
        (CmpOp::ULt, Operand::Reg(r)) => {
            let rr = REG_ENV.index(r);

            // then: left < r  <=> left - r <= -1
            let mut dt = pre.clone();
            add_edge_and_saturate(&mut dt, l, rr, -1);
            if !inconsistent(&dt) { out.push((target, dt)); }

            // else: left >= r  <=> r - left <= 0
            let mut de = pre.clone();
            add_edge_and_saturate(&mut de, rr, l, 0);
            if !inconsistent(&de) { out.push((pc + 1, de)); }
        }

        // MVP: other compares not yet refined, just fork
        _ => {
            out.push((target, pre.clone()));
            out.push((pc + 1, pre.clone()));
        }
    }

    out
}

fn transfer_call(pc: usize, _helper: u32, pre: &Dbm) -> Vec<(usize, Dbm)> {
    let mut d = pre.clone();

    // Same MVP ABI model as userspace:
    // clobber r0..r5, preserve r6..r10.
    for v in [crate::domain::Reg::R0,
              crate::domain::Reg::R1,
              crate::domain::Reg::R2,
              crate::domain::Reg::R3,
              crate::domain::Reg::R4,
              crate::domain::Reg::R5] {
        let idx = REG_ENV.index(v);
        forget_var_by_index(&mut d, idx);
    }

    if inconsistent(&d) { vec![] } else { vec![(pc + 1, d)] }
}

fn transfer_load(pc: usize, dst: crate::domain::Reg, pre: &Dbm) -> Vec<(usize, Dbm)> {
    // Local transfer does not check memory safety.
    // Effect on registers: dst becomes unknown.
    let mut d = pre.clone();
    let x = REG_ENV.index(dst);
    forget_var_by_index(&mut d, x);
    if inconsistent(&d) { vec![] } else { vec![(pc + 1, d)] }
}
