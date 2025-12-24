// src/kernel_semantics.rs

use crate::ast::{AluOp, CmpOp, Instr, Operand, Width};
use crate::dbm::{Dbm, INF};
use crate::domain::VAR_ENV;
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

// --- tiny top-level dispatcher ---

pub fn transfer_one_kernel(
    ctx: &ExecContext,
    pc: usize,
    instr: &Instr,
    pre: &Dbm,
) -> Vec<(usize, Dbm)> {
    match instr {
        Instr::MovArg0 { dst } => transfer_mov_arg0(ctx, pc, *dst, pre),
        Instr::Alu { op, dst, src, width } => transfer_alu(ctx, pc, *op, *width, *dst, *src, pre),
        Instr::If { left, op, right, target } => transfer_if(ctx, pc, *left, *op, *right, *target, pre),
        Instr::Load { dst, .. } => transfer_load(pc, *dst, pre),
        Instr::Store { .. } => vec![(pc + 1, pre.clone())],
        Instr::Exit => vec![],
    }
}

// --- per-instruction helpers ---

fn transfer_mov_arg0(ctx: &ExecContext, pc: usize, dst: crate::domain::Var, pre: &Dbm) -> Vec<(usize, Dbm)> {
    let mut d = pre.clone();
    let x = VAR_ENV.index(dst);
    let _zero_i = VAR_ENV.index(ctx.zero);

    forget_var_by_index(&mut d, x);

    if inconsistent(&d) { vec![] } else { vec![(pc + 1, d)] }
}

fn transfer_alu(
    ctx: &ExecContext,
    pc: usize,
    op: AluOp,
    width: Width,
    dst: crate::domain::Var,
    src: Operand,
    pre: &Dbm,
) -> Vec<(usize, Dbm)> {
    match op {
        AluOp::Mov => transfer_mov(ctx, pc, width, dst, src, pre),
        AluOp::Add => transfer_add(ctx, pc, dst, src, pre),
        AluOp::And => transfer_and(ctx, pc, dst, src, pre),

        // MVP: conservative for the rest
        AluOp::Sub | AluOp::Or | AluOp::Xor => transfer_forget_dst(pc, dst, pre),
    }
}

fn transfer_mov(ctx: &ExecContext, pc: usize, width: Width, dst: crate::domain::Var, src: Operand, pre: &Dbm) -> Vec<(usize, Dbm)> {
    let zero_i = VAR_ENV.index(ctx.zero);
    let mut d = pre.clone();
    let x = VAR_ENV.index(dst);
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
                let y = VAR_ENV.index(r);
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

fn transfer_add(ctx: &ExecContext, pc: usize, dst: crate::domain::Var, src: Operand, pre: &Dbm) -> Vec<(usize, Dbm)> {
    match src {
        Operand::Imm(imm) => transfer_add_imm(pc, dst, imm, pre),
        Operand::Reg(r) => transfer_add_reg_mvp(ctx, pc, dst, r, pre),
    }
}

fn transfer_add_imm(pc: usize, dst: crate::domain::Var, imm: i64, pre: &Dbm) -> Vec<(usize, Dbm)> {
    let mut d = pre.clone();
    let x = VAR_ENV.index(dst);
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

fn transfer_add_reg_mvp(ctx: &ExecContext, pc: usize, dst: crate::domain::Var, src: crate::domain::Var, pre: &Dbm) -> Vec<(usize, Dbm)> {
    // MVP rule (same as your current):
    // - if dst is provably constant, keep exact relation: dst := src + c
    // - else: forget dst
    let zero_i = VAR_ENV.index(ctx.zero);
    let mut d = pre.clone();
    let x = VAR_ENV.index(dst);
    let y = VAR_ENV.index(src);

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

fn transfer_and(ctx: &ExecContext, pc: usize, dst: crate::domain::Var, src: Operand, pre: &Dbm) -> Vec<(usize, Dbm)> {
    // We only model AND with immediate masks for now.
    let zero_i = VAR_ENV.index(ctx.zero);
    let mut d = pre.clone();
    let x = VAR_ENV.index(dst);

    forget_var_by_index(&mut d, x);

    if let Operand::Imm(mask) = src {
        // sound approximation for unsigned mask:
        // 0 <= dst <= mask
        add_edge_and_saturate(&mut d, x, zero_i, mask);
        add_edge_and_saturate(&mut d, zero_i, x, 0);
    }

    if inconsistent(&d) { vec![] } else { vec![(pc + 1, d)] }
}

fn transfer_forget_dst(pc: usize, dst: crate::domain::Var, pre: &Dbm) -> Vec<(usize, Dbm)> {
    let mut d = pre.clone();
    let x = VAR_ENV.index(dst);
    forget_var_by_index(&mut d, x);
    if inconsistent(&d) { vec![] } else { vec![(pc + 1, d)] }
}

fn transfer_if(
    ctx: &ExecContext,
    pc: usize,
    left: crate::domain::Var,
    op: CmpOp,
    right: Operand,
    target: usize,
    pre: &Dbm,
) -> Vec<(usize, Dbm)> {
    // In your AST: If { left, op, right, target }
    // Semantics: if cond true -> goto target else -> fallthrough pc+1
    let zero_i = VAR_ENV.index(ctx.zero);
    let l = VAR_ENV.index(left);

    let mut out = Vec::new();

    match (op, right) {
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

        (CmpOp::UGe, Operand::Reg(r)) => {
            let rr = VAR_ENV.index(r);

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
            let rr = VAR_ENV.index(r);

            // then: left <= r  <=> left - r <= 0
            let mut dt = pre.clone();
            add_edge_and_saturate(&mut dt, l, rr, 0);
            if !inconsistent(&dt) { out.push((target, dt)); }

            // else: left > r  <=> r - left <= -1
            let mut de = pre.clone();
            add_edge_and_saturate(&mut de, rr, l, -1);
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

fn transfer_load(pc: usize, dst: crate::domain::Var, pre: &Dbm) -> Vec<(usize, Dbm)> {
    // Local transfer does not check memory safety.
    // Effect on registers: dst becomes unknown.
    let mut d = pre.clone();
    let x = VAR_ENV.index(dst);
    forget_var_by_index(&mut d, x);
    if inconsistent(&d) { vec![] } else { vec![(pc + 1, d)] }
}
