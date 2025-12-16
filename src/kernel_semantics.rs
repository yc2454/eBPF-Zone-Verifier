use crate::ast::Instr;
use crate::dbm::{Dbm, INF};
use crate::domain::{VAR_ENV};
use crate::exec::ExecContext;
use crate::utils::{dbm_add, dbm_add3};

pub fn inconsistent(dbm: &Dbm) -> bool {
    let n = dbm.dim();
    for i in 0..n {
        if dbm.raw(i, i) < 0 {
            return true;
        }
    }
    false
}

// assumes dbm is closed before adding u - v <= c
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

            let via = dbm_add3(diu, c, dvj);

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

// local transfer:
// - assumes `pre` is closed (certificate guarantee)
// - O(n^2) saturation when adding a constraint edge
pub fn transfer_one_kernel(
    ctx: &ExecContext,
    pc: usize,
    instr: &Instr,
    pre: &Dbm,
) -> Vec<(usize, Dbm)> {
    use Instr::*;
    let mut out = Vec::new();

    let zero_i = VAR_ENV.index(ctx.zero);

    match *instr {
        MovArg0 { dst } => {
            let mut d = pre.clone();
            let x = VAR_ENV.index(dst);
            forget_var_by_index(&mut d, x);
            if !inconsistent(&d) {
                out.push((pc + 1, d));
            }
        }

        MovReg { dst, src } => {
            let mut d = pre.clone();
            let x = VAR_ENV.index(dst);
            let y = VAR_ENV.index(src);
            let n = d.dim();

            // forget dst
            forget_var_by_index(&mut d, x);

            if src == ctx.r10 {
                // dst := r10  ==> dst offset-from-frame = 0
                // encode dst == 0:
                // dst - 0 <= 0  AND  0 - dst <= 0
                add_edge_and_saturate(&mut d, x, zero_i, 0);
                add_edge_and_saturate(&mut d, zero_i, x, 0);
            } else {
                // dst := src, preserve closure by copying row/col from src
                for i in 0..n {
                    d.set_raw(x, i, pre.raw(y, i));
                    d.set_raw(i, x, pre.raw(i, y));
                }
                d.set_raw(x, x, 0);
            }

            if !inconsistent(&d) {
                out.push((pc + 1, d));
            }
        }

        AddImm { dst, imm } => {
            let mut d = pre.clone();
            let x = VAR_ENV.index(dst);
            let n = d.dim();

            // dst := dst + imm, closure preserved by row/col shift
            for i in 0..n {
                let xv = pre.raw(x, i);
                d.set_raw(x, i, dbm_add(xv, imm));
                let vx = pre.raw(i, x);
                d.set_raw(i, x, dbm_add(vx, -imm));
            }
            d.set_raw(x, x, 0);

            if !inconsistent(&d) {
                out.push((pc + 1, d));
            }
        }

        AddReg { dst, src } => {
            // MVP behavior: exact only if dst is provably constant, else forget dst
            let mut d = pre.clone();
            let x = VAR_ENV.index(dst);
            let y = VAR_ENV.index(src);

            let ub = pre.raw(x, zero_i);
            let lb_neg = pre.raw(zero_i, x);
            let is_const = ub < INF && lb_neg < INF && ub == -lb_neg;

            forget_var_by_index(&mut d, x);

            if is_const {
                let c = ub;
                add_edge_and_saturate(&mut d, x, y, c);   // dst - src <= c
                add_edge_and_saturate(&mut d, y, x, -c);  // src - dst <= -c
            }

            if !inconsistent(&d) {
                out.push((pc + 1, d));
            }
        }

        AndImmMask { dst, mask } => {
            let mut d = pre.clone();
            let x = VAR_ENV.index(dst);

            forget_var_by_index(&mut d, x);

            add_edge_and_saturate(&mut d, x, zero_i, mask.into()); // dst <= mask
            add_edge_and_saturate(&mut d, zero_i, x, 0);    // dst >= 0

            if !inconsistent(&d) {
                out.push((pc + 1, d));
            }
        }

        Instr::IfUgeImm { reg, imm, target } => {
            // Unsigned: then reg >= imm, else 0 <= reg <= imm-1
            let r = VAR_ENV.index(reg);

            // then branch: reg >= imm  <=> 0 - reg <= -imm
            let mut dt = pre.clone();
            add_edge_and_saturate(&mut dt, zero_i, r, -imm);
            if !inconsistent(&dt) {
                out.push((target, dt));
            }

            // else branch: reg <= imm-1 AND reg >= 0
            let mut de = pre.clone();
            add_edge_and_saturate(&mut de, r, zero_i, imm - 1);
            add_edge_and_saturate(&mut de, zero_i, r, 0);
            if !inconsistent(&de) {
                out.push((pc + 1, de));
            }
        }

        LoadStackU8 { .. } => {
            out.push((pc + 1, pre.clone()));
        }

        Exit => {},

        _ => {
            panic!("Unsupported instruction in kernel-sim: {:?}", instr);
        }
    }

    out
}
