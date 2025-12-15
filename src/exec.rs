// src/exec.rs
use std::collections::VecDeque;

use crate::ast::{Instr, Program};
use crate::dbm::Dbm;
use crate::domain::{
    Var,
    VAR_ENV,
    assign_eq,
    assign_add_const,
    assign_zero,
    assume_less_than,
    assume_ge_const,
    assign_add,
    add_imm
};

pub struct ExecContext {
    pub zero: Var,
    pub r10: Var,
    pub stack_min: i64,
    pub stack_max: i64,
}

fn dbm_equals(a: &Dbm, b: &Dbm) -> bool {
    if a.num_vars() != b.num_vars() {
        return false;
    }
    for i in 0..a.num_vars() {
        for j in 0..a.num_vars() {
            if a.get_idx(i, j) != b.get_idx(i, j) {
                return false;
            }
        }
    }
    true
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

/// Single-step semantic transfer: from (pc, dbm_in) to successors
fn transfer_instr(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    instr: &Instr,
) -> Vec<(usize, Dbm)> {
    use Instr::*;
    let mut out = Vec::new();

    match *instr {
        MovArg0 { dst } => {
            let mut dbm = dbm_in.clone();
            dbm.forget_var(dst);
            dbm.close();
            out.push((pc + 1, dbm));
        }

        MovReg { dst, src } => {
            let mut dbm = dbm_in.clone();
            if src == ctx.r10 {
                // dst = r10  ⇒ offset relative to frame is 0
                assign_zero(&mut dbm, dst, ctx.zero);
            } else {
                assign_eq(&mut dbm, dst, src);
            }
            out.push((pc + 1, dbm));
        }

        AddImm { dst, imm } => {
            let mut dbm = dbm_in.clone();
            add_imm(&mut dbm, dst, imm);
            out.push((pc + 1, dbm));
        }

        AddReg { dst, src } => {
            let mut dbm = dbm_in.clone();

            // generic x += y is *not* in zones, but if old x is constant c
            // we can rewrite as x := y + c.
            if let Some((lb, ub)) = dbm.var_bounds(dst, ctx.zero) {
                if lb == ub {
                    let c = lb;
                    assign_add_const(&mut dbm, dst, src, c);
                } else {
                    println!(
                        "Warning: AddReg on {} with non-constant old value; ignoring.",
                        dst.name()
                    );
                }
            } else {
                println!(
                    "Warning: AddReg on {} with unknown old value; ignoring.",
                    dst.name()
                );
            }

            out.push((pc + 1, dbm));
        }

        AddRegReg { dst, src1, src2 } => {
            let mut dbm = dbm_in.clone();
            assign_add(&mut dbm, dst, src1, src2, ctx.zero);
            out.push((pc + 1, dbm));
        }

        Instr::IfUgeImm { reg, imm, target } => {
            // then: reg >= imm
            let mut dbm_then = dbm_in.clone();
            assume_ge_const(&mut dbm_then, reg, ctx.zero, imm);
            if !dbm_then.is_inconsistent() {
                out.push((target, dbm_then));
            }

            // else: 0 <= reg < imm
            let mut dbm_else = dbm_in.clone();
            assume_less_than(&mut dbm_else, reg, ctx.zero, imm); // reg <= imm - 1
            assume_ge_const(&mut dbm_else, reg, ctx.zero, 0);    // reg >= 0
            if !dbm_else.is_inconsistent() {
                out.push((pc + 1, dbm_else));
            }
        }

        AndImmMask { dst, mask } => {
            let mut dbm = dbm_in.clone();
            let ub = mask as i64;

            // 0 <= dst
            assume_ge_const(&mut dbm, dst, ctx.zero, 0);
            // dst <= mask (encoded as dst < mask+1)
            assume_less_than(&mut dbm, dst, ctx.zero, ub + 1);

            out.push((pc + 1, dbm));
        }

        LoadStackU8 { base } => {
            let dbm = dbm_in.clone();
            check_stack_load(ctx, &dbm, base);
            out.push((pc + 1, dbm));
        }

        Exit => {
            // no successors
        }
    }

    out
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

