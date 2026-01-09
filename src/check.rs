use crate::ast::Program;
use crate::dbm::Dbm;
use crate::analysis::context::ExecContext;
use crate::kernel_semantics;
use crate::domain::{Reg, REG_ENV};
use crate::utils::clamp_upper_bound;

pub struct CheckError {
    pub pc: usize,
    pub succ: usize,
    pub msg: String,
}

impl CheckError {
    pub fn format(&self) -> String {
        format!("pc {} -> {}: {}", self.pc, self.succ, self.msg)
    }
}

#[derive(Debug)]
pub struct InclusionFailure {
    pub post: i64,
    pub cert: i64,
    pub xi: Reg,
    pub xj: Reg,
}

pub fn check_included(post: &Dbm, cert: &Dbm) -> Result<(), InclusionFailure> {
    let n = post.dim();
    for i in 0..n {
        for j in 0..n {
            let post_v = clamp_upper_bound(post.raw(i, j));
            let cert_v = clamp_upper_bound(cert.raw(i, j));
            if post_v > cert_v {
                let xi = REG_ENV.var_of_index(i);
                let xj = REG_ENV.var_of_index(j);
                return Err(InclusionFailure { post: post_v, cert: cert_v, xi, xj });
            }
        }
    }
    Ok(())
}

pub fn check_certificate_against_kernel_sim(
    ctx: &ExecContext,
    prog: &Program,
    cert: &Vec<Dbm>,
) -> Result<(), CheckError> {
    if cert.len() != prog.instrs.len() {
        return Err(CheckError {
            pc: 0,
            succ: 0,
            msg: format!(
                "certificate length {} != program length {}",
                cert.len(),
                prog.instrs.len()
            ),
        });
    }

    for pc in 0..prog.instrs.len() {
        let pre = &cert[pc];
        let instr = &prog.instrs[pc];

        let outs = kernel_semantics::transfer_one_kernel(ctx, pc, instr, pre);

        for (succ, post) in outs {
            if succ >= cert.len() {
                return Err(CheckError {
                    pc,
                    succ,
                    msg: "successor out of bounds".to_string(),
                });
            }

            if kernel_semantics::inconsistent(&post) {
                return Err(CheckError {
                    pc,
                    succ,
                    msg: "local transfer produced inconsistent DBM".to_string(),
                });
            }

            let next = &cert[succ];

            match check_included(&post, next) {
                Ok(()) => {}
                Err(f) => {
                    return Err(CheckError {
                        pc,
                        succ,
                        msg: format!(
                            "inclusion check failed\n{}",
                            format_inclusion_failure(&f)
                        ),
                    });
                }
            }
        }
    }

    Ok(())
}

pub fn format_inclusion_failure(f: &InclusionFailure) -> String {
    // Interpreting DBM entry: xi - xj <= c
    let xi_name = REG_ENV.name(f.xi);
    let xj_name = REG_ENV.name(f.xj);

    format!(
        "violated constraint at entry ({}, {}): {} - {} <= {}\n  post has {}\n  cert has {}",
        xi_name, xj_name,
        xi_name, xj_name, f.cert,
        f.post,
        f.cert
    )
}
