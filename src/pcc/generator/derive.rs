use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, Instr, Operand, Program, Width};
use crate::domains::dbm::Dbm;
use log::debug;

use super::super::checker::{derive_fact_from_branch, distance_upper_bound};
use super::super::model::ProofStep;
use super::bounds::zone_upper_bound;
use super::trace::{backward_trace, instr_writes};

// ---------------------------------------------------------------------------
// Derive-chain fallback (for derived-register patterns)
// ---------------------------------------------------------------------------

/// Fallback when backward_trace fails: attempts to build a proof chain using
/// a Derive step for the "derived register" pattern.
///
/// Pattern: `base += src_reg` at `target_pc - 1`, where:
/// - `base` has a known constant offset from `anchor` (from interval PtrOffset)
/// - `src_reg`'s bound in the zone comes through a derived register `k` where
///   `k = src_reg + offset` (established by `mov k, src_reg; add k, imm`)
///   and a branch constrains `k <= C`
///
/// Produces: Fact(k <= C) + Derive(k = src + offset) + Transfer(base += src, delta)
pub(super) fn try_derive_chain(
    prog: &Program,
    zone_dbms: &[Dbm],
    interval_states: &[State],
    target_pc: usize,
    base: Reg,
    anchor: Reg,
    zone_ub: i64,
) -> Option<Vec<ProofStep>> {
    // Step 1: Check instruction at target_pc - 1 is `add base, src_reg`
    let add_pc = target_pc.checked_sub(1)?;
    let add_instr = prog.instrs.get(add_pc)?;
    let src_reg = match add_instr {
        Instr::Alu {
            op: AluOp::Add,
            dst,
            src: Operand::Reg(src),
            ..
        } if *dst == base => *src,
        _ => return None,
    };

    // Step 2: Get base_old's upper bound relative to anchor from the interval state
    let interval_state = interval_states.get(add_pc)?;
    let base_old_ub = distance_upper_bound(interval_state, base, anchor)?;
    if base_old_ub == i64::MAX {
        return None;
    }

    // Required bound on src_reg: zone_ub = base_old_ub + src_bound → src_bound = zone_ub - base_old_ub
    let required_src_bound = zone_ub.checked_sub(base_old_ub)?;

    // Step 3: Try backward_trace on (src_reg, anchor) — might succeed if a branch directly constrains src_reg
    if let Some((_, _, _, _, mut proof)) = backward_trace(
        prog,
        zone_dbms,
        interval_states,
        add_pc, // trace up to (but not including) the add instruction
        src_reg,
        anchor,
        required_src_bound,
    ) {
        // Append the absorb Transfer for the add instruction
        proof.push(ProofStep::Transfer {
            pc: add_pc,
            pre_left_reg: src_reg.idx(),
            pre_right_reg: anchor.idx(),
            post_left_reg: base.idx(),
            post_right_reg: anchor.idx(),
            delta: base_old_ub,
            hint: Some(format!(
                "{} += {}  [absorb: {} offset={}, pair switches to {}]",
                base.name(),
                src_reg.name(),
                base.name(),
                base_old_ub,
                base.name(),
            )),
        });
        return Some(proof);
    }

    // Step 4: backward_trace on src_reg also failed — try Derive pattern.
    // Search for a register k where k = src_reg + offset, constrained by a branch.
    let src_bound_in_zone = zone_upper_bound(zone_dbms.get(add_pc)?, src_reg, anchor)?;
    if src_bound_in_zone > required_src_bound {
        return None; // zone can't prove src_reg <= required either
    }

    // Scan backward from add_pc for a branch that constrains some register k,
    // where k = src_reg + offset is established by earlier instructions.
    for branch_pc in (0..add_pc).rev() {
        let branch_instr = &prog.instrs[branch_pc];

        // Check if this is a branch with a fall-through constraint
        let guard = derive_fact_from_branch(branch_instr, branch_pc, branch_pc + 1)?;
        let k = Reg::idx_to_reg(guard.left_reg)?;
        if guard.right_reg != anchor.idx() {
            continue; // we need k - anchor <= c
        }
        let branch_c = guard.c;

        // Search for instructions between branch_pc and add_pc that establish k = src_reg + offset.
        // Pattern: mov k, src_reg; add k, imm (possibly with passthrough instructions between).
        if let Some((derive_start, derive_end, offset)) =
            find_derive_sequence(prog, branch_pc, k, src_reg)
        {
            // Verify: branch_c - offset <= required_src_bound
            let derived_bound = branch_c.checked_sub(offset)?;
            if derived_bound > required_src_bound {
                continue; // derived bound too loose
            }

            // Build proof chain: Fact + Derive + Transfer(absorb)
            let mut proof = Vec::with_capacity(3);

            proof.push(ProofStep::Fact {
                pc: branch_pc,
                left_reg: k.idx(),
                right_reg: anchor.idx(),
                c: branch_c,
            });

            proof.push(ProofStep::Derive {
                pc_start: derive_start,
                pc_end: derive_end,
                source_reg: k.idx(),
                target_reg: src_reg.idx(),
                offset,
            });

            proof.push(ProofStep::Transfer {
                pc: add_pc,
                pre_left_reg: src_reg.idx(),
                pre_right_reg: anchor.idx(),
                post_left_reg: base.idx(),
                post_right_reg: anchor.idx(),
                delta: base_old_ub,
                hint: Some(format!(
                    "{} += {}  [absorb: {} offset={}, pair switches to {}]",
                    base.name(),
                    src_reg.name(),
                    base.name(),
                    base_old_ub,
                    base.name(),
                )),
            });

            debug!(
                target: "pcc-gen",
                "[PCC-GEN] target={}: derive chain found: Fact(pc={}, {}≤{}) + Derive({}={}+{}) + Transfer(pc={})",
                target_pc, branch_pc, k.name(), branch_c, k.name(), src_reg.name(), offset, add_pc,
            );

            return Some(proof);
        }
    }

    None
}

/// Search backward from `branch_pc` for instructions establishing `k = src_reg + offset`.
/// Returns `(pc_mov, pc_add, offset)`.
///
/// Looks for the pattern: `mov k, src_reg` at some pc, then `add k, imm` at a later pc,
/// with no intervening instructions that overwrite k or src_reg, and no overwrites of
/// src_reg between the sequence and the branch.
fn find_derive_sequence(
    prog: &Program,
    branch_pc: usize,
    k: Reg,
    src_reg: Reg,
) -> Option<(usize, usize, i64)> {
    let mut add_pc = None;
    let mut offset = 0i64;

    // Scan backward from branch_pc - 1 looking for `add k, imm`
    for pc in (0..branch_pc).rev() {
        let instr = &prog.instrs[pc];
        match instr {
            Instr::Alu {
                width: Width::W64,
                op: AluOp::Add,
                dst,
                src: Operand::Imm(imm),
            } if *dst == k => {
                offset = *imm;
                add_pc = Some(pc);
            }
            Instr::Alu {
                width: Width::W64,
                op: AluOp::Mov,
                dst,
                src: Operand::Reg(src),
            } if *dst == k && *src == src_reg => {
                let start = pc;
                let end = add_pc.unwrap_or(pc);
                // Verify no overwrites of k or src_reg between start and end
                for check_pc in (start + 1)..end {
                    let ci = &prog.instrs[check_pc];
                    if instr_writes(ci, k) || instr_writes(ci, src_reg) {
                        return None;
                    }
                }
                // Also verify src_reg is not overwritten between end and the branch
                for check_pc in (end + 1)..branch_pc {
                    let ci = &prog.instrs[check_pc];
                    if instr_writes(ci, src_reg) {
                        return None;
                    }
                }
                return Some((start, end, offset));
            }
            _ if instr_writes(instr, k) => {
                // k was overwritten by something we don't understand; stop searching
                return None;
            }
            _ => {}
        }
    }
    None
}
