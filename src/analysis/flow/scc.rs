// src/analysis/flow/scc.rs
//
// Strongly-connected components on the lowered CFG. Iterative Tarjan
// adapted from kernel `compute_scc` (verifier.c v6.15 L25809-L25979).
//
// SCC ids start at 1 and are written into `env.insn_aux_data[pc].scc_id`.
// Per kernel convention, a singleton SCC WITHOUT a self-edge keeps
// `scc_id = 0` ("not in any SCC") — only multi-vertex components and
// singletons-with-self-edge get a real id. This is what
// `compute_scc_callchain` relies on to decide "is this insn in an SCC?".
//
// This is a behavior-neutral pre-pass — it just annotates aux data. The
// real consumers (`maybe_enter_scc`, `add_scc_backedge`,
// `propagate_backedges`, `incomplete_read_marks`) read `scc_id` at
// runtime to drive SCC-scoped precision propagation.

use crate::analysis::machine::env::VerifierEnv;
use crate::ast::{Instr, Operand, Program};

/// Sentinel returned by `low[t]` when a vertex has been popped out of
/// the SCC stack already. Larger than any real preorder number, so
/// `min(low[w], low[s])` is a no-op when `s` is no longer on stack.
const NOT_ON_STACK: u32 = u32::MAX;

/// Compute SCCs over the program's CFG and write `scc_id` into each
/// instruction's `insn_aux_data` entry. Idempotent in the sense that
/// repeated calls reproduce the same numbering for the same input
/// program (modulo deterministic successor order).
pub fn compute_scc(prog: &Program, env: &mut VerifierEnv) {
    let n = prog.instrs.len();
    if n == 0 {
        return;
    }

    // Tarjan bookkeeping. preorder/low indexed by pc.
    let mut pre: Vec<u32> = vec![0; n];
    let mut low: Vec<u32> = vec![0; n];
    // SCC-membership stack (vertices in DFS order; popped together when
    // a root is detected).
    let mut stack: Vec<usize> = Vec::with_capacity(n);
    // DFS work stack — emulates explicit recursion so we don't blow up
    // the host stack on long programs.
    let mut dfs: Vec<usize> = Vec::with_capacity(n);
    // Per-DFS-frame: which successor index do we resume at? Mirrors the
    // kernel's `succ` traversal — when we recurse into a successor we
    // need to come back and continue with the next sibling.
    let mut succ_iter: Vec<usize> = vec![0; n];

    let mut next_preorder: u32 = 1;
    let mut next_scc_id: u32 = 1;

    for root in 0..n {
        if pre[root] != 0 {
            continue;
        }
        dfs.push(root);

        'outer: while let Some(&w) = dfs.last() {
            if pre[w] == 0 {
                pre[w] = next_preorder;
                low[w] = next_preorder;
                next_preorder += 1;
                stack.push(w);
                succ_iter[w] = 0;
            }

            let succs = successors(prog, w);
            // Resume successor iteration from where we left off.
            while succ_iter[w] < succs.len() {
                let s = succs[succ_iter[w]];
                succ_iter[w] += 1;
                if s >= n {
                    continue;
                }
                if pre[s] == 0 {
                    // Recurse — push and restart.
                    dfs.push(s);
                    continue 'outer;
                }
                // Either still on stack (low[s] < NOT_ON_STACK) or
                // already popped (low[s] == NOT_ON_STACK). The
                // simplified Pearce-style `min(low[w], low[s])` is a
                // no-op in the popped case.
                if low[s] < low[w] {
                    low[w] = low[s];
                }
            }

            // All successors visited. Check whether `w` is the root of
            // a completed SCC.
            if low[w] < pre[w] {
                // Not a root — leave on stack, propagate up.
                dfs.pop();
                continue;
            }

            // `w` is an SCC root. Decide whether to assign a real id:
            // multi-vertex component, or singleton with a self-edge.
            let mut assign = stack.last().copied() != Some(w);
            if !assign {
                for &s in &succs {
                    if s == w {
                        assign = true;
                        break;
                    }
                }
            }

            // Pop component elements; assign id if applicable.
            loop {
                let t = stack.pop().expect("scc stack underflow");
                low[t] = NOT_ON_STACK;
                if assign && t < env.insn_aux_data.len() {
                    env.insn_aux_data[t].scc_id = next_scc_id;
                }
                if t == w {
                    break;
                }
            }
            if assign {
                next_scc_id += 1;
            }
            dfs.pop();
        }
    }
}

/// Pure successor function for the SCC pre-pass. Parallel to
/// `cfg::visit_insn` but free of side effects on `env`. Returns
/// in-bounds pcs only — out-of-bounds successors are silently skipped
/// (cfg::check_cfg flags those as errors before we run).
fn successors(prog: &Program, pc: usize) -> Vec<usize> {
    let n = prog.instrs.len();
    if pc >= n {
        return Vec::new();
    }
    let mut out = Vec::with_capacity(2);
    match &prog.instrs[pc] {
        Instr::Exit => {}
        Instr::Jmp { target } => {
            out.push(*target);
        }
        Instr::If { target, .. } => {
            if pc + 1 < n {
                out.push(pc + 1);
            }
            out.push(*target);
        }
        Instr::MayGoto { target } => {
            if pc + 1 < n {
                out.push(pc + 1);
            }
            out.push(*target);
        }
        Instr::Call { .. } => {
            // Helper / kfunc calls don't transfer control to another
            // pc in this program's CFG (callbacks are entered via
            // PSEUDO_FUNC pointers, which the CFG check tracks
            // separately — the SCC analysis treats the call as a
            // single-edge fall-through, same as the kernel's
            // `bpf_insn_successors` for helper calls).
            if pc + 1 < n {
                out.push(pc + 1);
            }
        }
        Instr::CallRel { target } => {
            // BPF-to-BPF call: edge into the callee's entry. SCC
            // membership is per-program-counter; we include the callee
            // edge so a recursive subprog (if ever legal) would form
            // an SCC.
            out.push(*target);
            if pc + 1 < n {
                out.push(pc + 1);
            }
        }
        // All non-branch instructions: single fall-through.
        _ => {
            if pc + 1 < n {
                out.push(pc + 1);
            }
        }
    }
    out
}

// Silence "unused" if `Operand` is never reached in match patterns
// above — keep the import name in scope for future expansions.
#[allow(dead_code)]
fn _operand_anchor(_: &Operand) {}

// ════════════════════════════════════════════════════════════════════
//  SCC visit lifecycle — mirror of kernel bpf_scc_callchain /
//  bpf_scc_visit / bpf_scc_backedge (include/linux/bpf_verifier.h
//  L703-L725, verifier.c L2142-L2351).
// ════════════════════════════════════════════════════════════════════

use crate::analysis::machine::frame_stack::FrameLevel;
use crate::analysis::machine::state::State;
use std::collections::HashMap;

/// Mirror of kernel `bpf_scc_callchain`: a tuple of (outer-frame
/// callsites, SCC id of the innermost SCC-bearing frame). Two states
/// with the same callchain belong to the same SCC visit instance.
///
/// `callsites[i]` is the call-instruction pc of frame i (frames are
/// numbered from outermost = 0 to innermost = curframe). For the
/// frame whose pc is in an SCC, no callsite is recorded — we stop
/// there and record `scc_id` instead. If no frame's pc is in an SCC,
/// `compute_scc_callchain` returns `None` (the state is not in any SCC).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SccCallchain {
    pub callsites: Vec<usize>,
    pub scc_id: u32,
}

/// Mirror of kernel `bpf_scc_backedge`: a cur-state snapshot saved at
/// the moment of a RANGE_WITHIN convergence hit, plus the cache_id of
/// the cached state that subsumed it (`equal_state` in kernel terms).
/// Stored on the SCC visit's backedges list; consumed by
/// `propagate_backedges` at SCC exit to bring precision marks to
/// fixpoint along the convergence cycle.
#[derive(Clone, Debug)]
pub struct SccBackedge {
    pub state: State,
    pub equal_state_cache_id: u32,
    pub insn_idx: usize,
}

/// Mirror of kernel `bpf_scc_visit`. One per (callchain) seen during a
/// verification run. `entry_state_cache_id` is the cache_id of the
/// FIRST state on the current verification path that entered this
/// SCC's visit instance — when that state's DFS subtree completes
/// (`branches → 0` in `complete_dfs_branch`), the visit exits and
/// `propagate_backedges` fires.
#[derive(Clone, Debug, Default)]
pub struct SccVisit {
    pub entry_state_cache_id: Option<u32>,
    pub backedges: Vec<SccBackedge>,
}

/// Compute the SCC callchain for a state. Returns `None` if no frame's
/// pc is in any SCC.
///
/// Walks frames outermost-to-innermost. For each frame i:
///   * Frame ip = innermost frame uses `state.pc`; caller frames use
///     the next-inner frame's `return_pc - 1` (the call insn pc).
///   * If `insn_aux_data[ip].scc_id != 0`, this is the SCC-bearing
///     frame; record its scc_id and stop.
///   * Otherwise, if it's not the innermost frame, record the
///     callsite and continue outward.
///   * If we reach the innermost frame without finding any SCC,
///     return None (state not in any SCC).
pub fn compute_scc_callchain(
    state: &State,
    insn_aux_data: &[crate::analysis::machine::env::InsnAuxData],
) -> Option<SccCallchain> {
    let n = state.frames.depth();
    let mut callsites: Vec<usize> = Vec::with_capacity(n.saturating_sub(1));
    for i in 0..n {
        let insn_idx = if i + 1 == n {
            state.pc
        } else {
            // Callsite of frame i = the call insn that pushed frame
            // i+1. zovia stores `return_pc` (= callsite + 1) on the
            // next-inner frame; recover the callsite by subtracting 1.
            let next = state.frames.get(FrameLevel::from_index(i + 1));
            next.return_pc.saturating_sub(1)
        };
        let scc_id = insn_aux_data
            .get(insn_idx)
            .map(|a| a.scc_id)
            .unwrap_or(0);
        if scc_id != 0 {
            return Some(SccCallchain {
                callsites,
                scc_id,
            });
        } else if i + 1 < n {
            callsites.push(insn_idx);
        } else {
            return None;
        }
    }
    None
}

/// Map keyed by `SccCallchain`, storing per-visit state. Lives on
/// `VerifierEnv.scc_visits`. Allocated lazily on first
/// `maybe_enter_scc` for a callchain.
pub type SccVisitMap = HashMap<SccCallchain, SccVisit>;
