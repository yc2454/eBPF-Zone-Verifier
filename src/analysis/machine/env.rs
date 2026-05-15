use crate::analysis::machine::error::VerificationError;
use crate::analysis::machine::history::History;
// src/analysis/env.rs
use crate::analysis::machine::context::ExecContext;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::Program;
use crate::pcc::ProgramCertificate;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Default, Debug)]
pub struct InsnAuxData {
    pub prune_point: bool,
    pub seen: bool,
    /// Registers that are live (read before next write) at this PC.
    pub live_regs: HashSet<Reg>,
    /// Stack slot offsets (byte-granularity, relative to R10) that are live at this PC.
    pub live_slots: HashSet<i16>,
    /// this pc is a "force checkpoint" — kernel keeps cached
    /// states here longer (eviction threshold n=64 vs default n=3) to
    /// preserve iter/may_goto/cb-call convergence checkpoints. Mirrors
    /// kernel `mark_force_checkpoint` (verifier.c v6.15 L17085) which
    /// flags iter_next kfunc calls, sync-callback-calling helpers
    /// (bpf_loop / bpf_for_each_map_elem / bpf_user_ringbuf_drain),
    /// and may_goto instructions.
    pub force_checkpoint: bool,
}

/// per-cached-state hit/miss counters for explored-states
/// eviction. Mirrors `bpf_verifier_state_list.{hit_cnt,miss_cnt}`
/// (verifier.c v6.15 ~L19180-L19233). Indexed identically with
/// `explored_states[pc]`: when an entry is evicted, both vectors drop
/// the same index.
#[derive(Clone, Default, Debug)]
pub struct StateMetrics {
    pub hit_cnt: u32,
    pub miss_cnt: u32,
}

/// Per-PC histogram of *why* a `state_subsumed_by` check failed. Used
/// by the end-of-analysis dump to figure out which subsumption sub-check
/// is the dominant miss reason on timeout-prone tests — informs whether
/// the next investment should be liveness (Stack), precision propagation
/// (Types/Tnum/Domain/ScalarIdLinks), or widening breadth.
///
/// One entry is recorded per miss against the first sub-check that
/// rejected; later sub-checks short-circuit so we don't see them. That's
/// the right granularity for "which mechanism would unblock the most
/// states."
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SubsumptionMissReason {
    Types,
    Domain,
    Stack,
    Tnum,
    ScalarIdLinks,
    ActiveLock,
    GotoBudget,
    ActiveRefs,
    CallerFrame,
}

/// Coarse counters describing how `should_prune` decisions broke down.
/// Lets the audit dump distinguish:
///   - "we didn't even try to prune" (not a prune point, on-path skip)
///   - "we tried but had no prev state to compare against" (first visit)
///   - "we tried and went through standard or loop pruning"
/// — which then composes with the miss-reason histogram to tell us
/// whether the bottleneck is subsumption-failure (rework subsumption)
/// or first-visit-explosion (rework prune-point density / loop detection).
#[derive(Clone, Default, Debug)]
pub struct PruningStats {
    pub should_prune_calls: u64,
    pub not_prune_point: u64,
    pub on_path_skip: u64,
    pub no_prev_states: u64,
    pub std_pruning_calls: u64,
    pub loop_pruning_calls: u64,
    /// Of the `loop_pruning_calls`, how many bailed early because
    /// `loop_has_conditional_exit` returned false. Distinguishes
    /// "we identify the construct as a loop but can't see its exit"
    /// (probably a missed iter_next-style exit pattern) from "we
    /// reached subsumption but the cache didn't help."
    pub loop_no_cond_exit: u64,
    /// Of `should_prune` calls reaching the post-skip phase, how many
    /// were short-circuited by the may_goto RANGE_WITHIN prune class
    /// (counted *before* the std/loop branch, so it's not in those).
    pub may_goto_range_within_hits: u64,
    /// Per-call tracking inside `handle_loop_pruning` itself. The
    /// outer `loop_pruning_calls` counts *attempts*; this is "we
    /// actually walked prev_states." Difference would show if the
    /// `loop_has_conditional_exit` bail-out happens after the counter
    /// increment.
    pub loop_walks_attempted: u64,
    pub loop_walks_no_prev: u64,
    pub loop_walks_hit: u64,
    pub loop_walks_miss: u64,
    pub loop_walks_pruned_via_convergence: u64,
    /// Lifetime cache hits (every successful subsumption, even on
    /// states that later get evicted via max_states_per_pc drain).
    /// The per-state `StateMetrics.hit_cnt` is wrong for end-of-run
    /// reporting because evicted entries take their counters with them;
    /// these monotonic counters give the true picture.
    pub lifetime_hits: u64,
    pub lifetime_misses: u64,
}

impl SubsumptionMissReason {
    pub const ALL: [SubsumptionMissReason; 9] = [
        SubsumptionMissReason::Types,
        SubsumptionMissReason::Domain,
        SubsumptionMissReason::Stack,
        SubsumptionMissReason::Tnum,
        SubsumptionMissReason::ScalarIdLinks,
        SubsumptionMissReason::ActiveLock,
        SubsumptionMissReason::GotoBudget,
        SubsumptionMissReason::ActiveRefs,
        SubsumptionMissReason::CallerFrame,
    ];
    pub fn idx(self) -> usize {
        match self {
            SubsumptionMissReason::Types => 0,
            SubsumptionMissReason::Domain => 1,
            SubsumptionMissReason::Stack => 2,
            SubsumptionMissReason::Tnum => 3,
            SubsumptionMissReason::ScalarIdLinks => 4,
            SubsumptionMissReason::ActiveLock => 5,
            SubsumptionMissReason::GotoBudget => 6,
            SubsumptionMissReason::ActiveRefs => 7,
            SubsumptionMissReason::CallerFrame => 8,
        }
    }
    pub fn label(self) -> &'static str {
        match self {
            SubsumptionMissReason::Types => "types",
            SubsumptionMissReason::Domain => "domain",
            SubsumptionMissReason::Stack => "stack",
            SubsumptionMissReason::Tnum => "tnum",
            SubsumptionMissReason::ScalarIdLinks => "scalar_id_links",
            SubsumptionMissReason::ActiveLock => "active_lock",
            SubsumptionMissReason::GotoBudget => "goto_budget",
            SubsumptionMissReason::ActiveRefs => "active_refs",
            SubsumptionMissReason::CallerFrame => "caller_frame",
        }
    }
}

pub struct VerifierEnv<'a> {
    pub ctx: &'a ExecContext,
    pub explored_states: HashMap<usize, Vec<State>>,
    /// parallel to `explored_states`. `state_metrics[pc][i]`
    /// holds the hit/miss counters for `explored_states[pc][i]`. Drop
    /// the same index from both vectors on eviction.
    pub state_metrics: HashMap<usize, Vec<StateMetrics>>,
    /// Per-PC histogram of subsumption-miss reasons (one bucket per
    /// `SubsumptionMissReason` variant). `subsumption_misses[pc][r.idx()]`
    /// is incremented every time the per-cached-state subsumption check
    /// rejected with reason `r`. Used by the end-of-analysis dump.
    pub subsumption_misses: HashMap<usize, [u64; 9]>,
    /// Coarse counters for `should_prune` to disambiguate "subsumption
    /// failed" from "subsumption never even attempted". Incremented in
    /// `should_prune` and dumped alongside the miss histogram.
    pub pruning_stats: PruningStats,
    pub insn_aux_data: Vec<InsnAuxData>,
    pub invalid_pc_set: HashSet<usize>,
    pub addr_space_cast_to_arena_pcs: HashSet<usize>,
    /// Subprog entry-PCs whose body contains a kfunc / helper that the
    /// kernel forbids inside an rbtree-add / list-push `less` callback
    /// (verifier.c v6.15: kernel rejects "X not allowed in rbtree cb"
    /// or "function calls not allowed while holding a lock"). At the
    /// graph-add validator we look up R3's `PtrToCallback{subprog_pc}`
    /// and reject if its entry PC is in this set.
    pub tainted_cb_subprogs: HashSet<usize>,

    /// Per-cb-subprog set of byte offsets (relative to the cb's ctx-arg
    /// pointer) that any branch through the cb body may write via
    /// `Store { base: <ctx-alias>, off, .. }`. Pre-computed at env
    /// init by static scan of the program. Used at cb-Exit propagation
    /// (`cb_exit_propagate`): when `cb_should_widen=true` we invalidate
    /// every caller-frame slot in this set, not just the slots THIS
    /// cb-exit branch happened to write — required to discover multi-
    /// iteration interleavings (e.g. `iter_limit_bug` where two
    /// iterations of a 3-branch cb can land on `{ctx.a=42, ctx.b=42}`,
    /// not reachable from any single-iteration analysis).
    pub cb_body_store_offsets: HashMap<usize, std::collections::HashSet<i16>>,

    /// Per-cb-subprog flag: does the body call (directly) any
    /// dynptr-(re)initializing helper or kfunc?
    /// (`BPF_DYNPTR_FROM_MEM`, `BPF_RINGBUF_RESERVE_DYNPTR`,
    /// `bpf_dynptr_from_skb`, `bpf_dynptr_from_xdp`, `bpf_dynptr_clone`,
    /// `bpf_dynptr_adjust`.) Pre-computed at env init by scanning the
    /// cb body. Used by `transfer_callback_helper` to suppress the
    /// kernel-pessimism dynptr-slice invalidation on the post-cb
    /// continuation when the cb provably cannot re-init the dynptr —
    /// the invalidation is required for FA safety on `invalid_data_slices`
    /// (cb body actually re-inits) but FRs valid programs like
    /// `dynptr_success::test_ringbuf` (cb body just reads via
    /// `bpf_dynptr_data`). Mirrors the kernel's actual model: only
    /// `destroy_if_dynptr_stack_slot` invalidates slices, and that
    /// only fires on real init/release operations. Conservatively true
    /// for cbs that make a `CallRel` (we don't transitively scan).
    pub cb_body_can_reinit_dynptr: HashSet<usize>,

    // --- Dynamic State ---
    pub insn_processed: usize,
    /// Holds the FIRST critical failure encountered.
    /// If this is Some, the analysis should halt immediately.
    pub error: Option<VerificationError>,
    // Path execution history
    pub history: History,
    // Optional PCC certificate loaded from CLI.
    pub certificate: Option<ProgramCertificate>,
    /// True while `analyze_exception_cb` is running. Mirrors the kernel's
    /// `frame->in_exception_callback_fn`: switches the main-frame exit
    /// check to the exception-cb-specific rule (R0 ∈ [0, 0] for fentry/
    /// fexit) without affecting ordinary main-program exits.
    pub analyzing_exception_cb: bool,

    /// Monotonic counter for cache_id assignment. Each call to
    /// `record_state` mints a fresh id (post-increment).
    pub next_cache_id: u32,

    /// Reverse map: cache_id -> (pc, idx_in_explored_states_at_pc).
    /// Maintained by `record_state` (insertion) and the eviction path
    /// in `record_state` (index updates after drain). Used by the
    /// per-path precision walker to look up the specific cached state
    /// referenced by a `parent_cache_id` chain.
    pub cache_loc_by_id: HashMap<u32, (usize, usize)>,

    /// Collected BCF refinement proofs from this verification run. Each
    /// entry carries the canonical hash of the refinement-condition root,
    /// the goal-expression table the kernel needs for `expr_equiv` +
    /// `bcf_check_proof`, the proof bytes, and a kind tag
    /// (`BCF_BUNDLE_KIND_*`). Populated by refinement callbacks at
    /// safety-check sites when `config.bcf_enabled` and cvc5 returns Unsat;
    /// flushed to the `<input>.bcf-bundle` sidecar at the end of verification.
    /// Format: see `c-ref/bcf_bundle.h`.
    pub bcf_proofs: Vec<crate::refinement::bundle::RefineEntry>,

    /// Transient: the size-arg register of a helper-mem-region check in
    /// progress, when one applies. Mirrors BCF's `bcf->size_regno`
    /// (kernel `set1/0014`). Set by `mem_checks.rs` immediately before a
    /// call into `check_ptr_access_size` whose size came from a register;
    /// cleared after. Consumed by `refine_map` to build template 4b case
    /// (iv)'s symbolic-size-aware refine_cond. `None` for accesses with
    /// a static size (instruction-level loads/stores).
    pub bcf_size_reg: Option<Reg>,

    /// Set by access-site path-unreachable speculation when cvc5 proves
    /// the accumulated path_conds unsat at a memory-access rejection
    /// (memory/access.rs). The caller of `check_load`/`check_store`
    /// reads-and-clears this via `take_bcf_path_drop_requested()` and
    /// returns `vec![]` to drop the path. Without the drop, the
    /// speculated-unreachable path continues exploring, hits more
    /// rejections, and cascades cvc5 calls (the 2026-05-14 calico
    /// runaway). This is the access-site analogue of branch/mod.rs's
    /// `is_inconsistent() → vec![]` flow; we use an env flag instead of
    /// mutating `state.domain` because `check_load`/`check_store` take
    /// `&State` and several mem-check call paths can't easily provide
    /// `&mut State` without a wider refactor.
    pub bcf_path_drop_requested: bool,

    /// Eviction-resistant precision marks keyed by `(pc, reg)`.
    /// `mark_chain_precision_backward` writes here as it walks the
    /// per-path history, so widening sites can detect "this reg was
    /// proven precision-critical at this pc on some earlier path"
    /// even after `max_states_per_pc` evicts the specific cached
    /// state that the walker originally marked. Reg-name boundaries
    /// (e.g. `r7 = r1` mov chains) are bridged at the *widening*
    /// site via the cached `scalar_ids` map: the widener checks the
    /// reg's id against all regs in cur/prev that share that id.
    pub precise_pcs: HashSet<(usize, Reg)>,
}

impl<'a> VerifierEnv<'a> {
    pub fn new(
        ctx: &'a ExecContext,
        prog: &'a Program,
        certificate: Option<ProgramCertificate>,
    ) -> Self {
        VerifierEnv {
            ctx,
            explored_states: HashMap::new(),
            state_metrics: HashMap::new(),
            subsumption_misses: HashMap::new(),
            pruning_stats: PruningStats::default(),
            insn_aux_data: vec![InsnAuxData::default(); prog.instrs.len()],
            invalid_pc_set: prog.invalid_pc_set.clone(),
            addr_space_cast_to_arena_pcs: prog.addr_space_cast_to_arena_pcs.clone(),
            tainted_cb_subprogs: compute_tainted_cb_subprogs(prog, &ctx.btf),
            cb_body_store_offsets: compute_cb_body_store_offsets(prog),
            cb_body_can_reinit_dynptr: compute_cb_body_can_reinit_dynptr(prog, &ctx.btf),
            insn_processed: 0,
            error: None,
            history: History::new(),
            certificate,
            analyzing_exception_cb: false,
            next_cache_id: 0,
            cache_loc_by_id: HashMap::new(),
            precise_pcs: HashSet::new(),
            bcf_proofs: Vec::new(),
            bcf_size_reg: None,
            bcf_path_drop_requested: false,
        }
    }

    /// Read-and-clear `bcf_path_drop_requested`. Called by `check_load`/
    /// `check_store` callers right after the access check; on `true`,
    /// the caller drops the current path (`return vec![]`).
    pub fn take_bcf_path_drop_requested(&mut self) -> bool {
        std::mem::take(&mut self.bcf_path_drop_requested)
    }

    /// Report a failure. Only the first failure is recorded.
    pub fn fail(&mut self, err: VerificationError) {
        if self.error.is_none() {
            self.error = Some(err);
        }
    }

    pub fn failed(&self) -> bool {
        self.error.is_some()
    }

    /// Backward precision walk — minimal kernel-aligned `mark_chain_precision`
    /// (verifier.c v6.15 ~L4500-4900, simplified).
    ///
    /// At a precision sink (variable-offset memory access, kfunc/helper arg
    /// requiring an exact value), the kernel walks the jmp_history backward
    /// from the current insn, marking the offset register precise at every
    /// prior cached state. As it walks, it tracks a *frontier* of regs whose
    /// values transitively contributed to the sink:
    ///   - `Mov dst, Reg(src)` — replace dst with src (precision flows past
    ///     the move to the source's prior value).
    ///   - `Alu dst = dst op Reg(src)` — keep dst (its prior value also
    ///     contributed) and add src.
    ///   - `Alu dst = dst op Imm(_)` — keep dst.
    ///   - `Mov dst, Imm(_)` — drop dst (constant source has no chain).
    ///   - `Load*` / `LoadMap` / `LoadPacket` / `LoadSx` — drop dst (loaded
    ///     from memory; no further reg-level chain).
    ///   - `Call` / `CallRel` — drop R0-R5 (caller-saved clobbered).
    ///   - everything else — frontier unchanged.
    ///
    /// Stops walking when the frontier becomes empty or history runs out.
    /// Marks every reg in the frontier precise on every cached state in
    /// `explored_states[step.pc]` at each step.
    ///
    /// The load-bearing primitive that lets the
    /// may_goto widener (`maybe_widen_reg` analogue) skip regs whose values
    /// matter for downstream variable-offset bounds checks. Without this,
    /// removing the over-aggressive branch precision-marker (which we
    /// otherwise need) clobbers test1-4's variable-offset stores; with this,
    /// the offset reg's lineage is preserved through widening sites.
    pub fn mark_chain_precision_backward(
        &mut self,
        history_idx: usize,
        parent_cache_id: Option<u32>,
        sink_reg: Reg,
    ) {
        let mut frontier: HashSet<Reg> = HashSet::new();
        frontier.insert(sink_reg);

        let caller_saved = [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5];

        let mut current_history: Option<usize> = Some(history_idx);
        let mut current_parent_id: Option<u32> = parent_cache_id;
        let mut budget: usize = 16_384;

        // Per-path lineage walk (kernel `__mark_chain_precision`,
        // verifier.c v6.15 L4655). For each cache event in the chain:
        // walk instructions back to the parent's boundary updating the
        // frontier, then mark frontier regs precise on the SPECIFIC
        // parent cached state (not all cached states at that PC). This
        // is the per-path equivalent of kernel `st->parent` chain walk.
        'outer: loop {
            // Resolve the current parent's location and metadata.
            let parent_loc = current_parent_id
                .and_then(|id| self.cache_loc_by_id.get(&id).copied());
            let (parent_history_stop, parent_grandparent_id) =
                if let Some((pc, idx)) = parent_loc {
                    let s = self
                        .explored_states
                        .get(&pc)
                        .and_then(|v| v.get(idx));
                    (
                        s.and_then(|s| s.history_idx),
                        s.and_then(|s| s.parent_cache_id),
                    )
                } else {
                    (None, None)
                };

            // Walk instructions back through current's local history,
            // stopping when we cross the parent's boundary.
            while let Some(idx) = current_history {
                if budget == 0 {
                    break 'outer;
                }
                budget -= 1;

                if let Some(stop) = parent_history_stop
                    && idx <= stop
                {
                    break;
                }

                let Some(step) = self.history.get(idx) else {
                    break;
                };
                let parent_idx = step.parent_idx;
                let instr_copy = step.instr;
                let step_pc = step.pc;
                update_frontier(&mut frontier, &instr_copy, &caller_saved);
                // Mirror frontier marks into `precise_pcs` at every
                // history step the walker traverses. The widening site
                // checks (pc, scalar_id) regardless of whether a
                // cached state at that pc still exists — eviction-
                // resistant. We need the cached state at this pc to
                // resolve scalar_ids for the frontier regs; if no
                // cached state exists at step_pc, fall back to the
                // current state's id which is the closest ground
                // truth for the path.
                for &r in &frontier {
                    self.precise_pcs.insert((step_pc, r));
                }
                current_history = parent_idx;

                if frontier.is_empty() {
                    break 'outer;
                }
            }

            // Mark precise on the parent cached state with the
            // frontier we've evolved back to its perspective. Per-path:
            // only this cached state, not all states at its PC.
            if let Some((pc, idx)) = parent_loc {
                if let Some(states) = self.explored_states.get_mut(&pc)
                    && let Some(s) = states.get_mut(idx)
                {
                    for &r in &frontier {
                        s.precise_regs.insert(r);
                    }
                }
                // Mirror the marks into the eviction-resistant
                // `precise_pcs` set. Cache eviction
                // (`max_states_per_pc`) drops the cached state's
                // `precise_regs` from the lookup chain — keep the
                // (pc, reg) facts in the env so widening sites can
                // still consult them, even after the specific cached
                // state that recorded the mark is gone.
                for &r in &frontier {
                    self.precise_pcs.insert((pc, r));
                }
            }

            // Recurse to grandparent: continue the instruction walk
            // from parent's history boundary toward grandparent's.
            if parent_grandparent_id.is_none() {
                break;
            }
            current_parent_id = parent_grandparent_id;
            current_history = parent_history_stop;
        }
    }

    /// Propagate precision marks from a hit cached state into the current
    /// state's ancestor chain.
    ///
    /// Mirrors kernel `propagate_precision` (verifier.c v6.15 L18828):
    /// when the current path is subsumed by a cached state, the cached
    /// state's precision marks identify which scalars *must* stay
    /// precise on this path's continuation for correctness. We pull
    /// those marks and run `mark_chain_precision_backward` for each on
    /// the CURRENT state's lineage, marking precise on the current
    /// path's specific cached ancestors via `parent_cache_id`. Safe
    /// under the kernel-precision regime because the walker writes
    /// only to per-path-lineage cached states, not all-states-at-pc.
    pub fn propagate_precision(&mut self, cur: &State, old: &State) {
        let regs: Vec<Reg> = old.precise_regs.iter().copied().collect();
        let Some(history_idx) = cur.history_idx else { return };
        for r in regs {
            self.mark_chain_precision_backward(history_idx, cur.parent_cache_id, r);
        }
    }

    /// Compute the PC at which all `target_regs`' definition chains have
    /// bottomed out (the kernel's "base state" PC). Query-only mirror of
    /// `backtrack_states` (vendor verifier.c bcf_track callers; in
    /// `/Users/yalucai/bpf-next-zovia/kernel/bpf/verifier.c` at the
    /// `backtrack_states` definition): walks backward through the linear
    /// breadcrumb history starting from `history_idx`, applying the
    /// per-insn frontier propagation rule
    /// (`update_frontier`, same one used by
    /// `mark_chain_precision_backward`), and returns the PC at which the
    /// frontier first becomes empty. Used by BCF refinement sites to
    /// filter eager `SymbolicState::path_conds` down to the suffix the
    /// kernel's `bcf_track` would emit.
    ///
    /// Semantics — mirrors `backtrack_states` step-by-step:
    /// * Initial frontier = `target_regs`.
    /// * Walk back through breadcrumbs; the **first** breadcrumb (the
    ///   refine site's own insn) is skipped (`skip_first = true`),
    ///   matching the kernel.
    /// * On each prior step, apply `update_frontier`. When it empties,
    ///   that step's PC is the kernel's base PC — return it.
    /// * If the walk runs out of history without emptying the frontier,
    ///   the kernel returns `-EFAULT`; we return `None` (callers treat
    ///   that as "keep all path_conds" — sound, just not tighter than
    ///   today).
    ///
    /// Returns `None` for empty `target_regs` (kernel returns
    /// `-EFAULT` in that case too) or when the walk runs out.
    pub fn bcf_suffix_base_pc(
        &self,
        history_idx: usize,
        parent_cache_id: Option<u32>,
        target_regs: &[Reg],
    ) -> Option<usize> {
        let debug = std::env::var("ZOVIA_BCF_TRACK_DEBUG").is_ok();
        let mut frontier: HashSet<Reg> = target_regs.iter().copied().collect();
        if debug {
            eprintln!(
                "[bcf-track] walk start: targets={:?} history_idx={} parent_cache_id={:?}",
                target_regs, history_idx, parent_cache_id
            );
        }
        if frontier.is_empty() {
            return None;
        }

        let caller_saved = [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5];
        let mut current_history: Option<usize> = Some(history_idx);
        let mut current_parent_id: Option<u32> = parent_cache_id;
        let mut budget: usize = 16_384;
        let mut skip_first = true;

        'outer: loop {
            let parent_loc = current_parent_id
                .and_then(|id| self.cache_loc_by_id.get(&id).copied());
            let (parent_history_stop, parent_grandparent_id) =
                if let Some((pc, idx)) = parent_loc {
                    let s = self
                        .explored_states
                        .get(&pc)
                        .and_then(|v| v.get(idx));
                    (
                        s.and_then(|s| s.history_idx),
                        s.and_then(|s| s.parent_cache_id),
                    )
                } else {
                    (None, None)
                };

            while let Some(idx) = current_history {
                if budget == 0 {
                    break 'outer;
                }
                budget -= 1;

                if let Some(stop) = parent_history_stop
                    && idx <= stop
                {
                    break;
                }

                let Some(step) = self.history.get(idx) else {
                    break;
                };
                let parent_idx = step.parent_idx;
                let instr_copy = step.instr.clone();
                let step_pc = step.pc;

                if !skip_first {
                    let pre: Vec<Reg> = {
                        let mut v: Vec<Reg> = frontier.iter().copied().collect();
                        v.sort_by_key(|r| *r as u8);
                        v
                    };
                    update_frontier(&mut frontier, &instr_copy, &caller_saved);
                    if debug {
                        let post: Vec<Reg> = {
                            let mut v: Vec<Reg> = frontier.iter().copied().collect();
                            v.sort_by_key(|r| *r as u8);
                            v
                        };
                        eprintln!(
                            "[bcf-track]   pc={:>3} {:?} frontier {:?} -> {:?}",
                            step_pc, instr_copy, pre, post
                        );
                    }
                    if frontier.is_empty() {
                        if debug {
                            eprintln!("[bcf-track] frontier empty at pc={}", step_pc);
                        }
                        // Base reached. The kernel's `bcf_track` re-runs
                        // the suffix starting at the parent state — i.e.
                        // from `step_pc` forward. Branches emitted in
                        // the suffix get tagged with their JMP PC, all
                        // ≥ `step_pc`. Return that as the cutoff.
                        return Some(step_pc);
                    }
                } else if debug {
                    eprintln!(
                        "[bcf-track]   pc={:>3} (skipped first: {:?})",
                        step_pc, instr_copy
                    );
                }
                skip_first = false;
                current_history = parent_idx;
            }

            if parent_grandparent_id.is_none() {
                break;
            }
            current_parent_id = parent_grandparent_id;
            current_history = parent_history_stop;
        }

        None
    }
}

/// Update `frontier` (the set of registers whose precision must
/// propagate further back) given that we are *un-doing* `instr`.
/// Pure free function so the walker can call it without re-borrowing
/// `self`.
fn update_frontier(
    frontier: &mut HashSet<Reg>,
    instr: &crate::ast::Instr,
    caller_saved: &[Reg],
) {
    use crate::ast::{AluOp, Instr, Operand};
    match instr {
        Instr::Alu { op, dst, src, .. } => {
            if frontier.contains(dst) {
                match (op, src) {
                    (AluOp::Mov, Operand::Reg(s)) => {
                        frontier.remove(dst);
                        frontier.insert(*s);
                    }
                    (AluOp::Mov, Operand::Imm(_)) => {
                        frontier.remove(dst);
                    }
                    (_, Operand::Reg(s)) => {
                        frontier.insert(*s);
                    }
                    (_, Operand::Imm(_)) => {}
                }
            }
        }
        Instr::MovSx { dst, src, .. } => {
            if frontier.contains(dst) {
                frontier.remove(dst);
                if let Operand::Reg(s) = src {
                    frontier.insert(*s);
                }
            }
        }
        Instr::Load { dst, .. }
        | Instr::LoadSx { dst, .. }
        | Instr::LoadAcq { dst, .. }
        | Instr::LoadMap { dst, .. } => {
            frontier.remove(dst);
        }
        Instr::LoadPacket { .. } => {
            frontier.remove(&Reg::R0);
        }
        Instr::Endian { dst, .. } => {
            let _ = dst;
        }
        Instr::Call { .. } => {
            // Helper / kfunc call: forward-direction clobbers
            // R0..R5. Going backward at this step means the values in
            // R0..R5 immediately after the call don't have a
            // pre-call source (R0 is the helper's return; R1..R5 are
            // clobbered). Drop them from the frontier.
            for r in caller_saved {
                frontier.remove(r);
            }
        }
        Instr::CallRel { .. } => {
            // Subprog call: drop only R0 (the callee's return value
            // — its source lives inside the callee body, which the
            // walker already traversed before reaching this CallRel
            // step on the linear history). R1..R5 in the frontier
            // post-call are the caller's pre-call arg-setup regs and
            // must propagate further back so the precision walk
            // reaches the caller-side instructions that wrote them
            // (e.g. `w2 = r7` at the call site, which is what
            // bridges arena_htab_llvm's loop-counter `r7` back to
            // the access-time precision sink inside the callee).
            // Walking across frames is more permissive than the
            // kernel's per-frame `mark_chain_precision` but matches
            // our linear-history walker's structure.
            frontier.remove(&Reg::R0);
        }
        _ => {}
    }
}

/// Cache-growth instrumentation flag. When set, `record_state` prints
/// `(pc, cache_size, distinct_type_sigs)` to stderr on every insert.
/// Used to diagnose state-graph traversal divergence between
/// flag-off and flag-on under the precision rebuild.
pub fn dump_cache_growth_enabled() -> bool {
    std::env::var("ZOVIA_DUMP_CACHE_GROWTH").ok().as_deref() == Some("1")
}

/// If set to a numeric PC, `record_state` dumps full per-register
/// type signatures at that PC for every cached state on each insert.
/// Used to identify which register's type-shape diverges between
/// flag-off and flag-on.
pub fn dump_cache_growth_pc() -> Option<usize> {
    std::env::var("ZOVIA_DUMP_CACHE_GROWTH_PC")
        .ok()
        .and_then(|s| s.parse().ok())
}

/// If set to a numeric PC, `record_state` dumps the env's
/// `precise_pcs` set (eviction-resistant precision marks written by
/// `mark_chain_precision_backward`) on every insert at that PC.
/// Diagnostic for designing pruning-side wideners that consume
/// `precise_pcs` — surfaces what the walker has actually marked by
/// the time the cache fires at the target loop head.
pub fn dump_precise_pcs_pc() -> Option<usize> {
    std::env::var("ZOVIA_DUMP_PRECISE_PCS_PC")
        .ok()
        .and_then(|s| s.parse().ok())
}

/// Static pre-pass identifying subprog entry PCs whose body is unsafe
/// to use as a graph-add (`bpf_rbtree_add_impl` / `bpf_list_push_*`)
/// `less` callback. Kernel verifier.c v6.15 rejects callbacks that
/// re-invoke graph-add/remove kfuncs, take/release spin_locks, or
/// `bpf_throw`. The kernel's checks include:
///
///   - "rbtree_remove not allowed in rbtree cb"
///   - "arg#1 expected pointer to allocated object" (when the cb
///     calls bpf_rbtree_add → recursion poisons the alloc-arg shape)
///   - "can't spin_{lock,unlock} in rbtree cb"
///   - "bpf_throw not allowed in rbtree cb"
///
/// We don't model these per-msg; we conservatively reject if any
/// forbidden op is reachable in the subprog's straight-line body
/// between its entry PC and its `Exit`. Subprogs are identified by
/// being targets of `LD_IMM64 BPF_PSEUDO_FUNC` (the way callbacks are
/// materialized).
fn compute_tainted_cb_subprogs(
    prog: &crate::ast::Program,
    btf: &crate::parsing::btf::BtfContext,
) -> HashSet<usize> {
    use crate::ast::{CallKind, Instr, MapLoadKind};
    use crate::common::constants;

    // Collect every PSEUDO_FUNC subprog entry PC. These are the only
    // PCs that can ever land in `RegType::PtrToCallback`.
    let mut entries: Vec<usize> = Vec::new();
    for insn in &prog.instrs {
        if let Instr::LoadMap {
            kind: MapLoadKind::PseudoFunc { subprog_pc },
            ..
        } = insn
        {
            entries.push(*subprog_pc as usize);
        }
    }
    entries.sort();
    entries.dedup();

    // Sorted full subprog-entry list (incl. main + every CallRel target +
    // every PSEUDO_FUNC target) used to bound each cb subprog's body
    // range — the Exit at end_pc is conservatively the next entry PC.
    let mut all_entries: Vec<usize> = vec![0];
    for insn in &prog.instrs {
        match insn {
            Instr::CallRel { target } => all_entries.push(*target),
            Instr::LoadMap {
                kind: MapLoadKind::PseudoFunc { subprog_pc },
                ..
            } => all_entries.push(*subprog_pc as usize),
            _ => {}
        }
    }
    all_entries.sort();
    all_entries.dedup();

    let is_forbidden_kfunc = |name: &str| {
        matches!(
            name,
            "bpf_throw"
                | "bpf_rbtree_add_impl"
                | "bpf_rbtree_remove"
                | "bpf_rbtree_first"
                | "bpf_list_push_front_impl"
                | "bpf_list_push_back_impl"
                | "bpf_list_pop_front"
                | "bpf_list_pop_back"
                | "bpf_obj_drop_impl"
                | "bpf_obj_new_impl"
                | "bpf_refcount_acquire_impl"
                | "bpf_rcu_read_lock"
                | "bpf_rcu_read_unlock"
        )
    };

    let mut tainted: HashSet<usize> = HashSet::new();
    for &start in &entries {
        let end = all_entries
            .iter()
            .find(|&&pc| pc > start)
            .copied()
            .unwrap_or(prog.instrs.len());
        let body = &prog.instrs[start..end.min(prog.instrs.len())];
        let mut bad = false;
        for insn in body {
            match insn {
                Instr::Call { kind } => match *kind {
                    CallKind::Helper { id } => {
                        if id == constants::BPF_SPIN_LOCK || id == constants::BPF_SPIN_UNLOCK {
                            bad = true;
                            break;
                        }
                    }
                    CallKind::Kfunc { btf_id, .. } => {
                        if let Some(name) = btf.kfunc_name(btf_id)
                            && is_forbidden_kfunc(name)
                        {
                            bad = true;
                            break;
                        }
                    }
                },
                _ => {}
            }
        }
        if bad {
            tainted.insert(start);
        }
    }
    tainted
}

/// Per-cb-subprog flag: does the body directly call any
/// dynptr-(re)initializing helper or kfunc? Used to suppress the
/// kernel-pessimism slice invalidation in `transfer_callback_helper`
/// when the cb provably cannot re-init the source dynptr.
fn compute_cb_body_can_reinit_dynptr(
    prog: &crate::ast::Program,
    btf: &crate::parsing::btf::BtfContext,
) -> HashSet<usize> {
    use crate::ast::{CallKind, Instr, MapLoadKind};
    use crate::common::constants;

    let mut entries: Vec<usize> = Vec::new();
    for insn in &prog.instrs {
        if let Instr::LoadMap {
            kind: MapLoadKind::PseudoFunc { subprog_pc },
            ..
        } = insn
        {
            entries.push(*subprog_pc as usize);
        }
    }
    entries.sort();
    entries.dedup();

    let mut all_entries: Vec<usize> = vec![0];
    for insn in &prog.instrs {
        match insn {
            Instr::CallRel { target } => all_entries.push(*target),
            Instr::LoadMap {
                kind: MapLoadKind::PseudoFunc { subprog_pc },
                ..
            } => all_entries.push(*subprog_pc as usize),
            _ => {}
        }
    }
    all_entries.sort();
    all_entries.dedup();

    let is_init_kfunc = |name: &str| {
        matches!(
            name,
            "bpf_dynptr_from_skb"
                | "bpf_dynptr_from_xdp"
                | "bpf_dynptr_clone"
                | "bpf_dynptr_adjust"
        )
    };

    let mut out: HashSet<usize> = HashSet::new();
    for &start in &entries {
        let end = all_entries
            .iter()
            .find(|&&pc| pc > start)
            .copied()
            .unwrap_or(prog.instrs.len());
        let body = &prog.instrs[start..end.min(prog.instrs.len())];
        let mut bad = false;
        for insn in body {
            match insn {
                Instr::Call { kind } => match *kind {
                    CallKind::Helper { id } => {
                        if id == constants::BPF_DYNPTR_FROM_MEM
                            || id == constants::BPF_RINGBUF_RESERVE_DYNPTR
                        {
                            bad = true;
                            break;
                        }
                    }
                    CallKind::Kfunc { btf_id, .. } => {
                        if let Some(name) = btf.kfunc_name(btf_id)
                            && is_init_kfunc(name)
                        {
                            bad = true;
                            break;
                        }
                    }
                },
                // Conservative: a CallRel to a global subprog could re-init
                // through a stack-passed dynptr ptr. We don't transitively
                // scan; treat any CallRel as taint. Cbs in our corpus that
                // reach the test cases of interest don't make CallRel.
                Instr::CallRel { .. } => {
                    bad = true;
                    break;
                }
                _ => {}
            }
        }
        if bad {
            out.insert(start);
        }
    }
    out
}

/// Per-cb-subprog set of byte offsets (relative to the cb's ctx-arg
/// pointer) the body may write through. Used by `cb_exit_propagate`
/// to widen across all branches when nr_loops > 1.
///
/// Strategy: for each cb-subprog entry (LD_IMM64 PSEUDO_FUNC target),
/// walk its body forward. Maintain the set of registers known to alias
/// the cb's ctx-arg pointer (R2 for bpf_loop / for_each_map_elem /
/// user_ringbuf_drain, R3 for find_vma — but the kernel routes the
/// caller's ctx into the cb's R2 in *all four* (cb's first non-index
/// arg). For simplicity, seed from {R1, R2, R3, R4, R5} so any of the
/// cb's typed args is treated as a candidate ctx-pointer; we further
/// narrow by only collecting offsets through stores via Mov-aliased
/// regs originating from R2 specifically. Cross-call clobber of
/// R0..R5 invalidates regs not preserved by helpers.
///
/// Misses we accept: register-arithmetic on the ctx pointer
/// (`R = R2 + 8; *R = …`), spill/fill, or stores via a stack-loaded
/// pointer (cb stores ctx to its own stack and loads it back). Any
/// such cb body simply gets a smaller offset set; widening still
/// fires for the offsets we DID detect, and the diff-based snapshot
/// path remains as the fallback for everything else.
fn compute_cb_body_store_offsets(
    prog: &crate::ast::Program,
) -> HashMap<usize, HashSet<i16>> {
    use crate::analysis::machine::reg::Reg;
    use crate::ast::{Instr, MapLoadKind, Operand};

    let mut entries: Vec<usize> = Vec::new();
    for insn in &prog.instrs {
        if let Instr::LoadMap {
            kind: MapLoadKind::PseudoFunc { subprog_pc },
            ..
        } = insn
        {
            entries.push(*subprog_pc as usize);
        }
    }
    entries.sort();
    entries.dedup();

    let mut all_entries: Vec<usize> = vec![0];
    for insn in &prog.instrs {
        match insn {
            Instr::CallRel { target } => all_entries.push(*target),
            Instr::LoadMap {
                kind: MapLoadKind::PseudoFunc { subprog_pc },
                ..
            } => all_entries.push(*subprog_pc as usize),
            _ => {}
        }
    }
    all_entries.sort();
    all_entries.dedup();

    let mut out: HashMap<usize, HashSet<i16>> = HashMap::new();
    for &start in &entries {
        let end = all_entries
            .iter()
            .find(|&&pc| pc > start)
            .copied()
            .unwrap_or(prog.instrs.len());
        let body = &prog.instrs[start..end.min(prog.instrs.len())];

        // Reg-aliasing scan. We seed `aliases` with R2 only (the cb's
        // ctx-pointer arg position for bpf_loop / for_each / user_ringbuf
        // — find_vma also uses the cb's R3 but the cb body's idiom there
        // is identical: ctx is one of the typed args). Adding R3..R5
        // here would broaden over-aggressively and risk widening
        // unrelated stack regions on other tests; leaving R2-only is
        // sound and closes the corpus FA without regressions seen so far.
        let mut aliases: HashSet<Reg> = HashSet::new();
        aliases.insert(Reg::R2);
        let mut offsets: HashSet<i16> = HashSet::new();
        for insn in body {
            match insn {
                Instr::Alu {
                    op: crate::ast::AluOp::Mov,
                    dst,
                    src: Operand::Reg(src_reg),
                    ..
                } => {
                    if aliases.contains(src_reg) {
                        aliases.insert(*dst);
                    } else {
                        // Mov from a non-alias clobbers any prior alias on dst.
                        aliases.remove(dst);
                    }
                }
                Instr::Alu { dst, .. } => {
                    // Any other ALU op breaks the alias on dst (we don't
                    // track ptr-arithmetic).
                    aliases.remove(dst);
                }
                Instr::Load { dst, .. }
                | Instr::LoadMap { dst, .. } => {
                    aliases.remove(dst);
                }
                Instr::Store { base, off, .. } => {
                    if aliases.contains(base) {
                        offsets.insert(*off);
                    }
                }
                Instr::Call { .. } => {
                    // Helper / kfunc calls clobber R0..R5. R6..R9 are
                    // callee-saved (preserved). Drop R0..R5 from aliases.
                    for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
                        aliases.remove(&r);
                    }
                }
                Instr::CallRel { .. } => {
                    // Callee may write through any stack-passed pointer
                    // we lose track of. Conservatively drop all aliases.
                    aliases.clear();
                }
                // Don't break on Exit — the cb body has multiple
                // basic blocks (one per branch) terminating in their
                // own Exit. We need to scan ALL of them. The body
                // range is bounded by the next subprog entry, so we
                // won't wander into another subprog.
                Instr::Exit => {}
                _ => {}
            }
        }
        if !offsets.is_empty() {
            out.insert(start, offsets);
        }
    }
    out
}
