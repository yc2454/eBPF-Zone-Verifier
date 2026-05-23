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
    /// Kernel `insn_aux_data[i].jmp_point` (verifier.c v6.15 L4148).
    /// Strict subset of `prune_point`: marked at conditional-branch
    /// TARGETS (kernel push_insn BRANCH edge L18319) and POST-CALL
    /// FALLTHROUGH (kernel L18361). Read by `is_jmp_point` to gate
    /// `push_jmp_history` calls — kernel's `cur->jmp_history_cnt`
    /// counts branch decisions made on the current state's lineage,
    /// and the long-history safety valve in `add_new_state` uses
    /// `jmp_history_cnt > 40` (verifier.c v6.15 L20256) — NOT the raw
    /// insn delta.
    pub jmp_point: bool,
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
    /// Kernel `insn_aux_data[i].scc` (verifier.c v6.15 ~L25775). SCC
    /// identifier (1+) assigned by Tarjan's algorithm in compute_scc;
    /// 0 means the insn is a singleton SCC without self-edge
    /// (kernel convention — "not in SCC" for the purposes of
    /// `bpf_scc_callchain`). Read by maybe_enter_scc /
    /// maybe_exit_scc / add_scc_backedge / incomplete_read_marks
    /// to identify SCC membership for `propagate_backedges`.
    pub scc_id: u32,
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
    /// Number of times a cached state was skipped in `handle_standard_pruning`
    /// because it had `children_unsafe=true` (i.e., an earlier BCF
    /// path-unreachable discharge invalidated it for subsumption).
    /// Counts the SUBSUMPTION ATTEMPTS that were short-circuited; not
    /// the number of distinct invalidated cache entries.
    pub children_unsafe_skips: u64,
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
    /// Mapping from an iter_next kfunc call pc to the iter slot it
    /// operates on `(frame_idx, stack_offset)`. Populated lazily by
    /// `iter_next_fork` on first visit. Read by iter-loop pruning
    /// (`handle_loop_pruning`) to identify which iter slot's
    /// `iter.depth` to inspect when deciding whether to defer the
    /// back-edge target prune in an iter loop body — the iter slot
    /// belonging to THIS loop's iter_next, not unrelated iters that
    /// happen to be active in some outer/inner nesting.
    pub iter_pc_slot: HashMap<usize, (usize, i16)>,
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
    /// Kernel `bpf_verifier_env::jmps_processed` (verifier.c v6.15
    /// L19553). Incremented once per BPF_JMP/JMP32-class insn. Used by
    /// the `add_new_state` sparse-cache heuristic.
    pub jmps_processed: usize,
    /// Snapshots at the most recent cache event (kernel
    /// `prev_jmps_processed` / `prev_insn_processed` L19260-L19261).
    pub prev_jmps_processed: usize,
    pub prev_insn_processed: usize,
    /// Per-PC visit counter (only populated when `ZOVIA_DUMP_VISITS=1`).
    /// Bumped once per non-pruned state expansion. Used by the per-PC
    /// audit dump to localize path-explosion hotspots vs the kernel
    /// verifier's per-PC visit count from the log_level-2 trace.
    pub pc_visit_count: HashMap<usize, u64>,
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

    /// Transient mirror of the kernel's `bcf->path_unreachable`. Set by
    /// the generic-load rejection site when a `kind=UNREACHABLE` bundle
    /// entry is emitted (cvc5 proved the accumulated `path_cond` unsat).
    /// The load transfer consumes it: it resets the flag and drops the
    /// path (no successors), the analog of the single-pass kernel's
    /// bundle discharge → `PROCESS_BPF_EXIT`.
    pub bcf_path_unreachable: bool,

    /// Breadcrumb index of the instruction currently being transferred
    /// (the just-recorded step in `history`). Set by `run_worklist`
    /// immediately after `history.record`, before the transfer. The
    /// in-flight `State` still carries its *parent* `history_idx`
    /// (`current_step_idx` is only assigned to *successors*), so a
    /// reactive path-unreachable discharge fired from inside a transfer
    /// must use THIS — the rejecting insn's own breadcrumb — as the
    /// `bcf_suffix_base_pc` walk start, mirroring the kernel's
    /// `backtrack_states` `last_idx = cur->insn_idx` (verifier.c
    /// ~24434) with `skip_first=true`. Starting from the parent
    /// breadcrumb skips one insn too early — benign for a load reject,
    /// fatal for a helper-call reject whose skipped predecessor is an
    /// argument's only definition.
    pub current_step_idx: Option<usize>,

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

    /// Mirror of kernel `env->scc_info` / per-callchain `bpf_scc_visit`
    /// (verifier.c v6.15 ~L2165, include/linux/bpf_verifier.h L717).
    /// Keyed by `SccCallchain`: callsites of outer frames + scc_id of
    /// the innermost SCC-bearing frame. Lifecycle:
    ///   * `maybe_enter_scc` (called on each cache event) populates
    ///     the visit and records the FIRST cur cache_id as
    ///     `entry_state_cache_id` if not yet set.
    ///   * `add_scc_backedge` (called from handle_loop_pruning on a
    ///     RANGE_WITHIN hit) appends backedge snapshots.
    ///   * `maybe_exit_scc` (called from complete_dfs_branch when the
    ///     entry state's branches → 0) drains backedges into
    ///     propagate_backedges and clears `entry_state_cache_id`.
    pub scc_visits: crate::analysis::flow::scc::SccVisitMap,
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
            iter_pc_slot: HashMap::new(),
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
            jmps_processed: 0,
            prev_jmps_processed: 0,
            prev_insn_processed: 0,
            pc_visit_count: HashMap::new(),
            error: None,
            history: History::new(),
            certificate,
            analyzing_exception_cb: false,
            next_cache_id: 0,
            cache_loc_by_id: HashMap::new(),
            precise_pcs: HashSet::new(),
            scc_visits: crate::analysis::flow::scc::SccVisitMap::new(),
            bcf_proofs: Vec::new(),
            bcf_size_reg: None,
            bcf_path_unreachable: false,
            current_step_idx: None,
        }
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
                let step_linked = step.linked_regs.clone();
                // Kernel `bt_sync_linked_regs` (verifier.c L4116-4147),
                // called BEFORE the per-insn backtrack (L4187): if any reg
                // in this conditional's recorded id-linked class is
                // already precise, all become precise. Mirrors the
                // forward `collect_linked_regs`/`push_insn_history`.
                bt_sync_linked_regs(&mut frontier, &step_linked);
                update_frontier(&mut frontier, &instr_copy, &caller_saved);
                // Kernel `bt_sync_linked_regs` is invoked AGAIN after
                // `backtrack_insn` (L4440) — the conditional-jump BPF_X
                // arm may have just added the other operand, which must
                // also propagate across the linked class.
                bt_sync_linked_regs(&mut frontier, &step_linked);
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
                // Linked-scalar precision propagation: marking a scalar
                // precise also marks every reg sharing its scalar id IN
                // THIS cached state precise. Mirrors kernel
                // `mark_chain_precision`'s linked-regs handling (Eduard
                // Zingerman, "bpf: propagate precision in
                // mark_chain_precision for linked scalars") — the exact
                // mechanism verifier_scalar_ids.c::check_ids_in_regsafe*
                // / linked_regs_* exercise. Without it, regsafe's
                // `scalar_ids_subsumed_by` only checks the directly-marked
                // reg's id and misses the id-linkage inconsistency between
                // a checkpoint where two scalars share an id and a sibling
                // path where they do not, wrongly subsuming the unsafe
                // path. `State::mark_reg_precise` performs the in-state
                // id-class propagation; collect the resulting set so the
                // eviction-resistant `precise_pcs` mirror stays consistent.
                let mut marked: Vec<Reg> = Vec::new();
                if let Some(states) = self.explored_states.get_mut(&pc)
                    && let Some(s) = states.get_mut(idx)
                {
                    for &r in &frontier {
                        s.mark_reg_precise(r);
                    }
                    marked = s.precise_regs.iter().copied().collect();
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
                for r in marked {
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

    /// Mirror of kernel `maybe_enter_scc` (verifier.c v6.15 L2228).
    /// Called on every cache event (right after `record_state` mints
    /// a new cache_id). If the new state's frame chain leads into an
    /// SCC, ensure a `SccVisit` entry exists for its callchain; if
    /// the visit is fresh (no entry_state recorded yet), assign
    /// `entry_state_cache_id = cid` so we know which cached state to
    /// pair with `maybe_exit_scc` when its DFS subtree drains.
    pub fn maybe_enter_scc(&mut self, state: &State, cid: u32) {
        let Some(callchain) =
            crate::analysis::flow::scc::compute_scc_callchain(state, &self.insn_aux_data)
        else {
            return;
        };
        let visit = self.scc_visits.entry(callchain).or_default();
        if visit.entry_state_cache_id.is_none() {
            visit.entry_state_cache_id = Some(cid);
        }
    }

    /// Mirror of kernel `maybe_exit_scc` (verifier.c v6.15 L2253).
    /// Called from `complete_dfs_branch` when a cached state's
    /// `branches` first hits 0. If that state was the SCC visit's
    /// `entry_state`, the visit is now done — flush backedges via
    /// `propagate_backedges` (landed in step 3) and clear
    /// `entry_state_cache_id` so a later re-entry creates a fresh
    /// visit.
    ///
    pub fn maybe_exit_scc(&mut self, cid: u32) {
        // Identify the callchain belonging to `cid`'s cached state.
        let Some(&(pc, idx)) = self.cache_loc_by_id.get(&cid) else {
            return;
        };
        // Snapshot the State so we can compute the callchain without
        // holding a long mutable borrow.
        let state_snapshot = match self
            .explored_states
            .get(&pc)
            .and_then(|v| v.get(idx))
        {
            Some(s) => s.clone(),
            None => return,
        };
        let Some(callchain) =
            crate::analysis::flow::scc::compute_scc_callchain(&state_snapshot, &self.insn_aux_data)
        else {
            return;
        };
        // Check entry + take backedges out without holding a long borrow.
        let backedges = {
            let Some(visit) = self.scc_visits.get_mut(&callchain) else {
                return;
            };
            if visit.entry_state_cache_id != Some(cid) {
                return;
            }
            visit.entry_state_cache_id = None;
            std::mem::take(&mut visit.backedges)
        };
        // Kernel `propagate_backedges` (verifier.c v6.15 L20079):
        // iterate the backedges list, calling propagate_precision on
        // each until fixpoint or MAX_BACKEDGE_ITERS. Each iteration
        // propagates precision marks from equal_state into the
        // backedge state's lineage. Kernel caps at 64; beyond that
        // it falls back to mark_all_scalars_precise on every
        // backedge (conservative).
        const MAX_BACKEDGE_ITERS: usize = 64;
        if backedges.is_empty() {
            return;
        }
        for _ in 0..MAX_BACKEDGE_ITERS {
            let mut changed = false;
            for be in &backedges {
                // Look up equal_state by cache_id; if evicted, skip
                // this backedge.
                let Some(&(epc, eidx)) = self.cache_loc_by_id.get(&be.equal_state_cache_id) else {
                    continue;
                };
                let Some(equal_state) = self
                    .explored_states
                    .get(&epc)
                    .and_then(|v| v.get(eidx))
                    .cloned()
                else {
                    continue;
                };
                // propagate_precision(cur=be.state, old=equal_state)
                // — pull equal_state's precise_regs into be.state's
                // ancestor lineage (parent_cache_id chain). The
                // method already exists for the same purpose in
                // standard subsumption hits; here we run it
                // post-hoc per backedge.
                let precise: Vec<Reg> = equal_state.precise_regs.iter().copied().collect();
                if precise.is_empty() {
                    continue;
                }
                if let Some(hidx) = be.state.history_idx {
                    let before = self.precise_pcs.len();
                    for r in precise {
                        self.mark_chain_precision_backward(hidx, be.state.parent_cache_id, r);
                    }
                    if self.precise_pcs.len() != before {
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// Mirror of kernel `incomplete_read_marks` (verifier.c v6.15
    /// L2327). Returns true iff the cached state's SCC visit has any
    /// pending backedges (i.e., the SCC hasn't yet been processed by
    /// `propagate_backedges`). Used in step 4 to gate
    /// RANGE_WITHIN vs NOT_EXACT subsumption strictness — replaces
    /// zovia's current `prev.branches > 0` approximation.
    pub fn incomplete_read_marks(&self, state: &State) -> bool {
        let Some(callchain) =
            crate::analysis::flow::scc::compute_scc_callchain(state, &self.insn_aux_data)
        else {
            return false;
        };
        self.scc_visits
            .get(&callchain)
            .map(|v| !v.backedges.is_empty())
            .unwrap_or(false)
    }

    /// Add a backedge to the SCC visit owning `equal_state_cache_id`'s
    /// callchain. Called from handle_loop_pruning at the hit point
    /// when the cached state belongs to an open SCC visit. Mirror of
    /// kernel `add_scc_backedge` (verifier.c v6.15 L2295).
    pub fn add_scc_backedge(
        &mut self,
        cur: &State,
        equal_state_cache_id: u32,
        insn_idx: usize,
    ) {
        // The kernel keys add_scc_backedge on `sl->state` (the cached
        // state we hit against) — same callchain as cur because both
        // are in the same SCC visit instance.
        let Some(&(epc, eidx)) = self.cache_loc_by_id.get(&equal_state_cache_id) else {
            return;
        };
        let Some(equal_state) = self.explored_states.get(&epc).and_then(|v| v.get(eidx)) else {
            return;
        };
        let Some(callchain) =
            crate::analysis::flow::scc::compute_scc_callchain(equal_state, &self.insn_aux_data)
        else {
            return;
        };
        let Some(visit) = self.scc_visits.get_mut(&callchain) else {
            return;
        };
        // Don't accumulate if the visit is closed (no entry_state).
        if visit.entry_state_cache_id.is_none() {
            return;
        }
        visit.backedges.push(crate::analysis::flow::scc::SccBackedge {
            state: cur.clone(),
            equal_state_cache_id,
            insn_idx,
        });
    }

    /// Read a cached state's (branches, dfs_depth, loop_entry_cache_id)
    /// without holding a borrow on env.explored_states. Returns None if
    /// the cache_id has been evicted.
    fn cached_scc_info(&self, cid: u32) -> Option<(u32, u32, Option<u32>)> {
        let &(pc, idx) = self.cache_loc_by_id.get(&cid)?;
        let st = self.explored_states.get(&pc)?.get(idx)?;
        Some((st.branches, st.dfs_depth, st.loop_entry_cache_id))
    }

    /// Mirror of kernel `get_loop_entry` (verifier.c v6.15 L1919). Walks
    /// the loop_entry chain to the OUTERMOST loop entry. Returns the
    /// final cache_id (or `None` if `start` has no loop_entry).
    pub fn get_loop_entry(&self, start_cache_id: u32) -> Option<u32> {
        let (_, _, mut le) = self.cached_scc_info(start_cache_id)?;
        let mut steps: u32 = 0;
        while let Some(cid) = le {
            // Defensive bound: walks deeper than max plausible DFS depth
            // indicate a cycle in the loop_entry chain (a bug).
            steps += 1;
            if steps > 4096 {
                break;
            }
            match self.cached_scc_info(cid) {
                Some((_, _, Some(next))) => le = Some(next),
                _ => return Some(cid),
            }
        }
        // Edge: start had loop_entry=Some(cid) but that cid had no entry
        // → outermost was `cid`.
        self.cached_scc_info(start_cache_id)
            .and_then(|(_, _, le)| le)
    }

    /// Mirror of kernel `update_loop_entry` (verifier.c v6.15 L1934).
    /// If `hdr_cache_id`'s branches > 0 (hdr's DFS is still open / hdr is
    /// on the current DFS path) AND hdr's dfs_depth is less than
    /// `cur`'s effective loop_entry depth, set cur.loop_entry = hdr.
    /// `cur` here is a worklist state (not yet cached), so we mutate it
    /// directly.
    pub fn update_loop_entry(&self, cur: &mut State, hdr_cache_id: u32) {
        let Some((hdr_br, hdr_depth, _)) = self.cached_scc_info(hdr_cache_id) else {
            return;
        };
        if hdr_br == 0 {
            return;
        }
        // Effective depth: cur.loop_entry's depth if set, else cur's own.
        let cur_eff_depth = match cur.loop_entry_cache_id {
            Some(le_cid) => self
                .cached_scc_info(le_cid)
                .map(|(_, d, _)| d)
                .unwrap_or(cur.dfs_depth),
            None => cur.dfs_depth,
        };
        if hdr_depth < cur_eff_depth {
            cur.loop_entry_cache_id = Some(hdr_cache_id);
        }
    }

    /// Decrement-and-walk on `parent_cache_id` lineage: mirrors kernel
    /// `update_branch_counts` (verifier.c L1955). Called when a worklist
    /// state's DFS exploration terminates (pruned/exit/reject/forked).
    /// `start_cache_id` is the parent_cache_id of the completing state.
    /// At each cached parent:
    /// - branches -= 1
    /// - if branches becomes 0 AND this state has a loop_entry, propagate
    ///   it to the grandparent via update_loop_entry
    /// - if branches > 0, stop (other DFS paths through parent still open)
    /// - else continue walking up
    pub fn complete_dfs_branch(&mut self, start_cache_id: Option<u32>) {
        let mut next = start_cache_id;
        let mut budget: u32 = 16_384;
        while let Some(cid) = next {
            if budget == 0 {
                break;
            }
            budget -= 1;
            let Some(&(pc, idx)) = self.cache_loc_by_id.get(&cid) else {
                break;
            };
            let Some(st) = self.explored_states.get_mut(&pc).and_then(|v| v.get_mut(idx)) else {
                break;
            };
            if st.branches > 0 {
                st.branches -= 1;
            }
            // Kernel-faithful dfs_paths decrement (parallel counter, see
            // State::dfs_paths). Walks the SAME chain as branches but
            // its 0-floor is what the inf-loop trap gate consults.
            if st.dfs_paths > 0 {
                st.dfs_paths -= 1;
            }
            let still_open = st.branches > 0;
            let st_parent = st.parent_cache_id;
            let st_loop_entry = st.loop_entry_cache_id;
            if !still_open {
                // This cached state's DFS subtree just completed. Mirror
                // kernel `clean_live_states` -> `clean_verifier_state`
                // (verifier.c v6.15 L19528 / L19482): mutate the cached
                // state to drop dead regs / dead stack slots, making
                // future subsumption against it looser.
                self.clean_verifier_state(cid);
                // Kernel `maybe_exit_scc` (verifier.c L2253, called
                // from update_branch_counts when branches→0): if this
                // cached state is the entry of an SCC visit, the
                // visit is now done — propagate_backedges fires and
                // the visit is reset. Step 2 (current): backedges
                // list is empty; this is a no-op. Step 3 wires
                // propagate_backedges into maybe_exit_scc proper.
                self.maybe_exit_scc(cid);
            }
            if still_open {
                // Other DFS paths through this parent still open ⇒ stop.
                // Still propagate the loop_entry hint if applicable.
                if let (Some(le), Some(parent_cid)) = (st_loop_entry, st_parent) {
                    // Read le's info first (immutable borrow), then mutate
                    // parent record. Cloning the &(ppc,pidx) tuple makes
                    // the lookup borrow short.
                    let hdr_info = self.cached_scc_info(le);
                    let parent_loc = self.cache_loc_by_id.get(&parent_cid).copied();
                    if let (Some((hbr, hd, _)), Some((ppc, pidx))) = (hdr_info, parent_loc)
                        && let Some(p) = self
                            .explored_states
                            .get_mut(&ppc)
                            .and_then(|v| v.get_mut(pidx))
                    {
                        let p_eff_depth = match p.loop_entry_cache_id {
                            Some(_) => p.dfs_depth, // approximation; chain-walk skipped to avoid re-borrow
                            None => p.dfs_depth,
                        };
                        if hbr > 0 && hd < p_eff_depth {
                            p.loop_entry_cache_id = Some(le);
                        }
                    }
                }
                break;
            }
            next = st_parent;
        }
    }

    /// Kernel-aligned `clean_verifier_state` (verifier.c v6.15 L19482)
    /// + `clean_func_state` (L19433). Called when a cached state's
    /// `branches` first hits 0 in `complete_dfs_branch`: its DFS
    /// subtree is complete, so future visits will only COMPARE
    /// against it, never extend through it. At that point dead regs
    /// and dead stack slots are mutated away so a later cur's
    /// subsumption check against this state has fewer comparand
    /// relations to satisfy.
    ///
    /// Per frame `i`, the kernel cleans against `frame_insn_idx(i)`:
    /// the innermost frame at the state's pc, caller frames at the
    /// next-inner frame's `return_pc`. Regs not in
    /// `live_regs_before[frame_ip]` are reset to `NotInit`; stack
    /// slots not in `live_slots[frame_ip]` are dropped (kernel's
    /// `STACK_INVALID` equivalent — zovia stores slots sparsely in a
    /// `BTreeMap`, so removal == invalidation).
    ///
    /// **Soundness:** zovia's existing subsumption already filters
    /// dead regs/slots out of the comparison via the same
    /// `live_regs` / `live_slots` sets (see `domain_subsumed_by`,
    /// `stack_subsumed_by`); this mutation just bakes in the same
    /// filter so the cached state object literally carries less
    /// relation state. The hit/miss verdict for any cur is identical
    /// to the pre-mutation case (live-only compare returns the same
    /// boolean on a subset where the dead slots have been removed).
    ///
    /// **Exempt:** ITER / DYNPTR / IRQ stack slots are NEVER cleaned
    /// — they carry semantic side effects (ref counts, slot ownership)
    /// independent of read-liveness. Kernel `bpf_stack_slot_alive`
    /// has analogous exemptions.
    ///
    /// Idempotent: skipped on already-cleaned states (kernel L19542
    /// `sl->state.cleaned` guard).
    pub fn clean_verifier_state(&mut self, cid: u32) {
        let Some(&(pc, idx)) = self.cache_loc_by_id.get(&cid) else {
            return;
        };

        // Snapshot the frame ips + their live sets BEFORE taking the
        // mutable borrow on explored_states (insn_aux_data lookup
        // borrows env immutably).
        let frame_ips: Vec<usize> = {
            let Some(st) = self.explored_states.get(&pc).and_then(|v| v.get(idx)) else {
                return;
            };
            if st.cleaned {
                return;
            }
            let n = st.frames.depth();
            (0..n)
                .map(|i| {
                    if i + 1 == n {
                        st.pc
                    } else {
                        st.frames
                            .get(crate::analysis::machine::frame_stack::FrameLevel::from_index(i + 1))
                            .return_pc
                    }
                })
                .collect()
        };
        let frame_live: Vec<(HashSet<Reg>, HashSet<i16>)> = frame_ips
            .iter()
            .map(|&fip| match self.insn_aux_data.get(fip) {
                Some(aux) => (aux.live_regs.clone(), aux.live_slots.clone()),
                None => (HashSet::new(), HashSet::new()),
            })
            .collect();

        // Mutate. Full clean (kernel `clean_func_state` faithful):
        // both stack slots AND register state. Per-frame live_regs /
        // live_slots comes from static MAY-liveness (matches the
        // kernel's `live_regs_before`).
        //
        // ITER/DYNPTR/IRQ stack slots are NEVER cleaned — they carry
        // semantic side effects beyond read-liveness. Kernel
        // `bpf_stack_slot_alive` has analogous exemptions.
        use crate::analysis::machine::frame_stack::FrameLevel;
        use crate::analysis::machine::reg_types::RegType;
        let Some(st) = self
            .explored_states
            .get_mut(&pc)
            .and_then(|v| v.get_mut(idx))
        else {
            return;
        };
        let n_frames = st.frames.depth();
        // Snapshot slot_anchored BEFORE any slot cleaning (subsequent
        // per-frame loop drops dead slots).
        let mut slot_anchored: std::collections::HashSet<Reg> = std::collections::HashSet::new();
        for fi in 0..n_frames {
            let frame = st.frames.get(FrameLevel::from_index(fi));
            for off in frame.stack.slot_offsets() {
                if let Some(slot) = frame.stack.get_slot(off)
                    && let Some(src) = slot.source_reg
                {
                    slot_anchored.insert(src);
                }
            }
        }
        for (i, (live_regs, live_slots)) in frame_live.iter().enumerate() {
            let level = FrameLevel::from_index(i);
            let frame = st.frames.get_mut(level);
            // Slot clean.
            let off_to_clean: Vec<i16> = frame
                .stack
                .slot_offsets()
                .into_iter()
                .filter(|off| !live_slots.contains(off))
                .filter(|&off| {
                    if let Some(slot) = frame.stack.get_slot(off) {
                        slot.iterator.is_none()
                            && slot.dynptr.is_none()
                            && slot.irq_flag.is_none()
                    } else {
                        true
                    }
                })
                .collect();
            for off in off_to_clean {
                frame.stack.slots.remove(&off);
            }
            // Caller-frame reg snapshot clean (only for non-innermost
            // frames; innermost frame's regs live in top-level
            // st.types, handled below).
            if i + 1 < n_frames {
                for r in Reg::ALL {
                    if r == Reg::R10 || r == Reg::Zero {
                        continue;
                    }
                    if !live_regs.contains(&r) {
                        frame.caller_types.set(r, RegType::NotInit);
                    }
                }
            }
        }
        // Innermost frame: regs in st.types. Don't clean a reg whose
        // value is currently anchored to a spilled scalar slot via
        // `source_reg` — the spill/fill chain depends on the reg's
        // value being recoverable from the slot, and the kernel's
        // `clean_func_state` is sound here only because
        // `bpf_live_stack_query_init` propagates per-path read marks
        // we don't yet mirror. Carve-out preserves
        // `tracking_for_u32_spill_fill`-style soundness without
        // requiring the full per-path liveness port.
        let inner_live = frame_live
            .last()
            .map(|(r, _)| r.clone())
            .unwrap_or_default();
        for r in Reg::ALL {
            if r == Reg::R10 || r == Reg::Zero {
                continue;
            }
            if !inner_live.contains(&r) && !slot_anchored.contains(&r) {
                st.types.set(r, RegType::NotInit);
                st.tnums.remove(&r);
                st.scalar_ids.remove(&r);
                st.precise_regs.remove(&r);
            }
        }
        // Audit dump (ZOVIA_DUMP_CLEAN=1): which regs got reset to
        // NotInit at this cached state's pc. Used to diagnose
        // tracking_for_u32_spill_fill-style FAs where the static
        // MAY-liveness incorrectly marks a reg dead.
        if std::env::var("ZOVIA_DUMP_CLEAN").ok().as_deref() == Some("1") {
            let cleaned_regs: Vec<usize> = (0..10)
                .filter(|i| !inner_live.iter().any(|r| {
                    crate::analysis::machine::reg::reg_to_index(*r) == Some(*i)
                }))
                .collect();
            eprintln!(
                "[clean] pc={} cid={} cleaned_innermost_regs={:?} (live_regs={:?})",
                pc, cid, cleaned_regs, inner_live
            );
        }

        st.cleaned = true;
    }

    /// Mirror of kernel `bcf_refine`'s parent-marking
    /// (verifier.c:24580-81: `for i in 0..vstate_cnt-1:
    /// parents[i]->children_unsafe = true`). After a path-unreachable
    /// refinement at `cur`'s reject site, walk `cur`'s
    /// `parent_cache_id` lineage and mark every cached ancestor
    /// `children_unsafe` so it can no longer prune a later arrival.
    /// Without this, zovia subsumes the kernel's *second* route to
    /// the same reject against the first route's cached ancestor and
    /// never emits the second route's distinct path-unreachable
    /// bundle entry (cilium bpf_wireguard pc246 route-B:
    /// 448B/0xf4f14bfbef845f45). The chain (not all-states-at-pc) is
    /// the faithful analog — only this path's ancestors, like the
    /// kernel's `parents[]` vstate chain.
    ///
    /// `base_pc` bounds the walk to the kernel's backtrack SUFFIX
    /// (`bcf->parents[0..vstate_cnt-1]`, same suffix
    /// `bcf_suffix_base_pc` feeds the path_cond filter): only
    /// ancestors with `pc >= base_pc` are marked. The kernel does
    /// NOT mark to program entry; full-lineage marking over-
    /// suppresses pruning and explodes route enumeration. `None`
    /// (kernel `backtrack_states` -EFAULT keep-all) means no lower
    /// bound — mark the whole lineage (conservative).
    pub fn mark_path_children_unsafe(&mut self, cur: &State, base_pc: Option<usize>) {
        let mut id = cur.parent_cache_id;
        let mut budget: usize = 16_384;
        let dump = std::env::var("ZOVIA_DUMP_DISCHARGE").ok().as_deref() == Some("1");
        let mut marked = 0usize;
        let mut first_pc: Option<usize> = None;
        let mut last_pc: Option<usize> = None;
        while let Some(cid) = id {
            if budget == 0 {
                break;
            }
            budget -= 1;
            let Some(&(pc, idx)) = self.cache_loc_by_id.get(&cid) else {
                break;
            };
            if let Some(bp) = base_pc
                && pc < bp
            {
                // Past the backtrack suffix base — kernel parents[]
                // span only the suffix; stop here.
                break;
            }
            let Some(s) = self
                .explored_states
                .get_mut(&pc)
                .and_then(|v| v.get_mut(idx))
            else {
                break;
            };
            if s.children_unsafe {
                // Already marked: this prefix (and its ancestors) was
                // marked by an earlier path-unreachable on the same
                // lineage — stop, the rest is already done.
                break;
            }
            s.children_unsafe = true;
            marked += 1;
            if first_pc.is_none() { first_pc = Some(pc); }
            last_pc = Some(pc);
            id = s.parent_cache_id;
        }
        if dump {
            eprintln!(
                "[disc] marked {} ancestors  pc=[{:?}..{:?}]  base_pc={:?}",
                marked, last_pc, first_pc, base_pc
            );
        }
    }

    /// Compute the PC at which all `target_regs`' definition chains have
    /// bottomed out (the kernel's "base state" PC). Query-only mirror of
    /// `backtrack_states` (vendor verifier.c; in
    /// `/Users/yalucai/bpf-next-zovia/kernel/bpf/verifier.c` at the
    /// `backtrack_states` definition): walks backward through the linear
    /// breadcrumb history starting from `history_idx`, applying a
    /// **faithful port of the kernel's `backtrack_insn`**
    /// ([`backtrack_insn_step`] over a per-frame [`BacktrackState`]:
    /// register + stack-slot masks, exact per-opcode data-flow, the
    /// kernel's `INSN_F_STACK_ACCESS` register-spill/fill gate, precise
    /// `bt_empty` termination), and returns the PC at which `bt` first
    /// becomes empty. Used by BCF refinement sites to filter eager
    /// `SymbolicState::path_conds` down to the suffix the kernel's
    /// `bcf_track` would emit.
    ///
    /// (`mark_chain_precision_backward` is a *separate* mechanism — the
    /// kernel `__mark_chain_precision` precision-marking heuristic — and
    /// keeps the older flat-frontier `update_frontier`; do not conflate
    /// the two.)
    ///
    /// Semantics — mirrors `backtrack_states` step-by-step:
    /// * Initial `bt` = `target_regs` set in the reject state's frame
    ///   (the breadcrumb's call depth = kernel `bt_init(st->curframe)`).
    /// * Walk back through breadcrumbs; the **first** breadcrumb (the
    ///   refine site's own insn) is skipped (`skip_first = true`),
    ///   matching the kernel.
    /// * Apply `backtrack_insn_step` per prior step. When `bt` empties,
    ///   that step's PC is the kernel's base PC — return it.
    /// * If a step hits the kernel's -ENOTSUPP/-EFAULT path, or the walk
    ///   runs out of history without emptying, the kernel aborts with
    ///   `base = NULL`; we return `None` (callers treat that as "keep
    ///   all path_conds" — sound, just not a tighter suffix).
    ///
    /// Returns `None` for empty `target_regs` (kernel returns
    /// `-EFAULT` in that case too) or when the walk runs out.
    /// For a cached state identified by its `cache_id`, return the PC
    /// of the instruction processed IMMEDIATELY BEFORE the cache event
    /// — zovia's analog of the kernel's `vstate->last_insn_idx`. Used
    /// by `filter_path_conds_from_pc` to mirror the kernel's
    /// `record_path_cond` push at `bcf_track` replay start: only
    /// triggers if prev_insn was a scalar conditional branch
    /// (verifier.c:21117 + 21000-21019). Returns `None` if the cache_id
    /// isn't found, or the cached state has no history breadcrumb, or
    /// the breadcrumb is the first (no parent step).
    pub fn cached_prev_insn_pc(&self, cache_id: u32) -> Option<usize> {
        let (pc, idx) = *self.cache_loc_by_id.get(&cache_id)?;
        let cached = self.explored_states.get(&pc)?.get(idx)?;
        let hidx = cached.history_idx?;
        let breadcrumb = self.history.get(hidx)?;
        let parent_idx = breadcrumb.parent_idx?;
        Some(self.history.get(parent_idx)?.pc)
    }

    /// Companion to `bcf_suffix_base_pc`: same walk, but returns
    /// `(base_pc, base_cache_id)` so the caller can also identify the
    /// cached state at the suffix base (needed by
    /// `filter_path_conds_from_pc` to look up that base state's
    /// `prev_insn_pc` and mirror the kernel's `record_path_cond` push
    /// at `bcf_track` replay start).
    pub fn bcf_suffix_base_pc_and_cache_id(
        &self,
        history_idx: usize,
        parent_cache_id: Option<u32>,
        target_regs: &[Reg],
    ) -> Option<(usize, u32)> {
        // Inline a minimal copy of the bcf_suffix_base_pc walk, returning
        // (pc, cache_id) instead of just pc. Logic mirrors the original;
        // diffs are limited to (a) returning the current_parent_id along
        // with parent_loc.pc when bt empties, (b) skipping the entry-arg
        // drain path (it only applies at pc=0, which has no cache_id —
        // callers wanting that termination keep using bcf_suffix_base_pc).
        if target_regs.is_empty() {
            return None;
        }
        let start_depth = self.history.get(history_idx).map(|s| s.depth).unwrap_or(0);
        let mut bt = BacktrackState::new();
        for &r in target_regs {
            bt.set_reg(start_depth, r);
        }
        if bt.is_empty() {
            return None;
        }

        let mut current_history: Option<usize> = Some(history_idx);
        let mut current_parent_id: Option<u32> = parent_cache_id;
        let mut budget: usize = 16_384;
        let mut skip_first = true;

        loop {
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
                    return None;
                }
                budget -= 1;
                if let Some(stop) = parent_history_stop
                    && idx <= stop
                {
                    break;
                }
                let Some(step) = self.history.get(idx) else {
                    return None;
                };
                let parent_idx = step.parent_idx;
                let instr_copy = step.instr.clone();
                let step_depth = step.depth;
                let step_stack_access = step.stack_access;
                if !skip_first {
                    if backtrack_insn_step(&mut bt, &instr_copy, step_depth, step_stack_access).is_err() {
                        return None;
                    }
                    if bt.is_empty() {
                        // Found the suffix base. Return its (pc, cache_id).
                        let (pc, _) = parent_loc?;
                        let cid = current_parent_id?;
                        return Some((pc, cid));
                    }
                }
                skip_first = false;
                current_history = parent_idx;
            }
            if parent_grandparent_id.is_none() {
                return None;
            }
            current_parent_id = parent_grandparent_id;
            current_history = parent_history_stop;
        }
    }

    pub fn bcf_suffix_base_pc(
        &self,
        history_idx: usize,
        parent_cache_id: Option<u32>,
        target_regs: &[Reg],
    ) -> Option<usize> {
        let debug = std::env::var("ZOVIA_BCF_TRACK_DEBUG").is_ok();
        let probe = std::env::var("ZOVIA_DUMP_DISCHARGE").ok().as_deref() == Some("1");
        if probe {
            eprintln!("[bcf-track-start] history_idx={} targets={:?}", history_idx, target_regs);
        }
        if target_regs.is_empty() {
            if probe { eprintln!("[bcf-track-none] reason=EMPTY_TARGETS history_idx={}", history_idx); }
            return None;
        }
        // Initial precision lives in the reject state's call frame. zovia
        // records the call depth on every breadcrumb forward, so it is the
        // authoritative analogue of the kernel's `bt->frame`
        // (`bt_init(bt, st->curframe)` in `backtrack_states`).
        let start_depth = self.history.get(history_idx).map(|s| s.depth).unwrap_or(0);
        let mut bt = BacktrackState::new();
        for &r in target_regs {
            bt.set_reg(start_depth, r);
        }
        if bt.is_empty() {
            if probe { eprintln!("[bcf-track-none] reason=BT_INIT_EMPTY"); }
            return None;
        }
        if debug {
            eprintln!(
                "[bcf-track] walk start: targets={:?} start_frame={} history_idx={} parent_cache_id={:?}",
                target_regs, start_depth, history_idx, parent_cache_id
            );
        }

        let mut current_history: Option<usize> = Some(history_idx);
        let mut current_parent_id: Option<u32> = parent_cache_id;
        let mut budget: usize = 16_384;
        let mut skip_first = true;
        let mut last_pc_walked: Option<usize> = None;
        let mut first_pc_walked: Option<usize> = None;

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
                let step_depth = step.depth;
                let step_stack_access = step.stack_access;
                if first_pc_walked.is_none() { first_pc_walked = Some(step_pc); }
                last_pc_walked = Some(step_pc);

                if !skip_first {
                    if backtrack_insn_step(&mut bt, &instr_copy, step_depth, step_stack_access).is_err() {
                        // Kernel `backtrack_insn` returned a negative errno
                        // (-ENOTSUPP / -EFAULT): `backtrack_states` aborts
                        // with `base = NULL`, which on the zovia side means
                        // "keep all accumulated path_conds" — sound, just
                        // not a tighter suffix.
                        if debug {
                            eprintln!(
                                "[bcf-track]   pc={:>3} {:?} -> ERR (keep all path_conds)",
                                step_pc, instr_copy
                            );
                        }
                        if probe { eprintln!("[bcf-track-none] reason=BACKTRACK_INSN_ERR pc={} instr={:?} regs={:?} stack={:?}", step_pc, instr_copy, bt.reg_masks, bt.stack_masks); }
                        return None;
                    }
                    if debug {
                        eprintln!(
                            "[bcf-track]   pc={:>3} d={} {:?} regs={:?} stack={:?}",
                            step_pc, step_depth, instr_copy, bt.reg_masks, bt.stack_masks
                        );
                    }
                    if bt.is_empty() {
                        if debug {
                            eprintln!("[bcf-track] bt empty at pc={}", step_pc);
                        }
                        // Kernel `backtrack_states` L24578-L24584 on
                        // bt_empty: `base = st->parent`. zovia's analog
                        // is `parent_loc` (the cached state at the
                        // current parent_cache_id, i.e. `st->parent` at
                        // this outer-iter level). Return its PC, NOT
                        // step_pc (which is kernel's `i`, the per-insn
                        // walk variable). Under sparse caching
                        // (`ZOVIA_KERNEL_ENGINE=1`), this yields a
                        // base_pc that matches the kernel's chain.
                        return parent_loc.map(|(pc, _)| pc);
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

        // Kernel-faithful program-entry termination. If the walker reached
        // pc 0 (the BPF program's first insn — clang's `r9 = r1` ctx-arg
        // capture is the canonical case) and the only remaining bits in
        // `bt` are BPF input arg regs (R1..R5) in the entry frame, those
        // regs are defined by the caller (the BPF runtime), not by any
        // in-program insn. The kernel's `backtrack_states` handles this
        // implicitly because input-arg precision is satisfied at frame
        // entry; the kernel's `bt_reg_mask(bt) & BPF_REGMASK_ARGS` is the
        // exact analog of `BacktrackState::args_set`.
        //
        // Without this drain, every BCF discharge that walks back to pc 0
        // returns `None`, which `mark_path_children_unsafe` interprets as
        // "no suffix bound — mark the whole lineage `children_unsafe`."
        // That over-marking is what blows calico_tc_main from 1,801 insns
        // (base verifier, no --bcf) to 1M timeout (with --bcf):
        // 750 discharges × ~73 ancestors marked each, 96% of subsumption
        // attempts short-circuit on poisoned cache entries.
        if last_pc_walked == Some(0) {
            for arg in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
                bt.clear_reg(start_depth, arg);
            }
            if bt.is_empty() {
                if probe {
                    eprintln!("[bcf-track-entry-drain] succeeded → returning Some(0)");
                }
                return Some(0);
            }
        }

        if probe {
            eprintln!(
                "[bcf-track-none] reason=WALKED_WHOLE_HISTORY budget_used={} first_pc={:?} last_pc={:?} regs_still_in_bt={:?} stack_still_in_bt={:?}",
                16_384 - budget, first_pc_walked, last_pc_walked, bt.reg_masks, bt.stack_masks
            );
        }
        None
    }
}

/// Kernel `bt_sync_linked_regs` (verifier.c L4116-4147): the breadcrumb
/// for a conditional jump records the scalar registers that shared the
/// compared register's scalar id (`collect_linked_regs`). If ANY of them
/// is currently in the precision frontier, ALL of them must be — the
/// kernel propagates a refined range across the whole id class, so a
/// precision requirement on one is a precision requirement on all.
fn bt_sync_linked_regs(frontier: &mut HashSet<Reg>, linked: &[Reg]) {
    if linked.len() < 2 {
        return;
    }
    if linked.iter().any(|r| frontier.contains(r)) {
        for &r in linked {
            frontier.insert(r);
        }
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
        Instr::If { left, right, .. } => {
            // Kernel `backtrack_insn` conditional-jump arm
            // (verifier.c L4407-4424):
            //   BPF_X (`dreg <cond> sreg`): if NEITHER operand needs
            //     precision, the jump is irrelevant — no change. If
            //     EITHER does, BOTH operands needed precision before
            //     this insn (the branch outcome depended on both), so
            //     add both.
            //   BPF_K (`dreg <cond> K`): only dreg still needs
            //     precision, which is already reflected — nothing new.
            if let Operand::Reg(s) = right
                && (frontier.contains(left) || frontier.contains(s))
            {
                frontier.insert(*left);
                frontier.insert(*s);
            }
        }
        _ => {}
    }
}

/// Per-frame register + stack-slot precision masks — a faithful mirror
/// of the kernel's `struct backtrack_state` (vendor verifier.c). For
/// frame `f`: `reg_masks[f]` bit `i` (`Reg::bcf_idx`, 0..=10 where 10 =
/// `BPF_REG_FP`/R10) tracks a register that needs precision; and
/// `stack_masks[f]` bit `spi` tracks a spilled-scalar stack slot. Frames
/// are indexed by the breadcrumb's call depth (zovia records this
/// forward — the authoritative analogue of the kernel's `bt->frame`).
struct BacktrackState {
    reg_masks: Vec<u16>,
    stack_masks: Vec<u64>,
}

impl BacktrackState {
    fn new() -> Self {
        Self { reg_masks: Vec::new(), stack_masks: Vec::new() }
    }

    #[inline]
    fn ensure(&mut self, frame: usize) {
        if self.reg_masks.len() <= frame {
            self.reg_masks.resize(frame + 1, 0);
            self.stack_masks.resize(frame + 1, 0);
        }
    }

    #[inline]
    fn set_reg(&mut self, frame: usize, reg: Reg) {
        if let Some(b) = reg.bcf_idx() {
            self.ensure(frame);
            self.reg_masks[frame] |= 1u16 << b;
        }
    }

    #[inline]
    fn clear_reg(&mut self, frame: usize, reg: Reg) {
        if let Some(b) = reg.bcf_idx()
            && frame < self.reg_masks.len()
        {
            self.reg_masks[frame] &= !(1u16 << b);
        }
    }

    #[inline]
    fn is_reg_set(&self, frame: usize, reg: Reg) -> bool {
        reg.bcf_idx().is_some_and(|b| {
            frame < self.reg_masks.len() && self.reg_masks[frame] & (1u16 << b) != 0
        })
    }

    #[inline]
    fn set_slot(&mut self, frame: usize, spi: u32) {
        self.ensure(frame);
        self.stack_masks[frame] |= 1u64 << spi;
    }

    #[inline]
    fn clear_slot(&mut self, frame: usize, spi: u32) {
        if frame < self.stack_masks.len() {
            self.stack_masks[frame] &= !(1u64 << spi);
        }
    }

    #[inline]
    fn is_slot_set(&self, frame: usize, spi: u32) -> bool {
        frame < self.stack_masks.len() && self.stack_masks[frame] & (1u64 << spi) != 0
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.reg_masks.iter().all(|&m| m == 0) && self.stack_masks.iter().all(|&m| m == 0)
    }

    /// Any of R1..R5 (the BPF arg registers) still set in `frame`. Mirror
    /// of kernel `bt_reg_mask(bt) & BPF_REGMASK_ARGS`.
    #[inline]
    fn args_set(&self, frame: usize) -> bool {
        // bcf_idx: R1=1 .. R5=5 ⇒ bits 1..=5.
        frame < self.reg_masks.len() && self.reg_masks[frame] & 0b0011_1110 != 0
    }
}

/// Kernel stack-slot index for a frame-pointer-relative register
/// spill/fill, or `None` if this access is *not* a tracked register
/// spill/fill (so the kernel records `insn_flags = 0` and
/// `backtrack_insn` does not follow it into the slot).
///
/// The kernel records `INSN_F_STACK_ACCESS` only for an 8-byte-aligned,
/// `BPF_REG_SIZE`-sized access (`!(off % BPF_REG_SIZE) && size ==
/// BPF_REG_SIZE` in `check_stack_{read,write}_fixed_off`); partial /
/// unaligned writes and non-restoring fills are plain stack data
/// (STACK_MISC/ZERO), `insn_flags = 0`. Mirroring that gate is what
/// keeps the precision suffix from running away through every buffer
/// write. `spi = (-off - 1) / BPF_REG_SIZE`; slots ≥ 64 (beyond
/// `MAX_BPF_STACK / 8`) are out of mask range.
#[inline]
fn spi_of(off: i16) -> Option<u32> {
    if off >= 0 {
        return None;
    }
    let slot = (-(off as i32)) - 1;
    if slot < 0 {
        return None;
    }
    let spi = (slot / 8) as u32;
    if spi >= 64 { None } else { Some(spi) }
}

/// Whether a stack-relative LDX/STX continues the precision chain into
/// its slot is no longer guessed structurally (the old `fill_slot` /
/// `store_slot` `off % 8` heuristic over-followed every slot-aligned
/// access). It is now read from the breadcrumb's `stack_access` flag —
/// zovia's analog of the kernel's `hist->flags & INSN_F_STACK_ACCESS`,
/// set forward only for a genuine register spill/fill (see
/// [`crate::analysis::machine::history::Breadcrumb::stack_access`] and
/// the forward marking in the memory transfer). The slot index is still
/// recovered from the insn's own fixed offset via [`spi_of`], exactly as
/// the kernel recovers it from `insn_stack_access_spi(hist->flags)`.

/// Faithful port of the kernel's `backtrack_insn` (vendor verifier.c) for
/// one linear-history step: mutate the per-frame precision masks `bt`
/// given that we are *un-doing* `instr`, which executed in call `frame`.
///
/// `Err(())` mirrors the kernel returning a negative errno (-ENOTSUPP /
/// -EFAULT) from `backtrack_insn`: `backtrack_states` then aborts with
/// `base = NULL`, which on the zovia side means "keep all accumulated
/// path_conds" (sound, just not as tight a suffix).
fn backtrack_insn_step(
    bt: &mut BacktrackState,
    instr: &crate::ast::Instr,
    frame: usize,
    stack_access: bool,
) -> Result<(), ()> {
    use crate::ast::{AluOp, Instr, Operand};
    match instr {
        // ── BPF_ALU / BPF_ALU64 ──────────────────────────────────────
        Instr::Alu { op, dst, src, .. } => {
            if !bt.is_reg_set(frame, *dst) {
                return Ok(());
            }
            match op {
                // BPF_NEG: sreg reserved/unused; dreg still needs
                // precision before this insn — nothing new.
                AluOp::Neg => {}
                AluOp::Mov => {
                    bt.clear_reg(frame, *dst);
                    if let Operand::Reg(s) = src
                        && *s != Reg::R10
                    {
                        // dreg = sreg: sreg needs precision before.
                        bt.set_reg(frame, *s);
                    }
                }
                _ => {
                    // dreg = dreg <op> src: dreg stays precise; a reg
                    // src also needs precision before this insn.
                    if let Operand::Reg(s) = src
                        && *s != Reg::R10
                    {
                        bt.set_reg(frame, *s);
                    }
                }
            }
        }
        // BPF_MOV with sign-extend (BPF_X form): dreg = (sN)sreg.
        Instr::MovSx { dst, src, .. } => {
            if !bt.is_reg_set(frame, *dst) {
                return Ok(());
            }
            bt.clear_reg(frame, *dst);
            if let Operand::Reg(s) = src
                && *s != Reg::R10
            {
                bt.set_reg(frame, *s);
            }
        }
        // BPF_END: like BPF_NEG — dreg stays precise, nothing new.
        Instr::Endian { .. } => {}
        // ── BPF_LDX (incl. atomic load-acquire) ──────────────────────
        Instr::Load { size, dst, base, off }
        | Instr::LoadSx { size, dst, base, off }
        | Instr::LoadAcq { size, dst, base, off } => {
            if !bt.is_reg_set(frame, *dst) {
                return Ok(());
            }
            let _ = (size, base);
            bt.clear_reg(frame, *dst);
            // Kernel `backtrack_insn` BPF_LDX clause: a load from
            // non-stack memory can be zero-extended — precision is
            // already on `dst`, nothing further. Only a *register fill*
            // continues the chain into the slot, and the kernel gates
            // that solely on `hist->flags & INSN_F_STACK_ACCESS`
            // (verifier.c:4612). zovia's `stack_access` breadcrumb flag
            // is that bit; the slot index comes from the insn's fixed
            // offset (kernel `insn_stack_access_spi`).
            if stack_access
                && let Some(spi) = spi_of(*off)
            {
                bt.set_slot(frame, spi);
            }
        }
        // ld_imm64 / map-ptr load: clear dst; no further tracking.
        Instr::LoadMap { dst, .. } => {
            if !bt.is_reg_set(frame, *dst) {
                return Ok(());
            }
            bt.clear_reg(frame, *dst);
        }
        // ld_abs / ld_ind: kernel returns -ENOTSUPP ("to be analyzed").
        Instr::LoadPacket { .. } => return Err(()),
        // ── BPF_STX / BPF_ST (incl. atomics) ─────────────────────────
        // ── BPF_STX / BPF_ST ─────────────────────────────────────────
        // Kernel `backtrack_insn` STX/ST clause (verifier.c:4621):
        //  * a precise *scalar* mem-base ⇒ pointer subtraction ⇒
        //    -ENOTSUPP;
        //  * `!(hist->flags & INSN_F_STACK_ACCESS)` ⇒ `return 0` —
        //    a plain data store does **not** clear the slot (the old
        //    `store_slot` cleared it unconditionally, which severed the
        //    chain a step early when a data write aliased a tracked
        //    spi);
        //  * else clear the slot; for class==BPF_STX propagate precision
        //    to the spilled source reg (BPF_ST const propagates nothing).
        Instr::Store { off, base, src, .. } => {
            if bt.is_reg_set(frame, *base) {
                return Err(());
            }
            if !stack_access {
                return Ok(());
            }
            let Some(spi) = spi_of(*off) else {
                return Ok(());
            };
            if !bt.is_slot_set(frame, spi) {
                return Ok(());
            }
            bt.clear_slot(frame, spi);
            if let Operand::Reg(s) = src {
                bt.set_reg(frame, *s);
            }
        }
        Instr::StoreRel { off, base, src, .. } => {
            if bt.is_reg_set(frame, *base) {
                return Err(());
            }
            if !stack_access {
                return Ok(());
            }
            let Some(spi) = spi_of(*off) else {
                return Ok(());
            };
            if !bt.is_slot_set(frame, spi) {
                return Ok(());
            }
            bt.clear_slot(frame, spi);
            bt.set_reg(frame, *src);
        }
        Instr::Atomic { off, base, src, .. } => {
            if bt.is_reg_set(frame, *base) {
                return Err(());
            }
            if !stack_access {
                return Ok(());
            }
            let Some(spi) = spi_of(*off) else {
                return Ok(());
            };
            if !bt.is_slot_set(frame, spi) {
                return Ok(());
            }
            bt.clear_slot(frame, spi);
            bt.set_reg(frame, *src);
        }
        // ── BPF_JMP / BPF_JMP32 ──────────────────────────────────────
        // Static BPF-to-BPF subprog call. Backtracking *past* it exits
        // the callee back into the caller: r1-r5 (the args) propagate
        // from the callee frame to the caller frame.
        Instr::CallRel { .. } => {
            let callee = frame + 1;
            for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
                if bt.is_reg_set(callee, r) {
                    bt.clear_reg(callee, r);
                    bt.set_reg(frame, r);
                }
            }
        }
        // Helper / kfunc call: sets R0; r1-r5 are clobbered and should
        // have been resolved already (kernel treats leftover args as a
        // verifier bug → -EFAULT → keep-all).
        Instr::Call { .. } => {
            bt.clear_reg(frame, Reg::R0);
            if bt.args_set(frame) {
                return Err(());
            }
        }
        // Subprog/callback return. Backtracking past EXIT enters the
        // callee frame; propagate R0 (the return value) if the caller
        // still needs it precise.
        Instr::Exit => {
            if frame >= 1 {
                let caller = frame - 1;
                let r0_precise = bt.is_reg_set(caller, Reg::R0);
                bt.clear_reg(caller, Reg::R0);
                if r0_precise {
                    bt.set_reg(frame, Reg::R0);
                }
            }
        }
        // Conditional jump. BPF_X: if either operand was precise after,
        // both need precision before. BPF_K / JA: nothing new.
        Instr::If { left, right, .. } => {
            if let Operand::Reg(r) = right {
                if !bt.is_reg_set(frame, *left) && !bt.is_reg_set(frame, *r) {
                    return Ok(());
                }
                bt.set_reg(frame, *r);
                bt.set_reg(frame, *left);
            }
        }
        Instr::Jmp { .. } | Instr::MayGoto { .. } => {}
    }
    Ok(())
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

/// Comma-separated list of PCs (e.g. `ZOVIA_DIAG_PCS=1972,1974,1976,1986,1987`).
/// run_worklist emits a compact per-arrival diagnostic at each: register
/// types + ranges + tnums before/after type-conflict resolution, the
/// prune decision, and successor PCs. Distinguishes the three calico
/// type-collapse loss mechanisms (merge-demote vs precision-strip vs
/// subsumption) in a single run.
pub fn diag_pcs() -> Option<std::collections::HashSet<usize>> {
    let raw = std::env::var("ZOVIA_DIAG_PCS").ok()?;
    let set: std::collections::HashSet<usize> = raw
        .split(',')
        .filter_map(|s| s.trim().parse().ok())
        .collect();
    if set.is_empty() { None } else { Some(set) }
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
