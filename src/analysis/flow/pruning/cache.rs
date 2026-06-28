// src/analysis/flow/pruning/cache.rs
//
// State-cache hygiene: mutate cached states once their DFS subtree
// completes so later subsumption compares against a leaner comparand.
// Mirrors the kernel's clean_verifier_state / clean_live_states, and the
// BCF-discharge children-unsafe invalidation. Free functions over
// `&mut VerifierEnv`, matching the flow/ convention.

use std::collections::HashSet;
use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;

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
pub fn clean_verifier_state(env: &mut VerifierEnv, cid: u32) {
    let Some(&(pc, idx)) = env.cache_loc_by_id.get(&cid) else {
        return;
    };

    // Snapshot the frame ips + their live sets BEFORE taking the
    // mutable borrow on explored_states (insn_aux_data lookup
    // borrows env immutably).
    let frame_ips: Vec<usize> = {
        let Some(st) = env.explored_states.get(&pc).and_then(|v| v.get(idx)) else {
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
        .map(|&fip| match env.insn_aux_data.get(fip) {
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
    let Some(st) = env
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
            frame.stack.remove_slot(off);
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
pub fn mark_path_children_unsafe(env: &mut VerifierEnv, cur: &State, base_pc: Option<usize>) {
    let mut id = cur.parent_cache_id;
    let mut budget: usize = 16_384;
    let dump = std::env::var("ZOVIA_DUMP_DISCHARGE").ok().as_deref() == Some("1");
    // EXPERIMENT (structural distinguisher): do not mark loop-header
    // states children_unsafe. A loop header is a back-edge target — the
    // state cached there is the loop's wide convergence subsumer. The
    // kernel rebuilds it on each BCF retry; zovia's one-shot cascade
    // would permanently invalidate it, collapsing the only state that
    // subsumes the loop's R1×R8×R9 fan (accepted_entrypoint pc-170 OOM).
    // calico_tc_main marks the same loop region but doesn't depend on it
    // for coverage (its route obligations are straight-line, high-pc).
    let skip_loop_hdr =
        std::env::var("ZOVIA_EXP_SKIP_LOOP_HEADER_UNSAFE").ok().as_deref() == Some("1");
    let mark_defs_only =
        std::env::var("ZOVIA_EXP_MARK_DEFS_ONLY").ok().as_deref() == Some("1");
    let mut marked = 0usize;
    let mut first_pc: Option<usize> = None;
    let mut last_pc: Option<usize> = None;
    while let Some(cid) = id {
        if budget == 0 {
            break;
        }
        budget -= 1;
        let Some(&(pc, idx)) = env.cache_loc_by_id.get(&cid) else {
            break;
        };
        // Kernel `bcf_refine` marks `parents[0..vstate_cnt-1]` where parents[]
        // is built from `cur->parent` walking up to BUT NOT INCLUDING `base`
        // (verifier.c:24570-24585), and the `- 1` also drops `cur`. So the
        // kernel marks the chain EXCLUDING both the reject `cur` (zovia already
        // starts at cur.parent) AND the suffix `base`. The base is the
        // convergence point where the reject's reg_masks backtrack ends — the
        // bottleneck shared by ALL paths to the reject. Leaving it prune-able
        // lets paths CONVERGE there; marking it (zovia's old `pc < bp`) kills
        // that convergence → the demux fan re-explores → route explosion
        // (accepted_entrypoint pc274). ZOVIA_EXP_EXCLUDE_BASE mirrors the
        // kernel: stop AT the base (`pc <= bp`), excluding it.
        let exclude_base =
            std::env::var("ZOVIA_EXP_EXCLUDE_BASE").ok().as_deref() == Some("1");
        // DIAGNOSTIC (pm20): the kernel bounds the children_unsafe marking by
        // how far the reject's reg_masks BACKTRACK reaches, not the suffix
        // `base_pc`. For calico_tc_main pc748 the reg_masks include the
        // protocol scalar spilled at fp-272 (pc746), whose backtrack continues
        // to the proto-demux convergence at pc521 — BELOW base_pc=582. With the
        // suffix bound the pc521 convergence cache stays prunable, so the
        // w1!=6 arm is pruned there and the 6-hash pc748 family is never
        // emitted. `ZOVIA_BCF_DEEP_UNSAFE=<pc>` overrides the lower bound to
        // <pc> to test whether deepening to the reg_masks reach recovers them.
        let deep_unsafe: Option<usize> = std::env::var("ZOVIA_BCF_DEEP_UNSAFE")
            .ok()
            .and_then(|s| s.parse().ok());
        let effective_bp = match (base_pc, deep_unsafe) {
            (Some(bp), Some(d)) => Some(bp.min(d)),
            (b, None) => b,
            (None, Some(d)) => Some(d),
        };
        if let Some(bp) = effective_bp
            && (pc < bp || (exclude_base && deep_unsafe.is_none() && pc == bp))
        {
            break;
        }
        let Some(s) = env
            .explored_states
            .get_mut(&pc)
            .and_then(|v| v.get_mut(idx))
        else {
            break;
        };
        if s.children_unsafe {
            // Already marked by an EARLIER discharge — but do NOT stop:
            // the kernel marks `parents[0..vstate_cnt-1]` UNCONDITIONALLY
            // (verifier.c:24629). Each discharge's backtrack base differs;
            // a shallow discharge (base 579) marks 579→cur, then a later
            // DEEPER discharge (base 521/512/455) walks the same lineage
            // and, hitting the already-marked 742/739 prefix, must keep
            // going to mark the 521→578 segment BELOW it. The old
            // `break` assumed "already-marked ⇒ rest done", which is false
            // when bases vary: it capped the cumulative marked floor at the
            // FIRST discharge's base (579), so the proto-demux convergences
            // at pc521 (calico from_nat_fib) stayed prune-safe and the
            // w1!=6 arm was pruned there → 2a94 never emitted. Continue up
            // the lineage; the `pc < base_pc` bound above still stops it.
            id = s.parent_cache_id;
            continue;
        }
        if skip_loop_hdr && env.loop_header_pcs.contains(&pc) {
            // EXPERIMENT: protect the loop-convergence subsumer; keep
            // walking ancestors (the suffix continues past it).
            id = s.parent_cache_id;
            continue;
        }
        // EXPERIMENT (ZOVIA_EXP_MARK_DEFS_ONLY): skip marking the state cached
        // at a branch pc. A branch is a USE, not a reg definition; its cached
        // state is the convergence subsumer at that demux point. Marking it
        // children_unsafe collapses pruning → route explosion
        // (accepted_entrypoint pc256/267/272). The reg DEF-sites a reject's
        // reg_masks depend on (assignments like pc521 `w1=0`, enabling pc748
        // d53) are NOT branches, so they still get marked. Borrow `s` ends
        // before the env read, so re-fetch is not needed (env.branch_pcs is a
        // separate field).
        if mark_defs_only && env.branch_pcs.contains(&pc) {
            id = s.parent_cache_id;
            continue;
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
