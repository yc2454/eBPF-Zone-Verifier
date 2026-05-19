// src/analysis/flow/pruning/subsumption.rs
//
// Subsumption predicates: state_subsumed_by and all helpers.

use std::collections::HashSet;

use crate::analysis::machine::env::SubsumptionMissReason;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::machine::state::State;
use crate::common::config::VerifierConfig;
use crate::domains::numeric::NumericDomain;
use crate::domains::tnum::Tnum;

fn callee_saved_regs() -> HashSet<Reg> {
    [Reg::R6, Reg::R7, Reg::R8, Reg::R9].into_iter().collect()
}

/// Check if `cur` is subsumed by `old` (old covers all behaviors of cur).
/// Returns `Ok(())` on success or `Err(reason)` identifying the *first*
/// sub-check that rejected. The reason is what the
/// `subsumption_misses` instrumentation aggregates per-PC.
pub(super) fn state_subsumed_by(
    cur: &State,
    old: &State,
    live_regs: &HashSet<Reg>,
    frame_live_slots: &[Option<HashSet<i16>>],
    config: &VerifierConfig,
) -> Result<(), SubsumptionMissReason> {
    // Order matters for instrumentation: the *first* rejecting check
    // is what we record, so cheaper / more-fundamental checks come
    // first to keep the histogram readable.
    if !types_subsumed_by(&cur.types, &old.types, live_regs) {
        // Measurement hatch (mirror ZOVIA_DUMP_DOMAIN_MISS): on a Types
        // miss, re-scan to report the first offending live reg + its
        // (cur, old) RegType at this pc. Runs ONLY when the env var is
        // set AND we already know the check failed — zero hot-path /
        // behavioral effect otherwise. Used to localize the
        // clean_verifier_state / liveness-fidelity gap (skb_drop = 100%
        // types misses).
        if std::env::var("ZOVIA_DUMP_TYPES_MISS").ok().as_deref() == Some("1") {
            for &r in live_regs {
                let ct = cur.types.get(r);
                let ot = old.types.get(r);
                if !type_subsumed_by(&ct, &ot) {
                    eprintln!(
                        "[types_miss] pc={} reg={:?} cur={:?} old={:?}",
                        cur.pc, r, ct, ot
                    );
                    break;
                }
            }
        }
        return Err(SubsumptionMissReason::Types);
    }
    if !config.skip_dbm_check
        && !domain_subsumed_by(&cur.domain, &old.domain, live_regs, &old.precise_regs)
    {
        return Err(SubsumptionMissReason::Domain);
    }
    if !stack_subsumed_by(cur, old, frame_live_slots) {
        return Err(SubsumptionMissReason::Stack);
    }
    if !tnum_subsumed_by(cur, old, live_regs) {
        return Err(SubsumptionMissReason::Tnum);
    }

    // regsafe scalar-id check.
    // If two live registers share a scalar_id in `old` (so a future
    // refinement on one will propagate to the other along the cached
    // continuation), `cur` must also have them linked. Otherwise the
    // cur-state's continuation would refine them independently — pruning
    // it against `old` hides paths where the unlinked register stays
    // unbounded. Mirrors upstream `check_ids` in `regsafe`.
    // Scalar ids: kernel-faithful single bijective idmap, precision-
    // gated (regsafe SCALAR). Pointer/packet linkage: the existing
    // pairwise relation (separate, unchanged). Both attribute to the
    // ScalarIdLinks miss bucket.
    if !scalar_ids_subsumed_by(cur, old, live_regs) {
        return Err(SubsumptionMissReason::ScalarIdLinks);
    }
    if !scalar_id_links_subsumed_by(cur, old, live_regs) {
        return Err(SubsumptionMissReason::ScalarIdLinks);
    }

    // Active-lock identity. When `old.active_lock` names a specific
    // map_value (`ptr_id`), every live register that *currently* holds
    // that map_value in `old` must still hold the same map_value in
    // `cur` — otherwise a future `bpf_spin_unlock` along the cached
    // continuation through such a register would mismatch the lock in
    // `cur`. This caught the FALSE_ACCEPT in
    // `verifier_spin_lock::reg_id_for_map_value`, where one path
    // reassigns the lock-holding register to a different map_value.
    if !active_lock_subsumed_by(cur, old, live_regs) {
        return Err(SubsumptionMissReason::ActiveLock);
    }

    // `old` must have at least as much may_goto budget remaining as
    // `cur`, otherwise pruning would let `cur` continue under behaviours
    // `old` never explored (old already exhausted the budget on a path cur
    // hasn't yet reached). Monotone: budget only ever decreases, so once
    // cur's future iterations are covered by an old state with a larger or
    // equal counter, pruning is sound.
    if old.goto_budget < cur.goto_budget {
        return Err(SubsumptionMissReason::GotoBudget);
    }

    // Active refcount-tracked acquisitions (dynptr / sock / cpumask /
    // kptr / ...) must be a subset in `cur` of those held by `old`. If
    // `cur` carries an active ref that `old` doesn't, pruning would
    // hide a leak: the cached continuation from `old` already proved
    // there's no leaking exit, but along that continuation cur's extra
    // ref never gets released — exit leak-check would catch it on cur
    // but not on old. Caught `dynptr_fail::ringbuf_missing_release2`,
    // where one branch releases both ptr1+ptr2 and the other only ptr1.
    if !cur.active_refs.is_subset(&old.active_refs) {
        return Err(SubsumptionMissReason::ActiveRefs);
    }

    // Check caller frames: callee-saved registers (r6-r9) persist across
    // calls and determine post-return control flow. Without this check,
    // two states that differ only in caller-frame r6-r9 values get pruned
    // against each other, hiding bugs that manifest after return.
    let saved = callee_saved_regs();
    for (cur_frame, old_frame) in cur.frames.iter().zip(old.frames.iter()) {
        if !types_subsumed_by(&cur_frame.caller_types, &old_frame.caller_types, &saved) {
            return Err(SubsumptionMissReason::CallerFrame);
        }
        if !config.skip_dbm_check
            && !domain_subsumed_by(
                &cur_frame.caller_domain,
                &old_frame.caller_domain,
                &saved,
                &HashSet::new(),
            )
        {
            return Err(SubsumptionMissReason::CallerFrame);
        }
        if !caller_tnum_subsumed_by(cur_frame, old_frame, &saved) {
            return Err(SubsumptionMissReason::CallerFrame);
        }
    }

    Ok(())
}

/// Linkage class for a register, used by `scalar_id_links_subsumed_by`.
///
/// Two registers belong to the same equivalence class when a future
/// refinement (e.g. null-check, range narrowing) on one will propagate
/// to the other along the kernel verifier's id-tracking. This covers:
///   - scalars sharing a `scalar_id`
///   - id-bearing nullable pointer types (`PtrToMapValueOrNull`,
///     `PtrToBtfIdOrNull`, `PtrToAllocMemOrNull`) sharing an id — null
///     refinement promotes all class members to the non-null form.
///   - the non-null forms `PtrToMapValue { id, .. }`, `PtrToAllocMem { id, .. }`
///     — the id persists post-refinement and still drives propagation.
///
/// The numeric tag in `LinkageKind` keeps classes from different RegType
/// variants disjoint even when their ids collide as `u32` values.
#[derive(PartialEq, Eq, Hash, Clone, Copy)]
enum LinkageKind {
    Scalar,
    MapValue,
    MapValueOrNull,
    BtfIdOrNull,
    AllocMem,
    AllocMemOrNull,
    /// Interval-mode packet-pointer family (kernel `reg->id`).
    /// Two registers with the same `(PacketPtr, id)` share a variable
    /// offset chain; a bounds check on one refines `range` for all.
    /// Zone mode handles this via DBM cells, not ids — the
    /// corresponding subsumption check lives in `zone_subsumed_by`.
    PacketPtr,
}

fn linkage_key(state: &State, r: Reg) -> Option<(LinkageKind, u32)> {
    match state.types.get(r) {
        RegType::PtrToMapValueOrNull { id, .. } => Some((LinkageKind::MapValueOrNull, id)),
        RegType::PtrToMapValue { id, .. } => Some((LinkageKind::MapValue, id)),
        RegType::PtrToBtfIdOrNull { id, .. } => Some((LinkageKind::BtfIdOrNull, id)),
        RegType::PtrToAllocMemOrNull { id, .. } => Some((LinkageKind::AllocMemOrNull, id)),
        RegType::PtrToAllocMem { id, .. } => Some((LinkageKind::AllocMem, id)),
        RegType::ScalarValue => state.scalar_id(r).map(|id| (LinkageKind::Scalar, id)),
        RegType::PtrToPacket | RegType::PtrToPacketEnd | RegType::PtrToPacketMeta => {
            if let NumericDomain::Interval(ref ivl) = state.domain {
                ivl.get_ptr_offset(r)
                    .and_then(|po| po.id)
                    .map(|id| (LinkageKind::PacketPtr, id))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// `old.active_lock` constraint check: for every live register that
/// holds the locked map_value in `old` (i.e. its `PtrToMapValue.id`
/// equals `old.active_lock.ptr_id`), the same register in `cur` must
/// still hold a map_value whose id equals `cur.active_lock.ptr_id`.
///
/// Encodes the rule that pruning must not collapse a state where the
/// lock's owning register has been reassigned to a different map_value
/// — `bpf_spin_unlock` later in the cached continuation would target
/// the wrong identity. See `verifier_spin_lock::reg_id_for_map_value`.
fn active_lock_subsumed_by(cur: &State, old: &State, live_regs: &HashSet<Reg>) -> bool {
    let Some(old_lock) = old.get_active_lock() else {
        return true;
    };
    let cur_lock_ptr = cur.get_active_lock().map(|l| l.ptr_id);
    for &r in live_regs {
        if let RegType::PtrToMapValue { id: old_id, .. } = old.types.get(r) {
            if old_id != old_lock.ptr_id {
                continue;
            }
            // r holds the lock's map_value in `old`. Require the same
            // in `cur`: cur.r must be a PtrToMapValue whose id matches
            // cur's active_lock.
            let RegType::PtrToMapValue { id: cur_id, .. } = cur.types.get(r) else {
                return false;
            };
            if Some(cur_id) != cur_lock_ptr {
                return false;
            }
        }
    }
    true
}

/// Kernel `check_ids` (verifier.c:19383): a per-comparison consistent
/// bijection `old_id ↔ cur_id`. Both zero ⇒ ok; exactly one zero ⇒
/// mismatch; else old_id must map to exactly one cur_id and a cur_id
/// may be claimed by only one old_id. `map` holds the recorded pairs
/// (zovia live-reg count is tiny, so the linear scan is trivial vs the
/// kernel's fixed BPF_ID_MAP_SIZE array).
fn check_ids(old_id: u32, cur_id: u32, map: &mut Vec<(u32, u32)>) -> bool {
    if (old_id != 0) != (cur_id != 0) {
        return false;
    }
    if old_id == 0 {
        return true;
    }
    for &(o, c) in map.iter() {
        if o == old_id {
            return c == cur_id;
        }
        if c == cur_id {
            return false;
        }
    }
    map.push((old_id, cur_id));
    true
}

/// Kernel `check_scalar_ids` (verifier.c:19416): like `check_ids` but a
/// zero id gets a fresh unique temp so `0 vs ID` / `ID vs 0` are valid
/// (but still consistently bijective). `tmp` is a per-comparison
/// generator seeded high (disjoint from real low-valued zovia ids).
fn check_scalar_ids(
    old_id: u32,
    cur_id: u32,
    map: &mut Vec<(u32, u32)>,
    tmp: &mut u32,
) -> bool {
    let o = if old_id != 0 {
        old_id
    } else {
        *tmp -= 1;
        *tmp
    };
    let c = if cur_id != 0 {
        cur_id
    } else {
        *tmp -= 1;
        *tmp
    };
    check_ids(o, c, map)
}

/// Kernel-faithful scalar-id check (regsafe SCALAR, verifier.c:19560):
/// scalar id is compared ONLY for a *precise* old scalar — an imprecise
/// old scalar is a wildcard (`if (!rold->precise && exact==NOT_EXACT)
/// return true`), so its id is never checked. All precise live scalars
/// are run through ONE bijective `check_scalar_ids` map, exactly as the
/// kernel threads `env->idmap_scratch` through every `regsafe`. This
/// replaces the scalar half of the old piecemeal pairwise
/// `scalar_id_links_subsumed_by` (pointer/packet linkage stays there):
/// the single bijection preserves linkage (same old id ⇒ same cur id)
/// AND is more permissive than exact-equality (remappable), while the
/// precision gate drops the over-conservative imprecise-scalar links
/// the kernel never checks.
fn scalar_ids_subsumed_by(cur: &State, old: &State, live_regs: &HashSet<Reg>) -> bool {
    let mut map: Vec<(u32, u32)> = Vec::new();
    let mut tmp: u32 = u32::MAX;
    for &r in live_regs {
        if old.types.get(r) != RegType::ScalarValue {
            continue;
        }
        if !old.is_reg_precise(r) {
            continue; // imprecise old scalar = wildcard (kernel)
        }
        let oid = old.scalar_id(r).unwrap_or(0);
        let cid = cur.scalar_id(r).unwrap_or(0);
        if !check_scalar_ids(oid, cid, &mut map, &mut tmp) {
            return false;
        }
    }
    true
}

/// Conservative id-equivalence check used by `state_subsumed_by`.
///
/// Returns true iff every pair `(r1, r2)` of live regs in the same
/// linkage class in `old` is also in the same linkage class in `cur`.
/// This is the safe direction: `cur` may have MORE links than `old`
/// (refinement narrows), but `old` cannot have links that `cur` lacks —
/// those are exactly the cases where future refinement in old's
/// continuation would silently miss propagation in cur. Mirrors
/// upstream `check_ids` in `regsafe`.
fn scalar_id_links_subsumed_by(
    cur: &State,
    old: &State,
    live_regs: &HashSet<Reg>,
) -> bool {
    let live: Vec<Reg> = live_regs.iter().copied().collect();
    for i in 0..live.len() {
        for j in (i + 1)..live.len() {
            let r1 = live[i];
            let r2 = live[j];
            // Scalar linkage now goes through the kernel-faithful
            // bijective `scalar_ids_subsumed_by`; this pairwise check
            // covers ONLY the pointer/packet linkage kinds.
            let old_link = match (linkage_key(old, r1), linkage_key(old, r2)) {
                (Some(a), Some(b)) if a == b && a.0 != LinkageKind::Scalar => true,
                _ => false,
            };
            if !old_link {
                continue;
            }
            let cur_link = match (linkage_key(cur, r1), linkage_key(cur, r2)) {
                (Some(a), Some(b)) if a == b && a.0 != LinkageKind::Scalar => true,
                _ => false,
            };
            if !cur_link {
                return false;
            }
        }
    }
    true
}

fn types_subsumed_by(cur: &TypeState, old: &TypeState, live_regs: &HashSet<Reg>) -> bool {
    for &r in live_regs {
        if !type_subsumed_by(&cur.get(r), &old.get(r)) {
            return false;
        }
    }
    true
}

fn type_subsumed_by(cur_ty: &RegType, old_ty: &RegType) -> bool {
    use RegType::*;

    match (old_ty, cur_ty) {
        // Identical types
        (ScalarValue, ScalarValue) => true,
        (NotInit, NotInit) => true,
        (PtrToCtx, PtrToCtx) => true,
        (PtrToPacketEnd, PtrToPacketEnd) => true,

        // Anything subsumes NotInit
        (NotInit, _) => true,

        // Packet pointers: old must have >= range
        (PtrToPacket, PtrToPacket) => true,

        // Map value pointers
        (
            PtrToMapValue {
                offset: o1,
                map_idx: m1,
                ..
            },
            PtrToMapValue {
                offset: o2,
                map_idx: m2,
                ..
            },
        ) => {
            m1 == m2
                && match (o1, o2) {
                    (None, _) => true,
                    (Some(a), Some(b)) => a == b,
                    (Some(_), None) => false,
                }
        }

        // Map value or null. Like `PtrToAllocMem` below, the kernel
        // mints a fresh `id` on every `bpf_map_lookup_elem` call —
        // looping `map_val = bpf_map_lookup_elem(...); if (map_val) ...`
        // produces non-equal-but-semantically-identical pointers across
        // iterations and id-equality blocks loop-top subsumption.
        // Structural identity is `map_idx` (which map); `id` is a per-
        // call tag used for null-check narrowing on the *current*
        // state's continuation, not for cross-state subsumption.
        // Pattern observed in iters.c::iter_tricky_but_fine.
        (
            PtrToMapValueOrNull { map_idx: m1, .. },
            PtrToMapValueOrNull { map_idx: m2, .. },
        ) => m1 == m2,

        // Socket pointers
        (PtrToSocket { ref_id: id1 }, PtrToSocket { ref_id: id2 }) => id1 == id2,
        (PtrToSocketOrNull { ref_id: id1 }, PtrToSocketOrNull { ref_id: id2 }) => id1 == id2,

        // Stack pointers - DBM subsumption covers the numeric relationship
        (PtrToStack { frame_level: fl1 }, PtrToStack { frame_level: fl2 }) => fl1 == fl2,

        // PtrToAllocMem from `bpf_iter_*_next` etc.: the dispatcher mints
        // a fresh `id` on every call, so two visits to the same loop top
        // hold non-equal-but-semantically-identical allocs in the loop
        // variable. Subsume when (mem_size, ref_id) match — `ref_id`
        // None means unref-tracked iter-elem alloc, Some(N) means the
        // alloc is owned by a tracked acquire (dynptr_data slice from
        // a specific dynptr; ringbuf reservation). For the latter, the
        // matching ref_id ensures we don't conflate two acquires;
        // mem_size pins the bounds-check budget. Without this rule,
        // unbounded `bpf_for_each` loops state-explode (each iter's
        // fresh id breaks loop-top subsumption on the loop variable).
        // The `id` field is intentionally ignored — it's a per-call
        // tag, not a structural property.
        (
            PtrToAllocMem { mem_size: ms1, ref_id: ri1, .. },
            PtrToAllocMem { mem_size: ms2, ref_id: ri2, .. },
        ) => ms1 == ms2 && ri1 == ri2,
        (
            PtrToAllocMemOrNull { mem_size: ms1, ref_id: ri1, .. },
            PtrToAllocMemOrNull { mem_size: ms2, ref_id: ri2, .. },
        ) => ms1 == ms2 && ri1 == ri2,

        // Default: structural equality. Covers variants without a
        // looser explicit rule (PtrToBtfId, PtrToCpumask, PtrToArena,
        // PtrToCgroup, PtrToTask, PtrToOwnedKptr, PtrToMapKptr,
        // PtrToCallback, PtrToSockCommon, PtrToTcpSock, PtrToPacketMeta,
        // and the *OrNull versions of the above). Without this fallback,
        // identical pointer types compare unequal at prune-points and
        // every state is treated as novel — that's the entire reason
        // `bpf_cubic_cong_avoid` (and any struct_ops program with a
        // long-lived `PtrToBtfId` arg in r6-r9) hits the complexity
        // limit. PartialEq is derived on RegType, so structural ==
        // is the right canonical check for these.
        (a, b) if a == b => true,
        _ => false,
    }
}

fn domain_subsumed_by(
    cur: &NumericDomain,
    old: &NumericDomain,
    live_regs: &HashSet<Reg>,
    precise: &HashSet<Reg>,
) -> bool {
    // Kernel `regsafe` rule (verifier.c v6.15 L18357 / L18387):
    //   - precise → range_within (old ⊇ cur)
    //   - !precise → accept (kernel doesn't compare imprecise scalars
    //     across cur/old at all).
    for &r in live_regs {
        if !precise.contains(&r) {
            continue;
        }
        let (old_min, old_max) = old.get_interval(r);
        let (cur_min, cur_max) = cur.get_interval(r);
        if !(old_min <= cur_min && old_max >= cur_max) {
            if std::env::var("ZOVIA_DUMP_DOMAIN_MISS").ok().as_deref() == Some("1") {
                eprintln!(
                    "[domain_miss] reg={:?} precise old=[{},{}] cur=[{},{}]",
                    r, old_min, old_max, cur_min, cur_max
                );
            }
            return false;
        }
    }

    // Anchor-to-anchor constraints (packet bounds) must also be subsumed.
    // These represent relationships like data_end - data >= N that are
    // critical for packet access safety and persist across calls.
    match (old, cur) {
        (NumericDomain::Zone(old_dbm), NumericDomain::Zone(cur_dbm)) => {
            zone_subsumed_by(old_dbm, cur_dbm, live_regs)
        }
        (NumericDomain::Interval(old_ivl), NumericDomain::Interval(cur_ivl)) => {
            interval_subsumed_by(old_ivl, cur_ivl)
        }
        _ => {
            // Mismatched domain types - should not happen in normal operation
            true
        }
    }
}

fn zone_subsumed_by(
    old_dbm: &crate::analysis::Dbm,
    cur_dbm: &crate::analysis::Dbm,
    live_regs: &HashSet<Reg>,
) -> bool {
    let anchors = [Reg::AnchorData, Reg::AnchorDataEnd, Reg::AnchorDataMeta];

    // Anchor↔anchor: packet-region geometry (e.g. `data_end - data >= N`).
    for &a in &anchors {
        for &b in &anchors {
            if a == b {
                continue;
            }
            if old_dbm.get(a, b) < cur_dbm.get(a, b) {
                if std::env::var("ZOVIA_DUMP_DOMAIN_MISS").ok().as_deref() == Some("1") {
                    eprintln!("[domain_miss] anchor-anchor a={:?} b={:?}", a, b);
                }
                return false;
            }
        }
    }

    // Live-reg pairs (including reg ↔ anchor): zone-mode analogue of
    // the kernel's id-tracking for packet pointers. Without this,
    // pruning collapses two states whose live registers differ in
    // their *relation* to one another or to a packet anchor —
    // e.g. one path established `r2 - r3 == 0` (`r2 = r3` aliasing)
    // and the other did not, but their standalone intervals coincide.
    // That's the FALSE_ACCEPT in
    // `verifier_direct_packet_access::id_in_regsafe_bad_access`.
    //
    // For subsumption: `old` covers `cur` only if every directed cell
    // `old.get(a, b) >= cur.get(a, b)` for live-reg pairs. (`>=` is
    // the looser direction in difference-bound semantics — a larger
    // upper bound on `a - b` is more permissive.)
    let live: Vec<Reg> = live_regs
        .iter()
        .copied()
        .filter(|r| !r.is_anchor())
        .collect();
    for &r in &live {
        for &a in &anchors {
            if old_dbm.get(r, a) < cur_dbm.get(r, a) {
                if std::env::var("ZOVIA_DUMP_DOMAIN_MISS").ok().as_deref() == Some("1") {
                    eprintln!("[domain_miss] reg-anchor r={:?} a={:?}", r, a);
                }
                return false;
            }
            if old_dbm.get(a, r) < cur_dbm.get(a, r) {
                if std::env::var("ZOVIA_DUMP_DOMAIN_MISS").ok().as_deref() == Some("1") {
                    eprintln!("[domain_miss] anchor-reg a={:?} r={:?}", a, r);
                }
                return false;
            }
        }
    }
    for i in 0..live.len() {
        for j in 0..live.len() {
            if i == j {
                continue;
            }
            let a = live[i];
            let b = live[j];
            if old_dbm.get(a, b) < cur_dbm.get(a, b) {
                return false;
            }
        }
    }
    true
}

fn interval_subsumed_by(
    old_ivl: &crate::domains::interval::IntervalState,
    cur_ivl: &crate::domains::interval::IntervalState,
) -> bool {
    // Interval domain: check packet_size_lower_bound and meta_size_lower_bound
    // For subsumption, old must be MORE permissive (fewer constraints) than cur.
    // If old requires a minimum packet size but cur doesn't, old does NOT subsume cur.
    let old_pkt = old_ivl.get_packet_size_bound().unwrap_or(0);
    let cur_pkt = cur_ivl.get_packet_size_bound().unwrap_or(0);
    if old_pkt > cur_pkt {
        return false;
    }
    let old_meta = old_ivl.get_meta_size_bound().unwrap_or(0);
    let cur_meta = cur_ivl.get_meta_size_bound().unwrap_or(0);
    if old_meta > cur_meta {
        return false;
    }
    true
}

/// Stack-slot type subsumption: stricter than `type_subsumed_by`.
/// NotInit only subsumes NotInit (no "covers anything" rule), and
/// otherwise we use the same family rules as registers.
fn stack_slot_type_subsumed_by(new_ty: &RegType, old_ty: &RegType) -> bool {
    use RegType::*;
    match (old_ty, new_ty) {
        (NotInit, NotInit) => true,
        // For non-NotInit pairs, defer to register-style rules.
        // The default rule `(a, b) if a == b => true` covers most
        // pointer types; ScalarValue→ScalarValue covers the common
        // "spilled scalar" case; PtrToMapValue offsets etc. have
        // their own match arms in `type_subsumed_by`.
        _ => type_subsumed_by(new_ty, old_ty),
    }
}

fn stack_subsumed_by(
    cur: &State,
    old: &State,
    frame_live_slots: &[Option<HashSet<i16>>],
) -> bool {
    // clean_verifier_state analog (kernel clean_func_state,
    // verifier.c:19424): a stack slot the kernel proves dead is set to
    // STACK_INVALID so `stacksafe` skips it — only LIVE slots are ever
    // compared. zovia previously compared the *union* of all slot
    // offsets with NO liveness filter (the divergence-map gap), so a
    // dead scratch slot differing across states blocked every prune.
    // The kernel cleans EVERY frame at its own ip; `frame_live_slots[i]`
    // is frame i's sound static MAY-liveness (per-byte offsets) at that
    // frame's resume pc, or `None` when unknown (⇒ don't skip — full
    // compare, the sound direction). Built in `should_prune`.
    // Kernel-aligned idmap (verifier.c v6.15 `check_ids` in regsafe at
    // STACK_ITER L18583): iter ids are minted fresh by every
    // `bpf_iter_*_new` call, so literal `old.id == cur.id` always fails
    // when an iter slot is re-initialized (e.g. nested iters: each outer
    // iteration recreates the inner iter at the same stack slot with a
    // fresh id). Build a per-comparison map `old_id → cur_id` and check
    // for consistency: a given old id may map to exactly one cur id
    // across the comparison.
    let mut iter_idmap: std::collections::HashMap<u32, u32> = std::collections::HashMap::new();
    for (frame_i, (old_frame, new_frame)) in
        old.frames.iter().zip(cur.frames.iter()).enumerate()
    {
        let all_offsets: HashSet<i16> = old_frame
            .stack
            .slot_offsets()
            .into_iter()
            .chain(new_frame.stack.slot_offsets())
            .collect();

        // Per-frame liveness for the clean_verifier_state skip. `None`
        // (frame liveness unknown) ⇒ no skip for this frame (full
        // compare — the sound direction).
        let frame_ls = frame_live_slots.get(frame_i).and_then(|o| o.as_ref());

        for offset in all_offsets {
            // Dead-slot skip: if no byte in this 8-byte slot is live at
            // frame i's resume pc, the kernel would have STACK_INVALID'd
            // it — skip, mirroring stacksafe. ITER / DYNPTR / IRQ slots
            // are semantically live regardless of byte-liveness (kernel
            // `bpf_stack_slot_alive` keeps them alive), so never skip
            // those. Conservative 8-byte span: any live byte → keep
            // (fewer skips = sound direction).
            if let Some(ls) = frame_ls
                && !(offset..offset.saturating_add(8)).any(|b| ls.contains(&b))
            {
                let structural = |fr: &crate::analysis::machine::frame_stack::CallFrame| {
                    fr.stack
                        .get_slot(offset)
                        .map(|s| {
                            s.iterator.is_some()
                                || s.dynptr.is_some()
                                || s.irq_flag.is_some()
                        })
                        .unwrap_or(false)
                };
                if !structural(old_frame) && !structural(new_frame) {
                    continue;
                }
            }
            let old_ty = old_frame.stack.get_slot_type(offset);
            let new_ty = new_frame.stack.get_slot_type(offset);
            // Stack-specific subsumption is STRICTER than register
            // `type_subsumed_by`. For registers, `(NotInit, _) => true`
            // is correct: an uninit reg "covers" anything because
            // future reads error anyway. For STACK slots, NotInit
            // means "never written" — semantically a specific state
            // distinct from "written with type X". Pruning cur (with
            // a written slot) against cached (with the slot
            // unwritten) skips exploring cur's continuation, which
            // observes the written slot; cached's continuation never
            // does, so the two are not equivalent.
            //
            // Pattern from `rbtree::rbtree_add_and_remove_array` and
            // `test_cls_redirect::cls_redirect`: slot reused across
            // paths with different types; cached state with NotInit
            // (or earlier-spilled scalar) wrongly subsumes a path
            // that has spilled `PtrToOwnedKptr` / `PtrToPacket` to
            // the same offset.
            if !stack_slot_type_subsumed_by(&new_ty, &old_ty) {
                return false;
            }

            // Precision: a precise *cached* slot requires the new slot
            // to fall inside its range/tnum (kernel `regsafe` SCALAR
            // verifier.c v6.15 L18357: precise old → range_within +
            // tnum_in; non-precise old → free pass when live). Earlier
            // we keyed on `new_s.precise` and demanded EXACT — that's
            // stricter than the kernel and blocks may_goto-bounded
            // loops where a body memory access precision-marks the
            // counter (cond_break1/2/3).
            let old_slot = old_frame.stack.get_slot(offset);
            let new_slot = new_frame.stack.get_slot(offset);
            if let (Some(old_s), Some(new_s)) = (old_slot, new_slot) {
                if old_s.precise {
                    if !tnum_covers(&new_s.tnum, &old_s.tnum) {
                        return false;
                    }
                    if !(old_s.bounds.min <= new_s.bounds.min
                        && new_s.bounds.max <= old_s.bounds.max)
                    {
                        return false;
                    }
                }
            }

            // open-coded iterator identity.
            //
            // An Active/Drained iterator slot represents a specific
            // loop instance (id minted at `*_new`). A cached state
            // subsumes the current one at this slot only when both
            // carry the exact same annotation — matching kind, state,
            // and id. Mismatched iterator state, mismatched id, or one
            // side carrying an annotation and the other not are all
            // semantically distinct program points and must not
            // collapse into a single pruned state.
            //
            // Non-precise loop-varying scalars are allowed to converge
            // via the existing non-precise superset rule above —
            // this check is about the iterator identity itself, not
            // the loop variable.
            // `depth` is intentionally ignored — it grows monotonically
            // per iter_next ACTIVE-fork (kernel `iter.depth`) and is
            // used by the inf-loop detector and `widen_imprecise_scalars`
            // to keep iterations distinguishable, NOT by subsumption.
            // Kernel `states_equal(RANGE_WITHIN)` for iter_next call
            // sites doesn't compare `iter.depth` either; convergence
            // here is exactly what allows e.g. `i++; while(iter_next)`
            // loops to terminate.
            let old_iter = old_slot.and_then(|s| s.iterator);
            let new_iter = new_slot.and_then(|s| s.iterator);
            let iter_eq_modulo_depth = match (old_iter, new_iter) {
                (None, None) => true,
                (Some(a), Some(b)) => {
                    if a.kind != b.kind || a.state != b.state {
                        false
                    } else {
                        // check_ids: id may be remapped, but consistently.
                        match iter_idmap.get(&a.id) {
                            Some(&mapped) => mapped == b.id,
                            None => {
                                iter_idmap.insert(a.id, b.id);
                                true
                            }
                        }
                    }
                }
                _ => false,
            };
            if !iter_eq_modulo_depth {
                return false;
            }

            // For packet pointers, also check interval_range subsumption.
            // If old has a proven range but cur doesn't, old does NOT subsume cur,
            // because cur might fail a packet access that old would pass.
            // We need to explore cur to find potential unsafe paths.
            if matches!(new_ty, RegType::PtrToPacket | RegType::PtrToPacketMeta) {
                let old_slot = old_frame.stack.get_slot(offset);
                let new_slot = new_frame.stack.get_slot(offset);
                if let (Some(old_s), Some(new_s)) = (old_slot, new_slot) {
                    use crate::analysis::machine::stack_state::PointerBounds;
                    let old_range = match &old_s.ptr_bounds {
                        Some(PointerBounds::Interval { range, .. }) => *range,
                        _ => None,
                    };
                    let new_range = match &new_s.ptr_bounds {
                        Some(PointerBounds::Interval { range, .. }) => *range,
                        _ => None,
                    };

                    match (old_range, new_range) {
                        // old has range but cur doesn't: old does NOT subsume cur
                        (Some(_), None) => return false,
                        // old has larger range than cur: old does NOT subsume cur
                        (Some(old_r), Some(new_r)) if old_r > new_r => return false,
                        // cur has range >= old, or both None: OK
                        _ => {}
                    }
                }
            }
        }
    }
    true
}

fn tnum_subsumed_by(cur_state: &State, old_state: &State, live_regs: &HashSet<Reg>) -> bool {
    // Kernel rule: precise → tnum-cover; !precise → accept.
    for &r in live_regs {
        if !old_state.is_reg_precise(r) {
            continue;
        }
        let cur = cur_state.get_tnum(r);
        let old = old_state.get_tnum(r);
        if !tnum_covers(&cur, &old) {
            return false;
        }
    }
    true
}

/// Check if old tnum covers cur tnum (old's possible values are a superset of cur's).
fn tnum_covers(cur: &Tnum, old: &Tnum) -> bool {
    // Every unknown bit in cur must also be unknown in old
    if cur.mask & !old.mask != 0 {
        return false;
    }
    // For bits that are known in both, the values must match
    let both_known = !cur.mask & !old.mask;
    (cur.value & both_known) == (old.value & both_known)
}

/// Like tnum_subsumed_by but operates on call stack frames instead of full states.
fn caller_tnum_subsumed_by(
    cur_frame: &crate::analysis::machine::frame_stack::CallFrame,
    old_frame: &crate::analysis::machine::frame_stack::CallFrame,
    regs: &HashSet<Reg>,
) -> bool {
    for &r in regs {
        let cur = cur_frame
            .caller_tnums
            .get(&r)
            .copied()
            .unwrap_or(Tnum::UNKNOWN);
        let old = old_frame
            .caller_tnums
            .get(&r)
            .copied()
            .unwrap_or(Tnum::UNKNOWN);
        if !tnum_covers(&cur, &old) {
            return false;
        }
    }
    true
}
