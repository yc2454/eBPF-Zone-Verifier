use crate::analysis::machine::reg::Reg;
use crate::domains::tnum::Tnum;
use crate::{analysis::machine::reg_types::RegType, ast::MemSize};
use std::collections::{BTreeMap, HashSet};

/// Open-coded iterator families (Phase 3 W3.2).
///
/// Mirrors the four in-tree `bpf_iter_*` structs created by `*_new`,
/// advanced by `*_next` and released by `*_destroy`. The iterator's
/// abstract state rides on the stack slot holding the struct (see
/// `IteratorSlot`), not on a register type — registers pointing at the
/// struct remain plain `PtrToStack`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IterKind {
    Num,
    Task,
    Css,
    Bits,
    /// `struct bpf_iter_task_vma` from kernel/bpf/task_iter.c. The
    /// program-visible struct is 8 bytes; `_next` returns
    /// `struct vm_area_struct *` (TRUSTED).
    TaskVma,
    /// `struct bpf_iter_testmod_seq` from the bpf testmod (16-byte
    /// program-visible struct). `_next` returns `s64 *` into the
    /// iterator's own state.
    TestmodSeq,
    /// `struct bpf_iter_css_task` from kernel/bpf/task_iter.c. Iterates
    /// tasks attached to a cgroup_subsys_state. `_next` returns
    /// `struct task_struct *` (RCU). Allowed only in LSM, iter, and
    /// sleepable program contexts (kernel `check_css_task_iter_allowlist`).
    CssTask,
    /// `struct bpf_iter_kmem_cache` from mm/slab_common.c. Iterates over
    /// all kernel slab caches. `_next` returns `struct kmem_cache *`
    /// (TRUSTED). Program-visible struct is 8 bytes (opaque __u64[1]).
    KmemCache,
}

impl IterKind {
    /// Mirrors the kernel's `KF_RCU_PROTECTED` annotation on iter
    /// `*_new` kfuncs. When true, the slot trust state at init time
    /// depends on whether we're in an RCU CS, and `bpf_rcu_read_unlock`
    /// invalidates trust on outstanding slots of this kind. Currently
    /// task and css iters; bits/num are pure userspace state.
    /// css_task is KF_TRUSTED_ARGS (not KF_RCU_PROTECTED) and is gated
    /// by the LSM/iter/sleepable allowlist instead, so its slot trust
    /// is independent of in_rcu_cs at init time.
    pub fn is_rcu_protected(self) -> bool {
        matches!(self, IterKind::Task | IterKind::Css)
    }
}

/// Lifecycle state for an open-coded iterator slot. Transitions:
/// (no annotation) -`*_new`-> Active -`*_next`=NULL-> Drained -`*_destroy`-> (no annotation).
/// `*_next` non-NULL keeps Active. Exit with any Active/Drained slot
/// is a REJECT (analogous to unreleased refs).
///
/// "Uninit" in the design doc corresponds to `SpilledReg::iterator ==
/// None` — no explicit enum variant, since the annotation's absence is
/// the authoritative signal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IterState {
    Active,
    Drained,
}

/// Per-slot iterator annotation. `id` is a fresh token minted at `*_new`
/// time (used by subsumption in W3.2c to match "same loop"). `depth`
/// mirrors kernel `iter.depth`: incremented on every ACTIVE-branch fork
/// at `*_next`, used by iter-loop convergence to keep iterations
/// distinguishable so the inf-loop detector doesn't fire on legitimate
/// loops, and (paired with `widen_imprecise_scalars`) drives convergence
/// at the iter_next call site itself. See kernel
/// `process_iter_next_call` / `iter_active_depths_differ` (verifier.c
/// v6.15 ~L8884 / ~L18965).
///
/// `untrusted` mirrors kernel `PTR_UNTRUSTED` on iter stack slots
/// (verifier.c v6.15 `mark_stack_slots_iter` ~L1041). For an iter kind
/// whose `_new` kfunc is `KF_RCU_PROTECTED` (currently `task`, `css`),
/// the kernel sets `MEM_RCU` if `in_rcu_cs` at `_new` time, else
/// `PTR_UNTRUSTED`. After `bpf_rcu_read_unlock`, every `MEM_RCU` reg/
/// slot is re-flagged `PTR_UNTRUSTED` (~L13543), so an iter created
/// inside a RCU CS becomes UNTRUSTED if the program later releases the
/// lock and re-enters `_next`. `_next` itself rejects with
/// "expected an RCU CS when using …" on UNTRUSTED slots (~L8691).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct IteratorSlot {
    pub kind: IterKind,
    pub state: IterState,
    pub id: u32,
    pub depth: u32,
    pub untrusted: bool,
}

/// Dynptr families (Phase 4 W4.2).
///
/// Mirrors the kernel's `enum bpf_dynptr_type`. The kind is fixed at
/// construction by the producer kfunc and constrains which consumer
/// kfuncs the slot can flow into (e.g. `bpf_dynptr_data` rejects
/// non-`Local`/`Ringbuf` kinds).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DynptrKind {
    /// `bpf_dynptr_from_mem` over a stack/map buffer.
    Local,
    /// `bpf_ringbuf_reserve_dynptr` — acquire/release tracked.
    Ringbuf,
    /// `bpf_dynptr_from_skb` — read-only into skb data.
    Skb,
    /// `bpf_dynptr_from_xdp` — into xdp frame data.
    Xdp,
    /// Kernel-managed user-ringbuf dynptr — synthesized for the
    /// `bpf_user_ringbuf_drain` cb's R1 (kernel sets
    /// `PTR_TO_DYNPTR | DYNPTR_TYPE_USER | MEM_RDONLY`,
    /// `set_user_ringbuf_callback_state` verifier.c v6.15 ~L10800).
    /// Not stack-based; only ever attached to `RegType::PtrToDynptr`,
    /// not to a `DynptrSlot` on the stack.
    User,
}

/// Per-slot dynptr annotation (W4.2). A dynptr occupies two adjacent
/// 8-byte stack slots; both carry an annotation so the verifier can
/// reject reads/writes that touch only one of the pair.
///
/// `ref_id` is non-zero only for kinds with acquire/release semantics
/// (`Ringbuf`); `Local`/`Skb`/`Xdp` dynptrs have no release kfunc and
/// carry `ref_id == 0`.
///
/// `first_slot` distinguishes the base byte (slot 0 of the pair) from
/// the trailing slot — only the base may be passed to dynptr kfuncs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DynptrSlot {
    pub kind: DynptrKind,
    pub ref_id: u32,
    pub rdonly: bool,
    pub first_slot: bool,
    /// Per-instance identity for slice tracking (mirrors kernel
    /// `state->stack[spi].spilled_ptr.id`, verifier.c v6.15 L911).
    /// Distinct from `ref_id`: minted for *every* dynptr (even
    /// unrefcounted `Local`/`Skb`/`Xdp`) so slices can be invalidated
    /// on overwrite via the kernel's `bpf_for_each_reg_in_vstate`
    /// loop (L913-919). Both pair slots carry the same value.
    pub dynptr_id: u32,
}

/// IRQ-flag kfunc class. Mirrors kernel `enum irq_kfunc_class`
/// (verifier.c v6.15 ~L1206): `bpf_local_irq_save/restore` are
/// `IRQ_NATIVE_KFUNC`; `bpf_res_spin_lock_irqsave/unlock_irqrestore`
/// are `IRQ_LOCK_KFUNC`. `_restore` must use the same class as `_save`,
/// otherwise kernel rejects with "irq flag acquired by … kfuncs cannot
/// be restored with … kfuncs".
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IrqKfuncClass {
    Native,
    Lock,
}

/// Per-slot IRQ-flag annotation. Stamped on the 8-byte stack slot that
/// holds an irq flag at `bpf_local_irq_save` (or
/// `bpf_res_spin_lock_irqsave`) time. Cleared on the matching
/// `_restore`. Mirrors the kernel `STACK_IRQ_FLAG` slot type
/// (verifier.c v6.15 ~L1184) plus `spilled_ptr.irq.kfunc_class`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct IrqFlagSlot {
    /// Fresh id minted at acquire (kernel `++env->id_gen`). Used by the
    /// LIFO ordering check in `release_irq_state`: must equal the
    /// program-level `active_irq_id`, else "cannot restore irq state out
    /// of order".
    pub id: u32,
    pub kfunc_class: IrqKfuncClass,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarBounds {
    pub min: i64,
    pub max: i64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PointerBounds {
    Zone {
        anchor: Option<Reg>,
        anchor_lo: Option<i64>, // anchor - reg <= ? (i.e., reg >= anchor + lo)
        anchor_hi: Option<i64>, // reg - anchor <= ? (i.e., reg <= anchor + hi)
        // Secondary packet anchor relation. For PtrToPacket /
        // PtrToPacketMeta the primary anchor (AnchorData /
        // AnchorDataMeta) plus DBM closure isn't enough on fill: the
        // distance between distinct packet anchors is bounded but not
        // fixed, so a `r - @data_end` bound proven before spill (e.g.
        // from a `r + N > data_end` check that tightens both r and
        // r5's relation to @data_end) cannot be reconstructed from the
        // saved `r - @data` bound alone. Save the @data_end edge here
        // and replay it on fill so the post-fill closure preserves the
        // packet-bounds invariant the access at `r + off` depends on.
        end_anchor: Option<Reg>,
        end_lo: Option<i64>,
        end_hi: Option<i64>,
    },
    Interval {
        off: Option<i64>,     // fixed offset from anchor
        var_off: Option<u64>, // variable offset uncertainty
        range: Option<i64>,   // proven safe access range
    },
}

/// Snapshot of a register's abstract state at spill time
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpilledReg {
    pub source_reg: Option<Reg>,
    pub reg_type: RegType,
    pub tnum: Tnum,
    pub bounds: ScalarBounds,
    pub size: MemSize,
    pub ptr_bounds: Option<PointerBounds>,
    /// Identity token for this scalar value. `None` until Phase-2 W2.1b
    /// wires assignment/linking; refinement (W2.1c) propagates bound/tnum
    /// tightenings across all slots and registers sharing the same id.
    pub scalar_id: Option<u32>,
    /// Precision mark carried from the source register at spill time
    /// (W2.2). Restored on fill so a register reloaded from the stack
    /// stays on the precise chain.
    pub precise: bool,
    /// Open-coded iterator annotation (W3.2). Set only on the base byte
    /// of the iterator struct at `*_new` time; trailing bytes of the
    /// struct stay as ordinary spill sentinels. Private — all access
    /// outside this module goes through `stack_{get,set,clear}_iterator`.
    pub(crate) iterator: Option<IteratorSlot>,
    /// Dynptr annotation (W4.2). Set on both 8-byte slots of the dynptr
    /// pair at construction; cleared on release / overwrite. Private —
    /// all access outside this module goes through
    /// `stack_{get,set,clear}_dynptr`.
    pub(crate) dynptr: Option<DynptrSlot>,
    /// IRQ-flag annotation. Set on the 8-byte slot at
    /// `bpf_local_irq_save` (or `_irqsave` lock variant); cleared on
    /// matching `_restore`. Private — go through
    /// `stack_{get,set,clear}_irq_flag`.
    pub(crate) irq_flag: Option<IrqFlagSlot>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct StackState {
    /// Spilled registers, keyed by stack offset
    pub slots: BTreeMap<i16, SpilledReg>,
}

impl std::fmt::Display for StackState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut entries: Vec<String> = Vec::new();
        for (offset, spilled) in &self.slots {
            entries.push(format!(
                "offset {}: type={:?}, bounds=[{}, {}], source_reg={:?}, ptr_bounds={:?}",
                offset,
                spilled.reg_type,
                spilled.bounds.min,
                spilled.bounds.max,
                spilled.source_reg,
                spilled.ptr_bounds
            ));
        }
        write!(f, "StackState {{\n  {}\n}}", entries.join("\n  "))
    }
}

impl StackState {
    pub fn invalidate_ref(&mut self, id: u32) {
        for (_, spilled) in self.slots.iter_mut() {
            if spilled.reg_type.get_ref_id() == Some(id) {
                spilled.reg_type = RegType::ScalarValue;
            }
        }
    }

    pub fn is_slot_initialized(&self, offset: i16) -> bool {
        self.slots.contains_key(&offset)
    }

    pub fn get_slot_type(&self, offset: i16) -> RegType {
        if let Some(spilled) = self.slots.get(&offset) {
            spilled.reg_type
        } else {
            RegType::ScalarValue
        }
    }

    pub fn get_slot(&self, offset: i16) -> Option<&SpilledReg> {
        self.slots.get(&offset)
    }

    pub fn get_slot_mut(&mut self, offset: i16) -> Option<&mut SpilledReg> {
        self.slots.get_mut(&offset)
    }

    pub fn slot_offsets(&self) -> Vec<i16> {
        self.slots.keys().cloned().collect()
    }

    pub fn set_slot_type(&mut self, offset: i16, reg_type: RegType, source_reg: Option<Reg>) {
        if let Some(spilled) = self.slots.get_mut(&offset) {
            spilled.reg_type = reg_type;
        } else {
            self.slots.insert(
                offset,
                SpilledReg {
                    source_reg,
                    reg_type,
                    tnum: Tnum::unknown(),
                    bounds: ScalarBounds {
                        min: i64::MIN,
                        max: i64::MAX,
                    },
                    size: MemSize::U64,
                    ptr_bounds: None,
                    scalar_id: None,
                    precise: false,
                    iterator: None,
                    dynptr: None,
                    irq_flag: None,
                },
            );
        }
    }

    pub fn invalidate_packet_pointers(&mut self) {
        for (_, spilled) in self.slots.iter_mut() {
            if spilled.reg_type == RegType::PtrToPacket {
                spilled.reg_type = RegType::ScalarValue;
            }
        }
    }

    pub fn insert(&mut self, offset: i16, spilled: SpilledReg) {
        self.slots.insert(offset, spilled);
    }

    pub fn invalidate_slot(&mut self, offset: i16) {
        self.slots.insert(
            offset,
            SpilledReg {
                source_reg: None,
                reg_type: RegType::ScalarValue,
                tnum: Tnum::unknown(),
                bounds: ScalarBounds {
                    min: i64::MIN,
                    max: i64::MAX,
                },
                size: MemSize::U64,
                ptr_bounds: None,
                scalar_id: None,
                precise: false,
                iterator: None,
                dynptr: None,
                    irq_flag: None,
            },
        );
    }

    /// Demote a stack slot's type to ScalarValue while preserving bounds/tnum.
    /// Used at merge points where different paths have incompatible pointer types.
    pub fn demote_slot_to_scalar(&mut self, offset: i16) {
        if let Some(spilled) = self.slots.get_mut(&offset) {
            spilled.reg_type = RegType::ScalarValue;
        }
    }

    /// Read the open-coded iterator annotation at a stack offset, if any
    /// (W3.2). Only the base byte of a multi-byte iterator struct carries
    /// the annotation.
    pub fn stack_get_iterator(&self, offset: i16) -> Option<IteratorSlot> {
        self.slots.get(&offset).and_then(|s| s.iterator)
    }

    /// Set the open-coded iterator annotation on an already-initialized
    /// slot (W3.2). The slot must exist — callers are expected to have
    /// reserved the iterator struct bytes on the stack first.
    pub fn stack_set_iterator(&mut self, offset: i16, iter: IteratorSlot) {
        if let Some(spilled) = self.slots.get_mut(&offset) {
            spilled.iterator = Some(iter);
        }
    }

    /// Clear the iterator annotation at a stack offset (W3.2). No-op if
    /// the slot doesn't exist or doesn't carry one.
    pub fn stack_clear_iterator(&mut self, offset: i16) {
        if let Some(spilled) = self.slots.get_mut(&offset) {
            spilled.iterator = None;
        }
    }

    /// True if any slot currently holds an Active or Drained iterator
    /// (W3.2). Parallel to `has_unreleased_refs` — used at exit to
    /// reject programs that leak iterators.
    pub fn has_active_iterators(&self) -> bool {
        self.slots.values().any(|s| {
            // Any annotation at all means Active or Drained — Uninit
            // is represented by the absence of the annotation.
            s.iterator.is_some()
        })
    }

    /// Read the dynptr annotation at a stack offset, if any (W4.2). Both
    /// the base and trailing slot of a dynptr pair carry an annotation;
    /// inspect `DynptrSlot::first_slot` to tell them apart.
    pub fn stack_get_dynptr(&self, offset: i16) -> Option<DynptrSlot> {
        self.slots.get(&offset).and_then(|s| s.dynptr)
    }

    /// Set the dynptr annotation on an already-initialized slot (W4.2).
    /// Callers are expected to have reserved the dynptr's 16 stack bytes
    /// first and to write *both* slots of the pair (base with
    /// `first_slot: true`, trailing with `first_slot: false`).
    pub fn stack_set_dynptr(&mut self, offset: i16, dynptr: DynptrSlot) {
        if let Some(spilled) = self.slots.get_mut(&offset) {
            spilled.dynptr = Some(dynptr);
        }
    }

    /// Clear the dynptr annotation at a stack offset (W4.2). No-op if
    /// the slot doesn't exist or doesn't carry one. Callers releasing a
    /// dynptr should clear both slots of the pair.
    pub fn stack_clear_dynptr(&mut self, offset: i16) {
        if let Some(spilled) = self.slots.get_mut(&offset) {
            spilled.dynptr = None;
        }
    }

    /// True if any slot holds a dynptr that carries an acquire/release
    /// ref (W4.2). Parallel to `has_active_iterators` / `has_unreleased_refs`
    /// — used at exit to reject programs that leak ringbuf reservations
    /// or other ref-bearing dynptrs. Non-ref dynptrs (`Local`, `Skb`,
    /// `Xdp`) carry `ref_id == 0` and are allowed at exit (they're just
    /// metadata; the kernel auto-releases them with the frame).
    pub fn has_unreleased_dynptr_refs(&self) -> bool {
        self.slots
            .values()
            .any(|s| s.dynptr.is_some_and(|d| d.ref_id != 0))
    }

    /// Read the IRQ-flag annotation at a stack offset, if any.
    pub fn stack_get_irq_flag(&self, offset: i16) -> Option<IrqFlagSlot> {
        self.slots.get(&offset).and_then(|s| s.irq_flag)
    }

    /// Set the IRQ-flag annotation on an already-initialized slot.
    /// Callers must have written the slot's 8 bytes first
    /// (typically via `update_store_types`).
    pub fn stack_set_irq_flag(&mut self, offset: i16, flag: IrqFlagSlot) {
        if let Some(spilled) = self.slots.get_mut(&offset) {
            spilled.irq_flag = Some(flag);
        }
    }

    /// Clear the IRQ-flag annotation at a stack offset (matched
    /// `_restore`). No-op if absent.
    pub fn stack_clear_irq_flag(&mut self, offset: i16) {
        if let Some(spilled) = self.slots.get_mut(&offset) {
            spilled.irq_flag = None;
        }
    }

    /// True if any slot still holds an IRQ-flag annotation. Used at
    /// EXIT to reject programs that leak an IRQ-disabled region.
    pub fn has_unreleased_irq_flags(&self) -> bool {
        self.slots.values().any(|s| s.irq_flag.is_some())
    }

    /// True if a write of `size` bytes at stack offset `off` would touch
    /// any byte covered by an active dynptr slot. Each dynptr occupies a
    /// 16-byte pair (two adjacent 8-byte slots, both annotated). A direct
    /// stack write that overlaps any byte of the pair is the kernel's
    /// "cannot overwrite referenced dynptr" / partial-slot-invalidate
    /// rejection. We only flag *referenced* dynptrs (`ref_id != 0`) so
    /// that overwriting a Local/Skb/Xdp dynptr — which the kernel allows
    /// — stays accepted.
    pub fn write_overlaps_referenced_dynptr(&self, off: i64, size: i64) -> bool {
        let write_end = off + size;
        self.slots.iter().any(|(slot_off, spilled)| {
            let Some(d) = spilled.dynptr else {
                return false;
            };
            if d.ref_id == 0 {
                return false;
            }
            let slot_start = *slot_off as i64;
            let slot_end = slot_start + 8;
            off < slot_end && write_end > slot_start
        })
    }

    /// Collect base offsets of every dynptr-pair (any kind) whose 16
    /// bytes are touched by a stack write of `size` at `off`. Used to
    /// destroy unrefcounted dynptrs (`Local`/`Skb`/`Xdp`) on direct
    /// stack writes — kernel `destroy_if_dynptr_stack_slot`
    /// (verifier.c v6.15 L880) clears both slots and invalidates slices
    /// rather than rejecting the write. Returns base-slot offsets; the
    /// caller is expected to clear `(base_off, base_off+8)` and run
    /// `invalidate_dynptr_slices` on the slot's `dynptr_id`.
    pub fn dynptr_pairs_touched_by_write(&self, off: i64, size: i64) -> Vec<(i16, u32)> {
        let write_end = off + size;
        let mut out: Vec<(i16, u32)> = Vec::new();
        for (slot_off, spilled) in &self.slots {
            let Some(d) = spilled.dynptr else { continue };
            let slot_start = *slot_off as i64;
            let slot_end = slot_start + 8;
            if off < slot_end && write_end > slot_start {
                let base_off = if d.first_slot {
                    *slot_off
                } else {
                    *slot_off - 8
                };
                if !out.iter().any(|(b, _)| *b == base_off) {
                    out.push((base_off, d.dynptr_id));
                }
            }
        }
        out
    }

    /// True if a direct read at `off..off+size` overlaps any byte of a
    /// dynptr's body (W4.2). Programs may not read the dynptr metadata
    /// bytes — they're opaque kernel state. Applies to *any* dynptr
    /// kind, regardless of ref_id (the body of a Local/Skb/Xdp dynptr
    /// is also not user-readable). Helpers reach into the dynptr via
    /// `bpf_dynptr_read` / `bpf_dynptr_data` instead.
    pub fn read_overlaps_dynptr(&self, off: i64, size: i64) -> bool {
        let read_end = off + size;
        self.slots.iter().any(|(slot_off, spilled)| {
            if spilled.dynptr.is_none() {
                return false;
            }
            let slot_start = *slot_off as i64;
            let slot_end = slot_start + 8;
            off < slot_end && read_end > slot_start
        })
    }

    /// True if a stack access at `off..off+size` overlaps any byte of an
    /// active open-coded iterator's body (W3.2). Iter structs span
    /// `bpf_iter_size(kind)` bytes — the annotation lives only on the
    /// base byte, so we resolve the size by looking at each annotated
    /// slot. Applies to both reads and writes: programs treat iter
    /// bodies as opaque (only `*_new`/`*_next`/`*_destroy` may touch
    /// them). Without this, `spill_at` silently wipes the iter
    /// annotation on a direct write and no leak is detected at exit.
    pub fn access_overlaps_iterator(&self, off: i64, size: i64) -> bool {
        let access_end = off + size;
        self.slots.iter().any(|(slot_off, spilled)| {
            let Some(iter) = spilled.iterator else {
                return false;
            };
            let slot_start = *slot_off as i64;
            let slot_end =
                slot_start + crate::common::stack_objects::bpf_iter_size(iter.kind) as i64;
            off < slot_end && access_end > slot_start
        })
    }

    /// True if a stack access at `off..off+size` overlaps any byte of an
    /// active IRQ-flag slot. Mirrors `access_overlaps_iterator`. The
    /// IRQ flag occupies a fixed 8-byte slot. Used by `irq_flag_overwrite`
    /// detection — direct writes invalidate the slot's STACK_IRQ_FLAG
    /// mark in the kernel; we treat them as REJECT instead of silently
    /// stripping the annotation, since otherwise a missing `_restore`
    /// slips by the exit-time leak check.
    pub fn access_overlaps_irq_flag(&self, off: i64, size: i64) -> bool {
        let access_end = off + size;
        self.slots.iter().any(|(slot_off, spilled)| {
            if spilled.irq_flag.is_none() {
                return false;
            }
            let slot_start = *slot_off as i64;
            let slot_end = slot_start + 8;
            off < slot_end && access_end > slot_start
        })
    }

    pub fn live_slot_offsets(&self, live_regs: &HashSet<Reg>) -> Vec<i16> {
        self.slots
            .iter()
            .filter(|(_, spilled)| spilled.source_reg.is_some_and(|r| live_regs.contains(&r)))
            .map(|(offset, _)| *offset)
            .collect()
    }
}
