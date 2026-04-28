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
/// time (used by subsumption in W3.2c to match "same loop").
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct IteratorSlot {
    pub kind: IterKind,
    pub state: IterState,
    pub id: u32,
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

    pub fn live_slot_offsets(&self, live_regs: &HashSet<Reg>) -> Vec<i16> {
        self.slots
            .iter()
            .filter(|(_, spilled)| spilled.source_reg.is_some_and(|r| live_regs.contains(&r)))
            .map(|(offset, _)| *offset)
            .collect()
    }
}
