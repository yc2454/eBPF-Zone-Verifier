// src/analysis/machine/stack_ops.rs
//
// Stack spill / reload / anchor-restore methods for `State`. Split from
// state.rs to keep that file focused on the core model; these are the
// heavyweight implementations (~500 lines) that translate between register
// values and StackState slots.

use crate::analysis::machine::frame_stack::FrameLevel;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::stack_state::{ScalarBounds, SpilledReg};
use crate::ast::MemSize;
use crate::domains::dbm::INF;
use crate::domains::numeric::NumericDomain;
use crate::domains::tnum::Tnum;
use log::trace;

use super::state::State;

impl State {
    /// Spill into a specific frame (cross-frame, e.g. store via PtrToStack)
    pub fn spill_at(&mut self, level: FrameLevel, reg: Reg, offset: i16, size: MemSize) {
        let is_aligned = (offset % 8) == 0;
        let reg_type = self.types.get(reg);

        // Only U64 stores at aligned offsets can preserve pointer types
        let preserved_type = if size == MemSize::U64 && is_aligned {
            reg_type
        } else {
            RegType::ScalarValue
        };

        // Save pointer bounds if applicable
        let ptr_bounds = if size == MemSize::U64 && is_aligned {
            use crate::analysis::machine::stack_state::PointerBounds;
            let (i_off, i_var, i_range) = self.save_interval_ptr_offset(reg);
            if i_off.is_some() || i_var.is_some() || i_range.is_some() {
                Some(PointerBounds::Interval {
                    off: i_off,
                    var_off: i_var,
                    range: i_range,
                })
            } else {
                let (a, lo, hi) = self.save_anchor_info(reg);
                let (ea, elo, ehi) = self.save_secondary_anchor_info(reg);
                if a.is_some()
                    || lo.is_some()
                    || hi.is_some()
                    || ea.is_some()
                    || elo.is_some()
                    || ehi.is_some()
                {
                    Some(PointerBounds::Zone {
                        anchor: a,
                        anchor_lo: lo,
                        anchor_hi: hi,
                        end_anchor: ea,
                        end_lo: elo,
                        end_hi: ehi,
                    })
                } else {
                    None
                }
            }
        } else {
            None
        };

        let (min, max) = self.domain.get_interval(reg);
        trace!("At spilling, {} bounds: [{}, {}]", reg.name(), min, max);

        // Only track as proper spill if 8-byte aligned
        let source_reg = if is_aligned { Some(reg) } else { None };

        // Allocate (or reuse) a scalar id for any aligned scalar spill so
        // the slot — and any same-width fill — joins the source's scalar
        // equivalence class. Mirrors kernel's `assign_scalar_id_before_mov`
        // at spill time. Without this, post-spill branch refinements on
        // the source can't fan out to slot/fill, which leaves dead
        // branches reachable in the verifier_spill_fill::*_ok tests.
        let slot_scalar_id = if is_aligned
            && size.bytes() <= 8
            && matches!(preserved_type, RegType::ScalarValue)
        {
            let id = match self.scalar_ids.get(&reg).copied() {
                Some(id) => id,
                None => {
                    let new_id = crate::analysis::machine::reg_types::new_scalar_id();
                    self.scalar_ids.insert(reg, new_id);
                    new_id
                }
            };
            Some(id)
        } else if size == MemSize::U64 && is_aligned {
            self.scalar_ids.get(&reg).copied()
        } else {
            None
        };

        let spilled = SpilledReg {
            source_reg,
            reg_type: preserved_type,
            tnum: self.tnums.get(&reg).cloned().unwrap_or(Tnum::unknown()),
            bounds: ScalarBounds { min, max },
            size,
            ptr_bounds,
            scalar_id: slot_scalar_id,
            precise: is_aligned && size == MemSize::U64 && self.precise_regs.contains(&reg),
            iterator: None,
            dynptr: None,
                    irq_flag: None,
        };

        let stack = &mut self.frames.get_mut(level).stack;
        for i in 0..size.bytes() {
            let current_byte = offset + i as i16;
            if i == 0 {
                stack.insert(current_byte, spilled.clone());
            } else {
                stack.insert(
                    current_byte,
                    SpilledReg {
                        source_reg: None,
                        reg_type: RegType::ScalarValue,
                        tnum: Tnum::unknown(),
                        bounds: ScalarBounds {
                            min: i64::MIN,
                            max: i64::MAX,
                        },
                        size,
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
    }

    pub fn store_imm_to_stack_at(
        &mut self,
        level: FrameLevel,
        imm: i64,
        offset: i16,
        size: MemSize,
    ) {
        let is_aligned = (offset % 8) == 0;

        // Mask the immediate value to the store size
        let masked_imm = match size {
            MemSize::U8 => (imm as u8) as i64,
            MemSize::U16 => (imm as u16) as i64,
            MemSize::U32 => (imm as u32) as i64,
            MemSize::U64 => imm,
        };

        // For immediate stores, always track exact bounds since we know the value.
        // The alignment check only affects whether we can reliably fill/restore,
        // but we should still track the bounds for validation purposes.
        let (tnum, bounds, _source_reg) = (
            Tnum::constant(masked_imm as u64),
            ScalarBounds {
                min: masked_imm,
                max: masked_imm,
            },
            if is_aligned { Some(Reg::R0) } else { None },
        );

        let slot_content = SpilledReg {
            source_reg: if is_aligned { Some(Reg::R0) } else { None }, // Use dummy reg to indicate "trackable"
            reg_type: RegType::ScalarValue,
            tnum,
            bounds,
            size,
            ptr_bounds: None,
            scalar_id: None,
            precise: false,
            iterator: None,
            dynptr: None,
                    irq_flag: None,
        };

        let stack = &mut self.frames.get_mut(level).stack;
        for i in 0..size.bytes() {
            let current_byte = offset + i as i16;
            if i == 0 {
                stack.insert(current_byte, slot_content.clone());
            } else {
                stack.insert(
                    current_byte,
                    SpilledReg {
                        source_reg: None,
                        reg_type: RegType::ScalarValue,
                        tnum: Tnum::unknown(),
                        bounds: ScalarBounds {
                            min: i64::MIN,
                            max: i64::MAX,
                        },
                        size,
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
    }

    /// Reload from current frame
    pub fn fill(&mut self, dst: Reg, offset: i16, size: MemSize) -> bool {
        let level = self.frames.current_level();
        self.fill_at(level, dst, offset, size)
    }

    /// Reload from a specific frame (cross-frame)
    pub fn fill_at(&mut self, level: FrameLevel, dst: Reg, offset: i16, size: MemSize) -> bool {
        let stack = &self.frames.get(level).stack;

        // Check all bytes we're reading are initialized
        for i in 0..size.bytes() {
            let current_byte = offset + i as i16;
            if stack.get_slot(current_byte).is_none() {
                return false; // Reading uninitialized memory
            }
        }

        // Get the slot at base offset
        let spilled = match stack.get_slot(offset).cloned() {
            Some(s) => s,
            None => return false,
        };

        self.domain.forget(dst);

        // Check if we can preserve type/bounds:
        // 1. Must be reading from start of a spilled value (source_reg.is_some())
        // 2. Load size must match store size
        // 3. Offset must be 8-byte aligned
        let is_aligned = (offset % 8) == 0;
        let sizes_match = spilled.source_reg.is_some() && spilled.size == size;


        // Try to extract a precise (sub-)value when reading a narrower
        // (or unaligned) slice of a wider spill whose enclosing tnum
        // pins enough bits. Walk back up to 7 bytes to find the slot
        // holding the actual spilled value. Placeholder bytes have
        // tnum=unknown (mask=u64::MAX) and large size, so the
        // alignment+const gates below let real spills win the search.
        let narrowed_tnum: Option<Tnum> = if !sizes_match && size.bytes() <= 8 {
            let mut found: Option<Tnum> = None;
            for back in 0..8i16 {
                let base = offset - back;
                if let Some(s) = stack.get_slot(base) {
                    // Aligned-base aligned-width spills are the only
                    // ones we trust beyond the simple zero (STACK_ZERO)
                    // case — kernel marks unaligned register spills
                    // STACK_MISC. We treat constant-zero stores as
                    // safe at any alignment to model STACK_ZERO.
                    let base_aligned = base % 8 == 0;
                    let covers = (back as usize) + size.bytes() <= s.size.bytes();
                    if !covers {
                        continue;
                    }
                    let trustable = base_aligned || (s.tnum.is_const() && s.tnum.value == 0);
                    if !trustable {
                        continue;
                    }
                    let shift = (back as u64) * 8;
                    let v = s.tnum.value >> shift;
                    let m = s.tnum.mask >> shift;
                    let mask: u64 = match size {
                        MemSize::U8 => 0xff,
                        MemSize::U16 => 0xffff,
                        MemSize::U32 => 0xffff_ffff,
                        MemSize::U64 => u64::MAX,
                    };
                    let nm = m & mask;
                    // Nothing pinned within the fill width → no info beyond
                    // the existing unbounded fallback. Skip to avoid spurious
                    // bounds (e.g. signed-overflow at U64) and pointless work.
                    if nm == mask {
                        break;
                    }
                    found = Some(Tnum {
                        value: v & mask,
                        mask: nm,
                    });
                    break;
                }
            }
            found
        } else {
            None
        };

        // Special case: u32 LE-low fill of an aligned u64 scalar spill
        // whose high 32 bits are known zero. The low half carries the
        // full spilled value, so preserve tnum, bounds AND scalar_id —
        // matching kernel's u32-fill-after-u64-spill-preserve-id rule.
        // (Counterpart `_clear_id` test fails the high-bits-zero check.)
        if !sizes_match
            && size == MemSize::U32
            && spilled.size == MemSize::U64
            && is_aligned
            && spilled.source_reg.is_some()
            && matches!(spilled.reg_type, RegType::ScalarValue)
            && (spilled.tnum.mask & 0xFFFFFFFF_00000000) == 0
            && (spilled.tnum.value >> 32) == 0
        {
            self.types.set(dst, RegType::ScalarValue);
            self.tnums.insert(dst, spilled.tnum.clone());
            self.domain
                .assign_interval(dst, spilled.bounds.min, spilled.bounds.max);
            if let Some(id) = spilled.scalar_id {
                self.scalar_ids.insert(dst, id);
            } else {
                self.scalar_ids.remove(&dst);
            }
            if spilled.precise {
                self.precise_regs.insert(dst);
            } else {
                self.precise_regs.remove(&dst);
            }
            return true;
        }

        if sizes_match && is_aligned {
            // Preserve type and bounds
            self.types.set(dst, spilled.reg_type);
            self.tnums.insert(dst, spilled.tnum);
            self.domain
                .assign_interval(dst, spilled.bounds.min, spilled.bounds.max);

            // Restore scalar id so the filled register remains part of any
            // existing copy chain (e.g. a spilled then reloaded r1 shares the
            // same id as copies of it that stayed in registers).
            if let Some(id) = spilled.scalar_id {
                self.scalar_ids.insert(dst, id);
            } else {
                self.scalar_ids.remove(&dst);
            }

            // Restore precision mark carried at spill time.
            if spilled.precise {
                self.precise_regs.insert(dst);
            } else {
                self.precise_regs.remove(&dst);
            }

            // Only restore anchors for U64 (pointers need full 64-bit)
            if size == MemSize::U64 {
                self.restore_anchor_info(dst, &spilled);
            }
        } else if let Some(tn) = narrowed_tnum {
            // Narrowing read of a wider spill whose tnum pins (some of)
            // the bits we're loading (any byte offset within the wider
            // value, LE byte order).
            self.types.set(dst, RegType::ScalarValue);
            let v = tn.value;
            let m = tn.mask;
            // Bounds derived from the narrowed tnum: low = pinned bits,
            // high = pinned | unknown bits. For partial-knowledge tnums
            // this is the tightest interval we can claim without the
            // spill-time bounds.
            let lo = v as i64;
            let hi = (v | m) as i64;
            self.tnums.insert(dst, tn);
            self.domain.assign_interval(dst, lo, hi);
            self.scalar_ids.remove(&dst);
            self.precise_regs.remove(&dst);
        } else {
            // Size mismatch or unaligned - return unbounded scalar for the load size
            self.types.set(dst, RegType::ScalarValue);
            let (min, max) = size.unbounded_scalar_bounds();
            self.tnums.insert(dst, Tnum::unknown());
            self.domain.assign_interval(dst, min, max);
            self.scalar_ids.remove(&dst);
            self.precise_regs.remove(&dst);
        }

        true
    }

    pub fn save_anchor_info(&self, reg: Reg) -> (Option<Reg>, Option<i64>, Option<i64>) {
        let anchor = match self.types.get(reg) {
            RegType::PtrToPacket => Some(Reg::AnchorData),
            RegType::PtrToPacketMeta => Some(Reg::AnchorDataMeta),
            RegType::PtrToPacketEnd => Some(Reg::AnchorDataEnd),
            _ => None,
        };

        if let Some(a) = anchor {
            let hi = self.domain.get(reg, a); // reg - anchor <= hi
            let lo = self.domain.get(a, reg); // anchor - reg <= lo  (i.e., reg - anchor >= -lo)
            let hi = if hi >= INF { None } else { Some(hi) };
            let lo = if lo >= INF { None } else { Some(lo) };
            (Some(a), lo, hi)
        } else {
            (None, None, None)
        }
    }

    /// Save a packet pointer's secondary anchor relation (the @data_end
    /// edge for PtrToPacket / PtrToPacketMeta, or the @data edge for
    /// PtrToPacketEnd). Returns `(None, None, None)` for non-packet
    /// pointers and when the constraint is INF.
    ///
    /// Needed alongside `save_anchor_info` because the relations between
    /// distinct packet anchors are bounded but not fixed: a `r - @data`
    /// bound preserved across spill/fill is insufficient on its own to
    /// reconstruct a tighter `r - @data_end` bound that the access-site
    /// `end_ok` check depends on.
    pub fn save_secondary_anchor_info(
        &self,
        reg: Reg,
    ) -> (Option<Reg>, Option<i64>, Option<i64>) {
        let secondary = match self.types.get(reg) {
            RegType::PtrToPacket | RegType::PtrToPacketMeta => Some(Reg::AnchorDataEnd),
            RegType::PtrToPacketEnd => Some(Reg::AnchorData),
            _ => None,
        };

        if let Some(a) = secondary {
            let hi = self.domain.get(reg, a);
            let lo = self.domain.get(a, reg);
            let hi = if hi >= INF { None } else { Some(hi) };
            let lo = if lo >= INF { None } else { Some(lo) };
            (Some(a), lo, hi)
        } else {
            (None, None, None)
        }
    }

    /// Save interval mode PtrOffset info for a register
    pub fn save_interval_ptr_offset(&self, reg: Reg) -> (Option<i64>, Option<u64>, Option<i64>) {
        if let NumericDomain::Interval(ref ivl) = self.domain {
            if let Some(ptr_off) = ivl.get_ptr_offset(reg) {
                return (Some(ptr_off.off), Some(ptr_off.var_off), ptr_off.range);
            }
        }
        (None, None, None)
    }

    pub fn restore_anchor_info(&mut self, reg: Reg, spilled: &SpilledReg) {
        trace!("Restoring anchor info for {}", reg.name());
        trace!("{:?}, ", spilled);

        // Map-value pointers are self-anchored at the synthetic
        // `Reg::Zero` (interval_ops::init_map_value_ptr) and ALWAYS
        // have a defined in-value offset (0 for a fresh lookup). A
        // spill taken BEFORE the `OrNull → Value` null-check carries
        // no captured `ptr_bounds` — `PtrToMapValueOrNull` never gets
        // `init_map_value_ptr`, so `save_interval_ptr_offset` returned
        // None. The null-check propagates the slot's *type*
        // OrNull→Value, but without re-establishing the offset the
        // filled pointer had none and `interval_check_map_access` fell
        // back to the (unbounded) scalar bounds → an in-bounds
        // `value[k]` load was rejected "Unsafe variable map access
        // range [1, 2^32+1]" (cilium lb4/6_reverse_nat, ct/snat —
        // ~23 FR). Default the offset to 0 here (the kernel preserves
        // PTR_TO_MAP_VALUE off/var_off/range across spill/fill, and a
        // fresh value pointer is off 0); the `Interval` arm below
        // overrides with the precise captured offset when a spill was
        // taken after pointer arithmetic.
        if matches!(
            spilled.reg_type,
            RegType::PtrToMapValue { .. } | RegType::PtrToMapValueOrNull { .. }
        ) {
            self.domain.init_map_value_ptr(reg);
        }

        use crate::analysis::machine::stack_state::PointerBounds;
        match &spilled.ptr_bounds {
            Some(PointerBounds::Zone {
                anchor,
                anchor_lo,
                anchor_hi,
                end_anchor,
                end_lo,
                end_hi,
            }) => {
                let mut touched = false;
                if let Some(anchor_reg) = anchor {
                    if let Some(hi) = anchor_hi {
                        self.domain.add_constraint(reg, *anchor_reg, *hi);
                    }
                    if let Some(lo) = anchor_lo {
                        self.domain.add_constraint(*anchor_reg, reg, *lo);
                    }
                    touched = true;
                }
                if let Some(end_reg) = end_anchor {
                    if let Some(hi) = end_hi {
                        self.domain.add_constraint(reg, *end_reg, *hi);
                    }
                    if let Some(lo) = end_lo {
                        self.domain.add_constraint(*end_reg, reg, *lo);
                    }
                    touched = true;
                }
                if touched {
                    self.domain.close();
                }
            }
            Some(PointerBounds::Interval {
                off,
                var_off,
                range,
            }) => {
                // Determine anchor from register type
                let anchor = match spilled.reg_type {
                    RegType::PtrToPacket => Some(Reg::AnchorData),
                    RegType::PtrToPacketMeta => Some(Reg::AnchorDataMeta),
                    RegType::PtrToPacketEnd => Some(Reg::AnchorDataEnd),
                    RegType::PtrToStack { .. } => Some(Reg::R10),
                    // Map-value pointers self-anchor at Reg::Zero
                    // (init_map_value_ptr). Restoring the captured
                    // off/var_off/range here overrides the off=0
                    // default set above for spills taken after
                    // in-value pointer arithmetic.
                    RegType::PtrToMapValue { .. }
                    | RegType::PtrToMapValueOrNull { .. } => Some(Reg::Zero),
                    _ => None, // fallback is None
                };

                if let (Some(anchor_reg), Some(o)) = (anchor, off) {
                    if let NumericDomain::Interval(ref mut ivl) = self.domain {
                        let v = var_off.unwrap_or(0);
                        let ptr_offset = crate::domains::interval::PtrOffset {
                            anchor: anchor_reg,
                            off: *o,
                            var_off: v,
                            range: *range,
                            // id not round-tripped through spill/fill
                            // today; conservative None — loses id-aware
                            // refinement on reload but stays sound.
                            id: None,
                        };

                        // Set the PtrOffset on the register
                        ivl.get_mut(reg).ptr_offset = Some(ptr_offset);
                    }
                }
            }
            None => {}
        }
    }

    /// Called on every stack access to track depth
    pub fn update_frame_depth(&mut self, off: i16) {
        if off < 0 && off > i16::MIN {
            let depth = (-off) as u16;
            self.frame_depth = self.frame_depth.max(depth);
        }
    }
}
