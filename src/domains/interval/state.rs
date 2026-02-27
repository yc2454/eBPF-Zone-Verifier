// Interval domain state representation
//
// Mirrors the kernel verifier's per-register tracking:
// - Signed and unsigned bounds (smin, smax, umin, umax)
// - Pointer offset tracking (fixed offset + variable range)

use crate::analysis::machine::reg::Reg;

/// Scalar interval bounds for a single register
/// Mirrors kernel's smin_value, smax_value, umin_value, umax_value
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScalarBounds {
    pub smin: i64,  // Signed minimum
    pub smax: i64,  // Signed maximum
    pub umin: u64,  // Unsigned minimum
    pub umax: u64,  // Unsigned maximum
}

impl ScalarBounds {
    /// Create bounds for an unknown value
    pub fn unknown() -> Self {
        ScalarBounds {
            smin: i64::MIN,
            smax: i64::MAX,
            umin: 0,
            umax: u64::MAX,
        }
    }

    /// Create bounds for a known constant
    pub fn constant(val: i64) -> Self {
        ScalarBounds {
            smin: val,
            smax: val,
            umin: val as u64,
            umax: val as u64,
        }
    }

    /// Create bounds for a non-negative value in range [0, max]
    #[allow(dead_code)]
    pub fn nonnegative(max: u64) -> Self {
        ScalarBounds {
            smin: 0,
            smax: max as i64,
            umin: 0,
            umax: max,
        }
    }

    /// Check if this represents a constant value
    pub fn is_constant(&self) -> bool {
        self.smin == self.smax && self.umin == self.umax
    }

    /// Get the constant value if this is constant
    pub fn get_constant(&self) -> Option<i64> {
        if self.is_constant() {
            Some(self.smin)
        } else {
            None
        }
    }

    /// Check if proven >= 0
    pub fn is_nonnegative(&self) -> bool {
        self.smin >= 0
    }

    /// Check if proven > 0
    pub fn is_positive(&self) -> bool {
        self.smin > 0
    }

    /// Check if proven == 0
    pub fn is_zero(&self) -> bool {
        self.smin == 0 && self.smax == 0
    }

    /// Check if in u32 range [0, 2^32-1]
    pub fn is_u32(&self) -> bool {
        self.smin >= 0 && self.umax <= u32::MAX as u64
    }

    /// Intersect with another bounds (take tighter constraints)
    #[allow(dead_code)]
    pub fn intersect(&self, other: &ScalarBounds) -> ScalarBounds {
        ScalarBounds {
            smin: self.smin.max(other.smin),
            smax: self.smax.min(other.smax),
            umin: self.umin.max(other.umin),
            umax: self.umax.min(other.umax),
        }
    }

    /// Join with another bounds (take looser constraints)
    #[allow(dead_code)]
    pub fn join(&self, other: &ScalarBounds) -> ScalarBounds {
        ScalarBounds {
            smin: self.smin.min(other.smin),
            smax: self.smax.max(other.smax),
            umin: self.umin.min(other.umin),
            umax: self.umax.max(other.umax),
        }
    }

    /// Apply signed constraint: value <= c
    pub fn assume_sle(&mut self, c: i64) {
        self.smax = self.smax.min(c);
        if c >= 0 {
            self.umax = self.umax.min(c as u64);
        }
    }

    /// Apply signed constraint: value >= c
    pub fn assume_sge(&mut self, c: i64) {
        self.smin = self.smin.max(c);
        if c >= 0 {
            self.umin = self.umin.max(c as u64);
        }
    }

    /// Apply unsigned constraint: value <= c
    #[allow(dead_code)]
    pub fn assume_ule(&mut self, c: u64) {
        self.umax = self.umax.min(c);
        if c <= i64::MAX as u64 {
            self.smax = self.smax.min(c as i64);
        }
    }

    /// Apply unsigned constraint: value >= c
    #[allow(dead_code)]
    pub fn assume_uge(&mut self, c: u64) {
        self.umin = self.umin.max(c);
        if c <= i64::MAX as u64 && self.smin >= 0 {
            self.smin = self.smin.max(c as i64);
        }
    }
}

impl Default for ScalarBounds {
    fn default() -> Self {
        Self::unknown()
    }
}

/// Pointer offset information
/// Tracks the relationship between a register and its base anchor
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PtrOffset {
    /// Which anchor this pointer is relative to
    pub anchor: Reg,
    /// Fixed offset from the anchor (like kernel's reg->off)
    pub offset: i64,
    /// Maximum variable range on top of offset (derived from var_off in kernel)
    /// This represents the uncertainty: actual offset is in [offset, offset + range]
    pub range: u64,
}

impl PtrOffset {
    /// Create offset info for a pointer equal to its anchor
    pub fn at_anchor(anchor: Reg) -> Self {
        PtrOffset {
            anchor,
            offset: 0,
            range: 0,
        }
    }

    /// Create offset info for a pointer at fixed offset from anchor
    #[allow(dead_code)]
    pub fn at_fixed(anchor: Reg, offset: i64) -> Self {
        PtrOffset {
            anchor,
            offset,
            range: 0,
        }
    }

    /// Create offset info with variable range
    #[allow(dead_code)]
    pub fn with_range(anchor: Reg, offset: i64, range: u64) -> Self {
        PtrOffset {
            anchor,
            offset,
            range,
        }
    }

    /// Check if the offset is exactly known (no variable part)
    #[allow(dead_code)]
    pub fn is_fixed(&self) -> bool {
        self.range == 0
    }

    /// Get the minimum possible offset
    pub fn min_offset(&self) -> i64 {
        self.offset
    }

    /// Get the maximum possible offset
    pub fn max_offset(&self) -> i64 {
        self.offset.saturating_add(self.range as i64)
    }
}

/// Per-register state in the interval domain
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegInterval {
    /// Scalar bounds for this register
    pub bounds: ScalarBounds,
    /// Optional pointer offset info (set when register holds a tracked pointer)
    pub ptr_offset: Option<PtrOffset>,
}

impl RegInterval {
    pub fn unknown() -> Self {
        RegInterval {
            bounds: ScalarBounds::unknown(),
            ptr_offset: None,
        }
    }

    pub fn constant(val: i64) -> Self {
        RegInterval {
            bounds: ScalarBounds::constant(val),
            ptr_offset: None,
        }
    }

    pub fn with_ptr_offset(bounds: ScalarBounds, ptr_offset: PtrOffset) -> Self {
        RegInterval {
            bounds,
            ptr_offset: Some(ptr_offset),
        }
    }
}

impl Default for RegInterval {
    fn default() -> Self {
        Self::unknown()
    }
}

/// The interval domain state
/// Tracks per-register bounds without relational constraints
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntervalState {
    /// Per-register interval information
    /// Index by Reg::idx() - includes all 12 registers + 3 anchors
    regs: [RegInterval; Reg::DBM_DIM],

    /// Packet geometry: known relationship between data and data_end
    /// If Some(n), then data_end - data >= n (packet has at least n bytes)
    /// This is learned from successful bounds checks
    packet_size_lower_bound: Option<u64>,
}

impl IntervalState {
    /// Create a new interval state with all registers unknown
    pub fn new() -> Self {
        let mut regs = std::array::from_fn(|_| RegInterval::unknown());

        // R0 (Zero) is always 0
        regs[Reg::Zero.idx()] = RegInterval::constant(0);

        // Initialize anchors to themselves at offset 0
        for anchor in [Reg::AnchorData, Reg::AnchorDataEnd, Reg::AnchorDataMeta] {
            regs[anchor.idx()] = RegInterval::with_ptr_offset(
                ScalarBounds::unknown(),
                PtrOffset::at_anchor(anchor),
            );
        }

        // R10 is the stack frame pointer - track it as an anchor for stack offsets
        // This allows us to compute distances like (R10 - 8) - R10 = -8
        regs[Reg::R10.idx()] = RegInterval::with_ptr_offset(
            ScalarBounds::unknown(),
            PtrOffset::at_anchor(Reg::R10),
        );

        IntervalState {
            regs,
            packet_size_lower_bound: None,
        }
    }

    /// Get the interval for a register
    pub fn get(&self, r: Reg) -> &RegInterval {
        &self.regs[r.idx()]
    }

    /// Get mutable reference to register interval
    pub fn get_mut(&mut self, r: Reg) -> &mut RegInterval {
        &mut self.regs[r.idx()]
    }

    /// Set the interval for a register
    pub fn set(&mut self, r: Reg, interval: RegInterval) {
        if r != Reg::Zero {
            self.regs[r.idx()] = interval;
        }
    }

    /// Get scalar bounds for a register
    pub fn get_bounds(&self, r: Reg) -> &ScalarBounds {
        &self.regs[r.idx()].bounds
    }

    /// Get mutable reference to scalar bounds
    pub fn get_bounds_mut(&mut self, r: Reg) -> &mut ScalarBounds {
        &mut self.regs[r.idx()].bounds
    }

    /// Get pointer offset info for a register
    pub fn get_ptr_offset(&self, r: Reg) -> Option<&PtrOffset> {
        self.regs[r.idx()].ptr_offset.as_ref()
    }

    /// Set pointer offset info for a register
    #[allow(dead_code)]
    pub fn set_ptr_offset(&mut self, r: Reg, offset: Option<PtrOffset>) {
        if r != Reg::Zero {
            self.regs[r.idx()].ptr_offset = offset;
        }
    }

    /// Get the [min, max] interval for a register (signed)
    pub fn get_interval(&self, r: Reg) -> (i64, i64) {
        let bounds = &self.regs[r.idx()].bounds;
        (bounds.smin, bounds.smax)
    }

    /// Check if register has a fixed (constant) value
    pub fn get_fixed_value(&self, r: Reg) -> Option<i64> {
        self.regs[r.idx()].bounds.get_constant()
    }

    /// Forget all information about a register
    pub fn forget(&mut self, r: Reg) {
        if r != Reg::Zero && !r.is_anchor() {
            self.regs[r.idx()] = RegInterval::unknown();
        }
    }

    /// Record that packet has at least n bytes (from bounds check)
    #[allow(dead_code)]
    pub fn set_packet_size_bound(&mut self, min_size: u64) {
        self.packet_size_lower_bound = Some(
            self.packet_size_lower_bound
                .map(|old| old.max(min_size))
                .unwrap_or(min_size),
        );
    }

    /// Get known lower bound on packet size
    pub fn get_packet_size_bound(&self) -> Option<u64> {
        self.packet_size_lower_bound
    }

    /// Check if the domain state is inconsistent (infeasible)
    pub fn is_inconsistent(&self) -> bool {
        for reg in &self.regs {
            if reg.bounds.smin > reg.bounds.smax || reg.bounds.umin > reg.bounds.umax {
                return true;
            }
        }
        false
    }
}

impl Default for IntervalState {
    fn default() -> Self {
        Self::new()
    }
}
