// src/zone/tnum.rs
//
// Tristate numbers for tracking bit-level information.
// Each bit can be: known-0, known-1, or unknown.
//
// Representation:
//   - `value`: bits known to be 1 (unknown bits are 0 here)
//   - `mask`:  bits that are unknown (1 = unknown, 0 = known)
//
// Invariant: (value & mask) == 0
//   Known-1 bits are in `value`, unknown bits are in `mask`, known-0 bits are in neither.
//
// Examples:
//   - Constant 5:        value=0b101, mask=0b000  (all bits known)
//   - Unknown:           value=0b000, mask=0b111...111 (all bits unknown)
//   - "At least 1":      value=0b001, mask=0b111...110 (bit 0 is 1, rest unknown)

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tnum {
    pub value: u64,  // Bits known to be 1
    pub mask: u64,   // Bits that are unknown
}

impl Tnum {
    /// A completely unknown value (any 64-bit value is possible)
    pub const UNKNOWN: Tnum = Tnum {
        value: 0,
        mask: u64::MAX,
    };

    /// Create a tnum representing an exact constant
    #[inline]
    pub fn constant(c: u64) -> Tnum {
        Tnum { value: c, mask: 0 }
    }

    /// Create a completely unknown tnum
    #[inline]
    pub fn unknown() -> Tnum {
        Tnum::UNKNOWN
    }

    /// Create a tnum where only the low `bits` are unknown
    /// Useful for representing values in range [0, 2^bits - 1]
    #[inline]
    pub fn unknown_bits(bits: u32) -> Tnum {
        if bits >= 64 {
            Tnum::UNKNOWN
        } else {
            Tnum {
                value: 0,
                mask: (1u64 << bits) - 1,
            }
        }
    }

    /// Check if this tnum represents an exact constant
    #[inline]
    pub fn is_const(&self) -> bool {
        self.mask == 0
    }

    /// Get the constant value (only valid if is_const() is true)
    #[inline]
    pub fn const_value(&self) -> Option<u64> {
        if self.is_const() {
            Some(self.value)
        } else {
            None
        }
    }

    /// Get the minimum possible value
    #[inline]
    pub fn min_value(&self) -> u64 {
        self.value // Unknown bits contribute 0 at minimum
    }

    /// Get the maximum possible value
    #[inline]
    pub fn max_value(&self) -> u64 {
        self.value | self.mask // Unknown bits contribute 1 at maximum
    }

    /// Check if the value could possibly be zero
    #[inline]
    pub fn could_be_zero(&self) -> bool {
        self.value == 0 // If any known bit is 1, it can't be zero
    }

    /// Check if the value is definitely non-zero
    #[inline]
    pub fn is_definitely_nonzero(&self) -> bool {
        self.value != 0 // At least one bit is known to be 1
    }

    /// Bitwise AND with another tnum
    pub fn and(self, other: Tnum) -> Tnum {
        // For AND:
        // - 0 & x = 0 (known)
        // - 1 & 1 = 1 (known)
        // - 1 & ? = ? (unknown)
        // - ? & ? = ? (unknown)
        let value = self.value & other.value;
        let mu = self.mask | other.mask; // Bits unknown in either input
        let mask = mu & !value; // Unknown unless both inputs have known-1
        
        // Wait, let me reconsider:
        // If self has known-0, result is known-0 regardless of other
        // If other has known-0, result is known-0 regardless of self
        // If both have known-1, result is known-1
        // Otherwise unknown
        
        // known-0 in self: bit NOT in (self.value | self.mask)
        // known-0 in other: bit NOT in (other.value | other.mask)
        
        // Actually the simple formula:
        // value = self.value & other.value (known-1 only if both are known-1)
        // mask = bits that COULD be 1 but aren't definitely 1
        //      = (self could be 1) & (other could be 1) & !(definitely 1)
        //      = (self.value | self.mask) & (other.value | other.mask) & !value
        let alpha = self.value | self.mask;  // bits that could be 1 in self
        let beta = other.value | other.mask; // bits that could be 1 in other
        let mask = (alpha & beta) & !value;
        
        Tnum { value, mask }
    }

    /// Bitwise AND with an immediate
    #[inline]
    pub fn and_imm(self, imm: u64) -> Tnum {
        self.and(Tnum::constant(imm))
    }

    /// Bitwise OR with another tnum
    pub fn or(self, other: Tnum) -> Tnum {
        // For OR:
        // - 1 | x = 1 (known)
        // - 0 | 0 = 0 (known)
        // - 0 | ? = ? (unknown)
        // - ? | ? = ? (unknown)
        
        // Known-1 if either input is known-1
        let value = self.value | other.value;
        
        // Unknown if: not known-1 AND (either input is unknown OR inputs differ)
        // Bits that are known-0 in self: !(self.value | self.mask)
        // Bits that are known-0 in other: !(other.value | other.mask)
        // Result is known-0 only if both are known-0
        let self_known_0 = !(self.value | self.mask);
        let other_known_0 = !(other.value | other.mask);
        let result_known_0 = self_known_0 & other_known_0;
        
        // mask = bits that are neither known-1 nor known-0
        let mask = !value & !result_known_0;
        
        Tnum { value, mask }
    }

    /// Bitwise OR with an immediate
    #[inline]
    pub fn or_imm(self, imm: u64) -> Tnum {
        self.or(Tnum::constant(imm))
    }

    /// Bitwise XOR with another tnum
    pub fn xor(self, other: Tnum) -> Tnum {
        // XOR: result is known only if both inputs are known (both known-0 or both known-1)
        let value = self.value ^ other.value;
        let mask = self.mask | other.mask;
        Tnum { value, mask }
    }

    /// Addition (approximate - may lose precision)
    pub fn add(self, other: Tnum) -> Tnum {
        // Addition with unknown bits is complex due to carries.
        // This is a conservative approximation from the Linux kernel.
        let sm = self.mask.wrapping_add(other.mask);
        let sv = self.value.wrapping_add(other.value);
        let sigma = sm.wrapping_add(sv);
        let chi = sigma ^ sv;
        let mu = chi | self.mask | other.mask;
        
        Tnum {
            value: sv & !mu,
            mask: mu,
        }
    }

    /// Add immediate
    #[inline]
    pub fn add_imm(self, imm: i64) -> Tnum {
        self.add(Tnum::constant(imm as u64))
    }

    /// Left shift by constant
    pub fn shl(self, shift: u32) -> Tnum {
        if shift >= 64 {
            Tnum::constant(0)
        } else {
            Tnum {
                value: self.value << shift,
                mask: self.mask << shift,
            }
        }
    }

    /// Logical right shift by constant
    pub fn shr(self, shift: u32) -> Tnum {
        if shift >= 64 {
            Tnum::constant(0)
        } else {
            Tnum {
                value: self.value >> shift,
                mask: self.mask >> shift,
            }
        }
    }

    /// Truncate to 32 bits (zero-extend)
    #[inline]
    pub fn trunc32(self) -> Tnum {
        Tnum {
            value: self.value & 0xFFFFFFFF,
            mask: self.mask & 0xFFFFFFFF,
        }
    }

    /// Intersect with another tnum (refine knowledge)
    /// Returns None if the intersection is empty (contradiction)
    pub fn intersect(self, other: Tnum) -> Option<Tnum> {
        // We want to combine knowledge from both tnums.
        // A bit is known-1 if either says it's known-1
        // A bit is known-0 if either says it's known-0
        // Contradiction if one says known-1 and other says known-0
        
        let self_known = !self.mask;
        let other_known = !other.mask;
        
        // Check for contradictions: both known but different values
        let both_known = self_known & other_known;
        if (self.value ^ other.value) & both_known != 0 {
            return None; // Contradiction!
        }
        
        // Merge: known bits from either, value from whichever knows it
        let mask = self.mask & other.mask;
        let value = (self.value & self_known) | (other.value & other_known);
        
        Some(Tnum { value, mask })
    }

    /// Check if this tnum could equal a specific value
    #[inline]
    pub fn could_equal(&self, val: u64) -> bool {
        // The value must match our known bits
        (val & !self.mask) == self.value
    }
}

impl Default for Tnum {
    fn default() -> Self {
        Tnum::UNKNOWN
    }
}

impl From<u64> for Tnum {
    fn from(c: u64) -> Self {
        Tnum::constant(c)
    }
}

impl From<i64> for Tnum {
    fn from(c: i64) -> Self {
        Tnum::constant(c as u64)
    }
}
