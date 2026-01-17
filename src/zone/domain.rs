// src/domain.rs
use crate::zone::dbm::{INF, Dbm};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Reg {
    Zero,   // constant 0
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    R8,
    R9,
    R10,
    // Later you can add Scratch(u16) or MapVal(u16) etc.
}

impl Reg {
    /// All "built-in" vars in index order used by DBM.
    pub const ALL: [Reg; 12] = [
        Reg::Zero,
        Reg::R0,
        Reg::R1,
        Reg::R2,
        Reg::R3,
        Reg::R4,
        Reg::R5,
        Reg::R6,
        Reg::R7,
        Reg::R8,
        Reg::R9,
        Reg::R10,
    ];

    /// Index used inside the DBM matrix.
    #[inline]
    pub fn idx(self) -> usize {
        match self {
            Reg::Zero => 0,
            Reg::R0   => 1,
            Reg::R1   => 2,
            Reg::R2   => 3,
            Reg::R3   => 4,
            Reg::R4   => 5,
            Reg::R5   => 6,
            Reg::R6   => 7,
            Reg::R7   => 8,
            Reg::R8   => 9,
            Reg::R9   => 10,
            Reg::R10  => 11,
        }
    }

    /// Human-readable name.
    #[inline]
    pub fn name(self) -> &'static str {
        match self {
            Reg::Zero => "0",
            Reg::R0   => "r0",
            Reg::R1   => "r1",
            Reg::R2   => "r2",
            Reg::R3   => "r3",
            Reg::R4   => "r4",
            Reg::R5   => "r5",
            Reg::R6   => "r6",
            Reg::R7   => "r7",
            Reg::R8   => "r8",
            Reg::R9   => "r9",
            Reg::R10  => "r10",
        }
    }

    pub fn idx_to_reg(idx: usize) -> Option<Reg> {
        match idx {
            0  => Some(Reg::Zero),
            1  => Some(Reg::R0),
            2  => Some(Reg::R1),
            3  => Some(Reg::R2),
            4  => Some(Reg::R3),
            5  => Some(Reg::R4),
            6  => Some(Reg::R5),
            7  => Some(Reg::R6),
            8  => Some(Reg::R7),
            9  => Some(Reg::R8),
            10 => Some(Reg::R9),
            11 => Some(Reg::R10),
            _  => None,
        }
    }
}

pub fn reg_to_index(r: Reg) -> Option<usize> {
    match r {
        Reg::R0  => Some(0),
        Reg::R1  => Some(1),
        Reg::R2  => Some(2),
        Reg::R3  => Some(3),
        Reg::R4  => Some(4),
        Reg::R5  => Some(5),
        Reg::R6  => Some(6),
        Reg::R7  => Some(7),
        Reg::R8  => Some(8),
        Reg::R9  => Some(9),
        Reg::R10 => Some(10),
        Reg::Zero => None,
    }
}

/// Simple wrapper so you can pass around an env if you want to extend later.
#[derive(Debug)]
pub struct RegEnv;

impl RegEnv {
    pub fn len(&self) -> usize {
        Reg::ALL.len()
    }

    pub fn all(&self) -> &'static [Reg] {
        &Reg::ALL
    }

    pub fn index(&self, v: Reg) -> usize {
        v.idx()
    }

}

/// Global env you can use anywhere without initializing in `main`.
pub static REG_ENV: RegEnv = RegEnv;

/// --- analysis helpers ---
/// 
// Extract bounds if finite.
// ub from: x - 0 <= ub
// lb from: 0 - x <= -lb  => lb = - (0 - x bound)
pub fn get_bounds(dbm: &Dbm, x: Reg, zero: Reg) -> (Option<i64>, Option<i64>) {
    let ub = dbm.get(x, zero);
    let lb_neg = dbm.get(zero, x);

    let ub_opt = if ub >= INF { None } else { Some(ub) };
    let lb_opt = if lb_neg >= INF { None } else { Some(-lb_neg) };

    (lb_opt, ub_opt)
}

// --- transfer functions ---
// exec.rs wants a uniform name.
pub fn forget(dbm: &mut Dbm, x: Reg) {
    dbm.forget_var(x);
    dbm.close(); // keep the "always closed" invariant
}

// dst += imm
pub fn assign_add_imm(dbm: &mut Dbm, dst: Reg, imm: i64) {
    add_imm(dbm, dst, imm); // your add_imm already closes
}

// dst += src
pub fn assign_add_reg(dbm: &mut Dbm, dst: Reg, src: Reg, zero: Reg) {
    // dst := dst + src  (sound interval-style update)
    let (ld, ud) = get_bounds(dbm, dst, zero);
    let (ls, us) = get_bounds(dbm, src, zero);

    dbm.forget_var(dst);

    if let (Some(ld), Some(ls)) = (ld, ls) {
        assume_ge_const(dbm, dst, ld + ls); // closes
    }
    if let (Some(ud), Some(us)) = (ud, us) {
        assume_le_const(dbm, dst, ud + us); // closes
    }

    // If neither bound exists, dst becomes unconstrained; still close to keep invariant.
    dbm.close();
}

/// Handle: dst = dst - src
pub fn assign_sub_reg(dbm: &mut Dbm, dst: Reg, src: Reg) {
    // 1. Get current bounds for both registers
    // We use a known zero register (like r10/frame pointer reference) or just absolute bounds if available
    let zero = Reg::Zero;
    
    let (dst_min, dst_max) = get_bounds(dbm, dst, zero);
    let (src_min, src_max) = get_bounds(dbm, src, zero);

    // 2. Subtraction destroys the delicate difference relationships (x - z <= c)
    // because (x - y) - z <= c requires knowing y + z relationship.
    // So we must forget the old 'dst'.
    forget(dbm, dst);

    // 3. Re-establish bounds based on Interval Arithmetic
    // New Min = Old Min - Src Max
    // New Max = Old Max - Src Min
    if let (Some(d_min), Some(d_max), Some(s_min), Some(s_max)) = (dst_min, dst_max, src_min, src_max) {
        // Check for underflow/overflow safety if you want, usually BPF wraps.
        // We assume 64-bit signed math for the verification domain.
        
        let new_min = d_min.saturating_sub(s_max);
        let new_max = d_max.saturating_sub(s_min);

        assume_ge_const(dbm, dst, new_min);
        assume_le_const(dbm, dst, new_max);
    }
}

// dst &= mask
pub fn assign_and_mask(dbm: &mut Dbm, dst: Reg, mask: i64, zero: Reg) {
    dbm.forget_var(dst);

    // 0 <= dst <= mask
    dbm.add_constraint(dst, zero, mask);
    dbm.add_constraint(zero, dst, 0);

    dbm.close();
}

// x <= y  encoded as: x - y <= 0
pub fn assume_le_var(dbm: &mut Dbm, x: Reg, y: Reg) {
    dbm.add_constraint(x, y, 0);
    dbm.close();
}

// x >= y  encoded as: y - x <= 0
pub fn assume_ge_var(dbm: &mut Dbm, x: Reg, y: Reg) {
    dbm.add_constraint(y, x, 0);
    dbm.close();
}

// x > y  encoded as: y - x <= -1
pub fn assume_gt_var(dbm: &mut Dbm, x: Reg, y: Reg) {
    dbm.add_constraint(y, x, -1);
    dbm.close();
}

// x <= y + c  encoded as: x - y <= c
pub fn assume_le_var_plus_const(dbm: &mut Dbm, x: Reg, y: Reg, c: i64) {
    dbm.add_constraint(x, y, c);
    dbm.close();
}

pub fn assign_zero(dbm: &mut Dbm, x: Reg, zero: Reg) {
    // Overwrite x: kill all old info about x
    dbm.forget_var(x);

    // Now enforce x == 0 (relative to `zero` var)
    dbm.add_constraint(x, zero, 0);   // x - 0 ≤ 0  ⇒ x ≤ 0
    dbm.add_constraint(zero, x, 0);   // 0 - x ≤ 0  ⇒ x ≥ 0

    dbm.close();
}

pub fn assign_eq(dbm: &mut Dbm, x: Reg, y: Reg) {
    dbm.forget_var(x);
    dbm.add_constraint(x, y, 0);
    dbm.add_constraint(y, x, 0);
    dbm.close();
}

// x <= c   encoded as: x - 0 <= c
pub fn assume_le_const(dbm: &mut Dbm, x: Reg, c: i64) {
    dbm.add_constraint(x, Reg::Zero, c);
    dbm.close();
}

// x >= c   encoded as: 0 - x <= -c
pub fn assume_ge_const(dbm: &mut Dbm, x: Reg, c: i64) {
    dbm.add_constraint(Reg::Zero, x, -c);
    dbm.close();
}

// x == c   encoded as: x <= c AND x >= c
pub fn assume_eq_const(dbm: &mut Dbm, x: Reg, c: i64) {
    dbm.add_constraint(x, Reg::Zero, c);
    dbm.add_constraint(Reg::Zero, x, -c);
    dbm.close();
}

pub fn assume_less_than(d: &mut Dbm, x: Reg, c: i64) {
    let bound = c - 1;
    d.add_constraint(x, Reg::Zero, bound);
    d.close();
}

pub fn add_imm(d: &mut Dbm, x: Reg, c: i64) {
    let xi = x.idx();
    let n = d.num_vars();

    // Shift row/col for x
    for zj in 0..n {
        // x - z <= old(x - z) + c
        let old_xz = d.get_idx(xi, zj);
        if old_xz < INF {
            d.set_idx(xi, zj, old_xz.saturating_add(c));
        }
    }
    for zi in 0..n {
        // z - x <= old(z - x) - c
        let old_zx = d.get_idx(zi, xi);
        if old_zx < INF {
            d.set_idx(zi, xi, old_zx.saturating_sub(c));
        }
    }
    // keep diagonal sane
    d.set_idx(xi, xi, 0);

    d.close();
}

// dst *= imm
pub fn assign_mul_imm(dbm: &mut Dbm, dst: Reg, imm: i64, zero: Reg) {
    // Handle easy special cases first.
    if imm == 0 {
        // dst = 0
        assign_zero(dbm, dst, zero);
        return;
    }

    if imm == 1 {
        // No-op on zones.
        return;
    }

    if imm < 0 {
        // Multiplication by negative constant flips the ordering of bounds.
        // We *could* do the full interval transform here, but for now stay
        // simple and sound: drop info about dst.
        forget(dbm, dst);
        return;
    }

    // imm > 0: monotone scaling, so we can scale bounds.
    let (ld_opt, ud_opt) = get_bounds(dbm, dst, zero);

    // Kill old relational info about dst.
    dbm.forget_var(dst);

    if let Some(ld) = ld_opt {
        let new_lb = ld.saturating_mul(imm);
        assume_ge_const(dbm, dst, new_lb);
    }
    if let Some(ud) = ud_opt {
        let new_ub = ud.saturating_mul(imm);
        assume_le_const(dbm, dst, new_ub);
    }

    // If we had no bounds, dst just becomes unconstrained.
    dbm.close();
}

/// Handle: dst = dst / imm
pub fn assign_div_imm(dbm: &mut Dbm, reg: Reg, imm: i64) {
    if imm == 0 {
        // Technically this is a runtime crash. 
        // We leave the state as is (or top) and let the verifier fail logic handle it.
        return; 
    }

    // 1. Get current concrete bounds (Interval Analysis)
    let (lo, hi) = get_bounds(dbm, reg, Reg::Zero); // r10 is not used for scalar bounds usually, checking against zero

    // 2. Division breaks linear relationships. We must FORGET the register.
    forget(dbm, reg);

    // 3. Compute new bounds
    // BPF Div is unsigned. We assume values are treated as u64.
    // However, our DBM is i64. We treat negative numbers as "Large Positive" (Unknown).
    if let (Some(l), Some(h)) = (lo, hi) {
        if l >= 0 && h >= 0 {
            // Safe positive range
            let new_lo = l / imm;
            let new_hi = h / imm;
            
            // 4. Constrain with new bounds
            // dst >= new_lo  =>  0 - dst <= -new_lo
            // dst <= new_hi  =>  dst - 0 <= new_hi
            assume_ge_const(dbm, reg, new_lo);
            assume_le_const(dbm, reg, new_hi);
        }
    } else {
        // If we didn't know the bounds, or they were "negative",
        // we know nothing about the result except that it is smaller than u64::MAX.
        // Since we forgot the register in step 2, it is already "Unknown".
    }
}

/// Handle: dst = dst / src
pub fn assign_div_reg(dbm: &mut Dbm, dst: Reg, _src: Reg) {
    // We know very little about division by a variable.
    // dst / src results in a value smaller than dst (if src > 1).
    
    // 1. Conservative approach: Forget the destination
    forget(dbm, dst);

    // 2. We could add constraints if we knew bounds of src, 
    // but for now, "Unknown" is the safest sound approximation.
}

/// Simulates `reg &= imm`.
/// Since bitwise AND is non-linear, we forget precise relationships but 
/// deduce that the result is in the range [0, imm].
pub fn bit_and_const(dbm: &mut Dbm, reg: Reg, imm: i64) {
    // 1. Bitwise operations destroy linear relationships (e.g. x < y).
    // We must remove 'reg' from the matrix to avoid unsound conclusions.
    forget(dbm, reg);

    // 2. Apply new bounds derived from the mask.
    // The result of (x & imm) is treated as unsigned, so it is >= 0.
    assume_ge_const(dbm, reg, 0);

    // The result cannot be larger than the mask itself (if mask is positive).
    // e.g. (x & 0xFF) <= 255.
    if imm >= 0 {
        assume_le_const(dbm, reg, imm);
    }
}

pub fn assign_neg(dbm: &mut Dbm, reg: Reg) {
    // 1. Get current concrete bounds [lo, hi]
    let (lo, hi) = get_bounds(dbm, reg, Reg::Zero); // r10/zero
    
    // 2. Forget existing relationships (destroy x - y <= c)
    forget(dbm, reg);

    // 3. Apply new bounds: [-hi, -lo]
    // Note: checking for overflow (i64::MIN) is good practice but BPF implies wrapping.
    if let (Some(l), Some(h)) = (lo, hi) {
        // new_lower = -old_upper
        // new_upper = -old_lower
        let new_lo = h.wrapping_neg();
        let new_hi = l.wrapping_neg();
        
        assume_ge_const(dbm, reg, new_lo);
        assume_le_const(dbm, reg, new_hi);
    }
}

pub fn proven_u32_range(dbm: &Dbm, v: Reg, zero: Reg) -> bool {
    let vi = REG_ENV.index(v);
    let zi = REG_ENV.index(zero);
    let ub = dbm.raw(vi, zi);
    let lb = dbm.raw(zi, vi);
    // 0 <= v <= u32::MAX
    ub <= 0xffff_ffff && lb <= 0
}
