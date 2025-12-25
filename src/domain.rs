// src/domain.rs
use crate::Dbm;
use crate::dbm::INF;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Var {
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

impl Var {
    /// All "built-in" vars in index order used by DBM.
    pub const ALL: [Var; 12] = [
        Var::Zero,
        Var::R0,
        Var::R1,
        Var::R2,
        Var::R3,
        Var::R4,
        Var::R5,
        Var::R6,
        Var::R7,
        Var::R8,
        Var::R9,
        Var::R10,
    ];

    /// Index used inside the DBM matrix.
    #[inline]
    pub fn idx(self) -> usize {
        match self {
            Var::Zero => 0,
            Var::R0   => 1,
            Var::R1   => 2,
            Var::R2   => 3,
            Var::R3   => 4,
            Var::R4   => 5,
            Var::R5   => 6,
            Var::R6   => 7,
            Var::R7   => 8,
            Var::R8   => 9,
            Var::R9   => 10,
            Var::R10  => 11,
        }
    }

    /// Human-readable name.
    #[inline]
    pub fn name(self) -> &'static str {
        match self {
            Var::Zero => "0",
            Var::R0   => "r0",
            Var::R1   => "r1",
            Var::R2   => "r2",
            Var::R3   => "r3",
            Var::R4   => "r4",
            Var::R5   => "r5",
            Var::R6   => "r6",
            Var::R7   => "r7",
            Var::R8   => "r8",
            Var::R9   => "r9",
            Var::R10  => "r10",
        }
    }
}

/// Simple wrapper so you can pass around an env if you want to extend later.
#[derive(Debug)]
pub struct VarEnv;

impl VarEnv {
    pub fn len(&self) -> usize {
        Var::ALL.len()
    }

    pub fn name(&self, v: Var) -> &'static str {
        v.name()
    }

    pub fn all(&self) -> &'static [Var] {
        &Var::ALL
    }

    pub fn index(&self, v: Var) -> usize {
        v.idx()
    }

    pub fn var_of_index(&self, idx: usize) -> Var {
        self.all()[idx]
    }
}

/// Global env you can use anywhere without initializing in `main`.
pub static VAR_ENV: VarEnv = VarEnv;

/// --- analysis helpers ---
/// 
// Extract bounds if finite.
// ub from: x - 0 <= ub
// lb from: 0 - x <= -lb  => lb = - (0 - x bound)
pub fn get_bounds(dbm: &Dbm, x: Var, zero: Var) -> (Option<i64>, Option<i64>) {
    let ub = dbm.get(x, zero);
    let lb_neg = dbm.get(zero, x);

    let ub_opt = if ub >= INF { None } else { Some(ub) };
    let lb_opt = if lb_neg >= INF { None } else { Some(-lb_neg) };

    (lb_opt, ub_opt)
}

// If both bounds exist and match, x is provably constant.
pub fn get_const(dbm: &Dbm, x: Var, zero: Var) -> Option<i64> {
    let (lb, ub) = get_bounds(dbm, x, zero);
    match (lb, ub) {
        (Some(l), Some(u)) if l == u => Some(l),
        _ => None,
    }
}

// --- transfer functions ---
// exec.rs wants a uniform name.
pub fn forget(dbm: &mut Dbm, x: Var) {
    dbm.forget_var(x);
    dbm.close(); // keep the "always closed" invariant
}

// dst += imm
pub fn assign_add_imm(dbm: &mut Dbm, dst: Var, imm: i64) {
    add_imm(dbm, dst, imm); // your add_imm already closes
}

// dst += src
pub fn assign_add_reg(dbm: &mut Dbm, dst: Var, src: Var, zero: Var) {
    // dst := dst + src  (sound interval-style update)
    let (ld, ud) = get_bounds(dbm, dst, zero);
    let (ls, us) = get_bounds(dbm, src, zero);

    dbm.forget_var(dst);

    if let (Some(ld), Some(ls)) = (ld, ls) {
        assume_ge_const(dbm, dst, zero, ld + ls); // closes
    }
    if let (Some(ud), Some(us)) = (ud, us) {
        assume_le_const(dbm, dst, zero, ud + us); // closes
    }

    // If neither bound exists, dst becomes unconstrained; still close to keep invariant.
    dbm.close();
}

// dst &= mask
pub fn assign_and_mask(dbm: &mut Dbm, dst: Var, mask: i64, zero: Var) {
    dbm.forget_var(dst);

    // 0 <= dst <= mask
    dbm.add_constraint(dst, zero, mask);
    dbm.add_constraint(zero, dst, 0);

    dbm.close();
}

// x <= y  encoded as: x - y <= 0
pub fn assume_le_var(dbm: &mut Dbm, x: Var, y: Var) {
    dbm.add_constraint(x, y, 0);
    dbm.close();
}

// x >= y  encoded as: y - x <= 0
pub fn assume_ge_var(dbm: &mut Dbm, x: Var, y: Var) {
    dbm.add_constraint(y, x, 0);
    dbm.close();
}

// x > y  encoded as: y - x <= -1
pub fn assume_gt_var(dbm: &mut Dbm, x: Var, y: Var) {
    dbm.add_constraint(y, x, -1);
    dbm.close();
}

// x <= y + c  encoded as: x - y <= c
pub fn assume_le_var_plus_const(dbm: &mut Dbm, x: Var, y: Var, c: i64) {
    dbm.add_constraint(x, y, c);
    dbm.close();
}

pub fn assign_zero(d: &mut Dbm, x: Var, zero: Var) {
    d.add_constraint(x, zero, 0);
    d.add_constraint(zero, x, 0);
    d.close();
}

pub fn assign_eq(d: &mut Dbm, x: Var, y: Var) {
    d.forget_var(x);
    d.add_constraint(x, y, 0);
    d.add_constraint(y, x, 0);
    d.close();
}

// x <= c   encoded as: x - 0 <= c
pub fn assume_le_const(dbm: &mut Dbm, x: Var, zero: Var, c: i64) {
    dbm.add_constraint(x, zero, c);
    dbm.close();
}

// x >= c   encoded as: 0 - x <= -c
pub fn assume_ge_const(dbm: &mut Dbm, x: Var, zero: Var, c: i64) {
    dbm.add_constraint(zero, x, -c);
    dbm.close();
}

// x == c   encoded as: x <= c AND x >= c
pub fn assume_eq_const(dbm: &mut Dbm, x: Var, zero: Var, c: i64) {
    dbm.add_constraint(x, zero, c);
    dbm.add_constraint(zero, x, -c);
    dbm.close();
}

pub fn assume_less_than(d: &mut Dbm, x: Var, zero: Var, c: i64) {
    let bound = c - 1;
    d.add_constraint(x, zero, bound);
    d.close();
}

pub fn add_imm(d: &mut Dbm, x: Var, c: i64) {
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
pub fn assign_mul_imm(dbm: &mut Dbm, dst: Var, imm: i64, zero: Var) {
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
        assume_ge_const(dbm, dst, zero, new_lb);
    }
    if let Some(ud) = ud_opt {
        let new_ub = ud.saturating_mul(imm);
        assume_le_const(dbm, dst, zero, new_ub);
    }

    // If we had no bounds, dst just becomes unconstrained.
    dbm.close();
}

