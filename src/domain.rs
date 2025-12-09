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
}

/// Global env you can use anywhere without initializing in `main`.
pub static VAR_ENV: VarEnv = VarEnv;

// --- transfer functions ---
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

pub fn assign_add_const(d: &mut Dbm, x: Var, y: Var, c: i64) {
    d.forget_var(x);
    d.add_constraint(x, y, c);     // x - y <= c
    d.add_constraint(y, x, -c);    // y - x <= -c
    d.close();
}

pub fn assume_less_than(d: &mut Dbm, x: Var, zero: Var, c: i64) {
    let bound = c - 1;
    d.add_constraint(x, zero, bound);
    d.close();
}

pub fn assume_ge_const(d: &mut Dbm, x: Var, zero: Var, c: i64) {
    d.add_constraint(zero, x, -c);
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
