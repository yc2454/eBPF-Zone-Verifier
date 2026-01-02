// src/domain.rs
use crate::Dbm;
use crate::dbm::INF;
use crate::ctx_model::MemRegionId;

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
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum RegType {
    NotInit,        // NOT_INIT
    ScalarValue,    // SCALAR_VALUE
    PtrToCtx,       // PTR_TO_CTX
    PtrToStack,     // PTR_TO_STACK
    PtrToMapValue,  // PTR_TO_MAP_VALUE
    PtrToMapKey,    // PTR_TO_MAP_KEY
    PtrToPacket { id: u32, range: u64 },    // PTR_TO_PACKET
    PtrToPacketMeta,// PTR_TO_PACKET_META
    PtrToPacketEnd, // PTR_TO_PACKET_END
    PtrToMem { region: MemRegionId },       // PTR_TO_MEM
    Unknown,        // our "top" / fallback for now
    // later: PtrToSocket, PtrToBtfId, PtrToBuf, etc.
}

impl Default for RegType {
    fn default() -> Self {
        RegType::NotInit
    }
}

impl RegType {
    pub fn is_pointer(self) -> bool {
        use RegType::*;
        matches!(
            self,
            PtrToCtx
                | PtrToStack
                | PtrToMapValue
                | PtrToMapKey
                | PtrToPacket { .. }
                | PtrToPacketMeta
                | PtrToPacketEnd
                | PtrToMem { .. }
        )
    }
}

pub const NUM_REGS: usize = 11; // number of RegType variants

/// We track types for actual R0..R10; Reg::Zero is not a real reg.
pub type RegTypes = [RegType; NUM_REGS];

#[derive(Copy, Clone, Debug)]
pub struct RegTypeState {
    pub regs: RegTypes,
}

impl RegTypeState {
    pub fn new_not_init() -> Self {
        Self {
            regs: [RegType::NotInit; NUM_REGS],
        }
    }

    pub fn get(&self, r: Reg) -> RegType {
        if let Some(i) = reg_to_index(r) {
            self.regs[i]
        } else {
            RegType::NotInit // or panic? Zero has no type
        }
    }

    pub fn set(&mut self, r: Reg, ty: RegType) {
        if let Some(i) = reg_to_index(r) {
            self.regs[i] = ty;
        }
    }

    /// Join in-place with `other`. Returns true if anything changed.
    /// A simple lattice join: if equal, keep; else go to Unknown.
    pub fn join_in_place(&mut self, other: &RegTypeState) -> bool {
        let mut changed = false;
        for i in 0..NUM_REGS {
            let before = self.regs[i];
            let after = join_reg_type(before, other.regs[i]);
            if after != before {
                self.regs[i] = after;
                changed = true;
            }
        }
        changed
    }

    pub fn iter_regs(&self) -> impl Iterator<Item = (Reg, RegType)> + '_ {
        Reg::ALL.iter().filter_map(|&r| {
            if let Some(i) = reg_to_index(r) {
                Some((r, self.regs[i]))
            } else {
                None
            }
        })
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

pub fn join_reg_type(a: RegType, b: RegType) -> RegType {
    use RegType::*;
    if a == b { return a; }

    match (a, b) {
        (NotInit, t) | (t, NotInit) => t,
        (Unknown, _t) | (_t, Unknown) => Unknown, // top
        // Scalar vs pointer kind: for now go to Unknown (lossy but safe)
        (ScalarValue, _) | (_, ScalarValue) => Unknown,
        (PtrToPacket { id: i1, range: r1 }, PtrToPacket { id: i2, range: r2 }) if i1 == i2 => {
            PtrToPacket { id: i1, range: r1.min(r2) }
        }
        // Different pointer flavors: also Unknown for now
        _ => Unknown,
    }
}

pub fn new_packet_id() -> u32 {
    use std::sync::atomic::{AtomicU32, Ordering};
    static PACKET_ID_COUNTER: AtomicU32 = AtomicU32::new(1); // start from 1
    PACKET_ID_COUNTER.fetch_add(1, Ordering::SeqCst)
}

/// Simple wrapper so you can pass around an env if you want to extend later.
#[derive(Debug)]
pub struct RegEnv;

impl RegEnv {
    pub fn len(&self) -> usize {
        Reg::ALL.len()
    }

    pub fn name(&self, v: Reg) -> &'static str {
        v.name()
    }

    pub fn all(&self) -> &'static [Reg] {
        &Reg::ALL
    }

    pub fn index(&self, v: Reg) -> usize {
        v.idx()
    }

    pub fn var_of_index(&self, idx: usize) -> Reg {
        self.all()[idx]
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
        assume_ge_const(dbm, dst, zero, ld + ls); // closes
    }
    if let (Some(ud), Some(us)) = (ud, us) {
        assume_le_const(dbm, dst, zero, ud + us); // closes
    }

    // If neither bound exists, dst becomes unconstrained; still close to keep invariant.
    dbm.close();
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
pub fn assume_le_const(dbm: &mut Dbm, x: Reg, zero: Reg, c: i64) {
    dbm.add_constraint(x, zero, c);
    dbm.close();
}

// x >= c   encoded as: 0 - x <= -c
pub fn assume_ge_const(dbm: &mut Dbm, x: Reg, zero: Reg, c: i64) {
    dbm.add_constraint(zero, x, -c);
    dbm.close();
}

// x == c   encoded as: x <= c AND x >= c
pub fn assume_eq_const(dbm: &mut Dbm, x: Reg, zero: Reg, c: i64) {
    dbm.add_constraint(x, zero, c);
    dbm.add_constraint(zero, x, -c);
    dbm.close();
}

pub fn assume_less_than(d: &mut Dbm, x: Reg, zero: Reg, c: i64) {
    let bound = c - 1;
    d.add_constraint(x, zero, bound);
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
        assume_ge_const(dbm, dst, zero, new_lb);
    }
    if let Some(ud) = ud_opt {
        let new_ub = ud.saturating_mul(imm);
        assume_le_const(dbm, dst, zero, new_ub);
    }

    // If we had no bounds, dst just becomes unconstrained.
    dbm.close();
}

