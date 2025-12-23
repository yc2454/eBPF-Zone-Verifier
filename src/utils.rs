use crate::dbm::{Dbm, INF};

pub const INF_GUARD_BAND: i64 = 1 << 40;

#[inline]
pub fn is_infinite(v: i64) -> bool {
    v >= INF - INF_GUARD_BAND
}

#[inline]
pub fn clamp_to_inf(v: i64) -> i64 {
    if is_infinite(v) { INF } else { v }
}

#[inline]
pub fn clamped_add(a: i64, b: i64) -> i64 {
    if is_infinite(a) || is_infinite(b) {
        INF
    } else {
        clamp_to_inf(a + b)
    }
}

#[inline]
pub fn clamped_add3(a: i64, b: i64, c: i64) -> i64 {
    if is_infinite(a) || is_infinite(b) || is_infinite(c) {
        INF
    } else {
        clamp_to_inf(a + b + c)
    }
}

pub fn canonicalize_infinity(dbm: &mut Dbm) {
    let n = dbm.dim();
    for i in 0..n {
        for j in 0..n {
            let v = dbm.raw(i, j);
            dbm.set_raw(i, j, clamp_to_inf(v));
        }
    }
}

pub fn dbm_is_inconsistent(dbm: &Dbm) -> bool {
    let n = dbm.dim();
    for i in 0..n {
        if dbm.raw(i, i) < 0 {
            return true;
        }
    }
    false
}

pub fn dbm_equals(a: &Dbm, b: &Dbm) -> bool {
    if a.num_vars() != b.num_vars() {
        return false;
    }
    for i in 0..a.num_vars() {
        for j in 0..a.num_vars() {
            if a.get_idx(i, j) != b.get_idx(i, j) {
                return false;
            }
        }
    }
    true
}
