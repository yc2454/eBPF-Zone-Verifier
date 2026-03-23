// src/dbm.rs
use crate::analysis::machine::reg::{REG_ENV, Reg};

pub const INF: i64 = i64::MAX / 4;

// Bounds for finite constraints inside the DBM.
// We never store anything > POS_BOUND or < NEG_BOUND.
const POS_BOUND: i64 = INF / 2;
const NEG_BOUND: i64 = -POS_BOUND;

#[inline]
pub fn clamp_upper_bound(c: i64) -> i64 {
    // We represent "no constraint" as INF.
    // For x - y <= c with huge positive c, we can treat it as no constraint.
    if c > POS_BOUND {
        INF
    } else if c < NEG_BOUND {
        // Very strong negative bound; weaken to NEG_BOUND
        NEG_BOUND
    } else {
        c
    }
}

#[inline]
pub fn clamped_add(a: i64, b: i64) -> i64 {
    // Safe addition for Floyd–Warshall.
    // If either side is INF, or the sum overflows, treat as INF (no useful bound).
    if a >= INF || b >= INF {
        return INF;
    }
    match a.checked_add(b) {
        Some(sum) => clamp_upper_bound(sum),
        None => INF,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Bounds {
    pub s32_min: i32,
    pub s32_max: i32,
    pub u32_min: u32,
    pub u32_max: u32,
    pub s64_min: i64,
    pub s64_max: i64,
    pub u64_min: u64,
    pub u64_max: u64,
}

impl Bounds {
    pub fn unknown() -> Self {
        Self {
            s32_min: i32::MIN,
            s32_max: i32::MAX,
            u32_min: 0,
            u32_max: u32::MAX,
            s64_min: i64::MIN,
            s64_max: i64::MAX,
            u64_min: 0,
            u64_max: u64::MAX,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dbm {
    pub data: Vec<Vec<i64>>,
    pub bounds: Vec<Bounds>,
}

impl Dbm {
    pub fn new() -> Self {
        let n = Reg::DBM_DIM;
        let mut data = vec![vec![INF; n]; n];
        for (i, row) in data.iter_mut().enumerate() {
            row[i] = 0;
        }
        Self {
            data,
            bounds: vec![Bounds::unknown(); n],
        }
    }

    pub fn num_vars(&self) -> usize {
        self.data.len()
    }

    pub fn dim(&self) -> usize {
        self.data.len()
    }

    pub fn raw(&self, i: usize, j: usize) -> i64 {
        self.data[i][j]
    }

    // low-level idx ops if you need them
    pub fn get_idx(&self, i: usize, j: usize) -> i64 {
        self.data[i][j]
    }

    pub fn set_idx(&mut self, i: usize, j: usize, val: i64) {
        self.data[i][j] = val;
    }

    // Var-level helpers
    #[inline]
    pub fn get(&self, i: Reg, j: Reg) -> i64 {
        self.data[i.idx()][j.idx()]
    }

    #[inline]
    pub fn set(&mut self, i: Reg, j: Reg, val: i64) {
        self.data[i.idx()][j.idx()] = val;
    }

    pub fn add_constraint(&mut self, i: Reg, j: Reg, c: i64) {
        // Constraint: i - j <= c
        let c = clamp_upper_bound(c);
        let old = self.get(i, j);

        // If c becomes INF, it's "no constraint". Only tighten if we had a finite bound before.
        if c == INF {
            return;
        }
        if c < old {
            self.set(i, j, c);
        }
    }

    pub fn forget_var(&mut self, x: Reg) {
        debug_assert!(!x.is_anchor(), "BUG: cannot forget anchor {:?}", x);
        let i = x.idx();
        let n = self.num_vars();
        for j in 0..n {
            if i == j {
                self.data[i][j] = 0;
            } else {
                self.data[i][j] = INF;
            }
        }
        for k in 0..n {
            if k == i {
                self.data[k][i] = 0;
            } else {
                self.data[k][i] = INF;
            }
        }
        self.bounds[i] = Bounds::unknown();
    }

    pub fn close(&mut self) {
        let n = self.num_vars();
        for k in 0..n {
            for i in 0..n {
                let dik = self.data[i][k];
                if dik >= INF {
                    continue;
                }
                for j in 0..n {
                    let dkj = self.data[k][j];
                    if dkj >= INF {
                        continue;
                    }

                    let via = clamped_add(dik, dkj);
                    if via < self.data[i][j] {
                        self.data[i][j] = via;
                    }
                }
            }
        }
    }

    pub fn is_inconsistent(&self) -> bool {
        for i in 0..self.num_vars() {
            if self.data[i][i] < 0 {
                return true;
            }
        }
        false
    }

    /// Returns the DBM as a formatted matrix string (real registers only, no anchors).
    /// The caller is responsible for logging the result at the desired level.
    #[allow(dead_code)]
    pub fn matrix_str(&self) -> String {
        use std::fmt::Write;
        let vars = REG_ENV.all();
        let n = vars.len();

        let mut output = String::new();
        writeln!(output, "DBM [{} x {}]:", n, n).unwrap();

        write!(output, "{:>8} ", "").unwrap();
        for v in vars {
            write!(output, "{:>12} ", v.name()).unwrap();
        }
        writeln!(output).unwrap();

        for (row_idx, vi) in vars.iter().enumerate() {
            write!(output, "{:>8} ", vi.name()).unwrap();
            for col_idx in 0..n {
                let v = self.data[row_idx][col_idx];
                if v >= INF {
                    write!(output, "{:>12} ", "INF").unwrap();
                } else {
                    write!(output, "{:>12} ", v).unwrap();
                }
            }
            writeln!(output).unwrap();
        }

        output
    }

    /// Returns the full DBM as a formatted matrix string (all registers including anchors).
    /// The caller is responsible for logging the result at the desired level.
    pub fn matrix_full_str(&self) -> String {
        use std::fmt::Write;
        let n = self.num_vars();
        let mut output = String::new();
        writeln!(output, "DBM [{} x {}] (full, with anchors):", n, n).unwrap();

        write!(output, "{:>12} ", "").unwrap();
        for j in 0..n {
            let name = Reg::idx_to_reg(j).map(|r| r.name()).unwrap_or("???");
            write!(output, "{:>12} ", name).unwrap();
        }
        writeln!(output).unwrap();

        for i in 0..n {
            let name = Reg::idx_to_reg(i).map(|r| r.name()).unwrap_or("???");
            write!(output, "{:>12} ", name).unwrap();
            for j in 0..n {
                let v = self.data[i][j];
                if v >= INF {
                    write!(output, "{:>12} ", "INF").unwrap();
                } else {
                    write!(output, "{:>12} ", v).unwrap();
                }
            }
            writeln!(output).unwrap();
        }

        output
    }

    /// Returns a compact, single-line string of non-trivial relational constraints
    /// suitable for embedding in a log line.
    ///
    /// Only register-register and register-anchor pairs are shown (pairs involving
    /// `Zero` encode absolute bounds and are already covered by the Ranges section).
    /// Each unique unordered pair `{ri, rj}` is emitted once (ri.idx() < rj.idx()),
    /// so symmetric entries are collapsed:
    ///
    ///   `ri-rj=={k}`          when both sides pin to the same value
    ///   `ri-rj in [lo,hi]`    when both sides are finite
    ///   `ri-rj<={hi}`         upper bound only
    ///   `ri-rj>={lo}`         lower bound only
    pub fn relations_str(&self) -> String {
        let n = self.dim();

        // Collect all non-Zero registers in index order (real regs + anchors).
        let regs: Vec<Reg> = (0..n)
            .filter_map(Reg::idx_to_reg)
            .filter(|r| *r != Reg::Zero)
            .collect();

        let mut parts: Vec<String> = Vec::new();

        for (a, &ri) in regs.iter().enumerate() {
            for &rj in &regs[a + 1..] {
                // c_ij: ri - rj <= c_ij
                // c_ji: rj - ri <= c_ji  (=> ri - rj >= -c_ji)
                let c_ij = self.get(ri, rj);
                let c_ji = self.get(rj, ri);

                if c_ij >= INF && c_ji >= INF {
                    continue; // no constraint between this pair
                }

                let hi = if c_ij >= INF { None } else { Some(c_ij) };
                let lo = if c_ji >= INF { None } else { Some(-c_ji) };

                let s = match (lo, hi) {
                    (Some(lo), Some(hi)) if lo == hi => {
                        format!("{}-{}=={}", ri.name(), rj.name(), lo)
                    }
                    (Some(lo), Some(hi)) => {
                        format!("{}-{} in [{},{}]", ri.name(), rj.name(), lo, hi)
                    }
                    (None, Some(hi)) => {
                        format!("{}-{}<={}", ri.name(), rj.name(), hi)
                    }
                    (Some(lo), None) => {
                        format!("{}-{}>={}", ri.name(), rj.name(), lo)
                    }
                    _ => continue,
                };
                parts.push(s);
            }
        }

        parts.join("  ")
    }

    /// Standard DBM widening: entries that loosen become INF.
    /// Guarantees convergence since each step can only introduce INF entries.
    pub fn widen(&self, newer: &Dbm) -> Dbm {
        let n = self.num_vars();
        let mut result = self.clone();
        for i in 0..n {
            for j in 0..n {
                if newer.data[i][j] > self.data[i][j] {
                    result.data[i][j] = INF;
                }
                // If newer <= self, keep self (stable/tightening)
            }
            let b1 = &self.bounds[i];
            let b2 = &newer.bounds[i];
            result.bounds[i].s32_min = if b2.s32_min < b1.s32_min {
                i32::MIN
            } else {
                b1.s32_min
            };
            result.bounds[i].s32_max = if b2.s32_max > b1.s32_max {
                i32::MAX
            } else {
                b1.s32_max
            };
            result.bounds[i].u32_min = if b2.u32_min < b1.u32_min {
                0
            } else {
                b1.u32_min
            };
            result.bounds[i].u32_max = if b2.u32_max > b1.u32_max {
                u32::MAX
            } else {
                b1.u32_max
            };
            result.bounds[i].s64_min = if b2.s64_min < b1.s64_min {
                i64::MIN
            } else {
                b1.s64_min
            };
            result.bounds[i].s64_max = if b2.s64_max > b1.s64_max {
                i64::MAX
            } else {
                b1.s64_max
            };
            result.bounds[i].u64_min = if b2.u64_min < b1.u64_min {
                0
            } else {
                b1.u64_min
            };
            result.bounds[i].u64_max = if b2.u64_max > b1.u64_max {
                u64::MAX
            } else {
                b1.u64_max
            };
        }
        result
    }

    /// Narrowing: intersect constraints from two DBMs.
    /// Takes the tighter (smaller) constraint for each entry.
    /// Used after widening to recover precision from the actual loop state.
    #[allow(dead_code)]
    pub fn narrow(&self, other: &Dbm) -> Dbm {
        let n = self.num_vars();
        let mut result = self.clone();
        for i in 0..n {
            for j in 0..n {
                // Take the tighter constraint (smaller value = tighter bound)
                result.data[i][j] = self.data[i][j].min(other.data[i][j]);
            }
            let b1 = &self.bounds[i];
            let b2 = &other.bounds[i];
            result.bounds[i].s32_min = b1.s32_min.max(b2.s32_min);
            result.bounds[i].s32_max = b1.s32_max.min(b2.s32_max);
            result.bounds[i].u32_min = b1.u32_min.max(b2.u32_min);
            result.bounds[i].u32_max = b1.u32_max.min(b2.u32_max);
            result.bounds[i].s64_min = b1.s64_min.max(b2.s64_min);
            result.bounds[i].s64_max = b1.s64_max.min(b2.s64_max);
            result.bounds[i].u64_min = b1.u64_min.max(b2.u64_min);
            result.bounds[i].u64_max = b1.u64_max.min(b2.u64_max);
        }
        result
    }
}

impl Default for Dbm {
    fn default() -> Self {
        Self::new()
    }
}
