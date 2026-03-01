// src/dbm.rs
use crate::analysis::machine::reg::{REG_ENV, Reg};
use log::debug;

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dbm {
    pub data: Vec<Vec<i64>>,
}

impl Dbm {
    pub fn new() -> Self {
        let n = Reg::DBM_DIM;
        let mut data = vec![vec![INF; n]; n];
        for (i, row) in data.iter_mut().enumerate() {
            row[i] = 0;
        }
        Self { data }
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

    #[allow(dead_code)]
    pub fn dump_matrix(&self) {
        use std::fmt::Write;
        let vars = REG_ENV.all();
        let n = vars.len();

        let mut output = String::new();
        writeln!(output, "DBM [{} x {}]:", n, n).unwrap();

        // header
        write!(output, "{:>8} ", "").unwrap();
        for v in vars {
            write!(output, "{:>12} ", v.name()).unwrap();
        }
        writeln!(output).unwrap();

        for (row_idx, vi) in vars.iter().enumerate() {
            write!(output, "{:>8} ", vi.name()).unwrap();
            for (col_idx, _vj) in vars.iter().enumerate() {
                let v = self.data[row_idx][col_idx];
                if v >= INF {
                    write!(output, "{:>12} ", "INF").unwrap();
                } else {
                    write!(output, "{:>12} ", v).unwrap();
                }
            }
            writeln!(output).unwrap();
        }

        debug!("{}", output);
    }

    #[allow(dead_code)]
    pub fn dump_matrix_full(&self) {
        use std::fmt::Write;
        let n = self.num_vars();
        let mut output = String::new();
        writeln!(output, "DBM [{} x {}] (full, with anchors):", n, n).unwrap();

        // header
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

        debug!("{}", output);
    }

    pub fn pretty_print(&self) {
        use std::fmt::Write;
        let zero = Reg::Zero;
        let mut output = String::new();
        writeln!(output, "  Bounds:").unwrap();
        for i in 0..self.dim() {
            let Some(i) = Reg::idx_to_reg(i) else {
                continue;
            };
            if i == zero || i.is_anchor() {
                continue;
            }

            let ub = self.get(i, zero); // x - 0 ≤ ub  →  x ≤ ub
            let lb_neg = self.get(zero, i); // 0 - x ≤ lb_neg  →  x ≥ -lb_neg

            // let min_str = if lb_neg >= INF { "-INF".to_string() } else { format!("{:#x}", -lb_neg) };
            // let max_str = if ub >= INF { "+INF".to_string() } else { format!("{:#x}", ub) };
            let min_str = if lb_neg >= INF {
                "-INF".to_string()
            } else {
                (-lb_neg).to_string()
            };
            let max_str = if ub >= INF {
                "+INF".to_string()
            } else {
                ub.to_string()
            };

            if min_str != "-INF" || max_str != "+INF" {
                writeln!(output, "    {}: [{}, {}]", i.name(), min_str, max_str).unwrap();
            }

            for j in 1..self.dim() {
                let Some(j) = Reg::idx_to_reg(j) else {
                    continue;
                };
                if j == zero || j == i {
                    continue;
                }

                let val = self.get(i, j);
                // let diff_str = if val >= INF || val <= -INF { "INF".to_string() } else { format!("{:#x}", val) };
                let diff_str = if val >= INF || val <= -INF {
                    "INF".to_string()
                } else {
                    val.to_string()
                };
                if diff_str != "INF" {
                    writeln!(output, "    {} - {} <= {}", i.name(), j.name(), diff_str).unwrap();
                }
            }
        }
        let anchors = [Reg::AnchorDataMeta, Reg::AnchorData, Reg::AnchorDataEnd];

        let mut has_anchor_info = false;
        for i in 0..self.dim() {
            let Some(reg) = Reg::idx_to_reg(i) else {
                continue;
            };
            if reg == Reg::Zero {
                continue;
            }

            for &anchor in &anchors {
                let reg_minus_anchor = self.get(reg, anchor);
                let anchor_minus_reg = self.get(anchor, reg);

                if reg_minus_anchor < INF || anchor_minus_reg < INF {
                    if !has_anchor_info {
                        writeln!(output, "  Anchor offsets:").unwrap();
                        has_anchor_info = true;
                    }
                    if reg_minus_anchor < INF && anchor_minus_reg < INF {
                        // exact or range: -anchor_minus_reg <= reg - anchor <= reg_minus_anchor
                        let lo = -anchor_minus_reg;
                        let hi = reg_minus_anchor;
                        if lo == hi {
                            writeln!(output, "    {} - {} == {}", reg.name(), anchor.name(), lo)
                                .unwrap();
                        } else {
                            writeln!(
                                output,
                                "    {} - {} in [{}, {}]",
                                reg.name(),
                                anchor.name(),
                                lo,
                                hi
                            )
                            .unwrap();
                        }
                    } else if reg_minus_anchor < INF {
                        writeln!(
                            output,
                            "    {} - {} <= {}",
                            reg.name(),
                            anchor.name(),
                            reg_minus_anchor
                        )
                        .unwrap();
                    } else {
                        writeln!(
                            output,
                            "    {} - {} >= {}",
                            reg.name(),
                            anchor.name(),
                            -anchor_minus_reg
                        )
                        .unwrap();
                    }
                }
            }
        }
        debug!("{}", output);
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
        }
        result
    }
}

impl Default for Dbm {
    fn default() -> Self {
        Self::new()
    }
}
