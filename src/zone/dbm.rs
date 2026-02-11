// src/dbm.rs
use crate::zone::domain::{Reg, REG_ENV};
use crate::common::utils::{clamp_upper_bound, clamped_add};

pub const INF: i64 = i64::MAX / 4;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dbm {
    pub data: Vec<Vec<i64>>,
}

impl Dbm {
    pub fn new() -> Self {
        let n = Reg::DBM_DIM;
        let mut data = vec![vec![INF; n]; n];
        for i in 0..n {
            data[i][i] = 0;
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
            if i == j { self.data[i][j] = 0; }
            else      { self.data[i][j] = INF; }
        }
        for k in 0..n {
            if k == i { self.data[k][i] = 0; }
            else      { self.data[k][i] = INF; }
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

    pub fn dump_matrix(&self) {
        let vars = REG_ENV.all();
        let n = vars.len();

        println!("DBM [{} x {}]:", n, n);

        // header
        print!("{:>5} ", "");
        for v in vars {
            print!("{:>8} ", v.name());
        }
        println!();

        for (row_idx, vi) in vars.iter().enumerate() {
            print!("{:>5} ", vi.name());
            for (col_idx, _vj) in vars.iter().enumerate() {
                let v = self.data[row_idx][col_idx];
                if v >= INF {
                    print!("{:>8} ", "INF");
                } else {
                    print!("{:>8} ", v);
                }
            }
            println!();
        }

        println!();
    }

    pub fn dump_matrix_full(&self) {
        let n = self.num_vars();
        println!("DBM [{} x {}] (full, with anchors):", n, n);

        // header
        print!("{:>12} ", "");
        for j in 0..n {
            let name = Reg::idx_to_reg(j)
                .map(|r| r.name())
                .unwrap_or("???");
            print!("{:>12} ", name);
        }
        println!();

        for i in 0..n {
            let name = Reg::idx_to_reg(i)
                .map(|r| r.name())
                .unwrap_or("???");
            print!("{:>12} ", name);
            for j in 0..n {
                let v = self.data[i][j];
                if v >= INF {
                    print!("{:>12} ", "INF");
                } else {
                    print!("{:>12} ", v);
                }
            }
            println!();
        }
        println!();
    }

    pub fn pretty_print(&self) {
        let zero = Reg::Zero;
        println!("  Bounds:");
        for i in 0..self.dim() {
            let Some(i) = Reg::idx_to_reg(i) else { continue; };
            if i == zero || i.is_anchor() { continue; }
            
            let ub = self.get(i, zero);      // x - 0 ≤ ub  →  x ≤ ub
            let lb_neg = self.get(zero, i);  // 0 - x ≤ lb_neg  →  x ≥ -lb_neg
            
            // let min_str = if lb_neg >= INF { "-INF".to_string() } else { format!("{:#x}", -lb_neg) };
            // let max_str = if ub >= INF { "+INF".to_string() } else { format!("{:#x}", ub) };
            let min_str = if lb_neg >= INF { "-INF".to_string() } else { (-lb_neg).to_string() };
            let max_str = if ub >= INF { "+INF".to_string() } else { ub.to_string() };

            if min_str != "-INF" || max_str != "+INF" {
                println!("    {}: [{}, {}]", i.name(), min_str, max_str);
            }

            for j in 1..self.dim() {
                let Some(j) = Reg::idx_to_reg(j) else { continue; };
                if j == zero || j == i { continue; }
                
                let val = self.get(i, j);
                // let diff_str = if val >= INF || val <= -INF { "INF".to_string() } else { format!("{:#x}", val) };
                let diff_str = if val >= INF || val <= -INF { "INF".to_string() } else { val.to_string() };
                if diff_str != "INF" {
                    println!("    {} - {} <= {}", i.name(), j.name(), diff_str);
                }
            }
        }
        let anchors = [
            Reg::AnchorDataMeta,
            Reg::AnchorData,
            Reg::AnchorDataEnd,
        ];

        let mut has_anchor_info = false;
        for i in 0..self.dim() {
            let Some(reg) = Reg::idx_to_reg(i) else { continue };
            if reg == Reg::Zero || reg.is_anchor() { continue; }

            for &anchor in &anchors {
                let reg_minus_anchor = self.get(reg, anchor);
                let anchor_minus_reg = self.get(anchor, reg);

                if reg_minus_anchor < INF || anchor_minus_reg < INF {
                    if !has_anchor_info {
                        println!("  Anchor offsets:");
                        has_anchor_info = true;
                    }
                    if reg_minus_anchor < INF && anchor_minus_reg < INF {
                        // exact or range: -anchor_minus_reg <= reg - anchor <= reg_minus_anchor
                        let lo = -anchor_minus_reg;
                        let hi = reg_minus_anchor;
                        if lo == hi {
                            println!("    {} - {} == {}", reg.name(), anchor.name(), lo);
                        } else {
                            println!("    {} - {} in [{}, {}]", reg.name(), anchor.name(), lo, hi);
                        }
                    } else if reg_minus_anchor < INF {
                        println!("    {} - {} <= {}", reg.name(), anchor.name(), reg_minus_anchor);
                    } else {
                        println!("    {} - {} >= {}", reg.name(), anchor.name(), -anchor_minus_reg);
                    }
                }
            }
        }
    }
}
