// src/dbm.rs
use crate::domain::{Var, VAR_ENV};

pub const INF: i64 = i64::MAX / 4;

#[derive(Debug, Clone)]
pub struct Dbm {
    pub data: Vec<Vec<i64>>,
}

impl Dbm {
    pub fn new(num_vars: usize) -> Self {
        let mut data = vec![vec![INF; num_vars]; num_vars];
        for i in 0..num_vars {
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

    pub fn set_raw(&mut self, i: usize, j: usize, v: i64) {
        self.data[i][j] = v;
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
    pub fn get(&self, i: Var, j: Var) -> i64 {
        self.data[i.idx()][j.idx()]
    }

    #[inline]
    pub fn set(&mut self, i: Var, j: Var, val: i64) {
        self.data[i.idx()][j.idx()] = val;
    }

    pub fn add_constraint(&mut self, i: Var, j: Var, c: i64) {
        let old = self.get(i, j);
        if c < old {
            self.set(i, j, c);
        }
    }

    pub fn forget_var(&mut self, x: Var) {
        let i = x.idx();
        let n = self.num_vars();

        // reset row i
        for j in 0..n {
            if i == j {
                self.data[i][j] = 0;
            } else {
                self.data[i][j] = INF;
            }
        }

        // reset column i
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
                for j in 0..n {
                    let via = self.data[i][k].saturating_add(self.data[k][j]);
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

    pub fn var_bounds(&self, x: Var, zero: Var) -> Option<(i64, i64)> {
        let ub = self.get(x, zero);
        let lb_c = self.get(zero, x);

        if ub == INF && lb_c == INF {
            return None;
        }

        let ub_opt = if ub == INF { None } else { Some(ub) };
        let lb_opt = if lb_c == INF { None } else { Some(-lb_c) };

        match (lb_opt, ub_opt) {
            (Some(lb), Some(ub)) => Some((lb, ub)),
            (Some(lb), None)     => Some((lb, i64::MAX / 4)),
            (None, Some(ub))     => Some((i64::MIN / 4, ub)),
            (None, None)         => None,
        }
    }

    pub fn dump_matrix(&self) {
        let vars = VAR_ENV.all();
        let n = self.num_vars();

        // Sanity: only print as many vars as the matrix actually has
        assert_eq!(n, vars.len(), "DBM size and VAR_ENV length differ");

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
                if v >= INF / 2 {
                    print!("{:>8} ", "INF");
                } else {
                    print!("{:>8} ", v);
                }
            }
            println!();
        }

        println!();
    }

    // you still have join, etc., unchanged except using Var or idx as needed
    pub fn join(&self, other: &Dbm) -> Dbm {
        let n = self.num_vars();
        let mut res = Dbm::new(n);
        for i in 0..n {
            for j in 0..n {
                let a = self.data[i][j];
                let b = other.data[i][j];
                res.data[i][j] = if a > b { a } else { b };
            }
        }
        res.close();
        res
    }
}
