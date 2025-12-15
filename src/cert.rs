// src/cert.rs
use std::io::{self, Read, Write};
use crate::dbm::{Dbm, INF};
use crate::domain::{Var, VAR_ENV};

pub struct Certificate {
    pub pcs: usize,
    pub dim: usize,
    pub states: Vec<Option<Dbm>>,
}

impl Certificate {
    pub fn from_states(states: Vec<Option<Dbm>>) -> Self {
        let pcs = states.len();
        let dim = VAR_ENV.len();
        Self { pcs, dim, states }
    }

    pub fn write_to<W: Write>(&self, mut w: W) -> io::Result<()> {
        writeln!(w, "{} {}", self.pcs, self.dim)?;
        for pc in 0..self.pcs {
            match &self.states[pc] {
                None => {
                    writeln!(w, "U")?;
                }
                Some(dbm) => {
                    writeln!(w, "R")?;
                    for i in 0..self.dim {
                        for j in 0..self.dim {
                            let v = dbm.raw(i, j);
                            if v >= INF {
                                write!(w, "INF ")?;
                            } else {
                                write!(w, "{} ", v)?;
                            }
                        }
                        writeln!(w)?;
                    }
                }
            }
        }
        Ok(())
    }

    pub fn read_from<R: Read>(mut r: R) -> io::Result<Self> {
        let mut s = String::new();
        r.read_to_string(&mut s)?;
        let mut it = s.split_whitespace();

        let pcs: usize = it.next().ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "pcs"))?.parse()
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "pcs parse"))?;
        let dim: usize = it.next().ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "dim"))?.parse()
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "dim parse"))?;

        let mut states: Vec<Option<Dbm>> = Vec::with_capacity(pcs);

        for _ in 0..pcs {
            let tag = it.next().ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "pc tag"))?;
            if tag == "U" {
                states.push(None);
            } else if tag == "R" {
                let mut dbm = Dbm::new(dim);
                for i in 0..dim {
                    for j in 0..dim {
                        let tok = it.next().ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "matrix token"))?;
                        let v = if tok == "INF" { INF } else {
                            tok.parse::<i32>().map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "int parse"))?
                        };
                        dbm.set_raw(i, j, v);
                    }
                }
                states.push(Some(dbm));
            } else {
                return Err(io::Error::new(io::ErrorKind::InvalidData, "bad tag"));
            }
        }

        Ok(Self { pcs, dim, states })
    }
}
