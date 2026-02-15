// src/analysis/machine/reg.rs

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Reg {
    Zero,
    R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10,
    // ── Phantom anchors (never appear in BPF instructions) ──
    AnchorDataMeta,
    AnchorData,
    AnchorDataEnd,
}

impl Reg {
    /// Only real registers — used by instruction dispatch, printing, iteration.
    pub const ALL: [Reg; 12] = [
        Reg::Zero,
        Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5,
        Reg::R6, Reg::R7, Reg::R8, Reg::R9, Reg::R10,
    ];

    /// Total DBM dimension (registers + anchors).
    pub const DBM_DIM: usize = 15;

    #[inline]
    pub fn idx(self) -> usize {
        match self {
            Reg::Zero => 0,
            Reg::R0   => 1,  Reg::R1  => 2,  Reg::R2  => 3,
            Reg::R3   => 4,  Reg::R4  => 5,  Reg::R5  => 6,
            Reg::R6   => 7,  Reg::R7  => 8,  Reg::R8  => 9,
            Reg::R9   => 10, Reg::R10 => 11,
            Reg::AnchorDataMeta => 12,
            Reg::AnchorData     => 13,
            Reg::AnchorDataEnd  => 14,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Reg::Zero => "0",
            Reg::R0  => "r0",  Reg::R1  => "r1",  Reg::R2  => "r2",
            Reg::R3  => "r3",  Reg::R4  => "r4",  Reg::R5  => "r5",
            Reg::R6  => "r6",  Reg::R7  => "r7",  Reg::R8  => "r8",
            Reg::R9  => "r9",  Reg::R10 => "r10",
            Reg::AnchorDataMeta => "@data_meta",
            Reg::AnchorData     => "@data",
            Reg::AnchorDataEnd  => "@data_end",
        }
    }

    pub fn idx_to_reg(idx: usize) -> Option<Reg> {
        match idx {
            0  => Some(Reg::Zero),
            1  => Some(Reg::R0),  2  => Some(Reg::R1),  3  => Some(Reg::R2),
            4  => Some(Reg::R3),  5  => Some(Reg::R4),  6  => Some(Reg::R5),
            7  => Some(Reg::R6),  8  => Some(Reg::R7),  9  => Some(Reg::R8),
            10 => Some(Reg::R9),  11 => Some(Reg::R10),
            12 => Some(Reg::AnchorDataMeta),
            13 => Some(Reg::AnchorData),
            14 => Some(Reg::AnchorDataEnd),
            _  => None,
        }
    }

    /// True for phantom anchors — these must never be forgotten or overwritten.
    #[inline]
    pub fn is_anchor(self) -> bool {
        matches!(self, Reg::AnchorDataMeta | Reg::AnchorData | Reg::AnchorDataEnd)
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
        _ => None,
    }
}

/// Simple wrapper so you can pass around an env if you want to extend later.
#[derive(Debug)]
pub struct RegEnv;

impl RegEnv {

    pub fn all(&self) -> &'static [Reg] {
        &Reg::ALL
    }

    pub fn index(&self, v: Reg) -> usize {
        v.idx()
    }

}

/// Global env you can use anywhere without initializing in `main`.
pub static REG_ENV: RegEnv = RegEnv;
