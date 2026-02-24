// src/analysis/transfer/alu/shift.rs

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{Operand, Width};
use crate::zone::domain::{
    apply_and_imm, assume_eq_imm, assume_ge_imm, assume_le_imm, forget, get_interval,
};
use crate::zone::tnum::Tnum;

use super::helpers::sync_tnum_to_dbm;

pub(crate) fn handle_shr(state: &mut State, width: Width, dst: Reg, src: &Operand) {
    match src {
        Operand::Imm(k) => {
            let k = *k as u32;
            let shift_amount = if width == Width::W32 {
                k & 0x1F
            } else {
                k & 0x3F
            };

            let (old_lo, old_hi) = get_interval(&state.dbm, dst);
            let old_tnum = state.get_tnum(dst);
            forget(&mut state.dbm, dst);

            if width == Width::W32 {
                let truncated_tnum = old_tnum.trunc32();
                let trunc_lo = truncated_tnum.min_value();
                let trunc_hi = truncated_tnum.max_value();

                let new_lo = (trunc_lo >> shift_amount) as i64;
                let new_hi = (trunc_hi >> shift_amount) as i64;

                assume_ge_imm(&mut state.dbm, dst, new_lo);
                assume_le_imm(&mut state.dbm, dst, new_hi);

                let new_tnum = truncated_tnum.shr_imm(shift_amount as u64);
                state.set_tnum(dst, new_tnum);
            } else {
                assume_ge_imm(&mut state.dbm, dst, 0);

                if old_lo != i64::MIN && old_hi != i64::MAX {
                    let (lo, hi) = (old_lo, old_hi);
                    if lo >= 0 {
                        let new_lo = (lo as u64 >> shift_amount) as i64;
                        let new_hi = (hi as u64 >> shift_amount) as i64;
                        assume_ge_imm(&mut state.dbm, dst, new_lo);
                        assume_le_imm(&mut state.dbm, dst, new_hi);
                    } else if shift_amount > 0 {
                        let max_result = u64::MAX >> shift_amount;
                        if max_result <= i64::MAX as u64 {
                            assume_le_imm(&mut state.dbm, dst, max_result as i64);
                        }
                    }
                }

                let new_tnum = old_tnum.shr_imm(shift_amount as u64);
                state.set_tnum(dst, new_tnum);
            }
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);
            assume_ge_imm(&mut state.dbm, dst, 0);

            if width == Width::W32 {
                assume_le_imm(&mut state.dbm, dst, u32::MAX as i64);
                state.set_tnum(dst, Tnum::u32_unknown());
            } else {
                state.set_tnum(dst, Tnum::unknown());
            }
        }
    }

    sync_tnum_to_dbm(state, dst);
}

pub(crate) fn handle_shl(state: &mut State, width: Width, dst: Reg, src: &Operand) {
    match src {
        Operand::Imm(k) => {
            let k = *k as u32;
            let shift_amount = if width == Width::W32 {
                k & 0x1F
            } else {
                k & 0x3F
            };

            let (old_lo, old_hi) = get_interval(&state.dbm, dst);
            let old_tnum = state.get_tnum(dst);
            forget(&mut state.dbm, dst);

            if width == Width::W32 {
                let truncated_tnum = old_tnum.trunc32();
                let trunc_lo = truncated_tnum.min_value();
                let trunc_hi = truncated_tnum.max_value();

                if shift_amount < 32 {
                    let max_safe = u32::MAX as u64 >> shift_amount;
                    if trunc_hi <= max_safe {
                        let new_lo = ((trunc_lo << shift_amount) & 0xFFFFFFFF) as i64;
                        let new_hi = ((trunc_hi << shift_amount) & 0xFFFFFFFF) as i64;
                        assume_ge_imm(&mut state.dbm, dst, new_lo);
                        assume_le_imm(&mut state.dbm, dst, new_hi);
                    } else {
                        assume_ge_imm(&mut state.dbm, dst, 0);
                        assume_le_imm(&mut state.dbm, dst, u32::MAX as i64);
                    }
                } else {
                    assume_eq_imm(&mut state.dbm, dst, 0);
                }

                let new_tnum = truncated_tnum.shl_imm(shift_amount as u64).trunc32();
                state.set_tnum(dst, new_tnum);
            } else {
                if shift_amount == 32 {
                    if old_lo != i64::MIN && old_hi != i64::MAX {
                        let (lo, hi) = (old_lo, old_hi);
                        if lo >= i32::MIN as i64 && hi <= i32::MAX as i64 {
                            assume_ge_imm(&mut state.dbm, dst, lo << 32);
                            assume_le_imm(&mut state.dbm, dst, hi << 32);
                        }
                    }
                } else if old_lo != i64::MIN && old_hi != i64::MAX {
                    let (lo, hi) = (old_lo, old_hi);
                    if lo >= 0 && shift_amount < 64 {
                        let max_safe: i64 = if shift_amount == 63 {
                            0
                        } else {
                            i64::MAX >> shift_amount
                        };
                        if hi <= max_safe {
                            assume_ge_imm(&mut state.dbm, dst, lo << shift_amount);
                            assume_le_imm(&mut state.dbm, dst, hi << shift_amount);
                        }
                    }
                }

                let new_tnum = old_tnum.shl_imm(shift_amount as u64);
                state.set_tnum(dst, new_tnum);
            }

            sync_tnum_to_dbm(state, dst);
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);

            if width == Width::W32 {
                assume_ge_imm(&mut state.dbm, dst, 0);
                assume_le_imm(&mut state.dbm, dst, u32::MAX as i64);
                state.set_tnum(dst, Tnum::u32_unknown());
            } else {
                state.set_tnum(dst, Tnum::unknown());
            }

            sync_tnum_to_dbm(state, dst);
        }
    }
}

pub(crate) fn handle_arsh(state: &mut State, width: Width, dst: Reg, src: &Operand) {
    match src {
        Operand::Imm(k) => {
            let k = *k as u32;
            let shift_amount = if width == Width::W32 {
                k & 0x1F
            } else {
                k & 0x3F
            };

            let old_tnum = state.get_tnum(dst);
            let (old_lo, old_hi) = get_interval(&state.dbm, dst);
            forget(&mut state.dbm, dst);

            if width == Width::W32 {
                let truncated_tnum = old_tnum.trunc32();
                let trunc_lo = truncated_tnum.min_value() as u32;
                let trunc_hi = truncated_tnum.max_value() as u32;

                let signed_lo = trunc_lo as i32;
                let signed_hi = trunc_hi as i32;

                if signed_lo <= signed_hi {
                    let new_lo = (signed_lo >> shift_amount) as u32 as i64;
                    let new_hi = (signed_hi >> shift_amount) as u32 as i64;
                    assume_ge_imm(&mut state.dbm, dst, new_lo);
                    assume_le_imm(&mut state.dbm, dst, new_hi);
                } else {
                    assume_ge_imm(&mut state.dbm, dst, 0);
                    assume_le_imm(&mut state.dbm, dst, u32::MAX as i64);
                }

                let sign_bit = (truncated_tnum.value >> 31) & 1;
                let sign_unknown = (truncated_tnum.mask >> 31) & 1;

                let mut sext_tnum = truncated_tnum;
                let upper_mask = 0xFFFFFFFF00000000;

                if sign_unknown != 0 {
                    sext_tnum.mask |= upper_mask;
                    sext_tnum.value &= !upper_mask;
                } else if sign_bit != 0 {
                    sext_tnum.value |= upper_mask;
                }

                let arsh_result = sext_tnum.arsh_imm(shift_amount as u64);
                let new_tnum = arsh_result.trunc32();
                state.set_tnum(dst, new_tnum);
            } else {
                if shift_amount == 32 {
                    let lower_32_bits = 0xFFFFFFFF_u64;
                    let lower_known_zero = (old_tnum.mask & lower_32_bits) == 0
                        && (old_tnum.value & lower_32_bits) == 0;
                    if lower_known_zero {
                        let new_lo = if old_lo != i64::MIN {
                            (old_lo >> 32).max(i32::MIN as i64)
                        } else {
                            i32::MIN as i64
                        };
                        let new_hi = if old_hi != i64::MAX {
                            (old_hi >> 32).min(i32::MAX as i64)
                        } else {
                            i32::MAX as i64
                        };

                        assume_ge_imm(&mut state.dbm, dst, new_lo);
                        assume_le_imm(&mut state.dbm, dst, new_hi);

                        let new_tnum = old_tnum.arsh_imm(shift_amount as u64);
                        state.set_tnum(dst, new_tnum);
                        sync_tnum_to_dbm(state, dst);
                        return;
                    }
                }

                if old_lo != i64::MIN && old_hi != i64::MAX {
                    let (lo, hi) = (old_lo, old_hi);
                    let new_lo = lo >> shift_amount;
                    let new_hi = hi >> shift_amount;
                    assume_ge_imm(&mut state.dbm, dst, new_lo);
                    assume_le_imm(&mut state.dbm, dst, new_hi);
                }

                let new_tnum = old_tnum.arsh_imm(shift_amount as u64);
                state.set_tnum(dst, new_tnum);
            }

            sync_tnum_to_dbm(state, dst);
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);

            if width == Width::W32 {
                assume_ge_imm(&mut state.dbm, dst, i32::MIN as i64);
                assume_le_imm(&mut state.dbm, dst, i32::MAX as i64);
            }

            state.set_tnum(dst, Tnum::unknown());
            sync_tnum_to_dbm(state, dst);
        }
    }
}

pub(crate) fn handle_rsh(state: &mut State, width: Width, dst: Reg, src: &Operand) {
    match src {
        Operand::Imm(k) => {
            let k = *k as u32;
            let shift_amount = if width == Width::W32 {
                k & 0x1F
            } else {
                k & 0x3F
            };

            let (old_lo, old_hi) = get_interval(&state.dbm, dst);
            forget(&mut state.dbm, dst);

            if old_lo != i64::MIN && old_hi != i64::MAX {
                let (lo, hi) = (old_lo, old_hi);
                if lo >= 0 {
                    let new_lo = (lo as u64 >> shift_amount) as i64;
                    let new_hi = (hi as u64 >> shift_amount) as i64;
                    assume_ge_imm(&mut state.dbm, dst, new_lo);
                    assume_le_imm(&mut state.dbm, dst, new_hi);
                } else {
                    assume_ge_imm(&mut state.dbm, dst, 0);
                    if shift_amount > 0 {
                        assume_le_imm(&mut state.dbm, dst, (u64::MAX >> shift_amount) as i64);
                    }
                }
            }

            if width == Width::W32 {
                apply_and_imm(&mut state.dbm, dst, 0xFFFFFFFF);
            }

            let t = state.get_tnum(dst);
            let new_t = t.rsh_imm(shift_amount as u64);
            state.set_tnum(dst, new_t);
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);
            assume_ge_imm(&mut state.dbm, dst, 0);

            if width == Width::W32 {
                assume_le_imm(&mut state.dbm, dst, u32::MAX as i64);
                state.set_tnum(dst, Tnum::u32_unknown());
            } else {
                state.set_tnum(dst, Tnum::unknown());
            }
        }
    }

    sync_tnum_to_dbm(state, dst);
}
