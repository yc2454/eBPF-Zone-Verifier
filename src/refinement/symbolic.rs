//! Symbolic state for BCF-style refinement.
//!
//! Mirrors the kernel's `struct bcf_state` plus per-register `bcf_expr`
//! tracking (kernel patches set1/0005–0011). During refinement, this state
//! captures the precise program state along the analysis suffix as a DAG of
//! [`BcfExpr`]s plus accumulated path conditions.
//!
//! This module provides the **primitive** state-manipulation API. Higher-level
//! transfer functions (the `bcf_alu` / `bcf_mov32` / `bcf_sx` analogues) and
//! site-specific refinement-condition formulators (`bcf_refine_access_bound`
//! analogues) live in sibling modules and call into these primitives.
//!
//! The "index" of an expression is its **u32 slot offset** from the start of
//! the expression table — identical to the on-disk BCF binary format. An
//! expression with `vlen = n` consumes `1 + n` slots (header + n args).

use super::bcf::*;

/// Number of BPF registers (R0–R10).
pub const NUM_REGS: usize = 11;

/// Symbolic-tracking state accumulated during BCF refinement.
#[derive(Debug, Clone, Default)]
pub struct SymbolicState {
    /// Expression DAG in declaration order.
    pub exprs: Vec<BcfExpr>,
    /// Total u32 slot count consumed by `exprs` (cached for O(1) `next_idx`).
    next_slot: u32,
    /// Per-register expression index (`None` until materialized).
    pub reg_expr: [Option<u32>; NUM_REGS],
    /// Path-condition predicates (each a u32 idx into `exprs`).
    pub path_conds: Vec<u32>,
    /// Final refinement condition (set by a site-specific callback).
    pub refine_cond: Option<u32>,
}

impl SymbolicState {
    pub fn new() -> Self {
        Self::default()
    }

    /// Append an expression and return its slot offset.
    pub fn push_expr(&mut self, e: BcfExpr) -> u32 {
        let idx = self.next_slot;
        self.next_slot += e.slot_len();
        self.exprs.push(e);
        idx
    }

    // ---------- value-level builders ----------

    /// Fresh symbolic bitvector variable of `sz` bits.
    pub fn add_var(&mut self, sz: u16) -> u32 {
        self.push_expr(bv_var(sz))
    }
    /// 32-bit constant.
    pub fn add_val32(&mut self, v: u32) -> u32 {
        self.push_expr(bv_val32(v))
    }
    /// 64-bit constant.
    pub fn add_val64(&mut self, v: u64) -> u32 {
        self.push_expr(bv_val64(v))
    }
    /// Binary BV ALU expression at `bits` bitwidth.
    pub fn add_alu(&mut self, op: u8, a: u32, b: u32, bits: u16) -> u32 {
        self.push_expr(bv_alu(op, a, b, bits))
    }
    /// Binary BV predicate (comparison). Result type is Bool.
    pub fn add_pred(&mut self, op: u8, a: u32, b: u32) -> u32 {
        self.push_expr(bv_pred(op, a, b))
    }
    /// Conjunction of boolean preds (≥ 2 args).
    pub fn add_conj(&mut self, args: Vec<u32>) -> u32 {
        self.push_expr(pred_conj(args))
    }
    /// Disjunction of boolean preds (≥ 2 args).
    pub fn add_disj(&mut self, args: Vec<u32>) -> u32 {
        self.push_expr(pred_disj(args))
    }

    /// Zero-extend a 32-bit value to 64 bits.
    /// `params = (ext_len << 8) | result_width`. ext_len=32 zero bits added,
    /// result_width=64 (the operand was 32-bit, result is 64-bit).
    pub fn zext_32_to_64(&mut self, arg: u32) -> u32 {
        self.push_expr(BcfExpr {
            code: BCF_ZERO_EXTEND | BCF_BV,
            params: (32_u16 << 8) | 64,
            args: vec![arg],
        })
    }

    /// Sign-extend a 32-bit value to 64 bits. Same param layout as zext.
    pub fn sext_32_to_64(&mut self, arg: u32) -> u32 {
        self.push_expr(BcfExpr {
            code: BCF_SIGN_EXTEND | BCF_BV,
            params: (32_u16 << 8) | 64,
            args: vec![arg],
        })
    }

    /// Extract the low `size` bits of `arg`. `params = start << 8 | end`,
    /// where `start = size - 1` (high bit) and `end = 0` (low bit).
    pub fn extract_lo(&mut self, size: u8, arg: u32) -> u32 {
        let start = (size as u16).saturating_sub(1);
        self.push_expr(BcfExpr {
            code: BCF_EXTRACT | BCF_BV,
            params: start << 8,
            args: vec![arg],
        })
    }

    // ---------- path conditions / refinement target ----------

    /// Append a path condition (an expression that must hold on the current path).
    pub fn add_cond(&mut self, pred_idx: u32) {
        self.path_conds.push(pred_idx);
    }

    /// Set the refinement condition target.
    pub fn set_refine_cond(&mut self, idx: u32) {
        self.refine_cond = Some(idx);
    }
}

/// Build the per-site refinement goal expression and return its slot.
///
/// Matches the kernel-side BCF goal layout (see `bcf_refine` in
/// kernel/bpf/verifier.c): `CONJ(path_cond_aggregated, refine_cond)` where
/// `path_cond_aggregated` is the single path-cond when there's one, or a
/// flat CONJ over all path-conds when there are several. The kernel's
/// `__expr_equiv` check against the proof's assume-step argument requires
/// this exact structural shape; pointing `goal_root` at just `refine_cond`
/// (the previous behaviour) caused -EINVAL at bundle prevalidate.
pub fn build_goal_root(sym: &mut SymbolicState, refine_cond: u32) -> u32 {
    match sym.path_conds.len() {
        0 => refine_cond,
        1 => sym.add_conj(vec![sym.path_conds[0], refine_cond]),
        _ => {
            let pcs = sym.path_conds.clone();
            let inner = sym.add_conj(pcs);
            sym.add_conj(vec![inner, refine_cond])
        }
    }
}

impl SymbolicState {

    // ---------- per-register bindings ----------

    /// Bind register `reg` to symbolic expression `idx`.
    pub fn bind_reg(&mut self, reg: usize, idx: u32) {
        self.reg_expr[reg] = Some(idx);
    }

    /// Get the bound expression for `reg`.
    pub fn get_reg(&self, reg: usize) -> Option<u32> {
        self.reg_expr[reg]
    }

    /// Clear the bound expression for `reg` (e.g., before a clobbering write
    /// whose new expression hasn't been built yet). Mirrors BCF's
    /// `reg->bcf_expr = -1` clears.
    pub fn clear_reg(&mut self, reg: usize) {
        self.reg_expr[reg] = None;
    }

    /// Lazy-materialize a 64-bit symbolic expression for `reg`.
    /// If already bound, returns the existing index; otherwise allocates a
    /// fresh 64-bit symbolic variable and binds it. Mirrors BCF's
    /// `bcf_reg_expr` entry point — anything that wants `reg` symbolically
    /// goes through here.
    ///
    /// **R10 is special**: it's the frame pointer, and its offset relative
    /// to itself is the constant 0 — not an unknown symbolic value. This
    /// lets pointer-arithmetic chains like `r1 = r10; r1 += -16; r1 += r0`
    /// produce a meaningful symbolic offset expression for r1 (β+ change,
    /// 2026-05-12). Index 10 is hard-coded to match the `Reg::R10.bcf_idx()`
    /// convention.
    ///
    /// Phase 1 simplification: always 64-bit (BCF picks 32 or 64 based on
    /// `fit_u32/fit_s32`; we'll add the 32-bit fast path in Phase 2 if the
    /// formula size matters).
    pub fn materialize_reg64(&mut self, reg: usize) -> u32 {
        if let Some(idx) = self.reg_expr[reg] {
            return idx;
        }
        let idx = if reg == 10 {
            self.add_val64(0)
        } else {
            self.add_var(64)
        };
        self.bind_reg(reg, idx);
        idx
    }

    // ---------- queries ----------

    /// Total expression-table size in u32 slots (matches the on-disk `expr_cnt`).
    pub fn expr_slot_count(&self) -> u32 {
        self.next_slot
    }

    /// Look up an expression by its slot offset. `None` if not found.
    pub fn expr_at(&self, idx: u32) -> Option<&BcfExpr> {
        let mut cur = 0u32;
        for e in &self.exprs {
            if cur == idx {
                return Some(e);
            }
            cur += e.slot_len();
        }
        None
    }

    /// Build a [`BcfProof`] artifact whose `exprs` is the current DAG and whose
    /// `steps` is empty. Useful for serializing the formula (without a proof
    /// yet) — e.g., to hash it canonically or feed it to an SMT-LIB encoder.
    pub fn to_proof_no_steps(&self) -> BcfProof {
        BcfProof {
            exprs: self.exprs.clone(),
            steps: vec![],
        }
    }
}

// ---------- tests ----------

#[cfg(test)]
mod tests {
    use super::*;

    /// The basic shape of a SymbolicState: expressions accumulate by slot offset,
    /// not by Vec index.
    #[test]
    fn slot_offsets_account_for_arg_arrays() {
        let mut s = SymbolicState::new();
        let v = s.add_var(64); // 1 slot
        assert_eq!(v, 0);
        let c = s.add_val64(0xdead_beef_cafe_babe); // 1 + 2 = 3 slots
        assert_eq!(c, 1);
        let a = s.add_alu(BPF_ADD, v, c, 64); // 1 + 2 = 3 slots
        assert_eq!(a, 4);
        assert_eq!(s.expr_slot_count(), 7);
    }

    /// `expr_at` finds entries by slot offset, not by Vec index.
    #[test]
    fn expr_at_lookup() {
        let mut s = SymbolicState::new();
        let v = s.add_var(64);
        let c = s.add_val64(42);
        let a = s.add_alu(BPF_ADD, v, c, 64);
        assert_eq!(s.expr_at(v).unwrap().code, BCF_VAR | BCF_BV);
        assert_eq!(s.expr_at(c).unwrap().code, BCF_VAL | BCF_BV);
        assert_eq!(s.expr_at(a).unwrap().code, BPF_ADD | BCF_BV);
        assert!(s.expr_at(99).is_none());
    }

    /// Reconstruct shift_constraint's symbolic state along the unsafe path
    /// (pc 1 → pc 8, with the fall-through of `if r1 > 4` taken). Build the
    /// refinement condition for the stack access at pc 8.
    ///
    /// Program (from `examples/src/shift_constraint.bpf.c`, summarised):
    /// ```text
    /// pc 0: r0 = helper(7)                  // tracepoint arg
    /// pc 1: r0 &= 0xff (32-bit)             // r0 ∈ [0, 255]
    /// pc 2: r1 = r0                         // mov
    /// pc 3: r2 = r10
    /// pc 4: r2 = r10 + (-16)                // stack offset = -16
    /// pc 5: r2 = r2 + r0                    // stack offset = -16 + r0
    /// pc 6: r1 = r1 >> 1                    // r1 = r0 >> 1
    /// pc 7: if r1 > 4 goto 10               // fall-through ⇒ r1 ≤ 4
    /// pc 8: load u8 [r2]                    // STACK ACCESS — rejected by us
    /// pc 9: r0 = 0
    /// pc 10: exit
    /// ```
    ///
    /// Refinement-condition shape (per cheat sheet §4a/§4b): the access at
    /// `r2 = r10 + off` with `off = -16 + r0` and access size 1 is safe iff
    /// `off ∈ [stack_min, -1]` (stack frame is below r10). We encode the OOB
    /// claim — `(off s> -1)` — and want cvc5 to prove the conjunction
    /// `path_conds ∧ refine_cond` unsat.
    #[test]
    fn build_shift_constraint_refinement_formula() {
        let mut s = SymbolicState::new();

        // pc 0–1: r0 originates from a helper return, then masked with 0xff in
        // 32-bit ALU. Modeling as: r0 = zext_32_to_64(sym32 & 0xff).
        let sym32 = s.add_var(32);
        let mask32 = s.add_val32(0xff);
        let masked32 = s.add_alu(BPF_AND, sym32, mask32, 32);
        let r0 = s.zext_32_to_64(masked32);
        s.bind_reg(0, r0);

        // pc 2: r1 = r0 (full mov shares the expression).
        s.bind_reg(1, r0);

        // pc 4–5: r2 represents the stack offset (-16 + r0). We don't
        // symbolically track r10 itself; the offset is what gates safety.
        let neg16 = s.add_val64((-16_i64) as u64);
        let off = s.add_alu(BPF_ADD, neg16, r0, 64);
        s.bind_reg(2, off);

        // pc 6: r1 = r1 >> 1 (ALU64). r1 = r0 >> 1.
        let one64 = s.add_val64(1);
        let r1_shifted = s.add_alu(BPF_RSH, r0, one64, 64);
        s.bind_reg(1, r1_shifted);

        // pc 7 fall-through: r1 ≤ 4. Encoded as r1 JLE 4.
        let four64 = s.add_val64(4);
        let p_fall = s.add_pred(BPF_JLE, r1_shifted, four64);
        s.add_cond(p_fall);

        // Refinement target: prove the access is in bounds. We assert the OOB
        // condition (off s> -1, i.e., off as signed is non-negative for a
        // stack offset that must be ≤ -1) and want unsat.
        let neg1 = s.add_val64((-1_i64) as u64);
        let oob = s.add_pred(BPF_JSGT, off, neg1);
        s.set_refine_cond(oob);

        // ---- structural sanity ----
        assert_eq!(s.path_conds.len(), 1);
        assert!(s.refine_cond.is_some());
        assert!(s.reg_expr[0].is_some());
        assert!(s.reg_expr[1].is_some());
        assert!(s.reg_expr[2].is_some());

        // ---- self-consistency: slot counts and on-disk size ----
        let proof = s.to_proof_no_steps();
        let bytes = proof.to_bytes();
        // Header (12 bytes) + 4 * expr_slot_count + 0 step bytes.
        let expected = 12 + 4 * s.expr_slot_count() as usize;
        assert_eq!(bytes.len(), expected);

        // ---- round-trip through ser/de ----
        let parsed = BcfProof::from_bytes(&bytes).expect("parse failed");
        assert_eq!(parsed.exprs.len(), s.exprs.len());
        assert_eq!(parsed.to_bytes(), bytes);

        // ---- spot-check: the recorded path-cond is a JLE BV predicate ----
        // BV predicates have boolean result type, so code = op | BCF_BOOL.
        let p_expr = s.expr_at(p_fall).unwrap();
        assert_eq!(p_expr.code, BPF_JLE | BCF_BOOL);
        let p_args = &p_expr.args;
        assert_eq!(p_args.len(), 2);
        assert_eq!(p_args[0], r1_shifted);
        assert_eq!(p_args[1], four64);

        // ---- spot-check: the refine-cond is JSGT off > -1 ----
        let r_expr = s.expr_at(oob).unwrap();
        assert_eq!(r_expr.code, BPF_JSGT | BCF_BOOL);
        assert_eq!(r_expr.args[0], off);
        assert_eq!(r_expr.args[1], neg1);
    }
}
