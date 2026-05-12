//! BCF bundle sidecar writer.
//!
//! Wire format frozen in `c-ref/bcf_bundle.h` as the proposed UAPI. This
//! Rust module is the authoritative writer; the C header is documentation
//! for the eventual kernel patch (step 3.4). Constants and offsets in the
//! two files must stay in sync.
//!
//! Bundle layout (little-endian):
//! ```text
//!   header: magic, entry_cnt, total_size, reserved          (4 × u32 = 16 B)
//!   entries: each (cond_hash u64, goal_off u32, goal_size u32,
//!                  proof_off u32, proof_size u32, kind u32)  (28 B)
//!   goal payloads + proof payloads (u32-aligned, addressed by entry offsets)
//! ```
//!
//! Per-entry goal payload (parsed by step 3.4's kernel-side bcf_check_proof
//! caller):
//! ```text
//!   u32 root          (expr-id of the refinement-condition root)
//!   u32 expr_cnt
//!   expr_cnt × {
//!       u8  code, u8 vlen, u16 params, vlen × u32 args
//!   }
//! ```

use std::io::{self, Write};
use std::path::Path;

use super::bcf::BcfExpr;
use super::canonical_hash::hash_expr;

// ---------- magic / kinds (mirror c-ref/bcf_bundle.h) ----------

pub const BCF_BUNDLE_MAGIC: u32 = 0x42464342; // 'BCFB' little-endian
pub const BCF_BUNDLE_KIND_REFINE: u32 = 1;
#[allow(dead_code)]
pub const BCF_BUNDLE_KIND_UNREACHABLE: u32 = 2;

pub const BUNDLE_HEADER_SIZE: usize = 16;
pub const BUNDLE_ENTRY_SIZE: usize = 28;

// ---------- in-memory entry ----------

/// One refinement entry, in unserialized form.
///
/// `cond_hash` is the canonical hash of the goal-root expression over the
/// `goal_exprs` table. `goal_exprs` is the expression table the kernel will
/// rebuild to run `expr_equiv` + `bcf_check_proof`. `proof_bytes` is the
/// raw cvc5-produced BCF proof.
#[derive(Debug, Clone)]
pub struct RefineEntry {
    pub cond_hash: u64,
    pub goal_root: u32,
    pub goal_exprs: Vec<BcfExpr>,
    pub proof_bytes: Vec<u8>,
    pub kind: u32,
}

impl RefineEntry {
    /// Build an entry, computing `cond_hash` via the canonical hash spec.
    pub fn new(goal_root: u32, goal_exprs: Vec<BcfExpr>, proof_bytes: Vec<u8>, kind: u32) -> Self {
        let cond_hash = hash_expr(goal_root, &goal_exprs);
        Self { cond_hash, goal_root, goal_exprs, proof_bytes, kind }
    }
}

// ---------- goal-payload serialization ----------

/// Serialize an `(exprs, root)` pair into the per-entry goal payload format
/// defined in c-ref/bcf_bundle.h. The output is u32-sized at the boundaries
/// but is itself a stream of bytes; callers pad to u32 alignment when
/// concatenating into the bundle.
pub fn serialize_goal(root: u32, exprs: &[BcfExpr]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + exprs.len() * 8);
    out.extend_from_slice(&root.to_le_bytes());
    out.extend_from_slice(&(exprs.len() as u32).to_le_bytes());
    for e in exprs {
        out.push(e.code);
        out.push(e.args.len() as u8);
        out.extend_from_slice(&e.params.to_le_bytes());
        for arg in &e.args {
            out.extend_from_slice(&arg.to_le_bytes());
        }
    }
    out
}

// ---------- bundle writer ----------

#[inline]
fn align4(n: usize) -> usize {
    (n + 3) & !3
}

/// Write a bundle to `path`. Returns total bytes written.
pub fn write_bundle(path: &Path, entries: &[RefineEntry]) -> io::Result<usize> {
    // First pass: serialize per-entry payloads (held in memory; bundles are
    // small — single-digit MB at most — so no streaming concerns).
    struct Serialized<'a> {
        cond_hash: u64,
        kind: u32,
        goal: Vec<u8>,
        proof: &'a [u8],
    }
    let serialized: Vec<Serialized> = entries
        .iter()
        .map(|e| Serialized {
            cond_hash: e.cond_hash,
            kind: e.kind,
            goal: serialize_goal(e.goal_root, &e.goal_exprs),
            proof: &e.proof_bytes,
        })
        .collect();

    // Layout: header | entries | concatenated (goal | proof) per entry,
    // each padded to u32. Interleaving goal and proof per entry keeps the
    // kernel-side parse simple and lets us add new payload sections later
    // without re-flowing earlier offsets.
    let mut payload_total = 0usize;
    for s in &serialized {
        payload_total += align4(s.goal.len()) + align4(s.proof.len());
    }
    let total_size =
        BUNDLE_HEADER_SIZE + BUNDLE_ENTRY_SIZE * entries.len() + payload_total;

    let mut buf = Vec::with_capacity(total_size);

    // --- header ---
    buf.extend_from_slice(&BCF_BUNDLE_MAGIC.to_le_bytes());
    buf.extend_from_slice(&(entries.len() as u32).to_le_bytes());
    buf.extend_from_slice(&(total_size as u32).to_le_bytes());
    buf.extend_from_slice(&0u32.to_le_bytes()); // reserved

    // --- entries (precompute offsets) ---
    let payload_base = BUNDLE_HEADER_SIZE + BUNDLE_ENTRY_SIZE * entries.len();
    let mut cur = payload_base;
    for s in &serialized {
        let goal_off = cur;
        let goal_padded = align4(s.goal.len());
        let proof_off = goal_off + goal_padded;
        let proof_padded = align4(s.proof.len());

        buf.extend_from_slice(&s.cond_hash.to_le_bytes());
        buf.extend_from_slice(&(goal_off as u32).to_le_bytes());
        buf.extend_from_slice(&(s.goal.len() as u32).to_le_bytes());
        buf.extend_from_slice(&(proof_off as u32).to_le_bytes());
        buf.extend_from_slice(&(s.proof.len() as u32).to_le_bytes());
        buf.extend_from_slice(&s.kind.to_le_bytes());

        cur = proof_off + proof_padded;
    }

    // --- payloads ---
    for s in &serialized {
        buf.extend_from_slice(&s.goal);
        let pad = align4(s.goal.len()) - s.goal.len();
        buf.resize(buf.len() + pad, 0);

        buf.extend_from_slice(s.proof);
        let pad = align4(s.proof.len()) - s.proof.len();
        buf.resize(buf.len() + pad, 0);
    }

    debug_assert_eq!(buf.len(), total_size, "bundle size accounting drift");

    let mut f = std::fs::File::create(path)?;
    f.write_all(&buf)?;
    Ok(total_size)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::refinement::bcf::{BCF_BV, BCF_VAL, BCF_VAR, BPF_ADD};

    fn sample_entry() -> RefineEntry {
        // Tiny goal expression: add(v, const). Slot offsets (BCF convention):
        //   v   at slot 0 (slot_len = 1 + 0)
        //   c   at slot 1 (slot_len = 1 + 1 = 2)
        //   add at slot 3 (slot_len = 1 + 2 = 3); args = [0, 1]
        let mut exprs = vec![];
        exprs.push(BcfExpr { code: BCF_VAR | BCF_BV, params: 64, args: vec![] });
        exprs.push(BcfExpr { code: BCF_VAL | BCF_BV, params: 0,  args: vec![42] });
        exprs.push(BcfExpr { code: BPF_ADD | BCF_BV, params: 0,  args: vec![0, 1] });
        let proof = vec![0xcf, 0x0b, 0x00, 0x00, 0xaa, 0xbb];
        RefineEntry::new(3, exprs, proof, BCF_BUNDLE_KIND_REFINE)
    }

    #[test]
    fn round_trip_one_entry() {
        let entry = sample_entry();
        let expected_hash = entry.cond_hash;
        let expected_proof = entry.proof_bytes.clone();
        let expected_goal_bytes =
            serialize_goal(entry.goal_root, &entry.goal_exprs);

        let dir = std::env::temp_dir().join(format!("zovia-bundle-test-{}", std::process::id()));
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("test.bcf-bundle");
        let total = write_bundle(&path, &[entry]).expect("write");
        let bytes = std::fs::read(&path).expect("read");
        assert_eq!(bytes.len(), total);

        // Header.
        assert_eq!(&bytes[0..4], &BCF_BUNDLE_MAGIC.to_le_bytes());
        assert_eq!(u32::from_le_bytes(bytes[4..8].try_into().unwrap()), 1);
        assert_eq!(u32::from_le_bytes(bytes[8..12].try_into().unwrap()) as usize, total);

        // Entry at byte 16.
        let cond_hash = u64::from_le_bytes(bytes[16..24].try_into().unwrap());
        let goal_off  = u32::from_le_bytes(bytes[24..28].try_into().unwrap()) as usize;
        let goal_size = u32::from_le_bytes(bytes[28..32].try_into().unwrap()) as usize;
        let proof_off = u32::from_le_bytes(bytes[32..36].try_into().unwrap()) as usize;
        let proof_size = u32::from_le_bytes(bytes[36..40].try_into().unwrap()) as usize;
        let kind      = u32::from_le_bytes(bytes[40..44].try_into().unwrap());

        assert_eq!(cond_hash, expected_hash);
        assert_eq!(kind, BCF_BUNDLE_KIND_REFINE);
        assert_eq!(&bytes[goal_off..goal_off + goal_size], &expected_goal_bytes[..]);
        assert_eq!(&bytes[proof_off..proof_off + proof_size], &expected_proof[..]);

        // Offsets are u32-aligned.
        assert_eq!(goal_off % 4, 0);
        assert_eq!(proof_off % 4, 0);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn cond_hash_matches_canonical_hash() {
        let entry = sample_entry();
        let direct = hash_expr(entry.goal_root, &entry.goal_exprs);
        assert_eq!(entry.cond_hash, direct);
    }

    #[test]
    fn two_entries_have_disjoint_payloads() {
        let a = sample_entry();
        let mut b_exprs = a.goal_exprs.clone();
        b_exprs[1].args[0] = 999; // different constant → different hash
        let b = RefineEntry::new(3, b_exprs, vec![0xde, 0xad], BCF_BUNDLE_KIND_REFINE);
        assert_ne!(a.cond_hash, b.cond_hash);

        let dir = std::env::temp_dir().join(format!("zovia-bundle-2ent-{}", std::process::id()));
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("two.bcf-bundle");
        write_bundle(&path, &[a.clone(), b.clone()]).expect("write");
        let bytes = std::fs::read(&path).expect("read");

        // Parse both entries' offsets and confirm non-overlap.
        let entry0_off = BUNDLE_HEADER_SIZE;
        let entry1_off = entry0_off + BUNDLE_ENTRY_SIZE;
        let g0_off = u32::from_le_bytes(bytes[entry0_off + 8..entry0_off + 12].try_into().unwrap()) as usize;
        let g0_sz  = u32::from_le_bytes(bytes[entry0_off + 12..entry0_off + 16].try_into().unwrap()) as usize;
        let p0_off = u32::from_le_bytes(bytes[entry0_off + 16..entry0_off + 20].try_into().unwrap()) as usize;
        let p0_sz  = u32::from_le_bytes(bytes[entry0_off + 20..entry0_off + 24].try_into().unwrap()) as usize;
        let g1_off = u32::from_le_bytes(bytes[entry1_off + 8..entry1_off + 12].try_into().unwrap()) as usize;
        let g1_sz  = u32::from_le_bytes(bytes[entry1_off + 12..entry1_off + 16].try_into().unwrap()) as usize;

        assert!(g0_off + g0_sz <= p0_off, "goal 0 overruns proof 0");
        assert!(p0_off + p0_sz <= g1_off, "proof 0 overruns goal 1");
        assert!(g1_off + g1_sz <= bytes.len(), "goal 1 overruns bundle");

        let _ = std::fs::remove_dir_all(&dir);
    }
}
