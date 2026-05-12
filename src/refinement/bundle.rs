//! BCF bundle sidecar writer.
//!
//! Phase 1 implementation of the single-pass bundle format described in
//! `project_userspace_bcf.md`. Each entry pairs a canonical hash of the
//! refinement-condition expression with the cvc5-produced proof bytes;
//! the kernel patch (Phase 3) will look entries up by hash at safety-check
//! sites instead of suspending into userspace.
//!
//! On-disk layout (little-endian, 4-byte-aligned):
//! ```text
//!   header: magic, entry_cnt, total_size, reserved   (4 × u32)
//!   entries: each (cond_hash u64, proof_offset u32,
//!                  proof_size u32, kind u32, reserved u32)
//!   proof blob: concatenated proof byte streams, addressed by entry offsets
//! ```
//!
//! The canonical-hash spec is deferred to Phase 3. For now we hash the
//! proof bytes directly with `DefaultHasher` so we have a stable identifier
//! per entry; the value isn't yet meaningful to a kernel-side lookup.

use std::io::{self, Write};
use std::path::Path;

pub const BCF_BUNDLE_MAGIC: u32 = 0x4246_4342; // "BCFB" little-endian
pub const BCF_BUNDLE_KIND_REFINE: u32 = 1;
#[allow(dead_code)]
pub const BCF_BUNDLE_KIND_UNREACHABLE: u32 = 2;

/// Write a bundle file containing `entries`. Each entry is
/// `(cond_hash, proof_bytes, kind)`. Returns the total byte count written.
pub fn write_bundle(path: &Path, entries: &[(u64, Vec<u8>, u32)]) -> io::Result<usize> {
    let header_size = 16; // 4 × u32
    let entry_size = 24; // u64 + 4 × u32
    let mut total_proof_bytes = 0usize;
    for (_, p, _) in entries {
        // pad each proof to 4-byte alignment for offset arithmetic
        let padded = (p.len() + 3) & !3;
        total_proof_bytes += padded;
    }
    let total_size = header_size + entry_size * entries.len() + total_proof_bytes;

    let mut buf = Vec::with_capacity(total_size);
    buf.extend_from_slice(&BCF_BUNDLE_MAGIC.to_le_bytes());
    buf.extend_from_slice(&(entries.len() as u32).to_le_bytes());
    buf.extend_from_slice(&(total_size as u32).to_le_bytes());
    buf.extend_from_slice(&0u32.to_le_bytes()); // reserved

    // First pass: compute proof offsets (relative to start of proof blob).
    let proof_blob_start = header_size + entry_size * entries.len();
    let mut cur_off = proof_blob_start;
    for (hash, proof, kind) in entries {
        buf.extend_from_slice(&hash.to_le_bytes());
        buf.extend_from_slice(&(cur_off as u32).to_le_bytes());
        buf.extend_from_slice(&(proof.len() as u32).to_le_bytes());
        buf.extend_from_slice(&kind.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes()); // reserved
        let padded = (proof.len() + 3) & !3;
        cur_off += padded;
    }

    // Second pass: append the actual proof bytes, each 4-byte-padded.
    for (_, proof, _) in entries {
        buf.extend_from_slice(proof);
        let pad = ((proof.len() + 3) & !3) - proof.len();
        for _ in 0..pad {
            buf.push(0);
        }
    }

    debug_assert_eq!(buf.len(), total_size, "bundle size accounting drift");

    let mut f = std::fs::File::create(path)?;
    f.write_all(&buf)?;
    Ok(total_size)
}

/// Hash proof bytes for use as a placeholder `cond_hash`. The Phase 3
/// canonical hash will replace this with a post-order DAG walk over the
/// refine_cond expression. For Phase 1 / bundle smoke testing this is just
/// a stable per-proof identifier.
pub fn placeholder_cond_hash(proof_bytes: &[u8]) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut h = DefaultHasher::new();
    proof_bytes.hash(&mut h);
    h.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip_one_entry() {
        let proof = vec![0xcf, 0x0b, 0x00, 0x00, 0xaa, 0xbb];
        let entries = vec![(0xdeadbeef_cafe_babe, proof.clone(), BCF_BUNDLE_KIND_REFINE)];
        let dir = std::env::temp_dir().join(format!("zovia-bundle-test-{}", std::process::id()));
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("test.bcf-bundle");
        let total = write_bundle(&path, &entries).expect("write");
        let bytes = std::fs::read(&path).expect("read");
        assert_eq!(bytes.len(), total);

        // Magic
        let magic = u32::from_le_bytes(bytes[0..4].try_into().unwrap());
        assert_eq!(magic, BCF_BUNDLE_MAGIC);
        // Entry count
        let n = u32::from_le_bytes(bytes[4..8].try_into().unwrap());
        assert_eq!(n, 1);
        // total_size matches
        let ts = u32::from_le_bytes(bytes[8..12].try_into().unwrap());
        assert_eq!(ts as usize, total);

        // First entry's proof_offset + proof_size must point at our bytes.
        let cond_hash = u64::from_le_bytes(bytes[16..24].try_into().unwrap());
        assert_eq!(cond_hash, 0xdeadbeef_cafe_babe);
        let off = u32::from_le_bytes(bytes[24..28].try_into().unwrap()) as usize;
        let sz = u32::from_le_bytes(bytes[28..32].try_into().unwrap()) as usize;
        let kind = u32::from_le_bytes(bytes[32..36].try_into().unwrap());
        assert_eq!(kind, BCF_BUNDLE_KIND_REFINE);
        assert_eq!(&bytes[off..off + sz], &proof[..]);

        let _ = std::fs::remove_dir_all(&dir);
    }
}
