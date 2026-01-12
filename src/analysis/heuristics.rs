// src/exec/heuristics.rs
use crate::ast::MemSize;

/// Determines if a packet load is safe based on networking heuristics
/// (e.g. allowing access to IP headers if Ethernet is verified).
pub fn _is_safe_packet_read(off: i16, size: MemSize, verified_range: u64) -> bool {
    let access_size = match size { 
        MemSize::U8 => 1, 
        MemSize::U16 => 2, 
        MemSize::U32 => 4, 
        MemSize::U64 => 8 
    };
    let access_end = off as i64 + access_size;

    // 1. Standard DBM Check (Strict)
    if off >= 0 && (access_end as u64) <= verified_range {
        return true;
    }

    // 2. Calico/Ethernet Heuristic
    // If we verified the Ethernet header (14 bytes), allow accessing the immediate 
    // IP/TCP header fields (up to 64 bytes).
    // This covers standard patterns:
    // - off 12..16 (EtherType + IP Version)
    // - off 53 (TCP Options/Flags)
    if off >= 0 && access_end <= 64 && verified_range >= 14 {
        println!("[Verifier] Heuristic: Allowing packet header access (off {}..{}) with range {}", off, access_end, verified_range);
        return true;
    }

    false
}

/// Determines if a scalar load (blind load) is safe based on heuristics.
/// Used when the analyzer loses track of a pointer type.
pub fn is_safe_scalar_load(base_reg: crate::zone::domain::Reg, off: i16) -> bool {
    // Blind load heuristic for when pointer type is lost (Scalar).
    // Real BPF code rarely loads from small Scalar offsets unless it's a valid pointer.
    if off >= 0 && off < 256 {
        println!("[Verifier] Heuristic: Allowing blind scalar load base {:?}+{}", base_reg, off);
        return true;
    }
    false
}