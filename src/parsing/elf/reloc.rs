use anyhow::Result;
use goblin::elf::Elf;
use std::collections::HashMap;
use std::fs;
use std::path::Path;

use super::types::{BpfCallTarget, BpfMapDef, RelocInfo, RelocKind};
use crate::common::constants::{self, R_BPF_64_32, R_BPF_64_64};
use crate::parsing::bpf_insn::RawBpfInsn;

/// Look up BPF helper ID by name.
/// Returns None if the name is not a known helper.
/// Uses constants from common::constants where available.
fn helper_id_by_name(name: &str) -> Option<u32> {
    match name {
        "bpf_unspec" => Some(0),
        "bpf_map_lookup_elem" => Some(constants::BPF_MAP_LOOKUP_ELEM),
        "bpf_map_update_elem" => Some(constants::BPF_MAP_UPDATE_ELEM),
        "bpf_map_delete_elem" => Some(constants::BPF_MAP_DELETE_ELEM),
        "bpf_probe_read" => Some(constants::BPF_PROBE_READ),
        "bpf_ktime_get_ns" => Some(constants::BPF_KTIME_GET_NS),
        "bpf_trace_printk" => Some(constants::BPF_TRACE_PRINTK),
        "bpf_get_prandom_u32" => Some(constants::BPF_GET_PRANDOM_U32),
        "bpf_get_smp_processor_id" => Some(constants::BPF_GET_SMP_PROCESSOR_ID),
        "bpf_skb_store_bytes" => Some(constants::BPF_SKB_STORE_BYTES),
        "bpf_l3_csum_replace" => Some(constants::BPF_L3_CSUM_REPLACE),
        "bpf_l4_csum_replace" => Some(constants::BPF_L4_CSUM_REPLACE),
        "bpf_tail_call" => Some(constants::BPF_TAIL_CALL),
        "bpf_clone_redirect" => Some(constants::BPF_CLONE_REDIRECT),
        "bpf_get_current_pid_tgid" => Some(14),
        "bpf_get_current_uid_gid" => Some(15),
        "bpf_get_current_comm" => Some(constants::BPF_GET_CURRENT_COMM),
        "bpf_get_cgroup_classid" => Some(constants::BPF_GET_CGROUP_CLASS_ID),
        "bpf_skb_vlan_push" => Some(18),
        "bpf_skb_vlan_pop" => Some(19),
        "bpf_skb_get_tunnel_key" => Some(20),
        "bpf_skb_set_tunnel_key" => Some(21),
        "bpf_perf_event_read" => Some(22),
        "bpf_redirect" => Some(constants::BPF_REDIRECT),
        "bpf_get_route_realm" => Some(24),
        "bpf_perf_event_output" => Some(constants::BPF_PERF_EVENT_OUTPUT),
        "bpf_skb_load_bytes" => Some(constants::BPF_SKB_LOAD_BYTES),
        "bpf_get_stackid" => Some(27),
        "bpf_csum_diff" => Some(constants::BPF_CSUM_DIFF),
        "bpf_skb_get_tunnel_opt" => Some(29),
        "bpf_skb_set_tunnel_opt" => Some(30),
        "bpf_skb_change_proto" => Some(constants::BPF_SKB_CHANGE_PROTO),
        "bpf_skb_change_type" => Some(32),
        "bpf_skb_under_cgroup" => Some(33),
        "bpf_get_hash_recalc" => Some(constants::BPF_GET_HASH_RECALC),
        "bpf_get_current_task" => Some(35),
        "bpf_probe_write_user" => Some(36),
        "bpf_current_task_under_cgroup" => Some(37),
        "bpf_skb_change_tail" => Some(constants::BPF_SKB_CHANGE_TAIL),
        "bpf_skb_pull_data" => Some(constants::BPF_SKB_PULL_DATA),
        "bpf_csum_update" => Some(constants::BPF_CSUM_UPDATE),
        "bpf_set_hash_invalid" => Some(41),
        "bpf_get_numa_node_id" => Some(42),
        "bpf_skb_change_head" => Some(constants::BPF_SKB_CHANGE_HEAD),
        "bpf_xdp_adjust_head" => Some(constants::BPF_XDP_ADJUST_HEAD),
        "bpf_probe_read_str" => Some(45),
        "bpf_get_socket_cookie" => Some(constants::BPF_GET_SOCKET_COOKIE),
        "bpf_get_socket_uid" => Some(47),
        "bpf_set_hash" => Some(48),
        "bpf_setsockopt" => Some(49),
        "bpf_skb_adjust_room" => Some(constants::BPF_SKB_ADJUST_ROOM),
        "bpf_redirect_map" => Some(51),
        "bpf_sk_redirect_map" => Some(52),
        "bpf_sock_map_update" => Some(constants::BPF_SOCK_MAP_UPDATE),
        "bpf_xdp_adjust_meta" => Some(constants::BPF_XDP_ADJUST_META),
        "bpf_perf_event_read_value" => Some(55),
        "bpf_perf_prog_read_value" => Some(56),
        "bpf_getsockopt" => Some(constants::BPF_GET_SOCKOPT),
        "bpf_override_return" => Some(58),
        "bpf_sock_ops_cb_flags_set" => Some(59),
        "bpf_msg_redirect_map" => Some(60),
        "bpf_msg_apply_bytes" => Some(61),
        "bpf_msg_cork_bytes" => Some(62),
        "bpf_msg_pull_data" => Some(63),
        "bpf_bind" => Some(64),
        "bpf_xdp_adjust_tail" => Some(65),
        "bpf_skb_get_xfrm_state" => Some(66),
        "bpf_get_stack" => Some(constants::BPF_GET_STACK),
        "bpf_skb_load_bytes_relative" => Some(68),
        "bpf_fib_lookup" => Some(constants::BPF_FIB_LOOKUP),
        "bpf_sock_hash_update" => Some(70),
        "bpf_msg_redirect_hash" => Some(71),
        "bpf_sk_redirect_hash" => Some(72),
        "bpf_lwt_push_encap" => Some(73),
        "bpf_lwt_seg6_store_bytes" => Some(74),
        "bpf_lwt_seg6_adjust_srh" => Some(75),
        "bpf_lwt_seg6_action" => Some(76),
        "bpf_rc_repeat" => Some(77),
        "bpf_rc_keydown" => Some(78),
        "bpf_skb_cgroup_id" => Some(79),
        "bpf_get_current_cgroup_id" => Some(80),
        "bpf_get_local_storage" => Some(constants::BPF_GET_LOCAL_STORAGE),
        "bpf_sk_select_reuseport" => Some(82),
        "bpf_skb_ancestor_cgroup_id" => Some(83),
        "bpf_sk_lookup_tcp" => Some(constants::BPF_SK_LOOKUP_TCP),
        "bpf_sk_lookup_udp" => Some(constants::BPF_SK_LOOKUP_UDP),
        "bpf_sk_release" => Some(constants::BPF_SK_RELEASE),
        "bpf_map_push_elem" => Some(87),
        "bpf_map_pop_elem" => Some(88),
        "bpf_map_peek_elem" => Some(89),
        "bpf_msg_push_data" => Some(90),
        "bpf_msg_pop_data" => Some(91),
        "bpf_rc_pointer_rel" => Some(92),
        "bpf_spin_lock" => Some(constants::BPF_SPIN_LOCK),
        "bpf_spin_unlock" => Some(constants::BPF_SPIN_UNLOCK),
        "bpf_sk_fullsock" => Some(constants::BPF_SK_FULLSOCK),
        "bpf_tcp_sock" => Some(constants::BPF_TCP_SOCK),
        "bpf_skb_ecn_set_ce" => Some(constants::BPF_SKB_ECN_SET_CE),
        "bpf_get_listener_sock" => Some(constants::BPF_GET_LISTENER_SOCK),
        "bpf_skc_lookup_tcp" => Some(constants::BPF_SKC_LOOKUP_TCP),
        "bpf_tcp_check_syncookie" => Some(100),
        "bpf_sysctl_get_name" => Some(101),
        "bpf_sysctl_get_current_value" => Some(102),
        "bpf_sysctl_get_new_value" => Some(103),
        "bpf_sysctl_set_new_value" => Some(104),
        "bpf_strtol" => Some(105),
        "bpf_strtoul" => Some(constants::BPF_STRTOUL),
        "bpf_sk_storage_get" => Some(constants::BPF_SK_STORAGE_GET),
        "bpf_sk_storage_delete" => Some(108),
        "bpf_send_signal" => Some(109),
        "bpf_tcp_gen_syncookie" => Some(110),
        "bpf_skb_output" => Some(111),
        "bpf_probe_read_user" => Some(constants::BPF_PROBE_READ_USER),
        "bpf_probe_read_kernel" => Some(constants::BPF_PROBE_READ_KERNEL),
        "bpf_probe_read_user_str" => Some(114),
        "bpf_probe_read_kernel_str" => Some(115),
        "bpf_tcp_send_ack" => Some(116),
        "bpf_send_signal_thread" => Some(117),
        "bpf_jiffies64" => Some(118),
        "bpf_read_branch_records" => Some(119),
        "bpf_get_ns_current_pid_tgid" => Some(120),
        "bpf_xdp_output" => Some(121),
        "bpf_get_netns_cookie" => Some(122),
        "bpf_get_current_ancestor_cgroup_id" => Some(123),
        "bpf_sk_assign" => Some(constants::BPF_SK_ASSIGN),
        "bpf_ktime_get_boot_ns" => Some(125),
        "bpf_seq_printf" => Some(126),
        "bpf_seq_write" => Some(127),
        "bpf_sk_cgroup_id" => Some(128),
        "bpf_sk_ancestor_cgroup_id" => Some(129),
        "bpf_ringbuf_output" => Some(constants::BPF_RINGBUF_OUTPUT),
        "bpf_ringbuf_reserve" => Some(constants::BPF_RINGBUF_RESERVE),
        "bpf_ringbuf_submit" => Some(constants::BPF_RINGBUF_SUBMIT),
        "bpf_ringbuf_discard" => Some(133),
        "bpf_ringbuf_query" => Some(134),
        "bpf_csum_level" => Some(135),
        "bpf_skc_to_tcp6_sock" => Some(136),
        "bpf_skc_to_tcp_sock" => Some(137),
        "bpf_skc_to_tcp_timewait_sock" => Some(138),
        "bpf_skc_to_tcp_request_sock" => Some(139),
        "bpf_skc_to_udp6_sock" => Some(constants::BPF_SKC_TO_UDP6_SOCK),
        "bpf_get_task_stack" => Some(constants::BPF_GET_TASK_STACK),
        "bpf_d_path" => Some(constants::BPF_D_PATH),
        "bpf_skc_to_unix_sock" => Some(constants::BPF_SKC_TO_UNIX_SOCK),
        _ => None,
    }
}

pub fn load_relocations<P: AsRef<Path>>(
    path: P,
    maps: &[BpfMapDef],
    target_section_name: &str,
) -> Result<HashMap<usize, RelocInfo>> {
    let buf = fs::read(path)?;
    let elf = Elf::parse(&buf)?;
    let mut pc_to_reloc = HashMap::new();

    let mut map_name_to_idx: HashMap<&str, usize> = HashMap::new();
    for (i, m) in maps.iter().enumerate() {
        map_name_to_idx.insert(m.name.as_str(), i);
    }

    let mut section_idx_to_map_idx: HashMap<usize, usize> = HashMap::new();
    for (sec_idx, sh) in elf.section_headers.iter().enumerate() {
        if let Some(name) = elf.shdr_strtab.get_at(sh.sh_name)
            && let Some(&map_idx) = map_name_to_idx.get(name)
        {
            section_idx_to_map_idx.insert(sec_idx, map_idx);
        }
    }

    let target_sec_idx = elf
        .section_headers
        .iter()
        .enumerate()
        .find(|(_, sh)| elf.shdr_strtab.get_at(sh.sh_name) == Some(target_section_name))
        .map(|(i, _)| i)
        .ok_or_else(|| anyhow::anyhow!("Section '{}' not found", target_section_name))?;

    for (reloc_sec_idx, section_relocs) in elf.shdr_relocs.iter() {
        let sh = &elf.section_headers[*reloc_sec_idx];
        if sh.sh_info as usize != target_sec_idx {
            continue;
        }

        for reloc in section_relocs {
            let pc = (reloc.r_offset / 8) as usize;
            let sym = match elf.syms.get(reloc.r_sym) {
                Some(s) => s,
                None => continue,
            };
            let name = elf.strtab.get_at(sym.st_name).unwrap_or("");

            // Check relocation type
            if reloc.r_type == R_BPF_64_32 {
                // Function call relocation - could be helper or BPF-to-BPF
                if let Some(helper_id) = helper_id_by_name(name) {
                    pc_to_reloc.insert(
                        pc,
                        RelocInfo {
                            map_idx: 0,
                            offset: 0,
                            helper_id,
                            kind: RelocKind::HelperCall,
                            bpf_call_target: None,
                        },
                    );
                } else if let Some((sec_name, offset, size)) =
                    resolve_symbol_location(&elf, &buf, name)
                {
                    // BPF-to-BPF call
                    pc_to_reloc.insert(
                        pc,
                        RelocInfo {
                            map_idx: 0,
                            offset: 0,
                            helper_id: 0,
                            kind: RelocKind::BpfCall,
                            bpf_call_target: Some(BpfCallTarget {
                                func_name: name.to_string(),
                                section: sec_name,
                                offset_in_section: offset,
                                size,
                            }),
                        },
                    );
                }
            } else if reloc.r_type == R_BPF_64_64 {
                // Map pointer/value relocation
                if let Some(&map_idx) = map_name_to_idx.get(name) {
                    pc_to_reloc.insert(
                        pc,
                        RelocInfo {
                            map_idx,
                            offset: 0,
                            helper_id: 0,
                            kind: RelocKind::MapPtr,
                            bpf_call_target: None,
                        },
                    );
                } else if let Some(&map_idx) = section_idx_to_map_idx.get(&sym.st_shndx) {
                    pc_to_reloc.insert(
                        pc,
                        RelocInfo {
                            map_idx,
                            offset: sym.st_value as i64,
                            helper_id: 0,
                            kind: RelocKind::MapValue,
                            bpf_call_target: None,
                        },
                    );
                }
            }
        }
    }
    Ok(pc_to_reloc)
}

/// Resolve a symbol name to its location (section name, offset within section, size).
/// Returns None if the symbol is not found or is not a function symbol in a valid section.
fn resolve_symbol_location(
    elf: &Elf,
    _buf: &[u8],
    symbol_name: &str,
) -> Option<(String, usize, usize)> {
    use goblin::elf::sym::STT_FUNC;

    // Find the symbol by name
    for sym in elf.syms.iter() {
        let name = elf.strtab.get_at(sym.st_name).unwrap_or("");
        if name != symbol_name {
            continue;
        }

        // Must be a function symbol
        if sym.st_type() != STT_FUNC {
            continue;
        }

        // Get the section name from section index
        if sym.st_shndx >= elf.section_headers.len() {
            continue;
        }

        let sh = &elf.section_headers[sym.st_shndx];
        let sec_name = elf.shdr_strtab.get_at(sh.sh_name)?;

        return Some((
            sec_name.to_string(),
            sym.st_value as usize,
            sym.st_size as usize,
        ));
    }

    None
}

/// Load relocations for a specific function within a section.
/// Adjusts PC values by subtracting the function's byte offset within the section.
pub fn load_relocations_for_function<P: AsRef<Path>>(
    path: P,
    maps: &[BpfMapDef],
    target_section_name: &str,
    func_byte_offset: usize,
    func_byte_size: usize,
) -> Result<HashMap<usize, RelocInfo>> {
    let buf = fs::read(path)?;
    let elf = Elf::parse(&buf)?;
    let mut pc_to_reloc = HashMap::new();

    let mut map_name_to_idx: HashMap<&str, usize> = HashMap::new();
    for (i, m) in maps.iter().enumerate() {
        map_name_to_idx.insert(m.name.as_str(), i);
    }

    let mut section_idx_to_map_idx: HashMap<usize, usize> = HashMap::new();
    for (sec_idx, sh) in elf.section_headers.iter().enumerate() {
        if let Some(name) = elf.shdr_strtab.get_at(sh.sh_name)
            && let Some(&map_idx) = map_name_to_idx.get(name)
        {
            section_idx_to_map_idx.insert(sec_idx, map_idx);
        }
    }

    let target_sec_idx = elf
        .section_headers
        .iter()
        .enumerate()
        .find(|(_, sh)| elf.shdr_strtab.get_at(sh.sh_name) == Some(target_section_name))
        .map(|(i, _)| i)
        .ok_or_else(|| anyhow::anyhow!("Section '{}' not found", target_section_name))?;

    // Calculate PC range for this function
    let func_start_pc = func_byte_offset / 8;
    let func_end_pc = (func_byte_offset + func_byte_size) / 8;

    for (reloc_sec_idx, section_relocs) in elf.shdr_relocs.iter() {
        let sh = &elf.section_headers[*reloc_sec_idx];
        if sh.sh_info as usize != target_sec_idx {
            continue;
        }

        for reloc in section_relocs {
            let section_pc = (reloc.r_offset / 8) as usize;

            // Only include relocations within this function's range
            if section_pc < func_start_pc || section_pc >= func_end_pc {
                continue;
            }

            // Adjust PC to be relative to function start
            let func_pc = section_pc - func_start_pc;

            let sym = match elf.syms.get(reloc.r_sym) {
                Some(s) => s,
                None => continue,
            };
            let name = elf.strtab.get_at(sym.st_name).unwrap_or("");

            // Check relocation type
            if reloc.r_type == R_BPF_64_32 {
                // Function call relocation - could be helper or BPF-to-BPF
                if let Some(helper_id) = helper_id_by_name(name) {
                    pc_to_reloc.insert(
                        func_pc,
                        RelocInfo {
                            map_idx: 0,
                            offset: 0,
                            helper_id,
                            kind: RelocKind::HelperCall,
                            bpf_call_target: None,
                        },
                    );
                } else if let Some((sec_name, offset, size)) =
                    resolve_symbol_location(&elf, &buf, name)
                {
                    // BPF-to-BPF call
                    pc_to_reloc.insert(
                        func_pc,
                        RelocInfo {
                            map_idx: 0,
                            offset: 0,
                            helper_id: 0,
                            kind: RelocKind::BpfCall,
                            bpf_call_target: Some(BpfCallTarget {
                                func_name: name.to_string(),
                                section: sec_name,
                                offset_in_section: offset,
                                size,
                            }),
                        },
                    );
                }
            } else if reloc.r_type == R_BPF_64_64 {
                // Map pointer/value relocation
                if let Some(&map_idx) = map_name_to_idx.get(name) {
                    pc_to_reloc.insert(
                        func_pc,
                        RelocInfo {
                            map_idx,
                            offset: 0,
                            helper_id: 0,
                            kind: RelocKind::MapPtr,
                            bpf_call_target: None,
                        },
                    );
                } else if let Some(&map_idx) = section_idx_to_map_idx.get(&sym.st_shndx) {
                    pc_to_reloc.insert(
                        func_pc,
                        RelocInfo {
                            map_idx,
                            offset: sym.st_value as i64,
                            helper_id: 0,
                            kind: RelocKind::MapValue,
                            bpf_call_target: None,
                        },
                    );
                }
            }
        }
    }
    Ok(pc_to_reloc)
}

/// Patch raw BPF instructions with relocation info.
/// This allows the lowerer (bpf_to_ast) to identify map pointers/values correctly.
pub fn apply_relocs(insns: &mut [RawBpfInsn], pc_to_reloc: &HashMap<usize, RelocInfo>) {
    for (&pc, reloc) in pc_to_reloc {
        if pc < insns.len() {
            let insn = &mut insns[pc];

            match reloc.kind {
                RelocKind::MapPtr | RelocKind::MapValue => {
                    // Must be a BPF_LD_IMM64 instruction (0x18)
                    if insn.code == 0x18 {
                        match reloc.kind {
                            RelocKind::MapPtr => {
                                insn.src = 1;
                                insn.imm = reloc.map_idx as i32;
                            }
                            RelocKind::MapValue => {
                                insn.src = 2;
                                insn.imm = reloc.map_idx as i32;
                                // The offset should be put in the continuation instruction's imm field
                                if pc + 1 < insns.len() {
                                    insns[pc + 1].imm = reloc.offset as i32;
                                }
                            }
                            _ => {}
                        }
                    }
                }
                RelocKind::HelperCall => {
                    // Must be a BPF_CALL instruction (0x85)
                    if insn.code == 0x85 {
                        // Convert from BPF_PSEUDO_CALL (src=1) to standard helper call (src=0)
                        insn.src = 0;
                        insn.imm = reloc.helper_id as i32;
                    }
                }
                RelocKind::BpfCall => {
                    // BPF-to-BPF call - the imm field will be fixed by combine_program_with_subprogs
                    // Here we just ensure src=1 (BPF_PSEUDO_CALL) is set for proper lowering
                    if insn.code == 0x85 {
                        insn.src = 1; // BPF_PSEUDO_CALL
                    }
                }
            }
        }
    }
}

/// Discover all BPF-to-BPF call targets for a given section.
pub fn discover_bpf_call_targets<P: AsRef<Path>>(
    path: P,
    target_section_name: &str,
) -> Result<Vec<BpfCallTarget>> {
    let buf = fs::read(&path)?;
    let elf = Elf::parse(&buf)?;
    let mut targets = Vec::new();

    let target_sec_idx = elf
        .section_headers
        .iter()
        .enumerate()
        .find(|(_, sh)| elf.shdr_strtab.get_at(sh.sh_name) == Some(target_section_name))
        .map(|(i, _)| i);

    let target_sec_idx = match target_sec_idx {
        Some(idx) => idx,
        None => return Ok(Vec::new()),
    };

    for (reloc_sec_idx, section_relocs) in elf.shdr_relocs.iter() {
        let sh = &elf.section_headers[*reloc_sec_idx];
        if sh.sh_info as usize != target_sec_idx {
            continue;
        }

        for reloc in section_relocs {
            if reloc.r_type != R_BPF_64_32 {
                continue;
            }

            let sym = match elf.syms.get(reloc.r_sym) {
                Some(s) => s,
                None => continue,
            };
            let name = elf.strtab.get_at(sym.st_name).unwrap_or("");

            // Skip helper functions
            if helper_id_by_name(name).is_some() {
                continue;
            }

            // Try to resolve as BPF function
            if let Some((sec_name, offset, size)) = resolve_symbol_location(&elf, &buf, name) {
                // Check if this is a cross-section call (target is in a different section)
                if sec_name != target_section_name {
                    targets.push(BpfCallTarget {
                        func_name: name.to_string(),
                        section: sec_name,
                        offset_in_section: offset,
                        size,
                    });
                }
            }
        }
    }

    // Remove duplicates (same function may be called multiple times)
    targets.sort_by(|a, b| (&a.section, &a.func_name).cmp(&(&b.section, &b.func_name)));
    targets.dedup_by(|a, b| a.func_name == b.func_name && a.section == b.section);

    Ok(targets)
}

/// Combined program with all subprograms appended
#[derive(Debug)]
pub struct CombinedProgram {
    pub raw_insns: Vec<RawBpfInsn>,
    pub pc_to_reloc: HashMap<usize, RelocInfo>,
    /// Maps function name to its start PC in the combined program
    pub func_offsets: HashMap<String, usize>,
}

/// Collect all sections referenced by cross-section calls, transitively.
fn collect_referenced_sections<P: AsRef<Path> + Clone>(
    path: P,
    main_section: &str,
) -> Result<Vec<String>> {
    let mut referenced = Vec::new();
    let mut visited = std::collections::HashSet::new();
    visited.insert(main_section.to_string());

    let mut to_process = vec![main_section.to_string()];

    while let Some(section) = to_process.pop() {
        let targets = discover_bpf_call_targets(&path, &section)?;

        for target in targets {
            if !visited.contains(&target.section) {
                visited.insert(target.section.clone());
                referenced.push(target.section.clone());
                to_process.push(target.section);
            }
        }
    }

    Ok(referenced)
}

/// Combine a program section with all its subprograms.
/// This follows libbpf's model: when a cross-section call is detected,
/// append ALL functions from the referenced section(s) and fix call targets.
pub fn combine_program_with_subprogs<P: AsRef<Path> + Clone>(
    path: P,
    maps: &[BpfMapDef],
    main_section: &str,
) -> Result<CombinedProgram> {
    use super::prog::{get_functions_in_section, load_bpf_insn_stream_section};
    use crate::parsing::bpf_insn::decode_insns;

    // Load main section instructions
    let main_bytes = load_bpf_insn_stream_section(&path, main_section)?;
    let mut combined_insns = decode_insns(&main_bytes);
    let mut func_offsets: HashMap<String, usize> = HashMap::new();

    // Load main section relocations
    let main_relocs = load_relocations(&path, maps, main_section)?;
    let mut combined_relocs = main_relocs;

    // Collect all sections that are referenced (transitively)
    let referenced_sections = collect_referenced_sections(&path, main_section)?;

    // For each referenced section, load ALL functions
    for ref_section in &referenced_sections {
        // Load the entire section's bytes
        let section_bytes = load_bpf_insn_stream_section(&path, ref_section)?;
        let section_start_pc = combined_insns.len();

        // Get all functions in this section to record their offsets
        let functions = get_functions_in_section(&path, ref_section)?;
        for func in &functions {
            // Compute the PC of this function in the combined program
            let func_pc = section_start_pc + (func.offset / 8);
            func_offsets.insert(func.name.clone(), func_pc);
        }

        // Decode and append all instructions from this section
        let section_insns = decode_insns(&section_bytes);

        // Load relocations for this entire section and adjust PCs
        let section_relocs = load_relocations(&path, maps, ref_section)?;
        for (sec_pc, reloc) in section_relocs {
            let combined_pc = section_start_pc + sec_pc;
            combined_relocs.insert(combined_pc, reloc);
        }

        combined_insns.extend(section_insns);
    }

    // Now fix all BPF call targets
    // For each BpfCall relocation, compute: imm = target_pc - (call_pc + 1)
    for (&call_pc, reloc) in combined_relocs.iter() {
        if reloc.kind == RelocKind::BpfCall
            && let Some(ref target) = reloc.bpf_call_target
            && let Some(&target_pc) = func_offsets.get(&target.func_name)
        {
            // Fix the imm field in the call instruction
            if call_pc < combined_insns.len() {
                let relative_offset = (target_pc as i32) - (call_pc as i32 + 1);
                combined_insns[call_pc].imm = relative_offset;
                combined_insns[call_pc].src = 1; // BPF_PSEUDO_CALL
            }
        }
    }

    // Apply other relocations (maps, helpers)
    apply_relocs(&mut combined_insns, &combined_relocs);

    Ok(CombinedProgram {
        raw_insns: combined_insns,
        pc_to_reloc: combined_relocs,
        func_offsets,
    })
}
