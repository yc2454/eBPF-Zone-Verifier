#![allow(dead_code)]

// src/btf.rs
use crate::parsing::elf::BpfMapDef;
use log::info;
use std::collections::HashMap;
use std::convert::TryInto;

const BTF_MAGIC: u16 = 0xeB9F;

// Kinds
pub const BTF_KIND_INT: u8 = 1;
pub const BTF_KIND_PTR: u8 = 2;
pub const BTF_KIND_ARRAY: u8 = 3;
pub const BTF_KIND_STRUCT: u8 = 4;
pub const BTF_KIND_UNION: u8 = 5;
pub const BTF_KIND_ENUM: u8 = 6;
pub const BTF_KIND_FWD: u8 = 7;
pub const BTF_KIND_TYPEDEF: u8 = 8;
pub const BTF_KIND_VOLATILE: u8 = 9;
pub const BTF_KIND_CONST: u8 = 10;
pub const BTF_KIND_RESTRICT: u8 = 11;
pub const BTF_KIND_FUNC: u8 = 12;
pub const BTF_KIND_FUNC_PROTO: u8 = 13;
pub const BTF_KIND_VAR: u8 = 14;
pub const BTF_KIND_DATASEC: u8 = 15;
pub const BTF_KIND_FLOAT: u8 = 16;
pub const BTF_KIND_DECL_TAG: u8 = 17;
pub const BTF_KIND_TYPE_TAG: u8 = 18;
pub const BTF_KIND_ENUM64: u8 = 19;

// -----------------------------------------------------------------------------
// PART 1: Public Interface for Analyzer (The "Context" view)
// -----------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecialFieldKind {
    SpinLock,
    Timer,
    ListHead,
    ListNode,
    RbRoot,
    RbNode,
    Refcount,
    // Future types...
}

#[derive(Debug, Clone)]
pub struct SpecialField {
    pub kind: SpecialFieldKind,
    pub offset: u32, // byte offset
    pub size: u32,
}

impl SpecialFieldKind {
    fn from_type_name(name: &str) -> Option<Self> {
        match name {
            "bpf_spin_lock" => Some(Self::SpinLock),
            "bpf_timer" => Some(Self::Timer),
            "bpf_list_head" => Some(Self::ListHead),
            "bpf_list_node" => Some(Self::ListNode),
            "bpf_rb_root" => Some(Self::RbRoot),
            "bpf_rb_node" => Some(Self::RbNode),
            "bpf_refcount" => Some(Self::Refcount),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct BtfMember {
    pub name_off: u32,
    pub type_id: u32,
    pub offset: u32, // Offset in bits
}

#[derive(Debug, Clone)]
pub struct BtfType {
    pub id: u32,
    pub name_off: u32,
    pub info: u32,
    pub size_or_type: u32,
    pub members: Vec<BtfMember>,
}

impl BtfType {
    pub fn kind(&self) -> u8 {
        ((self.info >> 24) & 0x1f) as u8
    }
}

#[derive(Clone, Default, Debug)]
pub struct BtfContext {
    pub types: HashMap<u32, BtfType>,
    pub strings: Vec<u8>,
}

impl BtfContext {
    pub fn new() -> Self {
        BtfContext {
            types: HashMap::new(),
            strings: Vec::new(),
        }
    }

    /// Looks up a struct member at a specific byte offset.
    /// Returns the Type ID of that member if found.
    pub fn resolve_field_type_id(&self, struct_id: u32, byte_offset: u32) -> Option<u32> {
        let bit_offset = byte_offset * 8;

        if let Some(ty) = self.types.get(&struct_id) {
            match ty.kind() {
                BTF_KIND_STRUCT | BTF_KIND_UNION => {
                    for member in &ty.members {
                        // Exact match for now
                        if member.offset == bit_offset {
                            return Some(member.type_id);
                        }
                    }
                }
                // Handle typedefs/const/volatile by peeling the wrapper
                BTF_KIND_TYPEDEF | BTF_KIND_VOLATILE | BTF_KIND_CONST | BTF_KIND_RESTRICT => {
                    return self.resolve_field_type_id(ty.size_or_type, byte_offset);
                }
                _ => {}
            }
        }
        None
    }

    /// Helper to check if a type ID effectively resolves to a Pointer.
    pub fn is_pointer(&self, mut type_id: u32) -> bool {
        let mut depth = 0;
        while let Some(ty) = self.types.get(&type_id) {
            let kind = ty.kind();
            match kind {
                BTF_KIND_PTR => return true,
                BTF_KIND_TYPEDEF | BTF_KIND_VOLATILE | BTF_KIND_CONST | BTF_KIND_RESTRICT => {
                    type_id = ty.size_or_type;
                }
                _ => return false,
            }
            depth += 1;
            if depth > 10 {
                break;
            } // Prevent loops
        }
        false
    }

    /// Find all special fields in a struct type
    pub fn find_special_fields(&self, type_id: u32) -> Vec<SpecialField> {
        let mut fields = Vec::new();

        let Some(ty) = self.types.get(&type_id) else {
            return fields;
        };

        for member in &ty.members {
            let Some(member_type) = self.types.get(&member.type_id) else {
                continue;
            };
            let Some(name) = self.get_string(member_type.name_off) else {
                continue;
            };

            if let Some(kind) = SpecialFieldKind::from_type_name(name) {
                fields.push(SpecialField {
                    kind,
                    offset: member.offset / 8,
                    size: member_type.size_or_type,
                });
            }
        }

        fields
    }

    fn get_string(&self, offset: u32) -> Option<&str> {
        let start = offset as usize;
        if start >= self.strings.len() {
            return None;
        }
        let end = self.strings[start..].iter().position(|&b| b == 0)? + start;
        std::str::from_utf8(&self.strings[start..end]).ok()
    }
}

/// Parses the .BTF section into a structured Context for analysis
pub fn parse_btf(bytes: &[u8]) -> Result<BtfContext, String> {
    if bytes.len() < 24 {
        return Err("BTF too short".into());
    }

    let hdr_len = u32::from_le_bytes(bytes[4..8].try_into().unwrap());
    let type_off = u32::from_le_bytes(bytes[8..12].try_into().unwrap());
    let type_len = u32::from_le_bytes(bytes[12..16].try_into().unwrap());
    let str_off = u32::from_le_bytes(bytes[16..20].try_into().unwrap());
    let str_len = u32::from_le_bytes(bytes[20..24].try_into().unwrap());

    let type_start = (hdr_len + type_off) as usize;
    let type_end = type_start + type_len as usize;
    let str_start = (hdr_len + str_off) as usize;
    let str_end = str_start + str_len as usize;

    if type_end > bytes.len() || str_end > bytes.len() {
        return Err("BTF sections out of bounds".into());
    }

    let strings = bytes[str_start..str_end].to_vec();
    let mut types = HashMap::new();
    let mut cursor = type_start;
    let mut type_id = 1;

    while cursor < type_end {
        if cursor + 12 > type_end {
            break;
        }

        let name_off = u32::from_le_bytes(bytes[cursor..cursor + 4].try_into().unwrap());
        let info = u32::from_le_bytes(bytes[cursor + 4..cursor + 8].try_into().unwrap());
        let size_or_type = u32::from_le_bytes(bytes[cursor + 8..cursor + 12].try_into().unwrap());
        cursor += 12;

        let kind = ((info >> 24) & 0x1f) as u8;
        let vlen = (info & 0xffff) as usize;
        let mut members = Vec::new();

        // Extract extra data based on Kind
        match kind {
            BTF_KIND_STRUCT | BTF_KIND_UNION => {
                for _ in 0..vlen {
                    if cursor + 12 > type_end {
                        break;
                    }
                    let m_name = u32::from_le_bytes(bytes[cursor..cursor + 4].try_into().unwrap());
                    let m_type =
                        u32::from_le_bytes(bytes[cursor + 4..cursor + 8].try_into().unwrap());
                    let m_off =
                        u32::from_le_bytes(bytes[cursor + 8..cursor + 12].try_into().unwrap());
                    cursor += 12;
                    members.push(BtfMember {
                        name_off: m_name,
                        type_id: m_type,
                        offset: m_off,
                    });
                }
            }
            BTF_KIND_INT => {
                cursor += 4;
            }
            BTF_KIND_ARRAY => {
                cursor += 12;
            }
            BTF_KIND_VAR => {
                cursor += 4;
            }
            BTF_KIND_DATASEC | BTF_KIND_ENUM64 => {
                cursor += vlen * 12;
            }
            BTF_KIND_ENUM | BTF_KIND_FUNC_PROTO => {
                cursor += vlen * 8;
            }
            BTF_KIND_DECL_TAG => {
                cursor += 4;
            }
            _ => {}
        }

        types.insert(
            type_id,
            BtfType {
                id: type_id,
                name_off,
                info,
                size_or_type,
                members,
            },
        );

        type_id += 1;
    }

    Ok(BtfContext { types, strings })
}

// -----------------------------------------------------------------------------
// PART 2: Helper Interface for Map Loader (Your existing logic)
// -----------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct BtfTypeRaw {
    name_off: u32,
    info: u32,
    size_or_type: u32,
    data: Vec<u8>,
}

impl BtfTypeRaw {
    fn kind(&self) -> u8 {
        ((self.info >> 24) & 0x1f) as u8
    }
    fn vlen(&self) -> u32 {
        self.info & 0xffff
    }
}

pub fn parse_btf_map_defs(bytes: &[u8]) -> Result<Vec<BpfMapDef>, String> {
    if bytes.len() < 24 {
        return Err("BTF too short".into());
    }

    let hdr_len = u32::from_le_bytes(bytes[4..8].try_into().unwrap());
    let type_off = u32::from_le_bytes(bytes[8..12].try_into().unwrap());
    let type_len = u32::from_le_bytes(bytes[12..16].try_into().unwrap());
    let str_off = u32::from_le_bytes(bytes[16..20].try_into().unwrap());
    let str_len = u32::from_le_bytes(bytes[20..24].try_into().unwrap());

    let type_start = (hdr_len + type_off) as usize;
    let type_end = type_start + type_len as usize;
    let str_start = (hdr_len + str_off) as usize;
    let str_end = str_start + str_len as usize;

    if type_end > bytes.len() || str_end > bytes.len() {
        return Err("BTF sections out of bounds".into());
    }

    // Parse Types purely for Map Discovery
    let mut types = Vec::new();
    types.push(BtfTypeRaw {
        name_off: 0,
        info: 0,
        size_or_type: 0,
        data: vec![],
    }); // ID 0

    let mut cursor = type_start;
    while cursor < type_end {
        if cursor + 12 > bytes.len() {
            break;
        }

        let name_off = u32::from_le_bytes(bytes[cursor..cursor + 4].try_into().unwrap());
        let info = u32::from_le_bytes(bytes[cursor + 4..cursor + 8].try_into().unwrap());
        let size_or_type = u32::from_le_bytes(bytes[cursor + 8..cursor + 12].try_into().unwrap());
        cursor += 12;

        let kind = ((info >> 24) & 0x1f) as u8;
        let vlen = (info & 0xffff) as usize;

        let extra = match kind {
            BTF_KIND_INT => 4,
            BTF_KIND_ARRAY => 12,
            BTF_KIND_STRUCT | BTF_KIND_UNION => vlen * 12,
            BTF_KIND_ENUM => vlen * 8,
            BTF_KIND_FUNC_PROTO => vlen * 8,
            BTF_KIND_VAR => 4,
            BTF_KIND_DATASEC => vlen * 12,
            BTF_KIND_DECL_TAG => 4,
            BTF_KIND_ENUM64 => vlen * 12,
            _ => 0,
        };

        if cursor + extra > bytes.len() {
            break;
        }
        let data = bytes[cursor..cursor + extra].to_vec();
        cursor += extra;

        types.push(BtfTypeRaw {
            name_off,
            info,
            size_or_type,
            data,
        });
    }

    let get_str = |off: u32| -> String {
        let start = str_start + off as usize;
        if start >= bytes.len() {
            return String::new();
        }
        let slice = &bytes[start..];
        slice
            .iter()
            .take_while(|&&c| c != 0)
            .map(|&c| c as char)
            .collect()
    };

    // Helper to extract __uint values from BTF map definitions
    // __uint(name, val) creates a pointer to an array[val] in BTF
    fn extract_btf_uint(types: &[BtfTypeRaw], type_id: u32) -> Option<u32> {
        let mut curr_id = type_id;
        let mut depth = 0;

        while depth < 5 && (curr_id as usize) < types.len() {
            let t = &types[curr_id as usize];
            match t.kind() {
                BTF_KIND_PTR => {
                    // Follow the pointer
                    curr_id = t.size_or_type;
                }
                BTF_KIND_ARRAY => {
                    // The value is encoded in nelems
                    if t.data.len() >= 12 {
                        let nelems = u32::from_le_bytes(t.data[8..12].try_into().unwrap());
                        return Some(nelems);
                    }
                    return None;
                }
                BTF_KIND_TYPEDEF | BTF_KIND_CONST | BTF_KIND_VOLATILE | BTF_KIND_RESTRICT => {
                    curr_id = t.size_or_type;
                }
                _ => return None,
            }
            depth += 1;
        }
        None
    }

    fn get_resolved_size(types: &[BtfTypeRaw], type_id: u32, depth: u32) -> u32 {
        if depth > 5 || type_id == 0 || (type_id as usize) >= types.len() {
            return 0;
        }
        let t = &types[type_id as usize];
        match t.kind() {
            BTF_KIND_INT | BTF_KIND_STRUCT | BTF_KIND_UNION | BTF_KIND_FLOAT | BTF_KIND_ENUM => {
                t.size_or_type
            }
            BTF_KIND_ARRAY => {
                if t.data.len() >= 12 {
                    let elem_t = u32::from_le_bytes(t.data[0..4].try_into().unwrap());
                    let nelems = u32::from_le_bytes(t.data[8..12].try_into().unwrap());
                    get_resolved_size(types, elem_t, depth + 1) * nelems
                } else {
                    0
                }
            }
            BTF_KIND_PTR => 8,
            BTF_KIND_TYPEDEF | BTF_KIND_VOLATILE | BTF_KIND_CONST | BTF_KIND_RESTRICT
            | BTF_KIND_VAR | BTF_KIND_TYPE_TAG => {
                get_resolved_size(types, t.size_or_type, depth + 1)
            }
            _ => 0,
        }
    }

    let mut map_defs = Vec::new();
    info!(target: "app", "Scanning {} BTF types for Maps...", types.len());

    for (_i, t) in types.iter().enumerate() {
        if t.kind() == BTF_KIND_VAR {
            let name = get_str(t.name_off);
            let def_id = t.size_or_type;

            if (def_id as usize) < types.len() {
                // Follow typedef chain to get to the underlying type
                let mut resolved_id = def_id;
                let mut resolved_t = &types[def_id as usize];
                while resolved_t.kind() == BTF_KIND_TYPEDEF && (resolved_t.size_or_type as usize) < types.len() {
                    resolved_id = resolved_t.size_or_type;
                    resolved_t = &types[resolved_id as usize];
                }
                let def_t = resolved_t;
                if def_t.kind() == BTF_KIND_STRUCT {
                    let mut is_map = false;
                    let mut value_size = 0;
                    let mut key_size = 0;
                    let mut max_entries = 0;
                    let mut map_type = 0u32;
                    let mut btf_val_type_id = None; // STORE THIS!

                    let members = def_t.vlen() as usize;
                    let mut m_cursor = 0;

                    for _ in 0..members {
                        if m_cursor + 12 > def_t.data.len() {
                            break;
                        }
                        let m_name_off = u32::from_le_bytes(
                            def_t.data[m_cursor..m_cursor + 4].try_into().unwrap(),
                        );
                        let m_type_id = u32::from_le_bytes(
                            def_t.data[m_cursor + 4..m_cursor + 8].try_into().unwrap(),
                        );
                        m_cursor += 12;

                        let m_name = get_str(m_name_off);
                        if m_name == "key" || m_name == "value" || m_name == "values" {
                            is_map = true;

                            let mut actual_type_id = m_type_id;
                            if (actual_type_id as usize) < types.len() {
                                let field_t = &types[actual_type_id as usize];
                                if field_t.kind() == BTF_KIND_PTR {
                                    actual_type_id = field_t.size_or_type;
                                }
                            }
                            let size = get_resolved_size(&types, actual_type_id, 0);

                            if m_name == "value" {
                                value_size = size;
                                btf_val_type_id = Some(actual_type_id);
                            } else if m_name == "values" {
                                // For map-in-map (ARRAY_OF_MAPS/HASH_OF_MAPS), the "values" field
                                // points to inner maps. The value_size is the size of a map pointer (4 bytes).
                                value_size = 4;
                            } else {
                                key_size = size;
                            }
                        } else if m_name == "type" {
                            // Extract map type from the BTF
                            // The member type might be a PTR to an ARRAY where nelems encodes the value
                            if let Some(val) = extract_btf_uint(&types, m_type_id) {
                                map_type = val;
                            }
                        } else if m_name == "max_entries" {
                            // Extract max_entries - similar encoding as type
                            if let Some(val) = extract_btf_uint(&types, m_type_id) {
                                max_entries = val;
                            }
                        }
                    }

                    if is_map && value_size > 0 {
                        info!(target: "app", "[BTF] Found Map: '{}' (Type: {}, KeySize: {}, ValSize: {}, MaxEntries: {}, TypeID: {:?})",
                            name, map_type, key_size, value_size, max_entries, btf_val_type_id);
                        map_defs.push(BpfMapDef {
                            name: name.clone(),
                            type_: map_type,
                            key_size,
                            value_size,
                            max_entries,
                            map_flags: 0,
                            btf_val_type_id,
                            initial_data: None, // No initial data here
                        });
                    }
                }
            }
        }
    }

    Ok(map_defs)
}
