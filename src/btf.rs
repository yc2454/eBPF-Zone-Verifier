// src/btf.rs
use std::convert::TryInto;
use crate::domain::BpfMapDef;

const BTF_MAGIC: u16 = 0xeB9F;

// Kinds
const BTF_KIND_INT: u8 = 1;
const BTF_KIND_PTR: u8 = 2;
const BTF_KIND_ARRAY: u8 = 3;
const BTF_KIND_STRUCT: u8 = 4;
const BTF_KIND_UNION: u8 = 5;
const BTF_KIND_ENUM: u8 = 6;
const BTF_KIND_FWD: u8 = 7;
const BTF_KIND_TYPEDEF: u8 = 8;
const BTF_KIND_VOLATILE: u8 = 9;
const BTF_KIND_CONST: u8 = 10;
const BTF_KIND_RESTRICT: u8 = 11;
const BTF_KIND_FUNC: u8 = 12;
const BTF_KIND_FUNC_PROTO: u8 = 13;
const BTF_KIND_VAR: u8 = 14;
const BTF_KIND_DATASEC: u8 = 15;
const BTF_KIND_FLOAT: u8 = 16;
const BTF_KIND_DECL_TAG: u8 = 17;
const BTF_KIND_TYPE_TAG: u8 = 18;
const BTF_KIND_ENUM64: u8 = 19;

#[derive(Debug, Clone)]
struct BtfTypeRaw {
    name_off: u32,
    info: u32,
    size_or_type: u32,
    data: Vec<u8>, 
}

impl BtfTypeRaw {
    fn kind(&self) -> u8 { ((self.info >> 24) & 0x1f) as u8 }
    fn vlen(&self) -> u32 { self.info & 0xffff }
}

pub fn parse_btf_map_defs(bytes: &[u8]) -> Result<Vec<BpfMapDef>, String> {
    if bytes.len() < 24 { return Err("BTF too short".into()); }

    // 1. Parse Header
    let magic = u16::from_le_bytes(bytes[0..2].try_into().unwrap());
    if magic != BTF_MAGIC { return Err("Invalid BTF magic".into()); }
    
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

    // 2. Parse Types
    let mut types = Vec::new();
    // BTF Type IDs are 1-based. 0 is VOID.
    types.push(BtfTypeRaw { name_off: 0, info: 0, size_or_type: 0, data: vec![] });

    let mut cursor = type_start;
    while cursor < type_end {
        if cursor + 12 > bytes.len() { break; }
        
        let name_off = u32::from_le_bytes(bytes[cursor..cursor+4].try_into().unwrap());
        let info = u32::from_le_bytes(bytes[cursor+4..cursor+8].try_into().unwrap());
        let size_or_type = u32::from_le_bytes(bytes[cursor+8..cursor+12].try_into().unwrap());
        cursor += 12;

        let kind = ((info >> 24) & 0x1f) as u8;
        let vlen = (info & 0xffff) as usize;

        // Calculate size of additional data based on Kind
        let extra = match kind {
            BTF_KIND_INT => 4,
            BTF_KIND_ARRAY => 12,
            BTF_KIND_STRUCT | BTF_KIND_UNION => vlen * 12, // members
            BTF_KIND_ENUM => vlen * 8,                     // enum entries
            BTF_KIND_FUNC_PROTO => vlen * 8,               // args
            BTF_KIND_VAR => 4,
            BTF_KIND_DATASEC => vlen * 12,                 // vars
            BTF_KIND_DECL_TAG => 4,
            BTF_KIND_ENUM64 => vlen * 12,
            _ => 0, // PTR, TYPEDEF, VOLATILE, CONST, etc. have no extra data
        };

        if cursor + extra > bytes.len() { break; }
        let data = bytes[cursor..cursor+extra].to_vec();
        cursor += extra;

        types.push(BtfTypeRaw { name_off, info, size_or_type, data });
    }

    // Helper: Strings
    let get_str = |off: u32| -> String {
        let start = str_start + off as usize;
        if start >= bytes.len() { return String::new(); }
        let slice = &bytes[start..];
        slice.iter().take_while(|&&c| c != 0).map(|&c| c as char).collect()
    };

    // Helper: Size Resolution
    fn get_resolved_size(types: &[BtfTypeRaw], type_id: u32, depth: u32) -> u32 {
        if depth > 5 || type_id == 0 || (type_id as usize) >= types.len() { return 0; }
        let t = &types[type_id as usize];
        match t.kind() {
            BTF_KIND_INT | BTF_KIND_STRUCT | BTF_KIND_UNION | BTF_KIND_FLOAT | BTF_KIND_ENUM => t.size_or_type,
            BTF_KIND_ARRAY => {
                if t.data.len() >= 12 {
                    let elem_t = u32::from_le_bytes(t.data[0..4].try_into().unwrap());
                    let nelems = u32::from_le_bytes(t.data[8..12].try_into().unwrap());
                    get_resolved_size(types, elem_t, depth+1) * nelems
                } else { 0 }
            }
            BTF_KIND_PTR => 8,
            BTF_KIND_TYPEDEF | BTF_KIND_VOLATILE | BTF_KIND_CONST | BTF_KIND_RESTRICT | BTF_KIND_VAR | BTF_KIND_TYPE_TAG => {
                get_resolved_size(types, t.size_or_type, depth+1)
            }
            _ => 0,
        }
    }

    // 3. Scan for Maps (Strategy: Look for all VARs, regardless of DATASEC)
    let mut map_defs = Vec::new();

    println!("Scanning {} BTF types...", types.len());

    for t in &types {
        if t.kind() == BTF_KIND_VAR {
            let name = get_str(t.name_off);
            
            let def_id = t.size_or_type;
            if (def_id as usize) < types.len() {
                let def_t = &types[def_id as usize];
                
                if def_t.kind() == BTF_KIND_STRUCT {
                    let mut is_map = false;
                    let mut value_size = 0;
                    let mut key_size = 0;
                    let mut max_entries = 0;

                    let members = def_t.vlen() as usize;
                    let mut m_cursor = 0;
                    
                    for _ in 0..members {
                        if m_cursor + 12 > def_t.data.len() { break; }
                        let m_name_off = u32::from_le_bytes(def_t.data[m_cursor..m_cursor+4].try_into().unwrap());
                        let m_type_id = u32::from_le_bytes(def_t.data[m_cursor+4..m_cursor+8].try_into().unwrap());
                        m_cursor += 12;

                        let m_name = get_str(m_name_off);
                        
                        // --- FIX STARTS HERE ---
                        if m_name == "key" || m_name == "value" {
                            is_map = true;
                            
                            // Check if the type is a Pointer. If so, strip it to get the actual struct size.
                            let mut actual_type_id = m_type_id;
                            if (actual_type_id as usize) < types.len() {
                                let field_t = &types[actual_type_id as usize];
                                if field_t.kind() == BTF_KIND_PTR {
                                    actual_type_id = field_t.size_or_type;
                                }
                            }

                            let size = get_resolved_size(&types, actual_type_id, 0);
                            
                            if m_name == "value" { value_size = size; }
                            else { key_size = size; }
                        }
                        // --- FIX ENDS HERE ---
                        
                        else if m_name == "max_entries" {
                             // max_entries logic (less critical)
                        }
                    }

                    if is_map && value_size > 0 {
                        println!("[BTF] Found Map: '{}' (Key: {}, Value: {})", name, key_size, value_size);
                        map_defs.push(BpfMapDef {
                            name: name.clone(),
                            type_: 0,
                            key_size,
                            value_size,
                            max_entries,
                            map_flags: 0,
                        });
                    }
                }
            }
        }
    }

    Ok(map_defs)
}
