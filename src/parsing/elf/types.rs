#[derive(Clone, Debug)]
pub struct BpfMapDef {
    pub type_: u32,
    pub key_size: u32,
    pub value_size: u32,
    #[allow(dead_code)]
    pub max_entries: u32,
    pub map_flags: u32,
    pub name: String,
    pub btf_val_type_id: Option<u32>,
    pub initial_data: Option<Vec<u8>>,
}

/// Represents a raw BPF program extracted from the ELF symbol table.
#[derive(Debug)]
pub struct RawBpfProgram {
    pub name: String,
    pub data: Vec<u8>,      // The raw bytecode slice
    pub section_idx: usize, // Which ELF section it lives in
    #[allow(dead_code)]
    pub file_offset: u64, // Absolute offset in the file
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelocKind {
    MapPtr,
    MapValue,
}

#[derive(Clone, Debug)]
pub struct RelocInfo {
    pub map_idx: usize,
    pub offset: i64,
    pub kind: RelocKind,
}
