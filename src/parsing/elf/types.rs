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
    pub inner_map_idx: Option<usize>,
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
    /// Helper function call - resolve helper name to ID
    HelperCall,
    /// BPF-to-BPF function call - cross-section call
    BpfCall,
}

/// Target information for a BPF-to-BPF function call
#[derive(Clone, Debug)]
pub struct BpfCallTarget {
    /// Name of the target function
    pub func_name: String,
    /// Section containing the target function
    pub section: String,
    /// Offset of the function within its section (in bytes)
    pub offset_in_section: usize,
    /// Size of the function (in bytes)
    pub size: usize,
}

#[derive(Clone, Debug)]
pub struct RelocInfo {
    /// Map index (for MapPtr/MapValue)
    pub map_idx: usize,
    /// Offset within map value (for MapValue)
    pub offset: i64,
    /// Helper function ID (for HelperCall)
    pub helper_id: u32,
    pub kind: RelocKind,
    /// BPF call target info (for BpfCall)
    pub bpf_call_target: Option<BpfCallTarget>,
}
