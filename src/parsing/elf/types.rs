#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KptrFieldKind {
    /// `__kptr_untrusted` — unreferenced kptr. Loaded value is
    /// `PtrToUntrustedKptrOrNull` and must be NULL-checked / ptr-cast'd
    /// before use; cannot be stored back as a referenced kptr.
    Unref,
    /// `__kptr` — referenced kptr (refcounted). Direct stores are
    /// disallowed; mutation is via `bpf_kptr_xchg`. Load yields
    /// `PtrToRefKptrOrNull` (still ref-tracked through xchg semantics).
    Ref,
    /// `__rcu` (with kptr) — RCU-protected referenced kptr. Loaded
    /// value carries MEM_RCU and is `PtrToRcuKptrOrNull`.
    Rcu,
    /// `percpu_kptr` — referenced percpu kptr. Loaded value is
    /// `PtrToPercpuKptrOrNull` and must be passed through
    /// `bpf_per_cpu_ptr` / `bpf_this_cpu_ptr` before deref.
    Percpu,
}

#[derive(Clone, Debug)]
pub struct KptrField {
    /// Byte offset of the field within the map value struct.
    pub offset: u32,
    pub kind: KptrFieldKind,
    /// BTF type id of the *pointee* struct (the inner type that the
    /// `__kptr*` PTR points to). Used for type-matching in
    /// `bpf_kptr_xchg` and pointee-struct bounds checks on deref.
    pub pointee_btf_id: u32,
}

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
    /// kptr fields embedded in the map value struct, extracted from BTF
    /// TYPE_TAGs (`kptr`, `kptr_untrusted`, `rcu`, `percpu_kptr`).
    /// Empty for legacy maps and data-section maps. See
    /// `parse_btf_map_defs` for population.
    pub kptr_fields: Vec<KptrField>,
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
    /// Kfunc call against a name we recognize via `signatures::get_kfunc_proto`.
    /// Apply rewrites the call as BPF_PSEUDO_KFUNC_CALL (src=2) with a
    /// synthesized btf_id; the runner then registers the name → id mapping
    /// into the analysis-context BTF so the kfunc dispatcher can route it.
    KfuncCall,
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
    /// Helper function ID (for HelperCall) or synthesized btf_id (for KfuncCall).
    pub helper_id: u32,
    pub kind: RelocKind,
    /// BPF call target info (for BpfCall)
    pub bpf_call_target: Option<BpfCallTarget>,
    /// Kfunc symbol name (for KfuncCall). Used by the runner to register
    /// the synth `helper_id` into the analysis-context BTF before analysis.
    pub kfunc_name: Option<String>,
}
