// src/analysis/context.rs
use crate::ast::{AttachKind, ProgramKind};
use crate::parsing::btf::BtfContext;
use crate::parsing::elf::{BpfMapDef, RelocInfo};
use std::collections::{HashMap, HashSet};

/// Per-argument entry-state typing for a struct_ops subprog (W6.4a).
///
/// Captured by the runner once a `SEC("struct_ops*")` subprog has been
/// matched against its ops-struct member binding (see
/// `src/parsing/elf/struct_ops.rs` + `BtfContext::resolve_struct_ops_method`).
/// `analyze_program_full` consumes this when seeding R1..Rn in place of
/// the default `R1 = PtrToCtx`.
#[derive(Debug, Clone)]
pub enum EntryArg {
    Scalar,
    /// Trusted pointer to a named kernel struct. The string is interned
    /// via `intern_btf_type_name` so it satisfies the `&'static str`
    /// requirement of `RegType::PtrToBtfId`. `nullable` is set by the
    /// runner from the W6.4c `STRUCT_OPS_MAYBE_NULL_ARGS` table —
    /// some struct_ops callbacks declare specific args as PTR_MAYBE_NULL
    /// (e.g. `sched_ext_ops.dispatch`'s `prev`), and the program is
    /// required to null-check before deref. When true, the entry-arg
    /// ctx-load idiom in `validate_ctx_access` produces
    /// `RegType::PtrToBtfIdOrNull` instead of `PtrToBtfId`.
    TrustedPtrBtfId {
        type_name: &'static str,
        nullable: bool,
    },
}

/// Intern a kernel struct/union name resolved from BTF into a `&'static
/// str`. Returns the interned literal *only* for names with a registered
/// memory-region layout in `mem_region_model::BPF_MAP_FIELDS` and friends.
/// For any other name, returns `"unknown"` — the sentinel that
/// `transfer/memory/access.rs` recognizes to skip per-field bounds
/// checking (because we have no layout to check against).
///
/// Why "unknown" by default: the access pass treats a known PtrToBtfId
/// type as "I have a layout for this struct, prove the access is in
/// bounds" — and rejects when the layout lookup fails. For struct_ops
/// args (and any other resolved-from-BTF pointer we don't have a layout
/// for) we want the kernel-verifier behavior of "typed pointer, no
/// per-field validation" rather than a hard reject. As we add
/// mem_region_model entries for specific kernel structs, move them out
/// of the catch-all by adding an explicit arm here.
///
/// Why a fixed table instead of a runtime interner: every entry here is
/// referenced from `RegType::PtrToBtfId { type_name: &'static str, .. }`,
/// and we deliberately avoid a leak-based interner.
pub fn intern_btf_type_name(_name: &str) -> &'static str {
    // No specific mem_region_model entries exist for struct_ops args yet
    // (sock, tcp_sock, task_struct, ...). When one is added, add a
    // matching arm below; until then, the catch-all is correct.
    //
    // Specifically: callers that need a *real* type_name (kfunc
    // ArgKind matchers like `validate_ptr_to_task` keyed on
    // `type_name == "task_struct"`) use `intern_btf_type_name_strict`
    // instead. Returning "unknown" by default preserves the lax
    // mem_region_model::is_valid_mem_region_read fall-through that
    // struct_ops field stores depend on (e.g. `bictcp` writes through
    // a `struct sock *` arg).
    "unknown"
}

/// Strict interner for callers that need the real BTF type_name to
/// flow into a `RegType::PtrToBtfId { type_name, .. }`. Used by the
/// BPF_PROG-style entry-arg seeders for LSM/tp_btf/tracing programs
/// where downstream kfunc validators (`bpf_get_task_exe_file` →
/// `validate_ptr_to_task` matching `"task_struct"`) need the actual
/// name. The leak-based cache keeps the same `name` round-tripping
/// through one `&'static str` so callers can compare with `==`.
///
/// Bounded by the number of distinct names referenced in any one
/// verified ELF (typically dozens). Not used by the struct_ops entry
/// seeder, which keeps `intern_btf_type_name` → "unknown" so the
/// lax mem-region policy still applies to its writes.
pub fn intern_btf_type_name_strict(name: &str) -> &'static str {
    match name {
        // Hot-path string literals for names already referenced by
        // existing kfunc matchers — keeps the LSM entry seeding
        // allocation-free.
        "task_struct" => return "task_struct",
        "file" => return "file",
        "path" => return "path",
        "sock" => return "sock",
        "sk_buff" => return "sk_buff",
        "sk_buff_head" => return "sk_buff_head",
        "sock_common" => return "sock_common",
        "tcp_sock" => return "tcp_sock",
        "cpumask" => return "cpumask",
        "bpf_cpumask" => return "bpf_cpumask",
        "cgroup" => return "cgroup",
        "bpf_key" => return "bpf_key",
        "inode" => return "inode",
        "cred" => return "cred",
        "dentry" => return "dentry",
        "socket" => return "socket",
        "sockaddr" => return "sockaddr",
        "linux_binprm" => return "linux_binprm",
        "vm_area_struct" => return "vm_area_struct",
        _ => {}
    }
    use std::collections::HashMap;
    use std::sync::{Mutex, OnceLock};
    static CACHE: OnceLock<Mutex<HashMap<String, &'static str>>> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let mut g = cache.lock().expect("intern cache poisoned");
    if let Some(&s) = g.get(name) {
        return s;
    }
    let leaked: &'static str = Box::leak(name.to_string().into_boxed_str());
    g.insert(name.to_string(), leaked);
    leaked
}

#[derive(Clone, Debug)]
#[allow(dead_code)]
pub enum VerificationMode {
    Priviledged,
    Unprivileged,
}

#[derive(Clone, Debug)]
pub struct ExecContext {
    pub map_defs: Vec<BpfMapDef>,
    pub pc_to_reloc: HashMap<usize, RelocInfo>,
    pub btf: BtfContext,
    pub prog_kind: ProgramKind,
    pub attach_kind: AttachKind,
    pub flags: u32,
    pub mode: VerificationMode,
    pub kfunc: Option<String>,
    /// W6.4a struct_ops entry-state typing. When `prog_kind` is
    /// `StructOps` and the runner has matched the subprog to its
    /// ops-struct member, this holds one [`EntryArg`] per kernel-passed
    /// argument (R1, R2, ...). `analyze_program_full` overrides the
    /// default `R1 = PtrToCtx` with these. None means "no struct_ops
    /// binding available" — fall back to the default.
    pub entry_args: Option<Vec<EntryArg>>,
    /// W6.4a-followon: true when the matched struct_ops member's
    /// FUNC_PROTO declares a void return. `transfer_exit` skips the
    /// "R0 not initialized" rejection in this case — void methods are
    /// not required to set R0, just like in the kernel verifier.
    pub entry_returns_void: bool,
    /// W6.4c: when verifying a struct_ops subprog, the (ops_struct,
    /// member) pair this subprog implements. Set by the runner from
    /// the same binding used to populate `entry_args`. Consumed by
    /// `transfer_kfunc_proto` to enforce per-(ops, member)
    /// `kfunc_ops_member_allowlist` (e.g. `scx_bpf_select_cpu_dfl`
    /// is callable only from `sched_ext_ops.select_cpu`).
    pub struct_ops_member: Option<(String, String)>,
    /// Cluster B: lowercase SEC suffix after the first `/`, used by
    /// `expected_retval_rule` to pick the per-attach-type R0 range
    /// enforced at exit. `None` for SECs without a slash (e.g. `"netfilter"`,
    /// `"syscall"`) or when the runner did not stash the section name.
    pub attach_subtype: Option<String>,
    /// Reverse of `combine_program_with_subprogs::func_offsets` — maps
    /// the absolute PC at which each subprog begins to its declared
    /// function name. Used by `transfer_call_rel` to resolve a
    /// `CallRel { target }` to a name and look up its BTF FUNC linkage
    /// + FUNC_PROTO. Empty when no subprogs were combined or the
    /// loader didn't populate the table.
    pub pc_to_subprog_name: HashMap<usize, String>,
    /// Name of the cb registered via `__exception_cb(<cb>)` decl_tag on
    /// the analyzed main subprog. Set by the runner after parsing the
    /// BTF DECL_TAG with prefix `"exception_callback:"`. Drives:
    ///   * direct-call rejection (main → cb resolves to "cannot call
    ///     exception cb directly"),
    ///   * throw-site checks inside the cb body ("cannot be called
    ///     from callback subprog").
    /// Distinct from the per-state `program_exception_cb`, which is
    /// populated at runtime by `bpf_set_exception_callback`.
    pub exception_callback: Option<String>,
    /// Lowercase SEC prefix before the first `/` (with leading `?`
    /// stripped). Captures the attach *flavor* — `"fentry"`, `"fexit"`,
    /// `"fmod_ret"`, `"tp_btf"`, `"iter"`, etc. Companion to
    /// `attach_subtype` (which holds the *target*, e.g. `"bpf_check"`).
    /// Together they reconstruct the SEC for checks that depend on the
    /// flavor: e.g. fentry/fexit programs require R0 ∈ [0, 0] at exit
    /// and at exception-cb exits / throw cookies.
    pub attach_flavor: Option<String>,
    /// Number of struct_ops member parameters declared as `__ref` (acquired
    /// at function entry, must be released before exit). Set by the runner
    /// from `STRUCT_OPS_REFCOUNTED_ARGS` for the matched (ops_struct,
    /// member) pair. `analyze_program_full` calls `state.acquire_ref()`
    /// this many times when seeding the initial state, so a program that
    /// fails to release one of its refcounted args fires
    /// `UnreleasedReference` at exit (matches the kernel's
    /// "Unreleased reference id=N alloc_insn=0" rejection on
    /// struct_ops_refcounted_fail__ref_leak.c).
    pub struct_ops_refcounted_args: usize,
    /// Subprogs (keyed by absolute start PC) whose body — directly or
    /// transitively via CallRel — invokes a MIGHT_SLEEP helper or kfunc.
    /// Computed once at runner setup via static call-graph closure.
    /// Consumed by `transfer_call_rel` to reject CallRel into a global
    /// may-sleep subprog from inside an irq- or preempt-disabled region
    /// (kernel: "global functions that may sleep are not allowed in
    /// non-sleepable context"). Independent of data flow — kernel
    /// rejects regardless of whether any specific path through the
    /// callee body actually reaches the sleepable call.
    pub may_sleep_subprogs: HashSet<usize>,
}

pub fn default_exec_ctx() -> ExecContext {
    ExecContext {
        map_defs: Vec::new(),
        pc_to_reloc: HashMap::new(),
        btf: BtfContext::new(),
        prog_kind: ProgramKind::Unknown,
        attach_kind: AttachKind::Unknown,
        flags: 0,
        mode: VerificationMode::Priviledged,
        kfunc: None,
        entry_args: None,
        entry_returns_void: false,
        struct_ops_member: None,
        attach_subtype: None,
        pc_to_subprog_name: HashMap::new(),
        exception_callback: None,
        attach_flavor: None,
        struct_ops_refcounted_args: 0,
        may_sleep_subprogs: HashSet::new(),
    }
}

impl ExecContext {
    pub fn has_flag(&self, flag: u32) -> bool {
        self.flags & flag != 0
    }

    pub fn is_privileged(&self) -> bool {
        matches!(self.mode, VerificationMode::Priviledged)
    }
}
