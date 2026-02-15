// src/selftest.rs
//
// Runner for kernel BPF verifier selftests converted to JSON format.
//
// Usage:
//   cargo run -- selftest-run tests/array_access.json
//   cargo run -- selftest-suite tests/

use std::collections::HashMap;
use std::fs;
use std::io::Write;
use std::path::Path;
use std::time::Instant;

use log::info;
use serde::{Deserialize, Serialize};

use crate::analysis;
use crate::analysis::machine::context::{default_exec_ctx};
use crate::common::constants;
use crate::ast::{AttachKind, ProgramKind};
use crate::parsing::bpf_to_ast::{lower_raw_to_program, LowerErrorKind};
use crate::parsing::btf::{BtfContext, BtfMember, BtfType};
use crate::common::config::VerifierConfig;
use crate::parsing::bpf_insn::RawBpfInsn;
use crate::parsing::elf_loader::{BpfMapDef, RelocInfo};
use crate::zone::dbm::Dbm;
use crate::analysis::machine::reg::Reg;
use crate::zone::domain::assign_zero;

// ============================================================================
// JSON Deserialization Types
// ============================================================================

#[allow(dead_code)]
#[derive(Debug, Deserialize)]
pub struct JsonTestCase {
    pub name: String,
    pub result: String,
    pub result_unpriv: Option<String>,
    pub errstr: Option<String>,
    pub errstr_unpriv: Option<String>,
    pub prog_type: Option<u32>,
    pub expected_attach_type: Option<u32>,
    pub flags: Option<u32>,
    pub kfunc: Option<String>,
    pub fixups: Option<HashMap<String, Vec<usize>>>,
    pub insns: Vec<JsonInsn>,
}

#[derive(Debug, Deserialize)]
pub struct JsonInsn {
    pub code: u8,
    pub dst: u8,
    pub src: u8,
    pub off: i16,
    pub imm: i32,
}

impl From<&JsonInsn> for RawBpfInsn {
    fn from(j: &JsonInsn) -> Self {
        RawBpfInsn {
            code: j.code,
            dst: j.dst,
            src: j.src,
            off: j.off,
            imm: j.imm,
        }
    }
}

// ============================================================================
// Test Results
// ============================================================================

#[derive(Debug, Clone, Serialize)]
pub enum TestOutcome {
    /// Our result matches expected
    Pass,
    /// Expected ACCEPT but we REJECT - precision issue (too conservative)
    FalsePositive,
    /// Expected REJECT but we ACCEPT - SOUNDNESS issue (too permissive - BAD!)
    FalseNegative,
    /// Test couldn't be run (parse error, unsupported feature, etc.)
    Skipped {
        reason: String,
    },
    /// Internal error during analysis
    Error {
        message: String,
    },
}

impl TestOutcome {
    pub fn is_false_positive(&self) -> bool {
        matches!(self, TestOutcome::FalsePositive)
    }

    pub fn is_false_negative(&self) -> bool {
        matches!(self, TestOutcome::FalseNegative)
    }
}

#[derive(Debug, Serialize)]
pub struct TestResult {
    pub name: String,
    pub outcome: TestOutcome,
    pub expected: String,
    pub actual: String,
    pub time_ms: u64,
}

#[derive(Debug, Serialize)]
pub struct FileResult {
    pub file: String,
    pub total: usize,
    pub passed: usize,
    pub false_positives: usize,  // Expected ACCEPT, got REJECT (precision)
    pub false_negatives: usize,  // Expected REJECT, got ACCEPT (SOUNDNESS!)
    pub skipped: usize,
    pub errors: usize,
    pub time_ms: u64,
    pub tests: Vec<TestResult>,
}

#[derive(Debug, Serialize)]
pub struct SuiteResult {
    pub total_files: usize,
    pub total_tests: usize,
    pub passed: usize,
    pub false_positives: usize,  // Precision issues
    pub false_negatives: usize,  // SOUNDNESS issues
    pub skipped: usize,
    pub errors: usize,
    pub time_ms: u64,
    pub files: Vec<FileResult>,
}

// ============================================================================
// Map Type Constants (from linux/bpf.h)
// ============================================================================

const BPF_MAP_TYPE_HASH: u32 = 1;
const BPF_MAP_TYPE_ARRAY: u32 = 2;
const BPF_MAP_TYPE_PROG_ARRAY: u32 = 3;
const BPF_MAP_TYPE_PERF_EVENT_ARRAY: u32 = 4;
const BPF_MAP_TYPE_CGROUP_STORAGE: u32 = 19;
const BPF_MAP_TYPE_PERCPU_CGROUP_STORAGE: u32 = 21;
const BPF_MAP_TYPE_RINGBUF: u32 = 16;
const BPF_MAP_TYPE_ARRAY_OF_MAPS: u32 = 12;
const BPF_MAP_TYPE_STACK_TRACE: u32 = 7;
const BPF_MAP_TYPE_SK_STORAGE: u32 = 24;
const BPF_MAP_TYPE_SOCKMAP: u32 = 15;
const BPF_MAP_TYPE_SOCKHASH: u32 = 18;
const BPF_MAP_TYPE_XSKMAP: u32 = 17;
const BPF_MAP_TYPE_REUSEPORT_SOCKARRAY: u32 = 22;
// Add more as needed

// ============================================================================
// Fixup → Map Definition
// ============================================================================

/// Convert fixup field names to BpfMapDef
fn map_def_for_fixup(fixup_name: &str) -> Option<BpfMapDef> {
    // Parse fixup name to determine map type and size
    // Format: fixup_map_{type}_{size} or fixup_map_{type}
    match fixup_name {
        "fixup_map_hash_8b" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_HASH,
            key_size: 8,
            value_size: 8,
            max_entries: 1,
            map_flags: 0,
            name: "test_map".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_hash_16b" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_HASH,
            key_size: 8,
            value_size: 16,
            max_entries: 1,
            map_flags: 0,
            name: "test_map".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_hash_48b" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_HASH,
            key_size: 8,
            value_size: 48,
            max_entries: 1,
            map_flags: 0,
            name: "test_map".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_array_48b" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_ARRAY,
            key_size: 4,
            value_size: 48,
            max_entries: 1,
            map_flags: 0,
            name: "test_map".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_array_ro" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_ARRAY,
            key_size: 4,
            value_size: 8,
            max_entries: 1,
            map_flags: constants::BPF_F_RDONLY_PROG,
            name: "test_map_ro".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_array_wo" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_ARRAY,
            key_size: 4,
            value_size: 8,
            max_entries: 1,
            map_flags: constants::BPF_F_WRONLY_PROG,
            name: "test_map_wo".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_array_small" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_ARRAY,
            key_size: 4,
            value_size: 1,
            max_entries: 1,
            map_flags: 0,
            name: "test_map".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_prog1" | "fixup_prog2" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_PROG_ARRAY,
            key_size: 4,
            value_size: 4,
            max_entries: 1,
            map_flags: 0,
            name: "test_prog_array".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_cgroup_storage" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_CGROUP_STORAGE,  // 19
            key_size: 16,  // struct bpf_cgroup_storage_key
            value_size: 64,
            max_entries: 0,  // cgroup storage doesn't use max_entries
            map_flags: 0,
            name: "test_cgroup_storage".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_percpu_cgroup_storage" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_PERCPU_CGROUP_STORAGE,  // 21
            key_size: 16,  // struct bpf_cgroup_storage_key
            value_size: 64,
            max_entries: 0,
            map_flags: 0,
            name: "test_percpu_cgroup_storage".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_event_output" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_PERF_EVENT_ARRAY,  // 4
            key_size: 4,
            value_size: 4,
            max_entries: 1,
            map_flags: 0,
            name: "test_event_output".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_ringbuf" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_RINGBUF,  // 16
            key_size: 4,
            value_size: 4,
            max_entries: 1,
            map_flags: 0,
            name: "test_ringbuf".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_in_map" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_ARRAY_OF_MAPS,  // 12
            key_size: 4,
            value_size: 4,
            max_entries: 1,
            map_flags: 0,
            name: "test_map_in_map".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_stacktrace" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_STACK_TRACE,  // 7
            key_size: 4,
            value_size: 1016,  // sizeof(__u64) * 127 (PERF_MAX_STACK_DEPTH)
            max_entries: 1,
            map_flags: 0,
            name: "test_stacktrace".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_sk_storage_map" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_SK_STORAGE,  // 24
            key_size: 4,
            value_size: 8,
            max_entries: 0,
            map_flags: 0x400,  // BPF_F_NO_PREALLOC (required for sk_storage)
            name: "test_sk_storage".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_sockmap" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_SOCKMAP,  // 15
            key_size: 4,
            value_size: 4,
            max_entries: 1,
            map_flags: 0,
            name: "test_sockmap".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_sockhash" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_SOCKHASH,  // 18
            key_size: 4,
            value_size: 4,
            max_entries: 1,
            map_flags: 0,
            name: "test_sockhash".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_xskmap" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_XSKMAP,  // 17
            key_size: 4,
            value_size: 4,
            max_entries: 1,
            map_flags: 0,
            name: "test_xskmap".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_reuseport_array" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_REUSEPORT_SOCKARRAY,  // 22
            key_size: 4,
            value_size: 8,
            max_entries: 1,
            map_flags: 0,
            name: "test_reuseport_array".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_spin_lock" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_ARRAY,
            key_size: 4,
            value_size: 8,
            max_entries: 1,
            map_flags: 0,
            name: "spin_lock_map".to_string(),
            btf_val_type_id: Some(3),  // points to struct val
            initial_data: None,
        }),
        // Add more fixup types as needed
        _ => None,
    }
}

// ============================================================================
// Build ExecContext from Test Case
// ============================================================================

pub fn create_spin_lock_btf() -> BtfContext {
    let strings = b"\0bpf_spin_lock\0val\0cnt\0l".to_vec();
    
    let mut types = HashMap::new();
    
    // Type 1: int
    types.insert(1, BtfType {
        id: 1,
        name_off: 0,
        info: 1 << 24,  // BTF_KIND_INT
        size_or_type: 4,
        members: vec![],
    });
    
    // Type 2: struct bpf_spin_lock
    types.insert(2, BtfType {
        id: 2,
        name_off: 1,  // "bpf_spin_lock"
        info: (4 << 24) | 1,  // BTF_KIND_STRUCT, 1 member
        size_or_type: 4,
        members: vec![
            BtfMember { name_off: 15, type_id: 1, offset: 0 },
        ],
    });
    
    // Type 3: struct val (the map value type)
    types.insert(3, BtfType {
        id: 3,
        name_off: 15,  // "val"
        info: (4 << 24) | 2,  // BTF_KIND_STRUCT, 2 members
        size_or_type: 8,
        members: vec![
            BtfMember { name_off: 19, type_id: 1, offset: 0 },   // cnt @ byte 0
            BtfMember { name_off: 23, type_id: 2, offset: 32 },  // lock @ byte 4
        ],
    });
    
    BtfContext { types, strings }
}

fn build_exec_context(test: &JsonTestCase) -> (crate::analysis::machine::context::ExecContext, bool) {
    let mut ctx = default_exec_ctx();
    let mut has_unsupported_fixup = false;

    if let Some(ref fixups) = test.fixups {
        for (fixup_name, pcs) in fixups {
            if let Some(map_def) = map_def_for_fixup(fixup_name) {
                let map_idx = ctx.map_defs.len();
                ctx.map_defs.push(map_def);

                // Record relocations for each PC
                // offset is 0 for direct map references (like in kernel selftests)
                for &pc in pcs {
                    ctx.pc_to_reloc.insert(
                        pc,
                        RelocInfo {
                            map_idx,
                            offset: 0,
                        },
                    );
                }
            } else {
                // Unsupported fixup type
                has_unsupported_fixup = true;
            }
        }
    }

    info!("Loaded {} map definitions", ctx.map_defs.len());
    info!("Map Definitions: {:?}", ctx.map_defs);

    ctx.prog_kind = match test.prog_type {
        Some(constants::BPF_PROG_TYPE_UNSPEC) => ProgramKind::Unspec,
        Some(constants::BPF_PROG_TYPE_SOCKET_FILTER) => ProgramKind::SocketFilter,
        Some(constants::BPF_PROG_TYPE_KPROBE) => ProgramKind::Kprobe,
        Some(constants::BPF_PROG_TYPE_SCHED_CLS) => ProgramKind::SchedCls,
        Some(constants::BPF_PROG_TYPE_SCHED_ACT) => ProgramKind::SchedAct,
        Some(constants::BPF_PROG_TYPE_TRACEPOINT) => ProgramKind::Tracepoint,
        Some(constants::BPF_PROG_TYPE_XDP) => ProgramKind::Xdp,
        Some(constants::BPF_PROG_TYPE_PERF_EVENT) => ProgramKind::PerfEvent,
        Some(constants::BPF_PROG_TYPE_CGROUP_SKB) => ProgramKind::CgroupSkb,
        Some(constants::BPF_PROG_TYPE_CGROUP_SOCK) => ProgramKind::CgroupSock,
        Some(constants::BPF_PROG_TYPE_LWT_IN) => ProgramKind::LwtIn,
        Some(constants::BPF_PROG_TYPE_LWT_OUT) => ProgramKind::LwtOut,
        Some(constants::BPF_PROG_TYPE_LWT_XMIT) => ProgramKind::LwtXmit,
        Some(constants::BPF_PROG_TYPE_SOCK_OPS) => ProgramKind::SockOps,
        Some(constants::BPF_PROG_TYPE_SK_SKB) => ProgramKind::SkSkb,
        Some(constants::BPF_PROG_TYPE_CGROUP_DEVICE) => ProgramKind::CgroupDevice,
        Some(constants::BPF_PROG_TYPE_SK_MSG) => ProgramKind::SkMsg,
        Some(constants::BPF_PROG_TYPE_RAW_TRACEPOINT) => ProgramKind::RawTracepoint,
        Some(constants::BPF_PROG_TYPE_CGROUP_SOCK_ADDR) => ProgramKind::CgroupSockAddr,
        Some(constants::BPF_PROG_TYPE_LSM) => ProgramKind::Lsm,
        Some(constants::BPF_PROG_TYPE_SK_LOOKUP) => ProgramKind::SkLookup,
        Some(constants::BPF_PROG_TYPE_RAW_TRACEPOINT_WRITABLE) => ProgramKind::RawTracepointWritable,
        Some(constants::BPF_PROG_TYPE_TRACING) => ProgramKind::Tracing,
        // Default fallback (usually SocketFilter is the safe default for tests)
        _ => ProgramKind::SocketFilter, 
    };
    println!("Program Type: {:?}", ctx.prog_kind);

    ctx.attach_kind = match test.expected_attach_type {
        Some(constants::BPF_ATTACH_TYPE_TRACE_RAW_TP) => AttachKind::TraceRawTp,
        Some(constants::BPF_ATTACH_TYPE_TRACE_ITER) => AttachKind::TraceIter,
        _ => AttachKind::Unknown,
    };

    ctx.kfunc = test.kfunc.clone();

    if test.flags.is_some() {
        ctx.flags |= test.flags.unwrap();
    }

    ctx.btf = create_spin_lock_btf();

    (ctx, has_unsupported_fixup)
}

// ============================================================================
// Entry State
// ============================================================================

fn make_entry_state() -> Dbm {
    let mut dbm = Dbm::new();
    assign_zero(&mut dbm, Reg::R10);
    dbm
}

// ============================================================================
// Run Single Test
// ============================================================================

pub fn run_test(test: &JsonTestCase, config: &VerifierConfig) -> TestResult {
    let start = Instant::now();

    // Convert JSON instructions to RawBpfInsn
    let raw_insns: Vec<RawBpfInsn> = test.insns.iter().map(|j| j.into()).collect();

    // Lower to Program AST
    
    let program = match lower_raw_to_program(&raw_insns) {
        Ok(p) => p,
        Err(e) => {
            let mut outcome = TestOutcome::Error {
                message: format!("Failed to lower program: {:?}", e),
            };
            let errstr = test.errstr.clone();
            match errstr {
                Some(s) => {
                    // In this case, the lowering is meant to fail, so PASS
                    if s.contains("unknown op") && matches!(e.kind, LowerErrorKind::UnknownOpcode) {
                        outcome = TestOutcome::Pass
                    } else if (s.contains("invalid bpf_ld_imm64 insn") || 
                                s.contains("expected continuation instruction after LDDW") || 
                                s.contains("uses reserved fields") ||
                                s.contains("unrecognized bpf_ld_imm64 insn")) && 
                                matches!(e.kind, LowerErrorKind::InvalidLDIMM64) {
                        outcome = TestOutcome::Pass
                    } else if s.contains("invalid destination") && matches!(e.kind, LowerErrorKind::CallTargetOutOfBounds) {
                        outcome = TestOutcome::Pass
                    } else if s.contains("reserved fields") && matches!(e.kind, LowerErrorKind::CallUsedReservedFields | LowerErrorKind::InvalidSrcReg) {
                        outcome = TestOutcome::Pass
                    } else if s.contains("jump out of range") && matches!(e.kind, LowerErrorKind::BranchTargetOutOfRange) {
                        outcome = TestOutcome::Pass
                    } else if s.contains("R15") && matches!(e.kind, LowerErrorKind::InvalidRegister) {
                        outcome = TestOutcome::Pass
                    } else if s.contains("arg#0") && matches!(e.kind, LowerErrorKind::InvalidSrcReg) {
                        outcome = TestOutcome::Pass
                    } else if s.contains("unknown opcode 00") && matches!(e.kind, LowerErrorKind::InvalidLDIMM64) {
                        outcome = TestOutcome::Pass
                    } else if matches!(e.kind, LowerErrorKind::InvalidRegister) {
                        outcome = TestOutcome::Pass
                    }
                }
                None => {}
            }
            return TestResult {
                name: test.name.clone(),
                outcome,
                expected: test.result.clone(),
                actual: "ERROR".to_string(),
                time_ms: start.elapsed().as_millis() as u64,
            };
        }
    };

    println!("Test '{}': Lowered Program AST:", test.name);
    for (instr, idx) in program.instrs.iter().zip(0..) {
        println!("  {:04}: {:?}", idx, instr);
    }

    // Build execution context
    let (ctx, has_unsupported_fixup) = build_exec_context(test);

    if has_unsupported_fixup {
        return TestResult {
            name: test.name.clone(),
            outcome: TestOutcome::Skipped {
                reason: "Unsupported fixup type".to_string(),
            },
            expected: test.result.clone(),
            actual: "SKIPPED".to_string(),
            time_ms: start.elapsed().as_millis() as u64,
        };
    }

    // Run analysis
    let entry = make_entry_state();
    let result = analysis::analyze_program(&ctx, &program, entry, config);

    let actual = if result.is_ok() { "ACCEPT" } else { "REJECT" };
    let expected = if test.result == "VERBOSE_ACCEPT" { "ACCEPT" } else {&test.result};

    let outcome = if actual == expected {
        TestOutcome::Pass
    } else if expected == "ACCEPT" && actual == "REJECT" {
        // We rejected something that should be accepted - precision issue
        TestOutcome::FalsePositive
    } else {
        // We accepted something that should be rejected - SOUNDNESS issue!
        TestOutcome::FalseNegative
    };

    TestResult {
        name: test.name.clone(),
        outcome,
        expected: expected.to_string(),
        actual: actual.to_string(),
        time_ms: start.elapsed().as_millis() as u64,
    }
}

// ============================================================================
// Run Test File
// ============================================================================

pub fn run_test_file(path: &str, config: &VerifierConfig) -> Result<FileResult, String> {
    let start = Instant::now();

    // Load JSON
    let content = fs::read_to_string(path)
        .map_err(|e| format!("Failed to read {}: {}", path, e))?;

    let tests: Vec<JsonTestCase> = serde_json::from_str(&content)
        .map_err(|e| format!("Failed to parse {}: {}", path, e))?;

    let mut results = Vec::new();
    let mut passed = 0;
    let mut false_positives = 0;
    let mut false_negatives = 0;
    let mut skipped = 0;
    let mut errors = 0;

    for test in &tests {
        let result = run_test(test, config);

        match &result.outcome {
            TestOutcome::Pass => passed += 1,
            TestOutcome::FalsePositive => false_positives += 1,
            TestOutcome::FalseNegative => false_negatives += 1,
            TestOutcome::Skipped { .. } => skipped += 1,
            TestOutcome::Error { .. } => errors += 1,
        }

        results.push(result);
    }

    Ok(FileResult {
        file: path.to_string(),
        total: tests.len(),
        passed,
        false_positives,
        false_negatives,
        skipped,
        errors,
        time_ms: start.elapsed().as_millis() as u64,
        tests: results,
    })
}

// ============================================================================
// Run Test Suite (Directory)
// ============================================================================

pub fn run_test_suite(dir: &str, config: &VerifierConfig) -> Result<SuiteResult, String> {
    let start = Instant::now();

    let mut files = Vec::new();

    // Find all .json files
    let entries = fs::read_dir(dir)
        .map_err(|e| format!("Failed to read directory {}: {}", dir, e))?;

    let mut json_files: Vec<_> = entries
        .filter_map(|e| e.ok())
        .filter(|e| {
            e.path()
                .extension()
                .map(|ext| ext == "json")
                .unwrap_or(false)
        })
        .collect();

    json_files.sort_by_key(|e| e.path());

    for entry in json_files {
        let path = entry.path();
        let path_str = path.to_string_lossy().to_string();

        match run_test_file(&path_str, config) {
            Ok(result) => files.push(result),
            Err(e) => {
                eprintln!("Warning: Skipping {}: {}", path_str, e);
            }
        }
    }

    // Aggregate stats
    let total_tests: usize = files.iter().map(|f| f.total).sum();
    let passed: usize = files.iter().map(|f| f.passed).sum();
    let false_positives: usize = files.iter().map(|f| f.false_positives).sum();
    let false_negatives: usize = files.iter().map(|f| f.false_negatives).sum();
    let skipped: usize = files.iter().map(|f| f.skipped).sum();
    let errors: usize = files.iter().map(|f| f.errors).sum();

    Ok(SuiteResult {
        total_files: files.len(),
        total_tests,
        passed,
        false_positives,
        false_negatives,
        skipped,
        errors,
        time_ms: start.elapsed().as_millis() as u64,
        files,
    })
}

// ============================================================================
// Report Generation
// ============================================================================

pub fn write_txt_report(result: &SuiteResult, path: &str) -> Result<(), String> {
    let mut f = fs::File::create(path)
        .map_err(|e| format!("Failed to create {}: {}", path, e))?;

    writeln!(f, "BPF Verifier Selftest Report").unwrap();
    writeln!(f, "============================\n").unwrap();

    writeln!(f, "Summary:").unwrap();
    writeln!(f, "  Files:            {}", result.total_files).unwrap();
    writeln!(f, "  Tests:            {}", result.total_tests).unwrap();
    writeln!(f, "  Passed:           {} ({:.1}%)", 
             result.passed, 
             100.0 * result.passed as f64 / result.total_tests.max(1) as f64).unwrap();
    writeln!(f, "  SOUNDNESS ISSUES: {} (expected REJECT, got ACCEPT) <<<", result.false_negatives).unwrap();
    writeln!(f, "  Precision issues: {} (expected ACCEPT, got REJECT)", result.false_positives).unwrap();
    writeln!(f, "  Skipped:          {}", result.skipped).unwrap();
    writeln!(f, "  Errors:           {}", result.errors).unwrap();
    writeln!(f, "  Time:             {} ms\n", result.time_ms).unwrap();

    // Per-file summary
    writeln!(f, "Per-File Results:").unwrap();
    writeln!(f, "-----------------").unwrap();
    for file in &result.files {
        let status = if file.false_negatives > 0 {
            "UNSOUND"
        } else if file.false_positives == 0 && file.errors == 0 {
            "OK"
        } else {
            "IMPRECISE"
        };
        writeln!(f, "  {:8} {} ({}/{} passed, {} soundness, {} precision) [{}ms]",
                 status,
                 Path::new(&file.file).file_name().unwrap().to_string_lossy(),
                 file.passed,
                 file.total,
                 file.false_negatives,
                 file.false_positives,
                 file.time_ms).unwrap();
    }

    // SOUNDNESS ISSUES (most important - show first!)
    let has_soundness = result.files.iter().any(|f| f.false_negatives > 0);
    if has_soundness {
        writeln!(f, "\n").unwrap();
        writeln!(f, "!!! SOUNDNESS ISSUES !!! (expected REJECT, we ACCEPT - DANGEROUS)").unwrap();
        writeln!(f, "================================================================").unwrap();
        for file in &result.files {
            for test in &file.tests {
                if test.outcome.is_false_negative() {
                    writeln!(f, "  [{}] {}", 
                             Path::new(&file.file).file_name().unwrap().to_string_lossy(),
                             test.name).unwrap();
                    writeln!(f, "    Expected: REJECT, Got: ACCEPT").unwrap();
                }
            }
        }
    }

    // Precision issues (less critical)
    let has_precision = result.files.iter().any(|f| f.false_positives > 0);
    if has_precision {
        writeln!(f, "\nPrecision Issues (expected ACCEPT, we REJECT - too conservative):").unwrap();
        writeln!(f, "----------------------------------------------------------------").unwrap();
        for file in &result.files {
            for test in &file.tests {
                if test.outcome.is_false_positive() {
                    writeln!(f, "  [{}] {}", 
                             Path::new(&file.file).file_name().unwrap().to_string_lossy(),
                             test.name).unwrap();
                    writeln!(f, "    Expected: ACCEPT, Got: REJECT").unwrap();
                }
            }
        }
    }

    // Errors detail
    let has_errors = result.files.iter().any(|f| f.errors > 0);
    if has_errors {
        writeln!(f, "\nErrors:").unwrap();
        writeln!(f, "-------").unwrap();
        for file in &result.files {
            for test in &file.tests {
                if let TestOutcome::Error { message } = &test.outcome {
                    writeln!(f, "  [{}] {}", 
                             Path::new(&file.file).file_name().unwrap().to_string_lossy(),
                             test.name).unwrap();
                    writeln!(f, "    {}", message).unwrap();
                }
            }
        }
    }

    Ok(())
}

pub fn write_json_report(result: &SuiteResult, path: &str) -> Result<(), String> {
    let json = serde_json::to_string_pretty(result)
        .map_err(|e| format!("Failed to serialize: {}", e))?;

    fs::write(path, json)
        .map_err(|e| format!("Failed to write {}: {}", path, e))?;

    Ok(())
}

// ============================================================================
// CLI Entry Points
// ============================================================================

/// Run a single test file and print results
pub fn selftest_run(json_path: &str, config: &VerifierConfig, output_dir: Option<&str>) {
    println!("Running selftest: {}\n", json_path);

    match run_test_file(json_path, config) {
        Ok(result) => {
            // Print summary
            println!("Results: {}/{} passed ({} soundness, {} precision, {} skipped, {} errors) in {}ms",
                     result.passed, result.total, 
                     result.false_negatives, result.false_positives,
                     result.skipped, result.errors, result.time_ms);

            // Print soundness issues first (most important!)
            for test in &result.tests {
                if test.outcome.is_false_negative() {
                    println!("  !!! SOUNDNESS: {} (expected REJECT, got ACCEPT)", test.name);
                }
            }

            // Print precision issues
            for test in &result.tests {
                if test.outcome.is_false_positive() {
                    println!("  PRECISION: {} (expected ACCEPT, got REJECT)", test.name);
                }
            }

            // Print other outcomes
            for test in &result.tests {
                match &test.outcome {
                    TestOutcome::Pass => {
                        if config.verbosity > 0 {
                            println!("  PASS: {}", test.name);
                        }
                    }
                    TestOutcome::Skipped { reason } => {
                        if config.verbosity > 0 {
                            println!("  SKIP: {} ({})", test.name, reason);
                        }
                    }
                    TestOutcome::Error { message } => {
                        println!("  ERROR: {} ({})", test.name, message);
                    }
                    _ => {} // Already printed above
                }
            }

            // Write reports if output_dir specified
            if let Some(dir) = output_dir {
                let base = Path::new(json_path)
                    .file_stem()
                    .unwrap()
                    .to_string_lossy();

                let suite = SuiteResult {
                    total_files: 1,
                    total_tests: result.total,
                    passed: result.passed,
                    false_positives: result.false_positives,
                    false_negatives: result.false_negatives,
                    skipped: result.skipped,
                    errors: result.errors,
                    time_ms: result.time_ms,
                    files: vec![result],
                };

                let txt_path = format!("{}/{}_report.txt", dir, base);
                let json_path = format!("{}/{}_report.json", dir, base);

                if let Err(e) = write_txt_report(&suite, &txt_path) {
                    eprintln!("Warning: {}", e);
                } else {
                    println!("\nReport written to: {}", txt_path);
                }

                if let Err(e) = write_json_report(&suite, &json_path) {
                    eprintln!("Warning: {}", e);
                }
            }
        }
        Err(e) => {
            eprintln!("Error: {}", e);
        }
    }
}

/// Run a single test by name from a JSON file
pub fn selftest_single(json_path: &str, test_name: &str, config: &VerifierConfig) {
    println!("Running single test: '{}' from {}\n", test_name, json_path);

    // Load JSON
    let content = match fs::read_to_string(json_path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error: Failed to read {}: {}", json_path, e);
            return;
        }
    };

    let tests: Vec<JsonTestCase> = match serde_json::from_str(&content) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("Error: Failed to parse {}: {}", json_path, e);
            return;
        }
    };

    // Find the test by name (case-insensitive substring match)
    let matching: Vec<_> = tests
        .iter()
        .filter(|t| t.name.to_lowercase().contains(&test_name.to_lowercase()) 
            && t.name.len() == test_name.len() )
        .collect();

    if matching.is_empty() {
        eprintln!("Error: No test matching '{}' found", test_name);
        eprintln!("\nAvailable tests:");
        for (i, t) in tests.iter().enumerate() {
            eprintln!("  [{}] {}", i, t.name);
        }
        return;
    }

    if matching.len() > 1 {
        eprintln!("Multiple tests match '{}', running all:\n", test_name);
    }

    for test in matching {
        println!("Test: {}", test.name);
        println!("Expected: {}", test.result);
        if let Some(ref err) = test.errstr {
            println!("Expected error: {}", err);
        }
        println!("Instructions: {}", test.insns.len());
        if let Some(ref fixups) = test.fixups {
            println!("Fixups: {:?}", fixups.keys().collect::<Vec<_>>());
        }
        println!();

        let result = run_test(test, config);

        match &result.outcome {
            TestOutcome::Pass => {
                println!("=== PASS === ({}ms)", result.time_ms);
            }
            TestOutcome::FalseNegative => {
                println!("=== !!! SOUNDNESS ISSUE !!! === ({}ms)", result.time_ms);
                println!("  Expected: REJECT");
                println!("  Actual:   ACCEPT");
                println!("  This is DANGEROUS - we accepted an unsafe program!");
            }
            TestOutcome::FalsePositive => {
                println!("=== PRECISION ISSUE === ({}ms)", result.time_ms);
                println!("  Expected: ACCEPT");
                println!("  Actual:   REJECT");
                println!("  Too conservative - rejected a safe program.");
            }
            TestOutcome::Skipped { reason } => {
                println!("=== SKIPPED === ({}ms)", result.time_ms);
                println!("  Reason: {}", reason);
            }
            TestOutcome::Error { message } => {
                println!("=== ERROR === ({}ms)", result.time_ms);
                println!("  {}", message);
            }
        }
        println!();
    }
}

/// List all tests in a JSON file
pub fn selftest_list(json_path: &str) {
    println!("Tests in {}:\n", json_path);

    // Load JSON
    let content = match fs::read_to_string(json_path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error: Failed to read {}: {}", json_path, e);
            return;
        }
    };

    let tests: Vec<JsonTestCase> = match serde_json::from_str(&content) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("Error: Failed to parse {}: {}", json_path, e);
            return;
        }
    };

    for (i, t) in tests.iter().enumerate() {
        let fixup_info = if let Some(ref f) = t.fixups {
            format!(" [{}]", f.keys().cloned().collect::<Vec<_>>().join(", "))
        } else {
            String::new()
        };
        println!("  [{:2}] {} -> {}{}", i, t.name, t.result, fixup_info);
    }
    println!("\nTotal: {} tests", tests.len());
}

/// Run all test files in a directory
pub fn selftest_suite(dir: &str, config: &VerifierConfig, output_dir: Option<&str>) {
    println!("Running selftest suite: {}\n", dir);

    match run_test_suite(dir, config) {
        Ok(result) => {
            // Print summary
            println!("========================================");
            println!("            SUITE SUMMARY");
            println!("========================================");
            println!("Files:            {}", result.total_files);
            println!("Tests:            {}", result.total_tests);
            println!("Passed:           {} ({:.1}%)",
                     result.passed,
                     100.0 * result.passed as f64 / result.total_tests.max(1) as f64);
            if result.false_negatives > 0 {
                println!("SOUNDNESS ISSUES: {} <<<", result.false_negatives);
            } else {
                println!("Soundness issues: 0 (good!)");
            }
            println!("Precision issues: {}", result.false_positives);
            println!("Skipped:          {}", result.skipped);
            println!("Errors:           {}", result.errors);
            println!("Time:             {} ms", result.time_ms);
            println!("========================================\n");

            // Per-file summary
            println!("Per-file results:");
            let mut soundness = Vec::new(); // ⚠
            let mut clean = Vec::new();     // ✓
            let mut precision = Vec::new(); // ○

            for file in &result.files {
                if file.false_negatives > 0 {
                    soundness.push(file);
                } else if file.false_positives == 0 && file.errors == 0 {
                    clean.push(file);
                } else {
                    precision.push(file);
                }
            }

            let print_group = |status: &str, files: Vec<&FileResult>| {
                for file in files {
                    println!(
                        "  {} {} ({}/{} passed, {} soundness, {} precision)",
                        status,
                        Path::new(&file.file)
                            .file_name()
                            .unwrap()
                            .to_string_lossy(),
                        file.passed,
                        file.total,
                        file.false_negatives,
                        file.false_positives
                    );
                }
            };

            print_group("⚠", soundness);
            print_group("○", precision);
            print_group("✓", clean);
            
            // Write reports
            let out = output_dir.unwrap_or(".");
            let txt_path = format!("{}/selftest_report.txt", out);
            let json_path = format!("{}/selftest_report.json", out);

            if let Err(e) = write_txt_report(&result, &txt_path) {
                eprintln!("Warning: {}", e);
            } else {
                println!("\nText report:  {}", txt_path);
            }

            if let Err(e) = write_json_report(&result, &json_path) {
                eprintln!("Warning: {}", e);
            } else {
                println!("JSON report:  {}", json_path);
            }
        }
        Err(e) => {
            eprintln!("Error: {}", e);
        }
    }
}
