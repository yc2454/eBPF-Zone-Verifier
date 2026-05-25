# eBPF Zone Verifier

A robust, user-space static analyzer for eBPF (Extended Berkeley Packet Filter) programs. This tool verifies the safety and correctness of BPF bytecode by reconstructing control flow graphs (CFGs), tracking register values with abstract interpretation (Difference Bound Matrices and Tri-state Numbers), and validating memory accesses, context usage, and map operations.

**Status (Linux v6.15 corpus):** 3278 PASS / 0 FA / 0 FR / 0 ERROR — see [CHANGES_v6.15.md](CHANGES_v6.15.md) for the full list of features added in this release.

## Features

* **Control Flow Reconstruction:** Parses raw BPF bytecode to build a navigable control flow graph.
* **Abstract Interpretation (Zone Domain):** Uses Difference Bound Matrices (DBM) to track relational constraints (e.g., `r1 < r2 + 10`) and value ranges.
* **Tri-state Numbers (Tnum):** Tracks bitwise knowledge (zeros, ones, and unknown bits) for precise bitwise operation analysis.
* **Context Validation:** Enforces strict access rules based on BPF program types (e.g., `sk_buff`, `xdp_md`, `bpf_sock_addr`).
* **Map Safety:** Validates map lookups and value dereferences, supporting map-in-map and global data (`.rodata`).
* **Dead Code Pruning:** Intelligently prunes unreachable paths using static branch evaluation and state comparison.
* **Kernel Compatibility Mode:** Optional `--kernel-mode` flag simulates kernel verifier behavior for compatibility testing.
* **Selftest Suite:** Built-in support for running large JSON-based test suites (compatible with Kernel BPF tests).
* **Benchmarking Suite:** Bulk analysis of BPF datasets with support for custom input lists, filtering, and detailed reporting.
* **dynptr Tracking:** Models `bpf_dynptr_*` helpers including clone lineage, read-only slice enforcement, and per-source-kind rules (SKB, `user_ringbuf`, `mem`).
* **kptr / Kernel Pointer Analysis:** Full offset representation, ALU arithmetic, `bpf_kptr_xchg` semantics, and per-CPU kptr support.
* **RCU Safety:** Detects nested RCU read-lock violations, demotes `MEM_RCU` on unlock, and validates sleepable subprog calls inside RCU critical sections.
* **Iterator Support:** Synthesises `bpf_iter__<subtype>` entry-arguments and per-subtype payload types from BTF annotations.
* **BTF CO-RE Foundation:** Parses `.BTF.ext` CO-RE relocation records; resolves `__ksym` externs via `BPF_PSEUDO_BTF_ID`; derives map-of-map inner indices from BTF `__array` annotations.
* **Struct Ops & Callbacks:** Accurately types `freplace`/`fexit`/`fentry` targets, exception callbacks, timer callbacks, and `for_each_map_elem` callbacks from their BTF signatures.
* **Arena Support:** Classifies `__arg_arena` parameters, syncs DBM bounds before widening, and correctly types `PtrToAllocMem` in pointer arithmetic.
* **Loop Widening (v6.15):** Multi-counter, spill-aware, and accumulator-feed widening strategies covering descending counters, branch-only register demotion, and eviction-resistant precise-PC walking.
* **v6.15 Corpus Verified:** 3278 PASS / 0 FA / 0 FR / 0 ERROR against the Linux v6.15 selftest suite.

## Installation

Ensure you have Rust installed (via `rustup`). Clone the repository and build:

```bash
cargo build --release
```

## Architecture Overview

### Loading and Parsing Pipeline

The verifier processes eBPF programs through a multi-stage pipeline:

```
ELF File (.o)
    │
    ├─► ELF Parsing (goblin)
    │   ├── Extract section headers and names
    │   ├── Load BPF maps from .maps section
    │   ├── Parse BTF (BPF Type Format) if present
    │   └── Process relocations for map references
    │
    ├─► Raw Instruction Extraction
    │   ├── Locate code sections (e.g., "tc", "xdp", "kprobe/...")
    │   ├── Extract 8-byte BPF instructions
    │   └── Identify function boundaries via symbols
    │
    ├─► AST Lowering (bpf_to_ast)
    │   ├── Decode opcodes into typed instructions
    │   ├── Handle 64-bit immediates (LD_IMM64)
    │   ├── Resolve branch targets
    │   └── Validate instruction encoding
    │
    └─► Control Flow Graph Construction
        ├── Identify basic blocks
        ├── Build predecessor/successor edges
        ├── Detect loops (back-edges)
        └── Compute liveness information
```

**Key Modules:**
- `parsing/elf/` - ELF file handling: sections, symbols, relocations
- `parsing/bpf_insn.rs` - Raw BPF instruction representation
- `parsing/bpf_to_ast.rs` - Instruction decoding to typed AST
- `parsing/btf.rs` - BPF Type Format parsing
- `analysis/flow/cfg.rs` - Control flow graph construction
- `analysis/flow/liveness.rs` - Register liveness analysis

### Abstract Domain

The verifier tracks program state using complementary abstract domains:

**1. Numeric Domain (selectable via flags)**

*Zone Domain (default, `--zone-mode`):*
- Uses Difference Bound Matrices (DBM) to represent constraints of the form `xi - xj <= c`
- Tracks relational bounds between registers (e.g., `r1 <= r2 + 10`)
- Enables precise reasoning about pointer arithmetic and array bounds
- Implemented with Floyd-Warshall closure for constraint propagation
- More precise than kernel, especially for packet bounds checking

*Interval Domain (`--kernel-mode`):*
- Tracks per-register bounds only (min, max for each register)
- Matches the kernel verifier's numeric analysis
- Faster but less precise (no relational constraints)
- Use for kernel compatibility testing

**2. Tri-state Numbers (Tnum)**
- Each bit is classified as: known-0, known-1, or unknown
- Enables precise bitwise operation analysis (AND, OR, XOR, shifts)
- Complements numeric domain for non-relational reasoning
- Used in both Zone and Interval modes

### Pruning Strategy

State-space exploration can explode exponentially. The verifier employs sophisticated pruning to ensure termination while maintaining soundness:

#### 1. State Subsumption
At designated prune points (merge points in the CFG), the verifier checks if the current state is *subsumed* by a previously explored state. State `A` subsumes state `B` if `A` covers all possible behaviors of `B`:

- **Type Subsumption:** Register types must be compatible (e.g., `PtrToMapValue` subsumes itself with matching map index)
- **DBM Subsumption:** For each live register, old bounds must be at least as permissive: `old_min <= cur_min && old_max >= cur_max`
- **Tnum Subsumption:** Old tnum's unknown bits must be a superset of current's unknown bits
- **Stack Subsumption:** Stack slot types must be compatible across frames
- **Caller Frame Subsumption:** Callee-saved registers (r6-r9) in caller frames must also be subsumed

```
If old_state subsumes cur_state:
    → Prune cur_state (already covered)
Else:
    → Continue exploration, save state for future comparisons
```

#### 2. Loop Handling with Widening
Loops require special treatment to ensure termination. The verifier detects loops via back-edges and applies widening:

**Loop Detection:**
- A back-edge is identified when a branch target is at a lower PC than the branch instruction
- The verifier tracks execution history to distinguish true loops from re-entry via different call paths

**Widening Strategy:**
1. On first loop iteration: record the state at the loop head
2. On subsequent iterations: apply widening to accelerate convergence
   - DBM widening: if a bound increased, set it to infinity
   - Tnum widening: if a tnum changed, set to fully unknown
3. Check for convergence: if widened state subsumes current state, the loop is verified

**Bounded Loop Detection (`--detect-bounded-loops`, default: enabled):**
For loops with compile-time bounds (e.g., `for (i = 0; i < 40; i++)`), the verifier detects the pattern:
```c
if (r != K) goto loop_head  // K is the bound
```
And applies the constraint `r < K` to enable faster convergence without losing precision. This is a precision improvement over the kernel verifier.

**Single-Entry Loop Requirement (`--single-entry-loops`):**
The kernel's bounded loop support uses dominator tree analysis, which requires loops to have a single entry point. Code that jumps into the middle of a loop (skipping over the loop head) is rejected with a "back-edge" error:
```c
// REJECTED: jumps into middle of loop
    goto condition;
body:
    r0 += 1;
condition:
    if (r0 < 4) goto body;
```
This check is enabled automatically by `--kernel-mode`.

**Loop Exit Verification:**
The verifier ensures loops have feasible exit paths:
- Loops must contain conditional branches (potential exits)
- Exit paths must be actually explored (not just syntactically present)
- Loops without verified exits are rejected via complexity limit

#### 3. Liveness-Based Pruning
Only live registers (those that may be read before being overwritten) are considered in subsumption checks. This significantly reduces false negatives in pruning:

```
At PC 50, if only r0, r1, r6 are live:
    → Compare only these registers for subsumption
    → Differences in r2-r5, r7-r10 are ignored
```

## Usage

The CLI is split into a small Rust binary (`zovia`, three user-facing
verbs) and a set of Python tools under `scripts/` for corpus
benchmarking and baseline diffing. Build with `cargo build --release`,
then invoke `./target/release/zovia` (or `cargo run --release --`).

### Top-level commands

```
zovia elf    <path> [...]      Inspect ELF / BTF contents (no verification)
zovia verify <path> [...]      Verify an eBPF program (auto-detects .o, .c, .json)
zovia pcc    <gen|check|cycle> Proof-Carrying Code certificate workflows
zovia dev    <subcommand>      Internal corpus / baseline / selftest harness
```

`zovia --help` and `zovia <verb> --help` print the full clap-generated
flag table — the canonical reference. Highlights below.

#### `elf <path>`

| Flag | Effect |
| --- | --- |
| *(none)* | List sections, programs, and maps |
| `--section <S>` | Analyze a single section |
| `--func <F>` | Analyze the section containing a given function |
| `--all` | Analyze every code section in the file |
| `--struct-ops <S>` | Diagnostic: dump the struct\_ops methods of struct `S` |
| `--btf-func <F>` | Diagnostic: print BTF parameter list of FUNC `F` |
| `--bindings` | Diagnostic: dump struct\_ops bindings recovered from `.struct_ops` sections |

#### `verify <path>`

Auto-detects input by extension:
* `.o` → ELF (use `--section S`, `--func F`, or default to whole file)
* `.c` → upstream selftest source, compiled via clang (use `--defines D1,D2,…`)
* `.json` → legacy test catalogue. Bare `verify foo.json` lists tests; pick one with `--test "<name>"`. (Bulk runs live under `dev legacy-selftest`.)

`--kind elf|c|json` forces the input kind when the extension is missing or ambiguous.

#### `pcc <gen|check|cycle>`

```
zovia pcc gen   <json> --test <name> [--out <cert>]    # zone-mode generation
zovia pcc check <json> --test <name> --cert <path>     # interval-mode verify
zovia pcc cycle <json> --test <name> [--out <cert>]    # gen + check in one
```

#### `dev <subcommand>`

Internal harness commands; not part of the user-facing surface and
subject to change. Run `zovia dev --help` for the list. Commonly used:

* `dev selftest-file <prog.c> [defines]` — single upstream-style C selftest
* `dev selftest-suite <progs_dir>` — every `.c` selftest in a directory
* `dev selftest-baseline-write-upstream <upstream_root> <out.json>` — full sweep against a kernel checkout (writes the gold-standard baseline)
* `dev selftest-baseline-check-modern <progs_dir> <baseline.json>` — fast in-place check (skips non-deterministic baseline rows)
* `dev verify-corpus <dir> --out FILE.jsonl` — JSONL emitter (one record per file/section); the single Rust entrypoint that the Python harnesses sit on top of
* `dev legacy-selftest {list|single|run|suite}` — pre-6.2 JSON corpus runner
* `dev pcc-regress [manifest]` — PCC regression manifest

### Configuration flags (global)

All flags are global and may appear before *or* after the subcommand.

| Flag | Effect |
| --- | --- |
| `-q`, `--quiet` | Errors only |
| `-v`, `--verbose` | Trace execution |
| `--very-verbose` | Full debug |
| `--kernel-mode` | Simulate the kernel verifier (interval domain + strict loops; disables bounded-loop detection) |
| `--zone-mode` | Zone domain (default, more precise) |
| `--detect-bounded-loops` / `--no-detect-bounded-loops` | Pattern-match early loop convergence |
| `--single-entry-loops` / `--multi-entry-loops` | Loop-entry strictness |
| `--enable-private-stack` / `--disable-private-stack` | v6.12 private-stack model (default ON) |
| `--max-insn <N>` | Step budget (default 1,000,000) |
| `--max-states <N>` | Per-PC state cap for pruning (default 8) |
| `--skip-dbm`, `--use-widening`, `--enable-path-trace` | Analysis tweaks |
| `--debug-pc <PC>`, `--log-interval <N>` | Diagnostics |
| `--map-override <name:size>` | Override a map's value size, repeatable |

## Python harnesses (`scripts/`)

Corpus walking, filtering, baseline diffing, bench reports, and CI
gating live in Python on top of `dev verify-corpus`. The Rust binary
stays focused on verification.

| Script | What it does |
| --- | --- |
| `scripts/bench_e2e.py` | End-to-end BCF bundle bench: phase 1 builds bundles via `zovia --bcf --kernel-mode verify`, phase 2 ships to cloudlab + kernel-loads via `test_loader`. Writes TSV. See script docstring. |
| `scripts/fa_scorecard.py` | Per-commit BCF gate: runs zovia against the cil42 / shift_constraint oracles, prints `CA/CR/FA/BP/FR/POSTVERIF` counts. Exit non-zero on any FA. |
| `scripts/parallel_selftest.py` | Fast upstream-selftest gate (minutes, not 2h). Runs the selftest suite in parallel and compares to the FA=2 baseline. |
| `scripts/l3_sweep.py` | L3 corpus sweep harness (cilium/calico, scored against an oracle). |
| `scripts/triage_frs.py` | FR triage tool — buckets failure reasons across a corpus run. |
| `scripts/calico_anchor_unified_bundle.sh` | Builds the 7/7-anchor unified bundle and runs `test_loader --type classifier` against it; gate for calico anchor regressions. |
| `scripts/zovia_memory_cop.sh` | Background memory cop: kills the largest zovia worker(s) when cumulative RSS across `./target/release/zovia` workers exceeds the cap. |
| `scripts/prevail.py` | Prevail catalogue runner + benchmark. Same JSON output shape as the old Rust path. |
| `scripts/demo_e2e.sh`, `scripts/demo_e2e_cilium.sh` | Demo drivers for the end-to-end flow. |
| `scripts/bench_e2e_legacy.py`, `scripts/calico_anchor_unified_bundle_legacy.sh` | Older single-pass variants kept for reference; use the non-`_legacy` versions for current work. |

## Examples

**1. Inspect an object file:**
```bash
zovia elf ./bpf_host.o
```

**2. Verify one section / one function / the whole file:**
```bash
zovia verify ./bpf_host.o --section tc
zovia verify ./bpf_host.o --func handle_packet
zovia verify ./bpf_host.o            # all sections
```

**3. Run a single legacy JSON test:**
```bash
zovia verify ./selftests/legacy/verifier/calls.json --test "calls: invalid kfunc call"
```

**4. Generate and check a PCC certificate in one shot:**
```bash
zovia pcc cycle pcc-tests/pcc_examples.json \
    --test "pcc motivating: var add packet access (zone ok, kernel reject)"
```

**5. End-to-end BCF bundle bench on a corpus:**
```bash
scripts/bench_e2e.py --list /tmp/calico_repr_list.txt --jobs 8 \
    --out /tmp/bench.tsv --kernel-test
```

**6. Prevail bench on a real-world corpus:**
```bash
scripts/prevail.py benchmark ~/ebpf-samples --project cilium
```

**7. Run modernized selftests in kernel-compatible mode:**
```bash
zovia --kernel-mode dev selftest-suite vendor/linux/tools/testing/selftests/bpf/progs
```

## Troubleshooting

The verifier can be strict. Below are common error patterns and how to resolve them.

### 1. Complexity Limit Exceeded
**Error:** `FAIL: Complexity limit of 1000000 exceeded`
**Cause:** The program has too many possible execution paths, often due to nested loops or many conditional branches.
**Solutions:**
*   Increase the limit with `--max-insn <N>`.
*   Enable **widening** with `--use-widening` to force loop convergence (may introduce unsoundness).
*   Use `--skip-dbm` to skip relational numeric analysis, which is faster but less precise.

### 2. Pointer / Stack Out of Bounds
**Error:** `FAIL: Stack out of bounds at pc 12: offset -128, size 8`
**Cause:** Accessing memory outside the allocated stack frame (e.g., `r10 - 512`) or beyond a map value boundary.
**Example Fix:**
```c
// Unsafe: offset might be OOB
val = bpf_map_lookup_elem(&my_map, &key);
if (val) {
    long x = *(long *)(val + offset); // Check your bounds!
}
```

### 3. Unsafe Generic Load/Store
**Error:** `FAIL: Unsafe generic load at pc 45: base R0, offset 0`
**Cause:** Attempting to dereference a pointer that might be `NULL` or is not of a memory-pointing type.
**Solution:** Always perform a null-check after map lookups or helper calls that return pointers.
```c
struct data *d = bpf_map_lookup_elem(&maps, &key);
if (!d) return 0; // The verifier now knows R0 is a valid pointer here
```

### 4. DBM Inconsistency
**Error:** `FAIL: DBM inconsistent at pc 80`
**Cause:** The analyzer found a logical contradiction in the numeric constraints (e.g., a path where `r1 < 5` AND `r1 > 10`). This often indicates unreachable code or a bug in the analyzer's pruning logic.
**Debugging:** Run with `-vv` to see the RELATIONAL constraints leading to the contradiction.

### 5. Relocation Info Missing
**Error:** `FAIL: Relocation info missing at pc 5`
**Cause:** The ELF file was compiled without relocation data for maps or global variables.
**Solution:** Ensure you are compiling with `-target bpf` and recent Clang/LLVM versions.

## Project Structure

```
src/
├── analysis/
│   ├── flow/               # CFG, liveness, merging, subprogram handling
│   │   └── pruning/        # State subsumption and loop widening
│   │       ├── subsumption.rs
│   │       └── widening.rs
│   ├── machine/            # Abstract state: registers, stack, frames
│   │   ├── state.rs        # Per-PC abstract state
│   │   ├── stack_ops.rs    # Stack slot operations (spill/fill/zext)
│   │   └── reg_types.rs    # Register type lattice
│   └── transfer/           # Transfer functions for each instruction type
│       ├── alu/            # Arithmetic and bitwise operations
│       ├── branch/         # Conditional branches and refinement
│       ├── call/           # BPF helper and kfunc calls
│       │   ├── checks.rs       # Argument type validation
│       │   ├── mem_checks.rs   # Memory-argument validation
│       │   ├── helper_protos.rs
│       │   ├── kfunc_protos.rs
│       │   ├── callback.rs     # Callback subprogram handling
│       │   └── validators/     # Per-argument-kind validators
│       ├── memory/         # Load/store, packet access, map access
│       └── field_tables.rs # BTF field-trust tables (RCU, kptr, etc.)
├── ast/                    # Typed instruction representation
├── common/                 # Configuration, utilities
├── domains/                # Abstract domains
│   ├── zone/               # Zone domain (DBM-based)
│   │   ├── dbm.rs          # Difference Bound Matrix
│   │   └── ops.rs          # Domain operations (assume, widen, etc.)
│   ├── interval/           # Interval domain (kernel-mode)
│   └── tnum.rs             # Tri-state numbers (shared)
├── parsing/                # ELF loading, instruction decoding, BTF
│   ├── btf/                # BPF Type Format
│   │   ├── context/        # Querying BTF: fields, kptr, funcs, datasec
│   │   ├── ext.rs          # .BTF.ext / CO-RE relocation records
│   │   └── map_defs.rs     # Map-of-maps BTF resolution
│   └── elf/                # ELF-specific: maps, programs, relocations, struct_ops
├── pcc/                    # Proof-Carrying Code
│   ├── generator/          # Zone-mode certificate generation
│   └── checker/            # Interval-mode certificate checking
└── testing/                # Test runners (see also: scripts/ for corpus harnesses)
    ├── runner.rs           # Core analysis driver (Analyzer)
    ├── jsonl.rs            # JSONL corpus emitter (`dev verify-corpus`)
    ├── legacy_selftest.rs  # Pre-6.2 JSON test corpus
    ├── pcc_test.rs         # PCC certificate workflows
    ├── selftest/           # Modern upstream selftest pipeline (clang + attrs)
    ├── scanner.rs          # ELF/BTF metadata extractor (`dev benchmark-scan`)
    └── logging.rs          # PC-range / register-trace filtering
```
