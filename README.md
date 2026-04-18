# eBPF Zone Verifier

A robust, user-space static analyzer for eBPF (Extended Berkeley Packet Filter) programs. This tool verifies the safety and correctness of BPF bytecode by reconstructing control flow graphs (CFGs), tracking register values with abstract interpretation (Difference Bound Matrices and Tri-state Numbers), and validating memory accesses, context usage, and map operations.

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

The tool is run via `cargo run -- [flags] <subcommand> [args]`.

### Subcommands

#### ELF Analysis
* **`elf-list <elf_path>`**: Lists all sections, BPF programs, and maps in an ELF file.
* **`elf-analyze <elf_path> <section_name>`**: Analyzes a specific BPF program in a section.
* **`elf-analyze-func <elf_path> <func_name>`**: Analyzes a specific program by its function name.
* **`elf-analyze-prog <elf_path>`**: Batch analyzes all code sections in the ELF file.

#### Benchmarks
* **`bcf-benchmark <dir_path>`**: Runs the BCF (BPF Complexity Framework) benchmark suite. Recursively scans for `.o` files with naming pattern `clang-<VER>_-<OPT>_<SOURCE>.o`.
* **`prevail-benchmark <dir_path>`**: Runs the PREVAIL benchmark suite on real-world eBPF programs. Files in `invalid/` subdirectory are expected to be rejected; all others should be accepted.

#### Selftests
* **`selftest-list <json_file>`**: Lists all tests contained in a JSON test file.
* **`selftest-run <json_file>`**: Runs all tests in a specific JSON file.
* **`selftest-single <json_file> <test_name>`**: Runs a single test by name from a JSON file.
* **`selftest-suite <json_dir>`**: Runs all JSON test files found in a directory.

#### PREVAIL Catalogue Tests
* **`prevail-list <catalogue.json>`**: Lists all tests in a PREVAIL catalogue.
* **`prevail-run <catalogue.json>`**: Runs all tests in a catalogue (with expected outcomes).
* **`prevail-single <catalogue.json> <test_name>`**: Runs a single test by name.

### Configuration Flags

Flags must be placed *before* the subcommand.

#### Domain Mode

| Flag | Description |
| --- | --- |
| `--kernel-mode` | Simulate kernel verifier: interval domain + strict loop checks. |
| `--zone-mode` | Use zone domain (default, more precise than kernel). |

#### Loop Analysis

These flags control loop handling. `--kernel-mode` sets both automatically for kernel compatibility.

| Flag | Description | Default |
| --- | --- | --- |
| `--detect-bounded-loops` | Use pattern matching for early loop convergence. | `true` |
| `--no-detect-bounded-loops` | Disable bounded loop detection. | |
| `--single-entry-loops` | Reject loops with jumps into middle (kernel behavior). | `false` |
| `--multi-entry-loops` | Allow loops with any entry pattern. | `true` |

#### General Options

| Flag | Description | Default |
| --- | --- | --- |
| `-q`, `--quiet` | Minimal output (errors only). | |
| `-v`, `--verbose` | Trace execution (Instruction-level logging). | |
| `-vv`, `--very-verbose` | Full debug output (State & DBM details). | |
| `--max-insn <N>` | Maximum instructions to process before aborting. | `1,000,000` |
| `--skip-dbm` | Skip DBM comparisons in pruning (faster, less precise). | `false` |
| `--use-widening` | Use widening in pruning (speeds up loops, potentially unsound). | `false` |
| `--max-states <N>` | Maximum abstract states to keep per PC for pruning. | `8` |
| `--debug-pc <N>` | Force verbose logging only around a specific PC. | `None` |
| `--enable-path-trace` | Enable detailed path reconstruction for crash analysis. | `false` |
| `--map-override <name:size>` | Manually specify a map's value size (e.g., `my_map:64`). | |
| `--log-interval <N>` | Heartbeat log interval for long-running analyses. | `100,000` |

### Benchmark Filters

| Flag | Description | Example |
| --- | --- | --- |
| `--project <NAME>` | Filter by project subdirectory. | `--project cilium` |
| `--compiler <NAME>` | Filter by compiler version (BCF only). | `--compiler clang-16` |
| `--opt <LEVEL>` | Filter by optimization level (BCF only). | `--opt -O2` |
| `--source <NAME>` | Filter by original source file name (BCF only). | `--source bpf_host` |
| `--input-list <FILE>` | Use a specific file containing a list of ELF paths. | `--input-list files.txt` |

## Examples

**1. Inspect an object file:**
```bash
cargo run -- elf-list ./bpf_host.o
```

**2. Analyze a specific section:**
```bash
cargo run -- elf-analyze ./bpf_host.o tc
```

**3. Run the "calls" selftest suite:**
```bash
cargo run -- selftest-run ./selftests/legacy/verifier/calls.json
```

**4. Run the BCF benchmark with filters:**
```bash
cargo run -- --project cilium --compiler clang-16 bcf-benchmark ./bpf-progs
```

**5. Run the PREVAIL benchmark on real-world programs:**
```bash
# Run on all projects
cargo run -- prevail-benchmark ~/ebpf-samples

# Filter to a specific project
cargo run -- prevail-benchmark ~/ebpf-samples --project cilium

# Test the invalid programs (expected rejections)
cargo run -- prevail-benchmark ~/ebpf-samples --project invalid
```

**6. Run selftests in kernel-compatible mode:**
```bash
# Simulate kernel verifier behavior (interval domain + strict loop checks)
cargo run -- --kernel-mode selftest-suite ./selftests/legacy/verifier
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
│   ├── flow/           # CFG, liveness, pruning, subprogram handling
│   ├── machine/        # Abstract state: registers, stack, frames
│   └── transfer/       # Transfer functions for each instruction type
│       ├── alu/        # Arithmetic and bitwise operations
│       ├── branch/     # Conditional branches and refinement
│       ├── call/       # BPF helper calls and validation
│       └── memory/     # Load/store, packet access, map access
├── ast/                # Typed instruction representation
├── common/             # Configuration, utilities
├── parsing/            # ELF loading, instruction decoding, BTF
│   └── elf/            # ELF-specific: maps, programs, relocations
├── testing/            # Test runners and benchmarks
│   ├── bcf_benchmark.rs    # BCF benchmark runner
│   ├── benchmark_common.rs # Shared benchmark utilities
│   ├── prevail.rs          # PREVAIL tests and benchmark
│   ├── selftest.rs         # JSON-based test runner
│   └── runner.rs           # Core analysis driver
└── zone/               # Abstract domains
    ├── dbm.rs          # Difference Bound Matrix implementation
    ├── domain.rs       # Domain operations (assume, refine, etc.)
    └── tnum.rs         # Tri-state number implementation
```
