# eBPF Zone Verifier

A robust, user-space static analyzer for eBPF (Extended Berkeley Packet Filter) programs. This tool verifies the safety and correctness of BPF bytecode by reconstructing control flow graphs (CFGs), tracking register values with abstract interpretation (Difference Bound Matrices and Tri-state Numbers), and validating memory accesses, context usage, and map operations.

## Features

* **Control Flow Reconstruction:** Parses raw BPF bytecode to build a navigable control flow graph.
* **Abstract Interpretation (Zone Domain):** Uses Difference Bound Matrices (DBM) to track relational constraints (e.g., `r1 < r2 + 10`) and value ranges.
* **Tri-state Numbers (Tnum):** Tracks bitwise knowledge (zeros, ones, and unknown bits) for precise bitwise operation analysis.
* **Context Validation:** Enforces strict access rules based on BPF program types (e.g., `sk_buff`, `xdp_md`, `bpf_sock_addr`).
* **Map Safety:** Validates map lookups and value dereferences, supporting map-in-map and global data (`.rodata`).
* **Dead Code Pruning:** Intelligently prunes unreachable paths using static branch evaluation and state comparison.
* **Selftest Suite:** Built-in support for running large JSON-based test suites (compatible with Kernel BPF tests).
* **Benchmarking Suite:** Bulk analysis of BPF datasets with support for custom input lists, filtering, and detailed reporting.

## Installation

Ensure you have Rust installed (via `rustup`). Clone the repository and build:

```bash
cargo build --release
```

## Usage

The tool is run via `cargo run -- [flags] <subcommand> [args]`.

### Subcommands

#### ELF Analysis
* **`elf-list <elf_path>`**: Lists all sections, BPF programs, and maps in an ELF file.
* **`elf-analyze <elf_path> <section_name>`**: Analyzes a specific BPF program in a section.
* **`elf-analyze-func <elf_path> <func_name>`**: Analyzes a specific program by its function name.
* **`elf-analyze-prog <elf_path>`**: Batch analyzes all code sections in the ELF file.
* **`elf-analyze-benchmark <dir_path>`**: Recursively scans a directory for `.o` files and runs analysis.

#### Selftests
* **`selftest-list <json_file>`**: Lists all tests contained in a JSON test file.
* **`selftest-run <json_file>`**: Runs all tests in a specific JSON file.
* **`selftest-single <json_file> <test_name>`**: Runs a single test by name from a JSON file.
* **`selftest-suite <json_dir>`**: Runs all JSON test files found in a directory.

### Configuration Flags

Flags must be placed *before* the subcommand.

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
| `--compiler <NAME>` | Filter by compiler version. | `--compiler clang-16` |
| `--opt <LEVEL>` | Filter by optimization level. | `--opt -O2` |
| `--source <NAME>` | Filter by original source file name. | `--source bpf_host` |
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
cargo run -- selftest-run ./selftests/calls.json
```

**4. Run a benchmark with filters:**
```bash
cargo run -- --project cilium --compiler clang-16 elf-analyze-benchmark ./bpf-progs
```

## Troubleshooting

* **"Unsafe Generic Load":** Often caused by reading from a map value that the analyzer thinks is scalar (integer). Ensure map lookups and bounds checks are correct.
* **"Complexity Limit Exceeded":** The program has too many paths. Try increasing `--max-insn`.
* **"Unsafe ctx store":** Writing to a read-only context field. Check if the program type supports writes at that offset.