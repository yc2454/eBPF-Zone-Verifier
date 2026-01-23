# BPF Static Analyzer

A robust, user-space static analyzer for eBPF (Extended Berkeley Packet Filter) programs. This tool verifies the safety and correctness of BPF bytecode by reconstructing control flow graphs (CFGs), tracking register values with abstract interpretation (Difference Bound Matrices), and validating memory accesses, context usage, and map operations.

## Features

* **Control Flow Reconstruction:** Parses raw BPF bytecode to build a navigable control flow graph.
* **Abstract Interpretation:** Uses Difference Bound Matrices (DBM) to track register value ranges and relational constraints (e.g., `r1 < r2 + 10`).
* **Context Validation:** Enforces strict access rules based on BPF program types (e.g., `sk_buff`, `xdp_md`, `bpf_sock_addr`).
* **Map Safety:** Validates map lookups and value dereferences, supporting map-in-map and global data (`.rodata`).
* **Dead Code Pruning:** Intelligently prunes unreachable paths using static branch evaluation.
* **Benchmarking Suite:** Bulk analysis of BPF datasets with support for custom input lists, filtering, and detailed reporting (JSON/Text).
* **Timeout Detection:** Distinguishes between verification failures and complexity limit timeouts.

## Installation

Ensure you have Rust installed (via `rustup`). Clone the repository and build:

```bash
cargo build --release

```

## Usage

The tool is run via `cargo run` with specific flags and subcommands.

```bash
cargo run -- [flags] <subcommand> [args]

```

### Subcommands

* **`elf-list <elf_path>`**
Lists all sections, BPF programs, and maps contained in an ELF object file.
* **`elf-analyze-section <elf_path> <section_name>`**
Analyzes a specific BPF program located in the given ELF section.
* **`elf-analyze-func <elf_path> <func_name>`**
Analyzes a specific BPF program by its function name (symbol).
* **`elf-analyze-prog <elf_path>`**
Batch analyzes *all* code sections found in the ELF file and provides a summary report (Pass/Fail stats).
* **`elf-analyze-benchmark <dir_path>`**
Runs the benchmarking suite. By default, it recursively scans `<dir_path>` for `.o` files.
* **Output:** Reports are saved to the `results/` directory with a timestamp (e.g., `results/benchmark_2023-10-27_10-30-00_report.txt`).
* **Note:** The benchmark dataset used for testing can be downloaded from the [BCF Repository](https://github.com/SunHao-0/BCF/tree/1588d0338b4ab9fbda09cdc124c8fd88a41b0522/bpf-progs).



### Configuration Flags

Flags must be placed *before* the subcommand.

| Flag | Description | Default |
| --- | --- | --- |
| `-q`, `--quiet` | Minimal output (errors only). |  |
| `-v`, `--verbose` | Trace execution (Instruction-level logging). |  |
| `-vv`, `--very-verbose` | Full debug output (State & DBM details). |  |
| `--max-insn <N>` | Maximum instructions to process before aborting (complexity limit). | `1,000,000` |
| `--skip-dbm` | Skip DBM (numeric) comparisons in pruning (faster, less precise). | `false` |
| `--max-states <N>` | Maximum abstract states to keep per PC for pruning. | `8` |
| `--debug-pc <N>` | Force verbose logging only around a specific PC. | `None` |
| `--enable-path-trace` | Enable detailed path reconstruction for crash analysis. | `false` |

### Benchmark Options

These flags control the `elf-analyze-benchmark` command.

| Flag | Description | Example |
| --- | --- | --- |
| `--input-list <FILE>` | Use a specific file containing a list of ELF paths to analyze (one per line). Ignores directory scan if set. | `--input-list files.txt` |
| `--project <NAME>` | Filter by subdirectory name (e.g., source project). | `--project cilium` |
| `--compiler <NAME>` | Filter by compiler version. | `--compiler clang-16` |
| `--opt <LEVEL>` | Filter by optimization level. | `--opt -O2` |
| `--source <NAME>` | Filter by original source file name. | `--source bpf_host` |

### Interpreting Results

The benchmark report distinguishes between three outcomes:

* **PASS:** The program is fully verified and safe.
* **FAIL:** The verifier found a safety violation (e.g., OOB access, invalid pointer).
* **TIMEOUT:** The verifier hit the complexity limit (`--max-insn`) before finishing. This is often due to state explosion in loops.

### Examples

**1. Inspect an object file:**

```bash
cargo run -- elf-list ./bpf_host.o

```

**2. Analyze a specific section (e.g., Traffic Control ingress):**

```bash
cargo run -- elf-analyze-section ./bpf_host.o tc

```

**3. Run a benchmark on the "Cilium" project files compiled with Clang-16:**

```bash
cargo run -- --project cilium --compiler clang-16 elf-analyze-benchmark ./bpf-progs

```

**4. Run a benchmark using a custom list of files:**
Create a file `my_tests.txt` containing paths to ELF files, then run:

```bash
cargo run -- --input-list my_tests.txt elf-analyze-benchmark .

```

*(Note: The `.` argument is required by the CLI parser but ignored for file discovery when `--input-list` is present)*

## Troubleshooting

* **"Unsafe Generic Load":** Often caused by reading from a map value that the analyzer thinks is scalar (integer). Ensure map lookups and bounds checks are correct.
* **"Complexity Limit Exceeded":** The program has too many paths. Try increasing `--max-insn` or checking for "TIMEOUT" status in benchmarks.
* **"Unsafe ctx store":** The program is writing to a read-only context field. Check if the program type supports writes at that offset.