# BPF Static Analyzer

A robust, user-space static analyzer for eBPF (Extended Berkeley Packet Filter) programs. This tool verifies the safety and correctness of BPF bytecode by reconstructing control flow graphs (CFGs), tracking register values with abstract interpretation (Difference Bound Matrices), and validating memory accesses, context usage, and map operations.

It allows developers to debug verification failures (such as "Unsafe Generic Load" or "Unsafe ctx store") offline, without needing to load the program into a live Linux kernel.

## Features

* **Control Flow Reconstruction:** Parses raw BPF bytecode to build a navigable control flow graph.
* **Abstract Interpretation:** Uses Difference Bound Matrices (DBM) to track register value ranges and relational constraints (e.g., `r1 < r2 + 10`).
* **Context Validation:** Enforces strict access rules based on BPF program types (e.g., `sk_buff`, `xdp_md`, `bpf_sock_addr`).
* **Map Safety:** Validates map lookups and value dereferences, supporting map-in-map and global data (`.rodata`).
* **Dead Code Pruning:** Intelligently prunes unreachable paths using static branch evaluation.
* **Crash Path Reconstruction:** Generates detailed execution traces leading to safety violations.
* **Configurable:** Supports overrides for map sizes, instruction limits, and analysis verbosity.

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

### Configuration Flags

Flags must be placed *before* the subcommand.

| Flag | Description | Default |
| --- | --- | --- |
| `-q`, `--quiet` | Minimal output (errors only). |  |
| `-v`, `--verbose` | Trace execution (Instruction-level logging). |  |
| `-vv`, `--very-verbose` | Full debug output (State & DBM details). |  |
| `--max-insn <N>` | Maximum instructions to process before aborting (complexity limit). | `1,000,000` |
| `--skip-dbm` | Skip numerical pruning checks (faster, less precise). | `false` |
| `--max-states <N>` | Maximum abstract states to keep per PC for pruning. | `8` |
| `--debug-pc <N>` | Force verbose logging only around a specific PC. | `None` |
| `--enable-path-trace` | Enable detailed path reconstruction for crash analysis. | `false` |
| `--map-override <name:size>` | Override the value size of a specific map. Useful for "dummy" maps in test objects. |  |

### Examples

**1. Inspect an object file:**

```bash
cargo run -- elf-list ./bpf_host.o

```

**2. Analyze a specific section (e.g., Traffic Control ingress):**

```bash
cargo run -- elf-analyze-section ./bpf_host.o tc

```

**3. Run with a higher complexity limit and verbose logging:**

```bash
cargo run -- --max-insn 5000000 -v elf-analyze-section ./bpf_host.o tc

```

**4. Batch analyze an entire file, skipping DBM checks for speed:**

```bash
cargo run -- --skip-dbm elf-analyze-prog ./bpf_host.o

```

**5. Debug a specific crash at PC 431:**

```bash
cargo run -- --debug-pc 431 --enable-path-trace elf-analyze-section ./bpf_host.o cgroup/connect4

```

**6. Handle "Dummy Map" failures by overriding map size:**
If the verifier complains about a map size mismatch (e.g., declared 0 in ELF but used as 64), override it:

```bash
cargo run -- --map-override "test_cilium_metrics:64" elf-analyze-section ./bpf_lxc.o tail_handle_ipv6

```

## Troubleshooting

* **"Unsafe Generic Load":** Often caused by reading from a map value that the analyzer thinks is scalar (integer). Ensure map lookups and bounds checks are correct.
* **"Complexity Limit Exceeded":** The program has too many paths. Try increasing `--max-insn`.
* **"Unsafe ctx store":** The program is writing to a read-only context field. Check if the program type supports writes at that offset (e.g., `bpf_sock_addr` user IP).
* **False Positives on Config:** If code is guarded by a flag in a map (like `.rodata`), the analyzer might explore dead paths. Map overrides or content mocking (future feature) can resolve this.