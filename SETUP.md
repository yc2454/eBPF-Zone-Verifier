# Setup Guide

End-to-end setup for the eBPF Zone Verifier (zovia) + userspace BCF bundle
workflow. **One Linux host does everything** — verifier, kernel-under-test
VM, bundle producer, loader. Cloudlab Ubuntu profiles work as-is; any
Ubuntu 22.04+ / Debian 12+ box with sudo and KVM is fine.

## TL;DR

zovia builds on top of **BCF** (Hao Sun et al., SOSP'25 —
[github.com/SunHao-0/BCF](https://github.com/SunHao-0/BCF)). We reuse BCF's
VM image, its in-VM `bpftool`/`cvc5`, its qemu launcher, and — most
importantly — its dependency installer. We supply our own patched kernel
(a downstream of BCF's that has diverged significantly, not the upstream
BCF patches) and the zovia verifier binary.

```
       BCF (upstream)                     zovia (this repo)
  ─────────────────────────────      ────────────────────────────
  • install-deps.sh ◀── deps        • zovia verifier (Rust)
  • VM image (bookworm.img)          • Patched kernel bzImage
  • In-VM bpftool + cvc5               (overrides BCF's after their
  • Host-side cvc5 binary               build.sh kernel produces one)
  • Patched libbpf static lib         • Bundle producers (calico, etc.)
    (built by build.sh kernel,        • test_loader / ll2_loader (.c)
     used by our loaders)
  • scripts/boot_vm.sh
```

---

## Dependencies

**BCF's `install-deps.sh` is the canonical dependency catalog.** It handles
~95% of what zovia needs, including a non-obvious one: it installs `rustup`
(so it can `cargo install virtiofsd`), which gives us a working Rust
toolchain for free. Don't install Rust separately.

What BCF installs (apt names; the installer auto-detects apt/dnf/pacman/brew):
- **Kernel-build**: `build-essential libncurses5-dev libssl-dev libelf-dev flex bison pkg-config libpcap-dev libcap-dev bc rsync unzip patch`
- **cvc5**: `cmake libgmp-dev libboost-all-dev libreadline-dev libedit-dev libffi-dev autoconf automake libtool`
- **VM**: `qemu-system-x86 qemu-utils openssh-server` + `rustup` (via curl) + `virtiofsd` (via cargo)
- **Python**: `numpy matplotlib scipy seaborn prettytable pandas`

What **zovia adds on top** (a single extra apt line):
```bash
sudo apt install clang llvm libbpf-dev dwarves
```
- `clang llvm libbpf-dev` — only if you want to recompile `.bpf.c` → `.bpf.o` yourself; sample objects come precompiled in `~/BCF/examples/` and in this repo's `bcf-tests/`.
- `dwarves` — provides `pahole`, **required** for `CONFIG_DEBUG_INFO_BTF=y` if you rebuild the kernel. Missing it silently disables BTF and any program using CO-RE returns `-ESRCH` at load. Skip if you only use the prebuilt `bzImage`.

KVM should be enabled (`kvm-ok` reports "acceleration can be used"). On
cloudlab, pick a profile with nested virtualization; on a plain VM, check
your hypervisor.

---

## Steps

### 1. Set up BCF (one time, ~30 min)

```bash
git clone https://github.com/SunHao-0/BCF ~/BCF
cd ~/BCF

# Installs all kernel/cvc5/VM deps + rustup + virtiofsd. See "Dependencies"
# above for the breakdown. Don't run as root; needs sudo for apt.
./scripts/install-deps.sh

# zovia's small extras (clang for compiling samples, dwarves only if you
# rebuild the kernel — see "Rebuilding the kernel" below)
sudo apt install -y clang llvm libbpf-dev dwarves

# Fetch the VM image bundle (rootfs + ssh key + a reference bzImage we discard)
cd imgs
wget -O imgs.zip 'https://zenodo.org/records/17542583/files/imgs.zip?download=1'
unzip imgs.zip
chmod 600 bookworm.id_rsa
cd ..

# Build the host-side cvc5
./scripts/build.sh solver
# Output: ~/BCF/output/cvc5-libs/bin/cvc5

# Build BCF's kernel + libbpf (~30 min). This materializes the patched
# libbpf static lib that our in-VM loaders link against. We override
# the resulting bzImage with zovia's in step 2, but the patched libbpf
# in ~/BCF/build/bpf-next/tools/lib/bpf/ stays put and is used by the
# loader compile step below.
./scripts/build.sh kernel
# Output: ~/BCF/output/bzImage (BCF's — we replace it)
#         ~/BCF/build/bpf-next/tools/lib/bpf/libbpf.a (patched, KEEP)

# Source rustup's shell hook if this is your first install
source "$HOME/.cargo/env"
```

### 2. Drop in zovia's kernel (replaces BCF's)

```bash
# Once we tag a release and attach the bzImage there:
#   wget -O ~/BCF/output/bzImage 'https://github.com/<owner>/<repo>/releases/download/<TAG>/bzImage'

# Until then, the canonical prebuilt lives in this repo's artifacts/ dir
# (gitignored — fetched from the cloudlab build host on demand):
cp ~/eBPF-Zone-Verifier/artifacts/bzImage ~/BCF/output/bzImage
```

Current artifact pin:
- File: `artifacts/bzImage` (42 MB)
- Kernel: `6.18.0-rc4-g47b3934f7ad8`, branch `userspace-bcf`
- sha256: `0755cb22fd116733714dad663c80bfd122bfbe247cd565691f3385bfc5249d6a`
- **Caveat**: HEAD is currently a WIP debug commit. The last clean commit
  is `9eee7bc66a0a` (`bcf: KIND_UNREACHABLE bundle discharge prunes the
  path`). For a real release, rebuild at the clean commit — see
  [Rebuilding the kernel](#rebuilding-the-kernel) below.

### 3. Build zovia

```bash
git clone <THIS_REPO_URL> ~/eBPF-Zone-Verifier
cd ~/eBPF-Zone-Verifier
cargo build --release

# Point zovia at BCF's cvc5
export ZOVIA_CVC5=~/BCF/output/cvc5-libs/bin/cvc5
```

### 4. Boot the VM

In a **persistent terminal** (tmux/screen — the VM is a child of this shell):

```bash
cd ~/BCF
./scripts/boot_vm.sh
# Boots qemu, mounts ~/BCF as virtiofs at /root/bcf inside the VM,
# exposes ssh on localhost:10023.
```

Verify from another shell:

```bash
ssh -i ~/BCF/imgs/bookworm.id_rsa -p 10023 root@localhost "uname -r && which bpftool"
# Expected: 6.18.0-rc4-g<sha> + /usr/bin/bpftool
```

### 5. Build the loaders inside the VM

zovia ships two C loaders alongside the bundle format. They statically
link against the patched libbpf built by step 1's `build.sh kernel`
(materialized at `~/BCF/build/bpf-next/tools/lib/bpf/libbpf.a`, visible
inside the VM via virtiofs). Compile in-VM so the resulting binary is
linked against the VM's libc / libelf / libz:

- [`linux-deltas/test_loader.c`](linux-deltas/test_loader.c) — the canonical
  bundle loader. Optional positional bundle argument:
  - **No bundle** → plain loader (the "base" mode used as the FA oracle).
  - **With bundle** → bundle-aware loader (the "tl2" mode used to verify
    that zovia's bundle is accepted by the kernel).
  - `--per-prog` → reopen the object once per program and report a kernel
    verdict for each (used by `fa_scorecard.py`).

- [`linux-deltas/ll2_loader.c`](linux-deltas/ll2_loader.c) — same default
  path, but runs at kernel verifier `log_level=2` and prints the full
  per-instruction trace. Used for debugging rejections.

`~/BCF` is mounted into the VM at `/root/bcf` via virtiofs, so copying
the sources into `~/BCF/sweep/` makes them visible inside the VM:

```bash
# On the host
cp ~/eBPF-Zone-Verifier/linux-deltas/test_loader.c ~/BCF/sweep/
cp ~/eBPF-Zone-Verifier/linux-deltas/ll2_loader.c ~/BCF/sweep/

# In the VM (ssh in)
ssh -i ~/BCF/imgs/bookworm.id_rsa -p 10023 root@localhost
cd /root/bcf/sweep

# Both loaders statically link the patched libbpf.a from the bpf-next
# tree (built by step 1's `build.sh kernel`). The VM's /usr/lib has
# libbpf.so.1 but no headers and no libbpf-dev package, so we go
# directly at the patched static lib in the kernel tree.
LIBBPF=/root/bcf/build/bpf-next/tools/lib
gcc -O2 -I$LIBBPF -o test_loader test_loader.c $LIBBPF/bpf/libbpf.a -lelf -lz
gcc -O2 -I$LIBBPF -o ll2_loader  ll2_loader.c  $LIBBPF/bpf/libbpf.a -lelf -lz
exit
```

The resulting binaries sit at `~/BCF/sweep/test_loader` and
`~/BCF/sweep/ll2_loader` on the host (because of the virtiofs share), and
at `/root/bcf/sweep/test_loader` / `/root/bcf/sweep/ll2_loader` inside the
VM.

### 6. End-to-end demo

Produce a bundle with zovia, then load it via `test_loader` in the VM:

```bash
cd ~/eBPF-Zone-Verifier

# Pick any sample object (BCF ships a few in ~/BCF/examples/)
OBJ=~/BCF/examples/shift_constraint.bpf.o

# Produce the bundle with zovia (writes <OBJ>.bcf-bundle next to the object)
./target/release/zovia --bcf --kernel-mode verify "$OBJ"

# Run the loader inside the VM — the object + bundle are already visible
# at /root/bcf/examples/ via virtiofs
VM_SSH=(ssh -i ~/BCF/imgs/bookworm.id_rsa -p 10023 -o StrictHostKeyChecking=no root@localhost)
"${VM_SSH[@]}" "/root/bcf/sweep/test_loader \
    /root/bcf/examples/shift_constraint.bpf.o \
    /root/bcf/examples/shift_constraint.bpf.o.bcf-bundle"
# Expected: "SUCCESS: loaded 1/1 program(s)"
```

For the calico anchor (seven-program object, our canonical e2e benchmark):

```bash
# Pre-stage the .o under ~/BCF so the VM can see it
cp /path/to/anchor_to_tnl_debug.o ~/BCF/sweep/

# Build the unified bundle on the host
ZOVIA=./target/release/zovia \
ANCHOR=~/BCF/sweep/anchor_to_tnl_debug.o \
  ./scripts/calico_anchor_unified_bundle.sh

# Load whole object in the VM
"${VM_SSH[@]}" "/root/bcf/sweep/test_loader --type classifier \
    /root/bcf/sweep/anchor_to_tnl_debug.o \
    /root/bcf/sweep/anchor_to_tnl_debug.o.bcf-bundle"
# Expected: "SUCCESS: loaded 7/7 program(s)"
```

---

## Environment variables

| Variable                    | Purpose                                                       |
|-----------------------------|---------------------------------------------------------------|
| `ZOVIA_CVC5`                | Absolute path to cvc5 (set to `~/BCF/output/cvc5-libs/bin/cvc5`) |
| `ZOVIA_BUNDLE_KEEP=1`       | Append discharge entries (multi-pass bundle build)            |
| `ZOVIA_KERNEL_ENGINE=1`     | Enable the kernel-shape exploration engine                    |
| `ZOVIA_KERNEL_ENGINE_AND=1` | AND-mode bundle merge (with `ZOVIA_KERNEL_ENGINE=1`)          |
| `ZOVIA_BCF_DUMP_SMT=1`      | Dump per-site SMT-LIB to disk (debugging)                     |

---

## Rebuilding the kernel

Only needed if you're modifying zovia's kernel side. Same Linux host works
fine; needs ~20 GB free + 8+ cores for a tolerable build time. **Make sure
`dwarves` is installed** (step 1's extras list) — without it, the build
silently produces a kernel that can't load CO-RE programs.

```bash
git clone <BPF_NEXT_ZOVIA_URL> ~/bpf-next-zovia
cd ~/bpf-next-zovia
git checkout userspace-bcf
cp ~/BCF/scripts/kernel-config .config
# Append the bpf selftest config knobs BCF expects:
cat tools/testing/selftests/bpf/config \
    tools/testing/selftests/bpf/config.x86_64 \
    tools/testing/selftests/bpf/config.vm >> .config
make olddefconfig
make -j"$(nproc)" bzImage
cp arch/x86/boot/bzImage ~/BCF/output/bzImage
```

Note: `bpf-next-zovia` is **not** the BCF patch series — it's a downstream
that started from BCF and diverged. Applying upstream BCF's `patches-kernel/`
on top of vanilla `bpf-next` will produce a *different* kernel than ours.

---

## Repository layout (for reference)

| Path                         | Purpose                                                    |
|------------------------------|------------------------------------------------------------|
| `src/`                       | zovia (Rust)                                               |
| `scripts/calico_anchor_unified_bundle.sh` | Build a 7-program unified bundle for the calico anchor |
| `scripts/bench_e2e.py`       | Parallel calico-71 e2e benchmark harness                   |
| `scripts/fa_scorecard.py`    | FA/FR scorecard vs. a kernel oracle                        |
| `selftests/`                 | upstream BPF selftests (FA/FR oracle)                      |
| `bcf-tests/`                 | curated BCF-bundle integration cases                       |

---

## Troubleshooting

**`test_loader` returns -EACCES with "invalid bpf_bundle"**
Bundle hash doesn't match what the kernel computes. Likely cause: zovia and
the running kernel are out of sync. Re-pull both to the same tag and
rebuild zovia.

**`gcc: ... bpf/libbpf.h: No such file or directory`**
You haven't run `./scripts/build.sh kernel` yet — that's what clones
bpf-next, applies BCF's set5 patches, and produces the patched libbpf
headers + static lib at `~/BCF/build/bpf-next/tools/lib/bpf/`.

**`ld: cannot find -lbpf`**
The Debian Bookworm VM has `libbpf.so.1` but no `libbpf-dev`. Don't use
`-lbpf` — link the patched static lib directly:
`$LIBBPF/bpf/libbpf.a -lelf -lz` (see the gcc one-liner in step 5).

**`cvc5 binary not found`**
`export ZOVIA_CVC5=~/BCF/output/cvc5-libs/bin/cvc5`. If that path doesn't
exist, run `~/BCF/scripts/build.sh solver`.

**VM doesn't boot / hangs on `boot_vm.sh`**
Check `~/BCF/output/vm.log` and `~/BCF/output/virtiofsd.log`. The most
common cause is a stale virtiofsd socket — `rm -f ~/BCF/output/bpf-test.sock`
and retry.

**`boot_vm.sh` exits when ssh disconnects**
The VM is a child of the shell running `boot_vm.sh`. Always launch it from
a tmux/screen pane, not from a one-shot ssh.

**Kernel boots but `uname -r` doesn't show our SHA**
The bzImage in `~/BCF/output/bzImage` wasn't replaced — BCF's `boot_vm.sh`
booted the reference kernel from `imgs.zip` instead. Verify
`stat ~/BCF/output/bzImage` matches what step 2 downloaded.

---

## Open-source notes

This guide deliberately keeps zovia decoupled from BCF's kernel build, so
that:
- Upstream BCF can evolve their kernel patches without breaking us.
- We can ship one bzImage artifact per zovia release without users
  having to compile a kernel.
- External contributors only need a Rust toolchain plus the BCF runtime
  substrate that's already public and citable on Zenodo.

When opening the repo for contributions, also publish:
- A GitHub Release per kernel tag carrying `bzImage` + a short changelog.
- A `KERNEL_VERSION` file at the repo root pinning the matching tag.
- The matching `bpf-next-zovia` branch (currently private).
