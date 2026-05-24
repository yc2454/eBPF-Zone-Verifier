# Setup

One Linux host (Ubuntu 22.04+ / Debian 12+, sudo, KVM). Cloudlab Ubuntu
profiles work as-is.

zovia sits on top of [BCF](https://github.com/SunHao-0/BCF): we reuse its
deps, VM image, in-VM bpftool/cvc5, qemu launcher, and patched libbpf. We
ship our own kernel `bzImage` and the verifier binary.

---

## 1. Clone BCF and install dependencies

```bash
git clone https://github.com/SunHao-0/BCF ~/BCF
cd ~/BCF
./scripts/install-deps.sh                          # kernel + cvc5 + qemu + rustup + virtiofsd
sudo apt install -y clang llvm libbpf-dev dwarves  # zovia extras: BPF compile + pahole (for BTF)
source "$HOME/.cargo/env"                          # if rustup was just installed
```

## 2. Download the BCF VM image

The image is ~4.7 GB. **On cloudlab, your `$HOME` quota is too small** —
put it under `/proj/ebpf-PG0/`:

```bash
# Cloudlab:
mkdir -p /proj/ebpf-PG0/bcf-vm
cd /proj/ebpf-PG0/bcf-vm
wget -O imgs.zip 'https://zenodo.org/records/17542583/files/imgs.zip?download=1'
unzip imgs.zip
chmod 600 bookworm.id_rsa

# Then symlink into ~/BCF/imgs/ (where BCF's scripts look):
ln -sf /proj/ebpf-PG0/bcf-vm/bookworm.img     ~/BCF/imgs/bookworm.img
ln -sf /proj/ebpf-PG0/bcf-vm/bookworm.id_rsa  ~/BCF/imgs/bookworm.id_rsa
ln -sf /proj/ebpf-PG0/bcf-vm/bookworm.id_rsa.pub ~/BCF/imgs/bookworm.id_rsa.pub
```

Non-cloudlab boxes: skip the symlinks, just `cd ~/BCF/imgs && wget … && unzip …`.

## 3. Build BCF's cvc5 and kernel tree

```bash
cd ~/BCF
./scripts/build.sh solver   # ~15 min — produces ~/BCF/output/cvc5-libs/bin/cvc5
./scripts/build.sh kernel   # ~30 min — clones bpf-next, applies BCF patches, builds bzImage + libbpf.a
```

`build.sh kernel` is required even though we override the bzImage in
step 4: it materializes the patched `libbpf.a` at
`~/BCF/build/bpf-next/tools/lib/bpf/`, which our loaders link against.

## 4. Replace BCF's bzImage with zovia's

```bash
# Get artifacts/bzImage from this repo (gitignored; ask Yalu or fetch from a Release).
cp ~/eBPF-Zone-Verifier/artifacts/bzImage ~/BCF/output/bzImage
```

Current pin: `6.18.0-rc4-g47b3934f7ad8`, branch `userspace-bcf`, sha256
`0755cb22fd116733714dad663c80bfd122bfbe247cd565691f3385bfc5249d6a`.

## 5. Build zovia

```bash
git clone <THIS_REPO_URL> ~/eBPF-Zone-Verifier
cd ~/eBPF-Zone-Verifier
cargo build --release
export ZOVIA_CVC5=~/BCF/output/cvc5-libs/bin/cvc5
```

Add the `export` line to `~/.bashrc` to persist.

## 6. Boot the VM

In a tmux/screen pane (VM dies when the parent shell exits):

```bash
cd ~/BCF
./scripts/boot_vm.sh        # qemu + virtiofs share ~/BCF → /root/bcf, ssh on localhost:10023
```

Verify from another shell:

```bash
ssh -i ~/BCF/imgs/bookworm.id_rsa -p 10023 root@localhost "uname -r"
# Expected: 6.18.0-rc4-g47b3934f7ad8
```

## 7. Build the in-VM loaders

```bash
cp ~/eBPF-Zone-Verifier/linux-deltas/test_loader.c ~/BCF/sweep/
cp ~/eBPF-Zone-Verifier/linux-deltas/ll2_loader.c  ~/BCF/sweep/

ssh -i ~/BCF/imgs/bookworm.id_rsa -p 10023 root@localhost <<'EOF'
cd /root/bcf/sweep
LIBBPF=/root/bcf/build/bpf-next/tools/lib
gcc -O2 -I$LIBBPF -o test_loader test_loader.c $LIBBPF/bpf/libbpf.a -lelf -lz
gcc -O2 -I$LIBBPF -o ll2_loader  ll2_loader.c  $LIBBPF/bpf/libbpf.a -lelf -lz
EOF
```

- `test_loader` — load object (+ optional bundle); `--per-prog` for the FA oracle.
- `ll2_loader` — same, but with kernel verifier `log_level=2` for debugging.

## 8. Smoke test

```bash
cd ~/eBPF-Zone-Verifier
OBJ=~/BCF/examples/shift_constraint.bpf.o
./target/release/zovia --bcf --kernel-mode verify "$OBJ"   # writes $OBJ.bcf-bundle

ssh -i ~/BCF/imgs/bookworm.id_rsa -p 10023 root@localhost \
  "/root/bcf/sweep/test_loader /root/bcf/examples/shift_constraint.bpf.o \
                               /root/bcf/examples/shift_constraint.bpf.o.bcf-bundle"
# Expected: SUCCESS: loaded 1/1 program(s)
```

---

## Environment variables

| Variable                    | Purpose                                                       |
|-----------------------------|---------------------------------------------------------------|
| `ZOVIA_CVC5`                | Absolute path to cvc5 (`~/BCF/output/cvc5-libs/bin/cvc5`)     |
| `ZOVIA_BUNDLE_KEEP=1`       | Append discharge entries (multi-pass bundle build)            |
| `ZOVIA_KERNEL_ENGINE=1`     | Enable kernel-shape exploration engine                        |
| `ZOVIA_KERNEL_ENGINE_AND=1` | AND-mode bundle merge (with `ZOVIA_KERNEL_ENGINE=1`)          |
| `ZOVIA_BCF_DUMP_SMT=1`      | Dump per-site SMT-LIB to disk (debugging)                     |

## Rebuilding the kernel

Only if you're modifying zovia's kernel side:

```bash
git clone <BPF_NEXT_ZOVIA_URL> ~/bpf-next-zovia
cd ~/bpf-next-zovia
git checkout userspace-bcf
cp ~/BCF/scripts/kernel-config .config
cat tools/testing/selftests/bpf/config \
    tools/testing/selftests/bpf/config.x86_64 \
    tools/testing/selftests/bpf/config.vm >> .config
make olddefconfig
make -j"$(nproc)" bzImage
cp arch/x86/boot/bzImage ~/BCF/output/bzImage
```

`bpf-next-zovia` is **not** upstream BCF + patches — it's a downstream
that diverged. Applying BCF's `patches-kernel/` to vanilla bpf-next won't
give you our kernel.

## Troubleshooting

**`gcc: bpf/libbpf.h: No such file or directory`** — `build.sh kernel` (step 3) hasn't run.

**`ld: cannot find -lbpf`** — Don't use `-lbpf`. Link `$LIBBPF/bpf/libbpf.a` directly (step 7).

**`test_loader: -EACCES` / "invalid bpf_bundle"** — zovia and the kernel are out of sync. Confirm both at the same SHA.

**`cvc5 binary not found`** — `export ZOVIA_CVC5=~/BCF/output/cvc5-libs/bin/cvc5`; re-run `build.sh solver` if missing.

**VM hangs on `boot_vm.sh`** — Stale virtiofsd socket: `rm -f ~/BCF/output/bpf-test.sock` and retry.

**`boot_vm.sh` exits when ssh disconnects** — VM is a child of the shell. Use tmux/screen.

**`uname -r` doesn't show our SHA** — bzImage wasn't replaced (step 4). `stat ~/BCF/output/bzImage` to check.
