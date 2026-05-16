#!/bin/bash
# Runs in VM. Loads wireguard with zovia's path-unreachable bundle and
# dumps the kernel's full bcf_canonical_hash byte stream(s) for the
# tail_nodeport_ipv6_dsr reject site.
#
# Output format (chunked since kernel-side fix for 513B truncation):
#   bcf_canonical_hash: buf.len=N hash=0xH off=OFF bytes: HH HH ...
# Reassembly: sort chunks by off=, concatenate hex runs per distinct hash.
TL=/root/bcf/build/test_loader
S=/root/bcf/sweep
dmesg -C
"$TL" --type classifier "$S/clang-14_-O1_bpf_wireguard.o" \
      "$S/clang-14_-O1_bpf_wireguard.o.bcf-bundle" >/dev/null 2>&1

echo "---DISTINCT-HASHES (count, len, hash)---"
dmesg | grep 'bcf_canonical_hash:' \
      | grep -oE 'buf\.len=[0-9]+ hash=0x[0-9a-f]+' \
      | sort | uniq -c

echo ""
echo "---FULL BYTE STREAMS (per distinct hash, reassembled from chunks)---"
# Collect all distinct (len, hash) pairs seen
dmesg | grep 'bcf_canonical_hash:' \
      | grep -oE 'buf\.len=[0-9]+ hash=0x[0-9a-f]+' \
      | sort -u | while read -r sig; do
    len=$(echo "$sig" | grep -oE 'buf\.len=[0-9]+' | grep -oE '[0-9]+')
    hash=$(echo "$sig" | grep -oE 'hash=0x[0-9a-f]+' | grep -oE '0x[0-9a-f]+')
    echo "=== buf.len=$len hash=$hash ==="
    # Extract all chunks for this hash, sort by off=, print hex bytes
    dmesg | grep "bcf_canonical_hash:.*hash=$hash " \
           | grep -oE 'off=[0-9]+ bytes: [0-9a-f ]+' \
           | sort -t= -k2 -n \
           | sed 's/off=[0-9]* bytes: //'
    echo ""
done
