#!/usr/bin/env python3
"""Decode a bcf_canonical_hash byte stream into human-readable post-order nodes.

Encoding format (canonical_hash.rs / kernel/bpf/canonical_hash.c):
  TAG_VAR        (0x01): 9 B  — tag(1) code(1) vlen(1) params(2 LE) idx(4 LE)
  TAG_LEAF_CONST (0x02): 5+4*vlen B — tag(1) code(1) vlen(1) params(2 LE) args[vlen]×4 LE
  TAG_INTERNAL   (0x03): 5 B  — tag(1) code(1) vlen(1) params(2 LE)

Usage:
  # zovia side (env hatch):
  ZOVIA_BCF_DUMP_HASH_BYTES=1 zovia --bcf --kernel-mode verify foo.bpf.o 2>&1 \\
      | grep 'bcf_canonical_hash' | python3 scripts/bcf_decode.py

  # kernel side (chunked dump — requires canonical_hash.c fix):
  dmesg | grep 'bcf_canonical_hash.*hash=0x<TARGET>' | python3 scripts/bcf_decode.py

  # diff two streams (zovia vs kernel):
  diff <(... | python3 scripts/bcf_decode.py) <(... | python3 scripts/bcf_decode.py)
"""
import re, struct, sys

TAG_VAR        = 0x01
TAG_LEAF_CONST = 0x02
TAG_INTERNAL   = 0x03

TYPE_MASK = 0x07
OP_MASK   = 0xf8

TYPE_NAME = {0: 'BV', 1: 'BOOL', 2: 'LIST'}

OP_BV = {
    0x00: 'ADD', 0x08: 'VAL', 0x10: 'SUB', 0x18: 'VAR', 0x20: 'MUL',
    0x28: 'ITE', 0x30: 'OR',  0x38: 'EXTRACT', 0x40: 'BVSIZE',
    0x48: 'SEXT', 0x50: 'AND', 0x58: 'ZEXT',   0x60: 'XOR',
    0x68: 'BVSIZE2', 0x70: 'RSH', 0x78: 'BVNOT', 0x80: 'NEG',
    0x90: 'LSH', 0x98: 'CONCAT', 0xa8: 'REPEAT',
    0xb0: 'SDIV', 0xd0: 'SMOD',
}
OP_BOOL = {
    0x00: 'CONJ', 0x08: 'VAL', 0x18: 'VAR', 0x28: 'ITE',
    0x38: 'XOR', 0x40: 'DISJ', 0x48: 'BITOF', 0x80: 'NOT', 0x90: 'IMPLIES',
    # BPF_JXX predicates
    0x10: 'JEQ', 0x20: 'JGT', 0x30: 'JGE', 0x50: 'JNE',
    0x60: 'JSGT', 0x70: 'JSGE', 0xa0: 'JLT', 0xb0: 'JLE',
    0xc0: 'JSLT', 0xd0: 'JSLE',
}


def code_name(code):
    typ = code & TYPE_MASK
    op  = code & OP_MASK
    tname = TYPE_NAME.get(typ, f'T{typ}')
    if typ == 0:
        oname = OP_BV.get(op, f'OP_{op:#04x}')
    elif typ == 1:
        oname = OP_BOOL.get(op, f'OP_{op:#04x}')
    else:
        oname = f'OP_{op:#04x}'
    return f'{oname}_{tname}'


def args_val(args):
    if len(args) == 0:
        return ''
    if len(args) == 1:
        v = args[0]
        return f' = {v} (0x{v:x})'
    if len(args) == 2:
        v = args[0] | (args[1] << 32)
        return f' = {v} (0x{v:016x})'
    return f' args={args}'


def decode(data):
    i = 0
    n = 0
    nodes = []
    while i < len(data):
        tag = data[i]
        rem = len(data) - i
        if tag == TAG_VAR:
            if rem < 9:
                nodes.append(f'[{n}] TAG_VAR @{i}: TRUNCATED ({rem} B remain)')
                break
            code   = data[i+1]
            vlen   = data[i+2]
            params = struct.unpack_from('<H', data, i+3)[0]
            idx    = struct.unpack_from('<I', data, i+5)[0]
            nodes.append(
                f'[{n}] @{i:3d} VAR      code=0x{code:02x} {code_name(code):<16} '
                f'params=0x{params:04x} var_idx={idx}')
            i += 9
        elif tag == TAG_LEAF_CONST:
            need = 5
            if rem < need:
                nodes.append(f'[{n}] TAG_LEAF_CONST @{i}: TRUNCATED')
                break
            code   = data[i+1]
            vlen   = data[i+2]
            params = struct.unpack_from('<H', data, i+3)[0]
            need   = 5 + 4 * vlen
            if rem < need:
                nodes.append(f'[{n}] TAG_LEAF_CONST @{i}: TRUNCATED (need {need}, have {rem})')
                break
            args = [struct.unpack_from('<I', data, i+5+4*j)[0] for j in range(vlen)]
            nodes.append(
                f'[{n}] @{i:3d} CONST    code=0x{code:02x} {code_name(code):<16} '
                f'params=0x{params:04x} vlen={vlen}{args_val(args)}')
            i += need
        elif tag == TAG_INTERNAL:
            if rem < 5:
                nodes.append(f'[{n}] TAG_INTERNAL @{i}: TRUNCATED')
                break
            code   = data[i+1]
            vlen   = data[i+2]
            params = struct.unpack_from('<H', data, i+3)[0]
            nodes.append(
                f'[{n}] @{i:3d} INTERNAL code=0x{code:02x} {code_name(code):<16} '
                f'params=0x{params:04x} vlen={vlen}')
            i += 5
        else:
            nodes.append(f'[{n}] @{i:3d} UNKNOWN tag=0x{tag:02x}  '
                         f'next8={data[i:i+8].hex()}')
            break
        n += 1
    return nodes


def parse_hex(s):
    return bytes(int(x, 16) for x in s.split() if x.strip())


def reassemble_kernel_chunks(lines):
    """Sort 'off=N bytes: HH HH ...' chunks and return (len, hash, data)."""
    chunks = {}
    total_len = None
    total_hash = None
    for line in lines:
        m = re.search(
            r'buf\.len=(\d+)\s+hash=(0x[0-9a-f]+)\s+off=(\d+)\s+bytes:\s+([0-9a-f ]+)',
            line)
        if m:
            total_len  = int(m.group(1))
            total_hash = m.group(2)
            off        = int(m.group(3))
            chunks[off] = m.group(4).strip()
    if not chunks:
        return None, None, None
    full_hex = ' '.join(chunks[k] for k in sorted(chunks))
    return total_len, total_hash, parse_hex(full_hex)


def main():
    raw = sys.stdin.read()
    lines = raw.splitlines()

    # Detect input kind
    if any('off=' in l and 'bytes:' in l for l in lines):
        # Kernel chunked dump
        total_len, total_hash, data = reassemble_kernel_chunks(lines)
        if data is None:
            sys.exit('ERROR: could not parse kernel chunked lines')
        print(f'kernel stream: buf.len={total_len} hash={total_hash} '
              f'({len(data)} bytes reassembled)')
    elif any('[zovia] bcf_canonical_hash' in l for l in lines):
        data = None
        for l in lines:
            m = re.search(
                r'\[zovia\] bcf_canonical_hash: buf\.len=(\d+) bytes: ([0-9a-f ]+)', l)
            if m:
                total_len = int(m.group(1))
                data = parse_hex(m.group(2))
                print(f'zovia  stream: buf.len={total_len} ({len(data)} bytes)')
                break
        if data is None:
            sys.exit('ERROR: could not parse zovia line')
    else:
        # Treat stdin as raw hex
        data = parse_hex(raw)
        print(f'raw stream: {len(data)} bytes')

    print()
    nodes = decode(data)
    for nd in nodes:
        print(nd)
    print(f'\n{len(nodes)} nodes, {len(data)} bytes total')


if __name__ == '__main__':
    main()
