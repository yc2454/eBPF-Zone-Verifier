[
  {
    "name": "BPF_ATOMIC_FETCH_ADD smoketest - 64bit",
    "result": "ACCEPT",
    "insns": [
      {"code": 183, "dst": 0, "src": 0, "off": 0, "imm": 0},
      {"code": 122, "dst": 10, "src": 0, "off": -8, "imm": 3},
      {"code": 183, "dst": 1, "src": 0, "off": 0, "imm": 1},
      {"code": 219, "dst": 10, "src": 1, "off": -8, "imm": 1},
      {"code": 21, "dst": 1, "src": 0, "off": 2, "imm": 3},
      {"code": 183, "dst": 0, "src": 0, "off": 0, "imm": 1},
      {"code": 149, "dst": 0, "src": 0, "off": 0, "imm": 0},
      {"code": 121, "dst": 1, "src": 10, "off": -8, "imm": 0},
      {"code": 21, "dst": 1, "src": 0, "off": 1, "imm": 4},
      {"code": 183, "dst": 0, "src": 0, "off": 0, "imm": 2},
      {"code": 149, "dst": 0, "src": 0, "off": 0, "imm": 0}
    ]
  },
  {
    "name": "BPF_ATOMIC_FETCH_ADD smoketest - 32bit",
    "result": "ACCEPT",
    "insns": [
      {"code": 183, "dst": 0, "src": 0, "off": 0, "imm": 0},
      {"code": 98, "dst": 10, "src": 0, "off": -4, "imm": 3},
      {"code": 180, "dst": 1, "src": 0, "off": 0, "imm": 1},
      {"code": 195, "dst": 10, "src": 1, "off": -4, "imm": 1},
      {"code": 21, "dst": 1, "src": 0, "off": 2, "imm": 3},
      {"code": 183, "dst": 0, "src": 0, "off": 0, "imm": 1},
      {"code": 149, "dst": 0, "src": 0, "off": 0, "imm": 0},
      {"code": 97, "dst": 1, "src": 10, "off": -4, "imm": 0},
      {"code": 21, "dst": 1, "src": 0, "off": 1, "imm": 4},
      {"code": 183, "dst": 0, "src": 0, "off": 0, "imm": 2},
      {"code": 149, "dst": 0, "src": 0, "off": 0, "imm": 0}
    ]
  },
  {
    "name": "Can't use ATM_FETCH_ADD on frame pointer",
    "result": "REJECT",
    "errstr": "frame pointer is read only",
    "errstr_unpriv": "R10 leaks addr into mem",
    "insns": [
      {"code": 183, "dst": 0, "src": 0, "off": 0, "imm": 0},
      {"code": 122, "dst": 10, "src": 0, "off": -8, "imm": 3},
      {"code": 219, "dst": 10, "src": 10, "off": -8, "imm": 1},
      {"code": 149, "dst": 0, "src": 0, "off": 0, "imm": 0}
    ]
  },
  {
    "name": "Can't use ATM_FETCH_ADD on uninit src reg",
    "result": "REJECT",
    "errstr": "!read_ok",
    "insns": [
      {"code": 183, "dst": 0, "src": 0, "off": 0, "imm": 0},
      {"code": 122, "dst": 10, "src": 0, "off": -8, "imm": 3},
      {"code": 219, "dst": 10, "src": 2, "off": -8, "imm": 1},
      {"code": 149, "dst": 0, "src": 0, "off": 0, "imm": 0}
    ]
  },
  {
    "name": "Can't use ATM_FETCH_ADD on uninit dst reg",
    "result": "REJECT",
    "errstr": "!read_ok",
    "insns": [
      {"code": 183, "dst": 0, "src": 0, "off": 0, "imm": 0},
      {"code": 219, "dst": 2, "src": 0, "off": -8, "imm": 1},
      {"code": 149, "dst": 0, "src": 0, "off": 0, "imm": 0}
    ]
  },
  {
    "name": "Can't use ATM_FETCH_ADD on kernel memory",
    "result": "REJECT",
    "errstr": "only read is supported",
    "prog_type": 26,
    "expected_attach_type": 24,
    "kfunc": "bpf_fentry_test7",
    "insns": [
      {"code": 121, "dst": 2, "src": 1, "off": 0, "imm": 0},
      {"code": 183, "dst": 3, "src": 0, "off": 0, "imm": 1},
      {"code": 219, "dst": 2, "src": 3, "off": 0, "imm": 1},
      {"code": 183, "dst": 0, "src": 0, "off": 0, "imm": 0},
      {"code": 149, "dst": 0, "src": 0, "off": 0, "imm": 0}
    ]
  }
]
