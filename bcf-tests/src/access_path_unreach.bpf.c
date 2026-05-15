// SPDX-License-Identifier: GPL-2.0
/*
 * Synthetic minimal repro for memory-access-site path-unreachable
 * speculation (project_future_improvements.md §0).
 *
 * Pattern: along the fall-through of the *second* branch, path_conds
 * accumulate `r1 != K` and `r1 == K` on the same register. The interval
 * domain can't represent disequality so misses the inconsistency; the
 * load via the type-collapsed r4 is rejected at check_load's
 * `ScalarValue | NotInit` arm. cvc5 must discharge {r1!=6, r1==6} as
 * unsat, the resulting kind=UNREACHABLE bundle entry matches the
 * kernel's path_cond canonical hash (commit 39f5104ed029), and the path
 * is dropped (no cascade into the rest of the program).
 */

#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>

SEC("tracepoint/syscalls/sys_enter_execve")
int access_unreach(void *ctx)
{
	asm volatile(
		"call 0x7\n\t"                  /* r0 = bpf_get_prandom_u32 (wide u32) */
		"r1 = r0\n\t"
		"*(u64 *)(r10 - 16) = 0\n\t"    /* init fp-16 so the PtrToStack load is safe */
		"if r1 == 6 goto L1_%=\n\t"     /* taken: r1=[6,6]; fall-through: r1 wide (r1!=6 disequality) */
		"r4 = 0\n\t"                    /* fall-through (state_A): r4 = ScalarValue */
		"goto L2_%=\n\t"
		"L1_%=:\n\t"                    /* taken (state_B): r1 == 6 */
		"r4 = r10\n\t"
		"r4 += -16\n\t"                 /* r4 = PtrToStack(fp-16) */
		"L2_%=:\n\t"
		"if r1 != 6 goto END_%=\n\t"    /* state_A fall-through: path_conds {r1!=6, r1==6} UNSAT */
		"r6 = *(u64 *)(r4 + 0)\n\t"     /* load: state_A r4=scalar → speculation site */
		"END_%=:\n\t"
		"r0 = 0\n\t"
		::: "r0", "r1", "r4", "r6", "memory");

	return 0;
}

char _license[] SEC("license") = "GPL";
