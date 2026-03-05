// SPDX-License-Identifier: GPL-2.0
// PCC prototype example: masked variable offset packet access.
//
// Shape is inspired by stack varoff selftests, but rewritten into a packet
// access pattern with DBM-expressible constraints (difference bounds only).
//
// Key pattern:
//   r4 = *(u8 *)(data + 0)
//   r4 &= 7
//   r5 = data
//   r5 += r4
//   *(u32 *)(r5 + 0)
//
// Zone mode can retain relational packet-end facts; kernel-style interval
// mode can lose precision at the variable add and reject without PCC.

#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>

SEC("tc")
int pcc_masked_varoff_example(struct __sk_buff *skb)
{
    void *data = (void *)(long)skb->data;
    void *data_end = (void *)(long)skb->data_end;

    if (data + 12 > data_end)
        return 0;

    __u8 v = *(__u8 *)(data + 0);
    v &= 7;

    __u32 out = *(__u32 *)(data + v);
    (void)out;
    return 0;
}

char _license[] SEC("license") = "GPL";
