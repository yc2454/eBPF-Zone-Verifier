/*
 * PCC motivating example: variable-length options header.
 *
 * Packet layout (TC/skb context):
 *   Byte 0:          length field; bits [1:0] = option word count (0–3 words)
 *   Bytes 1–3:       fixed header fields (ignored here)
 *   Bytes 4 .. 4+opt_bytes-1:  variable options  (0, 4, 8, or 12 bytes)
 *   Bytes 4+opt_bytes .. +3:   4-byte payload field  ← target access
 *
 * Bounds check: data + 20 > data_end → reject.
 *   Worst case = 4 (fixed) + 12 (max options) + 4 (payload) = 20 bytes.
 *
 * Safety argument:
 *   Let opt_bytes = (pkt[0] & 3) << 2  ∈ {0, 4, 8, 12}.
 *   After snap = data + 4:   snap − @end ≤ −20 + 4 = −16.
 *   After ptr  = snap + opt_bytes:
 *     Zone:     ptr − @end ≤ (snap − @end) + ub(opt_bytes)
 *                          = −16 + 12 = −4   ✓  (−4 ≤ −4 for u32 load)
 *     Interval: ptr − @end = ∞               ✗  (lost after variable add)
 *
 * PCC proof chain (for the u32 load at pc 12):
 *   Guard    pc=11,  r5 − @end ≤ −16   (interval pre-state proves this:
 *                                        constant-only path to this point)
 *   Transfer pc=11,  (r5,@end)→(r5,@end),  delta=12   [r5+=r4; ub(r4)=12]
 *   Sum: −16 + 12 = −4 = bound  ✓
 *
 * The snapshot register r6 (= r5 before the variable advance) is the
 * intermediate vertex in the zone's Floyd-Warshall closure:
 *   d[r5][@end] ≤ d[r5][r6] + d[r6][@end]  =  12 + (−16)  =  −4
 */
SEC("tc")
int pcc_var_opts_header(struct __sk_buff *skb)
{
    void *data     = (void *)(long)skb->data;      /* r2 */
    void *data_end = (void *)(long)skb->data_end;  /* r3 */

    /* pc 2–4: bounds check — data + 20 ≤ data_end */
    if (data + 20 > data_end)
        return 0;

    /* pc 5–7: opt_bytes = (pkt[0] & 3) << 2  ∈  {0, 4, 8, 12}
     *         zone: r4 ∈ [0, 12];  interval: r4 ∈ [0, 12]  (agree) */
    __u32 opt_bytes = (*(__u8 *)data & 3) << 2;    /* r4 */

    /* pc 8–9: ptr = data + 4  (skip fixed header)
     *         zone and interval both: r5 − @end ≤ −16 */
    __u8 *ptr  = (__u8 *)data + 4;                 /* r5 */

    /* pc 10: snap = ptr  — SNAPSHOT; zone records r6 − @end ≤ −16 exactly */
    __u8 *snap = ptr;                              /* r6  (intermediate vertex) */
    (void)snap;

    /* pc 11: ptr += opt_bytes  — variable advance; DIVERGENCE POINT
     *   zone:     ptr − @end ≤ d[r5][r6] + d[r6][@end] = 12 + (−16) = −4
     *   interval: ptr − @end = ∞  (relation to @end lost) */
    ptr += opt_bytes;

    /* pc 12: load 4-byte payload
     *   need: ptr − @end ≤ −4;  zone: −4 ≤ −4  ✓ (exactly tight) */
    return *(__u32 *)ptr & 1;
}
