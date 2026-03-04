/* PCC motivating example:
 * baseline kernel mode rejects at packet load after var-add;
 * pc-annotation cert (guard + prestate chain) enables acceptance.
 */
SEC("tc")
int pcc_branch_guard_chain(struct __sk_buff *skb)
{
    void *data = (void *)(long)skb->data;
    void *data_end = (void *)(long)skb->data_end;
    void *tmp;
    __u32 v;

    /* Guard first byte load. */
    if (data + 1 > data_end)
        return 0;

    /* Variable packet pointer: data + (data[0] & 3). */
    v = *(__u8 *)data;
    v &= 3;
    tmp = data + v;

    /* Materialize data_end - 4 in a register and compare. */
    if (tmp >= data_end - 4)
        return 0;

    /* Safe under relational reasoning; baseline interval mode rejects. */
    return *(__u32 *)tmp;
}
