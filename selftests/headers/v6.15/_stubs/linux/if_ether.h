#ifndef _ZOVIA_STUB_LINUX_IF_ETHER_H
#define _ZOVIA_STUB_LINUX_IF_ETHER_H
#define ETH_HLEN 14
#define ETH_ALEN 6
#define ETH_P_IP   0x0800
#define ETH_P_IPV6 0x86DD
struct ethhdr {
    unsigned char h_dest[6];
    unsigned char h_source[6];
    unsigned short h_proto;
} __attribute__((packed));
#endif
