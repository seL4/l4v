/* Relevant parts of libsel4 */
typedef unsigned int uint32_t;
typedef uint32_t seL4_Word;
typedef seL4_Word seL4_CPtr;
struct seL4_MessageInfo {
    uint32_t words[1];
};
typedef struct seL4_MessageInfo seL4_MessageInfo_t;
struct seL4_IPCBuffer_ {
    seL4_MessageInfo_t tag;
    seL4_Word msg[120];
    seL4_Word userData;
    seL4_Word caps_or_badges[3];
    seL4_CPtr receiveCNode;
    seL4_CPtr receiveIndex;
    seL4_Word receiveDepth;
};
typedef struct seL4_IPCBuffer_ seL4_IPCBuffer;
static inline seL4_MessageInfo_t __attribute__((__const__)) seL4_MessageInfo_new(uint32_t label, uint32_t capsUnwrapped, uint32_t extraCaps, uint32_t length)  {
    seL4_MessageInfo_t seL4_MessageInfo;
    seL4_MessageInfo.words[0] = 0;
    ((void)0);
    seL4_MessageInfo.words[0] |= (label & 1048575) << 12;
    ((void)0);
    seL4_MessageInfo.words[0] |= (capsUnwrapped & 7) << 9;
    ((void)0);
    seL4_MessageInfo.words[0] |= (extraCaps & 3) << 7;
    ((void)0);
    seL4_MessageInfo.words[0] |= (length & 127) << 0;
    return seL4_MessageInfo;
}
static inline uint32_t __attribute__((__const__)) seL4_MessageInfo_get_length(seL4_MessageInfo_t seL4_MessageInfo) {
    return (seL4_MessageInfo.words[0] & 0x7f) >> 0;
}
static inline seL4_MessageInfo_t __attribute__((__const__)) seL4_MessageInfo_set_length(seL4_MessageInfo_t seL4_MessageInfo, uint32_t v) {
    seL4_MessageInfo.words[0] &= ~0x7f;
    seL4_MessageInfo.words[0] |= (v << 0) & 0x7f;
    return seL4_MessageInfo;
}
enum  {
    seL4_GlobalsFrame = 4294950912U
};
static inline seL4_IPCBuffer *seL4_GetIPCBuffer() {
    return *(seL4_IPCBuffer **)seL4_GlobalsFrame;
}
static inline seL4_Word seL4_GetMR(int i) {
    return seL4_GetIPCBuffer()->msg[i];
}
static inline void seL4_SetMR(int i, seL4_Word mr) {
    seL4_GetIPCBuffer()->msg[i] = mr;
}
