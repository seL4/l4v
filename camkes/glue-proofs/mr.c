/* Relevant parts of libsel4 for seL4_GetMR and seL4_SetMR */
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
