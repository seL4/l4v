typedef unsigned int uintptr_t;
typedef int intptr_t;
typedef signed char int8_t;
typedef short int16_t;
typedef int int32_t;
typedef long long int64_t;
typedef long long intmax_t;
typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
typedef unsigned long long uint64_t;
typedef unsigned long long uintmax_t;
typedef int8_t int_fast8_t;
typedef int64_t int_fast64_t;
typedef int8_t int_least8_t;
typedef int16_t int_least16_t;
typedef int32_t int_least32_t;
typedef int64_t int_least64_t;
typedef uint8_t uint_fast8_t;
typedef uint64_t uint_fast64_t;
typedef uint8_t uint_least8_t;
typedef uint16_t uint_least16_t;
typedef uint32_t uint_least32_t;
typedef uint64_t uint_least64_t;
typedef int32_t int_fast16_t;
typedef int32_t int_fast32_t;
typedef uint32_t uint_fast16_t;
typedef uint32_t uint_fast32_t;
struct seL4_MessageInfo {
    uint32_t words[1];
};
typedef struct seL4_MessageInfo seL4_MessageInfo_t;
static inline seL4_MessageInfo_t __attribute__((__const__))
seL4_MessageInfo_new(uint32_t label, uint32_t capsUnwrapped, uint32_t extraCaps, uint32_t length) {
    seL4_MessageInfo_t seL4_MessageInfo;
    seL4_MessageInfo.words[0] = 0;
    (void)0;
    seL4_MessageInfo.words[0] |= (label & 0xfffff) << 12;
    (void)0;
    seL4_MessageInfo.words[0] |= (capsUnwrapped & 0x7) << 9;
    (void)0;
    seL4_MessageInfo.words[0] |= (extraCaps & 0x3) << 7;
    (void)0;
    seL4_MessageInfo.words[0] |= (length & 0x7f) << 0;
    return seL4_MessageInfo;
}
static inline void
seL4_MessageInfo_ptr_new(seL4_MessageInfo_t *seL4_MessageInfo_ptr, uint32_t label, uint32_t capsUnwrapped, uint32_t extraCaps, uint32_t length) {
    seL4_MessageInfo_ptr->words[0] = 0;
    (void)0;
    seL4_MessageInfo_ptr->words[0] |= (label & 0xfffff) << 12;
    (void)0;
    seL4_MessageInfo_ptr->words[0] |= (capsUnwrapped & 0x7) << 9;
    (void)0;
    seL4_MessageInfo_ptr->words[0] |= (extraCaps & 0x3) << 7;
    (void)0;
    seL4_MessageInfo_ptr->words[0] |= (length & 0x7f) << 0;
}
static inline uint32_t __attribute__((__const__))
seL4_MessageInfo_get_label(seL4_MessageInfo_t seL4_MessageInfo) {
    return (seL4_MessageInfo.words[0] & 0xfffff000) >> 12;
}
static inline seL4_MessageInfo_t __attribute__((__const__))
seL4_MessageInfo_set_label(seL4_MessageInfo_t seL4_MessageInfo, uint32_t v) {
    (void)0;
    seL4_MessageInfo.words[0] &= ~0xfffff000;
    seL4_MessageInfo.words[0] |= (v << 12) & 0xfffff000;
    return seL4_MessageInfo;
}
static inline uint32_t __attribute__((__pure__))
seL4_MessageInfo_ptr_get_label(seL4_MessageInfo_t *seL4_MessageInfo_ptr) {
    return (seL4_MessageInfo_ptr->words[0] & 0xfffff000) >> 12;
}
static inline void
seL4_MessageInfo_ptr_set_label(seL4_MessageInfo_t *seL4_MessageInfo_ptr, uint32_t v) {
    (void)0;
    seL4_MessageInfo_ptr->words[0] &= ~0xfffff000;
    seL4_MessageInfo_ptr->words[0] |= (v << 12) & 0xfffff000;
}
static inline uint32_t __attribute__((__const__))
seL4_MessageInfo_get_capsUnwrapped(seL4_MessageInfo_t seL4_MessageInfo) {
    return (seL4_MessageInfo.words[0] & 0xe00) >> 9;
}
static inline seL4_MessageInfo_t __attribute__((__const__))
seL4_MessageInfo_set_capsUnwrapped(seL4_MessageInfo_t seL4_MessageInfo, uint32_t v) {
    (void)0;
    seL4_MessageInfo.words[0] &= ~0xe00;
    seL4_MessageInfo.words[0] |= (v << 9) & 0xe00;
    return seL4_MessageInfo;
}
static inline uint32_t __attribute__((__pure__))
seL4_MessageInfo_ptr_get_capsUnwrapped(seL4_MessageInfo_t *seL4_MessageInfo_ptr) {
    return (seL4_MessageInfo_ptr->words[0] & 0xe00) >> 9;
}
static inline void
seL4_MessageInfo_ptr_set_capsUnwrapped(seL4_MessageInfo_t *seL4_MessageInfo_ptr, uint32_t v) {
    (void)0;
    seL4_MessageInfo_ptr->words[0] &= ~0xe00;
    seL4_MessageInfo_ptr->words[0] |= (v << 9) & 0xe00;
}
static inline uint32_t __attribute__((__const__))
seL4_MessageInfo_get_extraCaps(seL4_MessageInfo_t seL4_MessageInfo) {
    return (seL4_MessageInfo.words[0] & 0x180) >> 7;
}
static inline seL4_MessageInfo_t __attribute__((__const__))
seL4_MessageInfo_set_extraCaps(seL4_MessageInfo_t seL4_MessageInfo, uint32_t v) {
    (void)0;
    seL4_MessageInfo.words[0] &= ~0x180;
    seL4_MessageInfo.words[0] |= (v << 7) & 0x180;
    return seL4_MessageInfo;
}
static inline uint32_t __attribute__((__pure__))
seL4_MessageInfo_ptr_get_extraCaps(seL4_MessageInfo_t *seL4_MessageInfo_ptr) {
    return (seL4_MessageInfo_ptr->words[0] & 0x180) >> 7;
}
static inline void
seL4_MessageInfo_ptr_set_extraCaps(seL4_MessageInfo_t *seL4_MessageInfo_ptr, uint32_t v) {
    (void)0;
    seL4_MessageInfo_ptr->words[0] &= ~0x180;
    seL4_MessageInfo_ptr->words[0] |= (v << 7) & 0x180;
}
static inline uint32_t __attribute__((__const__))
seL4_MessageInfo_get_length(seL4_MessageInfo_t seL4_MessageInfo) {
    return (seL4_MessageInfo.words[0] & 0x7f) >> 0;
}
static inline seL4_MessageInfo_t __attribute__((__const__))
seL4_MessageInfo_set_length(seL4_MessageInfo_t seL4_MessageInfo, uint32_t v) {
    (void)0;
    seL4_MessageInfo.words[0] &= ~0x7f;
    seL4_MessageInfo.words[0] |= (v << 0) & 0x7f;
    return seL4_MessageInfo;
}
static inline uint32_t __attribute__((__pure__))
seL4_MessageInfo_ptr_get_length(seL4_MessageInfo_t *seL4_MessageInfo_ptr) {
    return (seL4_MessageInfo_ptr->words[0] & 0x7f) >> 0;
}
static inline void
seL4_MessageInfo_ptr_set_length(seL4_MessageInfo_t *seL4_MessageInfo_ptr, uint32_t v) {
    (void)0;
    seL4_MessageInfo_ptr->words[0] &= ~0x7f;
    seL4_MessageInfo_ptr->words[0] |= (v << 0) & 0x7f;
}
struct seL4_CapData {
    uint32_t words[1];
};
typedef struct seL4_CapData seL4_CapData_t;
enum seL4_CapData_tag {
    seL4_CapData_Badge = 0,
    seL4_CapData_Guard = 1
};
typedef enum seL4_CapData_tag seL4_CapData_tag_t;
static inline uint32_t __attribute__((__const__))
seL4_CapData_get_CapDataType(seL4_CapData_t seL4_CapData) {
    return (seL4_CapData.words[0] >> 31) & 0x1;
}
static inline int __attribute__((__const__))
seL4_CapData_CapDataType_equals(seL4_CapData_t seL4_CapData, uint32_t seL4_CapData_type_tag) {
    return ((seL4_CapData.words[0] >> 31) & 0x1) == seL4_CapData_type_tag;
}
static inline uint32_t __attribute__((__pure__))
seL4_CapData_ptr_get_CapDataType(seL4_CapData_t *seL4_CapData_ptr) {
    return (seL4_CapData_ptr->words[0] >> 31) & 0x1;
}
static inline seL4_CapData_t __attribute__((__const__))
seL4_CapData_Badge_new(uint32_t Badge) {
    seL4_CapData_t seL4_CapData;
    seL4_CapData.words[0] = 0;
    (void)0;
    seL4_CapData.words[0] |= (seL4_CapData_Badge & 0x1) << 31;
    (void)0;
    seL4_CapData.words[0] |= (Badge & 0xfffffff) << 0;
    return seL4_CapData;
}
static inline void
seL4_CapData_Badge_ptr_new(seL4_CapData_t *seL4_CapData_ptr, uint32_t Badge) {
    seL4_CapData_ptr->words[0] = 0;
    (void)0;
    seL4_CapData_ptr->words[0] |= (seL4_CapData_Badge & 0x1) << 31;
    (void)0;
    seL4_CapData_ptr->words[0] |= (Badge & 0xfffffff) << 0;
}
static inline uint32_t __attribute__((__const__))
seL4_CapData_Badge_get_Badge(seL4_CapData_t seL4_CapData) {
    (void)0;
    return (seL4_CapData.words[0] & 0xfffffff) >> 0;
}
static inline seL4_CapData_t __attribute__((__const__))
seL4_CapData_Badge_set_Badge(seL4_CapData_t seL4_CapData, uint32_t v) {
    (void)0;
    (void)0;
    seL4_CapData.words[0] &= ~0xfffffff;
    seL4_CapData.words[0] |= (v << 0) & 0xfffffff;
    return seL4_CapData;
}
static inline uint32_t __attribute__((__pure__))
seL4_CapData_Badge_ptr_get_Badge(seL4_CapData_t *seL4_CapData_ptr) {
    (void)0;
    return (seL4_CapData_ptr->words[0] & 0xfffffff) >> 0;
}
static inline void
seL4_CapData_Badge_ptr_set_Badge(seL4_CapData_t *seL4_CapData_ptr,
                                      uint32_t v) {
    (void)0;
    (void)0;
    seL4_CapData_ptr->words[0] &= ~0xfffffff;
    seL4_CapData_ptr->words[0] |= (v << 0) & 0xfffffff;
}
static inline seL4_CapData_t __attribute__((__const__))
seL4_CapData_Guard_new(uint32_t GuardBits, uint32_t GuardSize) {
    seL4_CapData_t seL4_CapData;
    seL4_CapData.words[0] = 0;
    (void)0;
    seL4_CapData.words[0] |= (seL4_CapData_Guard & 0x1) << 31;
    (void)0;
    seL4_CapData.words[0] |= (GuardBits & 0x3ffff) << 8;
    (void)0;
    seL4_CapData.words[0] |= (GuardSize & 0x1f) << 3;
    return seL4_CapData;
}
static inline void
seL4_CapData_Guard_ptr_new(seL4_CapData_t *seL4_CapData_ptr, uint32_t GuardBits, uint32_t GuardSize) {
    seL4_CapData_ptr->words[0] = 0;
    (void)0;
    seL4_CapData_ptr->words[0] |= (seL4_CapData_Guard & 0x1) << 31;
    (void)0;
    seL4_CapData_ptr->words[0] |= (GuardBits & 0x3ffff) << 8;
    (void)0;
    seL4_CapData_ptr->words[0] |= (GuardSize & 0x1f) << 3;
}
static inline uint32_t __attribute__((__const__))
seL4_CapData_Guard_get_GuardBits(seL4_CapData_t seL4_CapData) {
    (void)0;
    return (seL4_CapData.words[0] & 0x3ffff00) >> 8;
}
static inline seL4_CapData_t __attribute__((__const__))
seL4_CapData_Guard_set_GuardBits(seL4_CapData_t seL4_CapData, uint32_t v) {
    (void)0;
    (void)0;
    seL4_CapData.words[0] &= ~0x3ffff00;
    seL4_CapData.words[0] |= (v << 8) & 0x3ffff00;
    return seL4_CapData;
}
static inline uint32_t __attribute__((__pure__))
seL4_CapData_Guard_ptr_get_GuardBits(seL4_CapData_t *seL4_CapData_ptr) {
    (void)0;
    return (seL4_CapData_ptr->words[0] & 0x3ffff00) >> 8;
}
static inline void
seL4_CapData_Guard_ptr_set_GuardBits(seL4_CapData_t *seL4_CapData_ptr,
                                      uint32_t v) {
    (void)0;
    (void)0;
    seL4_CapData_ptr->words[0] &= ~0x3ffff00;
    seL4_CapData_ptr->words[0] |= (v << 8) & 0x3ffff00;
}
static inline uint32_t __attribute__((__const__))
seL4_CapData_Guard_get_GuardSize(seL4_CapData_t seL4_CapData) {
    (void)0;
    return (seL4_CapData.words[0] & 0xf8) >> 3;
}
static inline seL4_CapData_t __attribute__((__const__))
seL4_CapData_Guard_set_GuardSize(seL4_CapData_t seL4_CapData, uint32_t v) {
    (void)0;
    (void)0;
    seL4_CapData.words[0] &= ~0xf8;
    seL4_CapData.words[0] |= (v << 3) & 0xf8;
    return seL4_CapData;
}
static inline uint32_t __attribute__((__pure__))
seL4_CapData_Guard_ptr_get_GuardSize(seL4_CapData_t *seL4_CapData_ptr) {
    (void)0;
    return (seL4_CapData_ptr->words[0] & 0xf8) >> 3;
}
static inline void
seL4_CapData_Guard_ptr_set_GuardSize(seL4_CapData_t *seL4_CapData_ptr,
                                      uint32_t v) {
    (void)0;
    (void)0;
    seL4_CapData_ptr->words[0] &= ~0xf8;
    seL4_CapData_ptr->words[0] |= (v << 3) & 0xf8;
}
