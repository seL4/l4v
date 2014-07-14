/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

typedef unsigned int uint32_t;
typedef unsigned char uint8_t;

typedef uint32_t paddr_t;
typedef uint32_t word_t;
typedef uint8_t hw_asid_t;

word_t x;

/* Address space control */
/** MODIFIES: x */
void setCurrentPD(paddr_t addr);
/** MODIFIES: [*] */
void setHardwareASID(hw_asid_t hw_asid);

/* TLB control */
/** MODIFIES: [*] */
void invalidateTLB(void);
/** MODIFIES: [*] */
void invalidateHWASID(hw_asid_t hw_asid);
/** MODIFIES: [*] */
void invalidateMVA(word_t mva_plus_asid);
/** MODIFIES: [*] */
void lockTLBEntry(word_t vaddr);

void test() {
  setCurrentPD(0);
  }


