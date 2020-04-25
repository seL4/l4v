/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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


