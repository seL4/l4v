/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef unsigned int int32_t;

#define BIT(n) (1 << (n))
#define PAGE_BITS 12
#define PPTR_KDEV 0xffff0000
#define PPTR_APIC PPTR_KDEV
#define PPTR_DRHU_START (PPTR_APIC + BIT(PAGE_BITS))
#define MAX_NUM_DRHU ((-PPTR_DRHU_START) >> PAGE_BITS)
#define MAX_NUM_DRHU_VARIANT ((-(int32_t)PPTR_DRHU_START) >> PAGE_BITS)



char array[MAX_NUM_DRHU];  // array of 15 chars
char array2[MAX_NUM_DRHU_VARIANT]; // ditto

char f(unsigned i) { return i < 15 ? array[i] : 0; }

int g(void) { return sizeof(array); }

int h(void) { return sizeof(array2); }
