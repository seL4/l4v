/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int foo(int v)
{
  return v + 1;
}

void bar(void)
{
    unsigned long v;
    __asm__ volatile("mrc  " " p15, 0,  %0, c14,  c1, 0" /* 32-bit RW Timer PL1 Control register */ : "=r"(v));
}
