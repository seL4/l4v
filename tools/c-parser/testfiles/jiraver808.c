/*
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
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
