/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int f(int i)
{
  if (i < 10)
    asm("mcr p15, 0, %0, c2, c0, 0" : : "r"(pd_addr));
  asm("stmdb %0, {r8-r12}^" : : "r"(&dest->tcbContext.registers[R12] + 1));
  return 0;
}
