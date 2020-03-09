/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int f(int i)
{
  if (i < 10)
    asm("mcr p15, 0, %0, c2, c0, 0" : : "r"(pd_addr));
  asm("stmdb %0, {r8-r12}^" : : "r"(&dest->tcbContext.registers[R12] + 1));
  return 0;
}
