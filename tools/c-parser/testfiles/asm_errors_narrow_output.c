/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Error: "=r" output operand narrower than the machine word */
unsigned short f(void)
{
  unsigned short v;
  asm volatile("mrs %0, tpidr_el1" : "=r"(v));
  return v;
}
