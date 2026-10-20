/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Error: "=r" output operand of pointer type */
unsigned long *f(void)
{
  unsigned long *p;
  asm volatile("mrs %0, tpidr_el1" : "=r"(p));
  return p;
}
