/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Error: "=r" output operand that is not an lvalue */
unsigned long f(unsigned long x)
{
  asm volatile("mrs %0, tpidr_el1" : "=r"(x + 1));
  return x;
}
