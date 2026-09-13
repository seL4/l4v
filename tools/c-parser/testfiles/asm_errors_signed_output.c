/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Error: "=r" output operand with a signed type */
int f(void)
{
  int v;
  asm volatile("mrs %0, tpidr_el1" : "=r"(v));
  return v;
}
