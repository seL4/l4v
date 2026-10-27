/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Error: "r" input operand wider than the machine word */
void f(unsigned long long x)
{
  asm volatile("msr tpidr_el1, %0" : : "r"(x));
}
