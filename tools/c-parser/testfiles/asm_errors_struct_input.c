/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Error: "r" input operand of struct type */
struct s { unsigned long a; unsigned long b; };

void f(struct s x)
{
  asm volatile("msr tpidr_el1, %0" : : "r"(x));
}
