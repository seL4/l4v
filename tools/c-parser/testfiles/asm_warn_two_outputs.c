/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Should warn: outside the supported subset (two outputs). Will fail in SimplExport. */

typedef unsigned long word_t;

word_t two_outputs(void)
{
  word_t lo, hi;
  asm volatile("mrrc p15, 0, %0, %1, c7" : "=r"(lo), "=r"(hi));
  return lo + hi;
}
