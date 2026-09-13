/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Array size must be static and must be a constant expression */

int g(void);

int f(void)
{
  int a[] = g();
  return a[0];
}
