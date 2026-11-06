/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Array size must be static and constant */

int h(int n)
{
  int a[n];
  return a[0];
}
