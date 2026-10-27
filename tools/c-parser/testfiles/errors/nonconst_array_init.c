/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Array size must be static and must be a constant expression */

struct s {
  int arr[3];
};

struct s g(void);

int f(void)
{
  int a[] = g().arr;
  return a[0];
}
