/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* An array without size can only be initialized with an explicit initializer list */

struct s {
  int arr[3];
};

struct s g(void);

int f(void)
{
  int a[] = g().arr;
  return a[0];
}
