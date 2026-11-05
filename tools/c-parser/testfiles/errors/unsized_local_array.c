/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Local arrays must have a fixed size */

int f(void)
{
  int a[];
  return 1;
}
