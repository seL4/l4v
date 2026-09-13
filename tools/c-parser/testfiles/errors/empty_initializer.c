/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Zero-length arrays are not supported, which means empty initialiser lists
   are also not supported. Test that this case fails with an error. */

int arr[] = {};

int f(void)
{
  return sizeof(arr);
}
