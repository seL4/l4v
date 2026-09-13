/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Zero-length arrays are not supported. Test that this case fails with an error. */

int arr[0];

int f(void)
{
  return sizeof(arr);
}
