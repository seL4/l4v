/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int f(char c)
{
  switch (c) {
  case 0: return 3;
  case 1: return 2;
  default: return 0;
  }
}
