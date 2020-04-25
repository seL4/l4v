/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct s {
  int i;
  char c;
  char *ptr;
};

struct s mk_s (int j)
{
  struct s result;
  result.i = j;
  result.c = 0;
  result.ptr = 0;
  return result;
}
