/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct {
  int fld1;
  char fld2;
  _Bool fld3;
} global1;

struct {
  int fld;
} global2;

char f(void)
{
  global1.fld1++;
  return global1.fld2;
}
