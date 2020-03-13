/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* this file is no longer valid syntax; the pre-post should be
   replaced by an appropriate FNCALL specification, before the
   function */

int fact(int n)
     /** PRE: n > 0
         POST: fact_ret = FACT n */
{
  int c, result;
  c = n;
  result = 1;
  while (c > 1) {
    result = result * c;
    c = c - 1;
  }
  return result;
}
