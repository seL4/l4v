/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int g(int);
int f(int i)
{
  if (__builtin_expect(i < 0, 0)) return g(-i);
  else return i + 3;
}

int g(int i)
{
  int acc = i < 0 ? i : 0;
  while (acc < i) /** INV: "\<lbrace> \<acute>acc <=s \<acute>i \<rbrace>" */ {
    acc++;
  }
  return acc;
}
