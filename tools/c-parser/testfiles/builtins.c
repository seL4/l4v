/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
