/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
