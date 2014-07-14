/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int *pdiff1 (int *ptr, int off)
{
  return ptr - off;
}

int pdiff2 (int *p1, int *p2)
{
  return p1 - p2;
}

struct testing_struct
{
  int val1;
  int val2;
};

int pdiff3 (struct testing_struct *p1)
{
  return ((int)(p1 + 1)) - ((int)(p1));
}
