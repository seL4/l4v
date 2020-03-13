/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned len(unsigned *x)
{
  unsigned i;
  for (i = 0; x[i]; i++);
  return i;
}

/* lmin returns the index of the minimum element in the array, stopping when
   the array element is zero (this one doesn't count) */
unsigned lmin(unsigned *x)
{
  unsigned minsofar = x[0], mini = 0, i = 0;
  while (x[i]) {
    if (x[i] < minsofar) { minsofar = x[i]; mini = i; }
    i++;
  }
  return mini;
}

unsigned* ssort(unsigned* x)
{
  unsigned sidx,i,t,lo;
  unsigned ln;
  unsigned mini;
  ln = len(x);
  if (ln < 2) return x;

  for (sidx = 0 ; sidx < ln ; sidx++) {
    mini = lmin(x + sidx);
    lo = sidx + mini;
    t = x[sidx];
    x[sidx] = x[lo];
    x[lo] = t;
  }
  return x;
}
