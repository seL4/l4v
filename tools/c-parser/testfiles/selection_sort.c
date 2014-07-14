/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
