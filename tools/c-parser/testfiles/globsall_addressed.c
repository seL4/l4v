/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int glob1;
const int wannabe_constant = 3;
int really_addressed;

int deref(int *p)
{
  return *p;
}


int f(void)
{
  int y = deref(&really_addressed);
  glob1++;
  y += glob1;
  return y + wannabe_constant;
}


