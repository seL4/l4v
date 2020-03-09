/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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


