/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned main(unsigned int j, int d)
{
  int *c = (int *)j;
  return (unsigned) (c + d);
}

void set_intptr(void *ptr, int val)
{
  *(int *)ptr = val;
}
