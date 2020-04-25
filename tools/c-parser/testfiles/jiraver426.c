/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

_Noreturn void exit(int i);

unsigned f(unsigned i)
{
  if (i < 0) exit(-1);
  return i * i;
}

_Noreturn void myexit(int i)
{
  exit(i + 1);
}
