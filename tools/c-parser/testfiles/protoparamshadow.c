/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int var;

int proto(int var);

int realone(int var)
{
  return var + 1;
}

int f(void)
{
  var = var + 1;
  return var;
}

int var = 4;

