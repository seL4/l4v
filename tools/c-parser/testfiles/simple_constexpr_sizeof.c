/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct s {
  char c;
  int x;
};

char f(struct s *sptr, int byteno)
{
  char array[sizeof(struct s)];
  for (int i = 0; i < sizeof *sptr; i++)
    array[i] = *(((char *)sptr) + i);
  return array[byteno];
}
