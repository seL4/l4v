/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef struct s {
  int x,y;
  char c;
} s;

int f(void)
{
  unsigned char array[sizeof(s)];
  struct s var1;
  for (int i = 0; i < sizeof(s); i++) array[i] = 1;
  return sizeof (s);
}
