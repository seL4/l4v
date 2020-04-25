/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int global;

int g(int n) { global += n; }

int f(void)
{
  (void)0;
  (void)g(6);
  global + 3;
  return 3;
}

/* following would cause an error */
/*
void h (void)
{
  g(4) + f(5);
}
*/
