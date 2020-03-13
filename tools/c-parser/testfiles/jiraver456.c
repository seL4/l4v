/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct div_t {
  unsigned q;
};

unsigned f0(unsigned n, unsigned d)
{
  return n/d;
}

struct div_t f1(unsigned n, unsigned d)
{
  struct div_t r = { n / d };
  return r;
}

struct div_t f2(unsigned n, unsigned d)
{
  return (struct div_t){n/d};
}
