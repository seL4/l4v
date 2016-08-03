/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
