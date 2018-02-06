/*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

int f (void);


struct two_int {
  int first; int second;
};

void
g (void) {

  int x;
  unsigned int y;
  struct two_int t;
  int z[2];

  x = f ();

  y = f ();

  t.first = f ();

  z[0] = f ();
}
