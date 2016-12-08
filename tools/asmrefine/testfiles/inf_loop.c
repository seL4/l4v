/*
 * Copyright 2016, Data61
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int redundant_global = 3;
int another_redundant_global = 2;

void
redundant_fun (int x) {
  redundant_global = x;
}

void
other_f (void) {
  return;
}

int
main_f (void) {
  while (1) {
    other_f ();
  }
}


