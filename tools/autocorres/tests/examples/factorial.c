/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

unsigned factorial(unsigned n) {
  if(n == 0) return 1;
  return n * factorial(n-1);
}

unsigned call_factorial(void) {
  return factorial(42);
}
