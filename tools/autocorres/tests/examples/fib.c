/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

unsigned fib(unsigned n) {
  if(n == 0) return 0;
  if(n == 1) return 1;
  return fib(n-1) + fib(n-2);
}

unsigned fib_linear(unsigned n) {
  unsigned a = 0, b = 1;
  while(n) {
    unsigned t = b;
    b += a;
    a = t;
    n -= 1;
  }
  return a;
}

void call_fib(void) {
  fib(42);
}
