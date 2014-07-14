/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/*
The OptionMonad had some incorrect fundef_cong rules, which prevented
a function that called itself twice from being defined in isabelle.

For example, fib.
*/
unsigned fib(unsigned n) {
  if(n == 0) return 0;
  if(n == 1) return 1;
  return fib(n - 1) + fib(n - 2);
}

unsigned rev(unsigned x, unsigned b) {
  if(b < 2) return x;
  b <<= 1;
  unsigned m = (1u << b) - 1u;
  return rev (x >> b & m, b) | rev (x & m, b);
}

int b(int);
int c(int);
int a(int x) {
  return a(x) + b(x) + c(x);
}
int b(int x) {
  return a(x) - b(x) - c(x);
}
int c(int x) {
  return a(x) * b(x) * c(x);
}

/* Minimal testcase */
void ff(void) {
  ff(); ff();
}
