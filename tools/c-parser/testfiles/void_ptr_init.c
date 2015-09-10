/*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/*
 * Initialiser for void*; fixed in git-aa162a0.
 */

struct A {
  void *p;
};

void f(void) {
  struct A a = { 0 };
}
