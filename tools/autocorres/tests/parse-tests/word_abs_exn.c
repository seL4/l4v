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
 * Regression test: word_abstract on L2_catch/L2_call.
 */

int bad(int i) {
  return i == 0;
}

int bads(unsigned n) {
  unsigned i;
  for (i = 0; i < n; i++) {
    if (bad(i)) {
      return 1;
    }
  }
  return 0;
}
