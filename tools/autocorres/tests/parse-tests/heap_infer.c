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
Regression test: HeapLiftBase didn't look at recursive function definitions properly,
                 so it failed to infer that we needed a word32 heap here.
*/

unsigned foo(void) {
  return *(unsigned*)foo();
}
