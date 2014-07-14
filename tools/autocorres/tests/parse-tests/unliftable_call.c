/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/* Heap-unliftable functions calling liftable ones and vice versa. */

int f(int x) {
  return x + 1;
}
int g(int x) {
  return g(x + 1);
}

int *call_f(void *mem) {
  /** AUXUPD: "(True, ptr_retyp (ptr_coerce \<acute>mem :: word32 ptr))" */
  *(int*)mem = f(g(*(int*)mem));
}

void rec_untyp(int*);
void rec_typ(void *mem) {
  /** AUXUPD: "(True, ptr_retyp (ptr_coerce \<acute>mem :: word32 ptr))" */
  rec_untyp(mem);
}
void rec_untyp(int *ptr) {
  *ptr = f(g(*ptr));
  /** AUXUPD: "(True, ptr_retyp (ptr_coerce \<acute>ptr :: unit ptr))" */
  rec_typ(ptr);
}

void call_all(void) {
  rec_untyp(call_f(0));
}
