/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
