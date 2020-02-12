/*
 *
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */
int foo(int *p, int e) {
    int a = *p;
    if (e == 0) {
      return 0;
    } else {
      return e + a;
    }
}

int bar(int *p, int e) {
    *p += e;
    return *p;
}
