/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


int a_global;
int a_mod_global;
int b_mod_global;
int c_mod_global;
int d_mod_global;

int
f (int x) {
    unsigned int tmp1 = 0;
    __asm__ volatile("ubfx" "%0, %1, #11, #8" : "=r"(tmp1) : "r"(x));
    return tmp1;
}

static inline void do_dmb(void)
{
    __asm__ volatile("dmb" "sy" : : : "memory");
}

int
g (void) {
  a_mod_global ++;
  b_mod_global ++;
  c_mod_global ++;
  d_mod_global ++;
}

/** MODIFIES: [*] */
void unspecified_function(unsigned int x);

int
combine (int x) {
  x = f (x);
  b_mod_global ++;
  unspecified_function (x);
  do_dmb ();
  g ();
  x = f (x);
  return x;
}



