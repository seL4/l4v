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
 * rename.c: C file for AC_Rename.
 *
 * This code uses some inconvenient names. Its actual behaviour isn't important.
 */

int __real_var__;

int __get_real_var__(void) {
  return __real_var__;
}

void __set_real_var__(int x) {
  __real_var__ = x;
}

#define VAR (__get_real_var__())
