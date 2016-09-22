/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/*
 * AutoCorres does most of its translations using free variables
 * to stand for function arguments and callees.
 * Most of those free variables should be fixed appropriately,
 * (using variant_fixes) to prevent clashes in the following names.
 */

/* Function/arg name conflicts */
int f2(int, int);
int f1(int l2_f1, int l2_f2) {
  return f2(l2_f1, l2_f2);
}
int f2(int l2_f1, int l2_f2) {
  return f1(l2_f1, l2_f2);
}

/* Locale fixed frees */
void locale_fixed(void) {
}
int symbol_table(int symbol_table) {
  return symbol_table;
}

/* Basic function for doing other tests */
void foo(void) {
}
