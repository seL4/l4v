/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* C-parser does not technically allow the use of built-in functions
 * (__builtin_*) because:
 *
 * 1) it requires `allow_underscore_idents = true` to support __*
 *    identifiers.
 *
 * 2) built-ins are not defined or declared anywhere!
 *
 * A workaround is to re-declare the built-in so that the c-parser
 * "knows" what __builtin_* is even though is not defined anywhere,
 * interestingly GCC does not complain about this.
 *
 */


/* Interesting fact: the use of `extern` is optional */
extern void __builtin_unreachable(void);

void foo(void){
   __builtin_unreachable();
}
