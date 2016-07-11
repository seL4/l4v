/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
