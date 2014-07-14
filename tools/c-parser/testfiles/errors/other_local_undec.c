/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/* demonstrates that local variables in one function aren't available to other
   functions */

int f (int n) { return n + 1; }

int g (int m) { return n + m; }

