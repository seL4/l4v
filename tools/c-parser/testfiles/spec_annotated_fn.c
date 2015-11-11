/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/** FNSPEC
      Square_spec:
         "\<forall> n. \<Gamma> |-
              \<lbrace>\<acute>n = n\<rbrace>
              \<acute>ret__unsigned :== PROC Square(\<acute>n)
              \<lbrace>\<acute>ret__unsigned = n * n\<rbrace>"
*/
unsigned Square(unsigned n) { return n * n; }

/** DONT_TRANSLATE */
/**
    MODIFIES:
    FNSPEC
       f_spec: "\<forall> n. \<Gamma> |- \<lbrace>\<acute>n= n \<rbrace>
                           \<acute>ret__unsigned :== PROC f(\<acute>n)
                            \<lbrace>\<acute>ret__unsigned = n * n\<rbrace>"
*/
unsigned f(unsigned n) { return n * n; }
