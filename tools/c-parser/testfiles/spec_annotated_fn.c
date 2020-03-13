/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
