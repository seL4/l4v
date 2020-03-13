/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int x;

/* this spec is bogus, but at least it parses */

/** FNSPEC
     f_spec: "\<forall> \<sigma> n.
               \<Gamma> \<turnstile> {\<sigma>} CALL f(n)
                  \<lbrace> x_' (globals \<sigma>) + scast n = \<acute>x\<rbrace>"
*/
void f(char n)
{
  x = x + n;
}

