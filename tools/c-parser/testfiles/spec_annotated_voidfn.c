/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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

