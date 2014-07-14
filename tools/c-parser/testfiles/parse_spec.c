/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int f(int m, int n)
{
  int i;
  i = m;
  /** SPEC: "\<tau> . \<lbrace> \<tau>. \<acute>i = \<^bsup>\<sigma> \<^esup>m \<rbrace>" */
  m = n;
  n = i;
  /** END-SPEC: "\<lbrace> \<acute>m = \<^bsup>\<tau>\<^esup>n \<and> \<acute>n = \<^bsup>\<tau>\<^esup>i \<rbrace>" */
  return m + n;
}


