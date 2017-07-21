/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/** FNSPEC swap_spec:
  "\<forall>x y. \<Gamma> \<turnstile>
    \<lbrace>\<sigma>. (\<acute>p \<mapsto> x \<and>\<^sup>* \<acute>q \<mapsto> y)\<^bsup>sep\<^esup> \<rbrace>
      PROC swap(\<acute>p,\<acute>q)
    \<lbrace> (\<^bsup>\<sigma>\<^esup>p \<mapsto> y \<and>\<^sup>* \<^bsup>\<sigma>\<^esup>q \<mapsto> x)\<^bsup>sep\<^esup> \<rbrace>"
*/

void swap(unsigned int *p, unsigned int *q)
{
  unsigned int x;

  x = *p;
  *p = *q;
  *q = x;
}

/** FNSPEC test_spec:
  "\<forall>x y. \<Gamma> \<turnstile>
    \<lbrace>\<sigma>. (\<acute>a \<mapsto> x \<and>\<^sup>* \<acute>b \<mapsto> y \<and>\<^sup>* \<acute>c \<mapsto> -)\<^bsup>sep\<^esup> \<rbrace>
      PROC test(\<acute>a,\<acute>b,\<acute>c)
    \<lbrace> (\<^bsup>\<sigma>\<^esup>a \<mapsto> (x + y) \<and>\<^sup>* \<^bsup>\<sigma>\<^esup>b \<mapsto> x \<and>\<^sup>* \<^bsup>\<sigma>\<^esup>c \<mapsto> y)\<^bsup>sep\<^esup> \<rbrace>"
*/

void test(unsigned int *a, unsigned int *b, unsigned int *c)
{
  *c = *a + *b;
  swap(a,b);
  swap(c,a);
}
