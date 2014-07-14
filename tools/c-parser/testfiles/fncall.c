/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

unsigned global;

int mult(int x, int y)
{
  return x * y;
}

int fact(int n)
{
  int factor, total;
  total = 1;
  factor = 2;
  while (factor <= n)
    /** INV: "\<lbrace> unat \<acute>total = fac (unat \<acute>factor - 1) &
                       \<acute>factor \<le> \<acute>n + 1
              \<rbrace>" */
    {
      total = mult(factor, total);
      factor = factor + 1;
    }
  return total;
}

/** FNSPEC
  g_modifies: "\<forall> \<sigma>. \<Gamma> \<turnstile> {\<sigma>} \<acute>ret__int :== PROC g() {t. t may_not_modify_globals \<sigma>}"
*/
int g(void)
{
  return 257;
}

/** FNSPEC
  f_spec: "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== PROC f(n) \<lbrace> \<acute>ret__int = 1 \<rbrace>"
  f_modifies: "\<forall>\<sigma>. \<Gamma> \<turnstile> {\<sigma>} \<acute>ret__int :== PROC f(\<acute>n)
                       {t. t may_not_modify_globals \<sigma>}"
*/
int f (int n)
{
  char c;
  global++;
  c = g();
  return c;
}


/** FNSPEC
  h_modifies:
    "\<forall> \<sigma>.
       \<Gamma> \<turnstile>
          {\<sigma>}
            \<acute>ret__ptr_to_void :== PROC h()
          {t. t may_not_modify_globals \<sigma>}"
*/
void *h(void)
{
  return 0;
}

/** FNSPEC
  i_modifies: "\<forall> \<sigma>. \<Gamma> \<turnstile> {\<sigma>} \<acute>ret__int :== PROC i() {t. t may_not_modify_globals \<sigma>}"
*/
int i(void)
{
  int *iptr = h();
  return iptr[3];
}

/** FNSPEC
      has_bogus_spec_spec: "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== PROC has_bogus_spec() \<lbrace> \<acute>ret__int = 4 \<rbrace>"
*/
int has_bogus_spec(void)
{
  return 3;
}

int calls_bogus(void)
{
  return has_bogus_spec();
}
