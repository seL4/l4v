/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int y;

/** DONT_TRANSLATE */
/** MODIFIES:
    FNSPEC
    f_spec: "\<Gamma> \<turnstile> {s. x_' s < 3} Call f_'proc {s. ret__int_' s < 3}"
*/
int f(int x)
{
  // y++;
  return x;
}

int g(int x)
{
  return x + 1;
}

/** MODIFIES: */
/** DONT_TRANSLATE */
/** FNSPEC clz_spec:
  "\<forall>s. \<Gamma> \<turnstile>
    {\<sigma>. s = \<sigma> \<and> x_' s \<noteq> 0 }
      \<acute>ret__int :== PROC clz(\<acute>x)
    \<lbrace> \<acute>ret__int = of_nat (word_clz (x_' s)) \<rbrace>"
*/
static inline int
clz(unsigned int x)
{
    return __builtin_clz(x);
}


/** MODIFIES:
    FNSPEC
        halt_spec: "\<Gamma> \<turnstile> {} Call halt_'proc {}"
*/
void halt(void);
