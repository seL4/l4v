int y;

/** DONT_TRANSLATE */
/** MODIFIES: y
    FNSPEC
    f_spec: "\<Gamma> \<turnstile> {s. x_' s < 3} Call f_'proc {s. ret__int_' s < 3}"
*/
int f(int x)
{
  y++;
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
