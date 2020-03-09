/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef unsigned long word_t;

/** FNSPEC reverse_spec:
  "\<Gamma> \<turnstile>
    \<lbrace> list (lift_t_c \<zeta>) zs \<acute>i \<rbrace>
      \<acute>ret__unsigned_long :== PROC reverse(\<acute>i)
    \<lbrace> list (lift_t_c \<zeta>) (rev zs) (Ptr \<acute>ret__unsigned_long) \<rbrace>"

*/

word_t reverse(word_t *i)
{
  word_t j = 0;

  while (i)
    /** INV:
        "\<lbrace> \<exists>xs ys. list (lift_t_c \<zeta>) xs \<acute>i \<and>
                  list (lift_t_c \<zeta>) ys (Ptr \<acute>j) \<and>
                  rev zs = rev xs @ ys \<and>
                  distinct (rev zs) \<rbrace>" */
  {
    word_t *k = (word_t*)*i;

    *i = j;
    j = (word_t)i;
    i = k;
  }

  return j;
}
