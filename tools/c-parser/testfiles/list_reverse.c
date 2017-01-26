/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

typedef unsigned long word_t;

/** FNSPEC reverse_spec:
  "\<Gamma> \<turnstile>
    \<lbrace> (list zs \<acute>i)\<^bsup>sep\<^esup> \<rbrace>
      \<acute>ret__long :== PROC reverse(\<acute>i)
    \<lbrace> (list (rev zs) (Ptr (scast \<acute>ret__long)))\<^bsup>sep\<^esup> \<rbrace>"
*/

long reverse(word_t *i)
{
  word_t j = 0;

  while (i)
    /** INV: "\<lbrace> \<exists>xs ys. (list xs \<acute>i \<and>\<^sup>* list ys (Ptr \<acute>j))\<^bsup>sep\<^esup> \<and> rev zs = (rev xs)@ys \<rbrace>" */
  {
    word_t *k = (word_t*)*i;

    *i = j;
    j = (word_t)i;
    i = k;
  }

  return j;
}
