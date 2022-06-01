(*
 * Copyright Julius Michaelis, Cornelius Diekmann
 * SPDX-License-Identifier: BSD-3-Clause
 *)

section\<open>Increment and Decrement Machine Words Without Wrap-Around\<close>

theory Next_and_Prev
imports
  Aligned
begin

text \<open>Previous and next words addresses, without wrap around.\<close>

lift_definition word_next :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k. if 2 ^ LENGTH('a) dvd k + 1 then - 1 else k + 1\<close>
  by (simp flip: take_bit_eq_0_iff) (metis take_bit_add)

lift_definition word_prev :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k. if 2 ^ LENGTH('a) dvd k then 0 else k - 1\<close>
  by (simp flip: take_bit_eq_0_iff) (metis take_bit_diff)

lemma word_next_unfold:
  \<open>word_next w = (if w = - 1 then - 1 else w + 1)\<close>
  by transfer (simp flip: take_bit_eq_mask_iff_exp_dvd)

lemma word_prev_unfold:
  \<open>word_prev w = (if w = 0 then 0 else w - 1)\<close>
  by transfer (simp flip: take_bit_eq_0_iff)

lemma [code]:
  \<open>Word.the_int (word_next w :: 'a::len word) =
    (if w = - 1 then Word.the_int w else Word.the_int w + 1)\<close>
  by transfer
    (simp add: mask_eq_exp_minus_1 take_bit_incr_eq flip: take_bit_eq_mask_iff_exp_dvd)

lemma [code]:
  \<open>Word.the_int (word_prev w :: 'a::len word) =
    (if w = 0 then Word.the_int w else Word.the_int w - 1)\<close>
  by transfer (simp add: take_bit_eq_0_iff take_bit_decr_eq)

lemma word_adjacent_union:
  "word_next e = s' \<Longrightarrow> s \<le> e \<Longrightarrow> s' \<le> e' \<Longrightarrow> {s..e} \<union> {s'..e'} = {s .. e'}"
  apply (simp add: word_next_unfold ivl_disj_un_two_touch split: if_splits)
  apply (drule sym)
  apply simp
  apply (subst word_atLeastLessThan_Suc_atLeastAtMost_union)
     apply (simp_all add: word_Suc_le)
  done

end
