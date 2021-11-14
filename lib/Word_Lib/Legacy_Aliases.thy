(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Legacy aliases\<close>

theory Legacy_Aliases
  imports "HOL-Library.Word"
begin

context abstract_boolean_algebra
begin

lemma conj_assoc: "(x \<^bold>\<sqinter> y) \<^bold>\<sqinter> z = x \<^bold>\<sqinter> (y \<^bold>\<sqinter> z)"
  by (fact conj.assoc)

lemma conj_commute: "x \<^bold>\<sqinter> y = y \<^bold>\<sqinter> x"
  by (fact conj.commute)

lemmas conj_left_commute = conj.left_commute
lemmas conj_ac = conj.assoc conj.commute conj.left_commute

lemma conj_one_left: "\<^bold>1 \<^bold>\<sqinter> x = x"
  by (fact conj.left_neutral)

lemma conj_left_absorb: "x \<^bold>\<sqinter> (x \<^bold>\<sqinter> y) = x \<^bold>\<sqinter> y"
  by (fact conj.left_idem)

lemma conj_absorb: "x \<^bold>\<sqinter> x = x"
  by (fact conj.idem)

lemma disj_assoc: "(x \<^bold>\<squnion> y) \<^bold>\<squnion> z = x \<^bold>\<squnion> (y \<^bold>\<squnion> z)"
  by (fact disj.assoc)

lemma disj_commute: "x \<^bold>\<squnion> y = y \<^bold>\<squnion> x"
  by (fact disj.commute)

lemmas disj_left_commute = disj.left_commute

lemmas disj_ac = disj.assoc disj.commute disj.left_commute

lemma disj_zero_left: "\<^bold>0 \<^bold>\<squnion> x = x"
  by (fact disj.left_neutral)

lemma disj_left_absorb: "x \<^bold>\<squnion> (x \<^bold>\<squnion> y) = x \<^bold>\<squnion> y"
  by (fact disj.left_idem)

lemma disj_absorb: "x \<^bold>\<squnion> x = x"
  by (fact disj.idem)

end

context abstract_boolean_algebra_sym_diff
begin

lemmas xor_assoc = xor.assoc
lemmas xor_commute = xor.commute
lemmas xor_left_commute = xor.left_commute

lemmas xor_ac = xor.assoc xor.commute xor.left_commute

lemma xor_zero_right: "x \<^bold>\<ominus> \<^bold>0 = x"
  by (fact xor.comm_neutral)

lemma xor_zero_left: "\<^bold>0 \<^bold>\<ominus> x = x"
  by (fact xor.left_neutral)

end

abbreviation (input) test_bit :: \<open>'a::semiring_bits \<Rightarrow> nat \<Rightarrow> bool\<close>
  where \<open>test_bit \<equiv> bit\<close>

abbreviation (input) bin_nth :: \<open>int \<Rightarrow> nat \<Rightarrow> bool\<close>
  where \<open>bin_nth \<equiv> bit\<close>

abbreviation (input) bin_last :: \<open>int \<Rightarrow> bool\<close>
  where \<open>bin_last \<equiv> odd\<close>

abbreviation (input) bin_rest :: \<open>int \<Rightarrow> int\<close>
  where \<open>bin_rest w \<equiv> w div 2\<close>

abbreviation (input) bintrunc :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>bintrunc \<equiv> take_bit\<close>

abbreviation (input) sbintrunc :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>sbintrunc \<equiv> signed_take_bit\<close>

abbreviation (input) bin_cat :: \<open>int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>bin_cat k n l \<equiv> concat_bit n l k\<close>

abbreviation (input) norm_sint :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>norm_sint n \<equiv> signed_take_bit (n - 1)\<close>

abbreviation (input) max_word :: \<open>'a::len word\<close>
  where \<open>max_word \<equiv> - 1\<close>

abbreviation (input) complement :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  where \<open>complement \<equiv> not\<close>

lemma complement_mask:
  "complement (2 ^ n - 1) = not (mask n)"
  unfolding mask_eq_decr_exp by simp

context
  includes bit_operations_syntax
begin

abbreviation (input) bshiftr1 :: \<open>bool \<Rightarrow> 'a::len word \<Rightarrow> 'a word\<close>
  where \<open>bshiftr1 b w \<equiv> w div 2 OR push_bit (LENGTH('a) - Suc 0) (of_bool b) \<close>

end

lemma bit_bshiftr1_iff:
  \<open>bit (bshiftr1 b w) n \<longleftrightarrow> b \<and> n = LENGTH('a) - 1 \<or> bit w (Suc n)\<close>
    for w :: \<open>'a::len word\<close>
  by (auto simp add: bit_simps simp flip: bit_Suc)

abbreviation (input) setBit :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> 'a word\<close>
  where \<open>setBit w n \<equiv> set_bit n w\<close>

abbreviation (input) clearBit :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> 'a word\<close>
  where \<open>clearBit w n \<equiv> unset_bit n w\<close>

lemma bit_setBit_iff:
  \<open>bit (setBit w m) n \<longleftrightarrow> (m = n \<and> n < LENGTH('a) \<or> bit w n)\<close>
  for w :: \<open>'a::len word\<close>
  by (auto simp add: bit_simps)

lemma bit_clearBit_iff:
  \<open>bit (clearBit w m) n \<longleftrightarrow> m \<noteq> n \<and> bit w n\<close>
  for w :: \<open>'a::len word\<close>
  by (auto simp add: bit_simps)

lemmas less_def = less_eq [symmetric]
lemmas le_def = not_less [symmetric, where ?'a = nat]

end
