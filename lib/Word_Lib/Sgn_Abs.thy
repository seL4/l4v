(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Sgn_Abs
  imports Most_significant_bit
begin

lemma not_0_sless_minus_1 [simp]:
  \<open>\<not> 0 <s - 1\<close>
  by transfer simp

lemma not_0_sless_eq_minus_1 [simp]:
  \<open>\<not> 0 \<le>s - 1\<close>
  by transfer simp

section \<open>@{const sgn} and @{const abs} for @{typ "'a word"}\<close>

subsection \<open>Instances\<close>

text \<open>@{const sgn} on words returns -1, 0, or 1.\<close>

instantiation word :: (len) sgn
begin

lift_definition sgn_word :: \<open>'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k. sgn (signed_take_bit (LENGTH('a) - Suc 0) k)\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

instance ..

end

lemma sgn_word_if:
  \<open>sgn w = (if w = 0 then 0 else if 0 <s w then 1 else - 1)\<close>
  by transfer (simp only: flip: signed_take_bit_decr_length_iff, auto simp add: sgn_if)

text \<open>Simplificattion setup for sgn on numerals\<close>

lemma word_sgn_0[simp]:
  "sgn 0 = (0::'a::len word)"
  by transfer simp

lemma word_sgn_1[simp]:
  "sgn 1 = (1::'a::len word)"
  by (transfer; cases \<open>LENGTH('a) - Suc 0\<close>) simp_all

lemma word_sgn_max_word[simp]:
  "sgn (- 1) = (-1::'a::len word)"
  by transfer simp

lemma word_sgn_numeral [simp]:
  \<open>sgn (numeral n) = (if numeral n = (0 :: 'a::len word) then 0
    else if (0 :: 'a::len word) <s numeral n then 1 else (- 1 :: 'a::len word))\<close>
  by (fact sgn_word_if)

text \<open>@{const abs} on words is the usual definition.\<close>

instantiation word :: (len) abs
begin

lift_definition abs_word :: \<open>'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k. \<bar>signed_take_bit (LENGTH('a) - Suc 0) k\<bar>\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

instance ..

end

lemma abs_word_if:
  \<open>abs w = (if w \<le>s 0 then - w else w)\<close>
  by transfer (simp only: flip: signed_take_bit_decr_length_iff,
    auto simp add: abs_of_pos signed_take_bit_minus)


text \<open>Simplification setup for abs on numerals\<close>

lemma word_abs_0[simp]:
  "\<bar>0\<bar> = (0::'a::len word)"
  by transfer simp

lemma word_abs_1[simp]:
  "\<bar>1\<bar> = (1::'a::len word)"
  by (transfer; cases \<open>LENGTH('a) - Suc 0\<close>) simp_all

lemma word_abs_max_word[simp]:
  "\<bar>- 1\<bar> = (1::'a::len word)"
  by transfer simp

lemma word_abs_msb:
  "\<bar>w\<bar> = (if msb w then - w else w)" for w :: "'a::len word"
  by transfer
    (simp add: abs_of_neg msb_int_def signed_take_bit_eq_take_bit_minus take_bit_minus flip: take_bit_diff [of _ \<open>2 ^ LENGTH('a)\<close>])

lemmas word_abs_numeral[simp] = word_abs_msb[where w="numeral w" for w]


subsection \<open>Properties\<close>

(* Many of these are from linordered_idom, but need <s instead of < and occasionally
   an additional assumption on minimum word length, because in "1 word" we have -1 = 1. *)

lemma word_sgn_0_0:
  "sgn a = 0 \<longleftrightarrow> a = 0" for a::"'a::len word"
  by (simp add: sgn_word_if)

lemma word_sgn_1_pos:
  "1 < LENGTH('a) \<Longrightarrow> sgn a = 1 \<longleftrightarrow> 0 <s a" for a::"'a::len word"
  by (simp add: sgn_word_if)

lemma word_sgn_1_neg:
  "sgn a = - 1 \<longleftrightarrow> a <s 0"
  by (cases a rule: word_length_one) (auto simp add: sgn_word_if)

lemma word_sgn_pos[simp]:
  "0 <s a \<Longrightarrow> sgn a = 1"
  by transfer simp

lemma word_sgn_neg[simp]:
  "a <s 0 \<Longrightarrow> sgn a = - 1"
  by (simp only: word_sgn_1_neg)

lemma word_abs_sgn:
  "\<bar>k\<bar> = k * sgn k" for k :: "'a::len word"
  by (auto simp add: sgn_word_if abs_word_if)

lemma word_sgn_greater[simp]:
  "0 <s sgn a \<longleftrightarrow> 0 <s a" for a::"'a::len word"
  by (cases a rule: word_length_one) (simp_all add: sgn_word_if)

lemma word_sgn_less[simp]:
  "sgn a <s 0 \<longleftrightarrow> a <s 0" for a::"'a::len word"
  by (cases a rule: word_length_one) (auto simp add: sgn_word_if)

lemma word_abs_sgn_eq_1[simp]:
  "a \<noteq> 0 \<Longrightarrow> \<bar>sgn a\<bar> = 1" for a::"'a::len word"
  by (simp add: sgn_word_if)

lemma word_abs_sgn_eq:
  "\<bar>sgn a\<bar> = (if a = 0 then 0 else 1)" for a::"'a::len word"
  by simp

lemma word_sgn_mult_self_eq[simp]:
  "sgn a * sgn a = of_bool (a \<noteq> 0)" for a::"'a::len word"
  by (cases "0 <s a") simp_all

end
