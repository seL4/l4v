(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Sgn_Abs
  imports Most_significant_bit
begin

section \<open>@{const sgn} and @{const abs} for @{typ "'a word"}\<close>

subsection \<open>Instances\<close>

text \<open>@{const sgn} on words returns -1, 0, or 1.\<close>
instantiation word :: (len) sgn
begin

definition sgn_word :: \<open>'a word \<Rightarrow> 'a word\<close> where
  \<open>sgn w = (if w = 0 then 0 else if 0 <s w then 1 else -1)\<close>

instance ..

end


(* Simplification setup for sgn on numerals *)

lemma word_sgn_0[simp]:
  "sgn 0 = (0::'a::len word)"
  by (simp add: sgn_word_def)

lemma word_sgn_1[simp]:
  "sgn 1 = (1::'a::len word)"
  by (simp add: sgn_word_def)

lemma word_sgn_max_word[simp]:
  "sgn (- 1) = (-1::'a::len word)"
  by (clarsimp simp: sgn_word_def word_sless_alt)

lemmas word_sgn_numeral[simp] = sgn_word_def[where w="numeral w" for w]


text \<open>@{const abs} on words is the usual definition.\<close>
instantiation word :: (len) abs
begin

definition abs_word :: \<open>'a word \<Rightarrow> 'a word\<close> where
  \<open>abs w = (if w \<le>s 0 then -w else w)\<close>

instance ..

end


(* Simplification setup for abs on numerals *)

lemma word_abs_0[simp]:
  "\<bar>0\<bar> = (0::'a::len word)"
  by (simp add: abs_word_def)

lemma word_abs_1[simp]:
  "\<bar>1\<bar> = (1::'a::len word)"
  by (simp add: abs_word_def)

lemma word_abs_max_word[simp]:
  "\<bar>- 1\<bar> = (1::'a::len word)"
  by (clarsimp simp: abs_word_def word_sle_eq)

lemma word_abs_msb:
  "\<bar>w\<bar> = (if msb w then -w else w)" for w::"'a::len word"
  by (simp add: abs_word_def msb_word_iff_sless_0 word_sless_eq)

lemmas word_abs_numeral[simp] = word_abs_msb[where w="numeral w" for w]


subsection \<open>Properties\<close>

(* Many of these are from linordered_idom, but need <s instead of < and occasionally
   an additional assumption on minimum word length, because in "1 word" we have -1 = 1. *)

lemma word_sgn_0_0:
  "sgn a = 0 \<longleftrightarrow> a = 0" for a::"'a::len word"
  by (simp add: sgn_word_def)

lemma word_sgn_1_pos:
  "1 < LENGTH('a) \<Longrightarrow> sgn a = 1 \<longleftrightarrow> 0 <s a" for a::"'a::len word"
  unfolding sgn_word_def by simp

lemma word_sgn_1_neg:
  "sgn a = - 1 \<longleftrightarrow> a <s 0"
  unfolding sgn_word_def
  using sint_1_cases by force

lemma word_sgn_pos[simp]:
  "0 <s a \<Longrightarrow> sgn a = 1"
  by (simp add: sgn_word_def)

lemma word_sgn_neg[simp]:
  "a <s 0 \<Longrightarrow> sgn a = - 1"
  by (simp only: word_sgn_1_neg)

lemma word_abs_sgn:
  "\<bar>k\<bar> = k * sgn k" for k :: "'a::len word"
  unfolding sgn_word_def abs_word_def
  by auto

lemma word_sgn_greater[simp]:
  "0 <s sgn a \<longleftrightarrow> 0 <s a" for a::"'a::len word"
  by (smt (verit) signed_eq_0_iff sint_1_cases sint_n1 word_sgn_0_0 word_sgn_neg word_sgn_pos
                  word_sless_alt)

lemma word_sgn_less[simp]:
  "sgn a <s 0 \<longleftrightarrow> a <s 0" for a::"'a::len word"
  unfolding sgn_word_def
  using degenerate_word signed.antisym_conv3 word_sless_alt by force

lemma word_abs_sgn_eq_1[simp]:
  "a \<noteq> 0 \<Longrightarrow> \<bar>sgn a\<bar> = 1" for a::"'a::len word"
  unfolding abs_word_def sgn_word_def
  by (clarsimp simp: word_sle_eq)

lemma word_abs_sgn_eq:
  "\<bar>sgn a\<bar> = (if a = 0 then 0 else 1)" for a::"'a::len word"
  by clarsimp

lemma word_sgn_mult_self_eq[simp]:
  "sgn a * sgn a = of_bool (a \<noteq> 0)" for a::"'a::len word"
  by (cases "0 <s a"; simp)

end