(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Signed Words"

theory Signed_Words
  imports "HOL-Library.Word"
begin

text \<open>Signed words as separate (isomorphic) word length class. Useful for tagging words in C.\<close>

typedef ('a::len0) signed = "UNIV :: 'a set" ..

lemma card_signed [simp]: "CARD (('a::len0) signed) = CARD('a)"
  unfolding type_definition.card [OF type_definition_signed]
  by simp

instantiation signed :: (len0) len0
begin

definition
  len_signed [simp]: "len_of (x::'a::len0 signed itself) = LENGTH('a)"

instance ..

end

instance signed :: (len) len
  by (intro_classes, simp)

lemma scast_scast_id [simp]:
  "scast (scast x :: ('a::len) signed word) = (x :: 'a word)"
  "scast (scast y :: ('a::len) word) = (y :: 'a signed word)"
  by (auto simp: is_up scast_up_scast_id)

lemma ucast_scast_id [simp]:
  "ucast (scast (x :: 'a::len signed word) :: 'a word) = x"
  by transfer (simp add: take_bit_signed_take_bit)

lemma scast_of_nat [simp]:
  "scast (of_nat x :: 'a::len signed word) = (of_nat x :: 'a word)"
  by transfer (simp add: take_bit_signed_take_bit)

lemma scast_ucast_id [simp]:
  "scast (ucast (x :: 'a::len word) :: 'a signed word) = x"
  by transfer (simp add: take_bit_signed_take_bit)

lemma scast_eq_scast_id [simp]:
  "((scast (a :: 'a::len signed word) :: 'a word) = scast b) = (a = b)"
  by (metis ucast_scast_id)

lemma ucast_eq_ucast_id [simp]:
  "((ucast (a :: 'a::len word) :: 'a signed word) = ucast b) = (a = b)"
  by (metis scast_ucast_id)

lemma scast_ucast_norm [simp]:
  "(ucast (a :: 'a::len word) = (b :: 'a signed word)) = (a = scast b)"
  "((b :: 'a signed word) = ucast (a :: 'a::len word)) = (a = scast b)"
  by (metis scast_ucast_id ucast_scast_id)+

lemma scast_2_power [simp]: "scast ((2 :: 'a::len signed word) ^ x) = ((2 :: 'a word) ^ x)"
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma ucast_nat_def':
  "of_nat (unat x) = (ucast :: 'a :: len word \<Rightarrow> ('b :: len) signed word) x"
  by (fact of_nat_unat)

lemma zero_sle_ucast_up:
  "\<not> is_down (ucast :: 'a word \<Rightarrow> 'b signed word) \<Longrightarrow>
          (0 <=s ((ucast (b::('a::len) word)) :: ('b::len) signed word))"
  by transfer (simp add: bit_simps)

lemma word_le_ucast_sless:
  "\<lbrakk> x \<le> y; y \<noteq> -1; LENGTH('a) < LENGTH('b) \<rbrakk> \<Longrightarrow>
    (ucast x :: ('b :: len) signed word) <s ucast (y + 1)"
  for x y :: \<open>'a::len word\<close>
  apply (cases \<open>LENGTH('b)\<close>)
  apply simp_all
  apply transfer
  apply (simp add: signed_take_bit_take_bit)
  apply (metis add.commute mask_eq_exp_minus_1 take_bit_incr_eq zle_add1_eq_le)
  done

lemma zero_sle_ucast:
  "(0 <=s ((ucast (b::('a::len) word)) :: ('a::len) signed word))
                = (uint b < 2 ^ (LENGTH('a) - 1))"
  apply transfer
  apply (cases \<open>LENGTH('a)\<close>)
   apply (simp_all add: take_bit_Suc_from_most bit_simps)
  apply (simp_all add: bit_simps disjunctive_add)
  done

lemma nth_w2p_scast:
  "(bit (scast ((2::'a::len signed word) ^ n) :: 'a word) m)
         \<longleftrightarrow> (bit (((2::'a::len  word) ^ n) :: 'a word) m)"
  by (simp add: bit_simps)

lemma scast_nop1 [simp]:
  "((scast ((of_int x)::('a::len) word))::'a signed word) = of_int x"
  by transfer (simp add: take_bit_signed_take_bit)

lemma scast_nop2 [simp]:
  "((scast ((of_int x)::('a::len) signed word))::'a word) = of_int x"
  by transfer (simp add: take_bit_signed_take_bit)

lemmas scast_nop = scast_nop1 scast_nop2 scast_id

type_synonym 'a sword = "'a signed word"

end
