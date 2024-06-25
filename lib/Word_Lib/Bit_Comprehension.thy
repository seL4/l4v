(*
 * Copyright Brian Huffman, PSU; Jeremy Dawson and Gerwin Klein, NICTA
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Comprehension syntax for bit expressions\<close>

theory Bit_Comprehension
  imports
    "HOL-Library.Word"
begin

class bit_comprehension = ring_bit_operations +
  fixes set_bits :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> 'a\<close>  (binder \<open>BITS \<close> 10)
  assumes set_bits_bit_eq: \<open>set_bits (bit a) = a\<close>
begin

lemma set_bits_False_eq [simp]:
  \<open>(BITS _. False) = 0\<close>
  using set_bits_bit_eq [of 0] by (simp add: bot_fun_def)

end

instantiation word :: (len) bit_comprehension
begin

definition word_set_bits_def:
  \<open>(BITS n. P n) = (horner_sum of_bool 2 (map P [0..<LENGTH('a)]) :: 'a word)\<close>

instance by standard
  (simp add: word_set_bits_def horner_sum_bit_eq_take_bit)

end

lemma bit_set_bits_word_iff [bit_simps]:
  \<open>bit (set_bits P :: 'a::len word) n \<longleftrightarrow> n < LENGTH('a) \<and> P n\<close>
  by (auto simp add: word_set_bits_def bit_horner_sum_bit_word_iff)

lemma word_of_int_conv_set_bits: "word_of_int i = (BITS n. bit i n)"
  by (rule bit_eqI) (auto simp add: bit_simps)

lemma set_bits_K_False:
  \<open>set_bits (\<lambda>_. False) = (0 :: 'a :: len word)\<close>
  by (fact set_bits_False_eq)

lemma word_test_bit_set_bits: "bit (BITS n. f n :: 'a :: len word) n \<longleftrightarrow> n < LENGTH('a) \<and> f n"
  by (fact bit_set_bits_word_iff)

context
  includes bit_operations_syntax
  fixes f :: \<open>nat \<Rightarrow> bool\<close>
begin

definition set_bits_aux :: \<open>nat \<Rightarrow> 'a word \<Rightarrow> 'a::len word\<close>
  where \<open>set_bits_aux n w = push_bit n w OR take_bit n (set_bits f)\<close>

lemma bit_set_bit_aux [bit_simps]:
  \<open>bit (set_bits_aux n w) m \<longleftrightarrow> m < LENGTH('a) \<and>
    (if m < n then f m else bit w (m - n))\<close> for w :: \<open>'a::len word\<close>
  by (auto simp add: bit_simps set_bits_aux_def)

corollary set_bits_conv_set_bits_aux:
  \<open>set_bits f = (set_bits_aux LENGTH('a) 0 :: 'a :: len word)\<close>
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma set_bits_aux_0 [simp]:
  \<open>set_bits_aux 0 w = w\<close>
  by (simp add: set_bits_aux_def)

lemma set_bits_aux_Suc [simp]:
  \<open>set_bits_aux (Suc n) w = set_bits_aux n (push_bit 1 w OR (if f n then 1 else 0))\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps le_less_Suc_eq mult.commute [of _ 2])

lemma set_bits_aux_simps [code]:
  \<open>set_bits_aux 0 w = w\<close>
  \<open>set_bits_aux (Suc n) w = set_bits_aux n (push_bit 1 w OR (if f n then 1 else 0))\<close>
  by simp_all

lemma set_bits_aux_rec:
  \<open>set_bits_aux n w =
  (if n = 0 then w
   else let n' = n - 1 in set_bits_aux n' (push_bit 1 w OR (if f n' then 1 else 0)))\<close>
  by (cases n) simp_all

end

end
