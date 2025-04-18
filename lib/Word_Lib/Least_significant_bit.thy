(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Author: Jeremy Dawson, NICTA *)

section \<open>Abbreviation syntax for the least significant bit\<close>

theory Least_significant_bit
  imports
    "HOL-Library.Word"
begin

context semiring_bit_operations
begin

abbreviation lsb :: \<open>'a \<Rightarrow> bool\<close>
  where \<open>lsb a \<equiv> bit a 0\<close>

lemma lsb_odd:
  \<open>lsb = odd\<close>
  by (simp add: bit_0)

end

lemma bin_last_conv_lsb:
  \<open>odd = (lsb :: int \<Rightarrow> bool)\<close>
  by (simp add: bit_0)

lemma int_lsb_numeral [simp]:
  "lsb (0 :: int) = False"
  "lsb (1 :: int) = True"
  "lsb (Numeral1 :: int) = True"
  "lsb (- 1 :: int) = True"
  "lsb (- Numeral1 :: int) = True"
  "lsb (numeral (num.Bit0 w) :: int) = False"
  "lsb (numeral (num.Bit1 w) :: int) = True"
  "lsb (- numeral (num.Bit0 w) :: int) = False"
  "lsb (- numeral (num.Bit1 w) :: int) = True"
  by simp_all

lemma word_lsb_def:
  \<open>lsb a \<longleftrightarrow> odd (uint a)\<close> for a :: \<open>'a::len word\<close>
  by (simp flip: bit_0 add: bit_simps)

lemma lsb_word_eq:
  \<open>lsb = (odd :: 'a word \<Rightarrow> bool)\<close> for w :: \<open>'a::len word\<close>
  by (fact lsb_odd)

lemma word_lsb_alt: "lsb w = bit w 0"
  for w :: "'a::len word"
  by (simp add: lsb_word_eq bit_0)

lemma word_lsb_1_0 [simp]: "lsb (1::'a::len word) \<and> \<not> lsb (0::'b::len word)"
  unfolding word_lsb_def by simp

lemma word_lsb_int: "lsb w \<longleftrightarrow> uint w mod 2 = 1"
  by (simp flip: odd_iff_mod_2_eq_one bit_0 add: bit_simps)

lemma word_ops_lsb:
  \<open>(bit (or x y) 0 \<longleftrightarrow> bit x 0 \<or> bit y 0)
    \<and> (bit (and x y) 0 \<longleftrightarrow> bit x 0 \<and> bit y 0)
    \<and> (bit (xor x y) 0 \<longleftrightarrow> bit x 0 \<noteq> bit y 0)
    \<and> (bit (not x) 0 \<longleftrightarrow> \<not> bit x 0)\<close>
  by (simp add: bit_simps)

lemma word_lsb_numeral [simp]:
  "lsb (numeral bin :: 'a::len word) \<longleftrightarrow> odd (numeral bin :: int)"
  by (simp only: flip: bit_0) simp

lemma word_lsb_neg_numeral [simp]:
  "lsb (- numeral bin :: 'a::len word) \<longleftrightarrow> odd (- numeral bin :: int)"
  by (simp only: flip: bit_0) simp

lemma word_lsb_nat: "lsb w = (unat w mod 2 = 1)"
  by (simp only: flip: odd_iff_mod_2_eq_one bit_0) (simp add: bit_simps)

end
