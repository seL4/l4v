(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Author: Jeremy Dawson, NICTA *)

section \<open>Operation variant for the least significant bit\<close>

theory Least_significant_bit
  imports
    "HOL-Library.Word"
    More_Word
begin

class lsb = semiring_bits +
  fixes lsb :: \<open>'a \<Rightarrow> bool\<close>
  assumes lsb_odd: \<open>lsb = odd\<close>

instantiation int :: lsb
begin

definition lsb_int :: \<open>int \<Rightarrow> bool\<close>
  where \<open>lsb i = bit i 0\<close> for i :: int

instance
  by standard (simp add: fun_eq_iff lsb_int_def bit_0)

end

lemma bin_last_conv_lsb: "odd = (lsb :: int \<Rightarrow> bool)"
  by (simp add: lsb_odd)

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
  by (simp_all add: lsb_int_def bit_0)

instantiation word :: (len) lsb
begin

definition lsb_word :: \<open>'a word \<Rightarrow> bool\<close>
  where word_lsb_def: \<open>lsb a \<longleftrightarrow> odd (uint a)\<close> for a :: \<open>'a word\<close>

instance
  apply standard
  apply (simp add: fun_eq_iff word_lsb_def)
  apply transfer apply simp
  done

end

lemma lsb_word_eq:
  \<open>lsb = (odd :: 'a word \<Rightarrow> bool)\<close> for w :: \<open>'a::len word\<close>
  by (fact lsb_odd)

lemma word_lsb_alt: "lsb w = bit w 0"
  for w :: "'a::len word"
  by (simp add: lsb_word_eq bit_0)

lemma word_lsb_1_0 [simp]: "lsb (1::'a::len word) \<and> \<not> lsb (0::'b::len word)"
  unfolding word_lsb_def by simp

lemma word_lsb_int: "lsb w \<longleftrightarrow> uint w mod 2 = 1"
  apply (simp add: lsb_odd flip: odd_iff_mod_2_eq_one)
  apply transfer
  apply simp
  done

lemmas word_ops_lsb = lsb0 [unfolded word_lsb_alt]

lemma word_lsb_numeral [simp]:
  "lsb (numeral bin :: 'a::len word) \<longleftrightarrow> odd (numeral bin :: int)"
  by (simp only: lsb_odd, transfer) rule

lemma word_lsb_neg_numeral [simp]:
  "lsb (- numeral bin :: 'a::len word) \<longleftrightarrow> odd (- numeral bin :: int)"
  by (simp only: lsb_odd, transfer) rule

lemma word_lsb_nat:"lsb w = (unat w mod 2 = 1)"
  apply (simp add: word_lsb_def Groebner_Basis.algebra(31))
  apply transfer
  apply (simp add: even_nat_iff)
  done

instantiation integer :: lsb
begin

context
  includes integer.lifting
begin

lift_definition lsb_integer :: \<open>integer \<Rightarrow> bool\<close> is lsb .

instance
  by (standard; transfer) (fact lsb_odd)

end

end

end
