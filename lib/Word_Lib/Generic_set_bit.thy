(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Author: Jeremy Dawson, NICTA *)

section \<open>Operation variant for setting and unsetting bits\<close>

theory Generic_set_bit
  imports
    "HOL-Library.Word"
    Most_significant_bit
begin

class set_bit = semiring_bits +
  fixes set_bit :: \<open>'a \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 'a\<close>
  assumes bit_set_bit_iff_2n:
    \<open>bit (set_bit a m b) n \<longleftrightarrow>
      (if m = n then b else bit a n) \<and> 2 ^ n \<noteq> 0\<close>

lemmas bit_set_bit_iff[bit_simps] = bit_set_bit_iff_2n[simplified fold_possible_bit simp_thms]

lemma set_bit_eq:
  \<open>set_bit a n b = (if b then Bit_Operations.set_bit else unset_bit) n a\<close>
  for a :: \<open>'a::{ring_bit_operations, set_bit}\<close>
  by (rule bit_eqI) (simp add: bit_simps)

instantiation int :: set_bit
begin

definition set_bit_int :: \<open>int \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> int\<close>
  where \<open>set_bit_int i n b = (if b then Bit_Operations.set_bit else Bit_Operations.unset_bit) n i\<close>

instance
  by standard (simp_all add: set_bit_int_def bit_simps)

end

context
  includes bit_operations_syntax
begin

lemma fixes i :: int
  shows int_set_bit_True_conv_OR [code]: "Generic_set_bit.set_bit i n True = i OR push_bit n 1"
  and int_set_bit_False_conv_NAND [code]: "Generic_set_bit.set_bit i n False = i AND NOT (push_bit n 1)"
  and int_set_bit_conv_ops: "Generic_set_bit.set_bit i n b = (if b then i OR (push_bit n 1) else i AND NOT (push_bit n 1))"
  by (simp_all add: bit_eq_iff) (auto simp add: bit_simps)

end

instantiation word :: (len) set_bit
begin

definition set_bit_word :: \<open>'a word \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 'a word\<close>
  where set_bit_unfold: \<open>set_bit w n b = (if b then Bit_Operations.set_bit n w else unset_bit n w)\<close>
  for w :: \<open>'a::len word\<close>

instance
  by standard (auto simp add: set_bit_unfold bit_simps dest: bit_imp_le_length)

end

lemma bit_set_bit_word_iff [bit_simps]:
  \<open>bit (set_bit w m b) n \<longleftrightarrow> (if m = n then n < LENGTH('a) \<and> b else bit w n)\<close>
  for w :: \<open>'a::len word\<close>
  by (auto simp add: bit_simps dest: bit_imp_le_length)

lemma test_bit_set_gen:
  "bit (set_bit w n x) m \<longleftrightarrow> (if m = n then n < size w \<and> x else bit w m)"
  for w :: "'a::len word"
  by (simp add: bit_set_bit_word_iff word_size)

lemma test_bit_set:
  "bit (set_bit w n x) n \<longleftrightarrow> n < size w \<and> x"
  for w :: "'a::len word"
  by (auto simp add: bit_simps word_size)

lemma word_set_nth: "set_bit w n (bit w n) = w"
  for w :: "'a::len word"
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma word_set_set_same [simp]: "set_bit (set_bit w n x) n y = set_bit w n y"
  for w :: "'a::len word"
  by (rule word_eqI) (simp add : test_bit_set_gen word_size)

lemma word_set_set_diff:
  fixes w :: "'a::len word"
  assumes "m \<noteq> n"
  shows "set_bit (set_bit w m x) n y = set_bit (set_bit w n y) m x"
  by (rule word_eqI) (auto simp: test_bit_set_gen word_size assms)

lemma word_set_nth_iff: "set_bit w n b = w \<longleftrightarrow> bit w n = b \<or> n \<ge> size w"
  for w :: "'a::len word"
  apply (rule iffI)
   apply (rule disjCI)
   apply (drule word_eqD)
   apply (erule sym [THEN trans])
   apply (simp add: test_bit_set)
  apply (erule disjE)
   apply clarsimp
  apply (rule word_eqI)
   apply (clarsimp simp add : test_bit_set_gen)
   apply (auto simp add: word_size)
  apply (rule bit_eqI)
  apply (simp add: bit_simps)
  done

lemma word_clr_le: "w \<ge> set_bit w n False"
  for w :: "'a::len word"
  apply (simp add: set_bit_unfold)
  apply transfer
  apply (simp add: take_bit_unset_bit_eq unset_bit_less_eq)
  done

lemma word_set_ge: "w \<le> set_bit w n True"
  for w :: "'a::len word"
  apply (simp add: set_bit_unfold)
  apply transfer
  apply (simp add: take_bit_set_bit_eq set_bit_greater_eq)
  done

lemma set_bit_beyond:
  "size x \<le> n \<Longrightarrow> set_bit x n b = x" for x :: "'a :: len word"
  by (simp add: word_set_nth_iff)

lemma one_bit_shiftl: "set_bit 0 n True = (1 :: 'a :: len word) << n"
  apply (rule word_eqI)
  apply (auto simp add: word_size bit_simps)
  done

lemma one_bit_pow: "set_bit 0 n True = (2 :: 'a :: len word) ^ n"
  by (simp add: one_bit_shiftl shiftl_def)

instantiation integer :: set_bit
begin

context
  includes integer.lifting
begin

lift_definition set_bit_integer :: \<open>integer \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> integer\<close> is set_bit .

instance
  by (standard; transfer) (simp add: bit_simps)

end

end

end
