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

definition set_bit :: \<open>'a \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 'a::semiring_bit_operations\<close>
  where set_bit_eq: \<open>set_bit a n b = (if b then Bit_Operations.set_bit else unset_bit) n a\<close>

lemma bit_set_bit_iff [bit_simps]:
  \<open>bit (set_bit a m b) n \<longleftrightarrow>
    (if m = n then possible_bit TYPE('a) n \<and> b else bit a n)\<close>
  for a :: \<open>'a::semiring_bit_operations\<close>
  by (auto simp add: set_bit_eq bit_simps bit_imp_possible_bit)

lemma bit_set_bit_word_iff [bit_simps]:
  \<open>bit (set_bit w m b) n \<longleftrightarrow>
    (if m = n then n < LENGTH('a) \<and> b else bit w n)\<close> for w :: \<open>'a::len word\<close>
  by (simp add: bit_simps bit_imp_le_length)

lemma bit_set_bit_iff_2n:
  \<open>bit (set_bit a m b) n \<longleftrightarrow>
    (if m = n then b else bit a n) \<and> 2 ^ n \<noteq> (0 :: 'a)\<close>
  for a :: \<open>'a::semiring_bit_operations\<close>
  by (auto simp add: bit_simps fold_possible_bit bit_imp_possible_bit)

context
  includes bit_operations_syntax
begin

lemma int_set_bit_0 [simp]:
  "set_bit x 0 b = of_bool b + 2 * (x div 2)" for x :: int
  by (simp add: set_bit_eq set_bit_0 unset_bit_0)

lemma int_set_bit_Suc [simp]:
  "set_bit x (Suc n) b = of_bool (odd x) + 2 * set_bit (x div 2) n b" for x :: int
  by (simp add: set_bit_eq set_bit_Suc unset_bit_Suc mod2_eq_if)

lemma bin_last_set_bit:
  "odd (set_bit x n b :: int) = (if n > 0 then odd x else b)"
  by (cases n) (simp_all add: int_set_bit_Suc)

lemma bin_rest_set_bit:
  "(set_bit x n b :: int) div 2 = (if n > 0 then set_bit (x div 2) (n - 1) b else x div 2)"
  by (cases n) (simp_all add: int_set_bit_Suc)

lemma int_set_bit_numeral [simp]:
  "set_bit x (numeral w) b = of_bool (odd x) + 2 * set_bit (x div 2) (pred_numeral w) b" for x :: int
  by (simp add: numeral_eq_Suc int_set_bit_Suc)

lemmas int_set_bit_numerals [simp] =
  int_set_bit_numeral[where x="numeral w'"]
  int_set_bit_numeral[where x="- numeral w'"]
  int_set_bit_numeral[where x="Numeral1"]
  int_set_bit_numeral[where x="1"]
  int_set_bit_numeral[where x="0"]
  int_set_bit_Suc[where x="numeral w'"]
  int_set_bit_Suc[where x="- numeral w'"]
  int_set_bit_Suc[where x="Numeral1"]
  int_set_bit_Suc[where x="1"]
  int_set_bit_Suc[where x="0"]
  for w'

lemma fixes i :: int
  shows int_set_bit_True_conv_OR [code]: "Generic_set_bit.set_bit i n True = i OR push_bit n 1"
  and int_set_bit_False_conv_NAND [code]: "Generic_set_bit.set_bit i n False = i AND NOT (push_bit n 1)"
  and int_set_bit_conv_ops: "Generic_set_bit.set_bit i n b = (if b then i OR (push_bit n 1) else i AND NOT (push_bit n 1))"
  by (simp_all add: bit_eq_iff) (auto simp add: bit_simps)

lemma msb_set_bit [simp]:
  "msb (set_bit (x :: int) n b) \<longleftrightarrow> msb x"
  by (simp add: msb_int_def set_bit_eq)

lemmas msb_bin_sc = msb_set_bit

abbreviation (input) bin_sc :: \<open>nat \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>bin_sc n b i \<equiv> set_bit i n b\<close>

lemma bin_sc_eq:
  \<open>bin_sc n False = unset_bit n\<close>
  \<open>bin_sc n True = Bit_Operations.set_bit n\<close>
  by (simp_all add: set_bit_eq)

lemma bin_sc_0:
  "bin_sc 0 b w = of_bool b + 2 * (w div 2)"
  by (fact int_set_bit_0)

lemma bin_sc_Suc:
  "bin_sc (Suc n) b w = of_bool (odd w) + 2 * bin_sc n b (w div 2)"
  by (fact int_set_bit_Suc)

lemma bin_nth_sc [bit_simps]: "bit (bin_sc n b w) n \<longleftrightarrow> b"
  by (simp add: bit_simps)

lemma bin_sc_sc_same [simp]: "bin_sc n c (bin_sc n b w) = bin_sc n c w"
  by (rule bit_eqI) (simp add: bit_simps)

lemma bin_sc_sc_diff: "m \<noteq> n \<Longrightarrow> bin_sc m c (bin_sc n b w) = bin_sc n b (bin_sc m c w)"
  by (rule bit_eqI) (simp add: bit_simps)

lemma bin_nth_sc_gen: "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) (bin_sc n b w) m = (if m = n then b else (bit :: int \<Rightarrow> nat \<Rightarrow> bool) w m)"
  by (simp add: bit_simps)

lemma bin_sc_nth [simp]: "bin_sc n ((bit :: int \<Rightarrow> nat \<Rightarrow> bool) w n) w = w"
  by (rule bit_eqI) (simp add: bin_nth_sc_gen)

lemma bin_sc_bintr [simp]:
  "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m (bin_sc n x ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m w)) = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m (bin_sc n x w)"
  by (simp add: set_bit_eq take_bit_set_bit_eq take_bit_unset_bit_eq)

lemma bin_clr_le: "bin_sc n False w \<le> w"
  by (simp add: set_bit_eq unset_bit_less_eq)

lemma bin_set_ge: "bin_sc n True w \<ge> w"
  by (simp add: set_bit_eq set_bit_greater_eq)

lemma bintr_bin_clr_le: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (bin_sc m False w) \<le> (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w"
  by (simp add: set_bit_eq take_bit_unset_bit_eq unset_bit_less_eq)

lemma bintr_bin_set_ge: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (bin_sc m True w) \<ge> (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w"
  by (simp add: set_bit_eq take_bit_set_bit_eq set_bit_greater_eq)

lemma bin_sc_FP [simp]: "bin_sc n False 0 = 0"
  by (induct n) auto

lemma bin_sc_TM [simp]: "bin_sc n True (- 1) = - 1"
  by (induct n) auto

lemmas bin_sc_simps = bin_sc_0 bin_sc_Suc bin_sc_TM bin_sc_FP

lemma bin_sc_minus: "0 < n \<Longrightarrow> bin_sc (Suc (n - 1)) b w = bin_sc n b w"
  by auto

lemmas bin_sc_Suc_minus =
  trans [OF bin_sc_minus [symmetric] bin_sc_Suc]

lemma bin_sc_numeral:
  "bin_sc (numeral k) b w =
    of_bool (odd w) + 2 * bin_sc (pred_numeral k) b (w div 2)"
  by (fact int_set_bit_numeral)

lemmas bin_sc_minus_simps =
  bin_sc_simps (2,3,4) [THEN [2] trans, OF bin_sc_minus [THEN sym]]

lemma bin_sc_pos:
  "0 \<le> i \<Longrightarrow> 0 \<le> bin_sc n b i"
  by (simp add: set_bit_eq)

lemma bin_clr_conv_NAND:
  "bin_sc n False i = i AND NOT (push_bit n 1)"
  by (fact int_set_bit_False_conv_NAND)

lemma bin_set_conv_OR:
  "bin_sc n True i = i OR (push_bit n 1)"
  by (fact int_set_bit_True_conv_OR)

lemma word_set_bit_def:
  \<open>set_bit a n x = word_of_int (bin_sc n x (uint a))\<close>
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma set_bit_word_of_int:
  "set_bit (word_of_int x) n b = word_of_int (bin_sc n b x)"
  by (rule word_eqI) (auto simp add: bit_simps)

lemma word_set_numeral [simp]:
  "set_bit (numeral bin::'a::len word) n b =
    word_of_int (bin_sc n b (numeral bin))"
  by (metis set_bit_word_of_int word_of_int_numeral)

lemma word_set_neg_numeral [simp]:
  "set_bit (- numeral bin::'a::len word) n b =
    word_of_int (bin_sc n b (- numeral bin))"
  unfolding word_neg_numeral_alt by (rule set_bit_word_of_int)

lemma word_set_bit_0 [simp]: "set_bit 0 n b = word_of_int (bin_sc n b 0)"
  unfolding word_0_wi by (rule set_bit_word_of_int)

lemma word_set_bit_1 [simp]: "set_bit 1 n b = word_of_int (bin_sc n b 1)"
  unfolding word_1_wi by (rule set_bit_word_of_int)

lemma setBit_no: "Bit_Operations.set_bit n (numeral bin) = word_of_int (bin_sc n True (numeral bin))"
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma clearBit_no:
  "unset_bit n (numeral bin) = word_of_int (bin_sc n False (numeral bin))"
  by (rule bit_word_eqI) (simp add: bit_simps)

end

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
  by (smt (verit) linorder_not_le test_bit_set word_set_nth word_set_set_same)

lemma word_clr_le: "w \<ge> set_bit w n False"
  for w :: "'a::len word"
  by (metis test_bit_set_gen word_leI)

lemma word_set_ge: "w \<le> set_bit w n True"
  for w :: "'a::len word"
  by (simp add: test_bit_set_gen word_leI)

lemma set_bit_beyond:
  "size x \<le> n \<Longrightarrow> set_bit x n b = x" for x :: "'a :: len word"
  by (simp add: word_set_nth_iff)

lemma one_bit_shiftl: "set_bit 0 n True = (1 :: 'a :: len word) << n"
  by (rule word_eqI) (auto simp add: word_size bit_simps)

lemma one_bit_pow: "set_bit 0 n True = (2 :: 'a :: len word) ^ n"
  by (rule word_eqI) (simp add: bit_simps)

end
