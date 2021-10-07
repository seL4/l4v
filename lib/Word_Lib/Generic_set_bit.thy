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
    Bits_Int
    Most_significant_bit
begin

class set_bit = semiring_bits +
  fixes set_bit :: \<open>'a \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 'a\<close>
  assumes bit_set_bit_iff [bit_simps]:
    \<open>bit (set_bit a m b) n \<longleftrightarrow>
      (if m = n then b else bit a n) \<and> 2 ^ n \<noteq> 0\<close>

lemma set_bit_eq:
  \<open>set_bit a n b = (if b then Bit_Operations.set_bit else unset_bit) n a\<close>
  for a :: \<open>'a::{ring_bit_operations, set_bit}\<close>
  by (rule bit_eqI) (simp add: bit_simps)

instantiation int :: set_bit
begin

definition set_bit_int :: \<open>int \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> int\<close>
  where \<open>set_bit i n b = bin_sc n b i\<close>

instance
  by standard
    (simp_all add: set_bit_int_def bin_nth_sc_gen bit_simps)

end

lemma int_set_bit_0 [simp]: fixes x :: int shows
  "set_bit x 0 b = of_bool b + 2 * (x div 2)"
  by (auto simp add: set_bit_int_def intro: bin_rl_eqI)

lemma int_set_bit_Suc: fixes x :: int shows
  "set_bit x (Suc n) b = of_bool (odd x) + 2 * set_bit (x div 2) n b"
  by (auto simp add: set_bit_int_def intro: bin_rl_eqI)

lemma bin_last_set_bit:
  "bin_last (set_bit x n b) = (if n > 0 then bin_last x else b)"
  by (cases n) (simp_all add: int_set_bit_Suc)

lemma bin_rest_set_bit:
  "bin_rest (set_bit x n b) = (if n > 0 then set_bit (x div 2) (n - 1) b else x div 2)"
  by (cases n) (simp_all add: int_set_bit_Suc)

lemma int_set_bit_numeral: fixes x :: int shows
  "set_bit x (numeral w) b = of_bool (odd x) + 2 * set_bit (x div 2) (pred_numeral w) b"
  by (simp add: set_bit_int_def)

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

lemma msb_set_bit [simp]: "msb (set_bit (x :: int) n b) \<longleftrightarrow> msb x"
by(simp add: msb_conv_bin_sign set_bit_int_def)

instantiation word :: (len) set_bit
begin

definition set_bit_word :: \<open>'a word \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 'a word\<close>
  where word_set_bit_def: \<open>set_bit a n x = word_of_int (bin_sc n x (uint a))\<close>

instance
  by standard
    (auto simp add: word_set_bit_def bin_nth_sc_gen bit_simps)

end

lemma set_bit_unfold:
  \<open>set_bit w n b = (if b then Bit_Operations.set_bit n w else unset_bit n w)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: set_bit_eq)

lemma bit_set_bit_word_iff [bit_simps]:
  \<open>bit (set_bit w m b) n \<longleftrightarrow> (if m = n then n < LENGTH('a) \<and> b else bit w n)\<close>
  for w :: \<open>'a::len word\<close>
  by (auto simp add: bit_simps dest: bit_imp_le_length)

lemma word_set_nth [simp]: "set_bit w n (test_bit w n) = w"
  for w :: "'a::len word"
  by (auto simp: word_test_bit_def word_set_bit_def)

lemma test_bit_set: "(set_bit w n x) !! n \<longleftrightarrow> n < size w \<and> x"
  for w :: "'a::len word"
  by (auto simp: word_size word_test_bit_def word_set_bit_def nth_bintr)

lemma test_bit_set_gen:
  "test_bit (set_bit w n x) m = (if m = n then n < size w \<and> x else test_bit w m)"
  for w :: "'a::len word"
  apply (unfold word_size word_test_bit_def word_set_bit_def)
  apply (clarsimp simp add: nth_bintr bin_nth_sc_gen)
  apply (auto elim!: test_bit_size [unfolded word_size]
      simp add: word_test_bit_def [symmetric])
  done

lemma word_set_set_same [simp]: "set_bit (set_bit w n x) n y = set_bit w n y"
  for w :: "'a::len word"
  by (rule word_eqI) (simp add : test_bit_set_gen word_size)

lemma word_set_set_diff:
  fixes w :: "'a::len word"
  assumes "m \<noteq> n"
  shows "set_bit (set_bit w m x) n y = set_bit (set_bit w n y) m x"
  by (rule word_eqI) (auto simp: test_bit_set_gen word_size assms)

lemma set_bit_word_of_int: "set_bit (word_of_int x) n b = word_of_int (bin_sc n b x)"
  unfolding word_set_bit_def
  by (rule word_eqI)(simp add: word_size bin_nth_sc_gen nth_bintr)

lemma word_set_numeral [simp]:
  "set_bit (numeral bin::'a::len word) n b =
    word_of_int (bin_sc n b (numeral bin))"
  unfolding word_numeral_alt by (rule set_bit_word_of_int)

lemma word_set_neg_numeral [simp]:
  "set_bit (- numeral bin::'a::len word) n b =
    word_of_int (bin_sc n b (- numeral bin))"
  unfolding word_neg_numeral_alt by (rule set_bit_word_of_int)

lemma word_set_bit_0 [simp]: "set_bit 0 n b = word_of_int (bin_sc n b 0)"
  unfolding word_0_wi by (rule set_bit_word_of_int)

lemma word_set_bit_1 [simp]: "set_bit 1 n b = word_of_int (bin_sc n b 1)"
  unfolding word_1_wi by (rule set_bit_word_of_int)

lemma word_set_nth_iff: "set_bit w n b = w \<longleftrightarrow> w !! n = b \<or> n \<ge> size w"
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
  apply (drule test_bit_size)
  apply force
  done

lemma word_clr_le: "w \<ge> set_bit w n False"
  for w :: "'a::len word"
  apply (simp add: word_set_bit_def word_le_def)
  apply transfer
  apply (rule order_trans)
   apply (rule bintr_bin_clr_le)
  apply simp
  done

lemma word_set_ge: "w \<le> set_bit w n True"
  for w :: "'a::len word"
  apply (simp add: word_set_bit_def word_le_def)
  apply transfer
  apply (rule order_trans [OF _ bintr_bin_set_ge])
  apply simp
  done

lemma set_bit_beyond:
  "size x \<le> n \<Longrightarrow> set_bit x n b = x" for x :: "'a :: len word"
  by (auto intro: word_eqI simp add: test_bit_set_gen word_size)

lemma one_bit_shiftl: "set_bit 0 n True = (1 :: 'a :: len word) << n"
  apply (rule word_eqI)
  apply (auto simp add: test_bit_set_gen nth_shiftl word_size
              simp del: word_set_bit_0 shiftl_1)
  done

lemmas one_bit_pow = trans [OF one_bit_shiftl shiftl_1]

end
