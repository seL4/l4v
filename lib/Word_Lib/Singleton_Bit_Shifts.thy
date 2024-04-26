(*
 * Copyright 2021, Florian Haftmann
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Singleton_Bit_Shifts
  imports
    "HOL-Library.Word"
    Bit_Shifts_Infix_Syntax
begin

definition shiftl1 :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  where shiftl1_eq_double: \<open>shiftl1 = times 2\<close>

lemma bit_shiftl1_iff [bit_simps]:
  \<open>bit (shiftl1 w) n \<longleftrightarrow> 0 < n \<and> n < LENGTH('a) \<and> bit w (n - 1)\<close>
  for w :: \<open>'a::len word\<close>
  by (auto simp add: shiftl1_eq_double bit_simps)

definition shiftr1 :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  where shiftr1_eq_half: \<open>shiftr1 w = w div 2\<close>

lemma bit_shiftr1_iff [bit_simps]:
  \<open>bit (shiftr1 w) n \<longleftrightarrow> bit w (Suc n)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: shiftr1_eq_half bit_Suc)

definition sshiftr1 :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  where sshiftr1_def: \<open>sshiftr1 = signed_drop_bit 1\<close>

lemma bit_sshiftr1_iff [bit_simps]:
  \<open>bit (sshiftr1 w) n \<longleftrightarrow> bit w (if n = LENGTH('a) - 1 then LENGTH('a) - 1 else Suc n)\<close>
  for w :: \<open>'a::len word\<close>
  by (auto simp add: sshiftr1_def bit_simps)

lemma shiftl1_def:
  \<open>shiftl1 = push_bit 1\<close>
  by (rule ext, rule bit_word_eqI) (simp add: bit_simps mult.commute [of _ 2])

lemma shiftr1_def:
  \<open>shiftr1 = drop_bit 1\<close>
  by (rule ext, rule bit_word_eqI) (simp add: bit_simps)

lemma shiftr1_1:
  \<open>shiftr1 (1::'a::len word) = 0\<close>
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma sshiftr1_eq:
  \<open>sshiftr1 w = word_of_int (sint w div 2)\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps min_def simp flip: bit_Suc elim: le_SucE)

lemma shiftl1_eq:
  \<open>shiftl1 w = word_of_int (2 * uint w)\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma shiftr1_eq:
  \<open>shiftr1 w = word_of_int (uint w div 2)\<close>
  by (rule bit_word_eqI) (simp add: bit_simps flip: bit_Suc)

lemma shiftl1_rev:
  \<open>shiftl1 w = word_reverse (shiftr1 (word_reverse w))\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps Suc_diff_Suc simp flip: bit_Suc)

lemma shiftl1_p:
  \<open>shiftl1 w = w + w\<close>
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma shiftr1_bintr:
  \<open>(shiftr1 (numeral w) :: 'a::len word) =
    word_of_int (take_bit LENGTH('a) (numeral w) div 2)\<close>
  apply (rule bit_word_eqI)
  apply (simp add: bit_simps flip: bit_Suc)
  done

lemma sshiftr1_sbintr:
  \<open>(sshiftr1 (numeral w) :: 'a::len word) =
    word_of_int (signed_take_bit (LENGTH('a) - 1) (numeral w) div 2)\<close>
  apply (rule bit_word_eqI)
  apply (simp add: bit_simps flip: bit_Suc)
  apply transfer
  apply auto
  done

lemma shiftl1_wi:
  \<open>shiftl1 (word_of_int w) = word_of_int (2 * w)\<close>
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma shiftl1_numeral:
  \<open>shiftl1 (numeral w) = numeral (Num.Bit0 w)\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps bit_numeral_Bit0_iff)

lemma shiftl1_neg_numeral:
  \<open>shiftl1 (- numeral w) = - numeral (Num.Bit0 w)\<close>
  by (simp add: shiftl1_eq_double)

lemma shiftl1_0:
  \<open>shiftl1 0 = 0\<close>
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma shiftl1_def_u:
  \<open>shiftl1 w = word_of_int (2 * uint w)\<close>
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma shiftl1_def_s:
  \<open>shiftl1 w = word_of_int (2 * sint w)\<close>
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma shiftr1_0:
  \<open>shiftr1 0 = 0\<close>
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma sshiftr1_0:
  \<open>sshiftr1 0 = 0\<close>
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma sshiftr1_n1:
  \<open>sshiftr1 (- 1) = - 1\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma uint_shiftr1:
  \<open>uint (shiftr1 w) = uint w div 2\<close>
  by (rule bit_eqI) (simp add: bit_simps flip: bit_Suc)

lemma shiftr1_div_2:
  \<open>uint (shiftr1 w) = uint w div 2\<close>
  by (fact uint_shiftr1)

lemma sshiftr1_div_2:
  \<open>sint (sshiftr1 w) = sint w div 2\<close>
  by (rule bit_eqI) (auto simp add: bit_simps simp flip: bit_Suc)

lemma nth_shiftl1:
  \<open>bit (shiftl1 w) n \<longleftrightarrow> n < size w \<and> n > 0 \<and> bit w (n - 1)\<close>
  by (auto simp add: word_size bit_simps)

lemma nth_shiftr1:
  \<open>bit (shiftr1 w) n = bit w (Suc n)\<close>
  by (fact bit_shiftr1_iff)

lemma nth_sshiftr1:
  \<open>bit (sshiftr1 w) n = (if n = size w - 1 then bit w n else bit w (Suc n))\<close>
  by (auto simp add: word_size bit_simps)

lemma shiftl_power:
  \<open>(shiftl1 ^^ x) (y::'a::len word) = 2 ^ x * y\<close>
  by (simp add: shiftl1_eq_double funpow_double_eq_push_bit push_bit_eq_mult)

lemma le_shiftr1:
  \<open>shiftr1 u \<le> shiftr1 v\<close> if \<open>u \<le> v\<close>
  using that by (simp add: shiftr1_eq_half word_less_eq_imp_half_less_eq)

lemma le_shiftr1':
  \<open>u \<le> v\<close> if \<open>shiftr1 u \<le> shiftr1 v\<close> \<open>shiftr1 u \<noteq> shiftr1 v\<close>
  by (rule word_half_less_imp_less_eq) (use that in \<open>simp add: shiftr1_eq_half\<close>)

lemma sshiftr_eq_funpow_sshiftr1:
  \<open>w >>> n = (sshiftr1 ^^ n) w\<close>
proof -
  have \<open>sshiftr1 ^^ n = (signed_drop_bit n :: 'a word \<Rightarrow> _)\<close>
    by (induction n) (simp_all add: sshiftr1_def)
  then show ?thesis
    by (simp add: sshiftr_def)
qed

end
