(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Signed division on word\<close>

theory Signed_Division_Word
  imports "HOL-Library.Signed_Division" "HOL-Library.Word"
begin

instantiation word :: (len) signed_division
begin

lift_definition signed_divide_word :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k l. signed_take_bit (LENGTH('a) - Suc 0) k sdiv signed_take_bit (LENGTH('a) - Suc 0) l\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lift_definition signed_modulo_word :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k l. signed_take_bit (LENGTH('a) - Suc 0) k smod signed_take_bit (LENGTH('a) - Suc 0) l\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

instance ..

end

lemma sdiv_word_def [code]:
  \<open>v sdiv w = word_of_int (sint v sdiv sint w)\<close>
  for v w :: \<open>'a::len word\<close>
  by transfer simp

lemma smod_word_def [code]:
  \<open>v smod w = word_of_int (sint v smod sint w)\<close>
  for v w :: \<open>'a::len word\<close>
  by transfer simp

lemma sdiv_smod_id:
  \<open>(a sdiv b) * b + (a smod b) = a\<close>
  for a b :: \<open>'a::len word\<close>
  by (cases \<open>sint a < 0\<close>; cases \<open>sint b < 0\<close>) (simp_all add: signed_modulo_int_def sdiv_word_def smod_word_def)

lemma signed_div_arith:
    "sint ((a::('a::len) word) sdiv b) = signed_take_bit (LENGTH('a) - 1) (sint a sdiv sint b)"
  apply transfer
  apply simp
  done

lemma signed_mod_arith:
    "sint ((a::('a::len) word) smod b) = signed_take_bit (LENGTH('a) - 1) (sint a smod sint b)"
  apply transfer
  apply simp
  done

lemma word_sdiv_div1 [simp]:
    "(a :: ('a::len) word) sdiv 1 = a"
  apply (cases \<open>LENGTH('a)\<close>)
  apply simp_all
  apply transfer
  apply simp
  apply (case_tac nat)
   apply simp_all
  apply (simp add: take_bit_signed_take_bit)
  done

lemma word_sdiv_div0 [simp]:
    "(a :: ('a::len) word) sdiv 0 = 0"
  apply (auto simp: sdiv_word_def signed_divide_int_def sgn_if)
  done

lemma word_sdiv_div_minus1 [simp]:
    "(a :: ('a::len) word) sdiv -1 = -a"
  apply (auto simp: sdiv_word_def signed_divide_int_def sgn_if)
  apply transfer
  apply simp
  apply (metis Suc_pred len_gt_0 signed_take_bit_eq_iff_take_bit_eq signed_take_bit_of_0 take_bit_of_0)
  done

lemmas word_sdiv_0 = word_sdiv_div0

lemma sdiv_word_min:
    "- (2 ^ (size a - 1)) \<le> sint (a :: ('a::len) word) sdiv sint (b :: ('a::len) word)"
  using sdiv_int_range [where a="sint a" and b="sint b"]
  apply auto
  apply (cases \<open>LENGTH('a)\<close>)
   apply simp_all
  apply transfer
  apply simp
  apply (rule order_trans)
   defer
   apply assumption
  apply simp
  apply (metis abs_le_iff add.inverse_inverse le_cases le_minus_iff not_le signed_take_bit_int_eq_self_iff signed_take_bit_minus)
  done

lemmas word_sdiv_numerals_lhs = sdiv_word_def[where v="numeral x" for x]
    sdiv_word_def[where v=0] sdiv_word_def[where v=1]

lemmas word_sdiv_numerals = word_sdiv_numerals_lhs[where w="numeral y" for y]
    word_sdiv_numerals_lhs[where w=0] word_sdiv_numerals_lhs[where w=1]

lemma smod_word_mod_0 [simp]:
  "x smod (0 :: ('a::len) word) = x"
  by (clarsimp simp: smod_word_def)

lemma smod_word_0_mod [simp]:
  "0 smod (x :: ('a::len) word) = 0"
  by (clarsimp simp: smod_word_def)

lemma smod_word_max:
  "sint (a::'a word) smod sint (b::'a word) < 2 ^ (LENGTH('a::len) - Suc 0)"
  apply (cases \<open>sint b = 0\<close>)
   apply (simp_all add: sint_less)
  apply (cases \<open>LENGTH('a)\<close>)
   apply simp_all
  using smod_int_range [where a="sint a" and b="sint b"]
  apply auto
  apply (rule less_le_trans)
   apply assumption
  apply (auto simp add: abs_le_iff)
   apply (metis diff_Suc_1 le_cases linorder_not_le sint_lt)
  apply (metis add.inverse_inverse diff_Suc_1 linorder_not_less neg_less_iff_less sint_ge)
  done

lemma smod_word_min:
  "- (2 ^ (LENGTH('a::len) - Suc 0)) \<le> sint (a::'a word) smod sint (b::'a word)"
  apply (cases \<open>LENGTH('a)\<close>)
   apply simp_all
  apply (cases \<open>sint b = 0\<close>)
   apply simp_all
   apply (metis diff_Suc_1 sint_ge)
  using smod_int_range [where a="sint a" and b="sint b"]
  apply auto
  apply (rule order_trans)
   defer
   apply assumption
  apply (auto simp add: algebra_simps abs_le_iff)
   apply (metis abs_zero add.left_neutral add_mono_thms_linordered_semiring(1) diff_Suc_1 le_cases linorder_not_less sint_lt zabs_less_one_iff)
  apply (metis abs_zero add.inverse_inverse add.left_neutral add_mono_thms_linordered_semiring(1) diff_Suc_1 le_cases le_minus_iff linorder_not_less sint_ge zabs_less_one_iff)
  done

lemma smod_word_alt_def:
  "(a :: ('a::len) word) smod b = a - (a sdiv b) * b"
  apply (cases \<open>a \<noteq> - (2 ^ (LENGTH('a) - 1)) \<or> b \<noteq> - 1\<close>)
   apply (clarsimp simp: smod_word_def sdiv_word_def signed_modulo_int_def
     simp flip: wi_hom_sub wi_hom_mult)
  apply (clarsimp simp: smod_word_def signed_modulo_int_def)
  done

lemmas word_smod_numerals_lhs = smod_word_def[where v="numeral x" for x]
    smod_word_def[where v=0] smod_word_def[where v=1]

lemmas word_smod_numerals = word_smod_numerals_lhs[where w="numeral y" for y]
    word_smod_numerals_lhs[where w=0] word_smod_numerals_lhs[where w=1]

end