(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Signed division on word\<close>

theory Signed_Division_Word
  imports "HOL-Library.Signed_Division" "HOL-Library.Word"
begin

text \<open>
  The following specification of division follows ISO C99, which in turn adopted the typical
  behavior of hardware modern in the beginning of the 1990ies.
  The underlying integer division is named ``T-division'' in \cite{leijen01}.
\<close>

instantiation word :: (len) signed_division
begin

lift_definition signed_divide_word :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k l. signed_take_bit (LENGTH('a) - Suc 0) k sdiv signed_take_bit (LENGTH('a) - Suc 0) l\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lift_definition signed_modulo_word :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k l. signed_take_bit (LENGTH('a) - Suc 0) k smod signed_take_bit (LENGTH('a) - Suc 0) l\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lemma sdiv_word_def [code]:
  \<open>v sdiv w = word_of_int (sint v sdiv sint w)\<close>
  for v w :: \<open>'a::len word\<close>
  by transfer simp

lemma smod_word_def [code]:
  \<open>v smod w = word_of_int (sint v smod sint w)\<close>
  for v w :: \<open>'a::len word\<close>
  by transfer simp

instance proof
  fix v w :: \<open>'a word\<close>
  have \<open>sint v sdiv sint w * sint w + sint v smod sint w = sint v\<close>
    by (fact sdiv_mult_smod_eq)
  then have \<open>word_of_int (sint v sdiv sint w * sint w + sint v smod sint w) = (word_of_int (sint v) :: 'a word)\<close>
    by simp
  then show \<open>v sdiv w * w + v smod w = v\<close>
    by (simp add: sdiv_word_def smod_word_def)
qed

end

lemma sdiv_smod_id:
  \<open>(a sdiv b) * b + (a smod b) = a\<close>
  for a b :: \<open>'a::len word\<close>
  by (fact sdiv_mult_smod_eq)

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

lemma word_sdiv_div0 [simp]:
    "(a :: ('a::len) word) sdiv 0 = 0"
  apply (auto simp: sdiv_word_def signed_divide_int_def sgn_if)
  done

lemma smod_word_zero [simp]:
  \<open>w smod 0 = w\<close> for w :: \<open>'a::len word\<close>
  by transfer (simp add: take_bit_signed_take_bit)

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

lemma smod_word_one [simp]:
  \<open>w smod 1 = 0\<close> for w :: \<open>'a::len word\<close>
  by (simp add: smod_word_def signed_modulo_int_def)

lemma word_sdiv_div_minus1 [simp]:
    "(a :: ('a::len) word) sdiv -1 = -a"
  apply (auto simp: sdiv_word_def signed_divide_int_def sgn_if)
  apply transfer
  apply simp
  apply (metis Suc_pred len_gt_0 signed_take_bit_eq_iff_take_bit_eq signed_take_bit_of_0 take_bit_of_0)
  done

lemma smod_word_minus_one [simp]:
  \<open>w smod - 1 = 0\<close> for w :: \<open>'a::len word\<close>
  by (simp add: smod_word_def signed_modulo_int_def)

lemma one_sdiv_word_eq [simp]:
  \<open>1 sdiv w = of_bool (w = 1 \<or> w = - 1) * w\<close> for w :: \<open>'a::len word\<close>
proof (cases \<open>1 < \<bar>sint w\<bar>\<close>)
  case True
  then show ?thesis
    by (auto simp add: sdiv_word_def signed_divide_int_def split: if_splits)
next
  case False
  then have \<open>\<bar>sint w\<bar> \<le> 1\<close>
    by simp
  then have \<open>sint w \<in> {- 1, 0, 1}\<close>
    by auto
  then have \<open>(word_of_int (sint w) :: 'a::len word) \<in> word_of_int ` {- 1, 0, 1}\<close>
    by blast
  then have \<open>w \<in> {- 1, 0, 1}\<close>
    by simp
  then show ?thesis by auto
qed

lemma one_smod_word_eq [simp]:
  \<open>1 smod w = 1 - of_bool (w = 1 \<or> w = - 1)\<close> for w :: \<open>'a::len word\<close>
  using sdiv_smod_id [of 1 w] by auto

lemma minus_one_sdiv_word_eq [simp]:
  \<open>- 1 sdiv w = - (1 sdiv w)\<close> for w :: \<open>'a::len word\<close>
  apply (auto simp add: sdiv_word_def signed_divide_int_def)
  apply transfer
  apply simp
  done

lemma minus_one_smod_word_eq [simp]:
  \<open>- 1 smod w = - (1 smod w)\<close> for w :: \<open>'a::len word\<close>
  using sdiv_smod_id [of \<open>- 1\<close> w] by auto

lemma smod_word_alt_def:
  "(a :: ('a::len) word) smod b = a - (a sdiv b) * b"
  by (simp add: minus_sdiv_mult_eq_smod)

lemmas sdiv_word_numeral_numeral [simp] =
  sdiv_word_def [of \<open>numeral a\<close> \<open>numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas sdiv_word_minus_numeral_numeral [simp] =
  sdiv_word_def [of \<open>- numeral a\<close> \<open>numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas sdiv_word_numeral_minus_numeral [simp] =
  sdiv_word_def [of \<open>numeral a\<close> \<open>- numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas sdiv_word_minus_numeral_minus_numeral [simp] =
  sdiv_word_def [of \<open>- numeral a\<close> \<open>- numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b

lemmas smod_word_numeral_numeral [simp] =
  smod_word_def [of \<open>numeral a\<close> \<open>numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas smod_word_minus_numeral_numeral [simp] =
  smod_word_def [of \<open>- numeral a\<close> \<open>numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas smod_word_numeral_minus_numeral [simp] =
  smod_word_def [of \<open>numeral a\<close> \<open>- numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas smod_word_minus_numeral_minus_numeral [simp] =
  smod_word_def [of \<open>- numeral a\<close> \<open>- numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b

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

lemma sdiv_word_max:
  \<open>sint a sdiv sint b \<le> 2 ^ (size a - Suc 0)\<close>
  for a b :: \<open>'a::len word\<close>
proof (cases \<open>sint a = 0 \<or> sint b = 0 \<or> sgn (sint a) \<noteq> sgn (sint b)\<close>)
  case True then show ?thesis
    apply (auto simp add: sgn_if not_less signed_divide_int_def split: if_splits)
     apply (smt (z3) pos_imp_zdiv_neg_iff zero_le_power)
    apply (smt (z3) not_exp_less_eq_0_int pos_imp_zdiv_neg_iff)
    done
next
  case False
  then have \<open>\<bar>sint a\<bar> div \<bar>sint b\<bar> \<le> \<bar>sint a\<bar>\<close>
    by (subst nat_le_eq_zle [symmetric]) (simp_all add: div_abs_eq_div_nat)
  also have \<open>\<bar>sint a\<bar> \<le> 2 ^ (size a - Suc 0)\<close>
    using sint_range_size [of a] by auto
  finally show ?thesis
    using False by (simp add: signed_divide_int_def)
qed

lemmas word_sdiv_numerals_lhs = sdiv_word_def[where v="numeral x" for x]
    sdiv_word_def[where v=0] sdiv_word_def[where v=1]

lemmas word_sdiv_numerals = word_sdiv_numerals_lhs[where w="numeral y" for y]
    word_sdiv_numerals_lhs[where w=0] word_sdiv_numerals_lhs[where w=1]

lemma smod_word_mod_0:
  "x smod (0 :: ('a::len) word) = x"
  by (fact smod_word_zero)

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

lemmas word_smod_numerals_lhs = smod_word_def[where v="numeral x" for x]
    smod_word_def[where v=0] smod_word_def[where v=1]

lemmas word_smod_numerals = word_smod_numerals_lhs[where w="numeral y" for y]
    word_smod_numerals_lhs[where w=0] word_smod_numerals_lhs[where w=1]

end
