(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Words of Length 64"

theory Word_64
  imports
    Word_Lemmas
    Word_Names
    Word_Syntax
    Rsplit
    More_Word_Operations
begin

context
  includes bit_operations_syntax
begin

lemma len64: "len_of (x :: 64 itself) = 64" by simp

lemma ucast_8_64_inj:
  "inj (ucast ::  8 word \<Rightarrow> 64 word)"
  by (rule down_ucast_inj) (clarsimp simp: is_down_def target_size source_size)

lemmas unat_power_lower64' = unat_power_lower[where 'a=64]

lemmas word64_less_sub_le' = word_less_sub_le[where 'a = 64]

lemmas word64_power_less_1' = word_power_less_1[where 'a = 64]

lemmas unat_of_nat64' = unat_of_nat_eq[where 'a=64]

lemmas unat_mask_word64' = unat_mask[where 'a=64]

lemmas word64_minus_one_le' = word_minus_one_le[where 'a=64]
lemmas word64_minus_one_le = word64_minus_one_le'[simplified]

lemma less_4_cases:
  "(x::word64) < 4 \<Longrightarrow> x=0 \<or> x=1 \<or> x=2 \<or> x=3"
  apply clarsimp
  apply (drule word_less_cases, erule disjE, simp, simp)+
  done

lemma ucast_le_ucast_8_64:
  "(ucast x \<le> (ucast y :: word64)) = (x \<le> (y :: 8 word))"
  by (simp add: ucast_le_ucast)

lemma eq_2_64_0:
  "(2 ^ 64 :: word64) = 0"
  by simp

lemmas mask_64_max_word  = max_word_mask [symmetric, where 'a=64, simplified]

lemma of_nat64_n_less_equal_power_2:
 "n < 64 \<Longrightarrow> ((of_nat n)::64 word) < 2 ^ n"
  by (rule of_nat_n_less_equal_power_2, clarsimp simp: word_size)

lemma unat_ucast_10_64 :
  fixes x :: "10 word"
  shows "unat (ucast x :: word64) = unat x"
  by transfer simp

lemma word64_bounds:
  "- (2 ^ (size (x :: word64) - 1)) = (-9223372036854775808 :: int)"
  "((2 ^ (size (x :: word64) - 1)) - 1) = (9223372036854775807 :: int)"
  "- (2 ^ (size (y :: 64 signed word) - 1)) = (-9223372036854775808 :: int)"
  "((2 ^ (size (y :: 64 signed word) - 1)) - 1) = (9223372036854775807 :: int)"
  by (simp_all add: word_size)

lemmas signed_arith_ineq_checks_to_eq_word64'
    = signed_arith_ineq_checks_to_eq[where 'a=64]
      signed_arith_ineq_checks_to_eq[where 'a="64 signed"]

lemmas signed_arith_ineq_checks_to_eq_word64
    = signed_arith_ineq_checks_to_eq_word64' [unfolded word64_bounds]

lemmas signed_mult_eq_checks64_to_64'
    = signed_mult_eq_checks_double_size[where 'a=64 and 'b=64]
      signed_mult_eq_checks_double_size[where 'a="64 signed" and 'b=64]

lemmas signed_mult_eq_checks64_to_64 = signed_mult_eq_checks64_to_64'[simplified]

lemmas sdiv_word64_max' = sdiv_word_max [where 'a=64] sdiv_word_max [where 'a="64 signed"]
lemmas sdiv_word64_max = sdiv_word64_max'[simplified word_size, simplified]

lemmas sdiv_word64_min' = sdiv_word_min [where 'a=64] sdiv_word_min [where 'a="64 signed"]
lemmas sdiv_word64_min = sdiv_word64_min' [simplified word_size, simplified]

lemmas sint64_of_int_eq' = sint_of_int_eq [where 'a=64]
lemmas sint64_of_int_eq = sint64_of_int_eq' [simplified]

lemma ucast_of_nats [simp]:
  "(ucast (of_nat x :: word64) :: sword64) = (of_nat x)"
  "(ucast (of_nat x :: word64) :: 16 sword) = (of_nat x)"
  "(ucast (of_nat x :: word64) :: 8 sword) = (of_nat x)"
  by (simp_all add: of_nat_take_bit take_bit_word_eq_self unsigned_of_nat)

lemmas signed_shift_guard_simpler_64'
    = power_strict_increasing_iff[where b="2 :: nat" and y=31]
lemmas signed_shift_guard_simpler_64 = signed_shift_guard_simpler_64'[simplified]

lemma word64_31_less:
  "31 < len_of TYPE (64 signed)" "31 > (0 :: nat)"
  "31 < len_of TYPE (64)" "31 > (0 :: nat)"
  by auto

lemmas signed_shift_guard_to_word_64
    = signed_shift_guard_to_word[OF word64_31_less(1-2)]
    signed_shift_guard_to_word[OF word64_31_less(3-4)]

lemma mask_step_down_64:
  \<open>\<exists>x. mask x = b\<close> if \<open>b && 1 = 1\<close>
    and \<open>\<exists>x. x < 64 \<and> mask x = b >> 1\<close> for b :: \<open>64word\<close>
proof -
  from \<open>b && 1 = 1\<close> have \<open>odd b\<close>
    by (auto simp add: mod_2_eq_odd and_one_eq)
  then have \<open>b mod 2 = 1\<close>
    using odd_iff_mod_2_eq_one by blast
  from \<open>\<exists>x. x < 64 \<and> mask x = b >> 1\<close> obtain x where \<open>x < 64\<close> \<open>mask x = b >> 1\<close> by blast
  then have \<open>mask x = b div 2\<close>
    using shiftr1_is_div_2 [of b] by simp
  with \<open>b mod 2 = 1\<close> have \<open>2 * mask x + 1 = 2 * (b div 2) + b mod 2\<close>
    by (simp only:)
  also have \<open>\<dots> = b\<close>
    by (simp add: mult_div_mod_eq)
  finally have \<open>2 * mask x + 1 = b\<close> .
  moreover have \<open>mask (Suc x) = 2 * mask x + (1 :: 'a::len word)\<close>
    by (simp add: mask_Suc_rec)
  ultimately show ?thesis
    by auto
qed

lemma unat_of_int_64:
  "\<lbrakk>i \<ge> 0; i \<le> 2 ^ 63\<rbrakk> \<Longrightarrow> (unat ((of_int i)::sword64)) = nat i"
  by (simp add: unsigned_of_int nat_take_bit_eq take_bit_nat_eq_self)

lemmas word_ctz_not_minus_1_64 = word_ctz_not_minus_1[where 'a=64, simplified]

lemma word64_and_max_simp:
  \<open>x AND 0xFFFFFFFFFFFFFFFF = x\<close> for x :: \<open>64 word\<close>
  using word_and_full_mask_simp [of x]
  by (simp add: numeral_eq_Suc mask_Suc_exp)

end

end
