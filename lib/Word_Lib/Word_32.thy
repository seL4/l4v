(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Words of Length 32"

theory Word_32
  imports
    Word_Lemmas
    Word_Syntax
    Word_Names
    Rsplit
    More_Word_Operations
    Bitwise
begin

context
  includes bit_operations_syntax
begin

type_synonym word32 = "32 word"
lemma len32: "len_of (x :: 32 itself) = 32" by simp

type_synonym sword32 = "32 sword"

lemma ucast_8_32_inj:
  "inj (ucast ::  8 word \<Rightarrow> 32 word)"
  by (rule down_ucast_inj) (clarsimp simp: is_down_def target_size source_size)

lemmas unat_power_lower32' = unat_power_lower[where 'a=32]

lemmas word32_less_sub_le' = word_less_sub_le[where 'a = 32]

lemmas word32_power_less_1' = word_power_less_1[where 'a = 32]

lemmas unat_of_nat32' = unat_of_nat_eq[where 'a=32]

lemmas unat_mask_word32' = unat_mask[where 'a=32]

lemmas word32_minus_one_le' = word_minus_one_le[where 'a=32]
lemmas word32_minus_one_le = word32_minus_one_le'[simplified]

lemma unat_ucast_8_32:
  fixes x :: "8 word"
  shows "unat (ucast x :: word32) = unat x"
  by transfer simp

lemma ucast_le_ucast_8_32:
  "(ucast x \<le> (ucast y :: word32)) = (x \<le> (y :: 8 word))"
  by (simp add: ucast_le_ucast)

lemma eq_2_32_0:
  "(2 ^ 32 :: word32) = 0"
  by simp

lemmas mask_32_max_word  = max_word_mask [symmetric, where 'a=32, simplified]

lemma of_nat32_n_less_equal_power_2:
 "n < 32 \<Longrightarrow> ((of_nat n)::32 word) < 2 ^ n"
  by (rule of_nat_n_less_equal_power_2, clarsimp simp: word_size)

lemma unat_ucast_10_32 :
  fixes x :: "10 word"
  shows "unat (ucast x :: word32) = unat x"
  by transfer simp

lemma word32_bounds:
  "- (2 ^ (size (x :: word32) - 1)) = (-2147483648 :: int)"
  "((2 ^ (size (x :: word32) - 1)) - 1) = (2147483647 :: int)"
  "- (2 ^ (size (y :: 32 signed word) - 1)) = (-2147483648 :: int)"
  "((2 ^ (size (y :: 32 signed word) - 1)) - 1) = (2147483647 :: int)"
  by (simp_all add: word_size)

lemmas signed_arith_ineq_checks_to_eq_word32'
    = signed_arith_ineq_checks_to_eq[where 'a=32]
      signed_arith_ineq_checks_to_eq[where 'a="32 signed"]

lemmas signed_arith_ineq_checks_to_eq_word32
    = signed_arith_ineq_checks_to_eq_word32' [unfolded word32_bounds]

lemmas signed_mult_eq_checks32_to_64'
    = signed_mult_eq_checks_double_size[where 'a=32 and 'b=64]
      signed_mult_eq_checks_double_size[where 'a="32 signed" and 'b=64]

lemmas signed_mult_eq_checks32_to_64 = signed_mult_eq_checks32_to_64'[simplified]

lemmas sdiv_word32_max' = sdiv_word_max [where 'a=32] sdiv_word_max [where 'a="32 signed"]
lemmas sdiv_word32_max = sdiv_word32_max'[simplified word_size, simplified]

lemmas sdiv_word32_min' = sdiv_word_min [where 'a=32] sdiv_word_min [where 'a="32 signed"]
lemmas sdiv_word32_min = sdiv_word32_min' [simplified word_size, simplified]

lemmas sint32_of_int_eq' = sint_of_int_eq [where 'a=32]
lemmas sint32_of_int_eq = sint32_of_int_eq' [simplified]

lemma ucast_of_nats [simp]:
  "(ucast (of_nat x :: word32) :: sword32) = (of_nat x)"
  "(ucast (of_nat x :: word32) :: 16 sword) = (of_nat x)"
  "(ucast (of_nat x :: word32) :: 8 sword) = (of_nat x)"
  "(ucast (of_nat x :: 16 word) :: 16 sword) = (of_nat x)"
  "(ucast (of_nat x :: 16 word) :: 8 sword) = (of_nat x)"
  "(ucast (of_nat x :: 8 word) :: 8 sword) = (of_nat x)"
  by (simp_all add: of_nat_take_bit take_bit_word_eq_self unsigned_of_nat)

lemmas signed_shift_guard_simpler_32'
    = power_strict_increasing_iff[where b="2 :: nat" and y=31]
lemmas signed_shift_guard_simpler_32 = signed_shift_guard_simpler_32'[simplified]

lemma word32_31_less:
  "31 < len_of TYPE (32 signed)" "31 > (0 :: nat)"
  "31 < len_of TYPE (32)" "31 > (0 :: nat)"
  by auto

lemmas signed_shift_guard_to_word_32
    = signed_shift_guard_to_word[OF word32_31_less(1-2)]
    signed_shift_guard_to_word[OF word32_31_less(3-4)]

lemma has_zero_byte:
  "~~ (((((v::word32) && 0x7f7f7f7f) + 0x7f7f7f7f) || v) || 0x7f7f7f7f) \<noteq> 0
    \<Longrightarrow> v && 0xff000000 = 0 \<or> v && 0xff0000 = 0 \<or> v && 0xff00 = 0 \<or> v && 0xff = 0"
  by word_bitwise auto

lemma mask_step_down_32:
  \<open>\<exists>x. mask x = b\<close> if \<open>b && 1 = 1\<close>
    and \<open>\<exists>x. x < 32 \<and> mask x = b >> 1\<close> for b :: \<open>32word\<close>
proof -
  from \<open>b && 1 = 1\<close> have \<open>odd b\<close>
    by (auto simp add: mod_2_eq_odd and_one_eq)
  then have \<open>b mod 2 = 1\<close>
    using odd_iff_mod_2_eq_one by blast
  from \<open>\<exists>x. x < 32 \<and> mask x = b >> 1\<close> obtain x where \<open>x < 32\<close> \<open>mask x = b >> 1\<close> by blast
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

lemma unat_of_int_32:
  "\<lbrakk>i \<ge> 0; i \<le>2 ^ 31\<rbrakk> \<Longrightarrow> (unat ((of_int i)::sword32)) = nat i"
  by (simp add: unsigned_of_int nat_take_bit_eq take_bit_nat_eq_self)

lemmas word_ctz_not_minus_1_32 = word_ctz_not_minus_1[where 'a=32, simplified]

(* Helper for packing then unpacking a 64-bit variable. *)
lemma cast_chunk_assemble_id_64[simp]:
  "(((ucast ((ucast (x::64 word))::32 word))::64 word) || (((ucast ((ucast (x >> 32))::32 word))::64 word) << 32)) = x"
  by (simp add:cast_chunk_assemble_id)

(* Another variant of packing and unpacking a 64-bit variable. *)
lemma cast_chunk_assemble_id_64'[simp]:
  "(((ucast ((scast (x::64 word))::32 word))::64 word) || (((ucast ((scast (x >> 32))::32 word))::64 word) << 32)) = x"
  by (simp add:cast_chunk_scast_assemble_id)

(* Specialisations of down_cast_same for adding to local simpsets. *)
lemma cast_down_u64: "(scast::64 word \<Rightarrow> 32 word) = (ucast::64 word \<Rightarrow> 32 word)"
  by (subst down_cast_same[symmetric]; simp add:is_down)+

lemma cast_down_s64: "(scast::64 sword \<Rightarrow> 32 word) = (ucast::64 sword \<Rightarrow> 32 word)"
  by (subst down_cast_same[symmetric]; simp add:is_down)

lemma word32_and_max_simp:
  \<open>x AND 0xFFFFFFFF = x\<close> for x :: \<open>32 word\<close>
  using word_and_full_mask_simp [of x]
  by (simp add: numeral_eq_Suc mask_Suc_exp)

end

end
