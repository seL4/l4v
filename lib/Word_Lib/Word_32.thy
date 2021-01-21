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

type_synonym word32 = "32 word"
lemma len32: "len_of (x :: 32 itself) = 32" by simp

type_synonym sword32 = "32 sword"

type_synonym machine_word_len = 32
type_synonym machine_word = "machine_word_len word"

definition word_bits :: nat
where
  "word_bits = LENGTH(machine_word_len)"

text \<open>The following two are numerals so they can be used as nats and words.\<close>
definition word_size_bits :: "'a :: numeral"
where
  "word_size_bits = 2"

definition word_size :: "'a :: numeral"
where
  "word_size = 4"

lemma word_bits_conv[code]:
  "word_bits = 32"
  unfolding word_bits_def by simp

lemma word_size_word_size_bits:
  "(word_size::nat) = 2 ^ word_size_bits"
  unfolding word_size_def word_size_bits_def by simp

lemma word_bits_word_size_conv:
  "word_bits = word_size * 8"
  unfolding word_bits_def word_size_def by simp

lemma ucast_8_32_inj:
  "inj (ucast ::  8 word \<Rightarrow> 32 word)"
  by (rule down_ucast_inj) (clarsimp simp: is_down_def target_size source_size)

lemma upto_2_helper:
  "{0..<2 :: 32 word} = {0, 1}"
  by (safe; simp) unat_arith

lemmas upper_bits_unset_is_l2p_32 = upper_bits_unset_is_l2p [where 'a=32, folded word_bits_def]
lemmas le_2p_upper_bits_32 = le_2p_upper_bits [where 'a=32, folded word_bits_def]
lemmas le2p_bits_unset_32 = le2p_bits_unset[where 'a=32, folded word_bits_def]

lemma word_bits_len_of:
  "len_of TYPE (32) = word_bits"
  by (simp add: word_bits_conv)

lemmas unat_power_lower32' = unat_power_lower[where 'a=32]
lemmas unat_power_lower32 [simp] = unat_power_lower32'[unfolded word_bits_len_of]

lemmas word32_less_sub_le' = word_less_sub_le[where 'a = 32]
lemmas word32_less_sub_le[simp] = word32_less_sub_le' [folded word_bits_def]

lemma word_bits_size:
  "size (w::word32) = word_bits"
  by (simp add: word_bits_def word_size)

lemmas word32_power_less_1' = word_power_less_1[where 'a = 32]
lemmas word32_power_less_1[simp] = word32_power_less_1'[folded word_bits_def]

lemma of_nat32_0:
  "\<lbrakk>of_nat n = (0::word32); n < 2 ^ word_bits\<rbrakk> \<Longrightarrow> n = 0"
  by (erule of_nat_0, simp add: word_bits_def)

lemma unat_mask_2_less_4:
  "unat (p && mask 2 :: word32) < 4"
  apply (rule unat_less_helper)
  apply (rule order_le_less_trans, rule word_and_le1)
  apply (simp add: mask_eq)
  done

lemmas unat_of_nat32' = unat_of_nat_eq[where 'a=32]
lemmas unat_of_nat32 = unat_of_nat32'[unfolded word_bits_len_of]

lemmas word_power_nonzero_32 = word_power_nonzero [where 'a=32, folded word_bits_def]

lemmas unat_mult_simple = iffD1 [OF unat_mult_lem [where 'a = 32, unfolded word_bits_len_of]]

lemmas div_power_helper_32 = div_power_helper [where 'a=32, folded word_bits_def]

lemma n_less_word_bits:
  "(n < word_bits) = (n < 32)"
  by (simp add: word_bits_def)

lemmas of_nat_less_pow_32 = of_nat_power [where 'a=32, folded word_bits_def]

lemma lt_word_bits_lt_pow:
  "sz < word_bits \<Longrightarrow> sz < 2 ^ word_bits"
  by (simp add: word_bits_conv)

lemma unat_less_word_bits:
  fixes y :: word32
  shows "x < unat y \<Longrightarrow> x < 2 ^ word_bits"
  unfolding word_bits_def
  by (rule order_less_trans [OF _ unat_lt2p])

lemmas unat_mask_word32' = unat_mask[where 'a=32]
lemmas unat_mask_word32 = unat_mask_word32'[folded word_bits_def]

lemma unat_less_2p_word_bits:
  "unat (x :: 32 word) < 2 ^ word_bits"
  apply (simp only: word_bits_def)
  apply (rule unat_lt2p)
  done

lemma Suc_unat_mask_div:
  "Suc (unat (mask sz div word_size::word32)) = 2 ^ (min sz word_bits - 2)"
  apply (case_tac "sz < word_bits")
   apply (case_tac "2 \<le> sz")
    apply (clarsimp simp: word_size_def word_bits_def min_def mask_eq)
    apply (drule (2) Suc_div_unat_helper
           [where 'a=32 and sz=sz and us=2, simplified, symmetric])
   apply (simp add: not_le word_size_def word_bits_def)
   apply (case_tac sz, simp add: unat_word_ariths)
   apply (case_tac nat, simp add: unat_word_ariths
                                  unat_mask_word32 min_def word_bits_def)
   apply simp
  apply (simp add: unat_word_ariths
                   unat_mask_word32 min_def word_bits_def word_size_def)
  done

lemmas word32_minus_one_le' = word_minus_one_le[where 'a=32]
lemmas word32_minus_one_le = word32_minus_one_le'[simplified]

lemma ucast_not_helper:
  fixes a::"8 word"
  assumes a: "a \<noteq> 0xFF"
  shows "ucast a \<noteq> (0xFF::word32)"
proof
  assume "ucast a = (0xFF::word32)"
  also
  have "(0xFF::word32) = ucast (0xFF::8 word)" by simp
  finally
  show False using a
    apply -
    apply (drule up_ucast_inj, simp)
    apply simp
    done
qed

lemma less_4_cases:
  "(x::word32) < 4 \<Longrightarrow> x=0 \<or> x=1 \<or> x=2 \<or> x=3"
  apply clarsimp
  apply (drule word_less_cases, erule disjE, simp, simp)+
  done

lemma unat_ucast_8_32:
  fixes x :: "8 word"
  shows "unat (ucast x :: word32) = unat x"
  by transfer simp

lemma if_then_1_else_0:
  "((if P then 1 else 0) = (0 :: word32)) = (\<not> P)"
  by simp

lemma if_then_0_else_1:
  "((if P then 0 else 1) = (0 :: word32)) = (P)"
  by simp

lemmas if_then_simps = if_then_0_else_1 if_then_1_else_0

lemma ucast_le_ucast_8_32:
  "(ucast x \<le> (ucast y :: word32)) = (x \<le> (y :: 8 word))"
  by (simp add: ucast_le_ucast)

lemma in_16_range:
  "0 \<in> S \<Longrightarrow> r \<in> (\<lambda>x. r + x * (16 :: word32)) ` S"
  "n - 1 \<in> S \<Longrightarrow> (r + (16 * n - 16)) \<in> (\<lambda>x :: word32. r + x * 16) ` S"
  by (clarsimp simp: image_def elim!: bexI[rotated])+

lemma eq_2_32_0:
  "(2 ^ 32 :: word32) = 0"
  by simp

lemma x_less_2_0_1:
  fixes x :: word32 shows
  "x < 2 \<Longrightarrow> x = 0 \<or> x = 1"
  by (rule x_less_2_0_1') auto

lemmas mask_32_max_word  = max_word_mask [symmetric, where 'a=32, simplified]

lemma of_nat32_n_less_equal_power_2:
 "n < 32 \<Longrightarrow> ((of_nat n)::32 word) < 2 ^ n"
  by (rule of_nat_n_less_equal_power_2, clarsimp simp: word_size)

lemma word_rsplit_0:
  "word_rsplit (0 :: word32) = [0, 0, 0, 0 :: 8 word]"
  by (simp add: word_rsplit_def bin_rsplit_def)

lemma unat_ucast_10_32 :
  fixes x :: "10 word"
  shows "unat (ucast x :: word32) = unat x"
  by transfer simp

lemma bool_mask [simp]:
  fixes x :: word32
  shows "(0 < x && 1) = (x && 1 = 1)"
  by (rule bool_mask') auto

lemma word32_bounds:
  "- (2 ^ (size (x :: word32) - 1)) = (-2147483648 :: int)"
  "((2 ^ (size (x :: word32) - 1)) - 1) = (2147483647 :: int)"
  "- (2 ^ (size (y :: 32 signed word) - 1)) = (-2147483648 :: int)"
  "((2 ^ (size (y :: 32 signed word) - 1)) - 1) = (2147483647 :: int)"
  by (simp_all add: word_size)

lemma word_ge_min:"sint (x::32 word) \<ge> -2147483648"
  by (metis sint_ge word32_bounds(1) word_size)

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
  by (simp_all add: of_nat_take_bit take_bit_word_eq_self)

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

lemma le_step_down_word_3:
  fixes x :: "32 word"
  shows "\<lbrakk>x \<le>  y; x \<noteq> y; y < 2 ^ 32 - 1\<rbrakk> \<Longrightarrow> x \<le> y - 1"
  by (rule le_step_down_word_2, assumption+)

lemma shiftr_1:
  "(x::word32) >> 1 = 0 \<Longrightarrow> x < 2"
  by transfer (simp add: take_bit_drop_bit drop_bit_Suc)

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
  unfolding unat_eq_nat_uint
  apply (subst eq_nat_nat_iff)
    apply (auto simp add: take_bit_int_eq_self)
  done

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
