(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

section "Lemmas for Word Length 64"

theory Word_Lemmas_64
imports
  Word_Lemmas_Prefix
  Word_Setup_64
begin

lemma ucast_8_64_inj:
  "inj (ucast ::  8 word \<Rightarrow> 64 word)"
  by (rule down_ucast_inj) (clarsimp simp: is_down_def target_size source_size)

lemma upto_2_helper:
  "{0..<2 :: 64 word} = {0, 1}"
  by (safe; simp) unat_arith

lemmas upper_bits_unset_is_l2p_64 = upper_bits_unset_is_l2p [where 'a=64, folded word_bits_def]
lemmas le_2p_upper_bits_64 = le_2p_upper_bits [where 'a=64, folded word_bits_def]
lemmas le2p_bits_unset_64 = le2p_bits_unset[where 'a=64, folded word_bits_def]

lemma word_bits_len_of:
  "len_of TYPE (64) = word_bits"
  by (simp add: word_bits_conv)

lemmas unat_power_lower64' = unat_power_lower[where 'a=64]
lemmas unat_power_lower64 [simp] = unat_power_lower64'[unfolded word_bits_len_of]

lemmas word64_less_sub_le' = word_less_sub_le[where 'a = 64]
lemmas word64_less_sub_le[simp] = word64_less_sub_le' [folded word_bits_def]

lemma word_bits_size:
  "size (w::word64) = word_bits"
  by (simp add: word_bits_def word_size)

lemmas word64_power_less_1' = word_power_less_1[where 'a = 64]
lemmas word64_power_less_1[simp] = word64_power_less_1'[folded word_bits_def]

lemma of_nat64_0:
  "\<lbrakk>of_nat n = (0::word64); n < 2 ^ word_bits\<rbrakk> \<Longrightarrow> n = 0"
  by (erule of_nat_0, simp add: word_bits_def)

lemma unat_mask_2_less_4:
  "unat (p && mask 2 :: word64) < 4"
  apply (rule unat_less_helper)
  apply (rule order_le_less_trans, rule word_and_le1)
  apply (simp add: mask_def)
  done

lemmas unat_of_nat64' = unat_of_nat_eq[where 'a=64]
lemmas unat_of_nat64 = unat_of_nat64'[unfolded word_bits_len_of]

lemmas word_power_nonzero_64 = word_power_nonzero [where 'a=64, folded word_bits_def]

lemmas unat_mult_simple = iffD1 [OF unat_mult_lem [where 'a = 64, unfolded word_bits_len_of]]

lemmas div_power_helper_64 = div_power_helper [where 'a=64, folded word_bits_def]

lemma n_less_word_bits:
  "(n < word_bits) = (n < 64)"
  by (simp add: word_bits_def)

lemmas of_nat_less_pow_64 = of_nat_power [where 'a=64, folded word_bits_def]

lemma lt_word_bits_lt_pow:
  "sz < word_bits \<Longrightarrow> sz < 2 ^ word_bits"
  by (simp add: word_bits_conv)

lemma unat_less_word_bits:
  fixes y :: word64
  shows "x < unat y \<Longrightarrow> x < 2 ^ word_bits"
  unfolding word_bits_def
  by (rule order_less_trans [OF _ unat_lt2p])

lemmas unat_mask_word64' = unat_mask[where 'a=64]
lemmas unat_mask_word64 = unat_mask_word64'[folded word_bits_def]

lemma unat_less_2p_word_bits:
  "unat (x :: 64 word) < 2 ^ word_bits"
  apply (simp only: word_bits_def)
  apply (rule unat_lt2p)
  done

lemma Suc_unat_mask_div:
  "Suc (unat (mask sz div word_size::word64)) = 2 ^ (min sz word_bits - 3)"
  apply (case_tac "sz < word_bits")
   apply (case_tac "3\<le>sz")
    apply (clarsimp simp: word_size_def word_bits_def min_def mask_def)
    apply (drule (2) Suc_div_unat_helper
           [where 'a=64 and sz=sz and us=3, simplified, symmetric])
   apply (simp add: not_le word_size_def word_bits_def)
   apply (case_tac sz, simp add: unat_word_ariths)
   apply (case_tac nat, simp add: unat_word_ariths
                                  unat_mask_word64 min_def word_bits_def)
   apply (case_tac nata, simp add: unat_word_ariths unat_mask_word64 word_bits_def)
   apply simp
  apply (simp add: unat_word_ariths
                   unat_mask_word64 min_def word_bits_def word_size_def)
  done

lemmas word64_minus_one_le' = word_minus_one_le[where 'a=64]
lemmas word64_minus_one_le = word64_minus_one_le'[simplified]

lemma ucast_not_helper:
  fixes a::word8
  assumes a: "a \<noteq> 0xFF"
  shows "ucast a \<noteq> (0xFF::word64)"
proof
  assume "ucast a = (0xFF::word64)"
  also
  have "(0xFF::word64) = ucast (0xFF::word8)" by simp
  finally
  show False using a
    apply -
    apply (drule up_ucast_inj, simp)
    apply simp
    done
qed

lemma less_4_cases:
  "(x::word64) < 4 \<Longrightarrow> x=0 \<or> x=1 \<or> x=2 \<or> x=3"
  apply clarsimp
  apply (drule word_less_cases, erule disjE, simp, simp)+
  done

lemma unat_ucast_8_64:
  fixes x :: "word8"
  shows "unat (ucast x :: word64) = unat x"
  unfolding ucast_def unat_def
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply (rule lt2p_lem)
   apply simp
  apply simp
  done

lemma if_then_1_else_0:
  "((if P then 1 else 0) = (0 :: word64)) = (\<not> P)"
  by simp

lemma if_then_0_else_1:
  "((if P then 0 else 1) = (0 :: word64)) = (P)"
  by simp

lemmas if_then_simps = if_then_0_else_1 if_then_1_else_0

lemma ucast_le_ucast_8_64:
  "(ucast x \<le> (ucast y :: word64)) = (x \<le> (y :: word8))"
  by (simp add: ucast_le_ucast)

lemma in_16_range:
  "0 \<in> S \<Longrightarrow> r \<in> (\<lambda>x. r + x * (16 :: word64)) ` S"
  "n - 1 \<in> S \<Longrightarrow> (r + (16 * n - 16)) \<in> (\<lambda>x :: word64. r + x * 16) ` S"
  by (clarsimp simp: image_def elim!: bexI[rotated])+

lemma eq_2_64_0:
  "(2 ^ 64 :: word64) = 0"
  by simp

lemma x_less_2_0_1:
  fixes x :: word64 shows
  "x < 2 \<Longrightarrow> x = 0 \<or> x = 1"
  by (rule x_less_2_0_1') auto

lemmas mask_64_max_word  = max_word_mask [symmetric, where 'a=64, simplified]

lemma of_nat64_n_less_equal_power_2:
 "n < 64 \<Longrightarrow> ((of_nat n)::64 word) < 2 ^ n"
  by (rule of_nat_n_less_equal_power_2, clarsimp simp: word_size)

lemma word_rsplit_0:
  "word_rsplit (0 :: word64) = [0, 0, 0, 0, 0, 0, 0, 0 :: word8]"
  apply (simp add: word_rsplit_def bin_rsplit_def Let_def)
  done

lemma unat_ucast_10_64 :
  fixes x :: "10 word"
  shows "unat (ucast x :: word64) = unat x"
  unfolding ucast_def unat_def
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply (rule lt2p_lem)
   apply simp
  apply simp
  done

lemma bool_mask [simp]:
  fixes x :: word64
  shows "(0 < x && 1) = (x && 1 = 1)"
  by (rule bool_mask') auto

lemma word64_bounds:
  "- (2 ^ (size (x :: word64) - 1)) = (-9223372036854775808 :: int)"
  "((2 ^ (size (x :: word64) - 1)) - 1) = (9223372036854775807 :: int)"
  "- (2 ^ (size (y :: 64 signed word) - 1)) = (-9223372036854775808 :: int)"
  "((2 ^ (size (y :: 64 signed word) - 1)) - 1) = (9223372036854775807 :: int)"
  by (simp_all add: word_size)

lemma word_ge_min:"sint (x::64 word) \<ge> -9223372036854775808"
  by (metis sint_ge word64_bounds(1) word_size)

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
  "(ucast (of_nat x :: word64) :: sword16) = (of_nat x)"
  "(ucast (of_nat x :: word64) :: sword8) = (of_nat x)"
  "(ucast (of_nat x :: word16) :: sword16) = (of_nat x)"
  "(ucast (of_nat x :: word16) :: sword8) = (of_nat x)"
  "(ucast (of_nat x :: word8) :: sword8) = (of_nat x)"
  by (auto simp: ucast_of_nat is_down)

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

lemma le_step_down_word_3:
  fixes x :: "64 word"
  shows "\<lbrakk>x \<le>  y; x \<noteq> y; y < 2 ^ 64 - 1\<rbrakk> \<Longrightarrow> x \<le> y - 1"
  by (rule le_step_down_word_2, assumption+)

lemma shiftr_1:
  "(x::word64) >> 1 = 0 \<Longrightarrow> x < 2"
  by word_bitwise clarsimp

lemma mask_step_down_64:
  "(b::64word) && 0x1 = (1::64word) \<Longrightarrow> (\<exists>x. x < 64 \<and> mask x = b >> 1) \<Longrightarrow> (\<exists>x. mask x = b)"
  apply clarsimp
  apply (rule_tac x="x + 1" in exI)
  apply (subgoal_tac "x \<le> 63")
   apply (erule le_step_down_nat, clarsimp simp:mask_def, word_bitwise, clarsimp+)+
   apply (clarsimp simp:mask_def, word_bitwise, clarsimp)
  apply clarsimp
  done

lemma unat_of_int_64:
  "\<lbrakk>i \<ge> 0; i \<le> 2 ^ 63\<rbrakk> \<Longrightarrow> (unat ((of_int i)::sword64)) = nat i"
  unfolding unat_def
  apply (subst eq_nat_nat_iff, clarsimp+)
  apply (simp add: word_of_int uint_word_of_int)
  done

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
  apply (subst down_cast_same[symmetric])
   apply (simp add:is_down)+
  done

lemma cast_down_s64: "(scast::64 sword \<Rightarrow> 32 word) = (ucast::64 sword \<Rightarrow> 32 word)"
  apply (subst down_cast_same[symmetric])
   apply (simp add:is_down)+
  done

end
