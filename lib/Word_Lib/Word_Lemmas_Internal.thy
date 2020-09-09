(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "L4V-Internal Word Lemmas"

text \<open>
  This is a holding area for Word utility lemmas that are too specific or unpolished for the
  AFP, but which are reusable enough to be collected together for the rest of L4V. New
  utility lemmas that only prove facts about words should be added here (in preference to being
  kept where they were first needed).
\<close>

theory Word_Lemmas_Internal
imports Word_Lemmas
begin

lemma signed_ge_zero_scast_eq_ucast:
 "0 <=s x \<Longrightarrow> scast x = ucast x"
  by (simp add: scast_eq_ucast word_sle_msb_le)

(* FIXME: move out of Word_Lib *)
lemma disjCI2:
  "(\<not> P \<Longrightarrow> Q) \<Longrightarrow> P \<or> Q"
  by blast

(* FIXME: move out of Word_Lib *)
lemma nat_diff_diff_le_lhs:
  "a + c - b \<le> d \<Longrightarrow> a - (b - c) \<le> (d :: nat)"
  by arith

lemma is_aligned_obvious_no_wrap':
  "\<lbrakk> is_aligned ptr sz; x = 2 ^ sz - 1 \<rbrakk>
   \<Longrightarrow> ptr \<le> ptr + x"
  by (fastforce simp: field_simps intro: is_aligned_no_overflow)

lemmas add_ge0_weak = add_increasing[where 'a=int and b=0]

lemmas aligned_sub_aligned = Aligned.aligned_sub_aligned'

lemma minus_minus_swap:
  "\<lbrakk> a \<le> c; b \<le> d; b \<le> a; d \<le> c ; (d :: nat) - b = c - a \<rbrakk>
   \<Longrightarrow> a - b = c - d"
  by arith

lemma minus_minus_swap':
  "\<lbrakk> c \<le> a; d \<le> b; b \<le> a; d \<le> c ; (b :: nat) - d = a - c \<rbrakk>
   \<Longrightarrow> a - b = c - d"
  by arith

lemmas word_le_mask_eq = le_mask_imp_and_mask

lemma int_and_leR:
  "0 \<le> b \<Longrightarrow> a AND b \<le> (b :: int)"
  by (rule AND_upper2)

lemma int_and_leL:
  "0 \<le> a \<Longrightarrow> a AND b \<le> (a :: int)"
  by (rule AND_upper1)

lemma if_then_1_else_0:
  "(if P then 1 else 0) = (0 :: 'a :: zero_neq_one) \<longleftrightarrow> \<not>P"
  by (simp split: if_split)

lemma if_then_0_else_1:
  "(if P then 0 else 1) = (0 :: 'a :: zero_neq_one) \<longleftrightarrow> P"
  by simp

lemmas if_then_simps = if_then_0_else_1 if_then_1_else_0

lemma createNewCaps_guard:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> unat x = c; b < 2 ^ LENGTH('a) \<rbrakk>
         \<Longrightarrow> (n < of_nat b \<and> n < x) = (n < of_nat (min (min b c) c))"
  apply (erule subst)
  apply (simp add: min.assoc)
  apply (rule iffI)
   apply (simp add: min_def word_less_nat_alt split: if_split)
  apply (simp add: min_def word_less_nat_alt not_le le_unat_uoi split: if_split_asm)
  by (simp add: of_nat_inverse)

lemma bits_2_subtract_ineq:
  "i < (n :: ('a :: len) word)
   \<Longrightarrow> 2 ^ bits + 2 ^ bits * unat (n - (1 + i)) = unat (n - i) * 2 ^ bits"
  apply (simp add: unat_sub word_minus_one_le_leq)
  apply (subst unatSuc)
   apply clarsimp
   apply unat_arith
  apply (simp only: mult_Suc_right[symmetric])
  apply (rule trans[OF mult.commute], rule arg_cong2[where f="(*)"], simp_all)
  apply (simp add: word_less_nat_alt)
  done

lemmas double_neg_mask = neg_mask_combine

lemmas int_unat = uint_nat[symmetric]

lemmas word_sub_mono3 = word_plus_mcs_4'

lemma shift_distinct_helper:
  "\<lbrakk> (x :: 'a :: len word) < bnd; y < bnd; x \<noteq> y; x << n = y << n; n < LENGTH('a);
     bnd - 1 \<le> 2 ^ (LENGTH('a) - n) - 1 \<rbrakk>
   \<Longrightarrow> P"
  apply (cases "n = 0")
   apply simp
  apply (drule word_plus_mono_right[where x=1])
   apply simp_all
   apply (subst word_le_sub1)
    apply (rule power_not_zero)
    apply simp
   apply simp
  apply (drule(1) order_less_le_trans)+
  apply (clarsimp simp: bang_eq)
  apply (drule_tac x="na + n" in spec)
  apply (simp add: nth_shiftl)
  apply (case_tac "na + n < LENGTH('a)", simp_all)
  apply safe
   apply (drule(1) nth_bounded)
    apply simp
   apply simp
  apply (drule(1) nth_bounded)
   apply simp
  apply simp
  done

lemma of_nat_shift_distinct_helper:
  "\<lbrakk> x < bnd; y < bnd; x \<noteq> y; (of_nat x :: 'a :: len word) << n = of_nat y << n;
     n < LENGTH('a); bnd \<le> 2 ^ (LENGTH('a) - n) \<rbrakk>
   \<Longrightarrow> P"
  apply (cases "n = 0")
   apply (simp add: word_unat.Abs_inject unats_def)
  apply (subgoal_tac "bnd < 2 ^ LENGTH('a)")
   apply (erule(1) shift_distinct_helper[rotated, rotated, rotated])
      defer
      apply (erule(1) of_nat_mono_maybe[rotated])
     apply (erule(1) of_nat_mono_maybe[rotated])
    apply (simp add: word_unat.Abs_inject unats_def)
   apply (erule order_le_less_trans)
   apply (rule power_strict_increasing)
    apply simp
   apply simp
  apply (simp add: word_less_nat_alt)
  apply (simp add: unat_minus_one [OF of_nat_neq_0]
                   word_unat.Abs_inverse unats_def)
  done

lemmas pre_helper2 = add_mult_in_mask_range[folded add_mask_fold]

lemma ptr_add_distinct_helper:
  "\<lbrakk> ptr_add (p :: 'a :: len word) (x * 2 ^ n) = ptr_add p (y * 2 ^ n); x \<noteq> y;
     x < bnd; y < bnd; n < LENGTH('a);
     bnd \<le> 2 ^ (LENGTH('a) - n) \<rbrakk>
   \<Longrightarrow> P"
  apply (clarsimp simp: ptr_add_def word_unat_power[symmetric]
                        shiftl_t2n[symmetric, simplified mult.commute])
  using of_nat_shift_distinct_helper
  by blast

lemma unat_sub_le_strg:
  "unat v \<le> v2 \<and> x \<le> v \<and> y \<le> v \<and> y < (x :: ('a :: len) word)
    \<longrightarrow> unat (x + (- 1 - y)) \<le> v2"
  apply clarsimp
  apply (erule order_trans[rotated])
  apply (fold word_le_nat_alt)
  apply (rule order_trans[rotated], assumption)
  apply (rule order_trans[rotated], rule word_sub_le[where y="y + 1"])
   apply (erule Word.inc_le)
  apply (simp add: field_simps)
  done

lemma multi_lessD:
  "\<lbrakk> (a :: nat) * b < c; 0 < a; 0 < b \<rbrakk>
   \<Longrightarrow> a < c \<and> b < c"
  by (cases a, simp_all,cases b,simp_all)

lemmas leq_high_bits_shiftr_low_bits_leq_bits =
  leq_high_bits_shiftr_low_bits_leq_bits_mask[unfolded mask_2pm1[of high_bits]]

lemmas unat_le_helper = word_unat_less_le

lemmas word_of_nat_plus = of_nat_add[where 'a="'a :: len word"]
lemmas word_of_nat_minus = of_nat_diff[where 'a="'a :: len word"]

(* this is a bit deceptive: 2 ^ len.. = 0, so really this is relying on 'word_n1_ge': ptr \<le> -1 *)
lemma word_up_bound:
  "(ptr :: 'a :: len word) \<le> 2 ^ LENGTH('a) - 1 "
  by auto

lemma base_length_minus_one_inequality:
  assumes foo: "wbase \<le> 2 ^ sz - 1"
    "1 \<le> (wlength :: ('a :: len) word)"
    "wlength \<le> 2 ^ sz - wbase"
    "sz < LENGTH ('a)"
  shows "wbase \<le> wbase + wlength - 1"
proof -

  note sz_less = power_strict_increasing[OF foo(4), where a=2]

  from foo have plus: "unat wbase + unat wlength < 2 ^ LENGTH('a)"
    apply -
    apply (rule order_le_less_trans[rotated], rule sz_less, simp)
    apply (simp add: unat_arith_simps split: if_split_asm)
    done

  from foo show ?thesis
   by (simp add: unat_arith_simps plus)
qed

lemmas from_bool_to_bool_and_1 = from_to_bool_last_bit[where x=r for r]

lemmas max_word_neq_0 = max_word_not_0

lemmas word_le_p2m1 = word_up_bound[where ptr=w for w]

lemma inj_ucast:
  "\<lbrakk> uc = ucast; is_up uc \<rbrakk>
   \<Longrightarrow> inj uc"
  using down_ucast_inj is_up_down by blast

lemma ucast_eq_0[OF refl]:
  "\<lbrakk> c = ucast; is_up c \<rbrakk>
   \<Longrightarrow> (c x = 0) = (x = 0)"
  by (metis uint_0_iff uint_up_ucast)

lemmas is_up_compose' = is_up_compose

lemma uint_is_up_compose:
  fixes uc :: "'a :: len word \<Rightarrow> 'b :: len word"
    and uc' :: "'b word \<Rightarrow> 'c :: len sword"
  assumes "uc = ucast"
    and "uc' = ucast"
    and " uuc = uc' \<circ> uc"
  shows "\<lbrakk> is_up uc; is_up uc' \<rbrakk>
         \<Longrightarrow> uint (uuc b) = uint b"
  apply (simp add: assms)
  apply (frule is_up_compose)
   apply (simp_all )
  apply (simp only: Word.uint_up_ucast)
  done

lemma uint_is_up_compose_pred:
  fixes uc :: "'a :: len word \<Rightarrow> 'b :: len word"
    and uc' :: "'b word \<Rightarrow> 'c :: len sword"
  assumes "uc = ucast" and "uc' = ucast" and " uuc = uc' \<circ> uc"
  shows "\<lbrakk> is_up uc; is_up uc' \<rbrakk>
         \<Longrightarrow> P (uint (uuc b)) \<longleftrightarrow> P( uint b)"
  apply (simp add: assms)
  apply (frule is_up_compose)
   apply (simp_all )
  apply (simp only: Word.uint_up_ucast)
 done

lemma is_down_up_sword:
  fixes uc :: "'a :: len word \<Rightarrow> 'b :: len sword"
  shows "\<lbrakk> uc = ucast; LENGTH('a) < LENGTH('b) \<rbrakk>
         \<Longrightarrow> is_up uc = (\<not> is_down uc)"
  by (simp add: target_size source_size  is_up_def is_down_def )

lemma is_not_down_compose:
  fixes uc :: "'a :: len word \<Rightarrow> 'b :: len word"
    and uc' :: "'b word \<Rightarrow> 'c :: len sword"
  shows "\<lbrakk> uc = ucast; uc' = ucast; LENGTH('a) < LENGTH('c) \<rbrakk>
         \<Longrightarrow> \<not> is_down (uc' \<circ> uc)"
  unfolding is_down_def
  by (simp add: Word.target_size Word.source_size)

lemma sint_ucast_uint:
  fixes uc :: "'a :: len word \<Rightarrow> 'b :: len word"
    and uc' :: "'b word \<Rightarrow> 'c :: len sword"
  assumes "uc = ucast" and " uc' = ucast" and "uuc=uc' \<circ> uc "
    and "LENGTH('a) < LENGTH('c signed)"
  shows "\<lbrakk> is_up uc; is_up uc'\<rbrakk>
         \<Longrightarrow> sint (uuc b) = uint b"
  apply (simp add: assms)
  apply (frule is_up_compose')
   apply simp_all
  apply (simp add: ucast_ucast_b)
  apply (rule sint_ucast_eq_uint)
  apply (insert assms)
  apply (simp add: is_down_def target_size source_size)
  done

lemma sint_ucast_uint_pred:
  fixes uc :: "'a :: len word \<Rightarrow> 'b :: len word"
    and uc' :: "'b word \<Rightarrow> 'c :: len sword"
    and uuc :: "'a word \<Rightarrow> 'c sword"
  assumes "uc = ucast" and " uc' = ucast" and "uuc=uc' \<circ> uc "
    and "LENGTH('a) < LENGTH('c )"
  shows "\<lbrakk> is_up uc; is_up uc' \<rbrakk>
         \<Longrightarrow> P (uint b) \<longleftrightarrow> P (sint (uuc b))"
  apply (simp add: assms )
  apply (insert sint_ucast_uint[where uc=uc and uc'=uc' and uuc=uuc and b = b])
  apply (simp add: assms)
 done

lemma sint_uucast_uint_uucast_pred:
  fixes uc :: "'a :: len word \<Rightarrow> 'b :: len word"
    and uc' :: "'b word \<Rightarrow> 'c :: len sword"
  assumes "uc = ucast" and " uc' = ucast" and "uuc=uc' \<circ> uc "
    and "LENGTH('a) < LENGTH('c )"
  shows "\<lbrakk> is_up uc; is_up uc' \<rbrakk>
         \<Longrightarrow> P (uint(uuc b)) \<longleftrightarrow> P (sint (uuc b))"
  apply (simp add: assms )
  apply (insert sint_ucast_uint[where uc=uc and uc'=uc' and uuc=uuc and b = b])
  apply (insert uint_is_up_compose_pred[where uc=uc and uc'=uc' and uuc=uuc and b=b])
  apply (simp add: assms uint_is_up_compose_pred)
 done

lemma unat_minus':
  fixes x :: "'a :: len word"
  shows "x \<noteq> 0 \<Longrightarrow> unat (-x) = 2 ^ LENGTH('a) - unat x"
  by (simp add: unat_minus wsst_TYs(3))

lemma word_nth_neq:
  "n < LENGTH('a) \<Longrightarrow> (~~ x :: 'a :: len word) !! n = (\<not> x !! n)"
  by (simp add: word_size word_ops_nth_size)

lemma word_wrap_of_natD:
  fixes x :: "'a :: len word"
  assumes wraps: "\<not> x \<le> x + of_nat n"
  shows   "\<exists>k. x + of_nat k = 0 \<and> k \<le> n"
proof -
  show ?thesis
  proof (rule exI [where x = "unat (- x)"], intro conjI)
    show "x + of_nat (unat (-x)) = 0"
      by simp
  next
    show "unat (-x) \<le> n"
    proof (subst unat_minus')
      from wraps show "x \<noteq> 0"
        by (rule contrapos_pn, simp add: not_le)
    next
      show "2 ^ LENGTH('a) - unat x \<le> n" using wraps
        apply (simp add: no_olen_add_nat le_diff_conv not_less)
        apply (erule order_trans)
        apply (simp add: unat_of_nat)
        done
    qed
  qed
qed

lemma two_bits_cases:
  "\<lbrakk> LENGTH('a) > 2; (x :: 'a :: len word) && 3 = 0 \<Longrightarrow> P; x && 3 = 1 \<Longrightarrow> P;
     x && 3 = 2 \<Longrightarrow> P; x && 3 = 3 \<Longrightarrow> P \<rbrakk>
   \<Longrightarrow> P"
  apply (frule and_mask_cases[where n=2 and x=x, simplified mask_def])
  using upt_conv_Cons by auto[1]

lemma zero_OR_eq:
  "y = 0 \<Longrightarrow> (x || y) = x"
  by simp

declare is_aligned_neg_mask_eq[simp]
declare is_aligned_neg_mask_weaken[simp]

lemmas mask_in_range = neg_mask_in_mask_range[folded add_mask_fold]
lemmas aligned_range_offset_mem = aligned_offset_in_range[folded add_mask_fold]
lemmas range_to_bl' = mask_range_to_bl'[folded add_mask_fold]
lemmas range_to_bl = mask_range_to_bl[folded add_mask_fold]
lemmas aligned_ranges_subset_or_disjoint = aligned_mask_range_cases[folded add_mask_fold]
lemmas aligned_range_offset_subset = aligned_mask_range_offset_subset[folded add_mask_fold]
lemmas aligned_diff = aligned_mask_diff[unfolded mask_2pm1]
lemmas aligned_ranges_subset_or_disjoint_coroll = aligned_mask_ranges_disjoint[folded add_mask_fold]
lemmas distinct_aligned_addresses_accumulate = aligned_mask_ranges_disjoint2[folded add_mask_fold]

lemmas bang_big = test_bit_over

lemma unat_and_mask_le:
  fixes x::"'a::len word"
  assumes "n < LENGTH('a)"
  shows "unat (x && mask n) \<le> 2^n"
proof -
  from assms
  have "2^n-1 \<le> (2^n :: 'a word)"
    using word_1_le_power word_le_imp_diff_le by blast
  then
  have "unat (x && mask n) \<le> unat (2^n::'a word)"
    apply (fold word_le_nat_alt)
    apply (rule order_trans, rule word_and_le1)
    apply (simp add: mask_def)
    done
  with assms
  show ?thesis by (simp add: unat_2tp_if)
qed

lemma sign_extend_less_mask_idem:
  "\<lbrakk> w \<le> mask n; n < size w \<rbrakk> \<Longrightarrow> sign_extend n w = w"
  apply (simp add: sign_extend_def le_mask_imp_and_mask)
  apply (simp add: le_mask_high_bits)
  done

lemma word_and_le:
  "a \<le> c \<Longrightarrow> (a :: 'a :: len word) && b \<le> c"
  by (subst word_bool_alg.conj.commute)
     (erule word_and_le')

lemma le_smaller_mask:
  "\<lbrakk> x \<le> mask n; n \<le> m \<rbrakk> \<Longrightarrow> x \<le> mask m"
  by (erule (1) order.trans[OF _ mask_mono])

(* The strange phrasing and ordering of assumptions is to support using this as a
   conditional simp rule when y is a concrete value. For example, as a simp rule,
   it will solve a goal of the form:
     UCAST(8 \<rightarrow> 32) x < 0x20 \<Longrightarrow> unat x < 32
   This is used in an obscure corner of SimplExportAndRefine. *)
lemma upcast_less_unat_less:
  assumes less: "UCAST('a \<rightarrow> 'b) x < UCAST('a \<rightarrow> 'b) (of_nat y)"
  assumes len: "LENGTH('a::len) \<le> LENGTH('b::len)"
  assumes bound: "y < 2 ^ LENGTH('a)"
  shows "unat x < y"
  by (rule unat_mono[OF less, simplified unat_ucast_up_simp[OF len] unat_of_nat_eq[OF bound]])

end
