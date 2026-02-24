(*
 * Copyright 2023, Proofcraft Pty Ltd
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
imports Word_Lemmas More_Word_Operations Many_More Word_Syntax Syntax_Bundles
begin

(* this bundle doesn't survive theory merges from HOL.Main, because these simp/split rules
   are added there, so it may need to be unbundled or included locally more than once
*)
bundle l4v_word_context
begin
  declare bit_0 [simp del]
  declare split_of_bool_asm [split del]
end

unbundle bit_operations_syntax
unbundle bit_projection_infix_syntax
unbundle l4v_word_context

(* Override default word enum code generation setup, so that "value" and "eval"
   work with quantification over word. *)
lemma [code]:
  \<open>Enum.enum_all P \<longleftrightarrow> list_all P enum\<close>
  \<open>Enum.enum_ex P \<longleftrightarrow> list_ex P enum\<close> for P :: \<open>'a::len word \<Rightarrow> bool\<close>
  by (auto simp: list_all_iff list_ex_iff)

lemmas shiftl_nat_def = push_bit_eq_mult[of _ a for a::nat, folded shiftl_def]
lemmas shiftr_nat_def = drop_bit_eq_div[of _ a for a::nat, folded shiftr_def]

declare bit_simps[simp]
lemmas bit_0_numeral[simp] = bit_0[of "numeral w" for w]

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
  by (metis (no_types) min_less_iff_conj nat_neq_iff unat_less_helper unat_ucast_less_no_overflow
                       unsigned_less word_unat.Rep_inverse)

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
  apply (fastforce simp: unat_of_nat_minus_1 word_less_nat_alt)
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
  apply (frule and_mask_cases[where n=2 and x=x, simplified mask_eq])
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
  "n < LENGTH('a) \<Longrightarrow> unat (x && mask n) \<le> 2^n" for x::"'a::len word"
  by (simp add: and_mask_less' order_less_imp_le unat_less_power)

lemma sign_extend_less_mask_idem:
  "\<lbrakk> w \<le> mask n; n < size w \<rbrakk> \<Longrightarrow> sign_extend n w = w"
  by (simp add: sign_extend_def le_mask_imp_and_mask le_mask_high_bits)

lemma word_and_le:
  "a \<le> c \<Longrightarrow> (a :: 'a :: len word) && b \<le> c"
  by (subst and.commute) (erule word_and_le')

lemma le_smaller_mask:
  "\<lbrakk> x \<le> mask n; n \<le> m \<rbrakk> \<Longrightarrow> x \<le> mask m" for x :: "'a::len word"
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

lemma word_ctz_max:
  "word_ctz w \<le> size w"
  unfolding word_ctz_def
  by (rule order_trans[OF List.length_takeWhile_le], clarsimp simp: word_size)

lemma scast_of_nat_small:
  "x < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> scast (of_nat x :: 'a :: len word) = (of_nat x :: 'b :: len word)"
  apply transfer
  apply simp
  by (metis One_nat_def id_apply int_eq_sint of_int_eq_id signed_of_nat)

lemmas casts_of_nat_small = ucast_of_nat_small scast_of_nat_small

\<comment>\<open>The conditions under which `takeWhile P xs = take n xs` and `dropWhile P xs = drop n xs`\<close>
definition list_while_len where
  "list_while_len P n xs \<equiv> (\<forall>i. i < n \<longrightarrow> i < length xs \<longrightarrow> P (xs ! i))
                            \<and> (n < length xs \<longrightarrow> \<not> P (xs ! n))"

lemma list_while_len_iff_takeWhile_eq_take:
  "list_while_len P n xs \<longleftrightarrow> takeWhile P xs = take n xs"
  unfolding list_while_len_def
  apply (rule iffI[OF takeWhile_eq_take_P_nth], simp+)
  apply (intro conjI allI impI)
   apply (rule takeWhile_take_has_property_nth, clarsimp)
  apply (drule_tac f=length in arg_cong, simp)
  apply (induct xs arbitrary: n; clarsimp split: if_splits)
  done

lemma list_while_len_exists:
  "\<exists>n. list_while_len P n xs"
  apply (induction xs; simp add: list_while_len_def)
  apply (rename_tac x xs)
  apply (erule exE)
  apply (case_tac "P x")
   apply (rule_tac x="Suc n" in exI, clarsimp)
   apply (case_tac i; simp)
  apply (rule_tac x=0 in exI, simp)
  done

lemma takeWhile_truncate:
  "length (takeWhile P xs) \<le> m
   \<Longrightarrow> takeWhile P (take m xs) = takeWhile P xs"
  apply (cut_tac list_while_len_exists[where P=P and xs=xs], clarsimp)
  apply (case_tac "n \<le> m")
   apply (subgoal_tac "list_while_len P n (take m xs)")
    apply(simp add: list_while_len_iff_takeWhile_eq_take)
   apply (clarsimp simp: list_while_len_def)
  apply (simp add: list_while_len_iff_takeWhile_eq_take)
  done

lemma word_clz_shiftr_1:
  fixes z::"'a::len word"
  assumes wordsize: "1 < LENGTH('a)"
  shows "z \<noteq> 0 \<Longrightarrow> word_clz (z >> 1) = word_clz z + 1"
  supply word_size [simp]
  apply (clarsimp simp: word_clz_def)
  using wordsize apply (subst bl_shiftr, simp)
  apply (subst takeWhile_append2; simp add: wordsize)
  apply (subst takeWhile_truncate)
  using word_clz_nonzero_max[where w=z]
   apply (clarsimp simp: word_clz_def)
   apply simp+
  done

lemma shiftr_Suc:
  fixes x::"'a::len word"
  shows "x >> (Suc n) = x >> n >> 1"
  by (clarsimp simp: shiftr_shiftr)

lemma word_clz_shiftr:
  fixes z :: "'a::len word"
  shows "n < LENGTH('a) \<Longrightarrow> mask n < z \<Longrightarrow> word_clz (z >> n) = word_clz z + n"
  apply (simp add: le_mask_iff Not_eq_iff[THEN iffD2, OF le_mask_iff, simplified not_le]
                   word_neq_0_conv)
  apply (induction n; simp)
  apply (subgoal_tac "0 < z >> n")
   apply (subst shiftr_Suc)
   apply (subst word_clz_shiftr_1; simp)
  apply (clarsimp simp: word_less_nat_alt shiftr_div_2n' div_mult2_eq)
  apply (case_tac "unat z div 2 ^ n = 0"; simp)
  apply (clarsimp simp: div_eq_0_iff)
  done

lemma mask_to_bl_exists_True:
  "x && mask n \<noteq> 0 \<Longrightarrow> \<exists>m. (rev (to_bl x)) ! m \<and> m < n"
  apply (subgoal_tac "\<not>(\<forall>m. m < n \<longrightarrow> \<not>(rev (to_bl x)) ! m)", fastforce)
  apply (intro notI)
  apply (subgoal_tac "x && mask n = 0", clarsimp)
  apply (clarsimp simp: eq_zero_set_bl in_set_conv_nth)
  apply (subst (asm) to_bl_nth, clarsimp simp: word_size)
  apply (clarsimp simp: word_size)
  by (meson nth_mask test_bit_bl word_and_nth)

lemma word_ctz_shiftr_1:
  fixes z::"'a::len word"
  assumes wordsize: "1 < LENGTH('a)"
  shows "z \<noteq> 0 \<Longrightarrow> 1 \<le> word_ctz z \<Longrightarrow> word_ctz (z >> 1) = word_ctz z - 1"
  supply word_size [simp]
  apply (clarsimp simp: word_ctz_def)
  using wordsize apply (subst bl_shiftr, simp)
  apply (simp add: rev_take )
  apply (subgoal_tac
         "length (takeWhile Not (rev (to_bl z))) - Suc 0
          = length (takeWhile Not (take 1 (rev (to_bl z)) @ drop 1 (rev (to_bl z)))) - Suc 0")
   apply (subst (asm) takeWhile_append2)
    apply clarsimp
    apply (case_tac "rev (to_bl z)"; simp)
   apply clarsimp
   apply (subgoal_tac "\<exists>m. (rev (to_bl z)) ! m \<and> m < LENGTH('a)", clarsimp)
    apply (case_tac m)
     apply (case_tac "rev (to_bl z)"; simp)
    apply (subst takeWhile_append1, subst in_set_conv_nth)
      apply (rule_tac x=nat in exI)
      apply (intro conjI)
       apply (clarsimp simp: wordsize)
       using wordsize apply linarith
      apply (rule refl, clarsimp)
    apply simp
   apply (rule mask_to_bl_exists_True, simp)
  apply simp
  done

lemma word_ctz_bound_below_helper:
  fixes x :: "'a::len word"
  assumes sz: "n \<le> LENGTH('a)"
  shows "x && mask n = 0
         \<Longrightarrow> to_bl x = (take (LENGTH('a) - n) (to_bl x) @ replicate n False)"
  apply (subgoal_tac "replicate n False = drop (LENGTH('a) - n) (to_bl x)")
   apply (subgoal_tac "True \<notin> set (drop (LENGTH('a) - n) (to_bl x))")
    apply (drule list_of_false, clarsimp simp: sz)
   apply (drule_tac sym[where t="drop n x" for n x], clarsimp)
  apply (rule sym)
  apply (rule is_aligned_drop; clarsimp simp: is_aligned_mask sz)
  done

lemma word_ctz_bound_below:
  fixes x :: "'a::len word"
  assumes sz[simp]: "n \<le> LENGTH('a)"
  shows "x && mask n = 0 \<Longrightarrow> n \<le> word_ctz x"
  apply (clarsimp simp: word_ctz_def)
  apply (subst word_ctz_bound_below_helper[OF sz]; simp)
  apply (subst takeWhile_append2; clarsimp)
  done

lemma word_ctz_bound_above:
  fixes x :: "'a::len word"
  shows "x && mask n \<noteq> 0 \<Longrightarrow> word_ctz x < n"
  apply (cases "n \<le> LENGTH('a)")
   apply (frule mask_to_bl_exists_True, clarsimp)
   apply (clarsimp simp: word_ctz_def)
   apply (subgoal_tac "m < length ((rev (to_bl x)))")
    apply (subst id_take_nth_drop[where xs="rev (to_bl x)"], assumption)
    apply (subst takeWhile_tail, simp)
    apply (rule order.strict_trans1)
     apply (rule List.length_takeWhile_le)
    apply simp
   apply (erule order.strict_trans2, clarsimp)
  apply (simp add: not_le)
  apply (erule le_less_trans[OF word_ctz_max, simplified word_size])
  done

lemma word_ctz_shiftr:
  fixes z::"'a::len word"
  assumes nz: "z \<noteq> 0"
  shows "n < LENGTH('a) \<Longrightarrow> n \<le> word_ctz z \<Longrightarrow> word_ctz (z >> n) = word_ctz z - n"
  apply (induction n; simp)
  apply (subst shiftr_Suc)
  apply (subst word_ctz_shiftr_1, simp)
    apply clarsimp
    apply (subgoal_tac "word_ctz z < n", clarsimp)
    apply (rule word_ctz_bound_above, clarsimp simp: word_size)
    apply (subst (asm) and_mask_eq_iff_shiftr_0[symmetric], clarsimp simp: nz)
   apply (rule word_ctz_bound_below, clarsimp simp: word_size)
   apply (rule mask_zero)
   apply (rule is_aligned_shiftr, simp add: is_aligned_mask)
   apply (case_tac "z && mask (Suc n) = 0", simp)
   apply (frule word_ctz_bound_above[rotated]; clarsimp simp: word_size)
  apply simp
  done

\<comment> \<open>Useful for solving goals of the form `(w::32 word) <= 0xFFFFFFFF` by simplification\<close>
lemma word_less_max_simp:
  fixes w :: "'a::len word"
  assumes "max_w = -1"
  shows "w \<le> max_w"
  unfolding assms by simp

lemma word_and_mask_word_ctz_zero:
  assumes "l = word_ctz w"
  shows "w && mask l = 0"
  unfolding word_ctz_def assms
  apply (word_eqI)
  apply (drule takeWhile_take_has_property_nth)
  apply (simp add: test_bit_bl)
  done

lemma word_ctz_len_word_and_mask_zero:
  fixes w :: "'a::len word"
  shows "word_ctz w = LENGTH('a) \<Longrightarrow> w = 0"
  by (drule sym, drule word_and_mask_word_ctz_zero, simp)

lemma word_le_1:
  fixes w :: "'a::len word"
  shows "w \<le> 1 \<longleftrightarrow> w = 0 \<or> w = 1"
  using dual_order.antisym lt1_neq0 word_zero_le by blast

lemma less_ucast_ucast_less':
  "x < UCAST('b \<rightarrow> 'a) y \<Longrightarrow> UCAST('a \<rightarrow> 'b) x < y"
  for x :: "'a::len word" and y :: "'b::len word"
  by (clarsimp simp: order.strict_iff_order dual_order.antisym le_ucast_ucast_le)

lemma ucast_up_less_bounded_implies_less_ucast_down':
  assumes len: "LENGTH('a::len) < LENGTH('b::len)"
  assumes bound: "y < 2 ^ LENGTH('a)"
  assumes less: "UCAST('a \<rightarrow> 'b) x < y"
  shows "x < UCAST('b \<rightarrow> 'a) y"
  apply (rule le_less_trans[OF _ ucast_mono[OF less bound]])
  using len by (simp add: is_down ucast_down_ucast_id)

lemma ucast_up_less_bounded_iff_less_ucast_down':
  assumes len: "LENGTH('a::len) < LENGTH('b::len)"
  assumes bound: "y < 2 ^ LENGTH('a)"
  shows "UCAST('a \<rightarrow> 'b) x < y \<longleftrightarrow> x < UCAST('b \<rightarrow> 'a) y"
  apply (rule iffI)
   prefer 2
   apply (simp add: less_ucast_ucast_less')
  using assms by (rule ucast_up_less_bounded_implies_less_ucast_down')

lemma word_of_int_word_of_nat_eqD:
  "\<lbrakk> word_of_int x = (word_of_nat y :: 'a :: len word); 0 \<le> x; x < 2^LENGTH('a); y < 2^LENGTH('a) \<rbrakk>
   \<Longrightarrow> nat x = y"
  by (metis nat_eq_numeral_power_cancel_iff of_nat_inj word_of_int_nat zless2p zless_nat_conj)

lemma ucast_down_0:
  "\<lbrakk> UCAST('a::len \<rightarrow> 'b::len) x = 0; unat x < 2^LENGTH('b) \<rbrakk> \<Longrightarrow> x = 0"
  by (metis Word.of_nat_unat unat_0 unat_eq_of_nat word_unat_eq_iff)

lemma uint_minus_1_eq:
  \<open>uint (- 1 :: 'a word) = 2 ^ LENGTH('a::len) - 1\<close>
  by transfer (simp add: mask_eq_exp_minus_1)

lemma FF_eq_minus_1:
  \<open>0xFF = (- 1 :: 8 word)\<close>
  by simp

lemmas shiftl_t2n' = shiftl_eq_mult[where x="w::'a::len word" for w]


(* candidates for moving to AFP Word_Lib: *)

lemma word_mask_shift_eqI:
  "\<lbrakk> x && mask n = y && mask n; x >> n = y >> n \<rbrakk> \<Longrightarrow> x = y"
  apply (subst mask_or_not_mask[of x n, symmetric])
  apply (subst mask_or_not_mask[of y n, symmetric])
  apply (rule arg_cong2[where f="(OR)"]; blast intro: shiftr_eq_neg_mask_eq)
  done

lemma mask_shiftr_mask_eq:
  "m \<le> m' + n \<Longrightarrow> (w && mask m >> n) && mask m' = w && mask m >> n" for w :: "'a::len word"
  by word_eqI_solve

lemma mask_split_aligned:
  assumes len: "m \<le> a + len_of TYPE('a)"
  assumes align: "is_aligned p a"
  shows "(p && ~~ mask m) + (ucast ((ucast (p && mask m >> a))::'a::len word) << a) = p"
  apply (insert align[simplified is_aligned_nth])
  apply (subst word_plus_and_or_coroll; word_eqI)
  apply (rule iffI)
   apply (erule disjE; clarsimp)
  apply (case_tac "n < m"; case_tac "n < a")
  using len by auto

lemma mask_split_aligned_neg:
  fixes x :: "'a::len word"
  fixes p :: "'b::len word"
  assumes len: "a + len_of TYPE('a) \<le> len_of TYPE('b)"
               "m = a + len_of TYPE('a)"
  assumes x: "x \<noteq> ucast (p && mask m >> a)"
  shows "(p && ~~ mask m) + (ucast x << a) = p \<Longrightarrow> False"
  apply (subst (asm) word_plus_and_or_coroll)
   apply word_eqI
   using len apply linarith
  apply (insert x)
  apply (erule notE)
  apply word_eqI
  subgoal for n
    using len
    apply (clarsimp)
    apply (drule_tac x="n + a" in spec)
    by (clarsimp simp: add.commute)
  done

lemma mask_alignment_ugliness:
  "\<lbrakk> x \<noteq> x + z && ~~ mask m;
     is_aligned (x + z && ~~ mask m) m;
     is_aligned x m;
     \<forall>n \<ge> m. \<not>z !! n\<rbrakk>
  \<Longrightarrow> False"
  apply (erule notE)
  apply (subst word_plus_and_or_coroll; word_eqI)
   apply (meson linorder_not_le)
  by (auto simp: le_def)

lemma word_and_mask_shift_eq_0:
  "n \<le> m \<Longrightarrow> x && mask n >> m = 0"
  by word_eqI

lemma word_mask_and_neg_shift_eq_0:
  "n < m \<Longrightarrow> - (1 << m) && mask n = 0"
  by (metis NOT_mask_AND_mask add.inverse_neutral leD less_imp_le mask_AND_NOT_mask mask_eqs(10)
            shiftl_1 t2n_mask_eq_if)

lemma aligned_mask_plus_bounded:
  "\<lbrakk> is_aligned x m; m < n; n < LENGTH('a) \<rbrakk> \<Longrightarrow> (x && mask n) + 2^m \<le> 2^n" for x :: "'a::len word"
  by (metis add_mask_fold and_mask_less' is_aligned_add_step_le is_aligned_after_mask is_aligned_mask
            leD leI order_less_imp_le t2n_mask_eq_if word_less_sub_1)

lemma aligned_mask_le_mask_minus:
  "\<lbrakk> is_aligned x m; m \<le> n; n < LENGTH('a)\<rbrakk> \<Longrightarrow> x && mask n \<le> mask n - mask m" for x :: "'a::len word"
  by (metis and_mask_less' is_aligned_after_mask is_aligned_neg_mask_eq'
           mask_2pm1 mask_sub neg_mask_mono_le word_less_sub_le)

lemma shiftr_anti_mono:
  "m \<le> n \<Longrightarrow> w >> n \<le> w >> m" for w :: "'a::len word"
  apply transfer
  apply (simp add: take_bit_drop_bit)
  apply (simp add: drop_bit_eq_div zdiv_mono2)
  done

lemma mask_shift_neg_mask_eq:
  "\<lbrakk> n' \<le> n; x \<le> mask (m+n') \<rbrakk> \<Longrightarrow> (x && ~~ mask n) && (mask m << n') = x && ~~ mask n"
  by word_eqI_solve

lemma from_bool_inj[simp]:
  "(from_bool x = from_bool y) = (x = y)"
  unfolding from_bool_def
  by (auto split: bool.splits)

lemma word_le_1_and_idem:
  "w \<le> 1 \<Longrightarrow> w AND 1 = w" for w :: "_ word"
  by (metis word_bw_same(1) word_le_1 word_log_esimps(7))

lemma from_to_bool_le_1_idem:
  "w \<le> 1 \<Longrightarrow> from_bool (to_bool w) = w"
  apply (subst word_le_1_and_idem[symmetric], assumption)
  apply (simp add: from_to_bool_last_bit)
  apply (simp add: word_le_1_and_idem)
  done

lemma and_1_0_not_bit_0:
  "(w && 1 = 0) = (\<not> (w::'a::len word) !! 0)"
  using to_bool_and_1[simplified to_bool_def, where x=w]
  by auto

lemma unat_scast_up:
  "\<lbrakk> LENGTH('a) \<le> LENGTH('b); 0 \<le> sint x \<rbrakk> \<Longrightarrow>unat (scast x::'b::len word) = unat x"
  for x :: "'a :: len  word"
  apply (simp flip: bit_last_iff not_less)
  apply word_eqI
  apply (clarsimp simp: min_def split: if_splits)
  apply (rule conjI; clarsimp)
   apply (drule test_bit_lenD)
   apply clarsimp
   apply (metis le_antisym nat_le_Suc_less_imp)
  apply fastforce
  done

lemma unat_uint_less:
  "unat x < nat i \<Longrightarrow> uint x < i" for x :: "'a :: len word"
  by (simp add: zless_nat_eq_int_zless)

lemma sint_ge_zero_uint:
  "uint x < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> sint (x :: 'a :: len word) \<ge> 0"
  by (simp add: sint_eq_uint_2pl word_2p_lem wsst_TYs(3))

lemma sint_ge_zero_unat:
  "unat x < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> sint (x :: 'a :: len word) \<ge> 0"
  by (fastforce intro: sint_ge_zero_uint unat_uint_less simp: nat_power_eq)

lemma mask_shiftl_le_mask:
  "mask n << m \<le> (mask (n+m) :: 'a::len word)"
  by (subst add.commute)
     (rule leq_high_bits_shiftr_low_bits_leq_bits, simp)

(* This is more useful for getting rid of a downcast *)
lemma unat_ucast_unat_id:
  "unat x < 2 ^ LENGTH('b) \<Longrightarrow> unat (UCAST('a::len \<rightarrow> 'b::len) x) = unat x"
  by (simp add: unat_eq_of_nat)

lemma ucast_up_preserves_gt0:
  "\<lbrakk> 0 < x; LENGTH('a) < LENGTH('b) \<rbrakk> \<Longrightarrow> 0 < (ucast x :: 'b::len word)" for x :: "'a::len word"
  by (metis ucast_0 ucast_less_ucast_weak)

lemma ucast_up_preserves_not0:
  "\<lbrakk> x \<noteq> 0; LENGTH('a) < LENGTH('b::len) \<rbrakk> \<Longrightarrow> (ucast x :: 'b::len word) \<noteq> 0"
  for x :: "'a::len word"
  by (metis ucast_0 ucast_ucast_id)

lemma unat_le_fold:
  "n < 2 ^ LENGTH('a) \<Longrightarrow> (unat x \<le> n) = (x \<le> of_nat n)" for x::"'a::len word"
  by (simp add: word_le_nat_alt unat_of_nat_eq)

lemma ucast_and_mask_drop:
  "LENGTH('a) \<le> n \<Longrightarrow> (ucast w :: 'b::len word) && mask n = ucast w" for w::"'a::len word"
  by word_eqI (fastforce dest: test_bit_lenD)

lemma add_mask_ignore:
  "x && mask n = 0 \<Longrightarrow> v + x && mask n = v && mask n"
  by (metis add_0_right mask_eqs(2))

lemma word_ctz_upcast_id:
  "\<lbrakk> x \<noteq> 0; is_up (ucast::'a word \<Rightarrow>'b word) \<rbrakk> \<Longrightarrow>
  word_ctz (ucast x :: 'b::len word) = word_ctz x" for x :: "'a::len word"
  unfolding word_ctz_def
  by (simp add: ucast_up_app[where n="LENGTH('b) - LENGTH('a)"]
                source_size_def target_size_def is_up_def eq_zero_set_bl)

lemma ucast_ucast_mask_id:
  "\<lbrakk> LENGTH('b::len) < LENGTH('a); n = LENGTH('b) \<rbrakk> \<Longrightarrow>
   UCAST('b \<rightarrow> 'a) (UCAST('a \<rightarrow> 'b) (x && mask n)) = x && mask n" for x :: "'a::len word"
  by (simp add: ucast_ucast_len[OF eq_mask_less])

lemma msb_le_mono:
  fixes v w :: "'a::len word"
  shows "v \<le> w \<Longrightarrow> msb v \<Longrightarrow> msb w"
  by (simp add: msb_big)

lemma neg_msb_le_mono:
  fixes v w :: "'a::len word"
  shows "v \<le> w \<Longrightarrow> \<not> msb w \<Longrightarrow> \<not> msb v"
  by (simp add: msb_big)

lemmas msb_less_mono = msb_le_mono[OF less_imp_le]
lemmas neg_msb_less_mono = neg_msb_le_mono[OF less_imp_le]

lemma word_sless_iff_less:
  "\<lbrakk> \<not> msb v; \<not> msb w \<rbrakk> \<Longrightarrow> v <s w \<longleftrightarrow> v < w"
  by (simp add: word_sless_alt sint_eq_uint word_less_alt)

lemmas word_sless_imp_less = word_sless_iff_less[THEN iffD1, rotated 2]
lemmas word_less_imp_sless = word_sless_iff_less[THEN iffD2, rotated 2]

lemma to_bool_if:
  "(if w \<noteq> 0 then 1 else 0) = (if to_bool w then 1 else 0)"
  by (auto simp: to_bool_def)

lemma word_sle_iff_le:
  "\<lbrakk> \<not> msb v; \<not> msb w \<rbrakk> \<Longrightarrow> v <=s w \<longleftrightarrow> v \<le> w"
  apply (simp add: word_sle_def sint_eq_uint word_le_def)
  by (metis sint_eq_uint word_sle.rep_eq word_sle_eq)

lemmas word_sle_imp_le = word_sle_iff_le[THEN iffD1, rotated 2]
lemmas word_le_imp_sle = word_sle_iff_le[THEN iffD2, rotated 2]

lemma word_upcast_shiftr:
  assumes "LENGTH('a::len) \<le> LENGTH('b::len)"
  shows "UCAST('a \<rightarrow> 'b) (w >> n) = UCAST('a \<rightarrow> 'b) w >> n"
  apply (intro word_eqI impI iffI; clarsimp simp: word_size nth_shiftr nth_ucast)
  apply (drule test_bit_size)
  using assms by (simp add: word_size)

lemma word_upcast_neg_msb:
  "LENGTH('a::len) < LENGTH('b::len) \<Longrightarrow> \<not> msb (UCAST('a \<rightarrow> 'b) w)"
  unfolding ucast_eq msb_word_of_int
  by clarsimp (metis Suc_pred bit_imp_le_length lens_gt_0(2) not_less_eq)

lemma word_upcast_0_sle:
  "LENGTH('a::len) < LENGTH('b::len) \<Longrightarrow> 0 <=s UCAST('a \<rightarrow> 'b) w"
  by (simp add: word_sle_iff_le[OF word_msb_0 word_upcast_neg_msb])

lemma scast_ucast_up_eq_ucast:
  assumes "LENGTH('a::len) < LENGTH('b::len)"
  shows "SCAST('b \<rightarrow> 'c) (UCAST('a \<rightarrow> 'b) w) = UCAST('a \<rightarrow> 'c::len) w"
  using assms
  apply (subst scast_eq_ucast; simp)
  apply (simp only: ucast_eq msb_word_of_int)
   apply (metis bin_nth_uint_imp decr_length_less_iff numeral_nat(7) verit_comp_simplify1(3))
  by (metis less_or_eq_imp_le ucast_nat_def unat_ucast_up_simp)

lemmas not_max_word_iff_less = word_order.not_eq_extremum

lemma ucast_increment:
  assumes "w \<noteq> max_word"
  shows "UCAST('a::len \<rightarrow> 'b::len) w + 1 = UCAST('a \<rightarrow> 'b) (w + 1)"
  apply (cases "LENGTH('b) \<le> LENGTH('a)")
   apply (simp add: ucast_down_add is_down)
  apply (subgoal_tac "uint w + 1 < 2 ^ LENGTH('a)")
   apply (subgoal_tac "uint w + 1 < 2 ^ LENGTH('b)")
    apply (subst word_uint_eq_iff)
    apply (simp add: uint_arith_simps uint_up_ucast is_up)
   apply (erule less_trans, rule power_strict_increasing, simp, simp)
  apply (subst less_diff_eq[symmetric])
  using assms
  apply (simp add: not_max_word_iff_less word_less_alt)
  apply (erule less_le_trans)
  apply simp
  done

lemma max_word_gt_0:
  "0 < max_word"
  by (simp add: le_neq_trans[OF max_word_max])

lemma and_not_max_word:
  "m \<noteq> max_word \<Longrightarrow> w && m \<noteq> max_word"
  by (simp add: not_max_word_iff_less word_and_less')

lemma mask_not_max_word:
  "m < LENGTH('a::len) \<Longrightarrow> mask m \<noteq> (max_word :: 'a word)"
  by (simp add: mask_eq_exp_minus_1)

lemmas and_mask_not_max_word =
  and_not_max_word[OF mask_not_max_word]

lemma shiftr_not_max_word:
  "0 < n \<Longrightarrow> w >> n \<noteq> max_word"
  by (metis and_mask_eq_iff_shiftr_0 and_mask_not_max_word diff_less len_gt_0 shiftr_le_0 word_shiftr_lt)

lemma shiftr_less_max_mask:
  "0 < n \<Longrightarrow> x >> n < mask LENGTH('a)" for x :: "'a::len word"
  using not_max_word_iff_less shiftr_not_max_word
  by auto

lemma word_sandwich1:
  fixes a b c :: "'a::len word"
  assumes "a < b"
  assumes "b <= c"
  shows "0 < b - a \<and> b - a <= c"
  using assms diff_add_cancel order_less_irrefl add_0 word_le_imp_diff_le
        word_le_less_eq word_neq_0_conv
  by metis

lemma word_sandwich2:
  fixes a b :: "'a::len word"
  assumes "0 < a"
  assumes "a <= b"
  shows "b - a < b"
  using assms less_le_trans word_diff_less
  by blast

lemma unat_and_mask_less_2p:
  fixes w :: "'a::len word"
  shows "m < LENGTH('a) \<Longrightarrow> unat (w && mask m) < 2 ^ m"
  by (simp add: unat_less_helper  and_mask_less')

lemma unat_shiftr_less_2p:
  fixes w :: "'a::len word"
  shows "n + m = LENGTH('a) \<Longrightarrow> unat (w >> n) < 2 ^ m"
  by (cases "n = 0"; simp add: unat_less_helper shiftr_less_t2n3)

lemma nat_div_less_mono:
  fixes m n :: nat
  shows "m div d < n div d \<Longrightarrow> m < n"
  by (meson div_le_mono not_less)

lemma word_shiftr_less_mono:
  fixes w :: "'a::len word"
  shows "w >> n < v >> n \<Longrightarrow> w < v"
  by (auto simp: word_less_nat_alt shiftr_div_2n' elim: nat_div_less_mono)

lemma word_shiftr_less_mask:
  fixes w :: "'a::len word"
  shows "(w >> n < v >> n) \<longleftrightarrow> (w && ~~mask n < v && ~~mask n)"
  by (metis (mono_tags) le_shiftr mask_shift shiftr_eq_neg_mask_eq word_le_less_eq word_le_not_less)

lemma word_shiftr_le_mask:
  fixes w :: "'a::len word"
  shows "(w >> n \<le> v >> n) \<longleftrightarrow> (w && ~~mask n \<le> v && ~~mask n)"
  by (metis (mono_tags) le_shiftr mask_shift shiftr_eq_neg_mask_eq word_le_less_eq word_le_not_less)

lemma word_shiftr_eq_mask:
  fixes w :: "'a::len word"
  shows "(w >> n = v >> n) \<longleftrightarrow> (w && ~~mask n = v && ~~mask n)"
  by (metis (mono_tags) mask_shift shiftr_eq_neg_mask_eq)

lemmas word_shiftr_cmp_mask =
  word_shiftr_less_mask word_shiftr_le_mask word_shiftr_eq_mask

lemma if_if_if_same_output:
  "(if c1 then if c2 then t else f else if c3 then t else f) = (if c1 \<and> c2 \<or> \<not>c1 \<and> c3 then t else f)"
  by (simp split: if_splits)

lemma word_le_split_mask:
  "(w \<le> v) \<longleftrightarrow> (w >> n < v >> n \<or> w >> n = v >> n \<and> w && mask n \<le> v && mask n)"
  apply (simp add: word_shiftr_eq_mask word_shiftr_less_mask)
  apply (rule subst[where P="\<lambda>c. c \<le> d = e" for d e, OF AND_NOT_mask_plus_AND_mask_eq[where n=n]])
  apply (rule subst[where P="\<lambda>c. d \<le> c = e" for d e, OF AND_NOT_mask_plus_AND_mask_eq[where n=n]])
  by (metis (no_types) Orderings.order_eq_iff and_not_eq_minus_and bit.double_compl linorder_linear
                       neg_mask_mono_le word_and_le2 word_le_minus_cancel word_not_le
                       word_plus_and_or_coroll2)

lemma uint_minus_1_less_le_eq:
  "0 < n \<Longrightarrow> (uint (n - 1) < m) = (uint n \<le> m)"
  by uint_arith

lemma scast_ucast_up_minus_1_ucast:
  assumes "LENGTH('a::len) < LENGTH('b::len)"
  assumes "0 < w"
  shows "SCAST('b \<rightarrow> 'c) (UCAST('a \<rightarrow> 'b) w - 1) = UCAST('a \<rightarrow> 'c::len) (w - 1)"
  using assms
  apply (subst scast_eq_ucast; simp)
   apply (metis gt0_iff_gem1 msb_less_mono ucast_less_ucast_weak unsigned_0 word_upcast_neg_msb)
  by (metis less_le ucast_nat_def ucast_up_preserves_not0 unat_minus_one unat_ucast_up_simp)

lemma toEnum_unat_ucast:
  "unat w < 2^LENGTH('a) \<Longrightarrow> toEnum (unat w) = (ucast w :: 'a::len word)"
  by (clarsimp simp: not_le)

lemma aligned_intvl_neg_mask_start:
  fixes x::"'a :: len word"
  assumes iv: "start \<le> x" "x < start + sz"
  assumes al: "is_aligned start n"
  assumes sz: "sz \<le> 2^n"
  shows "x && ~~ mask n = start"
proof -
  from iv sz
  obtain y where "x = start + y" and "y \<le> mask n"
    by (metis (no_types, opaque_lifting) add.commute diff_add_cancel order.trans leD le_plus'
              linorder_linear mask_eq_decr_exp order_less_le word_le_minus_one_leq)
  moreover
  have "start + y && ~~ mask n = start"
    by (simp add: al and_mask_0_iff_le_mask calculation is_aligned_mask_out_add_eq)
  ultimately
  show ?thesis by simp
qed

(* This would hold for LENGTH('a) \<le> n, but would not be suitable for simp *)
lemma ucast_and_mask_source:
  "LENGTH('a) < n \<Longrightarrow>
   UCAST('a \<rightarrow> 'b::len) w && mask n = ucast w && mask LENGTH('a)" for w::"'a::len word"
  by word_eqI (fastforce dest: test_bit_lenD)

lemma toEnum_unat_le:
  "x \<le> ucast y \<Longrightarrow> toEnum (unat x) \<le> y" for x::"'a::len word" and y::"'b::len word"
  apply (subgoal_tac "unat y < 2^LENGTH('b)")
   apply (subgoal_tac "unat x < 2^LENGTH('b)")
    apply (simp add: le_ucast_ucast_le)
   apply (fastforce simp: word_le_nat_alt unat_ucast
                    elim!: order_trans order_le_less_trans[rotated])
  apply simp
  done

lemma ucast_ucast_le_mask:
  "x \<le> mask LENGTH('b) \<Longrightarrow> ucast (ucast x::'b::len word) = (x::'a::len word)"
  using of_nat_unat_le_mask_ucast
  by force

lemma shiftr_le_mask:
  fixes w :: "'a::len word"
  shows "w >> n \<le> mask (LENGTH('a) - n)"
  by (fastforce simp flip: shiftr_mask2 intro: le_shiftr)

end
