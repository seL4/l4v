(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory CommonOpsLemmas

imports
  "CommonOps"
begin

lemma fold_all_htd_updates':
  "ptr_retyp (p :: ('a :: c_type) ptr)
    = all_htd_updates TYPE('a) 1 (ptr_val p) 1"
  "(if P then (f :: heap_typ_desc \<Rightarrow> heap_typ_desc) else g) s
    = (if P then f s else g s)"
  "\<lbrakk> n < 2 ^ word_bits \<rbrakk> \<Longrightarrow>
    ptr_retyps n p = all_htd_updates TYPE('a) 1 (ptr_val p) (of_nat n)"
  "\<lbrakk> n < 2 ^ word_bits \<rbrakk> \<Longrightarrow>
    ptr_retyps (2 ^ n) p = all_htd_updates TYPE('a) 3 (ptr_val p) (of_nat n)"
  "n < 2 ^ word_bits \<Longrightarrow> typ_clear_region x n = all_htd_updates TYPE(machine_word) 0 x (of_nat n)"
  "n < 2 ^ word_bits \<Longrightarrow> typ_region_bytes x n = all_htd_updates TYPE(machine_word) 2 x (of_nat n)"
  "\<lbrakk> n < 2 ^ word_bits \<rbrakk> \<Longrightarrow>
    ptr_arr_retyps n p = all_htd_updates TYPE('a) 4 (ptr_val p) (of_nat n)"
  "\<lbrakk> n < 2 ^ word_bits \<rbrakk> \<Longrightarrow>
    ptr_arr_retyps (2 ^ n) p = all_htd_updates TYPE('a) 5 (ptr_val p) (of_nat n)"
  by (simp_all add: all_htd_updates_def fun_eq_iff word_bits_conv take_bit_nat_eq_self unat_of_nat)

lemma upcast_unat_less_2p_length:
    "is_up UCAST('a :: len \<rightarrow> 'b :: len) \<Longrightarrow> unat (x :: 'a word) < 2 ^ LENGTH('b)"
  by (simp add: is_up unat_pow_le_intro)

(* FIXME: this is a hack that happens to work on all arches. Use arch split. *)
lemma is_up_u32_word_size: "is_up UCAST(32 \<rightarrow> machine_word_len)"
  by (clarsimp simp add: is_up_def source_size target_size)

lemma is_up_i32_word_size: "is_up UCAST(32 signed \<rightarrow> machine_word_len)"
  by (clarsimp simp add: is_up_def source_size target_size)

(* This proof is a bit convoluted so that it happens to work with word_bits = 32 and 64 *)
lemma unat_word32_less_2p_word_bits: "unat (x :: 32 word) < 2 ^ word_bits"
  unfolding word_bits_def by (rule upcast_unat_less_2p_length, rule is_up_u32_word_size)

lemma unat_sword32_less_2p_word_bits: "unat (x :: 32 signed word) < 2 ^ word_bits"
  by (rule upcast_unat_less_2p_length[OF is_up_i32_word_size, simplified word_bits_def[symmetric]])

lemmas fold_all_htd_updates_intermediate
    = fold_all_htd_updates'
      fold_all_htd_updates'(3-)[OF unat_less_2p_word_bits]
      fold_all_htd_updates'(3-)[OF unat_word32_less_2p_word_bits]
      fold_all_htd_updates'(3-)[OF unat_sword32_less_2p_word_bits]

lemmas fold_all_htd_updates = fold_all_htd_updates_intermediate[simplified word_bits_conv]

lemma signed_div_range_check:
  assumes len: "size a > 1"
  shows
  "(sint a sdiv sint b = sint (a sdiv b))
    = (a \<noteq> (- (2 ^ (size a - 1))) \<or> b \<noteq> -1)"
proof -
  have sints: "(sint (1 :: 'a word)) = 1"
       "(sint (-1 :: 'a word)) = -1"
       "(sint (0 :: 'a word)) = 0"
    using len
    apply (simp_all add: word_size)
    done
  have abs_sint_gt_1:
    "b \<noteq> 0 \<and> b \<noteq> 1 \<and> b \<noteq> -1 \<Longrightarrow> abs (sint b) > 1"
    apply (fold word_sint.Rep_inject,
        simp only: sints abs_if split: if_split)
    apply arith
    done
  have mag: "(a \<noteq> (- (2 ^ (size a - 1))) \<or> (b \<noteq> -1 \<and> b \<noteq> 1))
    \<Longrightarrow> abs (abs (sint a) div abs (sint b)) < 2 ^ (size a - 1)"
    using word_sint.Rep_inject[where x=a and y="- (2 ^ (size a - 1))"]
          word_sint.Rep_inject[where x=b and y=1]
    apply (simp add: word_size sint_int_min sints)
    apply (simp add: nonneg_mod_div)
    apply (cases "b = 0")
     apply simp
    apply (erule impCE)
     apply (rule order_le_less_trans, rule zdiv_le_dividend, simp_all)
     apply (cut_tac x=a in sint_range')
     apply (clarsimp simp add: abs_if word_size)
    apply (cases "a = 0", simp_all)
    apply (rule order_less_le_trans, rule int_div_less_self, simp_all)
     apply (rule abs_sint_gt_1, simp)
    apply (cut_tac x=a in sint_range')
    apply (clarsimp simp add: abs_if word_size)
    done
  note sint_of_int_eq[simp] signed_take_bit_int_eq_self[simp]
  show ?thesis using mag len
    apply (cases "b = 1")
     apply (case_tac "size a", simp_all)[1]
     apply (case_tac nat, simp_all add: sint_word_ariths word_size)[1]
    apply (simp add: sdiv_int_def sdiv_word_def del: of_int_mult)
    apply (simp add: sbintrunc_eq_in_range range_sbintrunc sgn_if)
    apply (safe, simp_all add: word_size sint_int_min sint_int_max_plus_1;
           simp add: sint_word_ariths)
    done
qed

lemma ptr_add_assertion_uintD:
  "ptr_add_assertion ptr (uint (x :: ('a :: len) word)) strong htd
    \<longrightarrow> (x = 0 \<or> array_assertion ptr (if strong then unat (x + 1) else unat x) htd)"
  by (auto simp: unat_plus_if_size intro: array_assertion_shrink_right)

lemma sint_uint_sless_0_if:
  "sint x = (if x <s 0 then - uint (- x) else uint (x :: ('a :: len) word))"
  apply (simp add: word_sint_msb_eq word_sless_alt
                   word_size uint_word_ariths)
  apply (clarsimp simp: zmod_zminus1_eq_if uint_0_iff)
  done

lemma ptr_add_assertion_sintD:
  "ptr_add_assertion ptr (sint (x :: ('a :: len) word)) strong htd
    \<longrightarrow> (x = 0 \<or> (x <s 0 \<and> array_assertion (ptr +\<^sub>p sint x)
            (unat (- x)) htd)
        \<or> (x \<noteq> 0 \<and> \<not> x <s 0 \<and> array_assertion ptr (if strong then unat (x + 1) else unat x) htd))"
  apply (simp add: ptr_add_assertion_def word_sless_alt
                   sint_uint_sless_0_if[THEN arg_cong[where f="\<lambda>x. - x"]]
                   sint_uint_sless_0_if[THEN arg_cong[where f=nat]]
                   unat_plus_if_size)
  apply (simp add: array_assertion_shrink_right)
  apply (auto simp: linorder_not_less)
  done

\<comment> \<open>
  Some lemmas used by both SimplExport and ProveGraphRefine.
\<close>

lemmas sdiv_word_max_ineq = sdiv_word_max[folded zle_diff1_eq, simplified]

lemmas signed_mult_eq_checks_all =
  signed_mult_eq_checks_double_size[where 'a="32" and 'b="64", simplified]
  signed_mult_eq_checks_double_size[where 'a="32 signed" and 'b="64 signed", simplified]
  signed_mult_eq_checks_double_size[where 'a="64" and 'b="128", simplified]
  signed_mult_eq_checks_double_size[where 'a="64 signed" and 'b="128 signed", simplified]

lemmas signed_arith_ineq_checks_to_eq_all =
  signed_arith_ineq_checks_to_eq[where 'a="32"]
  signed_arith_ineq_checks_to_eq[where 'a="32", simplified word_size, simplified]
  signed_arith_ineq_checks_to_eq[where 'a="32 signed"]
  signed_arith_ineq_checks_to_eq[where 'a="32 signed", simplified word_size, simplified]
  signed_arith_ineq_checks_to_eq[where 'a="64"]
  signed_arith_ineq_checks_to_eq[where 'a="64", simplified word_size, simplified]
  signed_arith_ineq_checks_to_eq[where 'a="64 signed"]
  signed_arith_ineq_checks_to_eq[where 'a="64 signed", simplified word_size, simplified]

lemmas signed_div_range_check_all =
  signed_div_range_check[where 'a="32", simplified word_size, simplified]
  signed_div_range_check[where 'a="32 signed", simplified word_size, simplified]
  signed_div_range_check[where 'a="64", simplified word_size, simplified]
  signed_div_range_check[where 'a="64 signed", simplified word_size, simplified]

lemma word32_31_less:
  "31 < len_of TYPE (32 signed)" "31 > (0 :: nat)"
  "31 < len_of TYPE (32)" "31 > (0 :: nat)"
  by auto

lemma word64_31_less:
  "31 < len_of TYPE (64 signed)" "31 > (0 :: nat)"
  "31 < len_of TYPE (64)" "31 > (0 :: nat)"
  by auto

lemmas signed_shift_guard_to_word_all =
  signed_shift_guard_to_word[OF word32_31_less(1-2)]
  signed_shift_guard_to_word[OF word32_31_less(3-4)]
  signed_shift_guard_to_word[OF word64_31_less(1-2)]
  signed_shift_guard_to_word[OF word64_31_less(3-4)]

lemmas guard_arith_simps =
  neg_le_iff_le
  signed_arith_eq_checks_to_ord
  signed_arith_ineq_checks_to_eq_all
  signed_div_range_check_all
  signed_mult_eq_checks_all
  signed_shift_guard_to_word_all
  sdiv_word_min[THEN eqTrueI] sdiv_word_max_ineq

(* FIXME: move to word lib *)
lemma small_downcasts:
  "unat (x :: 'a :: len word) < 2 ^ LENGTH('b :: len) \<Longrightarrow> unat (UCAST('a \<rightarrow> 'b) x) = unat x"
  apply (case_tac "LENGTH('a) \<le> LENGTH('b)", simp add: unat_ucast_up_simp)
  apply (simp add: unat_ucast unat_less_power)
  done

(* FIXME: move to word lib *)
lemma less_shift_makes_shift_cast_safe:
  "y < (a :: 'a :: len word) >> unat (x :: 'b :: len word) \<Longrightarrow>
  unat (UCAST('b \<rightarrow> 'a) x) = unat x"
  apply (prop_tac "unat x < LENGTH('a)")
   apply (rotate_tac)
   apply (erule contrapos_pp; simp add: not_less)
   apply (prop_tac "a >> unat x = 0")
    apply (rule shiftr_eq_0; simp)
   apply simp
  apply (subst small_downcasts)
  apply (meson le_less_trans n_less_equal_power_2 nat_less_le)
  apply simp
  done

lemmas less_shift_makes_shift_cast_safe_arg_cong =
  arg_cong[where f="f w" for f w, OF less_shift_makes_shift_cast_safe]

\<comment> \<open>
  @{thm less_shift_makes_shift_cast_safe} allows us to
  remove the `ucast` in `unat (ucast x)`, but this loses potentially important
  type information. These rules act as "lenses" to make sure we only modify
  the relevant ucasts (the ones that show up in the guards of translated
  nontrivial shifts).
\<close>
lemmas less_shift_targeted_cast_convs =
  less_shift_makes_shift_cast_safe_arg_cong[where f=shiftr]
  less_shift_makes_shift_cast_safe_arg_cong[where f="(^)"]

end
