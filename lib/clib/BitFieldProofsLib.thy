(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory BitFieldProofsLib
imports
  Eisbach_Tools.Eisbach_Methods
  CParser.TypHeapLib
begin

lemmas guard_simps =
  word_sle_def word_sless_def

lemmas mask_shift_simps =
  ucast_def shift_over_ao_dists word_bw_assocs
  word_size multi_shift_simps mask_def
  word_ao_dist NOT_eq
  word_and_max_simps

(* a << Suc 0 is too eagerly simplified into a * 2, so we have to deal with some patterns that
  should otherwise not occur: *)
lemma word_and_t2_dist[simp]:
  "(a && b) * 2 = (a * 2) && (b * 2)" for a::"'a::len word"
proof -
  have "a && b << 1 = (a << 1) && (b << 1)" by (simp only: shift_over_ao_dists)
  thus ?thesis by simp
qed

lemma word_t2_shiftr[simp]:
  "c \<le> 1 \<Longrightarrow> (a * 2) >> c = a && mask (size a - 1) << 1 - c" for a::"'a::len word"
  by (drule shiftl_shiftr1) simp


lemmas sep_heap_simps =
  sep_app_def hrs_mem_update_def
  hrs_htd_def split_def

lemma tag_eq_to_tag_masked_eq:
  "tag == v ==> tag && m = v && m"
  by simp

lemma clift_heap_update_footprint:
  "\<forall>p' :: 'a ptr. hrs_htd hp,g \<Turnstile>\<^sub>t p' \<longrightarrow> s_footprint p \<inter> s_footprint p' = {}
    \<Longrightarrow> (lift_t g (hrs_mem_update (heap_update p (v :: 'b :: wf_type)) hp)
        :: ('a :: mem_type) typ_heap) = lift_t g hp"
  apply (cases hp, simp add: lift_t_if fun_eq_iff hrs_mem_update_def hrs_htd_def)
  apply clarsimp
  apply (drule spec, drule(1) mp)
  apply (simp add: h_val_def heap_update_def)
  apply (subst heap_list_update_disjoint_same, simp_all)
  apply (simp add: set_eq_iff s_footprint_intvl[symmetric])
  done

lemma s_footprint_field_lvalue_disj_helper:
  "field_lookup (typ_info_t TYPE('b::mem_type)) f 0 = Some (ti,b)
      \<Longrightarrow> export_uinfo ti = typ_uinfo_t TYPE('a)
      \<Longrightarrow> (\<forall>x. P x \<longrightarrow> s_footprint (p::'b ptr) \<inter> S x = {})
      \<Longrightarrow> (\<forall>x. P x \<longrightarrow> s_footprint ((Ptr &(p\<rightarrow>f))::'a::mem_type ptr) \<inter> S x = {})"
  apply (drule field_lookup_export_uinfo_Some)
  apply simp
  apply (drule field_ti_s_sub_typ)
  apply blast
  done

lemma s_footprint_distinct_helper:
  "h_t_valid htd g (p :: 'a ptr) \<Longrightarrow> typ_uinfo_t TYPE('a :: c_type) \<bottom>\<^sub>t typ_uinfo_t TYPE('b :: c_type)
    \<Longrightarrow> (\<forall>q :: 'b ptr. h_t_valid htd g' q \<longrightarrow> s_footprint p \<inter> s_footprint q = {})"
  apply clarsimp
  apply (drule(1) h_t_valid_neq_disjoint)
    apply (clarsimp simp: sub_typ_proper_def tag_disj_def preorder_class.less_imp_le)
   apply (clarsimp simp: field_of_t_def)
   apply (drule field_of_sub)
   apply (simp add: tag_disj_def)
  apply (simp add: set_eq_iff )
  apply (blast dest: s_footprintD)
  done

text \<open>Use these handy rules to prove that clift doesn't change
  over various updates.\<close>
method prove_one_bf_clift_invariance
    = (intro clift_heap_update_footprint[THEN trans]
               s_footprint_field_lvalue_disj_helper
               s_footprint_distinct_helper,
      simp_all only: hrs_htd_mem_update,
      tactic \<open>distinct_subgoals_tac\<close>,
      (auto simp: typ_uinfo_t_def[symmetric] tag_disj_via_td_name ntbs
            elim: h_t_valid_clift)+)[1]

text \<open>Select points in the goal where we need to prove that
  clift doesn't change over updates, and prove them with the above.\<close>
method prove_bf_clift_invariance
    = ((subst Eq_TrueI[where P="lift_t g h = lift_t g h'" for g h h'],
          prove_one_bf_clift_invariance)+, simp)

end
