(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CNode_DR
imports Finalise_DR
begin

context begin interpretation Arch . (*FIXME: arch-split*)

definition
  translate_cnode_invocation :: "Invocations_A.cnode_invocation \<Rightarrow> cdl_cnode_invocation option"
where
 "translate_cnode_invocation x \<equiv> case x of
    Invocations_A.InsertCall cap src_slot dest_slot
       \<Rightarrow> Some (Invocations_D.InsertCall (transform_cap cap)
                (transform_cslot_ptr src_slot) (transform_cslot_ptr dest_slot))
  | Invocations_A.MoveCall cap src_slot dest_slot
       \<Rightarrow> Some (Invocations_D.MoveCall (transform_cap cap)
                (transform_cslot_ptr src_slot) (transform_cslot_ptr dest_slot))
  | Invocations_A.DeleteCall slot \<Rightarrow> Some (Invocations_D.DeleteCall (transform_cslot_ptr slot))
  | _ \<Rightarrow> None"

lemma corres_assert_lhs:
  "(F \<Longrightarrow> corres_underlying sr False False r P P' (f ()) g)
    \<Longrightarrow> corres_underlying sr False False r (\<lambda>s. F \<and> P s) P' (assert F >>= f) g"
  by (cases F; simp add: corres_underlying_def)

lemma ex_cte_cap_to_not_idle:
  "\<lbrakk> ex_cte_cap_wp_to P p s; valid_global_refs s;
           valid_idle s; valid_irq_node s \<rbrakk> \<Longrightarrow> fst p \<noteq> idle_thread s"
  apply (cases p)
  apply (clarsimp simp: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state)
  apply (drule(1) valid_global_refsD2)
  apply (case_tac cap, simp_all add: cap_range_def global_refs_def)
  apply (rename_tac word)
  apply (clarsimp simp: valid_idle_def valid_irq_node_def pred_tcb_at_def
                        obj_at_def is_cap_table_def)
  apply (drule_tac x=word in spec, simp)
  done

definition
  "cap_insert_dest_original cap src_cap
     = (if is_ep_cap cap
        then cap_ep_badge cap \<noteq> cap_ep_badge src_cap
        else if is_ntfn_cap cap
        then cap_ep_badge cap \<noteq> cap_ep_badge src_cap
        else if is_IRQHandlerCap cap
        then src_cap = cap.IRQControlCap
        else if is_ArchObjectCap cap \<and> is_SGISignalCap (the_arch_cap cap)
        then src_cap = IRQControlCap
        else is_untyped_cap cap)"

lemma option_return_modify_modify:
  "case_option (return ()) (\<lambda>x. modify (f x))
       = (\<lambda>opt. modify (case_option id f opt))"
  by (auto split: option.split simp: modify_id_return)

lemma update_cdt_modify:
  "update_cdt f = modify (cdt_update f)"
  apply (simp add: update_cdt_def set_cdt_modify gets_fold_into_modify)
  apply (rule ext, simp add: simpler_modify_def)
  done

lemma is_untyped_cap_transform_cap[simp]:
  "Types_D.is_untyped_cap (transform_cap src_cap)
  = is_untyped_cap src_cap"
  apply (case_tac src_cap)
  apply (simp_all add:transform_cap_def cap_type_simps)
  apply (clarsimp simp:cap_type_simps split:arch_cap.splits)
  done

lemma is_untyped_cap_eqD:
  "Structures_A.is_untyped_cap src_cap
  \<Longrightarrow> \<exists>dev ptr sz idx. src_cap = cap.UntypedCap dev ptr sz idx"
  by (case_tac src_cap, simp_all)

lemma p2_less_minus:
  "2 ^ sz - Suc 0 < 2 ^ sz"
  by auto

lemma dcorres_set_untyped_cap_as_full:
  "dcorres dc \<top> (K (cap_aligned cap) and cte_wp_at ((=) src_cap) src
  and valid_objs and not_idle_thread (fst src) and valid_idle)
  (CSpace_D.set_untyped_cap_as_full (transform_cap src_cap) (transform_cap cap) (transform_cslot_ptr src))
  (CSpace_A.set_untyped_cap_as_full src_cap cap src)"
  apply (simp add:set_untyped_cap_as_full_def CSpace_D.set_untyped_cap_as_full_def
              split del:if_split)
  apply (case_tac "is_untyped_cap src_cap \<and> is_untyped_cap cap")
   apply (rule dcorres_expand_pfx)
   apply (rule corres_guard_imp)
     apply (rule corres_if)
       apply clarsimp
       apply (clarsimp dest!:is_untyped_cap_eqD)
       apply (drule(1) cte_wp_valid_cap)
       apply (simp add:valid_cap_def cap_aligned_def)
       apply (rule iffI)
        apply clarsimp
        apply (drule two_power_eq[THEN iffD1,rotated 2])
          apply (simp add:valid_cap_def word_bits_def cap_aligned_def)
         apply (simp add:valid_cap_def word_bits_def cap_aligned_def)
        apply simp
       apply simp
      apply (rule_tac F = "is_untyped_cap src_cap \<and> is_untyped_cap cap"  in corres_gen_asm)
      apply (clarsimp dest!:is_untyped_cap_eqD)
      apply (rule set_cap_corres)
       apply (clarsimp simp:transform_cap_def free_range_of_untyped_def cap_aligned_def max_free_index_def
                       dest!:is_untyped_cap_eqD)
       apply (cut_tac sz = sz in p2_less_minus)
       apply simp
      apply simp
     apply simp
    apply fastforce
   apply (fastforce simp:not_idle_thread_def)
  apply auto
  done

lemma dcorres_opt_parent_set_parent_helper:
  "dcorres dc \<top> P
  (gets (opt_parent (transform_cslot_ptr src)) >>=
  case_option (return ())
  (\<lambda>parent. modify (\<lambda>s. s\<lparr>cdl_cdt := (cdl_cdt s)(transform_cslot_ptr child \<mapsto> parent)\<rparr>)))
  g \<Longrightarrow>
  dcorres dc \<top> (\<lambda>s. cdt s child = None \<and> cte_at child s \<and>
   mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s) \<and> P s)
  (gets (opt_parent (transform_cslot_ptr src)) >>=
  case_option (return ()) (set_parent (transform_cslot_ptr child)))
  g"
  apply (clarsimp simp:gets_def set_parent_def bind_def
    return_def get_def assert_def corres_underlying_def
    fail_def
    simpler_modify_def split:option.splits)
  apply (drule_tac x = b in spec)
  apply (intro conjI impI)
    apply clarsimp
   apply clarsimp
  apply (clarsimp simp:KHeap_DR.cdl_cdt_transform)
  apply (drule(2) transform_cdt_none)
  apply simp
  done

lemma dcorres_set_parent_helper:
  "dcorres dc \<top> P
  (modify (\<lambda>s. s\<lparr>cdl_cdt := (cdl_cdt s)(transform_cslot_ptr child \<mapsto> parent)\<rparr>))
  g \<Longrightarrow>
  dcorres dc \<top> (\<lambda>s. cdt s child = None \<and> cte_at child s \<and>
   mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s) \<and> P s)
  (set_parent (transform_cslot_ptr child) parent)
  g"
  apply (clarsimp simp:gets_def set_parent_def bind_def
    return_def get_def assert_def corres_underlying_def
    fail_def
    simpler_modify_def split:option.splits)
  apply (drule_tac x = b in spec)
  apply (clarsimp simp:KHeap_DR.cdl_cdt_transform)
  apply (drule(2) transform_cdt_none)
  apply simp
  done

lemma revokable_cap_insert_dest_original:
  "is_cap_revocable capa cap = cap_insert_dest_original capa cap"
  by (clarsimp simp: is_cap_revocable_def arch_is_cap_revocable_def cap_insert_dest_original_def
                     is_cap_simps
               split: arch_cap.splits cap.splits)

lemma insert_cap_sibling_corres:
  "dcorres dc \<top>
        (\<lambda>s. cte_wp_at (\<lambda>cap'. \<not> should_be_parent_of cap' (is_original_cap s src)
                 cap (cap_insert_dest_original cap cap')) src s
              \<and> cte_wp_at ((=) cap.NullCap) sibling s
              \<and> cte_at src s
              \<and> not_idle_thread (fst sibling) s
              \<and> not_idle_thread (fst src) s
              \<and> valid_mdb s \<and> valid_idle s \<and> valid_objs s \<and> cap_aligned cap)
        (insert_cap_sibling (transform_cap cap) (transform_cslot_ptr src) (transform_cslot_ptr sibling))
        (cap_insert cap src sibling)"
  supply if_cong[cong]
  apply (simp add: cap_insert_def[folded cap_insert_dest_original_def])
  apply (simp add: insert_cap_sibling_def insert_cap_orphan_def bind_assoc
                   option_return_modify_modify
                   gets_fold_into_modify update_cdt_modify
                   set_original_def modify_modify
                   cap_insert_ext_def update_cdt_list_def set_cdt_list_modify
             cong: option.case_cong)
  apply (rule stronger_corres_guard_imp)
     apply (rule corres_split[OF get_cap_corres], simp)+
        apply (rule corres_assert_lhs corres_assert_rhs)+
        apply (rule_tac F = "src_cap = transform_cap src_capa" in corres_gen_asm)
        apply simp
        apply (rule corres_split[OF dcorres_set_untyped_cap_as_full])
          apply (rule corres_split[OF set_cap_corres[OF refl refl]])
            apply (rule dcorres_opt_parent_set_parent_helper)
            apply (clarsimp simp:gets_fold_into_modify dc_def[symmetric]
              option_return_modify_modify modify_modify bind_assoc
              cong:option.case_cong)
            apply (rule_tac P=\<top> and P'="(\<lambda>s. \<not> should_be_parent_of src_capa (is_original_cap s src) cap orig')
              and cte_at src and cte_at sibling
              and (\<lambda>s. mdb_cte_at (swp cte_at s) (cdt s))
              and (\<lambda>s. cdt s sibling = None)" for orig'
              in corres_modify)
            apply (clarsimp split del: if_split)
            apply (subst if_not_P, assumption)+
            apply (clarsimp simp: opt_parent_def transform_def
              transform_objects_def transform_cdt_def
              transform_current_thread_def
              transform_asid_table_def
              split: option.split)
            apply (clarsimp simp: fun_upd_def[symmetric] cong:if_cong)
            apply (subgoal_tac "inj_on transform_cslot_ptr ({src, sibling} \<union> dom (cdt s') \<union> ran (cdt s'))")
             apply (subst map_lift_over_f_eq map_lift_over_upd,
               erule inj_on_subset, fastforce)+
             apply (simp add: map_option_is_None[THEN trans [OF eq_commute]]
               fun_eq_iff del: inj_on_insert)
             apply (subst eq_commute [where a=None])
             apply (subst map_lift_over_f_eq map_lift_over_upd,
               erule inj_on_subset, fastforce)+
             apply clarsimp
            apply (rule_tac s=s' in transform_cdt_slot_inj_on_cte_at[where P=\<top>])
            apply (auto simp: swp_def dest: mdb_cte_atD
              elim!: ranE)[1]
           apply ((wp set_cap_caps_of_state2 get_cap_wp hoare_weak_lift_imp
             | simp add: swp_def cte_wp_at_caps_of_state)+)
         apply (wp set_cap_idle |
            simp add:set_untyped_cap_as_full_def split del: if_split)+
          apply (rule_tac Q'="\<lambda>r s. cdt s sibling = None
           \<and> \<not> should_be_parent_of src_capa (is_original_cap s sibling) cap (cap_insert_dest_original cap src_capa)
           \<and> mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)"
           in hoare_strengthen_post)
           apply (wp set_cap_mdb_cte_at arch_update_cap_valid_mdb)
          apply (clarsimp simp:mdb_cte_at_def should_be_parent_of_def
           cte_wp_at_caps_of_state has_parent_cte_at is_physical_def
           dest!:is_untyped_cap_eqD)
          apply fastforce
         apply (wp get_cap_wp set_cap_idle hoare_weak_lift_imp
           | simp add:set_untyped_cap_as_full_def
           split del: if_split)+
         apply (rule_tac Q'="\<lambda>r s. cdt s sibling = None
           \<and> (\<exists>cap. caps_of_state s src = Some cap)
           \<and> \<not> should_be_parent_of src_capa (is_original_cap s src) cap (cap_insert_dest_original cap src_capa)
           \<and> mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)"
           in hoare_strengthen_post)
          apply (wp set_cap_mdb_cte_at arch_update_cap_valid_mdb)
         apply (clarsimp simp:mdb_cte_at_def should_be_parent_of_def
           cte_wp_at_caps_of_state has_parent_cte_at is_physical_def
           dest!:is_untyped_cap_eqD)
         apply fastforce
        apply (wpsimp wp: get_cap_wp set_cap_idle)+
   apply (clarsimp simp: not_idle_thread_def)
   apply (clarsimp simp: caps_of_state_transform_opt_cap cte_wp_at_caps_of_state
     transform_cap_def)
  apply (clarsimp simp: not_idle_thread_def cte_wp_at_caps_of_state)
  apply (clarsimp simp: valid_mdb_def cte_wp_at_cases dest!:invs_mdb)
  apply (case_tac "cdt s' sibling", safe intro!: mdb_cte_atI)
  (* 145 subgoals *)
  by (auto dest: mdb_cte_atD is_untyped_cap_eqD
           simp: revokable_cap_insert_dest_original valid_mdb_def
                 swp_def cte_wp_at_caps_of_state not_idle_thread_def)

lemma insert_cap_child_corres:
  "dcorres dc \<top>
        (\<lambda>s. cte_wp_at (\<lambda>cap'. should_be_parent_of cap' (is_original_cap s src)
                 cap (cap_insert_dest_original cap cap')) src s
              \<and> not_idle_thread (fst child) s \<and> valid_idle s
              \<and> valid_mdb s \<and> not_idle_thread (fst src) s \<and> valid_objs s \<and> cap_aligned cap)
        (insert_cap_child (transform_cap cap) (transform_cslot_ptr src) (transform_cslot_ptr child))
        (cap_insert cap src child)"
  supply revokable_cap_insert_dest_original[simp]
  supply if_cong[cong]
  apply (simp add: cap_insert_def[folded cap_insert_dest_original_def])
  apply (simp add: insert_cap_child_def insert_cap_orphan_def bind_assoc
                   option_return_modify_modify
                   gets_fold_into_modify update_cdt_modify
                   set_original_def modify_modify
                   cap_insert_ext_def update_cdt_list_def set_cdt_list_modify
             cong: option.case_cong)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF get_cap_corres], simp)+
        apply (rule_tac P="old_cap \<noteq> cdl_cap.NullCap" and P'="rv' \<noteq> cap.NullCap"
          in corres_symmetric_bool_cases)
          apply (clarsimp simp :transform_cap_def split:cap.splits arch_cap.splits)
         apply (simp add:assert_def)
         apply (rule corres_trivial)
         apply (simp add:corres_free_fail)
        apply (simp add:assert_def)
        apply (rule corres_split[OF dcorres_set_untyped_cap_as_full])
          apply (rule corres_split[OF set_cap_corres[OF refl refl]])
            apply (rule dcorres_set_parent_helper)
            apply (rule_tac P=\<top> and P'="(\<lambda>s. should_be_parent_of src_capa (orig s) cap orig')
              and cte_at src and cte_at child
              and (\<lambda>s. mdb_cte_at (swp cte_at s) (cdt s))" for orig orig'
              in corres_modify)
            apply (clarsimp split del: if_split)
            apply (subst if_P, assumption)+
            apply (clarsimp simp: opt_parent_def transform_def transform_asid_table_def
                               transform_objects_def transform_cdt_def
                               transform_current_thread_def)
            apply (clarsimp simp: fun_upd_def[symmetric] cong:if_cong)
            apply (subgoal_tac "inj_on transform_cslot_ptr ({src, child} \<union> dom (cdt s') \<union> ran (cdt s'))")
             apply (subst map_lift_over_f_eq map_lift_over_upd,
                 erule inj_on_subset, fastforce)+
             apply (simp add: fun_eq_iff)
            apply (rule_tac s=s' in transform_cdt_slot_inj_on_cte_at[where P=\<top>])
            apply (auto simp: swp_def dest: mdb_cte_atD
                      elim!: ranE)[1]
           apply (wp set_cap_caps_of_state2 get_cap_wp hoare_weak_lift_imp
                    | simp add: swp_def cte_wp_at_caps_of_state)+
         apply (wp set_cap_idle |
          simp add:set_untyped_cap_as_full_def split del:if_split)+
          apply (rule_tac Q'="\<lambda>r s. not_idle_thread (fst child) s
            \<and> should_be_parent_of src_capa (is_original_cap s child) cap (cap_insert_dest_original cap src_capa)
            \<and> mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)"
           in hoare_strengthen_post)
           apply (wp set_cap_mdb_cte_at | simp add:not_idle_thread_def)+
          apply (clarsimp simp:mdb_cte_at_def cte_wp_at_caps_of_state)
          apply fastforce
         apply (wp get_cap_wp set_cap_idle hoare_weak_lift_imp
           | simp split del:if_split add:set_untyped_cap_as_full_def)+
         apply (rule_tac Q'="\<lambda>r s. not_idle_thread (fst child) s
           \<and> (\<exists>cap. caps_of_state s src = Some cap)
           \<and> should_be_parent_of src_capa (is_original_cap s src) cap (cap_insert_dest_original cap src_capa)
           \<and> mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)"
       in hoare_strengthen_post)
          apply (wp set_cap_mdb_cte_at hoare_weak_lift_imp | simp add:not_idle_thread_def)+
         apply (clarsimp simp:mdb_cte_at_def cte_wp_at_caps_of_state)
         apply fastforce
        apply clarsimp
        apply (wp get_cap_wp |simp)+
  apply (clarsimp simp: not_idle_thread_def)
  apply (clarsimp simp: caps_of_state_transform_opt_cap cte_wp_at_caps_of_state
    transform_cap_def)+
  apply (clarsimp simp: valid_mdb_def cte_wp_at_cases dest!:invs_mdb)
  by (case_tac "cdt s' child", safe intro!: mdb_cte_atI;
         auto dest: mdb_cte_atD is_untyped_cap_eqD
              simp: valid_mdb_def swp_def cte_wp_at_caps_of_state not_idle_thread_def)

lemma move_cap_corres:
  "dcorres dc \<top> (cte_wp_at ((=) cap.NullCap) p'
                     and invs and cte_wp_at ((\<noteq>) cap.NullCap) p
                     and not_idle_thread (fst p')
                     and not_idle_thread (fst p))
     (move_cap (transform_cap cap) (transform_cslot_ptr p)
          (transform_cslot_ptr p'))
     (cap_move cap p p')"
proof -
  note inj_on_insert[iff del]
  have insert_sub_walk:
    "\<And>p p' S. p \<noteq> p' \<Longrightarrow> insert p S - {p'} = insert p (S - {p'})"
    by auto
  show ?thesis
    supply if_cong[cong]
    apply (simp add: cap_move_def move_cap_def swap_parents_def
                del: fun_upd_apply)
    apply (rule stronger_corres_guard_imp)
      apply (rule corres_split_nor)
         apply (simp add: insert_cap_orphan_def)
         apply (rule corres_dummy_return_pr[where b="()"])
         apply (rule corres_split[where r'=dc])
            apply (rule corres_gets_the)
            apply simp
            apply (rule corres_trivial, rule gets_symb_exec_l)
           apply (rule corres_assert_lhs)
           apply simp
           apply (rule set_cap_corres, simp+)[1]
          apply (wp set_cap_caps_of_state2 set_cap_idle)+
        apply (rule corres_split_nor)
           apply (rule set_cap_corres)
            apply (simp add: transform_cap_def)
           apply simp
          apply (rule dcorres_gets_all_param)
          apply (rule dcorres_gets_all_param)
          apply (simp add: swap_parents_def
                           set_original_def set_cdt_modify
                           gets_fold_into_modify modify_modify
                           cap_move_ext_def bind_assoc update_cdt_list_def set_cdt_list_modify)
          apply (rule conjI, clarsimp)
           apply (rule_tac P'="cte_at p and cte_at p' and (\<lambda>s. cdt s p' = None)
                         and (\<lambda>s. p' \<notin> ran (cdt s)) and no_mloop o cdt
                         and (\<lambda>s. mdb_cte_at (swp cte_at s) (cdt s)) and K (p \<noteq> p')" and P=\<top>
                       in corres_inst)
           apply (rule corres_modify)
           apply (clarsimp simp: transform_def transform_current_thread_def
                                 transform_cdt_def transform_asid_table_def
                                 transform_objects_def)
          apply clarsimp
          apply (rule corres_modify)
          apply (clarsimp simp: transform_def transform_current_thread_def
                                transform_cdt_def transform_asid_table_def
                                transform_objects_def)
          apply (subgoal_tac "inj_on transform_cslot_ptr
              ({p, p'} \<union> dom (cdt s') \<union> ran (cdt s')) \<and> cdt s' p \<noteq> Some p")
           apply (elim conjE)
           apply (subst map_lift_over_if_eq)
            apply (erule inj_on_subset, auto elim!: ranE split: if_split_asm)[1]
           apply (rule sym)
           apply (simp add: Fun.swap_def split del: if_split)
           apply (subst map_lift_over_upd[unfolded fun_upd_def],
                    ((erule inj_on_subset, auto elim!: ranE split: if_split_asm)[1]))+
           apply (rule ext)
           apply (cases p, cases p')
           apply (simp split del: if_split)
           apply simp
           apply (subst inj_on_subset map_lift_over_f_eq[OF inj_on_subset],
                  assumption, fastforce)+
           apply (simp add: inj_on_eq_iff[where f="transform_cslot_ptr"]
                            ranI domI map_option_eq_Some[THEN trans [OF eq_commute]])
           apply (auto simp: inj_on_eq_iff[where f="transform_cslot_ptr"]
                             ranI domI,
                  auto simp: inj_on_eq_iff[where f="transform_cslot_ptr"]
                             ranI domI map_lift_over_eq_Some)[1]
          apply (clarsimp simp: no_cdt_loop_mloop)
          apply (rule_tac s=s' in transform_cdt_slot_inj_on_cte_at[where P=\<top>])
          apply (auto simp: swp_def dest: mdb_cte_atD
                      elim!: ranE)[1]
         apply (wp set_cap_caps_of_state2
                    | simp add: swp_def cte_wp_at_caps_of_state)+
     apply clarsimp
     apply (clarsimp simp: cte_wp_at_caps_of_state
                           caps_of_state_transform_opt_cap
                           transform_cap_def not_idle_thread_def)
    apply (clarsimp simp: mdb_Null_None[OF _ invs_mdb])
    apply (frule invs_mdb)
    apply (clarsimp simp: cte_wp_at_caps_of_state valid_mdb_def)
    apply (safe intro!: mdb_cte_atI)
         apply (auto simp: swp_def cte_wp_at_caps_of_state not_idle_thread_def
                     dest: mdb_cte_atD elim!: ranE)
    done
qed

lemma dcorres_get_cap_lhs:
  "(\<And>cap. dcorres r P (P' and cte_wp_at ((=) cap) slot) (f (transform_cap cap)) g) \<Longrightarrow>
   dcorres r P (P' and cte_at slot and valid_idle and not_idle_thread (fst slot))
     (KHeap_D.get_cap (transform_cslot_ptr slot) >>= f) g"
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp: cte_wp_at_caps_of_state not_idle_thread_def)
  apply (frule caps_of_state_transform_opt_cap; simp?)
  apply (simp add: gets_the_def assert_opt_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp: not_idle_thread_def cte_wp_at_caps_of_state)
  apply (rule corres_guard_imp, assumption)
   apply simp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

lemma dcorres_get_cap_rhs:
  "dcorres r P (Q and cte_wp_at ((=) cap) slot) f (g cap) \<Longrightarrow>
   dcorres r P (Q and cte_wp_at ((=) cap) slot) f (CSpaceAcc_A.get_cap slot >>= g)"
  apply (rule_tac Q'="\<lambda>rv s. Q s \<and> cte_wp_at ((=) cap) slot s \<and> rv = cap" in corres_symb_exec_r)
     apply (rename_tac rv)
     apply (case_tac "rv = cap")
      apply simp
      apply (erule corres_guard_imp; simp)
     apply (simp add: corres_underlying_def)
    apply (wp get_cap_wp)
    apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply wpsimp+
  done

text \<open>For caps that can be deleted in one step without recursion.\<close>
lemma dcorres_rec_del_fast:
  "can_fast_delete (transform_cap cap) \<Longrightarrow>
   dcorres (dc \<oplus> dc) \<top> ((invs and valid_pdpt_objs) and cte_wp_at ((=) cap) slot)
     (liftE (CSpace_D.finalise_cap (transform_cap cap)))
     (rec_del (FinaliseSlotCall slot True))"
  apply (subst rec_del_simps_ext)
  apply (simp add: liftE_bindE)
  apply (rule dcorres_get_cap_rhs)
  apply (cases "cap = cap.NullCap")
   apply (simp add: returnOk_liftE[symmetric])
   apply (rule corres_guard_imp, rule dcorres_returnOk; simp)
  apply (simp add: liftE_bindE)
  apply (rule_tac Q'="\<lambda>_. (invs and valid_pdpt_objs) and cte_wp_at ((=) cap) slot"
               in corres_symb_exec_r)
     apply (simp add: liftE_def split_def bind_assoc)
     apply (rule corres_guard_imp)
       apply (rule corres_split[OF dcorres_finalise_cap])
          apply assumption
         apply clarsimp
         apply (simp add: returnOk_def)
        apply wpsimp+
     apply (fastforce simp: cte_wp_at_caps_of_state elim: caps_of_state_valid)
    apply (wpsimp simp: IpcCancel_A.is_final_cap_def)+
  done

lemma delete_cap_corres':
  "dcorres (dc \<oplus> dc) \<top> (cte_at (a, b) and invs and emptyable (a, b)
                         and not_idle_thread a and valid_pdpt_objs)
     (delete_cap (transform_cslot_ptr (a, b))) (cap_delete (a, b))"
  apply (simp add: delete_cap_def liftE_bindE)
  apply (rule corres_guard_imp)
    apply (rule dcorres_get_cap_lhs[where P=\<top> and slot="(a, b)"
                  and P'="invs and emptyable (a, b) and not_idle_thread a and valid_pdpt_objs"])
    apply (rename_tac cap)
    apply (case_tac "can_fast_delete (transform_cap cap)"; simp add: dcorres_chaos_dc_dc)
    apply (simp add: cap_delete_def liftE_distrib)
    apply (subst rec_del_simps_ext)
    apply (simp add: bindE_assoc)
    apply (rule corres_guard_imp)
      apply (rule corres_splitEE[OF dcorres_rec_del_fast])
         apply assumption
        apply (clarsimp simp: bindE_assoc when_def)
        apply (rule empty_slot_corres)
       apply wp+
      apply (rule validE_validE_R)
      apply (simp add: validE_def weak_valid_mdb_def)
      apply (rule hoare_drop_imp)
      apply (rule_tac Q'="\<lambda>r. invs and not_idle_thread a" in hoare_strengthen_post)
       apply (wp rec_del_invs)
       apply (simp add: not_idle_thread_def validE_def)
       apply wp
      apply (clarsimp simp: invs_def valid_state_def valid_mdb_def)
     apply simp
    apply (clarsimp simp: not_idle_thread_def cte_wp_at_caps_of_state)
    apply (fastforce intro: caps_of_state_cteD)
   apply simp
  apply (clarsimp simp: not_idle_thread_def invs_valid_idle)
  done

lemma delete_cap_corres:
  "dcorres (dc \<oplus> dc) \<top> (cap_table_at (length b) a and invs and valid_pdpt_objs and ct_active)
     (delete_cap (transform_cslot_ptr (a, b))) (cap_delete (a, b))"
  apply (rule corres_guard_imp[OF delete_cap_corres'], simp)
  apply (clarsimp simp: cap_table_at_cte_at)
  apply (rule conjI)
   apply (clarsimp simp: emptyable_def obj_at_def is_cap_table_def)
   apply (clarsimp simp: is_tcb_def split: Structures_A.kernel_object.splits)
  apply (clarsimp simp: invs_def valid_state_def valid_idle_def pred_tcb_at_def
                        not_idle_thread_def obj_at_def is_cap_table_def)
  done


declare fun_upd_apply[simp del]

lemma opt_cap_asid_pool_Some:
  "\<lbrakk> valid_idle s; kheap s a = Some (ArchObj (arch_kernel_obj.ASIDPool pool)) \<rbrakk>
         \<Longrightarrow>  (opt_cap (a, snd (transform_asid asid)) (transform s))
    = Some (transform_asid_pool_entry (pool (ucast asid)))"
  apply (clarsimp simp:opt_cap_def transform_def slots_of_def object_slots_def
                       transform_objects_def map_add_def restrict_map_def not_idle_thread_def)
  apply (frule arch_obj_not_idle,simp)
  apply (clarsimp simp:transform_asid_pool_contents_def unat_map_def not_idle_thread_def
                       transform_asid_def)
  apply (rule unat_lt2p[where 'a="10", simplified])
  done

declare fun_upd_apply[simp]

lemmas valid_idle_invs_strg = invs_valid_idle_strg

crunch invalidate_tlb_by_asid
  for idle[wp]: "\<lambda>s. P (idle_thread s)"

lemma dcorres_unless_r:
  "\<lbrakk> \<not> G \<Longrightarrow> dcorres r P P' f g;
    G \<Longrightarrow> dcorres r Q Q' f (return ()) \<rbrakk>
  \<Longrightarrow> dcorres r (P and Q) (\<lambda>s. (\<not>G \<longrightarrow> P' s) \<and> (G \<longrightarrow> Q' s)) f (unless G g)"
  apply (cases G, simp_all add: when_def unless_def)
   apply (rule corres_guard_imp, simp+)+
  done

lemma invalidate_tlb_by_asid_dwp:
  "\<lbrace>\<lambda>a. transform a = cs\<rbrace> invalidate_tlb_by_asid aa \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  apply (simp add:invalidate_tlb_by_asid_def)
  apply (wp do_machine_op_wp|wpc)+
   apply clarsimp
   apply (wp)
  apply (rule_tac Q'="\<lambda>r s. transform s = cs" in hoare_strengthen_post)
   apply (simp add:load_hw_asid_def)
   apply (wp|clarsimp)+
  done

lemma store_pde_set_cap_corres:
  "\<lbrakk>ucast (ptr && mask pd_bits >> 2) \<in> kernel_mapping_slots \<rbrakk> \<Longrightarrow>
   dcorres dc \<top> valid_idle (return a)
      (store_pde ptr pde)"
  apply (clarsimp simp:store_pde_def get_pd_def set_pd_def set_object_def get_object_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:corres_free_fail assert_def split:Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:corres_free_fail)
  apply (frule arch_obj_not_idle)
   apply simp
  apply (simp add:not_idle_thread_def)
  apply (clarsimp simp:set_object_def return_def get_def put_def corres_underlying_def bind_def)
  apply (simp add:transform_def transform_current_thread_def)
  apply (rule ext)
  apply (clarsimp simp:transform_objects_def restrict_map_def map_add_def)
  apply (rule ext)
  apply (clarsimp simp:transform_page_directory_contents_def unat_map_def kernel_pde_mask_def )
  apply (simp add:kernel_mapping_slots_def)
  done

lemma copy_global_mappings_dwp:
  "is_aligned word pd_bits \<Longrightarrow>
   \<lbrace>\<lambda>s. valid_idle s \<and> transform s = cs\<rbrace>
   copy_global_mappings word
   \<lbrace>\<lambda>_ s. transform s = cs\<rbrace>"
  apply (simp add: copy_global_mappings_def)
  apply wp
    apply (rule_tac Q'="\<lambda>r s. valid_idle s \<and> transform s = cs" in hoare_strengthen_post)
     apply (rule mapM_x_wp')
     apply wp
       apply (rule_tac P'="\<lambda>s. valid_idle s \<and> transform s = cs" in hoare_weaken_pre)
        apply (rule dcorres_to_wp)
        apply (rule corres_guard_imp[OF store_pde_set_cap_corres])
          apply (clarsimp simp: kernel_mapping_slots_def)
          apply (simp add: pd_bits_def pageBits_def)
          apply (simp add: mask_add_aligned)
          apply (subst less_mask_eq, simp)
           apply (simp add: shiftl_t2n)
           apply (subst mult.commute)
           apply (rule div_lt_mult; simp; unat_arith; simp)
          apply (simp add: shiftl_shiftr1 word_size)
          apply (subst less_mask_eq, simp)
           apply unat_arith
          apply (subst ucast_le_migrate[symmetric])
            apply (simp add: word_size, unat_arith)
           apply (simp add: word_size)
          apply (subst ucast_ucast_len, word_bitwise; simp)
         apply clarsimp
        apply clarsimp
       apply assumption
      apply wpsimp+
  done

lemma thread_set_valid_idle:
  "\<lbrace>not_idle_thread thread and valid_idle\<rbrace> thread_set f thread \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  apply (simp add: thread_set_def not_idle_thread_def)
  apply (simp add: gets_the_def valid_idle_def)
  apply wp
  apply (rule_tac P'="not_idle_thread thread and valid_idle" in hoare_weaken_pre)
  apply (clarsimp simp: KHeap_A.set_object_def get_object_def in_monad get_def put_def bind_def obj_at_def
                        return_def valid_def not_idle_thread_def valid_idle_def pred_tcb_at_def)
  apply simp+
  apply wp
  apply (clarsimp simp:not_idle_thread_def valid_idle_def)
  done

lemma dcorres_insert_cap_combine:
  "cdl_cap = transform_cap cap \<Longrightarrow> dcorres dc \<top>
   (\<lambda>s. cte_wp_at ((=) cap.NullCap) dest s \<and> cte_at src s \<and>
        not_idle_thread (fst dest) s \<and> not_idle_thread (fst src) s \<and>
         valid_mdb s \<and> valid_idle s \<and> valid_objs s \<and> cap_aligned cap
   )
   (insert_cap_sibling cdl_cap (transform_cslot_ptr src) (transform_cslot_ptr dest)
    \<sqinter> insert_cap_child cdl_cap (transform_cslot_ptr src) (transform_cslot_ptr dest))
   (cap_insert cap src dest)"
  apply (rule dcorres_expand_pfx)
  apply clarsimp
  apply (case_tac "cte_wp_at (\<lambda>cap'. \<not> should_be_parent_of cap' (is_original_cap s' src)
    cap (cap_insert_dest_original cap cap')) src s'")
    apply (rule corres_alternate1)
    apply (rule corres_guard_imp[OF insert_cap_sibling_corres])
      apply clarsimp+
    apply (rule corres_alternate2)
    apply (rule corres_guard_imp[OF insert_cap_child_corres])
      apply clarsimp+
    apply (fastforce simp:cte_wp_at_def)
done

lemma invoke_cnode_corres:
  "translate_cnode_invocation cnodeinv = Some cdl_inv \<Longrightarrow>
   dcorres (dc \<oplus> dc) \<top>
     (valid_cnode_inv cnodeinv and invs and ct_in_state active
               and valid_pdpt_objs)
     (CNode_D.invoke_cnode cdl_inv)
     (CSpace_A.invoke_cnode cnodeinv)"
  apply (clarsimp simp: CSpace_A.invoke_cnode_def CNode_D.invoke_cnode_def
                        translate_cnode_invocation_def
                 split: Invocations_A.cnode_invocation.split_asm)
    apply (rule corres_guard_imp, rule dcorres_insert_cap_combine)
      apply (rule refl)
     apply (rule TrueI)
    apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (rule conjI)
     apply (drule ex_cte_cap_wp_to_not_idle, fastforce+)[1]
    apply (rule conjI)
     apply (clarsimp simp: valid_idle_def pred_tcb_at_def is_cap_table_def
       not_idle_thread_def obj_at_def dest!:invs_valid_idle)
    apply (fastforce simp:not_idle_thread_def)
   apply (rule corres_guard_imp, rule move_cap_corres)
    apply simp
   apply (clarsimp simp: cte_wp_at_caps_of_state not_idle_thread_def
                  elim!: ex_cte_cap_wp_to_weakenE)
   apply (subgoal_tac "valid_idle s")
    apply (auto simp: valid_idle_def pred_tcb_at_def obj_at_def is_obj_defs)[1]
   apply fastforce
  apply (rule corres_guard_imp[OF delete_cap_corres])
   apply (simp+)[2]
  done

lemma lookup_slot_for_cnode_op_corres:
  "\<lbrakk> idx = of_bl idx'; length idx' = 32; cnode_cap' = transform_cap cnode_cap;depth = depth'  \<rbrakk> \<Longrightarrow>
  dcorres (dc \<oplus> (\<lambda>p p'. p = transform_cslot_ptr p'))
    \<top>
    (valid_objs and valid_cap cnode_cap and valid_global_refs and valid_idle)
    (CSpace_D.lookup_slot_for_cnode_op cnode_cap' idx depth)
    (CSpace_A.lookup_slot_for_cnode_op b cnode_cap idx' depth')"
  apply (simp add: CSpace_D.lookup_slot_for_cnode_op_def
                   CSpace_A.lookup_slot_for_cnode_op_def
                   cdl_resolve_address_bits_error_branch1)
  apply (rule conjI)
   prefer 2
   apply (cases "depth = 0 \<or> word_bits < depth", simp)
   apply (simp add: fault_to_except_def throw_handle)
  apply (clarsimp simp: word_bits_def)
  apply (rule whenE_throwError_corres_initial, simp, rule refl)
  apply (simp add: fault_to_except_def lookup_error_on_failure_def)
  apply (rule corres_handle2')
  apply (rule corres_initial_splitE [where Q="\<lambda>_. \<top>" and Q'="\<lambda>_. \<top>"])
     apply (rule corres_handle2)
     apply (subst cdl_resolve_address_bits_eq [rule_format])
      prefer 2
      apply (rule resolve_address_bits_corres)
        apply simp
       apply (rule refl)
      apply clarsimp
     apply simp
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (rule corres_returnOk, rule refl)
    apply (clarsimp simp: neq_Nil_conv)
   apply wp+
  done

lemma dcorres_ensure_empty:
  "dcorres (dc\<oplus>dc) \<top>  (valid_idle and not_idle_thread (fst slot))
    (CSpace_D.ensure_empty (transform_cslot_ptr slot)) (ensure_empty slot)"
  apply (clarsimp simp: CSpace_D.ensure_empty_def ensure_empty_def liftE_bindE unlessE_whenE)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule get_cap_corres; simp)
      apply (rule corres_whenE)
        apply (simp add:transform_cap_def split:cap.splits arch_cap.splits)
       apply (rule dcorres_free_throw)
  by wpsimp+

lemma cdt_transform:
  "cdl_cdt (transform s) = map_lift_over transform_cslot_ptr (cdt s)"
  by (simp add: transform_def transform_cdt_def)

lemma dcorres_ensure_no_children:
  "dcorres (dc \<oplus> (=)) \<top>
           (\<lambda>s. mdb_cte_at (swp (cte_wp_at P) s) (cdt s) \<and> cte_at slot s)
           (CSpace_D.ensure_no_children (transform_cslot_ptr slot))
           (ensure_no_children slot)"
  apply (simp add: ensure_no_children_def CSpace_D.ensure_no_children_def)
  apply (clarsimp simp: corres_underlying_def return_def in_monad bindE_def lift_def)
  apply (clarsimp simp: liftE_def simpler_gets_def lift_def whenE_def
                        bind_def return_def throwError_def returnOk_def)
  apply (simp add: has_children_def KHeap_D.is_cdt_parent_def)
  apply (frule transform_cdt_slot_inj_on_mdb_cte_at)
  apply (simp add: transform_def transform_cdt_def)
  apply (case_tac "\<exists>slot'. cdt b slot' = Some slot")
   apply (clarsimp simp: map_lift_over_eq_Some)
   apply (cases slot)
   apply (simp add: transform_cslot_ptr_def)
   apply fastforce
  apply clarsimp
  apply (clarsimp simp: map_lift_over_eq_Some)
  apply (cases slot)
  apply (simp add: transform_cslot_ptr_def)
  apply (clarsimp simp: eq_nat_nat_iff bl_to_bin_ge0)
  apply (drule bl_to_bin_inj)
   apply (clarsimp simp: mdb_cte_at_def)
   apply (erule allE, erule allE, erule allE, erule allE, erule (1) impE)
   apply (clarsimp simp: cte_wp_at_cases)
   apply (erule disjE)
    apply clarsimp
    apply (drule (1) wf_cs_nD)+
    apply simp
   apply clarsimp
   apply (thin_tac "P \<or> Q" for P Q)
   apply (clarsimp simp: tcb_cap_cases_def tcb_cnode_index_def split: if_splits)
  apply simp
  done

lemmas dcorres_returnOk' = dcorres_returnOk [THEN corres_guard_imp [OF _ TrueI TrueI]]

lemma derive_cap_dcorres:
  "cap' = transform_cap cap \<Longrightarrow>
   dcorres (dc \<oplus> (\<lambda>c c'. c = transform_cap c')) \<top>
           (\<lambda>s. mdb_cte_at (swp (cte_wp_at P) s) (cdt s) \<and> cte_at slot s)
           (CSpace_D.derive_cap (transform_cslot_ptr slot) cap')
           (CSpace_A.derive_cap slot cap)"
  unfolding CSpace_D.derive_cap_def derive_cap_def
  apply (cases cap, simp_all add: dcorres_returnOk')
   \<comment> \<open>Untyped\<close>
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE[where r' = "(=)"])
        apply (rule dcorres_ensure_no_children)
       apply (rule dcorres_returnOk)
       apply simp
      apply wp
     apply wp
    apply simp
   apply fastforce
  apply (simp add: arch_derive_cap_def)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap, simp_all add: dcorres_returnOk')
    apply (rule dcorres_returnOk')
    apply (clarsimp simp:transform_mapping_def)
   apply (fastforce intro: corres_alternate1 corres_alternate2 dcorres_returnOk'
                   split: option.splits)+
  done

lemma derive_cap_Null [simp]:
  "CSpace_D.derive_cap slot cdl_cap.NullCap = returnOk cdl_cap.NullCap"
  by (simp add: CSpace_D.derive_cap_def)

lemma transform_cap_rights_update [simp]:
  "transform_cap (cap_rights_update R cap) =
   update_cap_rights R (transform_cap cap)"
  apply (simp add: cap_rights_update_def update_cap_rights_def)
  apply (clarsimp simp: transform_cap_def acap_rights_update_def
                  split: cap.splits arch_cap.splits)
  done

lemma update_cap_rights_transform [simp]:
  "update_cap_rights (Types_D.cap_rights (transform_cap cap) \<inter> R) (transform_cap cap) =
  update_cap_rights (Structures_A.cap_rights cap \<inter> R) (transform_cap cap)"
  apply (simp add: update_cap_rights_def transform_cap_def)
  apply (auto simp: Types_D.cap_rights_def split: cap.splits arch_cap.splits)
  done

lemma dcorres_update_cap_data:
  "cap = transform_cap cap' \<Longrightarrow>
   dcorres (\<lambda>c c'. c = transform_cap c') \<top>
    (valid_idle and valid_cap cap')
  (CSpace_D.update_cap_data preserve data cap)
  (return (CSpace_A.update_cap_data preserve data cap'))"
  apply (unfold CSpace_D.update_cap_data_def)
  apply (simp add:gets_the_def gets_def bind_assoc)
  apply (case_tac cap')
             apply (simp_all add:transform_cap_def update_cap_data_def is_cap_simps Let_def)
     apply (simp add: CSpace_D.badge_update_def update_cap_badge_def
                      Structures_A.badge_update_def Types_D.badge_bits_def)
    apply (simp add: CSpace_D.badge_update_def update_cap_badge_def
                     Structures_A.badge_update_def Types_D.badge_bits_def)
   apply (simp add:  bind_assoc gets_the_def gets_def the_cnode_cap_def)
   apply (clarsimp simp:word_bits_def dest!:leI)
   apply (simp add:of_drop_to_bl)
   apply (simp add:mask_twice)
   apply (clarsimp simp:word_size word_bits_def)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap, simp_all add: arch_update_cap_data_def)
  done

lemma dcorres_update_cap_data_bind:
  "\<lbrakk>cap = transform_cap cap' ; \<And>c'. dcorres r P P' (f (transform_cap c')) (f' c') \<rbrakk> \<Longrightarrow>
   dcorres r P (valid_idle and valid_cap cap' and P')
           ((CSpace_D.update_cap_data b data cap) >>= f)
           (f' (CSpace_A.update_cap_data b data cap'))"
  apply (subst return_bind [symmetric, where f=f'])
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule dcorres_update_cap_data, simp)
      apply simp
      apply assumption
     apply (clarsimp simp: CSpace_D.update_cap_data_def)
     apply (wp | wpc)+
   apply simp
  apply simp
  done

lemma lsfco_not_idle:
  "\<lbrace>valid_objs and valid_cap cap and valid_idle\<rbrace>
   CSpace_A.lookup_slot_for_cnode_op b cap idx depth
   \<lbrace>\<lambda>rv. not_idle_thread (fst rv)\<rbrace>, -"
  apply (rule_tac Q'="\<lambda>rv. real_cte_at rv and valid_idle" in hoare_strengthen_postE_R)
   apply (rule hoare_pre, wp)
   apply simp
  apply (clarsimp simp: obj_at_def not_idle_thread_def valid_idle_def
                        pred_tcb_at_def is_cap_table_def)
  done

lemma get_index_Nil [simp]:
  "get_index [] n = None"
  by (simp add: get_index_def)

lemma throw_on_none [simp]:
  "throw_on_none None = Monads_D.throw"
  by (simp add: throw_on_none_def)

lemma cnode_decode_throw:
  "\<lbrakk> transform_intent (invocation_type label) args = Some (CNodeIntent ui);
    invocation_type label = GenInvocationLabel CNodeCopy \<or>
    invocation_type label = GenInvocationLabel CNodeMint \<or>
    invocation_type label = GenInvocationLabel CNodeMove \<or>
    invocation_type label = GenInvocationLabel CNodeMutate \<rbrakk> \<Longrightarrow>
  CNode_D.decode_cnode_invocation target target_ref [] ui = Monads_D.throw"
  apply (auto simp: CNode_D.decode_cnode_invocation_def transform_intent_def
                    transform_intent_cnode_copy_def
                    transform_intent_cnode_mint_def
                    transform_intent_cnode_move_def
                    transform_intent_cnode_mutate_def
              split: list.splits)
  done

lemma corres_bindE_throwError:
  assumes f:"\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  assumes nf: "sf \<Longrightarrow> no_fail P' f"
  shows "corres_underlying sr af sf (dc \<oplus> r) P P' (Monads_D.throw) (doE x \<leftarrow> f; throwError (e x) odE)"
  apply (clarsimp simp: corres_underlying_def)
  apply (rule conjI)
   apply (clarsimp simp: in_monad bindE_def throwError_def return_def)
   apply (drule_tac P="(=) b" in use_valid [OF _ f], simp)
   apply (clarsimp simp: lift_def throwError_def return_def split: sum.splits)
  apply (rule impI, drule nf)
  apply (simp add: no_fail_def)
  apply (clarsimp simp: bindE_def bind_def throwError_def return_def lift_def split: sum.splits)
  done

lemma decode_cnode_corres:
  notes defns = transform_intent_def unlessE_whenE
                CNode_D.decode_cnode_invocation_def
                Decode_A.decode_cnode_invocation_def
                transform_intent_cnode_copy_def
                transform_intent_cnode_move_def
                transform_intent_cnode_mutate_def
                transform_intent_cnode_mint_def
                transform_cap_list_def get_index_def
                throw_on_none_def
                transform_cnode_index_and_depth_def
                gen_invocation_type_eq and
         splits = gen_invocation_labels.split_asm invocation_label.split_asm
                  arch_invocation_label.split_asm list.split_asm
  shows
  "\<lbrakk> Some (CNodeIntent ui) = transform_intent (invocation_type label') args';
     cap = transform_cap cap';
     cap' = Structures_A.CNodeCap word n x;
     slot = transform_cslot_ptr slot';
     excaps = transform_cap_list  excaps' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> (\<lambda>x y. translate_cnode_invocation y = Some x)) \<top>
     (invs and valid_cap cap' and (\<lambda>s. \<forall>e\<in>set excaps'. valid_cap (fst e) s))
     (CNode_D.decode_cnode_invocation cap slot excaps ui)
     (Decode_A.decode_cnode_invocation label' args' cap' (map fst excaps'))"
  apply (drule_tac s="Some x" for x in sym)
  apply (rule_tac label=label' and args=args' and exs="map fst excaps'"
              in decode_cnode_cases2)
        apply (clarsimp simp: defns split: splits)
           apply (rule corres_guard_imp)
             apply (rule corres_splitEE)
                apply (rule lookup_slot_for_cnode_op_corres)
                   apply simp
                  apply simp
                 apply simp
                apply (rule refl)
               apply (rule corres_splitEE)
                  apply simp
                  apply (rule dcorres_ensure_empty)
                 apply (rule corres_splitEE)
                    apply (rule lookup_slot_for_cnode_op_corres, simp_all)[1]
                   apply (simp add:liftE_bindE)
                   apply (rule corres_split)
                      apply (rule get_cap_corres, rule refl)
                     apply (rule_tac R="src_capa = cap.NullCap" in corres_cases [where P=\<top> and P'=\<top>])
                      apply (simp add: update_cap_rights_def)
                     apply simp
                     apply (rule corres_splitEE)
                        apply (rule derive_cap_dcorres)
                        apply (simp add: mask_cap_def)
                       apply (rule corres_splitEE[where r'=dc])
                          apply (rule corres_whenE, simp)
                           apply (rule dcorres_throw)
                          apply simp
                         apply (rule dcorres_returnOk)
                         apply (simp add: translate_cnode_invocation_def)
                        apply ((wp hoare_drop_imps get_cap_wellformed lsfco_not_idle|simp)+)
           apply (subgoal_tac "valid_mdb s")
            prefer 2
            apply fastforce
           apply (fastforce simp: valid_mdb_def mdb_cte_at_def)
          \<comment> \<open>Mint\<close>
          apply (rule corres_guard_imp)
            apply (rule corres_splitEE)
               apply (rule lookup_slot_for_cnode_op_corres; simp)
              apply simp
              apply (rule corres_splitEE[OF dcorres_ensure_empty])
                apply (rule corres_splitEE)
                   apply (rule lookup_slot_for_cnode_op_corres; simp)
                  apply (simp add:liftE_bindE)
                  apply (rule corres_split)
                     apply (rule get_cap_corres; simp)
                    apply (rule_tac R="src_capa = cap.NullCap"
                             in corres_cases [where P=\<top> and P'=\<top>])
                     apply (simp add:update_cap_rights_def CSpace_D.update_cap_data_def)
                    apply simp
                    apply (rule dcorres_update_cap_data_bind[where P = \<top>])
                     apply (simp add:mask_cap_def)
                    apply (rule corres_splitEE[where Q = \<top> and R = "\<lambda>r. \<top>", simplified])
                       apply (rule derive_cap_dcorres; simp)
                      apply (rule corres_splitEE[where r' = dc and Q = \<top>,simplified])
                         apply (rule corres_whenE[where P = \<top>,simplified])
                           apply simp
                          apply (rule dcorres_throw)
                         apply simp
                        apply (rule dcorres_returnOk)
                        apply (simp add:translate_cnode_invocation_def)
                       apply wp+
                    apply (rule hoare_strengthen_postE_R[OF validE_validE_R])
                     apply (rule hoareE_TrueI[where P = \<top>])
                    apply (wp|simp)+
                  apply (strengthen mask_cap_valid)
                  apply (wp lsfco_not_idle hoareE_TrueI[where P = \<top>] |simp)+
          apply (subgoal_tac "valid_mdb s")
           apply (fastforce simp: valid_mdb_def mdb_cte_at_def)
          apply fastforce

         \<comment> \<open>Move\<close>
         apply (rule corres_guard_imp)
           apply (rule corres_splitEE)
              apply (rule lookup_slot_for_cnode_op_corres)
                 apply simp
                apply simp
               apply simp
              apply (rule refl)
             apply (rule corres_splitEE)
                apply simp
                apply (rule dcorres_ensure_empty)
               apply (rule corres_splitEE)
                  apply (rule lookup_slot_for_cnode_op_corres, simp_all)[1]
                 apply (simp add:liftE_bindE)
                 apply (rule corres_split)
                    apply (rule get_cap_corres, rule refl)
                   apply (rule_tac R="src_capa = cap.NullCap" in corres_cases [where P=\<top> and P'=\<top>])
                    apply simp
                   apply simp
                   apply (rule_tac P="\<top>" and P'="K (wellformed_cap src_capa)" in corres_returnOk)
                   apply (simp add: translate_cnode_invocation_def all_rights_def)
                  apply ((wp hoare_drop_imps get_cap_wellformed lsfco_not_idle|simp)+)
         apply fastforce

        \<comment> \<open>Mutate\<close>
        apply (rule corres_guard_imp)
          apply (rule corres_splitEE)
             apply (rule lookup_slot_for_cnode_op_corres; simp)
            apply simp
            apply (rule corres_splitEE[OF dcorres_ensure_empty])
              apply (rule corres_splitEE)
                 apply (rule lookup_slot_for_cnode_op_corres; simp)
                apply (simp add:liftE_bindE)
                apply (rule corres_split)
                   apply (rule get_cap_corres; simp)
                  apply (rule_tac R="src_capa = cap.NullCap" in corres_cases [where P=\<top> and P'=\<top>])
                   apply (simp add:update_cap_rights_def
                       CSpace_D.update_cap_data_def)
                  apply simp
                  apply (rule_tac F="wellformed_cap src_capa" in corres_gen_asm2)
                  apply (simp add: all_rights_def)
                  apply (rule dcorres_update_cap_data_bind)
                   apply (simp)
                  apply (rule whenE_throwError_corres_initial)
                    apply simp
                   apply simp
                  apply (rule dcorres_returnOk)
                  apply (simp add:translate_cnode_invocation_def)
                 apply simp
                apply (wp get_cap_wellformed
                  lsfco_not_idle hoareE_TrueI[where P = \<top>] | simp)+
        apply (subgoal_tac "valid_mdb s")
         apply (fastforce simp: valid_mdb_def mdb_cte_at_def)
        apply fastforce

       \<comment> \<open>Revoke\<close>
       apply (simp add: transform_intent_def flip: gen_invocation_type_eq)
      \<comment> \<open>Delete\<close>
      apply (clarsimp simp: defns split: splits)
      apply (rule corres_guard_imp)
        apply (rule corres_splitEE)
           apply (rule lookup_slot_for_cnode_op_corres, simp_all)[1]
          apply (rule dcorres_returnOk)
          apply (simp add: translate_cnode_invocation_def)
         apply (wp+)[2]
       apply simp
      apply fastforce
     \<comment> \<open>SaveCaller\<close>
     apply (simp add: transform_intent_def flip: gen_invocation_type_eq)
    \<comment> \<open>CancelBadgedSends\<close>
    apply (simp add: transform_intent_def flip: gen_invocation_type_eq)
   \<comment> \<open>Rotate\<close>
   apply (simp add: transform_intent_def flip: gen_invocation_type_eq)
  apply (erule disjE)
   apply (simp add: transform_intent_def upto_enum_def toEnum_def fromEnum_def
                    enum_gen_invocation_labels enum_invocation_label gen_invocation_type_eq
               split: gen_invocation_labels.splits invocation_label.splits arch_invocation_label.splits)
  apply (erule disjE)
   apply (simp add: defns split: splits)
  apply (erule disjE)
   apply (simp add: defns split: splits)
  apply clarsimp
  apply (erule disjE)
   apply clarsimp
   apply (case_tac args'a)
    apply clarsimp
    apply (simp add: upto_enum_def toEnum_def fromEnum_def
                     enum_invocation_label enum_gen_invocation_labels)
    apply (simp add: defns split: splits)
   apply clarsimp
   apply (case_tac list)
    apply clarsimp
    apply (simp add: defns split: splits)
   apply clarsimp
   apply (case_tac excaps', simp_all)[1]
   apply (clarsimp simp: Decode_A.decode_cnode_invocation_def unlessE_whenE)
   apply (simp add: upto_enum_def toEnum_def fromEnum_def
                    enum_invocation_label enum_gen_invocation_labels
               flip: gen_invocation_type_eq)
   apply (clarsimp simp: cnode_decode_throw transform_cap_list_def)
   apply (rule corres_bindE_throwError, wp, simp)
  apply (clarsimp simp: transform_intent_def transform_cnode_index_and_depth_def
                  simp flip: gen_invocation_type_eq
                  split: list.splits)
  done

lemma decode_cnode_label_not_match:
  "\<lbrakk>Some intent = transform_intent (invocation_type label) args; \<forall>ui. intent \<noteq> CNodeIntent ui;
    intent \<noteq> OtherIntent\<rbrakk>
   \<Longrightarrow> \<lbrace>(=) s\<rbrace> Decode_A.decode_cnode_invocation label args (cap.CNodeCap a b c) (e) \<lbrace>\<lambda>r. \<bottom>\<rbrace>, \<lbrace>\<lambda>e. (=) s\<rbrace>"
  apply (case_tac "invocation_type label = GenInvocationLabel CNodeRevoke")
   apply (clarsimp simp:transform_intent_def)
  apply (case_tac "invocation_type label = GenInvocationLabel CNodeDelete")
   apply (clarsimp simp:Decode_A.decode_untyped_invocation_def transform_intent_def)
   apply (clarsimp simp:transform_cnode_index_and_depth_def split:option.splits list.splits)
  apply (case_tac "invocation_type label = GenInvocationLabel CNodeCancelBadgedSends")
   apply (clarsimp simp:transform_intent_def)
  apply (case_tac "invocation_type label = GenInvocationLabel CNodeCopy")
   apply (clarsimp simp:Decode_A.decode_untyped_invocation_def transform_intent_def)
   apply (clarsimp simp:transform_intent_cnode_copy_def split:option.splits list.splits)
  apply (case_tac "invocation_type label = GenInvocationLabel CNodeMint")
   apply (clarsimp simp:Decode_A.decode_untyped_invocation_def transform_intent_def)
   apply (clarsimp simp:transform_intent_cnode_mint_def split:option.splits list.splits)
  apply (case_tac "invocation_type label = GenInvocationLabel CNodeMove")
   apply (clarsimp simp:Decode_A.decode_untyped_invocation_def transform_intent_def)
   apply (clarsimp simp:transform_intent_cnode_move_def split:option.splits list.splits)
  apply (case_tac "invocation_type label = GenInvocationLabel CNodeMutate")
   apply (clarsimp simp:Decode_A.decode_untyped_invocation_def transform_intent_def)
   apply (clarsimp simp:transform_intent_cnode_mutate_def split:option.splits list.splits)
  apply (case_tac "invocation_type label = GenInvocationLabel CNodeRotate")
   apply (clarsimp simp:transform_intent_def)
  apply (case_tac "invocation_type label = GenInvocationLabel CNodeSaveCaller")
   apply (clarsimp simp:transform_intent_def)
  apply (clarsimp simp:Decode_A.decode_cnode_invocation_def unlessE_def)
  apply (subgoal_tac "\<not> gen_invocation_type label \<in> set [CNodeRevoke .e. CNodeSaveCaller]")
   apply (clarsimp simp: gen_invocation_type_eq)
   apply wp
  apply (clarsimp simp: upto_enum_def fromEnum_def toEnum_def enum_invocation_label
                        enum_gen_invocation_labels gen_invocation_type_eq)
  done

end

end
