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
  translate_cnode_invocation :: "Invocations_A.cnode_invocation \<Rightarrow> cdl_cnode_invocation"
where
 "translate_cnode_invocation x \<equiv> case x of
    Invocations_A.InsertCall cap src_slot dest_slot
       \<Rightarrow> Invocations_D.InsertCall (transform_cap cap)
              (transform_cslot_ptr src_slot) (transform_cslot_ptr dest_slot)
  | Invocations_A.MoveCall cap src_slot dest_slot
       \<Rightarrow> Invocations_D.MoveCall (transform_cap cap)
              (transform_cslot_ptr src_slot) (transform_cslot_ptr dest_slot)
  | Invocations_A.RevokeCall slot \<Rightarrow> Invocations_D.RevokeCall (transform_cslot_ptr slot)
  | Invocations_A.DeleteCall slot \<Rightarrow> Invocations_D.DeleteCall (transform_cslot_ptr slot)
  | Invocations_A.SaveCall slot \<Rightarrow> Invocations_D.SaveCall (transform_cslot_ptr slot)
  | Invocations_A.CancelBadgedSendsCall cap \<Rightarrow> Invocations_D.CancelBadgedSendsCall (transform_cap cap)
  | Invocations_A.RotateCall cap1 cap2 slot1 slot2 slot3
       \<Rightarrow> Invocations_D.RotateCall (transform_cap cap1) (transform_cap cap2)
              (transform_cslot_ptr slot1) (transform_cslot_ptr slot2)
              (transform_cslot_ptr slot3)"

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
               erule subset_inj_on, fastforce)+
             apply (simp add: map_option_is_None[THEN trans [OF eq_commute]]
               fun_eq_iff del: inj_on_insert)
             apply (subst eq_commute [where a=None])
             apply (subst map_lift_over_f_eq map_lift_over_upd,
               erule subset_inj_on, fastforce)+
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
                 erule subset_inj_on, fastforce)+
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

lemma reply_cap_insert_corres:
  "sid \<noteq> did\<Longrightarrow>dcorres dc \<top>
    (valid_idle and not_idle_thread did and valid_mdb and st_tcb_at (\<lambda>r. \<not> inactive r \<and> \<not> idle r) sid
     and tcb_at did and tcb_at sid and valid_objs)
    (insert_cap_child (cdl_cap.ReplyCap sid rights)  (sid, tcb_replycap_slot)
      (did, tcb_caller_slot))
    (cap_insert (cap.ReplyCap sid False rights) (sid,tcb_cnode_index 2) (did,tcb_cnode_index 3))"
  apply (rule corres_guard_imp)
  apply (rule insert_cap_child_corres [where cap = "cap.ReplyCap sid False rights"
      and src = "(sid, tcb_cnode_index 2)" and child = "(did, tcb_cnode_index 3)",
      unfolded transform_cap_def transform_tcb_slot_simp
      ,simplified])
   apply clarsimp+
  apply (frule st_tcb_at_reply_cap_valid)
   apply simp+
  apply (frule tcb_caller_cap)
   apply simp+
  apply (clarsimp simp:cte_wp_at_caps_of_state should_be_parent_of_def)
  apply (clarsimp simp: word_bits_def is_master_reply_cap_def
   split:cap.splits)
  apply (rule conjI)
   apply (drule caps_of_state_cteD)+
   apply (frule(1) cte_wp_tcb_cap_valid)
     apply (clarsimp simp:valid_mdb_def reply_master_revocable_def)
     apply (drule_tac x = "sid" in spec)
     apply (drule_tac x = "tcb_cnode_index 2" in spec)
     apply (clarsimp simp:cte_wp_at_caps_of_state is_master_reply_cap_def)
  apply (drule caps_of_state_cteD)+
  apply (frule(1) cte_wp_tcb_cap_valid[where p = "(did,tcb_cnode_index 3)"])
  apply (rule conjI)
   apply (clarsimp simp:valid_idle_def not_idle_thread_def)
   apply (clarsimp simp:pred_tcb_at_def2 obj_at_def)
  apply (clarsimp simp:tcb_at_def dest!:get_tcb_SomeD)
  apply (drule cte_wp_valid_cap)
   apply simp
  apply (simp add:valid_cap_def cap_aligned_def)
  done

lemma cap_move_swap_ext_def:
  "(cap_move new_cap src_slot dest_slot :: (unit, unit) s_monad)=
    do CSpaceAcc_A.set_cap new_cap dest_slot;
   CSpaceAcc_A.set_cap cap.NullCap src_slot;
   src_p \<leftarrow> gets (\<lambda>s. cdt s src_slot);
   dest_p \<leftarrow> gets (\<lambda>s. cdt s dest_slot);
   cdt \<leftarrow> gets cdt;
   parent \<leftarrow> return $ cdt src_slot;
   cdt' \<leftarrow> return $ cdt(dest_slot := parent, src_slot := None);
   set_cdt
    (\<lambda>r. if cdt' r = Some src_slot then Some dest_slot
         else cdt' r);
   is_original \<leftarrow> gets is_original_cap;
   set_original dest_slot (is_original src_slot);
   set_original src_slot False;
      do_extended_op
    (cap_move_ext src_slot dest_slot src_p dest_p)
od"
  unfolding cap_move_def
  apply (simp add: set_original_def gets_fold_into_modify)
  done

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
    apply (simp add: cap_move_def move_cap_def cap_move_swap_ext_def swap_parents_def
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
            apply (erule subset_inj_on, auto elim!: ranE split: if_split_asm)[1]
           apply (rule sym)
           apply (simp add: Fun.swap_def split del: if_split)
           apply (subst map_lift_over_upd[unfolded fun_upd_def],
                    ((erule subset_inj_on, auto elim!: ranE split: if_split_asm)[1]))+
           apply (rule ext)
           apply (cases p, cases p')
           apply (simp split del: if_split)
           apply simp
           apply (subst subset_inj_on map_lift_over_f_eq[OF subset_inj_on],
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

lemma cap_null_reply_case_If:
  "(case cap of cap.ReplyCap t b R \<Rightarrow> f t b R | cap.NullCap \<Rightarrow> g | _ \<Rightarrow> h)
        = (if cap = cap.NullCap then g
           else if is_reply_cap cap \<or> is_master_reply_cap cap
           then f (obj_ref_of cap) (is_master_reply_cap cap) (cap_rights cap)
           else h)"
  by (simp add: is_reply_cap_def is_master_reply_cap_def split: cap.split)

(* FIXME: move *)
lemma corres_if_rhs2:
  "\<lbrakk> G \<Longrightarrow> corres_underlying sr nf nf' rvr P Q a b;
      \<not> G \<Longrightarrow> corres_underlying sr nf nf' rvr P' Q' a c \<rbrakk>
     \<Longrightarrow> corres_underlying sr nf nf' rvr (P and P') (\<lambda>s. (G \<longrightarrow> Q s) \<and> (\<not> G \<longrightarrow> Q' s))
        a (if G then b else c)"
  by (rule corres_guard_imp, rule corres_if_rhs, simp+)

lemma delete_cap_corres:
  "dcorres (dc \<oplus> dc) (\<lambda>_. True) (cap_table_at (length b) a and invs
                                     and valid_pdpt_objs and ct_active)
             (delete_cap (transform_cslot_ptr (a, b))) (cap_delete (a, b))"
  apply (simp add:delete_cap_def cap_delete_def)
  apply (subst rec_del_simps_ext)
  apply (simp add:bindE_assoc)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE[OF dcorres_finalise_slot])
      apply (clarsimp simp:bindE_assoc when_def)
      apply (rule empty_slot_corres)
     apply wp+
    apply (rule validE_validE_R)
    apply (simp add:validE_def weak_valid_mdb_def)
    apply (rule hoare_drop_imp)
    apply (rule_tac Q'="\<lambda>r. invs and not_idle_thread a" in hoare_strengthen_post)
     apply (wp rec_del_invs)
     apply (simp add:not_idle_thread_def validE_def)
     apply wp
    apply (clarsimp simp:invs_def valid_state_def valid_mdb_def)
   apply clarsimp+
  apply (simp add:cap_table_at_cte_at)
  apply (clarsimp simp:emptyable_def obj_at_def is_cap_table_def)
  apply (clarsimp simp:is_tcb_def split:Structures_A.kernel_object.splits)
  apply (clarsimp simp:invs_def valid_state_def)
  apply (drule cnode_not_idle,simp)
  apply (simp add:not_idle_thread_def)
  done

lemma delete_cap_corres':
  "dcorres (dc \<oplus> dc) (\<lambda>_. True) (cte_at (a,b) and invs and emptyable (a,b)
                                     and not_idle_thread a and valid_pdpt_objs)
             (delete_cap (transform_cslot_ptr (a, b))) (cap_delete (a, b))"
  apply (simp add:delete_cap_def cap_delete_def)
  apply (subst rec_del_simps_ext)
  apply (simp add:bindE_assoc)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE[OF dcorres_finalise_slot])
      apply (clarsimp simp:bindE_assoc when_def)
      apply (rule empty_slot_corres)
     apply wp+
    apply (rule validE_validE_R)
    apply (simp add:validE_def weak_valid_mdb_def)
    apply (rule hoare_drop_imp)
    apply (rule_tac Q'="\<lambda>r. invs and not_idle_thread a" in hoare_strengthen_post)
     apply (wp rec_del_invs)
     apply (simp add:not_idle_thread_def validE_def)
     apply wp
    apply (clarsimp simp:invs_def valid_state_def valid_mdb_def)
   apply (clarsimp simp:not_idle_thread_def)+
  done

definition boolean_exception :: "'c + bool \<Rightarrow> 'a+'b \<Rightarrow> bool"
where "boolean_exception r r' \<equiv> case r' of Inr a \<Rightarrow> r = Inr True | Inl a \<Rightarrow> r = Inr False \<or> (\<exists>k. r = Inl k)"

lemma boolean_exception_corres:
  "\<lbrakk>dcorres (boolean_exception) P P' a b\<rbrakk>
    \<Longrightarrow> dcorres (dc\<oplus>dc) P P' (doE r \<leftarrow> a; unlessE r Monads_D.throw odE) b"
  apply (clarsimp simp:bindE_def lift_def unlessE_def corres_underlying_def bind_def)
  apply (erule allE, erule impE, rule conjI, assumption, assumption)
  apply (drule_tac x = "(aa,baa)" in bspec)
   apply simp
  apply clarsimp
  apply (rule bexI)
   prefer 2
   apply assumption
  apply (clarsimp simp: boolean_exception_def validE_def valid_def lift_def
                        throwError_def returnOk_def return_def
                  split: sum.splits)
  done

lemma cdl_Null_descendants:
  "\<lbrakk>cte_wp_at ((=) cap.NullCap) slot' s';valid_mdb s'\<rbrakk>
   \<Longrightarrow> KHeap_D.descendants_of (transform_cslot_ptr slot') (transform s') = {}"
  apply (subst descendants_of_eqv,clarsimp simp:valid_mdb_def,simp)
  apply (erule cte_wp_at_weakenE,simp_all)
  apply (erule mdb_Null_descendants,simp)
done

lemma empty_set_eq: "{x. False} = {}"
  by auto


lemma preemption_corres:
  "dcorres (dc \<oplus> dc) P P'
       (Monads_D.throw \<sqinter> returnOk x)
       preemption_point"
  apply (simp add: preemption_point_def)
  apply (auto simp: preemption_point_def o_def gets_def liftE_def whenE_def getActiveIRQ_def
                    corres_underlying_def select_def bind_def get_def bindE_def select_f_def modify_def
                    alternative_def throwError_def returnOk_def return_def lift_def
                    put_def do_machine_op_def
                    update_work_units_def wrap_ext_bool_det_ext_ext_def work_units_limit_def
                    work_units_limit_reached_def OR_choiceE_def reset_work_units_def mk_ef_def
           split: option.splits kernel_object.splits)
  done

lemma in_monad_cap_delete_invs:
  "\<lbrakk> invs sfix;slot \<in> CSpaceAcc_A.descendants_of slot' (cdt sfix);
     (r, s) \<in> fst (cap_delete slot sfix)\<rbrakk>
  \<Longrightarrow> invs s"
  using cap_delete_invs[unfolded valid_def,simplified]
  apply clarsimp
  apply (case_tac slot)
  apply (drule_tac x = a in meta_spec)
  apply (drule_tac x = b in meta_spec)
  apply (drule_tac x = sfix in spec)
  apply (clarsimp simp:emptyable_def)
  apply (auto simp:reply_slot_not_descendant)
done

lemma descendants_emptyable:
  "\<lbrakk>invs s; slot \<in> CSpaceAcc_A.descendants_of slot' (cdt s)\<rbrakk> \<Longrightarrow> emptyable slot s"
  apply (case_tac slot)
  apply (clarsimp simp:emptyable_def st_tcb_at_def obj_at_def is_tcb_def)
  apply (clarsimp split:Structures_A.kernel_object.splits)
  apply (frule reply_slot_not_descendant)
    apply (simp add:tcb_at_def)
    apply (rule exI)
    apply (erule get_tcb_rev)
  apply fastforce
done

lemma descendants_not_idle:
  "\<lbrakk> invs sfix; (a, b) \<in> CSpaceAcc_A.descendants_of slot' (cdt sfix)\<rbrakk>
         \<Longrightarrow> not_idle_thread a sfix"
  apply (clarsimp simp:not_idle_thread_def invs_def valid_state_def valid_mdb_def valid_pspace_def)
  apply (frule descendants_not_null_cap)
    apply simp
  apply (frule obj_ref_not_idle)
   apply simp+
  apply (erule cte_wp_at_weakenE)
    apply simp
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (frule valid_idle_has_null_cap)
    apply simp+
done

lemma valid_pdpt_objs_irq_state_independent[intro!, simp]:
  "valid_pdpt_objs (s \<lparr> machine_state := machine_state s \<lparr> irq_state := f (irq_state (machine_state s)) \<rparr> \<rparr> )
   = valid_pdpt_objs s"
  by (simp add: obj_valid_pdpt_def)

lemma cdt_machine_state_independent[intro!, simp]:
  "cdt (update_machine x s) = cdt s"
  by (simp)

lemma cte_wp_at_machine_state[simp]:
  "update_machine z s = s' \<Longrightarrow> cte_wp_at x y s' = cte_wp_at x y s"
  by (drule sym, simp add: cte_wp_at_def)

lemma valid_mdb_machine_state[simp]:
  "update_machine z s = s' \<Longrightarrow> valid_mdb s' = valid_mdb s"
  by (drule sym, simp add: valid_mdb_def swp_def)

lemma valid_idle_machine_state[simp]:
  "update_machine z s = s' \<Longrightarrow> valid_idle s' = valid_idle s"
  by (drule sym, simp add: valid_idle_def)

lemma not_idle_thread_machine_state[simp]:
  "update_machine z s  = s'\<Longrightarrow> not_idle_thread x s' = not_idle_thread x s"
  by (drule sym, simp add: not_idle_thread_def)

lemma dcorres_select_select_ext:
  "\<forall>s'\<in>S'. \<exists>s\<in>S. rvr s s' \<Longrightarrow>
    dcorres rvr \<top> \<top> (select S) (select_ext a S')"
  by (clarsimp simp: select_def select_ext_def get_def bind_def return_def assert_def fail_def corres_underlying_def)

lemma cap_revoke_corres_helper:
  "dcorres boolean_exception (\<lambda>_. True)
      ((=) s' and invs and valid_pdpt_objs)
      (monadic_trancl_preemptible
         (\<lambda>y. do S \<leftarrow> gets (KHeap_D.descendants_of (transform_cslot_ptr slot'));
                 if S = {} then returnOk True
                 else do child \<leftarrow> select S;
                         cap \<leftarrow> KHeap_D.get_cap child;
                         doE y \<leftarrow> assertE (cap \<noteq> cdl_cap.NullCap);
                             y \<leftarrow> delete_cap child;
                             Monads_D.throw \<sqinter> returnOk False
                         odE
                      od
              od)
         False)
       (cap_revoke slot')
  "
  proof (induct rule: cap_revoke.induct)
    case (1 slot' sfix)
  show ?case
  supply if_cong[cong]
  apply (subst cap_revoke.simps)
  apply (rule monadic_rewrite_corres_l[where P =\<top>,simplified])
   apply (rule Finalise_DR.monadic_trancl_preemptible_step)
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:liftE_bindE)
  apply (rule_tac Q'="\<lambda>cap. (=) sfix and cte_wp_at (\<lambda>x. x = cap) slot'" in corres_symb_exec_r)
     apply (rule dcorres_expand_pfx)
     apply (rule_tac Q'="\<lambda>cdt' s. s = sfix \<and> cdt' = cdt sfix" in corres_symb_exec_r)
           apply clarsimp
           apply (rule dcorres_expand_pfx)
           apply clarsimp
           apply (case_tac "rv = cap.NullCap")
            apply (simp add:gets_def bindE_def bind_assoc whenE_def)
            apply (rule dcorres_absorb_get_l)
            apply (subst cdl_Null_descendants)
              apply (subst identity_eq, simp )
             apply (drule invs_mdb, simp)
            apply (clarsimp simp:empty_set_eq)+
            apply (clarsimp simp:returnOk_def lift_def)
            apply (rule corres_guard_imp)
              apply (rule monadic_rewrite_corres_l[where P=\<top> ,simplified])
               apply (rule monadic_trancl_preemptible_return)
              apply (rule corres_trivial)
              apply (clarsimp simp:returnOk_def boolean_exception_def)+
           apply (case_tac "CSpaceAcc_A.descendants_of slot' (cdt sfix) = {}")
            apply (clarsimp simp:whenE_def empty_set_eq)
            apply (simp add:gets_def bindE_def bind_assoc whenE_def)
            apply (rule dcorres_absorb_get_l)
            apply (subst descendants_of_eqv)
              apply (drule invs_mdb_cte)
              apply (drule sym, force simp: swp_def)
             apply (rule cte_wp_at_weakenE)
              apply simp+
            apply (clarsimp simp: lift_def empty_set_eq)+
            apply (rule corres_guard_imp)
              apply (rule monadic_rewrite_corres_l[where P=\<top> ,simplified])
               apply (rule monadic_trancl_preemptible_return)
              apply (rule corres_trivial)
              apply (clarsimp simp:returnOk_def boolean_exception_def)+
           apply (clarsimp simp:whenE_def empty_set_eq)
           apply (subst gets_def)
           apply (simp add: bind_assoc bindE_def)
           apply (rule dcorres_absorb_get_l)
           apply (subst descendants_of_eqv)
             apply (drule invs_mdb_cte)
             apply (drule sym, force simp: swp_def)
            apply (rule cte_wp_at_weakenE, simp+)
           apply (clarsimp simp:bind_assoc)
           apply (rule corres_split_forwards'[where r'="\<lambda>slot slot'. slot = transform_cslot_ptr slot'"
             and Q =" \<lambda>r. \<top>" and Q'="\<lambda>r s. s = sfix \<and> r \<in> (CSpaceAcc_A.descendants_of slot' (cdt sfix)) \<and> (r, s) \<in> fst ((select_ext (next_revoke_cap slot') (CSpaceAcc_A.descendants_of slot' (cdt sfix))) sfix)"])
              apply (rule corres_guard_imp[OF dcorres_select_select_ext])
                apply (subst descendants_of_eqv)
                  apply (drule invs_mdb_cte)
                  apply (simp add: swp_def)
                 apply (erule cte_wp_at_weakenE, simp)
                apply (simp,blast)
              apply simp+
            apply (wp, (clarsimp simp: select_ext_def in_monad)+)
           apply (rule dcorres_expand_pfx)
           apply (rule_tac r'="\<lambda>cap cap'. cap = transform_cap cap'"
             and Q ="\<lambda>r. \<top>" and Q'="\<lambda>r s. cte_wp_at (\<lambda>x. x = r) (aa,ba) s \<and> s = sfix" in corres_split_forwards')
              apply (rule corres_guard_imp[OF get_cap_corres],simp+)
              apply (case_tac "next_revoke_cap slot' sfix")
              apply clarsimp
              apply (frule(1) descendants_not_idle)
              apply (simp add:invs_def valid_state_def)
             apply (wp get_cap_cte_wp_at | clarsimp)+
           apply (clarsimp simp:assertE_def corres_free_fail returnOk_def lift_def)
           apply (simp add:bindE_def[symmetric] return_returnOk)
           apply (simp add:bindE_assoc)
           apply (simp add:bindE_def)
           apply (rule dcorres_expand_pfx)
           apply (rule_tac r'= "dc\<oplus>dc" and Q =" \<lambda>r. \<top>"
             and Q'="\<lambda>r s. (r,s)\<in> fst (cap_delete (aa,ba) sfix)" in corres_split_forwards')
              apply (case_tac "next_revoke_cap slot' sfix")
              apply clarsimp
              apply (rule corres_guard_imp[OF delete_cap_corres'])
               apply clarsimp+
              apply (intro conjI, erule cte_wp_at_weakenE,simp)
               apply (rule descendants_emptyable,simp+)
              apply (rule descendants_not_idle,simp+)
            apply (clarsimp|wp)+
            apply (fastforce simp:valid_def)
           apply (clarsimp simp:bindE_def[symmetric] lift_def)
           apply (case_tac rva)
            apply (clarsimp simp:boolean_exception_def)+
           apply (simp add:bindE_def)
           apply (rule dcorres_expand_pfx)
           apply (rule_tac r'= "dc \<oplus> dc" and Q =" \<lambda>r s. case r of Inr a \<Rightarrow> a = False | _  \<Rightarrow> True"
             and Q' = "\<lambda>r s. (case r of Inr rva \<Rightarrow> (r , s) \<in> fst (Exceptions_A.preemption_point s') | _ \<Rightarrow> True)"
             in corres_split_forwards')
              apply (rule corres_guard_imp[OF corres_trivial[OF preemption_corres]])
               apply simp+
             apply wp
               apply (simp add:valid_def throwError_def return_def)
              apply (simp add:valid_def returnOk_def return_def)
             apply fastforce
            apply (clarsimp simp: valid_def)
           apply clarsimp
           apply (case_tac rva)
            apply (clarsimp simp:lift_def boolean_exception_def)
           apply (rule dcorres_expand_pfx)
           apply (clarsimp simp:lift_def assertE_def[symmetric] bindE_def[symmetric])
           apply (rule corres_guard_imp)
          apply (rule_tac rv = rv and rva = "cdt sfix" and rvb = "descendants_of slot' (cdt sfix)"
            and rvc = "(aa,ba)" and rvd = rv' and rve = "()" and rvf = "()"
            and st = sfix and sta = sfix and stb = sfix and stc = sfix
            and std = sfix and ste = sfix and stf = s' and stg = s'a in "1")
                  apply ((clarsimp simp: cte_wp_at_def in_monad select_def select_ext_def | rule refl)+)
        apply (erule use_valid[OF _ preemption_point_inv'])
          apply simp
         apply simp
        apply (simp add: in_monad_cap_delete_invs use_valid[OF _ cap_delete_valid_pdpt_objs] select_def)
       apply (simp add: gets_def valid_def bind_def get_def return_def)
      apply ((wp get_cap_cte_wp_at|clarsimp)+)
  done
qed

lemma revoke_cap_spec_corres:
  "dcorres (dc \<oplus> dc) \<top> ((=) s' and invs and valid_pdpt_objs)
       (revoke_cap (transform_cslot_ptr slot')) (cap_revoke slot')"
  apply (subst revoke_cap_def)
  apply (rule boolean_exception_corres)
  unfolding K_def
  apply (clarsimp simp: liftE_bindE cong: if_cong)
  apply (rule cap_revoke_corres_helper)
  done

lemma revoke_cap_corres:
  "slot = transform_cslot_ptr slot'
  \<Longrightarrow> dcorres (dc\<oplus>dc) \<top> (invs and valid_pdpt_objs)
       (revoke_cap (slot)) (cap_revoke (slot'))"
  apply (rule dcorres_expand_pfx)
  apply clarsimp
  apply (rule corres_guard_imp[OF revoke_cap_spec_corres])
  apply simp+
done

lemma cancel_badged_sends_def':
  "CSpace_D.cancel_badged_sends ep badge =
  (  do s\<leftarrow>get;
     tcb_filter_modify {x. \<exists>tcb. (cdl_objects s) x = Some (Tcb tcb) \<and> is_thread_blocked_on_endpoint tcb ep}
       (\<lambda>x. (case x of Some (Tcb tcb ) \<Rightarrow>
          if get_tcb_ep_badge tcb = Some badge then Some (Tcb (remove_pending_operation tcb cdl_cap.RestartCap))
          else x))
  od)"
  apply (simp add:CSpace_D.cancel_badged_sends_def get_def simpler_modify_def tcb_filter_modify_def)
  apply (clarsimp simp:bind_def)
  apply (rule ext)
  apply clarsimp
  apply (case_tac s)
  apply clarsimp
  apply (rule ext)
  apply (clarsimp simp:option_map_def split:option.splits cdl_object.split)
done

lemma cancel_badged_sends_def'':
  "CSpace_D.cancel_badged_sends ep badge =
  (  do s\<leftarrow>get;
     tcb_filter_modify {x. \<exists>tcb. (cdl_objects s) x = Some (Tcb tcb) \<and> is_thread_blocked_on_endpoint tcb ep
        \<and> get_tcb_ep_badge tcb = Some badge}
       (\<lambda>x. (case x of Some (Tcb tcb) \<Rightarrow> Some (Tcb (remove_pending_operation tcb cdl_cap.RestartCap))))
  od)"
  apply (simp add:CSpace_D.cancel_badged_sends_def get_def simpler_modify_def tcb_filter_modify_def)
  apply (clarsimp simp:bind_def)
  apply (rule ext)
  apply clarsimp
  apply (case_tac s)
  apply clarsimp
  apply (rule ext)
  apply (clarsimp simp:option_map_def split:option.splits cdl_object.split)
done

lemma corres_mapM_to_mapM_x:
  "corres_underlying sr fl fl' dc P P' f (mapM_x g xs)
     \<Longrightarrow> corres_underlying sr fl fl' dc P P' f (mapM g xs)"
  by (simp add: mapM_x_mapM liftM_def[symmetric])

lemma ep_waiting_set_recv_upd_kh:
  "ep_at epptr s \<Longrightarrow> (ep_waiting_set_recv epptr (update_kheap ((kheap s)(epptr \<mapsto> kernel_object.Endpoint X)) s))
    = (ep_waiting_set_recv epptr s)"
  apply (rule set_eqI)
  apply (clarsimp simp:ep_waiting_set_recv_def obj_at_def is_ep_def)
done

lemma ep_waiting_set_send_upd_kh:
  "ep_at epptr s \<Longrightarrow> (ep_waiting_set_send epptr (update_kheap ((kheap s)(epptr \<mapsto> kernel_object.Endpoint X)) s))
    = (ep_waiting_set_send epptr s)"
  apply (rule set_eqI)
  apply (clarsimp simp:ep_waiting_set_send_def obj_at_def is_ep_def)
done

lemma ntfn_waiting_set_upd_kh:
  "ep_at epptr s \<Longrightarrow> (ntfn_waiting_set epptr (update_kheap ((kheap s)(epptr \<mapsto> kernel_object.Endpoint X)) s))
    = (ntfn_waiting_set epptr s)"
  apply (rule set_eqI)
  apply (clarsimp simp:ntfn_waiting_set_def obj_at_def is_ep_def)
done

lemma dcorres_ep_cancel_badge_sends:
  notes hoare_TrueI[wp]
  shows
  "dcorres dc \<top> valid_state
    (CSpace_D.cancel_badged_sends epptr word2)
    (IpcCancel_A.cancel_badged_sends epptr word2)"
  supply if_cong[cong]
  apply (clarsimp simp:IpcCancel_A.cancel_badged_sends_def)
  apply (rule dcorres_expand_pfx)
  apply clarsimp
  apply (rule_tac Q' = "\<lambda>r. (=) s' and ko_at (kernel_object.Endpoint r) epptr and valid_ep r"
                in corres_symb_exec_r)
     apply (case_tac rv)
       apply (clarsimp simp: cancel_badged_sends_def')
       apply (rule dcorres_absorb_get_l)
       apply (rule corres_guard_imp[OF filter_modify_empty_corres])
         apply (clarsimp simp:invs_def)
         apply (frule_tac epptr = epptr in get_endpoint_pick ,simp add:obj_at_def)
         apply (cut_tac ep = epptr and s = "transform s'" in is_thread_blocked_on_sth)
         apply (drule_tac x = x in eqset_imp_iff)
         apply (clarsimp simp: valid_state_def valid_ep_abstract_def none_is_sending_ep_def
                               none_is_receiving_ep_def)
         apply (clarsimp simp: ntfn_waiting_set_lift ep_waiting_set_send_lift
                               ep_waiting_set_recv_lift)
         apply (drule ep_not_waiting_ntfn[rotated])
          apply (simp add:valid_pspace_def)
         apply auto[1]
        apply simp+
      apply (rule dcorres_expand_pfx)
      apply (rule_tac
        Q'="\<lambda>r s. s = (update_kheap ((kheap s')(epptr\<mapsto> (Endpoint Structures_A.endpoint.IdleEP))) s')"
        in dcorres_symb_exec_r)
        apply (clarsimp simp: filterM_mapM cancel_badged_sends_def')
        apply (rule dcorres_absorb_get_l)
        apply (rule corres_dummy_return_l)
        apply (rule corres_split_forwards'[where r'=dc])
           apply (rule corres_mapM_to_mapM_x)
           apply (rule corres_guard_imp)
             apply (rule_tac lift_func = id in set_list_modify_corres_helper)
                 apply (simp add:valid_ep_def)
                apply (simp add:inj_on_def)
               apply (simp add:is_thread_blocked_on_sth[simplified])
               apply (subgoal_tac "valid_idle s'a")
                apply (clarsimp simp: ntfn_waiting_set_lift ep_waiting_set_send_lift
                                      ep_waiting_set_recv_lift)
                apply (subst ntfn_waiting_set_upd_kh)
                 apply (simp add:obj_at_def is_ep_def)
                apply (subst ep_waiting_set_send_upd_kh)
                 apply (simp add:obj_at_def is_ep_def)
                apply (subst ep_waiting_set_recv_upd_kh)
                 apply (simp add:obj_at_def is_ep_def)
                apply (frule_tac epptr = epptr in get_endpoint_pick)
                 apply (simp add:obj_at_def)
                apply (clarsimp simp:valid_ep_abstract_def none_is_receiving_ep_def)
                apply (subst ep_not_waiting_ntfn)
                  apply (simp add:valid_state_def valid_pspace_def)
                 apply (simp add:obj_at_def)
                apply (rule set_eqI)
                apply (clarsimp simp:image_def)
               apply (clarsimp simp:valid_idle_def valid_state_def pred_tcb_at_def obj_at_def)
              apply (clarsimp simp: tcb_filter_modify_def bind_assoc thread_get_def
                                    get_thread_state_def)
              apply (rule_tac
                Q'="\<lambda>s. valid_idle s \<and> not_idle_thread a s
                      \<and> idle_thread s = idle_thread s' \<and>
                st_tcb_at (\<lambda>ts. \<exists>pl. ts = Structures_A.thread_state.BlockedOnSend epptr pl) a s"
                in corres_guard_imp[where Q=\<top>])
                apply (rule dcorres_absorb_gets_the)
                apply (clarsimp simp:pred_tcb_at_def obj_at_def dest!:get_tcb_SomeD)
                apply (rule conjI)
                 apply (clarsimp simp:set_thread_state_def bind_assoc | rule conjI)+
                 apply (rule dcorres_absorb_gets_the)
                 apply (rule corres_guard_imp)
                   apply (rule_tac P="(=) (transform s'b)" and P'="(=) s'b"
                               and Q=\<top> and Q'=\<top> in corres_split_noop_rhs2)
                      apply (clarsimp simp: set_object_def get_object_def in_monad simpler_modify_def
                                            get_def return_def bind_def put_def corres_underlying_def)
                      apply (clarsimp simp:transform_def transform_current_thread_def)
                      apply (rule ext)
                      apply (clarsimp simp:transform_objects_tcb not_idle_thread_def )
                      apply (clarsimp simp:transform_tcb_def transform_objects_def
                        get_tcb_ep_badge_def remove_pending_operation_def get_tcb_SomeD)
                      apply (fastforce simp: restrict_map_def map_add_def map_def tcb_slot_defs)
                     apply (rule dcorres_rhs_noop_above_True[OF set_thread_state_act_dcorres])
                     apply (rule dcorres_rhs_noop_above_True[OF tcb_sched_action_dcorres])
                     apply simp
                    apply (wp | simp)+
                apply (clarsimp simp: simpler_modify_def corres_underlying_def return_def
                                      transform_def
                               dest!: get_tcb_rev)
                apply (rule ext)
                apply clarsimp
                apply (case_tac "a=idle_thread s'a", simp add: not_idle_thread_def)
                apply (drule (1) transform_objects_tcb)
                apply (clarsimp simp: transform_current_thread_def transform_def)
                apply (clarsimp simp: not_idle_thread_def transform_tcb_def transform_def
                                      get_tcb_ep_badge_def remove_pending_operation_def tcb_slot_defs
                                      infer_tcb_pending_op_def infer_tcb_bound_notification_def)
               apply simp+
             apply (clarsimp simp:bind_assoc not_idle_thread_def)
             apply (wp sts_st_tcb_at_neq)
              apply (rule_tac Q'="\<lambda>r a. valid_idle a \<and> idle_thread a = idle_thread s' \<and>
                st_tcb_at (\<lambda>ts. \<exists>pl. ts = Structures_A.thread_state.BlockedOnSend epptr pl) y a
               \<and> y \<noteq> idle_thread a" in hoare_strengthen_post)
               apply wp
              apply clarsimp+
              apply (frule pending_thread_in_send_not_idle)
                 apply (simp add:valid_state_def)+
              apply (clarsimp simp:not_idle_thread_def)
             apply fastforce
            apply fastforce
           apply (frule_tac epptr = epptr in get_endpoint_pick, simp add:obj_at_def)
           apply (clarsimp simp:valid_ep_abstract_def ep_waiting_set_send_def)
           apply (clarsimp simp:valid_idle_def pred_tcb_at_def obj_at_def valid_ep_abstract_def)
           apply (rule conjI,clarsimp)
           apply (clarsimp simp:valid_state_def)
           apply (frule_tac y = x in generates_pending_not_idle)
            apply (fastforce simp:pred_tcb_at_def obj_at_def)
           apply (frule ep_not_idle)
            apply (fastforce simp:obj_at_def is_ep_def)
           apply (clarsimp simp:not_idle_thread_def valid_idle_def pred_tcb_at_def obj_at_def)
          apply wp+
        apply (clarsimp)
        apply (rule corres_guard_imp)
          apply (rule corres_split_noop_rhs[OF corres_dummy_set_sync_ep])
           apply (rule reschedule_required_dcorres[THEN corres_trivial])
          apply (wp set_ep_exec_wp|clarsimp)+
      apply (rule dcorres_to_wp[where Q=\<top>,simplified])
      apply (rule corres_dummy_set_sync_ep)
     apply (clarsimp simp: cancel_badged_sends_def'')
     apply (rule dcorres_absorb_get_l)
     apply (rule corres_guard_imp[OF filter_modify_empty_corres])
       apply (frule_tac epptr = epptr in get_endpoint_pick ,simp add:obj_at_def)
       apply (cut_tac ep = epptr and s = "transform s'a" in is_thread_blocked_on_sth)
       apply clarsimp
       apply (drule_tac x = x in eqset_imp_iff)
       apply (clarsimp simp: valid_state_def valid_ep_abstract_def none_is_sending_ep_def
                             none_is_receiving_ep_def)
       apply (clarsimp simp: ntfn_waiting_set_lift ep_waiting_set_send_lift
                             ep_waiting_set_recv_lift image_def)
       apply (drule ep_not_waiting_ntfn[rotated])
        apply (simp add:valid_pspace_def)
       apply (clarsimp simp: restrict_map_def transform_def transform_objects_def)
       apply (clarsimp simp: ep_waiting_set_recv_def restrict_map_def transform_def
                      split: if_split_asm dest!: get_tcb_rev elim!: CollectE)
       apply (clarsimp simp: transform_tcb_def transform_objects_def infer_tcb_bound_notification_def
                             is_thread_blocked_on_endpoint_def infer_tcb_pending_op_def tcb_slot_defs
                      dest!: get_tcb_SomeD)
       apply (clarsimp simp: get_tcb_ep_badge_def tcb_slot_defs
                      split: option.splits cdl_cap.splits)
      apply clarsimp+
    apply (wpsimp wp: get_simple_ko_sp get_simple_ko_ko_at
                      get_simple_ko_valid[where f=Endpoint, simplified valid_ep_def2[symmetric]]
                simp:valid_state_def)+
  done

lemma neq_CPSR:
  "msg_info_register \<noteq> CPSR \<and> cap_register \<noteq> CPSR"
  by (clarsimp simp: msg_info_register_def cap_register_def capRegister_def msgInfoRegister_def)

lemma transform_intent_invalid_invocation:
  "transform_intent (invocation_type (mi_label (data_to_message_info 0))) = (\<lambda>x. None)"
  apply (rule ext)
  apply (clarsimp simp: transform_intent_def)
  apply (simp add: data_to_message_info_def invocation_type_def fromEnum_def toEnum_def
                   enum_gen_invocation_labels enum_invocation_label)
  done

lemma transform_default_tcb:
  "transform_tcb ms y (Structures_A.default_tcb minBound) = cdl_default_tcb"
  apply (clarsimp simp:Structures_A.default_tcb_def tcb_registers_caps_merge_def
    transform_tcb_def infer_tcb_pending_op_def new_context_def default_arch_tcb_def)
  apply (clarsimp simp:get_tcb_message_info_def arch_tcb_context_get_def
                       transform_full_intent_def get_tcb_mrs_def Let_def neq_CPSR )
  apply (clarsimp simp:Suc_leI[OF msg_registers_lt_msg_max_length])
  apply (simp add:transform_intent_invalid_invocation)
  apply (simp add:get_ipc_buffer_words_def cdl_default_tcb_def guess_error_def
                  data_to_message_info_def default_domain_def tcb_slot_defs
                  infer_tcb_bound_notification_def)
  done

lemma dcorres_list_all2_mapM_':
  assumes w: "suffix xs oxs" "suffix ys oys"
  assumes y: "\<And>x xs y ys. \<lbrakk> F x y; suffix (x # xs) oxs; suffix (y # ys) oys \<rbrakk>
               \<Longrightarrow> dcorres dc (P (x # xs)) (P' (y # ys)) (f x) (g y)"
  assumes z: "\<And>x y xs. \<lbrakk> F x y; suffix (x # xs) oxs \<rbrakk> \<Longrightarrow> \<lbrace>P (x # xs)\<rbrace> f x \<lbrace>\<lambda>rv. P xs\<rbrace>"
             "\<And>x y ys. \<lbrakk> F x y; suffix (y # ys) oys \<rbrakk> \<Longrightarrow> \<lbrace>P' (y # ys)\<rbrace> g y \<lbrace>\<lambda>rv. P' ys\<rbrace>"
  assumes x: "list_all2 F xs ys"
  shows "dcorres dc (P xs) (P' ys) (mapM_x f xs) (mapM_x g ys)"
  apply (insert x w)
  apply (induct xs arbitrary: ys)
   apply (simp add: mapM_x_def sequence_x_def)
  apply (case_tac ys)
   apply simp
  apply (clarsimp simp add: mapM_x_def sequence_x_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule y; assumption)
      apply (clarsimp dest!: suffix_ConsD)
      apply (erule meta_allE, (drule(1) meta_mp)+)
      apply assumption
     apply (erule(1) z)+
   apply simp+
  done

lemmas dcorres_list_all2_mapM_
     = dcorres_list_all2_mapM_' [OF suffix_order.refl suffix_order.refl]

lemma set_get_set_asid_pool:
  "do _ \<leftarrow> set_asid_pool a x; ap \<leftarrow> get_asid_pool a; set_asid_pool a (y ap) od = set_asid_pool a (y x)"
  apply (rule ext)
  apply (simp add: get_asid_pool_def set_asid_pool_def get_object_def set_object_def
                   a_type_def bind_assoc exec_gets)
  apply (case_tac "kheap xa a", simp_all)
  apply (case_tac aa, simp_all)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj, simp_all)
  apply (simp add:set_object_def exec_gets bind_assoc exec_get exec_put)
  apply (simp add: put_def)
  done

lemma set_asid_pool_empty'_helper:
  "n < 1023 \<Longrightarrow>
   (if x = ucast ((1 :: word32) + of_nat n) then None else if x \<le> of_nat n then None else ap x) =
   (if (x :: 10 word) \<le> 1 + of_nat n then None else ap x)"
  apply (frule of_nat_mono_maybe[where x="2^10 - 1" and 'a=10, simplified])
  apply (subgoal_tac "ucast (1 + of_nat n :: word32) = (1 + of_nat n :: 10 word)")
   prefer 2
   apply (rule word_unat.Rep_eqD)
   apply (simp add: unat_word_ariths unat_ucast unat_of_nat)
  apply (subst word_le_make_less[where y="of_nat n"])
  apply (auto simp: add.commute)
  done

lemma set_asid_pool_empty':
  "n < 2 ^ asid_low_bits \<Longrightarrow>
   do ap \<leftarrow> get_asid_pool a; set_asid_pool a (\<lambda>x. if x \<le> of_nat n then None else ap x) od =
   mapM_x (\<lambda>slot. get_asid_pool a >>= (\<lambda>pool. set_asid_pool a (pool(ucast slot:=None))))
          [0 :: word32 .e. of_nat n]"
  apply (induct n)
   apply (simp add: mapM_x_Cons mapM_x_Nil fun_upd_def)
  apply (subgoal_tac "of_nat n < (2 :: word32) ^ word_bits - 1")
   prefer 2
   apply (rule of_nat_mono_maybe[where x="2^word_bits - 1", simplified])
    apply (simp add:word_bits_def)
   apply (simp add:asid_low_bits_def word_bits_def)
  apply (simp, drule sym)
  apply (simp add:upto_enum_inc_1 mapM_append_single bind_assoc fun_upd_def
                  set_get_set_asid_pool set_asid_pool_empty'_helper asid_low_bits_def)
  done

lemma empty_pool:
  "(\<lambda>x. if x \<le> 2 ^ asid_low_bits - 1 then None else (ap :: 10 word \<rightharpoonup> word32) x) = Map.empty"
  apply (rule ext)
  apply (cut_tac ptr=x and 'a=10 in word_up_bound)
  apply (simp add:asid_low_bits_def)
  done

lemma get_set_asid_pool:
  "do ap \<leftarrow> get_asid_pool a; set_asid_pool a x od = set_asid_pool a x"
  apply (rule ext)
  apply (simp add: get_asid_pool_def set_asid_pool_def set_object_def get_object_def
                   a_type_def bind_assoc exec_gets)
  apply (case_tac "kheap xa a", simp_all)
  apply (case_tac aa, simp_all)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj, simp_all)
  apply (simp add:exec_gets)
  done

lemma set_asid_pool_empty:
  "set_asid_pool a Map.empty \<equiv>
   mapM_x (\<lambda>slot. get_asid_pool a >>= (\<lambda>pool. set_asid_pool a (pool(ucast slot:=None))))
          [0 :: word32 .e. 2 ^ asid_low_bits - 1]"
  using set_asid_pool_empty' [of "2 ^ asid_low_bits - 1" a]
  apply -
  apply (rule eq_reflection)
  apply simp
  apply (subst (asm) empty_pool)
  apply (simp add: get_set_asid_pool)
  done

lemma get_asid_pool_triv:
  "\<lbrace> \<lambda>s. True \<rbrace>
   get_asid_pool a
   \<lbrace> \<lambda>r. ko_at (ArchObj (arch_kernel_obj.ASIDPool r)) a \<rbrace>"
  apply (wp | simp)+
  done

declare fun_upd_apply[simp del]

lemma dcorres_set_asid_pool_none_trivial:
  "dcorres dc (\<lambda>s. opt_cap (a, snd (transform_asid asid)) s = Some cdl_cap.NullCap)
              (valid_idle and ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) a)
   (return ()) (set_asid_pool a (pool(ucast asid := None)))"
  apply (simp add:set_asid_pool_def get_object_def gets_def bind_assoc)
  apply (clarsimp simp:KHeap_D.set_object_def simpler_modify_def put_def bind_def obj_at_def
                       corres_underlying_def update_slots_def return_def object_slots_def)
  apply (clarsimp simp:KHeap_A.set_object_def get_object_def in_monad get_def put_def bind_def return_def)
  apply (clarsimp simp:transform_def transform_current_thread_def
                       opt_cap_def slots_of_def)
  apply (drule(1) arch_obj_not_idle)
  apply (rule ext)
  apply (clarsimp simp:not_idle_thread_def transform_objects_def restrict_map_def map_add_def)
  apply (case_tac "kheap b x")
   apply (subgoal_tac "x \<noteq> a")
    apply (clarsimp simp:fun_upd_other)
   apply clarsimp
  apply simp
  apply (rule_tac P="x \<noteq> a" in case_split)
   apply (clarsimp simp:fun_upd_other)
  apply (clarsimp simp:fun_upd_same object_slots_def)
  apply (rule ext)
  apply (clarsimp simp:transform_asid_pool_contents_def transform_asid_def)
  apply (clarsimp simp:unat_map_def)
  apply (rule_tac P="of_nat x \<noteq> (ucast asid :: 10 word)" in case_split)
   apply (clarsimp simp:fun_upd_other)
  apply (clarsimp simp:fun_upd_same transform_asid_pool_entry_def)
  done

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

lemma dcorres_set_asid_pool_empty:
  "dcorres dc \<top> (valid_idle and asid_pool_at a and
                 (\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)))
    (mapM_x PageTableUnmap_D.empty_slot
                            (map (Pair a) [0 .e. 2 ^ asid_low_bits - 1]))
    (set_asid_pool a Map.empty)"
  apply (unfold set_asid_pool_empty)
  apply (rule dcorres_list_all2_mapM_[where F="\<lambda>x y. snd x = snd (transform_asid y)"])
     apply (clarsimp simp:PageTableUnmap_D.empty_slot_def gets_the_def gets_def bind_assoc)
     apply (rule dcorres_absorb_get_l)
     apply (subgoal_tac "aa=a", clarsimp)
      apply (clarsimp simp:assert_opt_def split:option.splits)
      apply (intro conjI, clarsimp simp:opt_cap_asid_pool_Some typ_at_eq_kheap_obj)
      apply (clarsimp, intro conjI, clarsimp)
       apply (rule dcorres_symb_exec_r)
         apply (rule corres_guard_imp)
           apply (rule dcorres_set_asid_pool_none_trivial)
          apply (wp | clarsimp | simp)+
      apply (rule dcorres_symb_exec_r)
        apply (rule corres_dummy_return_pr)
        apply (rule corres_guard_imp)
          apply (rule corres_split[OF dummy_remove_cdt_asid_pool_slot])
            apply (clarsimp)
            apply (rule dcorres_set_asid_pool)
              apply fastforce
             apply clarsimp
            apply (clarsimp simp:transform_asid_pool_entry_def)
           apply (wp | clarsimp)+
        apply simp
       apply (wp get_asid_pool_triv | clarsimp simp:typ_at_eq_kheap_obj obj_at_def swp_def)+
     apply (subgoal_tac "(aa, snd (transform_asid y)) \<in> set (map (Pair a) [0..<2 ^ asid_low_bits])")
      apply clarsimp
     apply (clarsimp simp del:set_map simp: suffix_def)
    apply (wp | clarsimp simp:swp_def)+
  apply (clarsimp simp:list_all2_iff transform_asid_def asid_low_bits_def set_zip)
  apply (clarsimp simp: upto_enum_def ucast_of_nat_small unat_of_nat)
  done

declare fun_upd_apply[simp]

lemma opt_cap_asid_pool_not_None:
  "\<lbrakk> ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) w s'; valid_idle s';
     ba < 2 ^ asid_low_bits \<rbrakk>
   \<Longrightarrow> \<exists>y. opt_cap (w, ba) (transform s') = Some y"
  by (clarsimp simp: opt_object_asid_pool obj_at_def slots_of_def unat_map_def
      opt_cap_def invs_def valid_state_def object_slots_def transform_asid_pool_contents_def
      asid_low_bits_def)

lemma opt_cap_asid_pool_None:
  "\<lbrakk> ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) w s'; valid_idle s';
   \<not> ba < 2 ^ asid_low_bits \<rbrakk>
   \<Longrightarrow> opt_cap (w, ba) (transform s') = None"
  by (clarsimp simp: opt_object_asid_pool obj_at_def slots_of_def unat_map_def
     opt_cap_def invs_def valid_state_def object_slots_def transform_asid_pool_contents_def
      asid_low_bits_def)

lemma dcorres_clear_object_caps_asid_pool:
  "dcorres dc \<top> (invs and  cte_wp_at ((=) (cap.ArchObjectCap (arch_cap.ASIDPoolCap w asid))) slot)
    (clear_object_caps w)
    (set_asid_pool w Map.empty)"
  apply (clarsimp simp:clear_object_caps_def gets_def)
  apply (rule dcorres_absorb_get_l)
  apply (subgoal_tac "\<exists>pool. (ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) w) s'")
   apply (clarsimp simp:invs_def valid_state_def valid_pspace_def valid_mdb_def)
   apply (drule cte_wp_valid_cap,simp)
   apply (clarsimp simp:valid_cap_def cap_aligned_def)
   apply (rule corres_guard_imp)
     apply (rule select_pick_corres)
     apply (rule dcorres_set_asid_pool_empty)
    apply (clarsimp simp: distinct_map distinct_enum_upto inj_on_def intro!:set_eqI)
    apply (rule iffI)
     apply (fastforce intro!:opt_cap_asid_pool_not_None)
    apply (subgoal_tac "b < 2 ^ asid_low_bits")
     apply simp
    apply (rule ccontr)
    apply (drule_tac ba = b in opt_cap_asid_pool_None)
      apply clarsimp
     apply clarsimp
    apply clarsimp
   apply clarsimp
  apply (clarsimp simp:invs_def valid_state_def valid_cap_def obj_at_def a_type_def
                       valid_pspace_def dest!: cte_wp_valid_cap)
  by (clarsimp split: Structures_A.kernel_object.split_asm
                      arch_kernel_obj.split_asm if_splits)

lemmas valid_idle_invs_strg = invs_valid_idle_strg

crunch invalidate_tlb_by_asid
  for idle[wp]: "\<lambda>s. P (idle_thread s)"

crunch invalidate_tlb_by_asid
  for st_tcb_at[wp]: "st_tcb_at P thread"

lemma dcorres_storeWord_mapM_x_cvt:
  "\<forall>x\<in>set ls. within_page buf x sz
   \<Longrightarrow> dcorres dc (\<lambda>_. True) (ko_at (ArchObj (DataPage False sz)) buf and  valid_objs and pspace_distinct and pspace_aligned)
    (corrupt_frame buf)
       (do_machine_op (mapM (\<lambda>p. storeWord p 0) ls))"
proof (induct ls)
  case Nil
  show ?case
    apply (clarsimp simp:mapM_def sequence_def dc_def[symmetric])
    apply (rule corres_guard_imp[OF dcorres_dummy_corrupt_frame])
     apply simp+
    done
next
  case (Cons ls x)
  show ?case
    apply (clarsimp simp:mapM_Cons)
    apply (subst do_machine_op_bind)
      apply (clarsimp simp:ef_storeWord empty_fail_cond)+
    apply (subst corrupt_frame_duplicate[symmetric])
    apply (rule corres_guard_imp)
      apply (rule corres_split)
         apply (rule dcorres_store_word_conservative[where sz = sz])
    using Cons apply simp
        apply (clarsimp)
        apply (subst do_machine_op_bind)
          apply (rule empty_fail_mapM,clarsimp simp:ef_storeWord)
         apply (clarsimp simp:dc_def[symmetric])+
        apply (rule corres_dummy_return_l)
        apply (rule corres_split)
           apply (rule_tac Cons.hyps)
    using Cons
           apply simp
          apply (rule corres_free_return[where P = \<top> and P'=\<top>])
         apply wp+
    using Cons
     apply fastforce
    apply (wp|clarsimp|force)+
    done
qed

lemmas upto_enum_step_shift_red =
  upto_enum_step_shift_red[where 'a=32, simplified word_bits_def[symmetric]]

lemma dcorres_unless_r:
  "\<lbrakk> \<not> G \<Longrightarrow> dcorres r P P' f g;
    G \<Longrightarrow> dcorres r Q Q' f (return ()) \<rbrakk>
  \<Longrightarrow> dcorres r (P and Q) (\<lambda>s. (\<not>G \<longrightarrow> P' s) \<and> (G \<longrightarrow> Q' s)) f (unless G g)"
  apply (cases G, simp_all add: when_def unless_def)
   apply (rule corres_guard_imp, simp+)+
  done

lemma opt_cap_pt_Some:
  "\<lbrakk>valid_idle s';kheap s' (y && ~~ mask pt_bits)= Some (ArchObj (arch_kernel_obj.PageTable fun))\<rbrakk>
         \<Longrightarrow>  (opt_cap (y && ~~ mask pt_bits, unat (y && mask pt_bits >> 2)) (transform s'))
    = Some (transform_pte (fun (of_nat (unat (y && mask pt_bits >> 2)))))"
  apply (clarsimp simp: opt_cap_def transform_def slots_of_def object_slots_def
                        transform_objects_def map_add_def restrict_map_def not_idle_thread_def)
  apply (frule arch_obj_not_idle, simp)
  apply (clarsimp simp:transform_page_table_contents_def unat_map_def not_idle_thread_def)
  apply (rule unat_less_helper)
  apply clarsimp
  apply (subst shiftr_div_2n_w)
   apply (simp add:word_size)+
  apply (rule word_div_mult,simp+)
  apply (rule eq_mask_less[where n = 10,simplified])
   apply (simp add: mask_twice pt_bits_def pageBits_def word_size)+
  done

lemma opt_cap_pd_Some:
  "\<lbrakk>valid_idle s';kheap s' (ptr && ~~ mask pd_bits)= Some (ArchObj (arch_kernel_obj.PageDirectory fun));
    ucast (ptr && mask pd_bits >> 2) \<notin> kernel_mapping_slots\<rbrakk>
         \<Longrightarrow>  (opt_cap (ptr && ~~ mask pd_bits, unat (ptr && mask pd_bits >> 2)) (transform s'))
    = Some (transform_pde (fun (of_nat (unat (ptr && mask pd_bits >> 2)))))"
  apply (clarsimp simp:opt_cap_def slots_of_def
    object_slots_def transform_objects_def  restrict_map_def not_idle_thread_def)
  apply (simp add:opt_object_page_directory object_slots_def)
  apply (clarsimp simp:transform_page_directory_contents_def
    transform_pde_def unat_map_def below_kernel_base)
done

lemma inj_neq:"\<lbrakk>inj f;a\<noteq> b\<rbrakk> \<Longrightarrow> f a\<noteq> f b"
  apply (rule ccontr)
  apply (clarsimp simp:inj_eq)
done

lemma dcorres_empty_pde_slot:"
ucast (y && mask pd_bits >> 2) \<notin> kernel_mapping_slots
 \<Longrightarrow> dcorres dc \<top> (valid_idle and cur_tcb and (\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)))
  (PageTableUnmap_D.empty_slot (y && ~~ mask pd_bits,unat (y && mask pd_bits >>2)))
  (store_pde y ARM_A.pde.InvalidPDE)"
  apply (clarsimp simp:store_pde_def get_pd_def get_object_def bind_assoc gets_def)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:assert_def corres_free_fail split:Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp:PageTableUnmap_D.empty_slot_def)
  apply (clarsimp simp:set_pd_def set_object_def get_object_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:assert_def corres_free_fail split:Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (simp add:PageTableUnmap_D.empty_slot_def gets_the_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp:assert_opt_def opt_cap_pd_Some split:option.splits)
  apply (intro conjI,clarsimp)
   apply (clarsimp simp:set_object_def get_def put_def bind_def return_def)
   apply (clarsimp simp:corres_underlying_def transform_def cur_tcb_def tcb_at_def dest!:get_tcb_SomeD)
   apply (clarsimp simp:transform_current_thread_def)
   apply (rule ext)
   apply (case_tac x)
   apply (frule(1) arch_obj_not_idle)
   apply (clarsimp simp: not_idle_thread_def transform_objects_def restrict_map_def map_add_def)
   apply (rule ext)
   apply (clarsimp simp: transform_page_directory_contents_def unat_map_def
                         kernel_pde_mask_def ucast_nat_def transform_pde_def
                   split: if_splits ARM_A.pte.split_asm)
  apply (clarsimp simp:)+
  apply (rule corres_dummy_return_pr)
  apply (rule_tac Q'="\<lambda>r. (=) s'" in  corres_split_forwards'[where r'=dc])
     apply (rule corres_guard_imp[OF dummy_remove_cdt_pd_slot])
      apply simp+
     apply (clarsimp simp:transform_objects_def restrict_map_def)
     apply (simp add:obj_at_def a_type_def)
    apply (rule hoare_TrueI)
   apply wp
  apply clarsimp
  apply (clarsimp simp:KHeap_D.set_cap_def gets_the_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp:update_slots_def assert_opt_def opt_cap_def slots_of_def
                       opt_object_page_directory has_slots_def object_slots_def
                  split:option.splits)
  apply (clarsimp simp:KHeap_D.set_object_def set_object_def simpler_modify_def get_def put_def bind_def return_def)
  apply (clarsimp simp:corres_underlying_def transform_def cur_tcb_def tcb_at_def dest!:get_tcb_SomeD)
  apply (clarsimp simp:transform_current_thread_def)
  apply (rule ext)
  apply (frule(1) arch_obj_not_idle)
  apply (clarsimp simp: not_idle_thread_def transform_objects_def restrict_map_def map_add_def)
  apply (subst transform_page_directory_contents_upd[symmetric])
   apply (clarsimp simp:transform_pde_def)+
  done

lemma dcorres_empty_pte_slot:
  " dcorres dc \<top> (valid_idle and cur_tcb and (\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)))
     (PageTableUnmap_D.empty_slot (y && ~~ mask pt_bits, unat (y && mask pt_bits >> 2)))
     (store_pte y ARM_A.pte.InvalidPTE)"
  apply (clarsimp simp:store_pte_def get_pt_def get_object_def bind_assoc gets_def)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:assert_def corres_free_fail split:Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp:PageTableUnmap_D.empty_slot_def)
  apply (clarsimp simp:set_pt_def set_object_def get_object_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:assert_def corres_free_fail split:Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (simp add:PageTableUnmap_D.empty_slot_def gets_the_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp:assert_opt_def opt_cap_pt_Some split:option.splits)
  apply (intro conjI,clarsimp)
   apply (clarsimp simp:set_object_def get_def put_def bind_def return_def)
   apply (clarsimp simp:corres_underlying_def transform_def cur_tcb_def tcb_at_def dest!:get_tcb_SomeD)
   apply (clarsimp simp:transform_current_thread_def)
   apply (rule ext)
   apply (case_tac x)
   apply (frule(1) arch_obj_not_idle)
   apply (clarsimp simp: not_idle_thread_def transform_objects_def restrict_map_def map_add_def)
   apply (rule ext)
   apply (clarsimp simp:transform_page_table_contents_def unat_map_def transform_pte_def ucast_nat_def
                   split: if_splits ARM_A.pte.split_asm)
  apply (clarsimp simp: )+
  apply (rule corres_dummy_return_pr)
  apply (rule_tac Q'="\<lambda>r. (=) s'" in  corres_split_forwards'[where r'=dc])
     apply (rule corres_guard_imp[OF dummy_remove_cdt_pt_slot])
      apply simp+
     apply (clarsimp simp:transform_objects_def restrict_map_def)
     apply (simp add:obj_at_def a_type_def)
    apply (rule hoare_TrueI)
   apply wp
  apply clarsimp
  apply (clarsimp simp:KHeap_D.set_cap_def gets_the_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp:update_slots_def assert_opt_def opt_cap_def slots_of_def opt_object_page_table
                       has_slots_def object_slots_def split:option.splits)
  apply (clarsimp simp:KHeap_D.set_object_def set_object_def simpler_modify_def get_def put_def bind_def return_def)
  apply (clarsimp simp:corres_underlying_def transform_def cur_tcb_def tcb_at_def dest!:get_tcb_SomeD)
  apply (clarsimp simp:transform_current_thread_def)
  apply (rule ext)
  apply (frule(1) arch_obj_not_idle)
  apply (clarsimp simp: not_idle_thread_def transform_objects_def restrict_map_def map_add_def)
  apply (subst transform_page_table_contents_upd[symmetric])
  apply (clarsimp simp:transform_pte_def)
  done

lemma store_pte_ct:
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> store_pte x y \<lbrace>\<lambda>r s. P (cur_thread s)\<rbrace>"
  apply (clarsimp simp:store_pte_def)
  apply wp
   apply (simp add:set_pt_def)
   apply wp
   apply (rule_tac Q'="\<lambda>r s. P (cur_thread s)" in hoare_strengthen_post)
    apply (wp|clarsimp)+
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

lemma page_table_mapped_dwp:
  "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace> page_table_mapped aa ba w \<lbrace>\<lambda>a b. transform b = cs\<rbrace>"
  by (rule page_table_mapped_inv)

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
  "is_aligned word pd_bits\<Longrightarrow> \<lbrace>\<lambda>ps. valid_idle (ps :: det_state) \<and> transform ps = cs\<rbrace> copy_global_mappings word \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  apply (simp add:copy_global_mappings_def)
  apply wp
    apply (rule_tac Q'="\<lambda>r s. valid_idle s \<and> transform s = cs" in hoare_strengthen_post)
     apply (rule mapM_x_wp')
     apply wp
       apply (rule_tac P'="\<lambda>s. valid_idle s \<and> transform s = cs" in hoare_weaken_pre)
        apply (rule dcorres_to_wp)
        apply (rule corres_guard_imp[OF store_pde_set_cap_corres])
          apply (clarsimp simp:kernel_mapping_slots_def)
          apply (simp add: kernel_base_def pd_bits_def pageBits_def)
          apply (simp add: mask_add_aligned)
          apply (subst less_mask_eq,simp)
           apply (simp add:shiftl_t2n)
           apply (subst mult.commute)
           apply (rule div_lt_mult,simp+,unat_arith,simp+)
          apply (simp add:shiftl_shiftr1 word_size)
          apply (subst less_mask_eq,simp)
           apply unat_arith
          apply (subst ucast_le_migrate[symmetric])
            apply (simp add:word_size,unat_arith)
           apply (simp add:word_size)+
      apply (wp|clarsimp)+
  done

lemma opt_cap_pd_not_None:
  "\<lbrakk>ko_at (ArchObj (arch_kernel_obj.PageDirectory ptx)) w s'; valid_idle s';ba<4096\<rbrakk>
   \<Longrightarrow> \<exists>y. opt_cap (w, ba) (transform s') = Some y"
  by (clarsimp simp: opt_object_page_directory obj_at_def slots_of_def unat_map_def
    opt_cap_def invs_def valid_state_def object_slots_def transform_page_directory_contents_def)+

lemma opt_cap_pd_None:
  "\<lbrakk>ko_at (ArchObj (arch_kernel_obj.PageDirectory ptx)) w s'; valid_idle s';\<not> ba < 4096\<rbrakk>
   \<Longrightarrow> opt_cap (w, ba) (transform s') = None"
  by (clarsimp simp: opt_object_page_directory obj_at_def slots_of_def unat_map_def
    opt_cap_def invs_def valid_state_def object_slots_def transform_page_directory_contents_def)+

lemma transform_pde_NullCap:
  "\<lbrakk>3584 \<le> unat (xa::word32); unat xa < 4096\<rbrakk> \<Longrightarrow>
            transform_pde (kernel_pde_mask ptx (ucast xa)) = cdl_cap.NullCap"
  apply (clarsimp simp:kernel_pde_mask_def kernel_base_def)
  apply (subst ucast_le_migrate[symmetric])
    apply (simp add:word_size,unat_arith)
   apply (simp add:word_size)+
  apply (drule word_of_nat_le,simp add:transform_pde_def)
  apply (subst ucast_le_migrate[symmetric])
    apply (simp_all add:word_size)
  apply unat_arith
  done

lemma dcorres_dummy_empty_slot_pd:
  "\<lbrakk>0xE00 \<le> unat xa ; unat xa < 0x1000\<rbrakk> \<Longrightarrow> dcorres dc \<top> (valid_idle and page_directory_at w)
  (PageTableUnmap_D.empty_slot (w, unat (xa::word32))) (return x)"
  apply (clarsimp simp:PageTableUnmap_D.empty_slot_def gets_the_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp:opt_cap_def slots_of_def)
  apply  (clarsimp simp:obj_at_def a_type_def
            ,clarsimp split:Structures_A.kernel_object.splits if_splits arch_kernel_obj.splits)
  apply (subst opt_object_page_directory)
    apply (simp add:obj_at_def)+
  apply (clarsimp simp:assert_opt_def object_slots_def)
  apply (clarsimp simp:transform_page_directory_contents_def unat_map_def)
  apply (drule transform_pde_NullCap)
   apply (simp add:ucast_nat_def)+
  apply fastforce
  done

lemma dcorres_dummy_empty_slot_pd_mapM_x:
  "\<forall>x\<in> set ls. 0xE00 \<le> unat x \<and> unat x < 4096
       \<Longrightarrow> dcorres dc \<top> (page_directory_at w and valid_idle)
           (mapM_x PageTableUnmap_D.empty_slot (map (\<lambda>x. (w, unat x)) (ls::word32 list)))
           (return x)"
proof (induct ls arbitrary: x)
  case Nil
  show ?case
    apply (clarsimp simp:mapM_x_def sequence_x_def)
    done
next
  case (Cons x ls)
  show ?case
    apply (clarsimp simp:mapM_x_Cons dc_def[symmetric])
    apply (rule corres_dummy_return_r)
    apply (rule dcorres_expand_pfx)
    apply (rule corres_guard_imp)
      apply (rule corres_split)
         apply (rule dcorres_dummy_empty_slot_pd)
          apply (clarsimp simp:Cons)+
        apply (rule Cons.hyps)
        apply (clarsimp simp:Cons)
       apply wp
      apply (fastforce simp: obj_at_def)+
    done
qed

lemmas dcorres_arch_finalise_cap = dcorres_finalise_cap [where cap = "cap.ArchObjectCap cap" for cap,
  simplified, simplified comp_def, simplified]

lemma cases_simp_imp:
  "((A = None \<longrightarrow> x \<and> a) \<and> ((\<exists>y. A = Some y) \<longrightarrow> x \<and> b)) = (x \<and> ((A = None \<longrightarrow> a) \<and> ((\<exists>y. A = Some y) \<longrightarrow> b)))"
  by (cases A, simp_all)

lemma upto_enum_word_append:
  fixes a :: "('a :: len) word"
  assumes lt: "1 \<le> b" and les: "a \<le> b" "b < c"
  shows "[a .e. b - 1] @ [b .e. c] = [a .e. c]" (is "?LHS = ?RHS")
proof -
  have "?LHS = map of_nat ([unat a ..< unat b] @ [unat b ..< Suc (unat c)])" using lt
    by (simp add: upto_enum_word Suc_unat_diff_1)
  also have "... = map of_nat [unat a ..< Suc (unat c)]" using les
    apply -
    apply (rule arg_cong [where f = "map of_nat"])
    apply (rule upt_add_eq_append' [symmetric])
    apply (simp_all add: word_less_nat_alt word_le_nat_alt)
    done
  finally show ?thesis by (simp add: upto_enum_word)
qed

lemma dcorres_clear_object_caps_pt:
  "dcorres dc \<top> (invs and  cte_wp_at ((=) (cap.ArchObjectCap (arch_cap.PageTableCap w option))) (a, b))
    (clear_object_caps w)
    (mapM_x (swp store_pte ARM_A.pte.InvalidPTE) [w , w + 4 .e. w + 2 ^ pt_bits - 1])"
  apply (clarsimp simp: clear_object_caps_def gets_def)
  apply (rule dcorres_absorb_get_l)
  apply (subgoal_tac "\<exists>ptx. (ko_at (ArchObj (arch_kernel_obj.PageTable ptx)) w) s'")
   apply clarsimp
   apply (subst upto_enum_step_subtract[where x = w])
    apply (clarsimp simp:invs_def valid_state_def valid_pspace_def)
    apply (drule cte_wp_valid_cap,simp)
    apply (clarsimp simp:valid_cap_def cap_aligned_def)
    apply (rule is_aligned_no_overflow)
    apply (simp add:pt_bits_def pageBits_def word_bits_def)+
   apply (rule corres_guard_imp)
     apply (rule_tac x = "(map (\<lambda>x. (w,unat (x >> 2))) [0 , 4 .e. 2 ^ pt_bits - 1])" in select_pick_corres)
     apply (rule_tac S = "{(x,y). x = (y && ~~ mask pt_bits,unat (y && mask pt_bits >> 2))}"  in corres_mapM_x)
         apply clarsimp
         apply (rule dcorres_empty_pte_slot,simp)
       apply (rule hoare_pre)
        apply (wp valid_idle_store_pte store_pte_ct |clarsimp simp:cur_tcb_def | wps store_pte_ct )+
       apply (simp add:swp_def)
      apply (simp add:pt_bits_def pageBits_def word_bits_def)+
     apply clarsimp
     apply (subst (asm) zip_map_eqv)
     apply (clarsimp)
     apply (drule cte_wp_valid_cap)
      apply (simp add:invs_def valid_state_def valid_pspace_def)
     apply (intro conjI)
      apply (simp add:valid_cap_def cap_aligned_def)
      apply (rule conjunct2[OF is_aligned_add_helper,symmetric])
       apply (clarsimp simp:valid_cap_def cap_aligned_def)
      apply (clarsimp simp:upto_enum_step_def image_def)
      apply (rule div_lt_mult,simp)
       apply (unat_arith,simp)
     apply (rule_tac f="\<lambda>x. x >>2" in arg_cong)
     apply (rule conjunct1[OF is_aligned_add_helper,symmetric])
      apply (clarsimp simp:valid_cap_def cap_aligned_def)
     apply (clarsimp simp:upto_enum_step_def image_def)
     apply (rule div_lt_mult,simp)
      apply (unat_arith,simp)
    apply (simp | rule conjI)+
     apply (rule set_eqI)
     apply (clarsimp simp:image_def)
     apply (clarsimp simp: transform_def opt_cap_def slots_of_def valid_state_def
                           valid_pspace_def transform_objects_def restrict_map_def map_add_def
                           obj_at_def invs_def)
     apply (drule(1) arch_obj_not_idle)
     apply (case_tac "aa = idle_thread s'", simp add: not_idle_thread_def, simp)
     apply (rule iffI)
      apply (clarsimp simp: upto_enum_step_def not_idle_thread_def object_slots_def
                            transform_page_table_contents_def unat_map_def)
      apply (rule unat_less_helper)
      apply (subst mult.commute)
      apply (simp add:shiftl_t2n[where n= 2,simplified,symmetric])
      apply (simp add:shiftl_shiftr1 word_size)
      apply (subst iffD2[OF mask_eq_iff_w2p])
        apply (simp add:word_size pt_bits_def pageBits_def)+
       apply unat_arith
      apply (simp add:word_size pt_bits_def pageBits_def)+
      apply unat_arith
     apply (clarsimp simp: not_idle_thread_def object_slots_def transform_page_table_contents_def unat_map_def
                    split: if_splits)
     apply (rule_tac x = "(of_nat ba) << 2" in bexI)
      apply (simp add: shiftl_shiftr1 word_size)
      apply (subst iffD2[OF mask_eq_iff_w2p],simp add:word_size)
       apply (rule of_nat_power)
        apply (simp add:word_size unat_of_nat)+
     apply (clarsimp simp:upto_enum_step_def image_def)
     apply (rule_tac x= "of_nat ba" in exI)
     apply (simp add:shiftl_t2n)
     apply (clarsimp simp: pt_bits_def pageBits_def word_of_nat_le)
    apply (clarsimp simp: distinct_map distinct_enum_upto upto_enum_step_def inj_on_def
                          pt_bits_def pageBits_def)
    apply (subst (asm) mult.commute[where b = 4])+
    apply (simp add:shiftl_t2n[where n=2,simplified,symmetric] shiftl_shiftr1 word_size)
    apply (subst (asm) iffD2[OF mask_eq_iff_w2p],simp add:word_size)
     apply (erule le_less_trans,simp)
    apply (subst (asm) iffD2[OF mask_eq_iff_w2p],simp add:word_size)
     apply (erule le_less_trans,simp+)
   apply (simp add:invs_def valid_state_def valid_pspace_def valid_mdb_def)
  by (clarsimp simp: invs_def valid_state_def valid_cap_def obj_at_def valid_pspace_def
              dest!: cte_wp_valid_cap)

lemma opt_object_cnode:
  "\<lbrakk>valid_idle s; kheap s a = Some (kernel_object.CNode sz fun)\<rbrakk> \<Longrightarrow>
   cdl_objects (transform s) a = Some (transform_object (machine_state s) a (CNode sz fun))"
  apply (clarsimp simp: transform_def)
  apply (frule cnode_not_idle)
   apply fastforce
  apply (clarsimp simp: not_idle_thread_def restrict_map_def
                        transform_object_def transform_objects_def)
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

lemma dcorres_get_object_special:
  fixes C   :: "'a \<Rightarrow> cdl_object"
  and   UN_C :: "cdl_object \<Rightarrow> 'a"
  and   AP :: "word32 \<Rightarrow> det_state \<Rightarrow> 'b option"
  and   AP_LIFT :: "'b \<Rightarrow> det_state \<Rightarrow> 'a"
  assumes unc: "\<And>obj. UN_C (C obj) = obj"
  and     ap_lift: "\<And>s obj. \<lbrakk>AP ptr s = Some obj; AP_Q s\<rbrakk>
                   \<Longrightarrow> cdl_objects (transform s) ptr = Some (C (AP_LIFT obj s))"
  and     c: "\<And>obj. dcorres r (R obj) (R' obj) (a (C obj)) c"
  \<comment> \<open>weak\<close>
  shows   "dcorres r (\<lambda>s. (\<forall>obj. cdl_objects s ptr = Some (C obj) \<longrightarrow> R obj s))
                     (\<lambda>s. (\<forall>obj'. AP ptr s = Some obj' \<longrightarrow> R' (AP_LIFT obj' s) s) \<and> AP ptr s \<noteq> None \<and> AP_Q s)
                     (KHeap_D.get_object ptr >>= a) c"
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_gets_the_bind)
    apply (rule corres_underlying_gets_pre_lhs)
    apply (rule_tac  F = "\<exists>obj. x = C obj" in corres_gen_asm)
    apply clarsimp
    apply (rule_tac P = "\<lambda>s. R (UN_C (C obj)) s \<and> cdl_objects s ptr = Some (C obj)"
      and P' = "\<lambda>s. (\<forall>obj'. AP ptr s = Some obj' \<longrightarrow> R' (UN_C (C (AP_LIFT obj' s))) s) \<and> AP ptr s \<noteq> None \<and> AP_Q s"
      in stronger_corres_guard_imp)
      apply (rule c)
     apply (simp add: unc)
    apply clarsimp
    apply (drule (1) ap_lift [symmetric])
    apply (simp, simp add: unc) \<comment> \<open>yuck, first simp applies unc too early\<close>
   apply clarsimp
   apply (frule (1) ap_lift)
   apply (simp add: unc)
   apply fastforce
  apply (simp add: unc)
  done

lemma dcorres_get_object_special_2:
  fixes   AP_LIFT :: "tcb \<Rightarrow> det_state \<Rightarrow> cdl_tcb"
  assumes     ap_lift: "\<And>s obj. \<lbrakk> get_tcb ptr s = Some obj; AP_Q s\<rbrakk>
                   \<Longrightarrow> cdl_objects (transform s) ptr = Some (Tcb (AP_LIFT obj s))"
  and     c: "\<And>obj. dcorres r (R obj) (R' obj) (a (Tcb obj)) c"
  \<comment> \<open>weak\<close>
  shows   "dcorres r (\<lambda>s. (\<forall>obj. cdl_objects s ptr = Some (Tcb obj) \<longrightarrow> R obj s))
                     (\<lambda>s. (\<forall>obj'. get_tcb ptr s = Some obj' \<longrightarrow> R' (AP_LIFT obj' s) s) \<and>
                           get_tcb ptr s \<noteq> None \<and> AP_Q s)
                     (KHeap_D.get_object ptr >>= a) c"
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_gets_the_bind)
    apply (rule corres_underlying_gets_pre_lhs)
    apply (rule_tac  F = "\<exists>obj. x = Tcb obj" in corres_gen_asm)
    apply clarsimp
    apply (rule_tac P = "\<lambda>s. R (obj_tcb (Tcb obj)) s \<and> cdl_objects s ptr = Some (Tcb obj)"
      and P' = "\<lambda>s. (\<forall>obj'. get_tcb ptr s = Some obj' \<longrightarrow> R' (AP_LIFT obj' s) s) \<and> get_tcb ptr s \<noteq> None \<and> AP_Q s"
      in stronger_corres_guard_imp)
      apply (rule c)
     apply (simp add: obj_tcb_def)
    apply clarsimp
    apply (drule (1) ap_lift [symmetric])
    apply (simp, simp add: obj_tcb_def)
   apply clarsimp
   apply (frule (1) ap_lift)
   apply (simp add: obj_tcb_def)+
  done

lemma dcorres_thread_get_get_object_split:
  assumes c: "\<And>tcb tcb'. dcorres r P (P' tcb tcb') (a (Tcb tcb')) (c (f tcb))"
  shows   "dcorres r P ((\<lambda>s. \<forall>tcb. get_tcb ptr s = Some tcb \<longrightarrow>
                            not_idle_thread ptr s \<and> P' tcb (obj_tcb (transform_tcb (machine_state s) ptr tcb)) s)
                        and not_idle_thread ptr)
             (KHeap_D.get_object ptr >>= a) (thread_get f ptr >>= c)"
  apply (simp add: thread_get_def)
  apply (rule corres_guard_imp)
    apply (rule corres_symb_exec_r)
       apply (rule dcorres_get_object_special_2 [where AP_LIFT = "\<lambda>tcb s. obj_tcb (transform_tcb (machine_state s) ptr tcb)"
         and AP_Q = "not_idle_thread ptr"])
        apply (simp add: obj_tcb_def)
        apply (drule opt_object_tcb, simp, simp add: not_idle_thread_def)
        apply (simp add: transform_tcb_def obj_tcb_def)
       apply (rule c)
      apply wp+
     apply clarsimp
    apply simp
   apply simp
  apply clarsimp
  done

(* MOVE *)
primrec (nonexhaustive)
  obj_cnode :: "cdl_object \<Rightarrow> cdl_cnode"
where
  "obj_cnode (Types_D.CNode cnode) = cnode"

(* MOVE *)
definition
  "get_cnode' ptr s \<equiv> case (kheap s ptr) of Some (Structures_A.CNode sz cn) \<Rightarrow> Some (sz,cn) | _ \<Rightarrow> None"

lemma get_cnode'D:
  "get_cnode' ptr s = Some (sz,cn) \<Longrightarrow> kheap s ptr = Some (Structures_A.CNode sz cn)"
  unfolding get_cnode'_def by (clarsimp split: Structures_A.kernel_object.splits option.splits)

lemma zombie_get_cnode:
  "\<lbrakk>cte_wp_at ((=) (cap.Zombie x (Some xc) xb)) slot s; invs s\<rbrakk> \<Longrightarrow> get_cnode' x s \<noteq> None"
  by (clarsimp dest!: cte_wp_at_valid_objs_valid_cap [OF _ invs_valid_objs] simp: valid_cap_simps get_cnode'_def obj_at_def
    elim!: is_cap_tableE)

definition
  object_at :: "(cdl_object \<Rightarrow> bool) \<Rightarrow> cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> bool"
where
  "object_at P obj_id s \<equiv> \<exists>object. cdl_objects s obj_id = Some object \<and> P object"

(* FIXME: MOVE *)
definition
  "transform_cnode sz cn \<equiv>
  if sz = 0
  then IRQNode \<lparr> cdl_irq_node_caps = transform_cnode_contents sz cn \<rparr>
  else Types_D.CNode \<lparr> cdl_cnode_caps = transform_cnode_contents sz cn,
                       cdl_cnode_size_bits = sz \<rparr>"

definition
  cnode_size_bits :: "kernel_object \<Rightarrow> nat"
where
  "cnode_size_bits obj \<equiv> case obj of CNode sz cs \<Rightarrow> sz | _ \<Rightarrow> 0"

lemma dcorres_get_object_cnode_split:
  assumes c: "\<And>cnode. dcorres r P (P' cnode) (a (cdl_object.CNode cnode)) c"
  shows   "dcorres r P
                    (\<lambda>s. (\<forall>sz cs. (get_cnode' ptr s = Some (sz,cs)) \<longrightarrow> P' (obj_cnode (transform_cnode sz cs)) s) \<and>
                         get_cnode' ptr s \<noteq> None \<and>
                         cnode_size_bits (the (kheap s ptr)) \<noteq> 0 \<and>
                         valid_idle s)
                    (KHeap_D.get_object ptr >>= a) c"
  apply (rule corres_guard_imp [where
         Q = "\<lambda>s. \<forall>obj. cdl_objects s ptr = Some (cdl_object.CNode obj) \<longrightarrow> P s" and
         Q' = "\<lambda>s. (\<forall>obj'. (get_cnode' ptr s = Some obj')\<longrightarrow> (P' (obj_cnode (transform_cnode (fst obj') (snd obj'))) s) ) \<and>
                    get_cnode' ptr s \<noteq> None \<and> cnode_size_bits (the (kheap s ptr)) \<noteq> 0 \<and> valid_idle s"])
    apply (rule dcorres_get_object_special [where C = "Types_D.CNode" and UN_C = obj_cnode
           and AP = "\<lambda> ptr s. get_cnode' ptr s" and AP_LIFT = "\<lambda>cn _. obj_cnode (transform_cnode (fst cn) (snd cn))"
           and AP_Q = "\<lambda>s. cnode_size_bits (the (kheap s ptr)) \<noteq> 0 \<and> valid_idle s" and R="\<lambda>obj s. P s"])
      apply simp
     apply (case_tac obj)
     apply clarsimp
     apply (drule (1) opt_object_cnode [OF _ get_cnode'D])
     apply (simp add: transform_cnode_def) defer
    apply (rule c)
   apply simp_all
   apply (clarsimp split: nat.splits)
   apply (clarsimp simp: get_cnode'_def cnode_size_bits_def split:  option.splits kernel_object.split)
   apply (case_tac x2, simp_all)
  done

lemma dcorres_gba_no_effect:
  "dcorres dc \<top> \<top> (return a) (get_bound_notification tcb)"
  apply (clarsimp simp: get_bound_notification_def thread_get_def gets_the_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_r)
   apply (clarsimp simp: assert_opt_def corres_free_fail split: Structures_A.kernel_object.splits option.splits)
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
  "dcorres (dc \<oplus> dc) \<top>
     (valid_cnode_inv cnodeinv and invs and ct_in_state active
               and valid_pdpt_objs)
     (CNode_D.invoke_cnode (translate_cnode_invocation cnodeinv))
     (CSpace_A.invoke_cnode cnodeinv)"
  supply if_cong[cong]
  apply (simp add: CSpace_A.invoke_cnode_def CNode_D.invoke_cnode_def
                   translate_cnode_invocation_def
                split: Invocations_A.cnode_invocation.split
            split del: if_split)
  apply (intro allI conjI impI)
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
      apply (rule corres_guard_imp[OF revoke_cap_corres],simp+)
     apply (rule corres_guard_imp[OF delete_cap_corres])
      apply (simp+)[2]
    apply (rule corres_req[rotated])
     apply (rule corres_guard_imp)
       apply (erule corres_if)
        apply (rule swap_cap_corres)
       apply (rule corres_split_nor [OF move_cap_corres move_cap_corres])
        apply wp+
       apply (simp add: cte_wp_at_caps_of_state not_idle_thread_def)
       apply (wp cap_move_caps_of_state)
      apply simp
     apply (clarsimp simp: invs_mdb not_idle_thread_def
                           ex_cte_cap_to_cnode_always_appropriate_strg
                           real_cte_tcb_valid)
     apply (subst real_cte_weak_derived_not_reply_masterD, assumption,
            clarsimp+)
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (drule ex_cte_cap_to_not_idle,clarsimp+)+
     apply (intro conjI impI)
        apply (clarsimp simp:invs_valid_idle)+
     apply (drule valid_idle_has_null_cap[rotated -1],clarsimp+)[1]
    apply (clarsimp simp: transform_cslot_ptr_inj [OF cte_wp_at_cte_at real_cte_at_cte])
   apply (simp add: cap_null_reply_case_If case_bool_If)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_split[OF get_cur_thread_corres])
       apply (rule corres_split)
          apply (rule get_cap_corres)
          apply (simp add: transform_tcb_slot_simp)
         apply (simp split del: if_split)
         apply (rule corres_if_rhs2)
          apply (rule corres_trivial, simp)
         apply (simp add: when_def split del: if_split)
         apply (rule corres_if_rhs2)
          apply (rule corres_if_rhs2)
           apply (rule corres_trivial[OF corres_free_fail])
          apply (simp add: transform_tcb_slot_simp[symmetric] dc_def[symmetric])
          apply (rule move_cap_corres)
         apply (rule corres_trivial[OF corres_free_fail])
        apply (wp get_cap_wp)+
    apply (auto simp: transform_def transform_current_thread_def
                      ct_in_state_def not_idle_thread_def
                      cte_wp_at_caps_of_state
                dest: st_tcb_at_idle_thread ex_cte_cap_to_not_idle)[2]
  apply (case_tac "has_cancel_send_rights x7", frule has_cancel_send_rights_ep_cap,
              simp add: is_cap_simps)
   apply (clarsimp simp: when_def)
   apply (rule corres_guard_imp)
     apply (rule dcorres_ep_cancel_badge_sends, clarsimp+)
  done

crunch lookup_source_slot
  for inv[wp]: "P"

lemma corres_symb_exec_r_dcE:
  "\<lbrakk> \<And>P. \<lbrace>P\<rbrace> g \<lbrace>\<lambda>rv. P\<rbrace>;
     \<And>x. corres_underlying rel False False (dc \<oplus> anyrel) P (R x) (throwError e) (h x);
     \<lbrace>Q\<rbrace> g \<lbrace>R\<rbrace>,- \<rbrakk> \<Longrightarrow>
   corres_underlying rel False False (dc \<oplus> anyrel) P Q
      (throwError e) (g >>=E (\<lambda>x. h x))"
  unfolding bindE_def
  apply (rule corres_symb_exec_r[where Q'="\<lambda>rv. case rv of Inl _ \<Rightarrow> \<top> | Inr x \<Rightarrow> R x"])
     apply (simp add: lift_def split: sum.split)
    apply (simp add: validE_R_def validE_def)
    apply (erule hoare_chain, simp_all split: sum.split)[1]
   apply assumption
  apply (rule no_fail_pre, simp+)
  done

lemma decode_cnode_error_corres:
  "\<not> (\<exists> ui. (Some (CNodeIntent ui)) = (transform_intent (invocation_type label) args)) \<Longrightarrow>
     dcorres (dc \<oplus> anyrel) \<top> \<top>
      (throwError e)
      (Decode_A.decode_cnode_invocation label args (cap.CNodeCap word n list) excaps)"
  apply(subst (asm) (1) transform_intent_isnot_CNodeIntent)
  apply(unfold Decode_A.decode_cnode_invocation_def)
  apply (rule_tac label=label and args=args and exs=excaps in decode_cnode_cases2)
        apply (simp_all add: unlessE_whenE gen_invocation_type_eq del: disj_not1)
   apply clarsimp
   apply (rule corres_symb_exec_r_dcE, wp)
    apply (rule corres_symb_exec_r_dcE, wp)
     apply (rule corres_symb_exec_r_dcE, wp)
      apply (rule corres_symb_exec_r_dcE, wp)
       apply (rule corres_symb_exec_r_dcE)
         apply (rule hoare_pre, wp whenE_wp)
         apply simp
        apply (rule corres_trivial)
        apply (simp split: gen_invocation_labels.split invocation_label.split list.split)
        apply (auto)[1]
       apply wp+
  apply (elim disjE, simp_all)
    apply (simp add: whenE_def)
   apply (clarsimp simp: whenE_def)
  apply clarsimp
  apply (elim disjE)
   apply (clarsimp split: list.split_asm
            | rule corres_symb_exec_r_dcE[OF _ corres_trivial]
            | wp | simp split del: if_split)+
  done

lemma transform_cnode_index_and_depth_Some:
  "(transform_cnode_index_and_depth f xs = Some v)
     = (length xs > 1 \<and> f (xs ! 0) (xs ! 1) = v)"
  by (simp add: transform_cnode_index_and_depth_def split: list.split)

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

lemma ensure_no_children_dummy:
  "dcorres dc \<top> \<top> (return x) (ensure_no_children slot)"
  apply (simp add: ensure_no_children_def)
  apply (clarsimp simp: corres_underlying_def return_def in_monad bindE_def lift_def)
  apply fastforce
  done

lemma derive_cap_dummy:
  "dcorres dc \<top> \<top> (return x) (derive_cap slot cap)"
  apply (simp add: derive_cap_def)
  apply (cases cap, simp_all add: returnOk_def)
   apply (simp add: bindE_def)
   apply (rule corres_dummy_return_l)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF ensure_no_children_dummy, where R="\<lambda>_. \<top>" and R'="\<lambda>_. \<top>"])
       apply (clarsimp simp: corres_underlying_def lift_def return_def split: sum.splits)
       apply (fastforce simp: in_monad)
      apply wp+
    apply simp
   apply simp
  apply (clarsimp simp: arch_derive_cap_def)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap, simp_all split: option.splits)
      apply (simp_all add: returnOk_def throwError_def)
  done

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

lemmas transform_cslot_ptr_inj_real_cte =
  transform_cslot_ptr_inj [OF real_cte_at_cte real_cte_at_cte]

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

lemma cdl_right_UNIV:
  "UNIV = {Read, Write, Grant, GrantReply}"
  apply (rule set_eqI)
  apply (case_tac x, auto)
  done

lemma has_recycle_rights_eq [simp]:
  "CNode_D.has_cancel_send_rights (transform_cap cap) =
   CSpace_A.has_cancel_send_rights cap"
  apply (simp add: CNode_D.has_cancel_send_rights_def CSpace_A.has_cancel_send_rights_def split: cap.splits)
  apply (auto simp: transform_cap_def all_rights_def
              split: rights.splits arch_cap.splits)
  done

lemma get_index_Nil [simp]:
  "get_index [] n = None"
  by (simp add: get_index_def)

lemma throw_opt_None [simp]:
  "throw_opt x None = throwError x"
  by (simp add: throw_opt_def)

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
                    transform_intent_cnode_rotate_def
              split: list.splits)
  done

lemma cnode_decode_rotate_throw:
  "length caps \<le> 1 \<Longrightarrow>
  CNode_D.decode_cnode_invocation target target_ref caps
                                  (CNodeRotateIntent a b c d e f g h) =
  Monads_D.throw"
  apply (cases caps)
   apply (simp add: CNode_D.decode_cnode_invocation_def)[1]
  apply (case_tac list)
   apply (auto simp: CNode_D.decode_cnode_invocation_def get_index_def throw_on_none_def)
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
                transform_intent_cnode_rotate_def
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
   dcorres (dc \<oplus> (\<lambda>x y. x = translate_cnode_invocation y)) \<top>
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
      apply (clarsimp simp: defns split: splits)
       apply (rule corres_guard_imp)
         apply (rule corres_splitEE)
            apply (rule lookup_slot_for_cnode_op_corres, simp_all)[1]
           apply (rule dcorres_returnOk)
           apply (simp add: translate_cnode_invocation_def)
          apply wp
         apply wp
        apply simp
       apply fastforce
      apply (clarsimp simp: defns split: splits)
      apply (rule corres_guard_imp)
        apply (rule corres_splitEE)
           apply (rule lookup_slot_for_cnode_op_corres, simp_all)[1]
          apply (rule dcorres_returnOk)
          apply (simp add: translate_cnode_invocation_def)
         apply (wp+)[2]
       apply simp
      apply fastforce
     apply (clarsimp simp: defns split: splits)
     apply (rule corres_guard_imp)
       apply (rule corres_splitEE)
          apply (rule lookup_slot_for_cnode_op_corres, simp_all)[1]
         apply (rule corres_splitEE)
            apply simp
            apply (rule dcorres_ensure_empty)
           apply (rule dcorres_returnOk)
           apply (simp add: translate_cnode_invocation_def)
          apply (wp lsfco_not_idle)+
      apply simp
     apply fastforce
    apply (clarsimp simp: defns split: splits)
    apply (rule corres_guard_imp)
      apply (rule corres_splitEE)
         apply (rule lookup_slot_for_cnode_op_corres, simp_all)[1]
        apply (simp add: liftE_bindE)
        apply (rule corres_split)
           apply (rule get_cap_corres, rule refl)
          apply (rule corres_splitEE)
             apply (rule corres_whenE [where r=dc])
              apply simp
             apply (rule dcorres_throw)
            apply simp
           apply (rule dcorres_returnOk)
           apply (simp add: translate_cnode_invocation_def)
          apply (wp lsfco_not_idle hoare_drop_imps|simp)+
    apply fastforce
   apply (clarsimp simp: defns split: splits)

   apply (rule corres_guard_imp)
     apply (rule corres_splitEE)
        apply (rule lookup_slot_for_cnode_op_corres, simp_all)[1]
       apply (rule corres_splitEE)
          apply (rule lookup_slot_for_cnode_op_corres, simp_all)[1]
         apply (rule corres_splitEE)
            apply (rule lookup_slot_for_cnode_op_corres, simp_all)[1]
           apply (rule_tac P=\<top> and P'="real_cte_at pivot_slota and real_cte_at src_slota
                                       and real_cte_at dest_slota" in corres_splitEE)
              apply (rule corres_assume_pre)
              apply (rule corres_guard_imp)
                apply (rule corres_whenE [where r=dc])
                  apply (clarsimp simp: transform_cslot_ptr_inj_real_cte)
                 apply (rule dcorres_throw)
                apply simp
               apply simp
              apply simp
             apply (rule_tac P=\<top> and
                             P'="real_cte_at src_slota and real_cte_at dest_slota
                                 and valid_idle and not_idle_thread (fst dest_slota)"
                             in corres_splitEE)
                apply (rule corres_assume_pre)
                apply (rule corres_guard_imp)
                  apply (rule corres_whenE)
                    apply (clarsimp simp: transform_cslot_ptr_inj_real_cte)
                   apply simp
                   apply (rule dcorres_ensure_empty)
                  apply simp
                 apply simp
                apply simp
               apply (simp add: liftE_bindE)
               apply (rule corres_split)
                  apply (rule get_cap_corres, rule refl)
                 apply (rule corres_splitEE)
                    apply (rule corres_whenE [where r=dc], simp)
                     apply (rule dcorres_throw)
                    apply simp
                   apply (rule corres_split)
                      apply (rule get_cap_corres, rule refl)
                     apply (rule corres_splitEE)
                        apply (rule corres_whenE [where r=dc], simp)
                         apply (rule dcorres_throw)
                        apply simp
                       apply (rule dcorres_update_cap_data_bind, simp)
                       apply (rule dcorres_update_cap_data_bind, simp)
                       apply (rule whenE_throwError_corres_initial)
                         apply simp
                        apply simp
                       apply (rule whenE_throwError_corres_initial)
                         apply simp
                        apply simp
                       apply (rule dcorres_returnOk)
                       apply (simp add:translate_cnode_invocation_def)
                      apply (wp get_cap_wp | simp)+
         apply (rule_tac Q'="\<lambda>r. real_cte_at src_slota and valid_objs and
                                real_cte_at dest_slota and valid_idle and
                                     not_idle_thread (fst src_slota) and
                                     not_idle_thread (fst dest_slota) and
                                     not_idle_thread (fst r)"
                             in hoare_strengthen_postE_R)
         apply (wp lsfco_not_idle)
        apply (clarsimp simp:Invariants_AI.cte_wp_valid_cap)
       apply (wp lsfco_not_idle)+
    apply simp
   apply fastforce
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
                        transform_intent_cnode_rotate_def
                  simp flip: gen_invocation_type_eq
                  split: list.splits)
   apply (simp add: cnode_decode_rotate_throw transform_cap_list_def)
   apply (simp add: Decode_A.decode_cnode_invocation_def unlessE_whenE gen_invocation_type_eq)
   apply (rule corres_bindE_throwError, wp, simp)
  apply (simp add: cnode_decode_rotate_throw transform_cap_list_def)
  apply (simp add: Decode_A.decode_cnode_invocation_def unlessE_whenE gen_invocation_type_eq)
  apply (rule corres_bindE_throwError, wp, simp)
  done

lemma decode_cnode_label_not_match:
  "\<lbrakk>Some intent = transform_intent (invocation_type label) args; \<forall>ui. intent \<noteq> CNodeIntent ui\<rbrakk>
   \<Longrightarrow> \<lbrace>(=) s\<rbrace> Decode_A.decode_cnode_invocation label args (cap.CNodeCap a b c) (e) \<lbrace>\<lambda>r. \<bottom>\<rbrace>, \<lbrace>\<lambda>e. (=) s\<rbrace>"
  apply (case_tac "invocation_type label = GenInvocationLabel CNodeRevoke")
   apply (clarsimp simp:Decode_A.decode_untyped_invocation_def transform_intent_def)
   apply (clarsimp simp:transform_cnode_index_and_depth_def split:option.splits list.splits)
  apply (case_tac "invocation_type label = GenInvocationLabel CNodeDelete")
   apply (clarsimp simp:Decode_A.decode_untyped_invocation_def transform_intent_def)
   apply (clarsimp simp:transform_cnode_index_and_depth_def split:option.splits list.splits)
  apply (case_tac "invocation_type label = GenInvocationLabel CNodeCancelBadgedSends")
   apply (clarsimp simp:Decode_A.decode_untyped_invocation_def transform_intent_def)
   apply (clarsimp simp:transform_cnode_index_and_depth_def split:option.splits list.splits)
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
   apply (clarsimp simp:Decode_A.decode_untyped_invocation_def transform_intent_def)
   apply (clarsimp simp:transform_intent_cnode_rotate_def split:option.splits list.splits)
  apply (case_tac "invocation_type label = GenInvocationLabel CNodeSaveCaller")
   apply (clarsimp simp:Decode_A.decode_untyped_invocation_def transform_intent_def)
   apply (clarsimp simp:transform_cnode_index_and_depth_def split:option.splits list.splits)
  apply (clarsimp simp:Decode_A.decode_cnode_invocation_def unlessE_def)
  apply (subgoal_tac "\<not> gen_invocation_type label \<in> set [CNodeRevoke .e. CNodeSaveCaller]")
   apply (clarsimp simp: gen_invocation_type_eq)
   apply wp
  apply (clarsimp simp: upto_enum_def fromEnum_def toEnum_def enum_invocation_label
                        enum_gen_invocation_labels gen_invocation_type_eq)
  done

end

end
