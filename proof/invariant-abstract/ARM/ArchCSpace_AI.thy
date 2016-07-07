(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
ARM-specific CSpace invariants
*)

theory ArchCSpace_AI
imports "../CSpace_AI"
begin

context Arch begin global_naming ARM

named_theorems CSpace_AI_assms

(* FIXME: move? *)
lemma getActiveIRQ_wp [CSpace_AI_assms]:
  "irq_state_independent_A P \<Longrightarrow>
   valid P (do_machine_op getActiveIRQ) (\<lambda>_. P)"
  apply (simp add: getActiveIRQ_def do_machine_op_def split_def exec_gets
                   select_f_select[simplified liftM_def]
                   select_modify_comm gets_machine_state_modify)
  apply wp
  apply (clarsimp simp: irq_state_independent_A_def in_monad return_def split: if_splits)
  done

lemma weak_derived_valid_cap [CSpace_AI_assms]:
  "\<lbrakk> s \<turnstile> c; wellformed_cap c'; weak_derived c' c\<rbrakk> \<Longrightarrow> s \<turnstile> c'"
  apply (case_tac "c = c'", simp)
  apply (clarsimp simp: weak_derived_def)
  apply (clarsimp simp: copy_of_def split: split_if_asm)
  apply (auto simp: is_cap_simps same_object_as_def wellformed_cap_simps
                    valid_cap_def cap_aligned_def bits_of_def
                     aobj_ref_cases Let_def cap_asid_def
               split: cap.splits arch_cap.splits option.splits)
  done

lemma weak_derived_tcb_cap_valid [CSpace_AI_assms]:
  "\<lbrakk> tcb_cap_valid cap p s; weak_derived cap cap' \<rbrakk> \<Longrightarrow> tcb_cap_valid cap' p s"
  apply (clarsimp simp add: tcb_cap_valid_def weak_derived_def
                            obj_at_def is_tcb
                     split: option.split)
  apply (clarsimp simp: st_tcb_def2)
  apply (erule disjE, simp_all add: copy_of_def split: split_if_asm)
    apply clarsimp
   apply (clarsimp simp: tcb_cap_cases_def split: split_if_asm)
   apply (auto simp: is_cap_simps same_object_as_def
                     valid_ipc_buffer_cap_def
              split: cap.split_asm arch_cap.split_asm
                     Structures_A.thread_state.split_asm)[3]
  apply clarsimp
  done

lemma copy_obj_refs [CSpace_AI_assms]:
  "copy_of cap cap' \<Longrightarrow> obj_refs cap' = obj_refs cap"
  apply (cases cap)
  apply (auto simp: copy_of_def same_object_as_def is_cap_simps
                    aobj_ref_cases
             split: split_if_asm cap.splits arch_cap.splits)
  done

lemma weak_derived_cap_class[simp, CSpace_AI_assms]: 
  "weak_derived cap src_cap \<Longrightarrow> cap_class cap = cap_class src_cap"
  apply (simp add:weak_derived_def)
  apply (auto simp:copy_of_def same_object_as_def is_cap_simps cap_asid_base_def
    split:if_splits cap.splits arch_cap.splits)
  done

lemma weak_derived_obj_refs [CSpace_AI_assms]:
  "weak_derived dcap cap \<Longrightarrow> obj_refs dcap = obj_refs cap"
  by (cases dcap, auto simp: is_cap_simps weak_derived_def copy_of_def 
                             same_object_as_def aobj_ref_cases
                       split: split_if_asm cap.splits arch_cap.splits)

lemma weak_derived_obj_ref_of [CSpace_AI_assms]:
  "weak_derived dcap cap \<Longrightarrow> obj_ref_of dcap = obj_ref_of cap"
  by (cases dcap, auto simp: is_cap_simps weak_derived_def copy_of_def 
                             same_object_as_def aobj_ref_cases
                       split: split_if_asm cap.splits arch_cap.splits)

lemma set_free_index_invs [CSpace_AI_assms]:
  "\<lbrace>\<lambda>s. (free_index_of cap \<le> idx \<and> is_untyped_cap cap \<and> idx \<le> 2^cap_bits cap) \<and>
        invs s \<and> cte_wp_at (op = cap ) cref s\<rbrace>
   set_cap (free_index_update (\<lambda>_. idx) cap) cref 
   \<lbrace>\<lambda>rv s'. invs s'\<rbrace>"
  apply (rule hoare_grab_asm)+
  apply (simp add:invs_def valid_state_def)
  apply (rule hoare_pre)
  apply (wp set_free_index_valid_pspace[where cap = cap] set_free_index_valid_mdb
    set_cap_idle update_cap_ifunsafe)
  apply (simp add:valid_irq_node_def)
  apply wps
  apply (wp hoare_vcg_all_lift set_cap_irq_handlers set_cap.valid_arch_obj set_cap_valid_arch_caps
            set_cap.valid_global_objs set_cap_irq_handlers cap_table_at_lift_valid set_cap_typ_at )
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (rule conjI,simp add:valid_pspace_def)
  apply (rule conjI,clarsimp simp:is_cap_simps)
  apply (rule conjI,rule ext,clarsimp simp: is_cap_simps)
  apply (clarsimp simp:is_cap_simps appropriate_cte_cap_def)
  apply (intro conjI)
       apply (clarsimp split:cap.splits)
      apply (drule(1) if_unsafe_then_capD[OF caps_of_state_cteD])
       apply clarsimp
      apply (simp add:ex_cte_cap_wp_to_def appropriate_cte_cap_def)
     apply (clarsimp dest!:valid_global_refsD2 simp:cap_range_def)
    apply (simp add:valid_irq_node_def)
   apply clarsimp
   apply (clarsimp simp:valid_irq_node_def)
   apply (clarsimp simp:no_cap_to_obj_with_diff_ref_def cte_wp_at_caps_of_state vs_cap_ref_def)
   apply (case_tac capa)
    apply (simp_all add:table_cap_ref_def)
    apply (rename_tac arch_cap)
    apply (case_tac arch_cap)
    apply simp_all
  apply (clarsimp simp:cap_refs_in_kernel_window_def
              valid_refs_def simp del:split_paired_All)
  apply (drule_tac x = cref in spec)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (drule_tac x = ref in orthD2[rotated])
   apply (simp add:cap_range_def)
  apply (simp)
  done

lemma set_untyped_cap_as_full_valid_arch_caps [CSpace_AI_assms]:
  "\<lbrace>valid_arch_caps and cte_wp_at (op = src_cap) src\<rbrace>
   set_untyped_cap_as_full src_cap cap src 
   \<lbrace>\<lambda>ya. valid_arch_caps\<rbrace>"
  apply (clarsimp simp:valid_arch_caps_def set_untyped_cap_as_full_def)
  apply (intro conjI impI)
    apply (wp set_cap_valid_vs_lookup set_cap_valid_table_caps)
    apply (clarsimp simp del:fun_upd_apply simp:cte_wp_at_caps_of_state)
    apply (subst unique_table_refs_upd_eqD)
         apply ((simp add: is_cap_simps table_cap_ref_def)+)
      apply clarsimp
    apply (subst unique_table_caps_upd_eqD)
      apply simp+
    apply (clarsimp simp:is_cap_simps cte_wp_at_caps_of_state)+
  apply wp
  apply clarsimp
  done

lemma set_untyped_cap_as_full[wp, CSpace_AI_assms]:
  "\<lbrace>\<lambda>s. no_cap_to_obj_with_diff_ref a b s \<and> cte_wp_at (op = src_cap) src s\<rbrace>
   set_untyped_cap_as_full src_cap cap src 
   \<lbrace>\<lambda>rv s. no_cap_to_obj_with_diff_ref a b s\<rbrace>"
  apply (clarsimp simp:no_cap_to_obj_with_diff_ref_def)
  apply (wp hoare_vcg_ball_lift set_untyped_cap_as_full_cte_wp_at_neg)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (drule_tac x=src in bspec, simp)
  apply (erule_tac x=src_cap in allE)
  apply (auto simp: table_cap_ref_def masked_as_full_def 
             split: Structures_A.cap.splits arch_cap.splits option.splits 
                    vmpage_size.splits)
  done

lemma is_derived_is_cap:
  "is_derived m p cap cap' \<Longrightarrow> 
    (is_pg_cap cap = is_pg_cap cap')
  \<and> (is_pt_cap cap = is_pt_cap cap')
  \<and> (is_pd_cap cap = is_pd_cap cap')
  \<and> (is_ep_cap cap = is_ep_cap cap')
  \<and> (is_ntfn_cap cap = is_ntfn_cap cap')
  \<and> (is_cnode_cap cap = is_cnode_cap cap')
  \<and> (is_thread_cap cap = is_thread_cap cap')
  \<and> (is_zombie cap = is_zombie cap')
  \<and> (is_arch_cap cap = is_arch_cap cap')"
  apply (clarsimp simp: is_derived_def is_derived_arch_def split: split_if_asm)
  apply (clarsimp simp: cap_master_cap_def is_cap_simps
    split: cap.splits arch_cap.splits)+
  done

(* FIXME: move to CSpace_I near lemma vs_lookup1_tcb_update *)
lemma vs_lookup_pages1_tcb_update:
  "kheap s p = Some (TCB t) \<Longrightarrow>
   vs_lookup_pages1 (s\<lparr>kheap := kheap s(p \<mapsto> TCB t')\<rparr>) = vs_lookup_pages1 s"
  by (clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
             intro!: set_eqI)

(* FIXME: move to CSpace_I near lemma vs_lookup_tcb_update *)
lemma vs_lookup_pages_tcb_update:
  "kheap s p = Some (TCB t) \<Longrightarrow>
   vs_lookup_pages (s\<lparr>kheap := kheap s(p \<mapsto> TCB t')\<rparr>) = vs_lookup_pages s"
  by (clarsimp simp add: vs_lookup_pages_def vs_lookup_pages1_tcb_update)

(* FIXME: move to CSpace_I near lemma vs_lookup1_cnode_update *)
lemma vs_lookup_pages1_cnode_update:
  "kheap s p = Some (CNode n cs) \<Longrightarrow>
   vs_lookup_pages1 (s\<lparr>kheap := kheap s(p \<mapsto> CNode m cs')\<rparr>) =
   vs_lookup_pages1 s"
  by (clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
             intro!: set_eqI)

(* FIXME: move to CSpace_I near lemma vs_lookup_cnode_update *)
lemma vs_lookup_pages_cnode_update:
  "kheap s p = Some (CNode n cs) \<Longrightarrow>
   vs_lookup_pages (s\<lparr>kheap := kheap s(p \<mapsto> CNode n cs')\<rparr>) = vs_lookup_pages s"
  by (clarsimp simp: vs_lookup_pages_def
              dest!: vs_lookup_pages1_cnode_update[where m=n and cs'=cs'])

lemma set_untyped_cap_as_full_not_reachable_pg_cap[wp]:
  "\<lbrace>\<lambda>s. \<not> reachable_pg_cap cap' s\<rbrace>
   set_untyped_cap_as_full src_cap cap src
   \<lbrace>\<lambda>rv s. \<not> reachable_pg_cap cap' s\<rbrace>"
  apply (clarsimp simp: set_untyped_cap_as_full_def set_cap_def split_def
                        set_object_def)
  apply (wp get_object_wp | wpc)+
  apply (clarsimp simp: obj_at_def simp del: fun_upd_apply)
  apply (auto simp: obj_at_def reachable_pg_cap_def is_cap_simps
                    vs_lookup_pages_cnode_update vs_lookup_pages_tcb_update)
  done

lemma table_cap_ref_eq_rewrite:
  "\<lbrakk>cap_master_cap cap = cap_master_cap capa;(is_pg_cap cap \<or> vs_cap_ref cap = vs_cap_ref capa)\<rbrakk>
   \<Longrightarrow> table_cap_ref cap = table_cap_ref capa"
  apply (frule cap_master_cap_pg_cap)
  apply (case_tac "is_pg_cap cap")
    apply (clarsimp simp:is_cap_simps table_cap_ref_def vs_cap_ref_to_table_cap_ref cap_master_cap_pg_cap)+
  done

lemma is_derived_cap_asid_issues:
  "is_derived m p cap cap'
      \<Longrightarrow> ((is_pt_cap cap \<or> is_pd_cap cap) \<longrightarrow> cap_asid cap \<noteq> None)
             \<and> (is_pg_cap cap \<or> (vs_cap_ref cap = vs_cap_ref cap'))"
   unfolding is_derived_def
   apply (cases "is_derived_arch cap cap'")
    apply (erule is_derived_cap_arch_asid_issues)
    apply (clarsimp split: split_if_asm)+
   done

lemma is_derived_is_pt_pd:
  "is_derived m p cap cap' \<Longrightarrow> (is_pt_cap cap = is_pt_cap cap') \<and> (is_pd_cap cap = is_pd_cap cap')"
  apply (clarsimp simp: is_derived_def split: split_if_asm)
  apply (clarsimp simp: cap_master_cap_def is_pt_cap_def is_pd_cap_def
    split: cap.splits arch_cap.splits)+
  done

lemma cap_insert_valid_arch_caps [CSpace_AI_assms]:
  "\<lbrace>valid_arch_caps and (\<lambda>s. cte_wp_at (is_derived (cdt s) src cap) src s)\<rbrace>
     cap_insert cap src dest
   \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (simp add: cap_insert_def)
  apply (rule hoare_pre)
   apply (wp set_cap_valid_arch_caps get_cap_wp set_untyped_cap_as_full_valid_arch_caps
               | simp split del: split_if)+
      apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift set_untyped_cap_as_full_cte_wp_at_neg
                set_untyped_cap_as_full_is_final_cap'_neg set_untyped_cap_as_full_cte_wp_at hoare_vcg_ball_lift
                hoare_vcg_ex_lift hoare_vcg_disj_lift | wps)+
  apply (wp set_untyped_cap_as_full_obj_at_impossible)
  apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift set_untyped_cap_as_full_cte_wp_at_neg
    set_untyped_cap_as_full_is_final_cap'_neg hoare_vcg_ball_lift
    hoare_vcg_ex_lift | wps)+
  apply (wp set_untyped_cap_as_full_obj_at_impossible)
  apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift set_untyped_cap_as_full_cte_wp_at_neg
    set_untyped_cap_as_full_is_final_cap'_neg hoare_vcg_ball_lift
    hoare_vcg_ex_lift | wps)+
  apply (rule hoare_strengthen_post)
    prefer 2
    apply (erule iffD2[OF caps_of_state_cteD'])
  apply (wp set_untyped_cap_as_full_cte_wp_at hoare_vcg_all_lift hoare_vcg_imp_lift
    set_untyped_cap_as_full_cte_wp_at_neg hoare_vcg_ex_lift | clarsimp)+
  apply (rule hoare_strengthen_post)
    prefer 2
    apply (erule iffD2[OF caps_of_state_cteD'])
  apply (wp set_untyped_cap_as_full_cte_wp_at hoare_vcg_all_lift hoare_vcg_imp_lift
    set_untyped_cap_as_full_cte_wp_at_neg hoare_vcg_ex_lift | clarsimp)+
  apply (wp get_cap_wp)
  apply (intro conjI allI impI disj_subst)
          apply simp
         apply clarsimp
         defer
        apply (clarsimp simp:valid_arch_caps_def cte_wp_at_caps_of_state)
        apply (drule(1) unique_table_refs_no_cap_asidD)
        apply (frule is_derived_obj_refs)
        apply (frule is_derived_cap_asid_issues)
        apply (frule is_derived_is_cap)
        apply (clarsimp simp:no_cap_to_obj_with_diff_ref_def  Ball_def
          del:disjCI dest!: derived_cap_master_cap_eq)
        apply (drule table_cap_ref_eq_rewrite)
         apply clarsimp
        apply (erule_tac x=a in allE, erule_tac x=b in allE)
        apply simp
       apply simp
      apply (clarsimp simp:obj_at_def is_cap_simps valid_arch_caps_def)
      apply (frule(1) valid_table_capsD)
        apply (clarsimp simp:cte_wp_at_caps_of_state)
        apply (drule is_derived_is_pt_pd)
        apply (clarsimp simp:is_derived_def is_cap_simps)
       apply (clarsimp simp:cte_wp_at_caps_of_state)
       apply (frule is_derived_cap_asid_issues)
       apply (clarsimp simp:is_cap_simps)
      apply (clarsimp simp:cte_wp_at_caps_of_state)
      apply (frule is_derived_obj_refs)
      apply (drule_tac x = p in bspec)
        apply fastforce
      apply (clarsimp simp:obj_at_def empty_table_caps_of)
     apply (clarsimp simp:empty_table_caps_of valid_arch_caps_def)
     apply (frule(1) valid_table_capsD)
       apply (clarsimp simp:cte_wp_at_caps_of_state is_derived_is_pt_pd)
      apply (clarsimp simp:cte_wp_at_caps_of_state)
      apply (frule is_derived_cap_asid_issues)
      apply (clarsimp simp:is_cap_simps)
     apply (clarsimp simp:cte_wp_at_caps_of_state)
     apply (frule is_derived_obj_refs)
     apply (drule_tac x = x in bspec)
       apply fastforce
     subgoal by (clarsimp simp:obj_at_def empty_table_caps_of)
    apply (clarsimp simp:is_cap_simps cte_wp_at_caps_of_state)
    apply (frule is_derived_is_pt_pd)
    apply (frule is_derived_obj_refs)
    apply (frule is_derived_cap_asid_issues)
       apply (clarsimp simp:is_cap_simps valid_arch_caps_def cap_master_cap_def 
                            is_derived_def is_derived_arch_def)
       apply (drule_tac ptr = src and ptr' = "(x,xa)" in unique_table_capsD)
    apply (simp add:is_cap_simps)+
   apply (clarsimp simp:is_cap_simps cte_wp_at_caps_of_state)
   apply (frule is_derived_is_pt_pd)
   apply (frule is_derived_obj_refs)
   apply (frule is_derived_cap_asid_issues)
   apply (clarsimp simp:is_cap_simps valid_arch_caps_def
                        cap_master_cap_def cap_master_arch_cap_def
                        is_derived_def is_derived_arch_def)
   apply (drule_tac ptr = src and ptr' = "(x,xa)" in unique_table_capsD)
   apply (simp add:is_cap_simps)+
  apply (auto simp:cte_wp_at_caps_of_state)
done

end


global_interpretation cap_insert_crunches?: cap_insert_crunches .


context Arch begin global_naming ARM

lemma cap_insert_cap_refs_in_kernel_window[wp, CSpace_AI_assms]:
  "\<lbrace>cap_refs_in_kernel_window
          and cte_wp_at (\<lambda>c. cap_range cap \<subseteq> cap_range c) src\<rbrace>
     cap_insert cap src dest
   \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: cap_insert_def set_untyped_cap_as_full_def)
  apply (wp get_cap_wp | simp split del: split_if)+
  apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_def)
  apply (frule(1) cap_refs_in_kernel_windowD[where ptr=src])
  apply auto
  done


lemma mask_cap_valid[simp, CSpace_AI_assms]:
  "s \<turnstile> c \<Longrightarrow> s \<turnstile> mask_cap R c"
  apply (cases c, simp_all add: valid_cap_def mask_cap_def
                             cap_rights_update_def
                             cap_aligned_def
                             acap_rights_update_def)
  using valid_validate_vm_rights[simplified valid_vm_rights_def]
  apply (rename_tac arch_cap)
  by (case_tac arch_cap, simp_all)

lemma mask_cap_objrefs[simp, CSpace_AI_assms]:
  "obj_refs (mask_cap rs cap) = obj_refs cap"
  by (cases cap, simp_all add: mask_cap_def cap_rights_update_def
                               acap_rights_update_def
                        split: arch_cap.split)


lemma mask_cap_zobjrefs[simp, CSpace_AI_assms]:
  "zobj_refs (mask_cap rs cap) = zobj_refs cap"
  by (cases cap, simp_all add: mask_cap_def cap_rights_update_def
                               acap_rights_update_def
                        split: arch_cap.split)


lemma derive_cap_valid_cap [CSpace_AI_assms]:
  "\<lbrace>valid_cap cap\<rbrace> derive_cap slot cap \<lbrace>valid_cap\<rbrace>,-"
  apply (simp add: derive_cap_def)
  apply (rule hoare_pre)
   apply (wpc, (wp arch_derive_cap_valid_cap | simp)+)
  apply auto
  done


lemma valid_cap_update_rights[simp, CSpace_AI_assms]:
  "valid_cap cap s \<Longrightarrow> valid_cap (cap_rights_update cr cap) s"
  apply (case_tac cap,
         simp_all add: cap_rights_update_def valid_cap_def cap_aligned_def
                       acap_rights_update_def)
  using valid_validate_vm_rights[simplified valid_vm_rights_def]
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap, simp_all)
  done


lemma update_cap_data_validI [CSpace_AI_assms]:
  "s \<turnstile> cap \<Longrightarrow> s \<turnstile> update_cap_data p d cap"
  apply (cases cap)
  apply (simp_all add: is_cap_defs update_cap_data_def Let_def split_def)
     apply (simp add: valid_cap_def cap_aligned_def)
    apply (simp add: valid_cap_def cap_aligned_def)
   apply (simp add: the_cnode_cap_def valid_cap_def cap_aligned_def)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap)
      apply (simp_all add: is_cap_defs arch_update_cap_data_def)
  done


lemma tcb_cnode_index_def2 [CSpace_AI_assms]:
  "tcb_cnode_index n = nat_to_cref 3 n"
  apply (simp add: tcb_cnode_index_def nat_to_cref_def)
  apply (rule nth_equalityI)
   apply (simp add: word_bits_def)
  apply (clarsimp simp: to_bl_nth word_size word_bits_def)
  apply (subst of_nat_ucast[where 'a=32 and 'b=3])
   apply (simp add: is_down_def target_size_def source_size_def word_size)
  apply (simp add: nth_ucast)
  apply fastforce
  done


lemma ex_nonz_tcb_cte_caps [CSpace_AI_assms]:
  "\<lbrakk>ex_nonz_cap_to t s; tcb_at t s; valid_objs s; ref \<in> dom tcb_cap_cases\<rbrakk>
   \<Longrightarrow> ex_cte_cap_wp_to (appropriate_cte_cap cp) (t, ref) s"
  apply (clarsimp simp: ex_nonz_cap_to_def ex_cte_cap_wp_to_def
                        cte_wp_at_caps_of_state)
  apply (subgoal_tac "s \<turnstile> cap")
   apply (rule_tac x=a in exI, rule_tac x=ba in exI)
   apply (clarsimp simp: valid_cap_def obj_at_def
                         is_obj_defs dom_def
                         appropriate_cte_cap_def
                  split: cap.splits arch_cap.split_asm)
  apply (clarsimp simp: caps_of_state_valid_cap)
  done


lemma no_cap_to_obj_with_diff_ref_triv:
  "\<lbrakk> valid_objs s; valid_cap cap s; \<not> is_pt_cap cap;
           \<not> is_pd_cap cap; table_cap_ref cap = None \<rbrakk>
      \<Longrightarrow> no_cap_to_obj_with_diff_ref cap S s"
  apply (clarsimp simp add: no_cap_to_obj_with_diff_ref_def)
  apply (drule(1) cte_wp_at_valid_objs_valid_cap)
  apply (clarsimp simp: table_cap_ref_def valid_cap_def
                        obj_at_def is_ep is_ntfn is_tcb is_cap_table
                        a_type_def is_cap_simps
                 split: cap.split_asm arch_cap.split_asm
                        split_if_asm option.split_asm)
        apply auto
  done


lemma setup_reply_master_arch_caps[wp, CSpace_AI_assms]:
  "\<lbrace>valid_arch_caps and tcb_at t and valid_objs and pspace_aligned\<rbrace>
     setup_reply_master t
   \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (simp add: setup_reply_master_def)
  apply (wp set_cap_valid_arch_caps get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state is_pd_cap_def
                        is_pt_cap_def vs_cap_ref_def)
  apply (rule no_cap_to_obj_with_diff_ref_triv,
         simp_all add: is_cap_simps table_cap_ref_def)
  apply (simp add: valid_cap_def cap_aligned_def word_bits_def)
  apply (clarsimp simp: obj_at_def is_tcb dest!: pspace_alignedD)
  done


lemma setup_reply_master_cap_refs_in_kernel_window[wp, CSpace_AI_assms]:
  "\<lbrace>cap_refs_in_kernel_window and tcb_at t and pspace_in_kernel_window\<rbrace>
      setup_reply_master t
   \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: setup_reply_master_def)
  apply (wp get_cap_wp)
  apply (clarsimp simp: pspace_in_kernel_window_def obj_at_def
                        cap_range_def)
  done


(* FIXME: prove same_region_as_def2 instead or change def *)
lemma same_region_as_Untyped2 [CSpace_AI_assms]:
  "\<lbrakk> is_untyped_cap pcap; same_region_as pcap cap \<rbrakk> \<Longrightarrow>
  (is_physical cap \<and> cap_range cap \<noteq> {} \<and> cap_range cap \<subseteq> cap_range pcap)"
  by (fastforce simp: is_cap_simps cap_range_def is_physical_def arch_is_physical_def
               split: cap.splits arch_cap.splits)


lemma same_region_as_cap_class [CSpace_AI_assms]:
  shows "same_region_as a b \<Longrightarrow> cap_class a = cap_class b"
  apply (case_tac a)
   apply (fastforce simp: cap_range_def arch_is_physical_def is_cap_simps
     is_physical_def split:cap.splits arch_cap.splits)+
 apply (clarsimp split: arch_cap.splits cap.splits)
 apply (rename_tac arch_cap arch_capa)
 apply (case_tac arch_cap)
  apply (case_tac arch_capa,clarsimp+)+
 done


lemma cap_insert_simple_arch_caps_no_ap:
  "\<lbrace>valid_arch_caps and (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src cap) src s)
             and no_cap_to_obj_with_diff_ref cap {dest} and K (is_simple_cap cap \<and> \<not>is_ap_cap cap)\<rbrace>
     cap_insert cap src dest
   \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (simp add: cap_insert_def)
  apply (wp set_cap_valid_arch_caps set_untyped_cap_as_full_valid_arch_caps get_cap_wp
    | simp split del: split_if)+
  apply (wp hoare_vcg_all_lift hoare_vcg_conj_lift hoare_vcg_imp_lift hoare_vcg_ball_lift hoare_vcg_disj_lift
    set_untyped_cap_as_full_cte_wp_at_neg set_untyped_cap_as_full_is_final_cap'_neg
    set_untyped_cap_as_full_empty_table_at hoare_vcg_ex_lift
    set_untyped_cap_as_full_caps_of_state_diff[where dest=dest]
    | wps)+
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (intro conjI impI allI)
  by (auto simp:is_simple_cap_def[simplified is_simple_cap_arch_def] is_cap_simps)

end


global_interpretation CSpace_AI?: CSpace_AI_7
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact CSpace_AI_assms)?)
  qed


context Arch begin global_naming ARM

lemma cap_insert_simple_invs:
  "\<lbrace>invs and valid_cap cap and tcb_cap_valid cap dest and
    ex_cte_cap_wp_to (appropriate_cte_cap cap) dest and
    cte_wp_at (\<lambda>c. is_untyped_cap c \<longrightarrow> usable_untyped_range c = {}) src and
    cte_wp_at (\<lambda>c. c = cap.NullCap) dest and 
    no_cap_to_obj_with_diff_ref cap {dest} and
    (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src cap) src s) and
    K (is_simple_cap cap \<and> \<not>is_ap_cap cap) and (\<lambda>s. \<forall>irq \<in> cap_irqs cap. irq_issued irq s)\<rbrace>
  cap_insert cap src dest \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre)
   apply (wp cap_insert_simple_mdb cap_insert_iflive 
             cap_insert_zombies cap_insert_ifunsafe 
             cap_insert_valid_global_refs cap_insert_idle
             valid_irq_node_typ cap_insert_simple_arch_caps_no_ap)
  apply (clarsimp simp: is_simple_cap_def cte_wp_at_caps_of_state)
  apply (drule safe_parent_cap_range)
  apply simp
  apply (rule conjI)
   prefer 2
   apply (clarsimp simp: is_cap_simps)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule_tac p="(a,b)" in caps_of_state_valid_cap, fastforce)
  apply (clarsimp dest!: is_cap_simps [THEN iffD1])
  apply (auto simp add: valid_cap_def [where c="cap.Zombie a b x" for a b x]
              dest: obj_ref_is_tcb obj_ref_is_cap_table split: option.splits)
  done

lemmas is_derived_def = is_derived_def[simplified is_derived_arch_def]

end

end
