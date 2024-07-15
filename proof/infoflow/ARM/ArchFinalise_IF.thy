(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchFinalise_IF
imports Finalise_IF
begin

context Arch begin global_naming ARM

named_theorems Finalise_IF_assms

crunch arch_post_cap_deletion
  for globals_equiv[Finalise_IF_assms, wp]: "globals_equiv st"

lemma dmo_maskInterrupt_reads_respects[Finalise_IF_assms]:
  "reads_respects aag l \<top> (do_machine_op (maskInterrupt m irq))"
  unfolding maskInterrupt_def
  apply (rule use_spec_ev)
  apply (rule do_machine_op_spec_reads_respects)
   apply (simp add: equiv_valid_def2)
   apply (rule modify_ev2)
   apply (fastforce simp: equiv_for_def)
  apply (wp modify_wp | simp)+
  done

lemma arch_post_cap_deletion_read_respects[Finalise_IF_assms, wp]:
  "reads_respects aag l \<top> (arch_post_cap_deletion acap)"
  by wpsimp

lemma equiv_asid_sa_update[Finalise_IF_assms, simp]:
  "equiv_asid asid (scheduler_action_update f s) s' = equiv_asid asid s s'"
  "equiv_asid asid s (scheduler_action_update f s') = equiv_asid asid s s'"
  by (auto simp: equiv_asid_def)

lemma equiv_asid_ready_queues_update[Finalise_IF_assms, simp]:
  "equiv_asid asid (ready_queues_update f s) s' = equiv_asid asid s s'"
  "equiv_asid asid s (ready_queues_update f s') = equiv_asid asid s s'"
  by (auto simp: equiv_asid_def)

lemma arch_finalise_cap_makes_halted[Finalise_IF_assms]:
  "\<lbrace>invs and valid_cap (ArchObjectCap arch_cap)
        and (\<lambda>s. ex = is_final_cap' (ArchObjectCap arch_cap) s)
        and cte_wp_at ((=) (ArchObjectCap arch_cap)) slot\<rbrace>
   arch_finalise_cap arch_cap ex
   \<lbrace>\<lambda>rv s. \<forall>t \<in> obj_refs_ac (fst rv). halted_if_tcb t s\<rbrace>"
  by (wpsimp simp: arch_finalise_cap_def)

(* FIXME: move *)
lemma set_object_modifies_at_most:
  "modifies_at_most aag {pasObjectAbs aag ptr}
                    (\<lambda>s. \<not> asid_pool_at ptr s \<and> (\<forall>asid_pool. obj \<noteq> ArchObj (ASIDPool asid_pool)))
                    (set_object ptr obj)"
  apply (rule modifies_at_mostI)
  apply (wp set_object_equiv_but_for_labels)
  apply clarsimp
  done

lemma set_thread_state_reads_respects[Finalise_IF_assms]:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "reads_respects aag l (\<lambda>s. is_subject aag (cur_thread s)) (set_thread_state ref ts)"
  unfolding set_thread_state_def fun_app_def
  apply (simp add: bind_assoc[symmetric])
  apply (rule pre_ev)
   apply (rule_tac P'=\<top> in bind_ev)
     apply (rule set_thread_state_ext_reads_respects)
    apply (case_tac "aag_can_read aag ref \<or> aag_can_affect aag l ref")
     apply (wp set_object_reads_respects gets_the_ev)
     apply (fastforce simp: get_tcb_def split: option.splits
                     elim: reads_equivE affects_equivE equiv_forE)
    apply (simp add: equiv_valid_def2)
    apply (rule equiv_valid_rv_bind)
      apply (rule equiv_valid_rv_trivial)
      apply (wp | simp)+
     apply (rule_tac P=\<top> and P'=\<top> and L="{pasObjectAbs aag ref}" and L'="{pasObjectAbs aag ref}"
                  in ev2_invisible[OF domains_distinct])
         apply (blast | simp add: labels_are_invisible_def)+
       apply (rule set_object_modifies_at_most)
      apply (rule set_object_modifies_at_most)
     apply (simp | wp)+
    apply (blast dest: get_tcb_not_asid_pool_at)
   apply (subst thread_set_def[symmetric, simplified fun_app_def])
   apply (wp | simp)+
  done

lemma set_thread_state_runnable_reads_respects[Finalise_IF_assms]:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "runnable ts \<Longrightarrow> reads_respects aag l \<top> (set_thread_state ref ts)"
  unfolding set_thread_state_def fun_app_def
  apply (simp add: bind_assoc[symmetric])
  apply (rule pre_ev)
   apply (rule_tac P'=\<top> in bind_ev)
     apply (rule set_thread_state_ext_runnable_reads_respects)
    apply (case_tac "aag_can_read aag ref \<or> aag_can_affect aag l ref")
     apply (wp set_object_reads_respects gets_the_ev)
     apply (fastforce simp: get_tcb_def split: option.splits elim: reads_equivE affects_equivE equiv_forE)
    apply (simp add: equiv_valid_def2)
    apply (rule equiv_valid_rv_bind)
      apply (rule equiv_valid_rv_trivial)
      apply (wp | simp)+
     apply (rule_tac P=\<top> and P'=\<top> and L="{pasObjectAbs aag ref}" and L'="{pasObjectAbs aag ref}"
                  in ev2_invisible[OF domains_distinct])
         apply (blast | simp add: labels_are_invisible_def)+
       apply (rule set_object_modifies_at_most)
      apply (rule set_object_modifies_at_most)
     apply (simp | wp)+
    apply (blast dest: get_tcb_not_asid_pool_at)
   apply (subst thread_set_def[symmetric, simplified fun_app_def])
   apply (wp thread_set_st_tcb_at | simp)+
   done

lemma set_bound_notification_none_reads_respects[Finalise_IF_assms]:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "reads_respects aag l \<top> (set_bound_notification ref None)"
  unfolding set_bound_notification_def fun_app_def
  apply (rule pre_ev(5)[where Q=\<top>])
   apply (case_tac "aag_can_read aag ref \<or> aag_can_affect aag l ref")
    apply (wp set_object_reads_respects gets_the_ev)[1]
    apply (fastforce simp: get_tcb_def split: option.splits elim: reads_equivE affects_equivE equiv_forE)
   apply (simp add: equiv_valid_def2)
   apply (rule equiv_valid_rv_bind)
     apply (rule equiv_valid_rv_trivial)
     apply (wp | simp)+
    apply (rule_tac P=\<top> and P'=\<top> and L="{pasObjectAbs aag ref}" and L'="{pasObjectAbs aag ref}"
                 in ev2_invisible[OF domains_distinct])
        apply (blast | simp add: labels_are_invisible_def)+
      apply (rule set_object_modifies_at_most)
     apply (rule set_object_modifies_at_most)
    apply (simp | wp)+
   apply (blast dest: get_tcb_not_asid_pool_at)
  apply simp
  done

lemma set_tcb_queue_reads_respects[Finalise_IF_assms, wp]:
  "reads_respects aag l \<top> (set_tcb_queue d prio queue)"
  unfolding equiv_valid_def2 equiv_valid_2_def
  apply (clarsimp simp: set_tcb_queue_def bind_def modify_def put_def get_def)
  apply (rule conjI)
   apply (rule reads_equiv_ready_queues_update, assumption)
   apply (fastforce simp: reads_equiv_def affects_equiv_def states_equiv_for_def equiv_for_def)
  apply (rule affects_equiv_ready_queues_update, assumption)
  apply (clarsimp simp: reads_equiv_def affects_equiv_def states_equiv_for_def equiv_for_def
                        equiv_asids_def equiv_asid_def)
  apply (rule ext)
  apply force
  done

lemma set_tcb_queue_modifies_at_most:
  "modifies_at_most aag L (\<lambda>s. pasDomainAbs aag d \<inter> L \<noteq> {}) (set_tcb_queue d prio queue)"
  apply (rule modifies_at_mostI)
  apply (simp add: set_tcb_queue_def modify_def, wp)
  apply (force simp: equiv_but_for_labels_def states_equiv_for_def equiv_for_def equiv_asids_def)
  done

lemma set_notification_equiv_but_for_labels[Finalise_IF_assms]:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag ntfnptr \<in> L)\<rbrace>
   set_notification ntfnptr ntfn
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding set_simple_ko_def
  apply (wp set_object_equiv_but_for_labels get_object_wp)
  apply (clarsimp simp: asid_pool_at_kheap partial_inv_def obj_at_def split: kernel_object.splits)
  done

lemma thread_set_reads_respects[Finalise_IF_assms]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects aag l \<top> (thread_set x y)"
  unfolding thread_set_def fun_app_def
  apply (case_tac "aag_can_read aag y \<or> aag_can_affect aag l y")
   apply (wp set_object_reads_respects)
   apply (clarsimp, rule reads_affects_equiv_get_tcb_eq, simp+)[1]
  apply (simp add: equiv_valid_def2)
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule_tac L="{pasObjectAbs aag y}" and L'="{pasObjectAbs aag y}"
                in ev2_invisible[OF domains_distinct])
       apply (assumption | simp add: labels_are_invisible_def)+
     apply (rule modifies_at_mostI[where P="\<top>"]
            | wp set_object_equiv_but_for_labels
            | simp
            | (clarify, drule get_tcb_not_asid_pool_at))+
  done

lemma aag_cap_auth_ASIDPoolCap:
  "pas_cap_cur_auth aag (ArchObjectCap (ASIDPoolCap r asid)) \<Longrightarrow>
   pas_refined aag s \<Longrightarrow> is_subject aag r"
  unfolding aag_cap_auth_def
  by (simp add: clas_no_asid cap_auth_conferred_def arch_cap_auth_conferred_def
                cli_no_irqs pas_refined_all_auth_is_owns is_page_cap_def)

lemma aag_cap_auth_PageDirectory:
  "pas_cap_cur_auth aag (ArchObjectCap (PageDirectoryCap word (Some a))) \<Longrightarrow>
    pas_refined aag s \<Longrightarrow> is_subject aag word"
  unfolding aag_cap_auth_def
  by (simp add: clas_no_asid cap_auth_conferred_def arch_cap_auth_conferred_def
                cli_no_irqs pas_refined_all_auth_is_owns is_page_cap_def)

lemma aag_cap_auth_ASIDPoolCap_asid:
  "\<lbrakk> pas_cap_cur_auth aag (ArchObjectCap (ASIDPoolCap r asid)); asid' \<noteq> 0;
     asid_high_bits_of asid' = asid_high_bits_of asid; pas_refined aag s \<rbrakk>
     \<Longrightarrow> is_subject_asid aag asid'"
  apply (frule (1) aag_cap_auth_ASIDPoolCap)
  apply (unfold aag_cap_auth_def)
  apply (rule is_subject_into_is_subject_asid)
  apply auto
  done

lemma aag_cap_auth_PageCap_asid:
  "\<lbrakk> pas_cap_cur_auth aag (ArchObjectCap (PageCap dev ref r sz (Some (a, b)))); pas_refined aag s \<rbrakk>
     \<Longrightarrow> is_subject_asid aag a"
  by (auto simp: aag_cap_auth_def cap_links_asid_slot_def label_owns_asid_slot_def
          intro: pas_refined_Control_into_is_subject_asid)

lemma aag_cap_auth_PageTableCap:
  "\<lbrakk> pas_cap_cur_auth aag (ArchObjectCap (PageTableCap word option)); pas_refined aag s \<rbrakk>
     \<Longrightarrow> is_subject aag word"
  unfolding aag_cap_auth_def
  by (simp add: clas_no_asid cap_auth_conferred_def arch_cap_auth_conferred_def
                cli_no_irqs pas_refined_all_auth_is_owns is_page_cap_def)

lemma aag_cap_auth_PageTableCap_asid:
  "\<lbrakk> pas_cap_cur_auth aag (ArchObjectCap (PageTableCap word (Some (a, b)))); pas_refined aag s \<rbrakk>
     \<Longrightarrow> is_subject_asid aag a"
  by (auto simp: aag_cap_auth_def cap_links_asid_slot_def label_owns_asid_slot_def
          intro: pas_refined_Control_into_is_subject_asid)

lemma aag_cap_auth_PageDirectoryCap:
  "\<lbrakk> pas_cap_cur_auth aag (ArchObjectCap (PageDirectoryCap word option));  pas_refined aag s \<rbrakk>
     \<Longrightarrow> is_subject aag word"
  unfolding aag_cap_auth_def
  by (simp add: clas_no_asid cap_auth_conferred_def arch_cap_auth_conferred_def
                cli_no_irqs pas_refined_all_auth_is_owns is_page_cap_def)

lemma aag_cap_auth_PageDirectoryCap_asid:
  "\<lbrakk> pas_cap_cur_auth aag (ArchObjectCap (PageDirectoryCap word (Some a))); pas_refined aag s \<rbrakk>
     \<Longrightarrow> is_subject_asid aag a"
  unfolding aag_cap_auth_def
  by (auto simp: cap_links_asid_slot_def label_owns_asid_slot_def
          intro: pas_refined_Control_into_is_subject_asid)

lemmas aag_cap_auth_subject = aag_cap_auth_ASIDPoolCap_asid
                              aag_cap_auth_PageCap_asid
                              aag_cap_auth_PageTableCap_asid
                              aag_cap_auth_PageDirectoryCap_asid

lemma prepare_thread_delete_reads_respects_f[Finalise_IF_assms]:
  "reads_respects_f aag l \<top> (prepare_thread_delete thread)"
  unfolding prepare_thread_delete_def by wp

lemma arch_finalise_cap_reads_respects[Finalise_IF_assms]:
  "reads_respects aag l (pas_refined aag and invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
                                         and K (pas_cap_cur_auth aag (ArchObjectCap cap)))
                        (arch_finalise_cap cap final)"
  unfolding arch_finalise_cap_def
  apply (rule gen_asm_ev)
  apply (case_tac cap)
  apply simp
  apply (simp split: bool.splits)
  apply (intro impI conjI)
  by (wp delete_asid_pool_reads_respects
         unmap_page_reads_respects
         unmap_page_table_reads_respects
         delete_asid_reads_respects
      | simp add: invs_psp_aligned invs_vspace_objs invs_valid_objs valid_cap_def
           split: option.splits bool.splits
      | intro impI conjI allI
      | elim conjE
      | rule aag_cap_auth_subject,assumption,assumption
      | drule cte_wp_valid_cap)+

(*NOTE: Required to dance around the issue of the base potentially
        being zero and thus we can't conclude it is in the current subject.*)
lemma requiv_arm_asid_table_asid_high_bits_of_asid_eq':
  "\<lbrakk> pas_cap_cur_auth aag (ArchObjectCap (ASIDPoolCap p b)); reads_equiv aag s t; pas_refined aag x \<rbrakk>
     \<Longrightarrow> arm_asid_table (arch_state s) (asid_high_bits_of b) =
         arm_asid_table (arch_state t) (asid_high_bits_of b)"
  apply (subgoal_tac "asid_high_bits_of 0 = asid_high_bits_of 1")
   apply (case_tac "b = 0")
    apply (subgoal_tac "is_subject_asid aag 1")
     apply ((fastforce intro: requiv_arm_asid_table_asid_high_bits_of_asid_eq
                              aag_cap_auth_ASIDPoolCap_asid)+)[2]
   apply (auto intro: requiv_arm_asid_table_asid_high_bits_of_asid_eq
                      aag_cap_auth_ASIDPoolCap_asid)[1]
  apply (simp add: asid_high_bits_of_def asid_low_bits_def)
  done

lemma pt_cap_aligned:
  "\<lbrakk> caps_of_state s p = Some (ArchObjectCap (PageTableCap word x)); valid_caps (caps_of_state s) s \<rbrakk>
     \<Longrightarrow> is_aligned word pt_bits"
  by (auto simp: obj_ref_of_def pt_bits_def pageBits_def
          dest!: cap_aligned_valid[OF valid_capsD, unfolded cap_aligned_def, THEN conjunct1])

lemma maskInterrupt_no_mem:
  "maskInterrupt a b \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace>"
  by (wpsimp simp: maskInterrupt_def)

lemma maskInterrupt_no_exclusive:
  "maskInterrupt a b \<lbrace>\<lambda>ms. P (exclusive_state ms)\<rbrace>"
  by (wpsimp simp: maskInterrupt_def)

lemma set_irq_state_valid_global_objs:
  "set_irq_state state irq \<lbrace>valid_global_objs\<rbrace>"
  apply (simp add: set_irq_state_def)
  apply (wp modify_wp)
  apply (fastforce simp: valid_global_objs_def)
  done

lemma set_irq_state_globals_equiv[Finalise_IF_assms]:
  "set_irq_state state irq \<lbrace>globals_equiv st\<rbrace>"
  apply (simp add: set_irq_state_def)
  apply (wp dmo_no_mem_globals_equiv maskInterrupt_no_mem maskInterrupt_no_exclusive modify_wp)
  apply (simp add: globals_equiv_interrupt_states_update)
  done

lemma set_notification_globals_equiv[Finalise_IF_assms]:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   set_notification ptr ntfn
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding set_simple_ko_def
  apply (wp set_object_globals_equiv get_object_wp)
  apply (fastforce simp: obj_at_def valid_arch_state_def)
  done

lemma delete_asid_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   delete_asid asid pd
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding delete_asid_def
  by (wpsimp wp: set_vm_root_globals_equiv set_asid_pool_globals_equiv
                 invalidate_asid_entry_globals_equiv flush_space_globals_equiv)

lemma pagebitsforsize_ge_2[simp]:
  "2 \<le> pageBitsForSize vmpage_size"
  by (induct vmpage_size; simp)

lemma arch_finalise_cap_globals_equiv[Finalise_IF_assms]:
  "\<lbrace>globals_equiv st and invs and valid_arch_cap cap\<rbrace>
   arch_finalise_cap cap b
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (induct cap; simp add: arch_finalise_cap_def)
  by (wp delete_asid_pool_globals_equiv case_option_wp unmap_page_globals_equiv
         unmap_page_table_globals_equiv delete_asid_globals_equiv
      | wpc | clarsimp split: bool.splits option.splits | intro impI conjI)+

lemma mapM_x_swp_store_kernel_base_globals_equiv:
  "\<lbrace>invs and globals_equiv st and cte_wp_at ((=) (ArchObjectCap (PageDirectoryCap word option))) slot\<rbrace>
   mapM_x (swp store_pde InvalidPDE) (map ((\<lambda>x. x + word) \<circ> swp (<<) 2) [0 .e. (kernel_base >> 20) - 1])
   \<lbrace>\<lambda>_ s. globals_equiv st s \<and> invs s\<rbrace>"
  apply (rule hoare_pre)
   apply (wp mapM_x_swp_store_pde_invs_unmap mapM_x_swp_store_pde_globals_equiv)
  apply clarsimp
  apply (frule invs_valid_objs)
  apply (frule invs_valid_global_refs)
  apply (intro impI conjI allI)
  by (simp add: cte_wp_at_page_directory_not_in_globals
                cte_wp_at_page_directory_not_in_kernel_mappings
                not_in_global_not_arm pde_ref_def)+

declare arch_get_sanitise_register_info_def[simp]

crunch prepare_thread_delete
  for globals_equiv[Finalise_IF_assms, wp]: "globals_equiv st"
  (wp: dxo_wp_weak)

lemma set_bound_notification_globals_equiv[Finalise_IF_assms]:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   set_bound_notification ref ts
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_bound_notification_def
  apply (wp set_object_globals_equiv dxo_wp_weak |simp)+
  apply (intro impI conjI allI)
  by (clarsimp simp: valid_arch_state_def obj_at_def tcb_at_def2 get_tcb_def is_tcb_def
               dest: get_tcb_SomeD
              split: option.splits kernel_object.splits)+

end


global_interpretation Finalise_IF_1?: Finalise_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Finalise_IF_assms)?)
qed

end
