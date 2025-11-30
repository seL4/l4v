(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchSyscall_IF
imports Syscall_IF
begin

context Arch begin global_naming RISCV64

named_theorems Syscall_IF_assms

lemma globals_equiv_irq_state_update[Syscall_IF_assms, simp]:
  "globals_equiv st (s\<lparr>machine_state :=
                       machine_state s \<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>) =
   globals_equiv st s"
  by (auto simp: globals_equiv_def idle_equiv_def)

lemma thread_set_globals_equiv'[Syscall_IF_assms]:
  "\<lbrace>globals_equiv s and valid_arch_state and (\<lambda>s. tptr \<noteq> idle_thread s)\<rbrace>
   thread_set f tptr
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding thread_set_def
  apply (wp set_object_globals_equiv)
  apply simp
  apply (fastforce simp: obj_at_def get_tcb_def valid_arch_state_def
                   dest: valid_global_arch_objs_pt_at)
  done

lemma sts_authorised_for_globals_inv[Syscall_IF_assms]:
  "set_thread_state d f \<lbrace>authorised_for_globals_inv oper\<rbrace>"
  unfolding authorised_for_globals_inv_def authorised_for_globals_arch_inv_def
            authorised_for_globals_page_table_inv_def authorised_for_globals_page_inv_def
  apply (case_tac oper)
           apply (wp | simp)+
  apply (rename_tac arch_invocation)
  apply (case_tac arch_invocation)
     apply simp
     apply (rename_tac page_table_invocation)
     apply (case_tac page_table_invocation)
      apply wpsimp+
    apply (rename_tac page_invocation)
    apply (case_tac page_invocation)
      apply (simp | wp hoare_vcg_ex_lift)+
  done

lemma dmo_maskInterrupt_globals_equiv[Syscall_IF_assms, wp]:
  "do_machine_op (maskInterrupt b irq) \<lbrace>globals_equiv s\<rbrace>"
  unfolding maskInterrupt_def
  apply (rule dmo_no_mem_globals_equiv)
    apply (wp modify_wp | simp)+
  done

lemma dmo_ackInterrupt_globals_equiv[Syscall_IF_assms, wp]:
  "do_machine_op (ackInterrupt irq) \<lbrace>globals_equiv s\<rbrace>"
  unfolding ackInterrupt_def by wpsimp

lemma dmo_resetTimer_globals_equiv[Syscall_IF_assms, wp]:
  "do_machine_op resetTimer \<lbrace>globals_equiv s\<rbrace>"
  unfolding resetTimer_def by (rule dmo_mol_globals_equiv)

lemma arch_mask_irq_signal_globals_equiv[Syscall_IF_assms, wp]:
  "arch_mask_irq_signal irq \<lbrace>globals_equiv st\<rbrace>"
  by wpsimp

lemma handle_reserved_irq_globals_equiv[Syscall_IF_assms, wp]:
  "handle_reserved_irq irq \<lbrace>globals_equiv st\<rbrace>"
  unfolding handle_reserved_irq_def by wpsimp

lemma handle_vm_fault_reads_respects[Syscall_IF_assms]:
  "reads_respects aag l (K (is_subject aag thread)) (handle_vm_fault thread vmfault_type)"
  unfolding handle_vm_fault_def
  by (cases vmfault_type; wpsimp wp: dmo_read_stval_reads_respects)

lemma handle_hypervisor_fault_reads_respects[Syscall_IF_assms]:
  "reads_respects aag l \<top> (handle_hypervisor_fault thread hypfault_type)"
  by (cases hypfault_type; wpsimp)

lemma handle_vm_fault_globals_equiv[Syscall_IF_assms]:
  "\<lbrace>globals_equiv st and valid_arch_state and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace>
   handle_vm_fault thread vmfault_type
   \<lbrace>\<lambda>r. globals_equiv st\<rbrace>"
  unfolding handle_vm_fault_def
  by (cases vmfault_type; wpsimp wp: dmo_no_mem_globals_equiv)

lemma handle_hypervisor_fault_globals_equiv[Syscall_IF_assms]:
  "handle_hypervisor_fault thread hypfault_type \<lbrace>globals_equiv st\<rbrace>"
  by (cases hypfault_type; wpsimp)

crunch arch_activate_idle_thread
  for globals_equiv[Syscall_IF_assms, wp]: "globals_equiv st"

lemma select_f_setNextPC_reads_respects[Syscall_IF_assms, wp]:
  "reads_respects aag l \<top> (select_f (setNextPC a b))"
  unfolding setNextPC_def setRegister_def
  by (wpsimp simp: select_f_returns)

lemma select_f_getRestartPC_reads_respects[Syscall_IF_assms, wp]:
  "reads_respects aag l \<top> (select_f (getRestartPC a))"
  unfolding getRestartPC_def getRegister_def
  by (wpsimp simp: select_f_returns)

lemma arch_activate_idle_thread_reads_respects[Syscall_IF_assms, wp]:
  "reads_respects aag l \<top> (arch_activate_idle_thread t)"
  unfolding arch_activate_idle_thread_def by wpsimp

lemma decode_asid_pool_invocation_authorised_for_globals:
  "\<lbrace>invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)\<rbrace>
   decode_asid_pool_invocation label msg slot cap excaps
   \<lbrace>authorised_for_globals_arch_inv\<rbrace>, -"
  unfolding authorised_for_globals_arch_inv_def decode_asid_pool_invocation_def
  apply (simp add: split_def Let_def cong: if_cong split del: if_split)
  apply wpsimp
  done

lemma decode_asid_control_invocation_authorised_for_globals:
  "\<lbrace>invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)\<rbrace>
   decode_asid_control_invocation label msg slot cap excaps
   \<lbrace>authorised_for_globals_arch_inv\<rbrace>, -"
  unfolding authorised_for_globals_arch_inv_def decode_asid_control_invocation_def
  apply (simp add: split_def Let_def cong: if_cong split del: if_split)
  apply wpsimp
  done

lemma decode_frame_invocation_authorised_for_globals:
  "\<lbrace>invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)\<rbrace>
   decode_frame_invocation label msg slot cap excaps
   \<lbrace>authorised_for_globals_arch_inv\<rbrace>, -"
  unfolding authorised_for_globals_arch_inv_def authorised_for_globals_page_inv_def
             decode_frame_invocation_def decode_fr_inv_map_def
  apply (simp add: split_def Let_def cong: arch_cap.case_cong if_cong split del: if_split)
  apply (wpsimp wp: check_vp_wpR)
  apply (subgoal_tac
          "(\<exists>a b. cte_wp_at (parent_for_refs (make_user_pte (addrFromPPtr x)
                                                            (attribs_from_word (msg ! 2))
                                                            (mask_vm_rights xa
                                                               (data_to_rights (msg ! Suc 0))),
                                              ba)) (a, b) s)", clarsimp)
  apply (clarsimp simp: parent_for_refs_def cte_wp_at_caps_of_state)
  apply (frule vspace_for_asid_vs_lookup)
  apply (frule_tac vptr="msg ! 0" in pt_lookup_slot_cap_to)
      apply fastforce
     apply (fastforce elim: vs_lookup_table_is_aligned)
    apply (drule not_le_imp_less)
    apply (frule order.strict_implies_order[where b=user_vtop])
    apply (drule order.strict_trans[OF _ user_vtop_pptr_base])
    apply (drule canonical_below_pptr_base_user)
     apply (erule below_user_vtop_canonical)
    apply (clarsimp simp: vmsz_aligned_def)
    apply (drule is_aligned_no_overflow_mask)
    apply (clarsimp simp: user_region_def)
    apply (erule (1) dual_order.trans)
   apply assumption
  apply (fastforce simp: is_pt_cap_def is_PageTableCap_def split: option.splits)
  done

lemma decode_page_table_invocation_authorised_for_globals:
  "\<lbrace>invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)\<rbrace>
   decode_page_table_invocation label msg slot cap excaps
   \<lbrace>authorised_for_globals_arch_inv\<rbrace>, -"
  unfolding authorised_for_globals_arch_inv_def authorised_for_globals_page_table_inv_def
            decode_page_table_invocation_def decode_pt_inv_map_def
  apply (simp add: split_def Let_def cong: arch_cap.case_cong if_cong split del: if_split)
  apply (wpsimp cong: if_cong wp: hoare_vcg_if_lift2)
  apply (clarsimp simp: pt_lookup_slot_from_level_def pt_lookup_slot_def)
  apply (frule (1) pt_lookup_vs_lookupI, clarsimp)
  apply (drule vs_lookup_level)
  apply (frule pt_walk_max_level)
  apply (subgoal_tac "msg ! 0 \<in> user_region")
   apply (frule reachable_page_table_not_global; clarsimp?)
   apply (frule vs_lookup_table_is_aligned; clarsimp?)
   apply (fastforce dest: riscv_global_pt_in_global_refs invs_arch_state simp: valid_arch_state_def)
  apply (drule not_le_imp_less)
  apply (frule order.strict_implies_order[where b=user_vtop])
  apply (drule order.strict_trans[OF _ user_vtop_pptr_base])
  apply (drule canonical_below_pptr_base_user)
   apply (erule below_user_vtop_canonical)
  apply clarsimp
  done

lemma decode_arch_invocation_authorised_for_globals[Syscall_IF_assms]:
  "\<lbrace>invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)\<rbrace>
   arch_decode_invocation label msg x_slot slot cap excaps
   \<lbrace>authorised_for_globals_arch_inv\<rbrace>, -"
  unfolding arch_decode_invocation_def
  by (wpsimp wp: decode_asid_pool_invocation_authorised_for_globals
                 decode_asid_control_invocation_authorised_for_globals
                 decode_frame_invocation_authorised_for_globals
                 decode_page_table_invocation_authorised_for_globals, fastforce)

declare arch_prepare_set_domain_inv[Syscall_IF_assms]

end


global_interpretation Syscall_IF_1?: Syscall_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Syscall_IF_assms)?)
qed

end
