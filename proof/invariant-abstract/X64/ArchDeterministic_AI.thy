(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDeterministic_AI
imports Deterministic_AI
begin

context Arch begin global_naming X64

named_theorems Deterministic_AI_assms

lemma flush_table_valid_list[wp]: "\<lbrace>valid_list\<rbrace> flush_table a b c d \<lbrace>\<lambda>rv. valid_list\<rbrace>"
  by (wp mapM_x_wp' | wpc | simp add: flush_table_def | rule hoare_pre)+

crunch set_object
  for valid_list[wp]: valid_list
  (wp: get_object_wp)

crunch
  cap_swap_for_delete,set_cap,finalise_cap,arch_get_sanitise_register_info,
  arch_post_modify_registers, arch_invoke_irq_handler
  for valid_list[wp, Deterministic_AI_assms]: valid_list
  (wp: crunch_wps simp: unless_def crunch_simps)
declare get_cap_inv[Deterministic_AI_assms]

end

global_interpretation Deterministic_AI_1?: Deterministic_AI_1
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Deterministic_AI_assms)?)
  qed

context Arch begin global_naming X64

crunch invoke_untyped
  for valid_list[wp]: valid_list
  (wp: crunch_wps preemption_point_inv' unless_wp mapME_x_wp'
   simp: mapM_x_def_bak crunch_simps)

crunch invoke_irq_control, store_pde, store_pte, store_pdpte, store_pml4e,
                       perform_io_port_invocation, perform_ioport_control_invocation
  for valid_list[wp]: valid_list
  (wp: crunch_wps simp: crunch_simps)

lemma perform_pdpt_invocation_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> perform_pdpt_invocation a \<lbrace>\<lambda>_.valid_list\<rbrace>"
  apply (simp add: perform_pdpt_invocation_def)
  apply (cases a,simp_all)
  apply (wp mapM_x_wp' hoare_vcg_all_lift
          | intro impI conjI allI
          | wpc
          | simp split: cap.splits arch_cap.splits option.splits
          | wp (once) hoare_drop_imps)+
  done

lemma perform_page_directory_invocation_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> perform_page_directory_invocation a \<lbrace>\<lambda>_.valid_list\<rbrace>"
  apply (simp add: perform_page_directory_invocation_def)
  apply (cases a,simp_all)
  apply (wp mapM_x_wp' hoare_vcg_all_lift
          | intro impI conjI allI
          | wpc
          | simp split: cap.splits arch_cap.splits option.splits
          | wp (once) hoare_drop_imps)+
  done

lemma perform_page_table_invocation_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> perform_page_table_invocation a \<lbrace>\<lambda>_.valid_list\<rbrace>"
  apply (simp add: perform_page_table_invocation_def)
  apply (cases a,simp_all)
  apply (wp mapM_x_wp' hoare_vcg_all_lift
          | intro impI conjI allI
          | wpc
          | simp split: cap.splits arch_cap.splits option.splits
          | wp (once) hoare_drop_imps)+
  done

lemma perform_page_invocation_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> perform_page_invocation a \<lbrace>\<lambda>_.valid_list\<rbrace>"
  apply (simp add: perform_page_invocation_def)
  apply (cases a,simp_all)
  apply (wp mapM_x_wp' mapM_wp' crunch_wps hoare_vcg_all_lift
          | intro impI conjI allI
          | wpc
          | simp add: set_message_info_def set_mrs_def perform_page_invocation_unmap_def
               split: cap.splits arch_cap.splits option.splits sum.splits)+
  done

crunch perform_invocation
  for valid_list[wp]: valid_list
  (wp: crunch_wps simp: crunch_simps ignore: without_preemption)

crunch handle_invocation
  for valid_list[wp, Deterministic_AI_assms]: valid_list
  (wp: crunch_wps syscall_valid simp: crunch_simps
   ignore: without_preemption syscall)

crunch handle_recv, handle_yield, handle_call,
                                               handle_hypervisor_fault
  for valid_list[wp, Deterministic_AI_assms]: valid_list
  (wp: crunch_wps simp: crunch_simps)

lemma handle_vm_fault_valid_list[wp, Deterministic_AI_assms]:
"\<lbrace>valid_list\<rbrace> handle_vm_fault thread fault \<lbrace>\<lambda>_.valid_list\<rbrace>"
  unfolding handle_vm_fault_def
  apply (cases fault,simp_all)
  apply (wp|simp)+
  done

lemma handle_interrupt_valid_list[wp, Deterministic_AI_assms]:
  "\<lbrace>valid_list\<rbrace> handle_interrupt irq \<lbrace>\<lambda>_.valid_list\<rbrace>"
  unfolding handle_interrupt_def ackInterrupt_def
  apply (rule hoare_pre)
   by (wp get_cap_wp  do_machine_op_valid_list
       | wpc | simp add: get_irq_slot_def handle_reserved_irq_def arch_mask_irq_signal_def
       | wp (once) hoare_drop_imps)+

crunch handle_send,handle_reply
  for valid_list[wp, Deterministic_AI_assms]: valid_list

end
global_interpretation Deterministic_AI_2?: Deterministic_AI_2
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Deterministic_AI_assms)?)
  qed

end

