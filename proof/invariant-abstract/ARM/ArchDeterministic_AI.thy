(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDeterministic_AI
imports Deterministic_AI
begin

context Arch begin arch_global_naming

named_theorems Deterministic_AI_assms

crunch
  cap_swap_for_delete,set_cap,finalise_cap,arch_get_sanitise_register_info,
  arch_post_modify_registers, arch_post_set_flags
  for valid_list[wp, Deterministic_AI_assms]: valid_list
  (wp: crunch_wps simp: unless_def crunch_simps)
declare get_cap_inv[Deterministic_AI_assms]

end

global_interpretation Deterministic_AI_1?: Deterministic_AI_1
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Deterministic_AI_assms)?)
  qed

context Arch begin arch_global_naming

crunch arch_invoke_irq_handler
  for valid_list[wp, Deterministic_AI_assms]: valid_list

crunch invalidate_tlb_by_asid
  for valid_list[wp]: valid_list
  (wp: crunch_wps preemption_point_inv' simp: crunch_simps filterM_mapM)

crunch invoke_untyped
  for valid_list[wp]: valid_list
  (wp: crunch_wps preemption_point_inv' unless_wp mapME_x_wp'
   simp: mapM_x_def_bak crunch_simps)

crunch invoke_irq_control
  for valid_list[wp]: valid_list

lemma perform_page_table_invocation_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> perform_page_table_invocation a \<lbrace>\<lambda>_.valid_list\<rbrace>"
  apply (simp add: perform_page_table_invocation_def)
  apply (cases a,simp_all)
  apply (wp mapM_x_wp' | intro impI conjI allI | wpc | simp split: cap.splits arch_cap.splits option.splits)+
  done

lemma perform_page_invocation_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> perform_page_invocation a \<lbrace>\<lambda>_.valid_list\<rbrace>"
  apply (simp add: perform_page_invocation_def)
  apply (cases a,simp_all)
  apply (wp mapM_x_wp' mapM_wp' crunch_wps | intro impI conjI allI | wpc | simp add: set_message_info_def set_mrs_def split: cap.splits arch_cap.splits option.splits sum.splits)+
  done

crunch perform_invocation
  for valid_list[wp]: valid_list
  (wp: crunch_wps simp: crunch_simps ignore: without_preemption)

crunch handle_invocation
  for valid_list[wp, Deterministic_AI_assms]: valid_list
  (wp: crunch_wps syscall_valid simp: crunch_simps
   ignore: without_preemption syscall)

crunch handle_recv, handle_yield, handle_call
  for valid_list[wp, Deterministic_AI_assms]: valid_list
  (wp: crunch_wps simp: crunch_simps)

lemma handle_vm_fault_valid_list[wp, Deterministic_AI_assms]:
"\<lbrace>valid_list\<rbrace> handle_vm_fault thread fault \<lbrace>\<lambda>_.valid_list\<rbrace>"
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

crunch handle_hypervisor_fault
  for valid_list[wp, Deterministic_AI_assms]: valid_list

end
global_interpretation Deterministic_AI_2?: Deterministic_AI_2
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Deterministic_AI_assms)?)
  qed

end

