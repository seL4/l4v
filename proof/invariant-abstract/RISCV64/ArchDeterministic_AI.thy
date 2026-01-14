(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDeterministic_AI
imports Deterministic_AI
begin

context Arch begin arch_global_naming

named_theorems Deterministic_AI_assms

crunch
  cap_swap_for_delete,set_cap,finalise_cap,
  arch_post_modify_registers, arch_post_set_flags
  for valid_list[wp, Deterministic_AI_assms]: valid_list
  (wp: crunch_wps maybeM_inv simp: unless_def crunch_simps)

declare get_cap_inv[Deterministic_AI_assms]
        arch_get_sanitise_register_info_inv[Deterministic_AI_assms]

end

global_interpretation Deterministic_AI_1?: Deterministic_AI_1
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Deterministic_AI_assms)?)
  qed

context Arch begin arch_global_naming

crunch arch_invoke_irq_handler
  for valid_list[wp,Deterministic_AI_assms]: valid_list

crunch invoke_untyped
  for valid_list[wp]: valid_list
  (wp: crunch_wps preemption_point_inv' unless_wp mapME_x_wp'
   simp: mapM_x_def_bak crunch_simps)

crunch invoke_irq_control
  for valid_list[wp]: valid_list

lemma perform_page_table_invocation_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> perform_page_table_invocation a \<lbrace>\<lambda>_.valid_list\<rbrace>"
  unfolding perform_page_table_invocation_def
  by (wpsimp wp: mapM_x_wp' simp: perform_pt_inv_map_def perform_pt_inv_unmap_def)

lemma perform_page_invocation_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> perform_page_invocation a \<lbrace>\<lambda>_.valid_list\<rbrace>"
  apply (simp add: perform_page_invocation_def)
  apply (cases a, simp_all add: perform_pg_inv_map_def perform_pg_inv_unmap_def
                                perform_pg_inv_get_addr_def split_def)
    apply (wp mapM_x_wp' mapM_wp' crunch_wps | intro impI conjI allI | wpc
           | simp add: set_message_info_def set_mrs_def split: cap.splits arch_cap.splits)+
  done

crunch update_waiting_ntfn, invoke_domain
 for valid_list[wp]: valid_list
  (wp: crunch_wps)
crunch do_reply_transfer
 for valid_list[wp]: valid_list
 (simp: is_round_robin_def
  wp: maybeM_inv get_refills_wp hoare_vcg_if_lift2 get_sched_context_wp hoare_drop_imps)

lemma send_signal_valid_list[wp]: "\<lbrace>valid_list\<rbrace> send_signal param_a param_b \<lbrace>\<lambda>_. valid_list\<rbrace>"
  by (wpsimp simp: send_signal_def wp: get_simple_ko_wp)

crunch arch_perform_invocation, perform_invocation
 for valid_list[wp]: valid_list
  (wp: crunch_wps)

crunch handle_invocation
  for valid_list[wp, Deterministic_AI_assms]: valid_list
  (wp: crunch_wps syscall_valid simp: crunch_simps
   ignore: without_preemption syscall)

crunch receive_ipc
 for valid_list[wp]: valid_list
  (wp: hoare_drop_imps hoare_vcg_if_lift2)

crunch handle_recv
 for valid_list[wp, Deterministic_AI_assms]: valid_list
  (wp: hoare_drop_imps hoare_vcg_if_lift2 simp: Let_def whenE_def)

crunch handle_yield, handle_call
 for valid_list[wp, Deterministic_AI_assms]: valid_list
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps)

lemma handle_vm_fault_valid_list[wp, Deterministic_AI_assms]:
  "handle_vm_fault thread fault \<lbrace>valid_list\<rbrace>"
  unfolding handle_vm_fault_def by (cases fault; wpsimp)

lemma handle_interrupt_valid_list[wp, Deterministic_AI_assms]:
  "\<lbrace>valid_list\<rbrace> handle_interrupt irq \<lbrace>\<lambda>_.valid_list\<rbrace>"
  unfolding handle_interrupt_def ackInterrupt_def
  apply (rule hoare_pre)
   by (wp get_cap_wp  do_machine_op_valid_list
       | wpc | simp add: get_irq_slot_def handle_reserved_irq_def arch_mask_irq_signal_def
       | wp (once) hoare_drop_imps)+

crunch handle_send, handle_spurious_irq, handle_hypervisor_fault
  for valid_list[wp, Deterministic_AI_assms]: valid_list

named_theorems machine_ops_last_machine_time'
named_theorems arch_machine_ops_last_machine_time'

lemmas [machine_ops_last_machine_time'] = storeWord_machine_times ackInterrupt_machine_times

crunch storeWord, clearMemory, freeMemory, ackDeadlineIRQ, ackInterrupt, maskInterrupt, setDeadline
  for machine_times[wp, machine_ops_last_machine_time']: "\<lambda>ms. P (last_machine_time ms) (time_state ms)"
  (wp: crunch_wps simp: crunch_simps ignore_del: storeWord maskInterrupt clearMemory)

lemmas machine_ops_last_machine_time = machine_ops_last_machine_time'
lemmas arch_machine_ops_last_machine_time = arch_machine_ops_last_machine_time'

end

global_interpretation Deterministic_AI_2?: Deterministic_AI_2
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Deterministic_AI_assms)?)
  qed

end
