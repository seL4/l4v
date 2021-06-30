(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory DetSchedDomainTime_AI
imports "$L4V_ARCH/ArchDetSchedAux_AI"
begin

text \<open>
  This theory deals with the preservation of domain_list validity over kernel invocations,
  as well as ensuring preserving that the domain time is never zero at kernel exit.
\<close>

(* Note: domains in the domain list should also be \<le> maxDomain, but this is not needed right now *)
definition
  "valid_domain_list_2 dlist \<equiv> 0 < length dlist \<and> (\<forall>(d,time) \<in> set dlist. 0 < time)"

abbreviation
  valid_domain_list :: "'z state \<Rightarrow> bool"
where
  "valid_domain_list \<equiv> \<lambda>s. valid_domain_list_2 (domain_list s)"

lemmas valid_domain_list_def = valid_domain_list_2_def


section \<open>Preservation of domain list validity\<close>

crunch domain_list_inv[wp]:
  empty_slot_ext, cap_swap_ext "\<lambda>s. P (domain_list s)"

crunch domain_list_inv[wp]:
  schedule_tcb, set_thread_state "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps)

(*
  FIXME: cleanup
  Many of these could be factored out into the general state_ext class instead, but they will be
  applied to det_ext lemmas that contain e.g. preemption_point which needs the det_ext work_units,
  i.e. those will need additional locales, because 'state_ext needs to be interpreted first
  into ?'state_ext.
*)
locale DetSchedDomainTime_AI =
  assumes finalise_cap_domain_list_inv'[wp]:
    "\<And>P cap fin. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_finalise_cap cap fin \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_activate_idle_thread_domain_list_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_activate_idle_thread t \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_switch_to_thread_domain_list_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_get_sanitise_register_info_domain_list_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_get_sanitise_register_info t \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_switch_to_idle_thread_domain_list_inv'[wp]:
    "\<And>P. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes handle_arch_fault_reply_domain_list_inv'[wp]:
    "\<And>P f t x y. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes init_arch_objects_domain_list_inv'[wp]:
    "\<And>P t p n s r. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> init_arch_objects t p n s r \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_post_modify_registers_domain_list_inv'[wp]:
    "\<And>P t p. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_post_modify_registers t p \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_invoke_irq_control_domain_list_inv'[wp]:
    "\<And>P i. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_invoke_irq_control i \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes handle_vm_fault_domain_list_inv'[wp]:
    "\<And>P t f. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes prepare_thread_delete_domain_list_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes finalise_cap_domain_time_inv'[wp]:
    "\<And>P cap fin. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_finalise_cap cap fin \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_activate_idle_thread_domain_time_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_activate_idle_thread t \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_switch_to_thread_domain_time_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_switch_to_thread_domain_consumed_time_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_time s)(consumed_time s)\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_ s. P (domain_time s)(consumed_time s)\<rbrace>"
  assumes arch_get_sanitise_register_info_domain_time_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_get_sanitise_register_info t \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_switch_to_idle_thread_domain_time_inv'[wp]:
    "\<And>P. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_switch_to_idle_thread_domain_consumed_time_inv'[wp]:
    "\<And>P. \<lbrace>\<lambda>s::det_state. P (domain_time s)(consumed_time s)\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_ s. P (domain_time s)(consumed_time s)\<rbrace>"
  assumes handle_arch_fault_reply_domain_time_inv'[wp]:
    "\<And>P f t x y. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes init_arch_objects_domain_time_inv'[wp]:
    "\<And>P t p n s r. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> init_arch_objects t p n s r \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_post_modify_registers_domain_time_inv'[wp]:
    "\<And>P t p. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_post_modify_registers t p \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_invoke_irq_control_domain_time_inv'[wp]:
    "\<And>P i. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_invoke_irq_control i \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes handle_vm_fault_domain_time_inv'[wp]:
    "\<And>P t f. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes prepare_thread_delete_domain_time_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes make_arch_fault_msg_domain_time_inv'[wp]:
    "\<And>P ft t. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> make_arch_fault_msg ft t \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes make_arch_fault_msg_domain_list_inv'[wp]:
    "\<And>P ft t. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> make_arch_fault_msg ft t \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes make_arch_fault_msg_domain_consumed_time_inv'[wp]:
    "\<And>P ft t. \<lbrace>\<lambda>s::det_state. P (domain_time s)(consumed_time s)\<rbrace>
         make_arch_fault_msg ft t \<lbrace>\<lambda>_ s. P (domain_time s)(consumed_time s)\<rbrace>"
  assumes make_arch_fault_msg_domain_consumed_inv'[wp]:
    "\<And>P ft t. \<lbrace>\<lambda>s::det_state. P (domain_time s)(consumed_time s)\<rbrace>
             make_arch_fault_msg ft t \<lbrace>\<lambda>_ s. P (domain_time s)(consumed_time s)\<rbrace>"
  assumes arch_post_cap_deletion_domain_time_inv'[wp]:
    "\<And>P ft. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_post_cap_deletion ft \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_post_cap_deletion_domain_list_inv'[wp]:
    "\<And>P ft. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_post_cap_deletion ft \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_invoke_irq_handler_domain_list_inv'[wp]:
    "\<And>P i. arch_invoke_irq_handler i \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace>"
  assumes arch_invoke_irq_handler_domain_time_inv'[wp]:
    "\<And>P i. arch_invoke_irq_handler i \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace>"

crunches update_restart_pc
  for domain_list[wp]: "\<lambda>s. P (domain_list s)"
  and domain_time[wp]: "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps)

locale DetSchedDomainTime_AI_2 = DetSchedDomainTime_AI +
  assumes handle_hypervisor_fault_domain_list_inv'[wp]:
    "\<And>P t f. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> handle_hypervisor_fault t f \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes handle_hypervisor_fault_domain_time_inv'[wp]:
    "\<And>P t f. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> handle_hypervisor_fault t f \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_perform_invocation_domain_list_inv'[wp]:
    "\<And>P i. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_perform_invocation i \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_perform_invocation_domain_time_inv'[wp]:
    "\<And>P i. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_perform_invocation i \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes handle_interrupt_valid_domain_time:
    "\<And>i.
      \<lbrace>\<lambda>s :: det_state. 0 < domain_time s \<rbrace>
        handle_interrupt i
      \<lbrace>\<lambda>rv s.  domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread \<rbrace>"
  assumes handle_reserved_irq_some_time_inv'[wp]:
    "\<And>P irq. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> handle_reserved_irq irq \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes handle_reserved_irq_domain_list_inv'[wp]:
    "\<And>P irq. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> handle_reserved_irq irq \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_mask_irq_signal_domain_list_inv'[wp]:
    "\<And>P irq. arch_mask_irq_signal irq \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace>"
  assumes arch_mask_irq_signal_domain_time_inv'[wp]:
    "\<And>P irq. arch_mask_irq_signal irq \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace>"

crunch (empty_fail) empty_fail[wp]: commit_domain_time

context DetSchedDomainTime_AI begin

crunch domain_list_inv[wp]:
  cap_swap_for_delete, empty_slot, get_object, get_cap, tcb_sched_action
  "\<lambda>s::det_state. P (domain_list s)"
  (wp: dxo_wp_weak)

crunch domain_list_inv[wp]: reschedule_required,schedule_tcb "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps simp: crunch_simps)

crunch domain_list_inv[wp]: reply_unlink_tcb, reply_unlink_sc, tcb_sched_action "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps hoare_unless_wp maybeM_inv select_inv gets_the_inv simp: crunch_simps set_object_def)

crunch domain_list_inv[wp]: reply_remove, sched_context_unbind_tcb, sched_context_zero_refill_max "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps get_simple_ko_wp)

crunch domain_list_inv[wp]: cancel_all_ipc, cancel_all_signals "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps mapM_x_wp')

crunch domain_list_inv[wp]: finalise_cap "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps hoare_unless_wp maybeM_inv dxo_wp_weak select_inv simp: crunch_simps)

lemma rec_del_domain_list[wp]:
  "\<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> rec_del call \<lbrace>\<lambda>rv s. P (domain_list s)\<rbrace>"
  by (wp rec_del_preservation preemption_point_inv' | simp)+

crunch domain_list_inv[wp]: cap_delete, activate_thread "\<lambda>s::det_state. P (domain_list s)"
  (wp: hoare_drop_imp)

crunch domain_list_inv[wp]: possible_switch_to "\<lambda>s. P (domain_list s)"
  (simp: get_tcb_obj_ref_def wp: hoare_vcg_if_lift2 hoare_drop_imp)

crunches awaken
  for domain_list_inv[wp]: "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps)

crunch domain_list_inv[wp]: commit_time "\<lambda>s. P (domain_list s)"
  (simp: Let_def
   wp: get_sched_context_wp get_refills_wp crunch_wps hoare_vcg_all_lift hoare_vcg_if_lift2)

crunch domain_list_inv[wp]: refill_new "\<lambda>s. P (domain_list s)"
  (simp: Let_def crunch_simps wp: get_sched_context_wp get_refills_wp wp: crunch_wps)

crunch domain_list_inv[wp]: refill_update "\<lambda>s. P (domain_list s)"
  (simp: Let_def crunch_simps
     wp: get_refills_wp update_sched_context_wp set_refills_wp crunch_wps)

crunch domain_list_inv[wp]: set_next_interrupt, switch_sched_context
  "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps)

lemma sc_and_timer_domain_list[wp]:
  "sc_and_timer \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace>"
  by (wpsimp simp: sc_and_timer_def Let_def wp: get_sched_context_wp)

crunch domain_list_inv[wp]: sc_and_timer "\<lambda>s::det_state. P (domain_list s)"
    (simp: Let_def wp: get_sched_context_wp ignore: do_machine_op set_next_interrupt)

crunch domain_list_inv[wp]: schedule "\<lambda>s::det_state. P (domain_list s)"
  (wp: hoare_drop_imp dxo_wp_weak simp: Let_def)

crunch domain_list_inv[wp]: send_signal "\<lambda>s::det_state. P (domain_list s)"
  (wp: maybeM_inv crunch_wps)

end

lemma (in DetSchedDomainTime_AI_2) handle_interrupt_domain_list[wp]:
  "\<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> handle_interrupt irq \<lbrace>\<lambda>rv s. P (domain_list s)\<rbrace>"
  by (wpsimp simp: handle_interrupt_def wp: hoare_vcg_if_lift2 hoare_drop_imp split_del: if_split)

crunch domain_list_inv[wp]: cap_insert "\<lambda>s::det_state. P (domain_list s)"
  (wp: hoare_drop_imps)

crunch domain_list_inv[wp]:
  lookup_cap_and_slot,set_extra_badge "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps)

crunch domain_list_inv[wp]: postpone "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps mapM_wp)

context DetSchedDomainTime_AI begin
crunch domain_list_inv[wp]: do_ipc_transfer "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps transfer_caps_loop_pres simp: zipWithM_x_mapM ignore: transfer_caps_loop)

lemma reply_push_domain_list_inv[wp]:
  "\<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> reply_push param_a param_b param_c param_d \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  by (wpsimp simp: reply_push_def bind_sc_reply_def split_del: if_split
    wp: hoare_vcg_if_lift2 hoare_vcg_all_lift hoare_drop_imp get_sched_context_wp)

lemma send_ipc_domain_list_inv[wp]:
  "\<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace>
   send_ipc block call badge can_grant can_reply_grant can_donate thread epptr
   \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  by (wpsimp simp: send_ipc_def wp: hoare_drop_imp hoare_vcg_all_lift)

lemma send_fault_ipc_domain_list_inv[wp]:
 "\<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> send_fault_ipc param_a param_b param_c param_d \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  by (wpsimp simp: send_fault_ipc_def wp: hoare_drop_imp hoare_vcg_all_lift)

crunch domain_list_inv[wp]: handle_fault "\<lambda>s::det_state. P (domain_list s)"
  (wp: mapM_wp hoare_drop_imps hoare_unless_wp maybeM_inv dxo_wp_weak simp: crunch_simps ignore:copy_mrs)

crunch domain_list_inv[wp]: create_cap_ext "\<lambda>s. P (domain_list s)"
  (wp: maybeM_inv mapM_wp dxo_wp_weak)

crunch domain_list_inv[wp]:
  reply_from_kernel, create_cap
  "\<lambda>s::det_state. P (domain_list s)"
  (wp: hoare_drop_imps maybeM_inv dxo_wp_weak mapM_wp)

crunch domain_list_inv[wp]:
  retype_region, do_reply_transfer
  "\<lambda>s::det_state. P (domain_list s)"
  (wp: hoare_drop_imps maybeM_inv dxo_wp_weak mapM_wp)
end

crunches delete_objects, preemption_point, reset_untyped_cap
  for domain_list_inv[wp]: "\<lambda>s :: det_state. P (domain_list s)"
  (wp: crunch_wps mapME_x_inv_wp OR_choiceE_weak_wp simp: detype_def ignore_del: preemption_point)

crunches
  set_priority, restart, sched_context_bind_tcb,sched_context_bind_ntfn,
  sched_context_unbind_reply, sched_context_yield_to
  for domain_list_inv[wp]: "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps mapM_wp' maybeM_inv whileLoop_wp' simp: crunch_simps)

context DetSchedDomainTime_AI begin

crunch domain_list_inv[wp]:
  refill_budget_check,charge_budget, check_budget
  "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps check_cap_inv maybeM_inv simp: Let_def)

crunch domain_list_inv[wp]: invoke_untyped "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps
    simp: crunch_simps mapM_x_defsym)

crunch domain_list_inv[wp]: invoke_tcb "\<lambda>s::det_state. P (domain_list s)"
 (wp: hoare_drop_imp check_cap_inv mapM_x_wp')

lemma invoke_sched_control_configure_flags_domain_list[wp]:
 "\<lbrace>(\<lambda>s :: det_state. P (domain_list s))\<rbrace> invoke_sched_control_configure_flags iv \<lbrace>\<lambda>rv s. P (domain_list s)\<rbrace>"
  by (wpsimp wp: hoare_drop_imps simp: invoke_sched_control_configure_flags_def)

lemma invoke_sched_context_domain_list_inv[wp]:
  "\<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> invoke_sched_context i \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  by (wpsimp simp: invoke_sched_context_def)

crunch domain_list_inv[wp]:
  invoke_domain, invoke_irq_control, invoke_irq_handler
  "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps check_cap_inv maybeM_inv)

end

context DetSchedDomainTime_AI_2
begin

crunch domain_list_inv[wp]: arch_perform_invocation "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps check_cap_inv)

crunch domain_list_inv[wp]: handle_interrupt "\<lambda>s::det_state. P (domain_list s)"

end

crunch domain_list_inv[wp]: cap_move_ext "\<lambda>s. P (domain_list s)"

crunch domain_list_inv[wp]: cap_move "\<lambda>s::det_state. P (domain_list s)"

context DetSchedDomainTime_AI begin
lemma cap_revoke_domain_list_inv[wp]:
  "\<lbrace>(\<lambda>s :: det_state. P (domain_list s))\<rbrace> cap_revoke a \<lbrace>\<lambda>rv s. P (domain_list s)\<rbrace>"
  by (rule cap_revoke_preservation2)
     (wp preemption_point_inv'|simp)+
end

crunch domain_list_inv[wp]: cancel_badged_sends "\<lambda>s. P (domain_list s)"
  (ignore: filterM clearMemory
     simp: filterM_mapM crunch_simps
       wp: crunch_wps)

crunch domain_list[wp]: maybe_donate_sc "\<lambda>s :: det_state. P (domain_list s)"
  (wp: crunch_wps)

crunch domain_list_inv[wp]: send_signal "\<lambda>s::det_state. P (domain_list s)"
  (wp: hoare_drop_imps mapM_x_wp_inv select_wp maybeM_inv simp: crunch_simps unless_def)

crunch domain_list_inv[wp]: lookup_reply,lookup_cap "\<lambda>s::det_state. P (domain_list s)"

context DetSchedDomainTime_AI_2 begin

lemma invoke_cnode_domain_list_inv[wp]:
  "\<lbrace>\<lambda>s :: det_state. P (domain_list s)\<rbrace>
     invoke_cnode i
   \<lbrace>\<lambda>rv s. P (domain_list s) \<rbrace>"
  apply (rule hoare_pre)
   apply (wp crunch_wps cap_move_src_slot_Null hoare_drop_imps hoare_vcg_all_lift
          | wpc | simp add: invoke_cnode_def crunch_simps split del: if_split)+
  done

lemma perform_invocation_domain_list_inv[wp]:
  "\<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace>
  perform_invocation block call can_donate i \<lbrace>\<lambda>rv s. P (domain_list s)\<rbrace>"
  by (cases i; wpsimp)

(*
crunch domain_list_inv[wp]: perform_invocation "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps syscall_valid maybeM_inv simp: crunch_simps ignore: without_preemption)
*)
crunch domain_list_inv[wp]: handle_invocation,receive_ipc,receive_signal "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps syscall_valid maybeM_inv simp: crunch_simps ignore: without_preemption syscall)

lemma handle_recv_domain_list_inv[wp]:
  "\<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace>
  handle_recv is_blocking can_reply \<lbrace>\<lambda>rv s. P (domain_list s)\<rbrace>"
  apply (wpsimp simp: handle_recv_def Let_def whenE_def get_sk_obj_ref_def
                split_del: if_split wp: hoare_drop_imps)
  by (rule_tac Q'="\<lambda>_ s. P (domain_list s)" in hoare_post_imps(1))  wpsimp+

crunches
  handle_yield, handle_call, handle_vm_fault, handle_hypervisor_fault
  for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps simp: crunch_simps)

crunch domain_list_inv[wp]: check_budget_restart "\<lambda>s::det_state. P (domain_list s)"
  (simp: is_round_robin_def wp: hoare_drop_imps)

lemma handle_event_domain_list_inv[wp]:
  "\<lbrace>\<lambda>s::det_state. P (domain_list s) \<rbrace>
   handle_event e
   \<lbrace>\<lambda>_ s. P (domain_list s) \<rbrace>"
  apply (cases e, simp_all)
      apply (rename_tac syscall)
      apply (case_tac syscall, simp_all add: handle_send_def whenE_def)
             apply wpsimp+
  done

(* no one modifies domain_list - supplied at compile time *)
lemma call_kernel_domain_list_inv_det_ext:
  "\<lbrace> \<lambda>s::det_state. P (domain_list s) \<rbrace>
     (call_kernel e) :: (unit,det_ext) s_monad
   \<lbrace>\<lambda>_ s. P (domain_list s) \<rbrace>"
  unfolding call_kernel_def preemption_path_def
  apply (wp)
   apply (simp add: schedule_def)
   apply (wpsimp wp: without_preemption_wp is_schedulable_wp hoare_vcg_all_lift hoare_drop_imps
               simp: if_apply_def2)+
  done

end


section \<open>Preservation of domain time remaining\<close>

crunch domain_time_inv[wp]: do_user_op "\<lambda>s. P (domain_time s)"
  (wp: select_wp)

crunch domain_time_inv[wp]: schedule_tcb,tcb_release_remove "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps)

crunch domain_time_inv[wp]: set_thread_state,store_word_offs "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps)

lemma set_mrs_domain_time_inv[wp]:
  "\<lbrace>\<lambda>s. P (domain_time s)\<rbrace> set_mrs param_a param_b param_c \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  by (wpsimp simp: set_mrs_def zipWithM_x_mapM split_del: if_split wp: mapM_wp')

crunch domain_time_inv[wp]: complete_yield_to "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps maybeM_inv)

context DetSchedDomainTime_AI begin

crunch domain_time_inv[wp]:
  get_cap, activate_thread, set_scheduler_action, tcb_sched_action
  "\<lambda>s::det_state. P (domain_time s)" (wp: hoare_drop_imp)

crunch domain_time_inv[wp]: guarded_switch_to "\<lambda>s::det_state. P (domain_time s)"
  (wp: hoare_drop_imp whenE_inv)

crunch domain_time_inv[wp]: choose_thread "\<lambda>s::det_state. P (domain_time s)"
crunch domain_time_inv[wp]: sched_context_donate "\<lambda>s::det_state. P (domain_time s)"

crunch domain_time_inv[wp]: reply_remove, maybe_donate_sc "\<lambda>s::det_state. P (domain_time s)"
  (wp: hoare_drop_imps crunch_wps simp: crunch_simps)

crunch domain_time_inv[wp]: send_signal "\<lambda>s::det_state. P (domain_time s)"
  (wp: hoare_drop_imps mapM_x_wp_inv maybeM_inv select_wp simp: crunch_simps unless_def)

crunch domain_time_inv[wp]:
  cap_swap_for_delete, empty_slot, get_object, get_cap, tcb_sched_action
  "\<lambda>s::det_state. P (domain_time s)"

crunch domain_time_inv[wp]: sched_context_unbind_tcb "\<lambda>s. P (domain_time s)" (wp: hoare_drop_imp)

crunch domain_time_inv[wp]: finalise_cap "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps hoare_drop_imps hoare_unless_wp select_inv mapM_wp
       subset_refl if_fun_split maybeM_inv simp: crunch_simps ignore: tcb_sched_action)

lemma rec_del_domain_time[wp]:
  "\<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> rec_del call \<lbrace>\<lambda>rv s. P (domain_time s)\<rbrace>"
  by (wp rec_del_preservation preemption_point_inv' | simp)+

crunch domain_time_inv[wp]:
  cap_delete, activate_thread, lookup_cap_and_slot
  "\<lambda>s::det_state. P (domain_time s)"

end

crunch domain_time_inv[wp]: cap_insert "\<lambda>s::det_state. P (domain_time s)"
  (wp: hoare_drop_imps)

crunch domain_time_inv[wp]: set_extra_badge "\<lambda>s. P (domain_time s)"

crunch domain_time_inv[wp]: postpone,reply_push "\<lambda>s::det_state. P (domain_time s)"
  (wp: hoare_drop_imp mapM_wp' hoare_vcg_if_lift)

context DetSchedDomainTime_AI begin

crunch domain_time_inv[wp]: do_ipc_transfer "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps transfer_caps_loop_pres simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch domain_time_inv[wp]: send_ipc "\<lambda>s::det_state. P (domain_time s)"
  (wp: mapM_wp hoare_drop_imps maybeM_inv simp: crunch_simps ignore:copy_mrs sched_context_donate)

crunch domain_time_inv[wp]: send_fault_ipc "\<lambda>s::det_state. P (domain_time s)"

crunch domain_time_inv[wp]: handle_fault "\<lambda>s::det_state. P (domain_time s)"
  (wp: mapM_wp hoare_drop_imps maybeM_inv hoare_unless_wp simp: crunch_simps ignore:copy_mrs)

crunch domain_time_inv[wp]: reply_from_kernel, create_cap, retype_region
  "\<lambda>s::det_state. P (domain_time s)"

crunch domain_time_inv[wp]: do_reply_transfer "\<lambda>s::det_state. P (domain_time s)"
  (wp: hoare_drop_imps maybeM_inv mapM_wp)
end

crunch domain_time_inv[wp]: delete_objects "\<lambda>s :: det_state. P (domain_time s)"
  (wp: crunch_wps
   simp: detype_def wrap_ext_det_ext_ext_def cap_insert_ext_def
   ignore: freeMemory)

crunch domain_time_inv[wp]: preemption_point "\<lambda>s::det_state. P (domain_time s)"
  (wp: select_inv OR_choiceE_weak_wp crunch_wps ignore: OR_choiceE ignore_del: preemption_point)

crunch domain_time_inv[wp]: reset_untyped_cap "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps hoare_unless_wp mapME_x_inv_wp select_inv
   simp: crunch_simps)

crunches sched_context_bind_tcb, restart
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"
  (wp: hoare_drop_imp maybeM_inv)

crunches refill_update, refill_new
  for domain_time_inv[wp]: "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps)

crunches set_extra_badge, schedule_tcb
  for domain_consumed_time_inv[wp]: "\<lambda>s. P (domain_time s)(consumed_time s)"
  (wp: crunch_wps)

crunches cap_insert, set_thread_state, postpone, reply_push
  for domain_consumed_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)(consumed_time s)"
  (wp: hoare_drop_imps mapM_wp' hoare_vcg_if_lift)

context DetSchedDomainTime_AI begin

crunch domain_time_inv[wp]:
  refill_budget_check,charge_budget,refill_budget_check_round_robin
  "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps check_cap_inv maybeM_inv simp: Let_def)

crunch domain_time_inv[wp]: invoke_untyped "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps
    simp: crunch_simps mapM_x_defsym)

crunch domain_time_inv[wp]: invoke_tcb "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps check_cap_inv
    simp: crunch_simps)

crunch domain_time_inv[wp]:
  invoke_domain, invoke_irq_control,invoke_irq_handler
  "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps check_cap_inv maybeM_inv)


crunch domain_time_inv[wp]: invoke_sched_context "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps check_cap_inv maybeM_inv
    simp: crunch_simps)

lemma commit_domain_time_domain_time:
  "\<lbrace>\<lambda>s. P (if domain_time s < consumed_time s then 0 else domain_time s - consumed_time s)\<rbrace>
      commit_domain_time \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  by (wpsimp simp: commit_domain_time_def)

crunch consumed_time_inv[wp]: set_thread_state,store_word_offs "\<lambda>s::det_state. P (consumed_time s)"
  (wp: crunch_wps dxo_wp_weak)

crunch domain_time_consumed_time[wp]: refill_budget_check, refill_budget_check_round_robin
  "\<lambda>s::det_state. P (domain_time s)(consumed_time s)"
  (wp: crunch_wps check_cap_inv maybeM_inv dxo_wp_weak
   simp: zipWithM_x_mapM Let_def)

crunch domain_time_consumed_time[wp]: do_ipc_transfer
  "\<lambda>s::det_state. P (domain_time s)(consumed_time s)"
  (wp: crunch_wps transfer_caps_loop_pres simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch domain_time_consumed_time[wp]: end_timeslice
  "\<lambda>s::det_state. P (domain_time s)(consumed_time s)"
  (wp: crunch_wps maybeM_inv simp: zipWithM_x_mapM ignore: do_reply_transfer)

crunch valid_domain_list[wp]:
  charge_budget,check_budget
  "valid_domain_list :: det_state \<Rightarrow> _"
  (wp: crunch_wps check_cap_inv mapM_wp' maybeM_inv simp: Let_def zipWithM_x_mapM)

crunch domain_time_inv[wp]:
  charge_budget,check_budget
  "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps check_cap_inv mapM_wp' maybeM_inv simp: Let_def zipWithM_x_mapM)

lemma charge_budget_domain_time_consumed_time:
   "\<lbrace>\<lambda>s::det_state. P (domain_time s) 0 \<rbrace>
    charge_budget consumed canTimeout
    \<lbrace>\<lambda>_ s. P (domain_time s) (consumed_time s)\<rbrace> "
  by (wpsimp simp: charge_budget_def wp: assert_inv)

lemma check_budget_domain_time_left[wp]:
  "\<lbrace> valid_domain_list and (\<lambda>s. consumed_time s < domain_time s)\<rbrace>
   check_budget
   \<lbrace>\<lambda>_ s::det_state. 0 < domain_time s \<rbrace>"
  by (wpsimp simp: check_budget_def word_gt_0)

lemma check_budget_domain_consumed_time_gt[wp]:
  "\<lbrace>\<lambda>s::det_state. consumed_time s < domain_time s\<rbrace> check_budget \<lbrace>\<lambda>_ s. consumed_time s  < domain_time s \<rbrace>"
  by (wpsimp simp: check_budget_def word_gt_0
               wp: charge_budget_domain_time_consumed_time)

lemma commit_domain_time_domain_time_left:
  "\<lbrace> valid_domain_list and (\<lambda>s. consumed_time s < domain_time s)\<rbrace>
   commit_domain_time
   \<lbrace>\<lambda>_ s. 0 < domain_time s \<rbrace>"
  apply (wpsimp simp: commit_domain_time_def Let_def)
  using word_gt_0 by fastforce

lemma commit_time_domain_time_left[wp]:
  "\<lbrace> valid_domain_list and (\<lambda>s. consumed_time s < domain_time s)\<rbrace>
   commit_time
   \<lbrace>\<lambda>_ s::det_state. 0 < domain_time s \<rbrace>"
  by (wpsimp simp: commit_time_def num_domains_def
               wp: commit_domain_time_domain_time_left hoare_drop_imp)

lemma invoke_sched_control_configure_flags_domain_time_inv[wp]:
  "\<lbrace>valid_domain_list and (\<lambda>s. consumed_time s < domain_time s)\<rbrace>
      invoke_sched_control_configure_flags i \<lbrace>\<lambda>_ s::det_state. 0 < domain_time s \<rbrace>"
  by (cases i)
     (wpsimp simp: invoke_sched_control_configure_flags_def split_def word_gt_0 tcb_release_remove_def
       split_del: if_split
       wp: hoare_vcg_if_lift2 hoare_drop_imp hoare_vcg_conj_lift
           commit_time_domain_time_left[simplified word_neq_0_conv[symmetric]]
           check_budget_domain_time_left[simplified word_neq_0_conv[symmetric]])

end

crunch domain_time_inv[wp]: cap_move "\<lambda>s::det_state. P (domain_time s)"

context DetSchedDomainTime_AI begin
lemma cap_revoke_domain_time_inv[wp]:
  "\<lbrace>(\<lambda>s :: det_state. P (domain_time s))\<rbrace> cap_revoke a \<lbrace>\<lambda>rv s. P (domain_time s)\<rbrace>"
  apply (rule cap_revoke_preservation2)
  apply (wp preemption_point_inv'|simp)+
  done
end

crunch domain_time_inv[wp]: cancel_badged_sends "\<lambda>s::det_state. P (domain_time s)"
  (ignore: filterM clearMemory
     simp: filterM_mapM crunch_simps
       wp: crunch_wps)

context DetSchedDomainTime_AI_2 begin

lemma invoke_cnode_domain_time_inv[wp]:
  "\<lbrace>\<lambda>s :: det_state. P (domain_time s)\<rbrace>
     invoke_cnode i
   \<lbrace>\<lambda>rv s. P (domain_time s) \<rbrace>"
  apply (rule hoare_pre)
   apply (wp crunch_wps cap_move_src_slot_Null hoare_drop_imps hoare_vcg_all_lift
          | wpc | simp add: invoke_cnode_def crunch_simps split del: if_split)+
  done

lemma perform_invocation_domain_time_inv:
  "\<lbrace>valid_domain_list and (\<lambda>s. consumed_time s < domain_time s)\<rbrace>
      perform_invocation block call can_donate i \<lbrace>\<lambda>_ s::det_state. 0 < domain_time s \<rbrace>"
  by (cases i; wpsimp; clarsimp simp: word_gt_0)

lemma handle_invocation_domain_time_inv[wp]:
  "\<lbrace>valid_domain_list and (\<lambda>s. consumed_time s < domain_time s)\<rbrace>
     handle_invocation calling blocking can_donate first_phase cptr
   \<lbrace>\<lambda>_ s::det_state. 0 < domain_time s \<rbrace>"
  by (wpsimp simp: handle_invocation_def
      wp: syscall_valid crunch_wps perform_invocation_domain_time_inv)
     (clarsimp simp: word_gt_0)

crunch domain_time_inv[wp]: receive_ipc,lookup_reply "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps simp: crunch_simps)

crunch domain_time_inv[wp]: receive_signal "\<lambda>s::det_state. P (domain_time s)"
  (wp: hoare_drop_imp hoare_vcg_if_lift2)

lemma handle_recv_domain_time_inv[wp]:
  "\<lbrace>\<lambda>s. P (domain_time s)\<rbrace>
  handle_recv is_blocking can_reply \<lbrace>\<lambda>rv s::det_state. P (domain_time s)\<rbrace>"
  apply (wpsimp simp: handle_recv_def Let_def whenE_def get_sk_obj_ref_def
                split_del: if_split wp: hoare_drop_imps)
  by (rule_tac Q'="\<lambda>_ s. P (domain_time s)" in hoare_post_imps(1))  wpsimp+


crunch domain_time_inv[wp]: handle_yield, handle_vm_fault, handle_hypervisor_fault
  "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps simp: crunch_simps)

lemma handle_call_domain_time_inv[wp]:
  "\<lbrace>valid_domain_list and (\<lambda>s. consumed_time s < domain_time s)\<rbrace>
      handle_call \<lbrace>\<lambda>_ s::det_state. 0 < domain_time s \<rbrace>"
  by (wpsimp simp: handle_call_def wp: handle_invocation_domain_time_inv)

lemma check_budget_restart_domain_time_inv[wp]:
  "\<lbrace>valid_domain_list and (\<lambda>s. consumed_time s < domain_time s)\<rbrace>
      check_budget_restart \<lbrace>\<lambda>_ s::det_state. 0 < domain_time s \<rbrace>"
  by (wpsimp simp: check_budget_restart_def)

lemma check_budget_restart_domain_consumed_time_gt[wp]:
  "\<lbrace>(\<lambda>s. consumed_time s < domain_time s)\<rbrace>
      check_budget_restart \<lbrace>\<lambda>_ s::det_state. consumed_time s  < domain_time s \<rbrace>"
  by (wpsimp simp: check_budget_restart_def)
(*
lemma update_time_stamp_domain_consumed_time_gt[wp]:
  "\<lbrace>\<lambda>s. P (domain_time s)\<rbrace>
      update_time_stamp \<lbrace>\<lambda>_ s. P (domain_time s)(consumed_time s) \<rbrace>"
  apply (clarsimp simp: update_time_stamp_def)
  apply (wpsimp simp: do_machine_op_def ARM.getCurrentTime_def)


lemma handle_event_domain_time_inv:
  "\<lbrace>valid_domain_list and (\<lambda>s. consumed_time s < domain_time s) and K (e \<noteq> Interrupt)\<rbrace>
      handle_event e \<lbrace>\<lambda>_ s. 0 < domain_time s\<rbrace>"
  apply (cases e, simp_all)
      apply (rename_tac syscall)
      apply (case_tac syscall, simp_all add: handle_send_def whenE_def)
             apply (wpsimp split_del: if_split wp: hoare_vcg_if_lift2 hoare_drop_imp)+
  apply (clarsimp simp: valid_domain_list_def)
  using word_gt_0 by fastforce*)

end

lemma reschedule_required_valid_domain_time:
  "\<lbrace> \<top> \<rbrace> reschedule_required
   \<lbrace>\<lambda>x s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding reschedule_required_def set_scheduler_action_def
  by (wpsimp wp: hoare_vcg_imp_lift is_schedulable_wp simp: thread_get_def)

crunch domain_time_inv[wp]: set_next_interrupt "\<lambda>s. P (domain_time s)"
  (wp: hoare_drop_imps)


context DetSchedDomainTime_AI begin

lemma switch_sched_context_domain_time_left[wp]:
  "\<lbrace>valid_domain_list and (\<lambda>s. consumed_time s < domain_time s)\<rbrace>
   switch_sched_context
   \<lbrace>\<lambda>_ s :: det_state. 0 < domain_time s\<rbrace>"
  apply (wpsimp simp: switch_sched_context_def refill_unblock_check_defs
                  wp: hoare_vcg_if_lift2 hoare_drop_imp whileLoop_wp' split_del: if_split)
  apply (clarsimp simp: word_gt_0)
  done

lemma sc_and_timer_domain_time_left[wp]:
  "\<lbrace> valid_domain_list and (\<lambda>s. consumed_time s < domain_time s)\<rbrace>
     sc_and_timer \<lbrace>\<lambda>_ s::det_state. 0 < domain_time s \<rbrace>"
  by (wpsimp simp: sc_and_timer_def Let_def)
(*
lemma next_domain_domain_time_left[wp]:
  "\<lbrace> valid_domain_list \<rbrace> next_domain \<lbrace>\<lambda>_ s. 0 < domain_time s \<rbrace>"
  apply (wpsimp simp: next_domain_def Let_def)
   apply (clarsimp simp: valid_domain_list_def)
   apply (simp add: all_set_conv_all_nth)
   apply (erule_tac x="Suc (domain_index s) mod length (domain_list s)" in allE)
   apply (clarsimp simp: \<mu>s_to_ms_def)


lemma schedule_choose_new_thread_domain_time_left[wp]:
  "\<lbrace> valid_domain_list \<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_ s. 0 < domain_time s \<rbrace>"
  unfolding schedule_choose_new_thread_def
  by (wpsimp simp: word_gt_0)

crunch valid_domain_list: schedule_choose_new_thread valid_domain_list

crunch etcb_at[wp]: tcb_sched_action "etcb_at P t"

lemma schedule_domain_time_left:
  "\<lbrace>valid_domain_list and (\<lambda>s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread) \<rbrace>
   schedule
   \<lbrace>\<lambda>_ s. 0 < domain_time s \<rbrace>" (is "\<lbrace>?P\<rbrace> _ \<lbrace>\<lambda>_ . ?Q\<rbrace>")
  supply word_neq_0_conv[simp]
  apply (simp add: schedule_def)
  apply (wp|wpc)+
(*           apply (wp hoare_drop_imps)[1]
          apply (wpsimp wp: gts_wp hoare_drop_imps simp: is_schedulable_def)+
  done*)
*)
end

(* FIXME: move to where hoare_drop_imp is, add E/R variants etc *)
lemma hoare_false_imp:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. \<not> R r s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. R r s \<longrightarrow> Q r s\<rbrace>"
  by (auto simp: valid_def)

context DetSchedDomainTime_AI_2 begin
(*
lemma call_kernel_domain_time_inv_det_ext:
  "\<lbrace> (\<lambda>s. 0 < domain_time s) and valid_domain_list and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) \<rbrace>
   (call_kernel e) :: (unit,det_ext) s_monad
   \<lbrace>\<lambda>_ s. 0 < domain_time s \<rbrace>"
  unfolding call_kernel_def
  apply (case_tac "e = Interrupt")
   apply simp
   apply (rule hoare_pre)
   apply ((wp schedule_domain_time_left handle_interrupt_valid_domain_time
           | wpc | simp)+)[1]
   apply (rule_tac Q="\<lambda>_ s. 0 < domain_time s \<and> valid_domain_list s" in hoare_strengthen_post)
    apply wp
   apply fastforce+
  (* now non-interrupt case; may throw but does not touch domain_time in handle_event *)
  apply (wp schedule_domain_time_left without_preemption_wp handle_interrupt_valid_domain_time)
    apply (rule_tac Q="\<lambda>_ s. 0 < domain_time s \<and> valid_domain_list s" in hoare_post_imp)
(*     apply fastforce
    apply (wp handle_event_domain_time_inv)+
   apply (rule_tac Q'="\<lambda>_ s. 0 < domain_time s" in hoare_post_imp_R)
    apply (wp handle_event_domain_time_inv)
   apply fastf orce+
  done*) *)
end

end
