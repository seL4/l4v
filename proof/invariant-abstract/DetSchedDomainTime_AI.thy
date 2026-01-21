(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory DetSchedDomainTime_AI
imports ArchDetSchedAux_AI
begin

text \<open>
  This theory deals with the preservation of domain_list validity over kernel invocations,
  as well as ensuring preserving that the domain time is never zero at kernel exit.
\<close>

(* Note: domains in the domain list should also be \<le> maxDomain, but this is not needed right now *)
definition
  "valid_domain_list_2 start dlist \<equiv>
     0 < length dlist \<and> (\<forall>(d,time) \<in> set dlist. time = 0 \<longrightarrow> d = 0) \<and>
     start < length dlist \<and> dlist ! start \<noteq> (0,0)"

abbreviation
  valid_domain_list :: "'z state \<Rightarrow> bool"
where
  "valid_domain_list \<equiv> \<lambda>s. valid_domain_list_2 (domain_start_index s) (domain_list s)"

lemmas valid_domain_list_def = valid_domain_list_2_def

lemma valid_domain_list_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (domain_list s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (domain_start_index s)\<rbrace>"
  shows "f \<lbrace>valid_domain_list\<rbrace>"
  by (rule hoare_lift_Pf[OF assms])

section \<open>Preservation of domain list validity\<close>

(*
  FIXME: cleanup
  Many of these could be factored out into the general state_ext class instead, but they will be
  applied to det_ext lemmas that contain e.g. preemption_point which needs the det_ext work_units,
  i.e. those will need additional locales, because 'state_ext needs to be interpreted first
  into ?'state_ext.
*)
locale DetSchedDomainTime_AI =
  assumes finalise_cap_domain_list_inv'[wp]:
    "\<And>P cap fin. arch_finalise_cap cap fin \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace>"
  assumes finalise_cap_domain_start_index_inv'[wp]:
    "\<And>P cap fin. arch_finalise_cap cap fin \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes arch_activate_idle_thread_domain_list_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_activate_idle_thread t \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_activate_idle_thread_domain_start_index_inv'[wp]:
    "\<And>P t. arch_activate_idle_thread t \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes arch_switch_to_thread_domain_list_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_switch_to_thread_domain_start_index_inv'[wp]:
    "\<And>P t. arch_switch_to_thread t \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes arch_get_sanitise_register_info_domain_list_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_get_sanitise_register_info t \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_get_sanitise_register_info_domain_start_index_inv'[wp]:
    "\<And>P t. arch_get_sanitise_register_info t \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes arch_switch_to_idle_thread_domain_list_inv'[wp]:
    "\<And>P. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_switch_to_idle_thread_domain_start_index_inv'[wp]:
    "\<And>P. arch_switch_to_idle_thread \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes handle_arch_fault_reply_domain_list_inv'[wp]:
    "\<And>P f t x y. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes handle_arch_fault_reply_domain_start_index_inv'[wp]:
    "\<And>P f t x y. handle_arch_fault_reply f t x y \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes init_arch_objects_domain_list_inv'[wp]:
    "\<And>P t d p n s r. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> init_arch_objects t d p n s r \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes init_arch_objects_domain_start_index_inv'[wp]:
    "\<And>P t d p n s r. init_arch_objects t d p n s r \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes arch_post_modify_registers_domain_list_inv'[wp]:
    "\<And>P t p. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_post_modify_registers t p \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_post_modify_registers_domain_start_index_inv'[wp]:
    "\<And>P t p. arch_post_modify_registers t p \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes arch_invoke_irq_control_domain_list_inv'[wp]:
    "\<And>P i. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_invoke_irq_control i \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_invoke_irq_control_domain_start_idnex_inv'[wp]:
    "\<And>P i. arch_invoke_irq_control i \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes handle_vm_fault_domain_list_inv'[wp]:
    "\<And>P t f. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes handle_vm_fault_domain_start_index_inv'[wp]:
    "\<And>P t f. handle_vm_fault t f \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes prepare_thread_delete_domain_list_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes prepare_thread_delete_domain_start_index_inv'[wp]:
    "\<And>P t. prepare_thread_delete t \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes finalise_cap_domain_time_inv'[wp]:
    "\<And>P cap fin. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_finalise_cap cap fin \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_activate_idle_thread_domain_time_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_activate_idle_thread t \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_switch_to_thread_domain_time_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_get_sanitise_register_info_domain_time_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_get_sanitise_register_info t \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_switch_to_idle_thread_domain_time_inv'[wp]:
    "\<And>P. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes handle_arch_fault_reply_domain_time_inv'[wp]:
    "\<And>P f t x y. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes init_arch_objects_domain_time_inv'[wp]:
    "\<And>P t d p n s r. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> init_arch_objects t d p n s r \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_post_modify_registers_domain_time_inv'[wp]:
    "\<And>P t p. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_post_modify_registers t p \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_invoke_irq_control_domain_time_inv'[wp]:
    "\<And>P i. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_invoke_irq_control i \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes handle_vm_fault_domain_time_inv'[wp]:
    "\<And>P t f. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes prepare_thread_delete_domain_time_inv'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_post_cap_deletion_domain_time_inv'[wp]:
    "\<And>P ft. \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> arch_post_cap_deletion ft \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  assumes arch_post_cap_deletion_domain_list_inv'[wp]:
    "\<And>P ft. \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> arch_post_cap_deletion ft \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  assumes arch_post_cap_deletion_domain_start_index_inv'[wp]:
    "\<And>P ft. arch_post_cap_deletion ft \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes arch_invoke_irq_handler_domain_list_inv'[wp]:
    "\<And>P i. arch_invoke_irq_handler i \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace>"
  assumes arch_invoke_irq_handler_domain_start_index_inv'[wp]:
    "\<And>P i. arch_invoke_irq_handler i \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes arch_invoke_irq_handler_domain_time_inv'[wp]:
    "\<And>P i. arch_invoke_irq_handler i \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace>"
  assumes arch_prepare_next_domain_domain_list_inv'[wp]:
    "\<And>P. arch_prepare_next_domain \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace>"
  assumes arch_prepare_next_domain_domain_start_index_inv'[wp]:
    "\<And>P. arch_prepare_next_domain \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes arch_prepare_set_domain_domain_list_inv'[wp]:
    "\<And>P t d. arch_prepare_set_domain t d \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace>"
  assumes arch_prepare_set_domain_domain_start_index_inv'[wp]:
    "\<And>P t d. arch_prepare_set_domain t d \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes arch_post_set_flags_domain_list_inv'[wp]:
    "\<And>P t fs. arch_post_set_flags t fs \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace>"
  assumes arch_post_set_flags_domain_start_index_inv'[wp]:
    "\<And>P t fs. arch_post_set_flags t fs \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes arch_prepare_set_domain_domain_time_inv'[wp]:
    "\<And>P t d. arch_prepare_set_domain t d \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace>"
  assumes arch_post_set_flags_domain_time_inv'[wp]:
    "\<And>P t fs. arch_post_set_flags t fs \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace>"

crunch update_restart_pc
  for domain_list[wp]: "\<lambda>s. P (domain_list s)"
  and domain_time[wp]: "\<lambda>s. P (domain_time s)"
  and domain_start_index[wp]: "\<lambda>s. P (domain_start_index s)"
  (wp: crunch_wps)

locale DetSchedDomainTime_AI_2 = DetSchedDomainTime_AI +
  assumes handle_hypervisor_fault_domain_list_inv'[wp]:
    "\<And>P t f. \<lbrace>\<lambda>s. P (domain_list s)\<rbrace> handle_hypervisor_fault t f \<lbrace>\<lambda>_ s::det_state. P (domain_list s)\<rbrace>"
  assumes handle_hypervisor_fault_domain_start_index_inv'[wp]:
    "\<And>P t f. handle_hypervisor_fault t f \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes handle_hypervisor_fault_domain_time_inv'[wp]:
    "\<And>P t f. \<lbrace>\<lambda>s. P (domain_time s)\<rbrace> handle_hypervisor_fault t f \<lbrace>\<lambda>_ s::det_state. P (domain_time s)\<rbrace>"
  assumes arch_perform_invocation_domain_list_inv'[wp]:
    "\<And>P i. \<lbrace>\<lambda>s. P (domain_list s)\<rbrace> arch_perform_invocation i \<lbrace>\<lambda>_ s::det_state. P (domain_list s)\<rbrace>"
  assumes arch_perform_invocation_domain_start_index_inv'[wp]:
    "\<And>P i. arch_perform_invocation i \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes arch_perform_invocation_domain_time_inv'[wp]:
    "\<And>P i. \<lbrace>\<lambda>s. P (domain_time s)\<rbrace> arch_perform_invocation i \<lbrace>\<lambda>_ s::det_state. P (domain_time s)\<rbrace>"
  assumes handle_interrupt_valid_domain_time:
    "\<And>i.
      \<lbrace>\<lambda>s :: det_ext state. 0 < domain_time s \<rbrace>
        handle_interrupt i
      \<lbrace>\<lambda>rv s.  domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread \<rbrace>"
  assumes handle_reserved_irq_some_time_inv'[wp]:
    "\<And>P irq. \<lbrace>\<lambda>s. P (domain_time s)\<rbrace> handle_reserved_irq irq \<lbrace>\<lambda>_ s::det_state. P (domain_time s)\<rbrace>"
  assumes handle_reserved_irq_domain_list_inv'[wp]:
    "\<And>P irq. \<lbrace>\<lambda>s. P (domain_list s)\<rbrace> handle_reserved_irq irq \<lbrace>\<lambda>_ s::det_state. P (domain_list s)\<rbrace>"
  assumes handle_reserved_irq_domain_start_index_inv'[wp]:
    "\<And>P irq. handle_reserved_irq irq \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes arch_mask_irq_signal_domain_list_inv'[wp]:
    "\<And>P irq. arch_mask_irq_signal irq \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace>"
  assumes arch_mask_irq_signal_domain_start_index_inv'[wp]:
    "\<And>P irq. arch_mask_irq_signal irq \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes arch_mask_irq_signal_domain_time_inv'[wp]:
    "\<And>P irq. arch_mask_irq_signal irq \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace>"
  assumes handle_spurious_irq_domain_time_inv'[wp]:
    "\<And>P. handle_spurious_irq \<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace>"
  assumes handle_spurious_irq_domain_list_inv'[wp]:
    "\<And>P. handle_spurious_irq \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace>"
  assumes handle_spurious_irq_domain_start_index_inv'[wp]:
    "\<And>P. handle_spurious_irq \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  assumes handle_spurious_irq_scheduler_action[wp]:
    "handle_spurious_irq \<lbrace>\<lambda>s::det_state. P (scheduler_action s) \<rbrace>"

context DetSchedDomainTime_AI begin

crunch
  cap_swap_for_delete, empty_slot, get_object, get_cap, tcb_sched_action
  for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"

crunch finalise_cap
  for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"
  (wp: crunch_wps unless_wp select_inv simp: crunch_simps)

lemma rec_del_domain_list[wp]:
  "rec_del call \<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace>"
  by (wp rec_del_preservation preemption_point_inv' | simp)+

lemma rec_del_domain_start_index[wp]:
  "rec_del call \<lbrace>\<lambda>s::det_state. P (domain_start_index s)\<rbrace>"
  by (wp rec_del_preservation preemption_point_inv' | simp)+

crunch cap_delete, activate_thread
  for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"

crunch schedule
  for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"
  (wp: hoare_drop_imp dxo_wp_weak simp: Let_def)

end

crunch (in DetSchedDomainTime_AI_2) handle_interrupt
  for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"

crunch cap_insert
 for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"
  (wp: hoare_drop_imps)

crunch
  lookup_cap_and_slot, set_extra_badge
  for domain_list_inv[wp]: "\<lambda>s. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"
  (wp: hoare_drop_imps)

context DetSchedDomainTime_AI begin
crunch do_ipc_transfer
  for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"
  (wp: crunch_wps simp: zipWithM_x_mapM rule: transfer_caps_loop_pres)

crunch handle_fault
  for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"
  (wp: mapM_wp hoare_drop_imps simp: crunch_simps ignore:copy_mrs)


crunch
  reply_from_kernel, create_cap, retype_region, do_reply_transfer
  for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"
  (wp: hoare_drop_imps)
end

crunch delete_objects
  for domain_list_inv[wp]: "\<lambda>s :: det_ext state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"
  (wp: crunch_wps simp: detype_def)

crunch preemption_point
  for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"
  (wp: OR_choiceE_weak_wp ignore_del: preemption_point)

crunch reset_untyped_cap
  for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"
  (wp: crunch_wps unless_wp mapME_x_inv_wp select_inv
   simp: crunch_simps)

context DetSchedDomainTime_AI begin

crunch invoke_untyped
  for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"
  (wp: crunch_wps
    simp: crunch_simps mapM_x_defsym)

crunch
  invoke_tcb, invoke_set_domain, invoke_irq_control, invoke_irq_handler
  for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"
  (wp: crunch_wps check_cap_inv)

end

crunch cap_move
  for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"

context DetSchedDomainTime_AI begin

lemma cap_revoke_domain_list_inv[wp]:
  "cap_revoke a \<lbrace>\<lambda>s::det_ext state. P (domain_list s)\<rbrace>"
  by (rule cap_revoke_preservation2)
     (wp preemption_point_inv'|simp)+

lemma cap_revoke_domain_start_index_inv[wp]:
  "cap_revoke a \<lbrace>\<lambda>s::det_ext state. P (domain_start_index s)\<rbrace>"
  by (rule cap_revoke_preservation2)
     (wp preemption_point_inv'|simp)+

end

crunch cancel_badged_sends
  for domain_list_inv[wp]: "\<lambda>s. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"
  (ignore: filterM clearMemory
     simp: filterM_mapM crunch_simps
       wp: crunch_wps)

context DetSchedDomainTime_AI_2 begin

lemma handle_spurious_irq_valid_domain[wp]:
  "handle_spurious_irq \<lbrace>\<lambda>s::det_state. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread \<rbrace>"
  by (wp | wps)+

lemma invoke_cnode_domain_list_inv[wp]:
  "invoke_cnode i \<lbrace>\<lambda>s :: det_ext state. P (domain_list s) \<rbrace>"
  by (wpsimp wp: crunch_wps cap_move_src_slot_Null hoare_drop_imps hoare_vcg_all_lift
             simp: invoke_cnode_def crunch_simps
             split_del: if_split)

lemma invoke_cnode_domain_start_index_inv[wp]:
  "invoke_cnode i \<lbrace>\<lambda>s :: det_ext state. P (domain_start_index s) \<rbrace>"
  by (wpsimp wp: crunch_wps cap_move_src_slot_Null hoare_drop_imps hoare_vcg_all_lift
             simp: invoke_cnode_def crunch_simps
             split_del: if_split)

crunch
  handle_recv, handle_yield, handle_reply, handle_vm_fault, handle_hypervisor_fault,
  maybe_handle_interrupt
  for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"
  (wp: crunch_wps simp: crunch_simps)

lemma domain_set_start_valid_domain_list_inv[wp]:
  "\<lbrace>valid_domain_list and valid_domain_inv (InvokeDomainScheduleSetStart start)\<rbrace>
   domain_set_start start
   \<lbrace>\<lambda>_ s::det_state. valid_domain_list s\<rbrace>"
  unfolding domain_set_start_def
  apply (wpsimp wp: valid_domain_list_lift[of reschedule_required])
  apply (simp add: valid_domain_inv_def valid_domain_list_def domain_end_marker_def)
  done

lemma domain_schedule_configure_valid_domain_list_inv[wp]:
  "\<lbrace>valid_domain_list and valid_domain_inv (InvokeDomainScheduleConfigure index domain duration)\<rbrace>
   domain_schedule_configure index domain duration
   \<lbrace>\<lambda>_ s::det_state. valid_domain_list s\<rbrace>"
  unfolding domain_schedule_configure_def
  apply wpsimp
  apply (simp add: valid_domain_inv_def valid_domain_list_def domain_end_marker_def)
  apply (rule conjI; clarsimp)
   apply (cut_tac set_update_subset_insert)
   apply fastforce
  apply (metis nth_list_update_eq nth_list_update_neq snd_conv)
  done

lemma invoke_domain_valid_domain_list_inv[wp]:
  "\<lbrace>valid_domain_list and valid_domain_inv di\<rbrace>
   invoke_domain di
   \<lbrace>\<lambda>_ s::det_state. valid_domain_list s\<rbrace>"
  unfolding invoke_domain_def
  apply (wpsimp wp: valid_domain_list_lift[where f="invoke_set_domain t d" for t d])
  apply fastforce
  done

lemma perform_invocation_valid_domain_list_inv[wp]:
  "\<lbrace>valid_domain_list and valid_invocation iv\<rbrace>
   perform_invocation block call iv
   \<lbrace>\<lambda>_ s::det_state. valid_domain_list s\<rbrace>"
  by (cases iv; (wpsimp | wp valid_domain_list_lift)+)


lemma handle_invocation_valid_domain_list_inv[wp]:
  "\<lbrace>valid_domain_list and invs\<rbrace>
   handle_invocation calling blocking
   \<lbrace>\<lambda>_ s::det_state. valid_domain_list s\<rbrace>"
proof -
  have [simp]:
    "\<And>x P. (\<forall>a b c. x = (a, b, c) \<longrightarrow> P a b c) = P (fst x) (fst (snd x)) (snd (snd x))"
    by fastforce

  show ?thesis
    unfolding handle_invocation_def
    by (wpsimp wp: syscall_valid gts_wp
        | wp valid_domain_list_lift
        | wp hoare_vcg_all_liftE_R hoare_drop_impE_R)+
qed

crunch handle_call, handle_send
  for valid_domain_list_inv[wp]: "\<lambda>s::det_state. valid_domain_list s"

lemma handle_event_domain_list_inv[wp]:
  "\<lbrace>valid_domain_list and invs\<rbrace>
   handle_event e
   \<lbrace>\<lambda>_ s::det_state. valid_domain_list s\<rbrace>"
  by (cases e; (wpsimp | wp valid_domain_list_lift)+)

lemma call_kernel_domain_list_inv_det_ext:
  "\<lbrace>valid_domain_list and invs\<rbrace>
     (call_kernel e) :: (unit,det_ext) s_monad
   \<lbrace>\<lambda>_. valid_domain_list\<rbrace>"
  unfolding call_kernel_def
  by (wpsimp | wp valid_domain_list_lift)+

end


section \<open>Preservation of domain time remaining\<close>

crunch do_user_op
  for domain_time_inv[wp]: "(\<lambda>s. P (domain_time s))"

context DetSchedDomainTime_AI begin

crunch
  get_cap, activate_thread, set_scheduler_action, tcb_sched_action, thread_set_time_slice
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"

crunch guarded_switch_to
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"
  (wp: hoare_drop_imp whenE_inv)

crunch choose_thread
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"

crunch send_signal
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"
  (wp: hoare_drop_imps mapM_x_wp_inv simp: crunch_simps unless_def)

crunch
  cap_swap_for_delete, empty_slot, get_object, get_cap, tcb_sched_action
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"

crunch finalise_cap
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps hoare_drop_imps unless_wp select_inv mapM_wp
       subset_refl if_fun_split simp: crunch_simps ignore: tcb_sched_action)

lemma rec_del_domain_time[wp]:
  "\<lbrace>\<lambda>s. P (domain_time s)\<rbrace> rec_del call \<lbrace>\<lambda>rv s::det_state. P (domain_time s)\<rbrace>"
  by (wp rec_del_preservation preemption_point_inv' | simp)+

crunch
  cap_delete, activate_thread, lookup_cap_and_slot
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"

end

crunch cap_insert
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"
  (wp: hoare_drop_imps)

crunch set_extra_badge
  for domain_time_inv[wp]: "\<lambda>s. P (domain_time s)"

context DetSchedDomainTime_AI begin

crunch do_ipc_transfer
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps simp: zipWithM_x_mapM rule: transfer_caps_loop_pres)

crunch handle_fault
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"
  (wp: mapM_wp hoare_drop_imps simp: crunch_simps ignore:copy_mrs)

crunch
  reply_from_kernel, create_cap, retype_region
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"

crunch do_reply_transfer
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"
  (wp: hoare_drop_imps)
end

crunch delete_objects
  for domain_time_inv[wp]: "\<lambda>s :: det_ext state. P (domain_time s)"
  (wp: crunch_wps simp: detype_def)

crunch preemption_point
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"
  (wp: OR_choiceE_weak_wp ignore_del: preemption_point)

crunch reset_untyped_cap
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps unless_wp mapME_x_inv_wp select_inv
   simp: crunch_simps)

context DetSchedDomainTime_AI begin

crunch invoke_untyped
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps
    simp: crunch_simps mapM_x_defsym)

crunch
  invoke_tcb, invoke_set_domain, domain_schedule_configure, invoke_irq_control, invoke_irq_handler
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps check_cap_inv)

end

crunch cap_move
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"

context DetSchedDomainTime_AI begin
lemma cap_revoke_domain_time_inv[wp]:
  "\<lbrace>(\<lambda>s :: det_ext state. P (domain_time s))\<rbrace> cap_revoke a \<lbrace>\<lambda>rv s. P (domain_time s)\<rbrace>"
  apply (rule cap_revoke_preservation2)
  apply (wp preemption_point_inv'|simp)+
  done
end

crunch cancel_badged_sends
  for domain_time_inv[wp]: "\<lambda>s. P (domain_time s)"
  (ignore: filterM clearMemory
     simp: filterM_mapM crunch_simps
       wp: crunch_wps)

lemma reschedule_required_choose_new_thread[wp]:
  "\<lbrace> \<top> \<rbrace> reschedule_required
   \<lbrace>\<lambda>x s. scheduler_action s = choose_new_thread\<rbrace>"
  unfolding reschedule_required_def set_scheduler_action_def
  by (wp hoare_vcg_imp_lift | simp | wpc)+

lemma reschedule_required_valid_domain_time:
  "\<lbrace> \<top> \<rbrace> reschedule_required
   \<lbrace>\<lambda>x s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  by (wpsimp wp: hoare_drop_imp reschedule_required_choose_new_thread)

lemma domain_set_start_valid_domain_time[wp]:
  "\<lbrace>\<top>\<rbrace>
   domain_set_start start
   \<lbrace>\<lambda>_ s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding domain_set_start_def
  by (wpsimp wp: reschedule_required_valid_domain_time)

context DetSchedDomainTime_AI_2 begin

lemma invoke_cnode_domain_time_inv[wp]:
  "\<lbrace>\<lambda>s :: det_ext state. P (domain_time s)\<rbrace>
     invoke_cnode i
   \<lbrace>\<lambda>rv s. P (domain_time s) \<rbrace>"
  apply (rule hoare_pre)
   apply (wp crunch_wps cap_move_src_slot_Null hoare_drop_imps hoare_vcg_all_lift
          | wpc | simp add: invoke_cnode_def crunch_simps split del: if_split)+
  done

crunch
  handle_recv, handle_yield, handle_reply, handle_vm_fault, handle_hypervisor_fault
  for domain_time_inv[wp]: "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps simp: crunch_simps)

lemma domain_time_strg:
  "0 < domain_time s \<Longrightarrow> domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread"
  by fastforce

lemma invoke_domain_domain_time_valid[wp]:
  "\<lbrace>\<lambda>s::det_state. 0 < domain_time s\<rbrace>
   invoke_domain di
   \<lbrace>\<lambda>_ s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding invoke_domain_def
  by (wpsimp | strengthen domain_time_strg)+

lemma perform_invocation_domain_time_valid[wp]:
  "\<lbrace>\<lambda>s::det_state. 0 < domain_time s\<rbrace>
   perform_invocation block call iv
   \<lbrace>\<lambda>_ s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  by (cases iv; (wpsimp | strengthen domain_time_strg)+)

lemma domain_time_valid_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (domain_time s)\<rbrace>"
  shows "\<lbrace>\<lambda>s::det_state. 0 < domain_time s\<rbrace>
         f
         \<lbrace>\<lambda>_ s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  by (strengthen domain_time_strg)
     (wp assms)

lemma sts_domain_time_valid:
  "set_thread_state t st
   \<lbrace>\<lambda>s::det_state. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding set_thread_state_def set_thread_state_act_def set_scheduler_action_def
  by (wpsimp wp: gts_wp set_object_wp)

crunch reply_from_kernel
  for schact_inv[wp]: "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps simp: crunch_simps)

lemma reply_from_kernel_domain_time_valid:
  "reply_from_kernel thread msg
   \<lbrace>\<lambda>s::det_state. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  by (wpsimp wp: hoare_vcg_imp_lift)

lemma handle_invocation_domain_time_valid[wp]:
  "\<lbrace>\<lambda>s::det_state. 0 < domain_time s\<rbrace>
   handle_invocation calling blocking
   \<lbrace>\<lambda>_ s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding handle_invocation_def
  apply (wpsimp wp: syscall_valid gts_wp
                    domain_time_valid_lift[where f="handle_fault t ex" for t ex]
                    sts_domain_time_valid reply_from_kernel_domain_time_valid
                    hoare_vcg_all_liftE_R
                    hoare_drop_impE_R[where Q'="\<lambda>_. st_tcb_at P st" for P st]
                    hoare_drop_impE_R[where Q'="\<lambda>_ _. Q'" for Q']
                split_del: if_split)
        apply (strengthen domain_time_strg)
        apply (wpsimp wp: hoare_drop_imps)
       apply (wpsimp simp: if_apply_def2 split_del: if_split)+
      apply (rule_tac Q'="\<lambda>_ s. 0 < domain_time s" in hoare_strengthen_postE_R)
       apply wp
      apply clarsimp
     apply (wpsimp split_del: if_split)+
  apply clarsimp
  done

lemma handle_event_domain_time_valid[wp]:
  "\<lbrace>\<lambda>s::det_state. 0 < domain_time s \<and> e \<noteq> Interrupt \<rbrace>
   handle_event e
   \<lbrace>\<lambda>_ s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  apply (cases e; simp)
      apply (wpsimp simp : handle_send_def handle_call_def | strengthen domain_time_strg)+
  done

lemma perform_invocation_domain_time_invE[wp]:
  "\<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace>
   perform_invocation blocking calling iv
   -, \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  by (cases iv; wpsimp)

lemma handle_invocation_domain_time_invE[wp]:
  "\<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace>
   handle_invocation calling blocking
   -, \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  unfolding handle_invocation_def syscall_def
  by (wpsimp wp: crunch_wps)

lemma handle_event_domain_time_invE[wp]:
  "\<lbrace>\<lambda>s::det_state. P (domain_time s)\<rbrace> handle_event e -, \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  by (cases e; wpsimp simp: handle_call_def handle_send_def)+

end

lemma next_domain_domain_time_left[wp]:
  "\<lbrace> valid_domain_list \<rbrace> next_domain \<lbrace>\<lambda>_ s. 0 < domain_time s \<rbrace>"
  unfolding next_domain_def Let_def
  apply (wpsimp wp: dxo_wp_weak)
  apply (fastforce simp: valid_domain_list_def all_set_conv_all_nth word_greater_zero_iff
                         ucast_eq_0 is_up domain_end_marker_def not_le)
  done

context DetSchedDomainTime_AI begin

lemma schedule_choose_new_thread_domain_time_left[wp]:
  "\<lbrace> valid_domain_list \<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_ s::det_state. 0 < domain_time s \<rbrace>"
  unfolding schedule_choose_new_thread_def
  by (wpsimp simp: word_gt_0 wp: valid_domain_list_lift)

crunch tcb_sched_action
  for etcb_at[wp]: "etcb_at P t"

lemma schedule_domain_time_left:
  "\<lbrace>valid_domain_list and (\<lambda>s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread) \<rbrace>
   schedule
   \<lbrace>\<lambda>_ s::det_state. 0 < domain_time s \<rbrace>" (is "\<lbrace>?P\<rbrace> _ \<lbrace>\<lambda>_ . ?Q\<rbrace>")
  supply word_neq_0_conv[simp]
  apply (simp add: schedule_def)
  apply (wp valid_domain_list_lift|wpc)+
           apply (wp hoare_drop_imp)[1]
          apply (wpsimp wp: gts_wp valid_domain_list_lift)+
  apply auto
  done

end (* context DetSchedDomainTime_AI *)

(* FIXME: move to where hoare_drop_imp is, add E/R variants etc *)
lemma hoare_false_imp:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. \<not> R r s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. R r s \<longrightarrow> Q r s\<rbrace>"
  by (auto simp: valid_def)

context DetSchedDomainTime_AI_2 begin

lemma maybe_handle_interrupt_valid_domain_time:
  "\<lbrace>\<lambda>s. 0 < domain_time s \<rbrace>
   maybe_handle_interrupt in_kernel :: (unit, det_ext) s_monad
   \<lbrace>\<lambda>_ s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding maybe_handle_interrupt_def
  apply (wpsimp wp: handle_interrupt_valid_domain_time)
   apply (rule_tac Q'="\<lambda>_ s. 0 < domain_time s" in hoare_strengthen_post)
    apply wpsimp+
  done

lemma call_kernel_domain_time_inv_det_ext:
  "\<lbrace>(\<lambda>s. 0 < domain_time s) and valid_domain_list and invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
   (call_kernel e) :: (unit,det_ext) s_monad
   \<lbrace>\<lambda>_ s. 0 < domain_time s \<rbrace>"
  unfolding call_kernel_def
  apply (cases "e = Interrupt"; simp)
   apply (wpsimp wp: schedule_domain_time_left maybe_handle_interrupt_valid_domain_time
                     valid_domain_list_lift)
  (* now non-interrupt case *)
  apply (wpsimp wp: schedule_domain_time_left without_preemption_wp
                    maybe_handle_interrupt_valid_domain_time handle_event_domain_time_valid
                    valid_domain_list_lift[where f="maybe_handle_interrupt in_kernel" for in_kernel])
  done

end

end
