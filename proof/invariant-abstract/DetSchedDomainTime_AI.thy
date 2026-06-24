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
  as well as ensuring preserving that the domain time is never zero at kernel exit (if there is
  more than one domain).
\<close>

(* Note: domains in the domain list should also be \<le> maxDomain, but this is not needed right now *)
definition valid_domain_list_2 :: "nat \<Rightarrow> nat \<Rightarrow> (domain \<times> domain_duration) list \<Rightarrow> bool" where
  "valid_domain_list_2 start index dlist \<equiv>
     \<comment> \<open>We need at least two entries in the schedule: One active entry and the reserved domain end
         marker at the end. Technically this is redundant with the last conjunct in this predicate,
         but it is convenient to have it spelled out.\<close>
     1 < length dlist \<and>
     \<comment> \<open>Time can only be 0 in the end marker.\<close>
     (\<forall>(d,time) \<in> set dlist. time = 0 \<longrightarrow> d = 0) \<and>
     start < length dlist \<and>
     \<comment> \<open>The start must always be a non-end-marker so that the schedule can make progress.\<close>
     dlist ! start \<noteq> (0,0) \<and>
     \<comment> \<open>The last entry in the schedule is reserved to always be an end marker.\<close>
     dlist ! (length dlist - 1) = (0,0) \<and>
     \<comment> \<open>The current index never gets to the final end marker.\<close>
     index < length dlist - 1"

abbreviation
  valid_domain_list :: "'z state \<Rightarrow> bool"
where
  "valid_domain_list \<equiv>
     \<lambda>s. valid_domain_list_2 (domain_start_index s) (domain_index s) (domain_list s)"

lemmas valid_domain_list_def = valid_domain_list_2_def

lemma valid_domain_list_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (domain_list s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (domain_index s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (domain_start_index s)\<rbrace>"
  shows "f \<lbrace>valid_domain_list\<rbrace>"
  by (wp_pre, wps assms, wp)

section \<open>Preservation of domain list validity\<close>

abbreviation (input) domain_fields ::
  "(ticks \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (domain \<times> domain_duration) list \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> bool"
  where
  "domain_fields P s \<equiv> P (domain_time s) (domain_index s) (domain_start_index s) (domain_list s)"

abbreviation (input) dlist_fields ::
  "(nat \<Rightarrow> nat \<Rightarrow> (domain \<times> domain_duration) list \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> bool"
  where
  "dlist_fields P s \<equiv> P (domain_index s) (domain_start_index s) (domain_list s)"

lemma valid_domain_list_lift':
  assumes "\<And>P. f \<lbrace>domain_fields P\<rbrace>"
  shows "f \<lbrace>valid_domain_list\<rbrace>"
  by (wp assms)

crunch schedule_tcb, set_thread_state
  for domain_list_inv[wp]: "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps)

locale DetSchedDomainTime_AI =
  assumes finalise_cap_domain_fields_inv[wp]:
    "\<And>P cap fin. arch_finalise_cap cap fin \<lbrace>domain_fields P\<rbrace>"
  assumes arch_activate_idle_thread_domain_fields_inv[wp]:
    "\<And>P t. arch_activate_idle_thread t \<lbrace>domain_fields P\<rbrace>"
  assumes arch_switch_to_thread_domain_fields_inv[wp]:
    "\<And>P t. arch_switch_to_thread t \<lbrace>domain_fields P\<rbrace>"
  assumes arch_get_sanitise_register_info_domain_fields_inv[wp]:
    "\<And>P t. arch_get_sanitise_register_info t \<lbrace>domain_fields P\<rbrace>"
  assumes arch_switch_to_idle_thread_domain_fields_inv[wp]:
    "\<And>P. arch_switch_to_idle_thread \<lbrace>domain_fields P\<rbrace>"
  assumes handle_arch_fault_reply_domain_fields_inv[wp]:
    "\<And>P f t x y. handle_arch_fault_reply f t x y \<lbrace>domain_fields P\<rbrace>"
  assumes init_arch_objects_domain_fields_inv[wp]:
    "\<And>P t d p n s r. init_arch_objects t d p n s r \<lbrace>domain_fields P\<rbrace>"
  assumes arch_post_modify_registers_domain_fields_inv[wp]:
    "\<And>P t p. arch_post_modify_registers t p \<lbrace>domain_fields P\<rbrace>"
  assumes arch_invoke_irq_control_domain_fields_inv[wp]:
    "\<And>P i. arch_invoke_irq_control i \<lbrace>domain_fields P\<rbrace>"
  assumes handle_vm_fault_domain_fields_inv[wp]:
    "\<And>P t f. handle_vm_fault t f \<lbrace>domain_fields P\<rbrace>"
  assumes prepare_thread_delete_domain_fields_inv[wp]:
    "\<And>P t. prepare_thread_delete t \<lbrace>domain_fields P\<rbrace>"
  assumes arch_post_cap_deletion_domain_fields_inv[wp]:
    "\<And>P ft. arch_post_cap_deletion ft \<lbrace>domain_fields P\<rbrace>"
  assumes arch_invoke_irq_handler_domain_fields_inv[wp]:
    "\<And>P i. arch_invoke_irq_handler i \<lbrace>domain_fields P\<rbrace>"
  assumes arch_prepare_next_domain_domain_fields_inv[wp]:
    "\<And>P. arch_prepare_next_domain \<lbrace>domain_fields P\<rbrace>"
  assumes arch_prepare_set_domain_domain_fields_inv[wp]:
    "\<And>P t d. arch_prepare_set_domain t d \<lbrace>domain_fields P\<rbrace>"
  assumes arch_post_set_flags_domain_fields_inv[wp]:
    "\<And>P t fs. arch_post_set_flags t fs \<lbrace>domain_fields P\<rbrace>"

crunch update_restart_pc
  for domain_fields[wp]: "domain_fields P"
  (wp: crunch_wps)

locale DetSchedDomainTime_AI_2 = DetSchedDomainTime_AI +
  assumes handle_hypervisor_fault_domain_fields_invs[wp]:
    "\<And>P t f. handle_hypervisor_fault t f \<lbrace>domain_fields P\<rbrace>"
  assumes arch_perform_invocation_domain_fields_invs[wp]:
    "\<And>P i. arch_perform_invocation i \<lbrace>domain_fields P\<rbrace>"
  assumes handle_reserved_irq_domain_fields_invs[wp]:
    "\<And>P irq. handle_reserved_irq irq \<lbrace>domain_fields P\<rbrace>"
  assumes arch_mask_irq_signal_domain_fields_invs[wp]:
    "\<And>P irq. arch_mask_irq_signal irq \<lbrace>domain_fields P\<rbrace>"
  assumes handle_spurious_irq_domain_fields_invs[wp]:
    "\<And>P. handle_spurious_irq \<lbrace>domain_fields P\<rbrace>"
  assumes handle_spurious_irq_scheduler_action[wp]:
    "\<And>P. handle_spurious_irq \<lbrace>\<lambda>s::det_state. P (scheduler_action s)\<rbrace>"

context DetSchedDomainTime_AI begin

crunch
  cap_swap_for_delete, empty_slot, get_object, get_cap, tcb_sched_action
  for domain_fields_invs[wp]: "domain_fields P"

crunch reply_unlink_tcb, reply_unlink_sc, tcb_sched_action
  for domain_list_inv[wp]:  "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps maybeM_inv select_inv gets_the_inv simp: crunch_simps set_object_def)

crunch reply_remove, sched_context_unbind_tcb, sched_context_set_inactive
  for domain_list_inv[wp]:  "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps get_simple_ko_wp)

crunch cancel_all_ipc, cancel_all_signals
  for domain_list_inv[wp]: "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps mapM_x_wp' whileLoop_valid_inv)

crunch finalise_cap
  for domain_fields_invs[wp]: "domain_fields P"
  (wp: crunch_wps maybeM_inv dxo_wp_weak select_inv simp: crunch_simps)

lemma rec_del_dlist_fields_invs[wp]:
  "rec_del call \<lbrace>dlist_fields P\<rbrace>"
  by (wp rec_del_preservation preemption_point_inv' | simp)+

crunch cap_delete, activate_thread
  for domain_fields_invs[wp]: "dlist_fields P"
  (wp: hoare_drop_imp)

crunch awaken, commit_time, refill_new, refill_update, set_next_interrupt, switch_sched_context,
  sc_and_timer, check_domain_time
  for domain_fields_invs[wp]: "domain_fields P"
  (wp: crunch_wps simp: crunch_simps)

crunch schedule
  for domain_list_invs[wp]: "\<lambda>s::det_state. P (domain_list s)"
  and domain_start_index_inv[wp]: "\<lambda>s::det_state. P (domain_start_index s)"
  (wp: hoare_drop_imp dxo_wp_weak whileLoop_valid_inv simp: Let_def)

crunch send_signal
 for dlist_fields_inv[wp]: "dlist_fields P"
  (wp: maybeM_inv crunch_wps)

end

crunch (in DetSchedDomainTime_AI_2) handle_interrupt
  for dlist_fields_inv[wp]: "dlist_fields P"

crunch cap_insert, lookup_cap_and_slot, set_extra_badge
  for domain_fields_invs[wp]: "domain_fields P"
  (wp: hoare_drop_imps)

crunch postpone
  for domain_list_inv[wp]: "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps mapM_wp)

context DetSchedDomainTime_AI begin

crunch do_ipc_transfer
  for domain_fields_invs[wp]: "domain_fields P"
  (wp: crunch_wps transfer_caps_loop_pres simp: zipWithM_x_mapM ignore: transfer_caps_loop)

lemma reply_push_domain_list_inv[wp]:
  "\<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> reply_push param_a param_b param_c param_d \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  by (wpsimp simp: reply_push_def bind_sc_reply_def split_del: if_split
    wp: hoare_vcg_if_lift2 hoare_vcg_all_lift hoare_drop_imp get_sched_context_wp)

crunch tcb_ep_append, tcb_ntfn_append, tcb_ep_dequeue, tcb_ntfn_dequeue
  for domain_list[wp]: "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps)

lemma send_ipc_domain_list_inv[wp]:
  "\<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace>
   send_ipc block call badge can_grant can_reply_grant can_donate thread epptr
   \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  by (wpsimp simp: send_ipc_def send_ipc_blocked_def wp: hoare_drop_imp hoare_vcg_all_lift)

lemma send_fault_ipc_domain_list_inv[wp]:
 "\<lbrace>\<lambda>s::det_state. P (domain_list s)\<rbrace> send_fault_ipc param_a param_b param_c param_d \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  by (wpsimp simp: send_fault_ipc_def wp: hoare_drop_imp hoare_vcg_all_lift)

crunch handle_fault
  for domain_fields_invs[wp]: "domain_fields P"
  (wp: mapM_wp hoare_drop_imps maybeM_inv dxo_wp_weak simp: crunch_simps ignore:copy_mrs)

crunch
  reply_from_kernel, create_cap, retype_region, do_reply_transfer
  for domain_fields_invs[wp]: "domain_fields P"
  (wp: hoare_drop_imps maybeM_inv dxo_wp_weak mapM_wp)

end

crunch delete_objects
  for domain_fields_invs[wp]: "domain_fields P"
  (simp: detype_def)

crunch preemption_point, reset_untyped_cap
  for dlist_fields_invs[wp]: "dlist_fields P"
  (wp: crunch_wps mapME_x_inv_wp OR_choiceE_weak_wp simp: ignore_del: preemption_point)

crunch
  set_priority, restart, sched_context_bind_tcb,sched_context_bind_ntfn,
  sched_context_unbind_reply, sched_context_yield_to
  for domain_list_inv[wp]: "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps mapM_wp' maybeM_inv whileLoop_valid_inv simp: crunch_simps)

context DetSchedDomainTime_AI begin

crunch refill_budget_check,charge_budget, check_budget
  for dlist_fields_invs[wp]: "dlist_fields P"
  (wp: crunch_wps)

crunch invoke_untyped
  for dlist_fields_invs[wp]: "dlist_fields P"
  (wp: crunch_wps
   simp: crunch_simps mapM_x_defsym)

crunch invoke_tcb, invoke_set_domain, invoke_irq_control, invoke_irq_handler
  for dlist_fields_invs[wp]: "dlist_fields P"
  (wp: crunch_wps check_cap_inv maybeM_inv case_options_weak_wp)

crunch invoke_sched_control_configure_flags, invoke_sched_context
  for domain_fields_invs[wp]: "domain_fields P"
  (wp: crunch_wps simp: crunch_simps)

end

crunch cap_move
  for domain_fields_invs[wp]: "domain_fields P"

context DetSchedDomainTime_AI begin

lemma cap_revoke_dlist_fields_invs[wp]:
  "cap_revoke a \<lbrace>dlist_fields P\<rbrace>"
  by (rule cap_revoke_preservation2)
     (wp preemption_point_inv'|simp)+

end

crunch cancel_badged_sends
  for domain_fields_invs[wp]: "domain_fields P"
  (ignore: filterM clearMemory
     simp: filterM_mapM crunch_simps
       wp: crunch_wps)

crunch maybe_donate_sc
 for domain_list[wp]: "\<lambda>s :: det_state. P (domain_list s)"
  (wp: crunch_wps)

crunch send_signal
 for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"
  (wp: hoare_drop_imps mapM_x_wp_inv maybeM_inv simp: crunch_simps unless_def)

crunch lookup_reply,lookup_cap
 for domain_list_inv[wp]: "\<lambda>s::det_state. P (domain_list s)"

context DetSchedDomainTime_AI_2 begin

lemma handle_spurious_irq_valid_domain[wp]:
  "handle_spurious_irq \<lbrace>\<lambda>s::det_state. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread \<rbrace>"
  by (wp | wps)+

lemma invoke_cnode_dlist_fields_invs[wp]:
  "invoke_cnode i \<lbrace>dlist_fields P\<rbrace>"
  by (wpsimp wp: crunch_wps cap_move_src_slot_Null hoare_drop_imps hoare_vcg_all_lift
             simp: invoke_cnode_def crunch_simps
             split_del: if_split)

crunch handle_recv, handle_yield, handle_vm_fault, check_domain_time
  for domain_fields_invs[wp]: "domain_fields P"
  (simp: crunch_simps wp: crunch_wps hoare_vcg_all_lift)

crunch maybe_handle_interrupt
  for dlist_fields_invs[wp]: "dlist_fields P"
  (wp: crunch_wps simp: crunch_simps)

lemma domain_set_start_valid_domain_list_inv[wp]:
  "\<lbrace>valid_domain_list and valid_domain_inv (InvokeDomainScheduleSetStart start)\<rbrace>
   domain_set_start start
   \<lbrace>\<lambda>_ s::det_state. valid_domain_list s\<rbrace>"
  unfolding domain_set_start_def
  apply (wpsimp wp: valid_domain_list_lift[of reschedule_required])
  apply (fastforce simp add: valid_domain_inv_def valid_domain_list_def domain_end_marker_def)
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
   perform_invocation block call can_donate iv
   \<lbrace>\<lambda>_ s::det_state. valid_domain_list s\<rbrace>"
  by (cases iv; (wpsimp | wp valid_domain_list_lift)+)


lemma handle_invocation_valid_domain_list_inv[wp]:
  "\<lbrace>valid_domain_list and invs\<rbrace>
   handle_invocation calling blocking can_donate first_phase cptr
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
       fastforce
qed


crunch preemption_path
  for domain_list[wp]: "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps simp: crunch_simps)

crunch handle_call, handle_send
  for valid_domain_list_inv[wp]: "\<lambda>s::det_state. valid_domain_list s"

crunch check_budget_restart
 for valid_domain_list[wp]: "valid_domain_list :: det_state \<Rightarrow> _"

lemma handle_event_valid_domain_list[wp]:
  "\<lbrace>valid_domain_list and invs\<rbrace>
   handle_event e
   \<lbrace>\<lambda>_ s::det_state. valid_domain_list s\<rbrace>"
  by (cases e; simp add: whenE_def; wpsimp wp: hoare_drop_imps)

lemma next_domain_valid_domain_list[wp]:
  "next_domain \<lbrace>\<lambda>s::det_state. valid_domain_list s\<rbrace>"
  unfolding next_domain_def
  apply (wpsimp wp: dxo_wp_weak)
  apply (clarsimp simp: valid_domain_list_def Let_def domain_end_marker_def)
  using less_Suc_eq
  apply fastforce
  done

crunch schedule, preemption_path
  for valid_domain_list[wp]: "\<lambda>s::det_state. valid_domain_list s"
  (wp: crunch_wps)

lemma call_kernel_domain_list_inv_det_ext:
  "\<lbrace>valid_domain_list and invs\<rbrace>
   (call_kernel e) :: (unit,det_ext) s_monad
   \<lbrace>\<lambda>_. valid_domain_list\<rbrace>"
  unfolding call_kernel_def
  by wpsimp

end


section \<open>Preservation of domain time remaining.\<close>

text \<open> When numDomains = 1, the domain scheduler is not in use, and the notion of the domain time
       does not hold any significance. Therefore, many of our results on the domain time are stated
       only in the case where 1 < numDomains. \<close>

lemma check_domain_time_domain_time_zero_imp_sched_act_choose_new_thread[wp]:
  "\<lbrace>\<top>\<rbrace>
   check_domain_time
   \<lbrace>\<lambda>_ s :: det_state. domain_time s = 0 \<and> 1 < numDomains \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  apply (clarsimp simp: check_domain_time_def reschedule_required_def set_scheduler_action_def)
  apply wpsimp
  apply (clarsimp simp: is_cur_domain_expired_def)
  done

crunch set_next_interrupt
  for domain_time_inv[wp]: "\<lambda>s. P (domain_time s) (scheduler_action s)"
  (wp: hoare_drop_imps)

crunch switch_sched_context, sc_and_timer
  for domain_time_inv[wp]: "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps)

lemma next_domain_domain_time_left[wp]:
  "\<lbrace>valid_domain_list\<rbrace> next_domain \<lbrace>\<lambda>_ s. 0 < domain_time s \<rbrace>"
  unfolding next_domain_def Let_def
  apply (wpsimp wp: dxo_wp_weak)
  apply (clarsimp simp: valid_domain_list_def all_set_conv_all_nth word_greater_zero_iff
                         ucast_eq_0 is_up domain_end_marker_def not_le)
  apply (rule conjI)
   apply fastforce
  apply (metis (mono_tags, lifting) less_imp_diff_less linorder_neqE_nat not_less_eq prod.simps(2)
                                    surjective_pairing)
  done

context DetSchedDomainTime_AI begin

crunch choose_thread
  for domain_time_inv[wp]: "\<lambda>s :: det_state. P (domain_time s)"
  (wp: crunch_wps)

lemma schedule_choose_new_thread_domain_time_left[wp]:
  "\<lbrace>valid_domain_list\<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_ s::det_state. 0 < domain_time s \<rbrace>"
  unfolding schedule_choose_new_thread_def
  by (wpsimp simp: word_gt_0 wp: valid_domain_list_lift)

lemma schedule_domain_time_left:
  "\<lbrace>valid_domain_list\<rbrace>
   schedule
   \<lbrace>\<lambda>_ s::det_state. Suc 0 < numDomains \<longrightarrow> 0 < domain_time s \<rbrace>"
  supply word_neq_0_conv[simp]
  apply (simp add: schedule_def)
  apply (rule bind_wp_fwd_skip, wpsimp)
  apply (rule_tac Q'="\<lambda>_ s. (domain_time s = 0 \<and> 1 < numDomains \<longrightarrow> scheduler_action s = choose_new_thread)
                           \<and> valid_domain_list s"
                in bind_wp_fwd)
   apply wpsimp
  apply (rule bind_wp[OF _ gets_sp])
  apply (rule bind_wp[OF _ gets_sp])
  apply (rule bind_wp[OF _  gets_sp], rename_tac action)
  apply (case_tac action; wpsimp wp: hoare_vcg_const_imp_lift hoare_drop_imps)
  done

end (* context DetSchedDomainTime_AI *)

(* FIXME: move to where hoare_drop_imp is, add E/R variants etc *)
lemma hoare_false_imp:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. \<not> R r s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. R r s \<longrightarrow> Q r s\<rbrace>"
  by (auto simp: valid_def)

context DetSchedDomainTime_AI_2 begin

crunch activate_thread
  for domain_time_inv[wp]: "\<lambda>s :: det_state. P (domain_time s)"
  (wp: crunch_wps simp: crunch_simps)

lemma call_kernel_domain_time_inv_det_ext:
  "\<lbrace>valid_domain_list and invs\<rbrace>
   call_kernel e
   \<lbrace>\<lambda>_ s :: det_state. Suc 0 < numDomains \<longrightarrow> 0 < domain_time s\<rbrace>"
  unfolding call_kernel_def
  apply (cases "e = Interrupt"; clarsimp)
   apply (wpsimp wp: schedule_domain_time_left)
  apply (rule_tac Q'="\<lambda>_. valid_domain_list" in bind_wp_fwd)
   apply wpsimp
  apply (wp schedule_domain_time_left without_preemption_wp)
  done

end

end
