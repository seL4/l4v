(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDetSchedSchedule_AI
imports DetSchedSchedule_AI
begin

context Arch begin global_naming ARM

named_theorems DetSchedSchedule_AI_assms

crunch arch_mask_irq_signal
  for valid_sched[wp, DetSchedSchedule_AI_assms]: valid_sched

crunch
  prepare_thread_delete
  for prepare_thread_delete_idle_thread[wp, DetSchedSchedule_AI_assms]: "\<lambda>(s:: det_ext state). P (idle_thread s)"

crunch
  arch_switch_to_idle_thread, arch_switch_to_thread, arch_get_sanitise_register_info, arch_post_modify_registers
  for valid_etcbs[wp, DetSchedSchedule_AI_assms]: valid_etcbs
  (simp: crunch_simps ignore: clearExMonitor)

crunch
  switch_to_idle_thread, switch_to_thread, set_vm_root, arch_get_sanitise_register_info, arch_post_modify_registers
  for valid_queues[wp, DetSchedSchedule_AI_assms]: valid_queues
  (simp: crunch_simps ignore: set_tcb_queue tcb_sched_action clearExMonitor)

crunch
  switch_to_idle_thread, switch_to_thread, set_vm_root, arch_get_sanitise_register_info, arch_post_modify_registers
  for weak_valid_sched_action[wp, DetSchedSchedule_AI_assms]: "weak_valid_sched_action"
  (simp: crunch_simps ignore: clearExMonitor)

crunch set_vm_root
  for ct_not_in_q[wp]: "ct_not_in_q"
  (wp: crunch_wps simp: crunch_simps)

crunch set_vm_root
  for ct_not_in_q'[wp]: "\<lambda>s. ct_not_in_q_2 (ready_queues s) (scheduler_action s) t"
  (wp: crunch_wps simp: crunch_simps)

lemma switch_to_idle_thread_ct_not_in_q [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_queues and valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: switch_to_idle_thread_def)
  apply wp
   apply (simp add: arch_switch_to_idle_thread_def)
   apply wp+
  apply (fastforce simp: valid_queues_def ct_not_in_q_def not_queued_def
                         valid_idle_def pred_tcb_at_def obj_at_def)
  done

crunch set_vm_root
  for valid_sched_action'[wp]: "\<lambda>s. valid_sched_action_2 (scheduler_action s)
                                                 (ekheap s) (kheap s) thread (cur_domain s)"
  (wp: crunch_wps simp: crunch_simps)

lemma switch_to_idle_thread_valid_sched_action [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_sched_action and valid_idle\<rbrace>
     switch_to_idle_thread
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: switch_to_idle_thread_def)
  apply wp
   apply (simp add: arch_switch_to_idle_thread_def do_machine_op_def split_def)
   apply wp+
  apply (clarsimp simp: valid_sched_action_def valid_idle_def is_activatable_def
                        pred_tcb_at_def obj_at_def)
  done

crunch set_vm_root
  for ct_in_cur_domain'[wp]: "\<lambda>s. ct_in_cur_domain_2 t (idle_thread s)
                                                   (scheduler_action s) (cur_domain s) (ekheap s)"
  (wp: crunch_wps simp: crunch_simps)

lemma switch_to_idle_thread_ct_in_cur_domain [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  by (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def do_machine_op_def
                split_def
      | wp
      | simp add: ct_in_cur_domain_def)+

crunch arch_switch_to_thread, arch_get_sanitise_register_info, arch_post_modify_registers
  for ct_not_in_q[wp, DetSchedSchedule_AI_assms]: ct_not_in_q
  (simp: crunch_simps ignore: clearExMonitor)

crunch arch_switch_to_thread, arch_get_sanitise_register_info, arch_post_modify_registers
  for is_activatable[wp, DetSchedSchedule_AI_assms]: "is_activatable t"
  (simp: crunch_simps ignore: clearExMonitor)

crunch arch_switch_to_thread, arch_get_sanitise_register_info, arch_post_modify_registers
  for valid_sched_action[wp, DetSchedSchedule_AI_assms]: valid_sched_action
  (simp: crunch_simps ignore: clearExMonitor)

crunch arch_switch_to_thread, arch_get_sanitise_register_info, arch_post_modify_registers
  for valid_sched[wp, DetSchedSchedule_AI_assms]: valid_sched
  (simp: crunch_simps ignore: clearExMonitor)

crunch set_vm_root
  for exst[wp]: "\<lambda>s. P (exst s)"
  (wp: crunch_wps whenE_wp simp: crunch_simps)

crunch arch_switch_to_thread
  for ct_in_cur_domain_2[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (ekheap s)"
  (simp: crunch_simps)

crunch set_vm_root
  for valid_blocked[wp]: valid_blocked
  (simp: crunch_simps)

crunch set_vm_root
  for ct_in_q[wp]: ct_in_q
  (simp: crunch_simps)

crunch switch_to_thread
  for etcb_at[wp, DetSchedSchedule_AI_assms]: "etcb_at P t"

crunch
  arch_switch_to_idle_thread
  for valid_idle[wp, DetSchedSchedule_AI_assms]: "valid_idle"
  (wp: crunch_wps simp: crunch_simps)

crunch arch_switch_to_idle_thread
  for etcb_at[wp, DetSchedSchedule_AI_assms]: "etcb_at P t"

crunch
  arch_switch_to_idle_thread, next_domain
  for scheduler_action[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (scheduler_action s)"
  (simp: Let_def)

lemma set_vm_root_valid_blocked_ct_in_q [wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> set_vm_root p \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  by (wp | wpc | auto)+

lemma arch_switch_to_thread_valid_blocked [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> arch_switch_to_thread thread \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply (rule bind_wp)+
   apply (rule do_machine_op_valid_blocked)
  apply wp
  done

lemma switch_to_idle_thread_ct_not_queued [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_queues and valid_etcbs and valid_idle\<rbrace>
     switch_to_idle_thread
   \<lbrace>\<lambda>rv s. not_queued (cur_thread s) s\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def
                   tcb_sched_action_def | wp)+
  apply (fastforce simp: valid_sched_2_def valid_queues_2_def valid_idle_def
                         pred_tcb_at_def obj_at_def not_queued_def)
  done

crunch set_vm_root
  for valid_blocked_2[wp]: "\<lambda>s.
           valid_blocked_2 (ready_queues s) (kheap s)
            (scheduler_action s) thread"
  (wp: crunch_wps simp: crunch_simps)

lemma switch_to_idle_thread_valid_blocked [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def do_machine_op_def | wp | wpc)+
  apply clarsimp
  apply (drule(1) ct_in_q_valid_blocked_ct_upd)
  apply simp
  done

crunch arch_switch_to_thread
  for exst[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (exst s :: det_ext)"
  (ignore: clearExMonitor)

crunch arch_switch_to_idle_thread
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"

lemma astit_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (simp add: arch_switch_to_idle_thread_def)
  by (wpsimp)

lemma stit_activatable' [DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv . ct_in_state activatable\<rbrace>"
  apply (simp add: switch_to_idle_thread_def ct_in_state_def do_machine_op_def split_def)
  apply wpsimp
  apply (clarsimp simp: valid_idle_def ct_in_state_def pred_tcb_at_def obj_at_def)
  done

crunch set_vm_root
  for it[wp]: "\<lambda>s. P (idle_thread s)"
  (simp: crunch_simps)

lemma switch_to_idle_thread_cur_thread_idle_thread [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_ s. cur_thread s = idle_thread s\<rbrace>"
  by (wp | simp add:switch_to_idle_thread_def arch_switch_to_idle_thread_def)+

lemma set_pd_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_pd ptr pd \<lbrace>\<lambda>rv. valid_etcbs\<rbrace>"
  by (wp hoare_drop_imps valid_etcbs_lift | simp add: set_pd_def)+

lemma set_pt_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_pt ptr pt \<lbrace>\<lambda>rv. valid_etcbs\<rbrace>"
  by (wp hoare_drop_imps valid_etcbs_lift | simp add: set_pt_def)+

lemma set_asid_pool_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_asid_pool ptr pool \<lbrace>\<lambda>rv. valid_etcbs\<rbrace>"
  by (wp hoare_drop_imps valid_etcbs_lift | simp add: set_asid_pool_def)+

lemma set_pt_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_pt ptr pt \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: set_pt_def)+

lemma set_pd_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_pd ptr pd \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: set_pd_def)+

lemma set_asid_pool_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_asid_pool ptr pool \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: set_asid_pool_def)+

crunch
  arch_finalise_cap, prepare_thread_delete
  for ct_not_in_q[wp, DetSchedSchedule_AI_assms]: ct_not_in_q
  (wp: crunch_wps hoare_drop_imps unless_wp select_inv mapM_wp
       subset_refl if_fun_split simp: crunch_simps ignore: tcb_sched_action)

crunch
  arch_finalise_cap, prepare_thread_delete
  for valid_etcbs[wp, DetSchedSchedule_AI_assms]: valid_etcbs
  (wp: hoare_drop_imps unless_wp select_inv mapM_x_wp mapM_wp subset_refl
       if_fun_split simp: crunch_simps ignore: set_object thread_set)

crunch
  arch_finalise_cap, prepare_thread_delete
  for simple_sched_action[wp, DetSchedSchedule_AI_assms]: simple_sched_action
  (wp: hoare_drop_imps mapM_x_wp mapM_wp subset_refl
   simp: unless_def if_fun_split)

crunch arch_finalise_cap, prepare_thread_delete, arch_invoke_irq_handler
  for valid_sched [wp, DetSchedSchedule_AI_assms]: valid_sched
  (ignore: set_object wp: crunch_wps subset_refl simp: if_fun_split)

lemma activate_thread_valid_sched [DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_sched\<rbrace> activate_thread \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: activate_thread_def)
  apply (wp set_thread_state_runnable_valid_sched gts_wp | wpc | simp add: arch_activate_idle_thread_def)+
  apply (force elim: st_tcb_weakenE)
  done

crunch
  perform_page_invocation, perform_page_table_invocation, perform_asid_pool_invocation,
  perform_page_directory_invocation
  for valid_sched[wp]: valid_sched
  (wp: mapM_x_wp' mapM_wp')

lemma arch_perform_invocation_valid_sched [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>invs and valid_sched and ct_active and valid_arch_inv a\<rbrace>
     arch_perform_invocation a
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (cases a, simp_all add: arch_perform_invocation_def)
     apply (wp perform_asid_control_invocation_valid_sched | wpc |
            simp add: valid_arch_inv_def invs_valid_idle)+
  done

crunch
  handle_arch_fault_reply, handle_vm_fault
  for valid_sched[wp, DetSchedSchedule_AI_assms]: valid_sched
  (ignore: getFAR getDFSR getIFSR)

crunch
  handle_vm_fault, handle_arch_fault_reply
  for not_queued[wp, DetSchedSchedule_AI_assms]: "not_queued t"
  (ignore: getFAR getDFSR getIFSR)

crunch
  handle_arch_fault_reply, handle_vm_fault
  for sched_act_not[wp, DetSchedSchedule_AI_assms]: "scheduler_act_not t"
  (ignore: getFAR getDFSR getIFSR)

lemma hvmf_st_tcb_at [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>st_tcb_at P t' \<rbrace> handle_vm_fault t w \<lbrace>\<lambda>rv. st_tcb_at P t' \<rbrace>"
  by (cases w, simp_all) ((wp | simp)+)

lemma handle_vm_fault_st_tcb_cur_thread [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace> \<lambda>s. st_tcb_at P (cur_thread s) s \<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_ s. st_tcb_at P (cur_thread s) s \<rbrace>"
  apply (fold ct_in_state_def)
  apply (rule ct_in_state_thread_state_lift)
   apply (cases f)
    apply (wp|simp)+
  done

crunch arch_invoke_irq_control
  for valid_sched[wp, DetSchedSchedule_AI_assms]: "valid_sched"

crunch
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread
  for valid_list[wp, DetSchedSchedule_AI_assms]: "valid_list"

crunch handle_arch_fault_reply, handle_vm_fault, arch_get_sanitise_register_info, arch_post_modify_registers
  for cur_tcb[wp, DetSchedSchedule_AI_assms]: cur_tcb

crunch arch_get_sanitise_register_info, arch_post_modify_registers
  for not_cur_thread[wp, DetSchedSchedule_AI_assms]: "not_cur_thread t'"
crunch arch_get_sanitise_register_info, arch_post_modify_registers
  for ready_queues[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (ready_queues s)"
crunch arch_get_sanitise_register_info, arch_post_modify_registers
  for scheduler_action[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (scheduler_action s)"
declare make_arch_fault_msg_inv[DetSchedSchedule_AI_assms]

lemma arch_post_modify_registers_not_idle_thread[DetSchedSchedule_AI_assms]:
  "\<lbrace>\<lambda>s::det_ext state. t \<noteq> idle_thread s\<rbrace> arch_post_modify_registers c t \<lbrace>\<lambda>_ s. t \<noteq> idle_thread s\<rbrace>"
  by (wpsimp simp: arch_post_modify_registers_def)

crunch arch_post_cap_deletion
  for valid_sched[wp, DetSchedSchedule_AI_assms]: valid_sched
  and valid_etcbs[wp, DetSchedSchedule_AI_assms]: valid_etcbs
  and ct_not_in_q[wp, DetSchedSchedule_AI_assms]: ct_not_in_q
  and simple_sched_action[wp, DetSchedSchedule_AI_assms]: simple_sched_action
  and not_cur_thread[wp, DetSchedSchedule_AI_assms]: "not_cur_thread t"
  and is_etcb_at[wp, DetSchedSchedule_AI_assms]: "is_etcb_at t"
  and not_queued[wp, DetSchedSchedule_AI_assms]: "not_queued t"
  and sched_act_not[wp, DetSchedSchedule_AI_assms]: "scheduler_act_not t"
  and weak_valid_sched_action[wp, DetSchedSchedule_AI_assms]: weak_valid_sched_action

crunch flush_space, invalidate_asid_entry, get_asid_pool
  for idle_thread[wp]: "\<lambda>s. P (idle_thread s)"

crunch flush_space, invalidate_asid_entry
  for valid_idle[wp]: "valid_idle"
  (wp: crunch_wps simp:crunch_simps)

crunch
  delete_asid_pool
  for delete_asid_pool[wp]: "\<lambda>(s:: det_ext state). P (idle_thread s)"
  (wp: crunch_wps simp: if_apply_def2)

crunch
  finalise_cap
  for idle_thread[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas[DetSchedSchedule_AI_assms] = arch_post_cap_deletion_valid_idle

crunch cap_swap_for_delete, cap_move, cancel_badged_sends
  for idle_thread[wp]: "\<lambda>s::'a::state_ext state. P (idle_thread s)"
  (wp: syscall_valid crunch_wps rec_del_preservation cap_revoke_preservation modify_wp dxo_wp_weak
   simp: crunch_simps check_cap_at_def filterM_mapM unless_def
   ignore: without_preemption filterM rec_del check_cap_at cap_revoke)

end

global_interpretation DetSchedSchedule_AI?: DetSchedSchedule_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedSchedule_AI_assms)?)
  qed

context Arch begin global_naming ARM

lemma handle_hyp_fault_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and st_tcb_at active t and not_queued t and scheduler_act_not t
      and (ct_active or ct_idle)\<rbrace>
    handle_hypervisor_fault t fault \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (cases fault; wpsimp wp: handle_fault_valid_sched simp: valid_fault_def)

lemma handle_reserved_irq_valid_sched:
  "\<lbrace>valid_sched and invs and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow>  scheduler_act_sane s \<and> ct_not_queued s)\<rbrace>
  handle_reserved_irq irq \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding handle_reserved_irq_def by (wpsimp simp: non_kernel_IRQs_def)

end

global_interpretation DetSchedSchedule_AI_handle_hypervisor_fault?: DetSchedSchedule_AI_handle_hypervisor_fault
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact handle_hyp_fault_valid_sched handle_reserved_irq_valid_sched)?)
  qed

end
