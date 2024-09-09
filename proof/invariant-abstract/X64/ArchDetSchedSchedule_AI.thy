(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDetSchedSchedule_AI
imports DetSchedSchedule_AI
begin

context Arch begin arch_global_naming

named_theorems DetSchedSchedule_AI_assms

crunch
  prepare_thread_delete
  for prepare_thread_delete_idel_thread[wp, DetSchedSchedule_AI_assms]: "\<lambda>(s:: det_ext state). P (idle_thread s)"

crunch
  switch_to_idle_thread, switch_to_thread, arch_get_sanitise_register_info, arch_post_modify_registers,
  arch_prepare_next_domain
  for valid_queues[wp, DetSchedSchedule_AI_assms]: valid_queues
  (simp: crunch_simps wp: crunch_wps ignore: tcb_sched_action )

crunch
  switch_to_idle_thread, switch_to_thread, arch_get_sanitise_register_info, arch_post_modify_registers
  for weak_valid_sched_action[wp, DetSchedSchedule_AI_assms]: "weak_valid_sched_action"
  (simp: crunch_simps wp: crunch_wps)

crunch set_vm_root
  for ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and ct_not_in_q[wp]: "ct_not_in_q"
  and ct_not_in_q'[wp]: "\<lambda>s. ct_not_in_q_2 (ready_queues s) (scheduler_action s) t"
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
                                                 (etcbs_of s) (kheap s) thread (cur_domain s)"
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
                                                   (scheduler_action s) (cur_domain s) (etcbs_of s)"
  (wp: crunch_wps simp: crunch_simps)

lemma switch_to_idle_thread_ct_in_cur_domain [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  by (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def do_machine_op_def
                split_def
      | wp
      | simp add: ct_in_cur_domain_def)+

crunch
  arch_switch_to_thread, arch_get_sanitise_register_info
  for ct_not_in_q[wp, DetSchedSchedule_AI_assms]: ct_not_in_q
  (simp: crunch_simps wp: crunch_wps)

crunch
  arch_switch_to_thread, arch_get_sanitise_register_info
  for is_activatable[wp, DetSchedSchedule_AI_assms]: "is_activatable t"
  (simp: crunch_simps wp: crunch_wps)

crunch
  arch_switch_to_thread, arch_get_sanitise_register_info, arch_post_modify_registers
  for valid_sched_action[wp, DetSchedSchedule_AI_assms]: valid_sched_action
  (simp: crunch_simps wp: crunch_wps)

crunch
  arch_switch_to_thread, arch_get_sanitise_register_info, arch_post_modify_registers,
  arch_prepare_next_domain, arch_post_set_flags, arch_prepare_set_domain
  for valid_sched[wp, DetSchedSchedule_AI_assms]: valid_sched
  (simp: crunch_simps wp: crunch_wps)

crunch set_vm_root
  for exst[wp]: "\<lambda>s. P (exst s)"
  (wp: crunch_wps whenE_wp simp: crunch_simps)

lemma arch_thread_set_ct_in_cur_domain_2[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)\<rbrace>"
  apply (simp add: arch_thread_set_def set_object_def get_object_def)
  by wpsimp

crunch arch_switch_to_thread
  for ct_in_cur_domain_2[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)"
  (simp: whenE_def)

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
  for valid_idle[wp, DetSchedSchedule_AI_assms]: valid_idle
  (wp: crunch_wps simp: crunch_simps)

crunch arch_switch_to_idle_thread, arch_prepare_next_domain
  for etcb_at[wp, DetSchedSchedule_AI_assms]: "etcb_at P t"

crunch
  arch_prepare_next_domain, arch_prepare_set_domain
  for scheduler_action[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (scheduler_action s)"
  (simp: Let_def)

lemma as_user_ct_in_q[wp]:
  "as_user t f \<lbrace>ct_in_q\<rbrace>"
  unfolding ct_in_q_def
  by (wpsimp wp: hoare_vcg_imp_lift | wps)+

crunch arch_prepare_next_domain
  for ready_queues[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (ready_queues s)"
  and ct_in_q[wp, DetSchedSchedule_AI_assms]: ct_in_q
  and valid_blocked[wp, DetSchedSchedule_AI_assms]: valid_blocked
  (wp: crunch_wps)

crunch arch_prepare_set_domain
  for idle_thread[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (idle_thread s)"
  and valid_idle[wp, DetSchedSchedule_AI_assms]: valid_idle

lemma set_vm_root_valid_blocked_ct_in_q [wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> set_vm_root p \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  by (wp | wpc | auto)+

crunch lazy_fpu_restore
  for valid_blocked[wp]: valid_blocked
  and ct_in_q[wp]: ct_in_q

lemma arch_switch_to_thread_valid_blocked [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> arch_switch_to_thread thread \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  by (wpsimp simp: arch_switch_to_thread_def)

lemma switch_to_idle_thread_ct_not_queued [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_queues and valid_idle\<rbrace>
     switch_to_idle_thread
   \<lbrace>\<lambda>rv s. not_queued (cur_thread s) s\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def
                   tcb_sched_action_def | wp)+
  apply (fastforce simp: valid_sched_2_def valid_queues_2_def valid_idle_def
                         pred_tcb_at_def obj_at_def not_queued_def)
  done

crunch set_vm_root
  for valid_blocked_2[wp]: "\<lambda>s. valid_blocked_2 (ready_queues s) (kheap s) (scheduler_action s) thread"
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
  (ignore: )

crunch arch_switch_to_idle_thread
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"

crunch arch_switch_to_idle_thread
  for inv[wp]: "\<lambda>s. P"
  (wp: crunch_wps simp: crunch_simps)

lemma astit_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (simp add: arch_switch_to_idle_thread_def)
  by (wpsimp)

lemma stit_activatable' [DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv . ct_in_state activatable\<rbrace>"
  apply (simp add: switch_to_idle_thread_def do_machine_op_def split_def ct_in_state_def)
  apply wpsimp
  apply (clarsimp simp: valid_idle_def ct_in_state_def pred_tcb_at_def obj_at_def)
  done

crunch set_vm_root
  for it[wp]: "\<lambda>s. P (idle_thread s)"
  (simp: crunch_simps)

lemma switch_to_idle_thread_cur_thread_idle_thread [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_ s. cur_thread s = idle_thread s\<rbrace>"
  by (wp | simp add:switch_to_idle_thread_def arch_switch_to_idle_thread_def)+

lemma set_pt_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_pt ptr pt \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: set_pt_def)+

lemma set_pm_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_pml4 ptr pm \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp add: hoare_drop_imps valid_sched_lift del: set_pml4_typ_at | simp add: set_pml4_def)+

lemma set_pdpt_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_pdpt ptr pd \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp add: hoare_drop_imps valid_sched_lift del: set_pdpt_typ_at | simp add: set_pdpt_def)+

lemma set_pd_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_pd ptr pd \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp add: hoare_drop_imps valid_sched_lift del: set_pd_typ_at | simp add: set_pd_def)+

lemma set_asid_pool_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_asid_pool ptr pool \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: set_asid_pool_def)+

crunch set_object
  for ct_not_in_q[wp]: ct_not_in_q
  (wp: crunch_wps hoare_drop_imps unless_wp select_inv mapM_wp
       subset_refl if_fun_split simp: crunch_simps ignore: tcb_sched_action)

lemma flush_table_ct_not_in_q[wp]: "\<lbrace>ct_not_in_q\<rbrace> flush_table a b c d \<lbrace>\<lambda>rv. ct_not_in_q\<rbrace>"
  by (wp mapM_x_wp' | wpc | simp add: flush_table_def | rule hoare_pre)+

crunch
  arch_finalise_cap, prepare_thread_delete
  for ct_not_in_q[wp, DetSchedSchedule_AI_assms]: ct_not_in_q
  (wp: crunch_wps hoare_drop_imps unless_wp select_inv mapM_wp
       subset_refl if_fun_split simp: crunch_simps ignore: tcb_sched_action)

lemma flush_table_simple_sched_action[wp]: "\<lbrace>simple_sched_action\<rbrace> flush_table a b c d \<lbrace>\<lambda>rv. simple_sched_action\<rbrace>"
  by (wp mapM_x_wp' | wpc | simp add: flush_table_def | rule hoare_pre)+

crunch
  arch_finalise_cap, prepare_thread_delete
  for simple_sched_action[wp, DetSchedSchedule_AI_assms]: simple_sched_action
  (wp: hoare_drop_imps mapM_x_wp mapM_wp subset_refl crunch_wps
   simp: unless_def if_fun_split crunch_simps)

lemma flush_table_valid_sched[wp]: "\<lbrace>valid_sched\<rbrace> flush_table a b c d \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp mapM_x_wp' | wpc | simp add: flush_table_def | rule hoare_pre)+

lemma store_pte_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> store_pte pter pte \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: store_pte_def set_arch_obj_simps)+

lemma store_pm_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> store_pml4e pter pm \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp add: hoare_drop_imps valid_sched_lift del: store_pml4e_typ_at | simp add: store_pml4e_def)+

lemma store_pdepte_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> store_pdpte pter pd \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp add: hoare_drop_imps valid_sched_lift del: store_pdpte_typ_at
      | simp add: store_pdpte_def set_arch_obj_simps)+

lemma store_pde_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> store_pde pter pd \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp add: hoare_drop_imps valid_sched_lift del: store_pde_typ_at
      | simp add: store_pde_def set_arch_obj_simps)+

crunch
  arch_finalise_cap, prepare_thread_delete
  for valid_sched[wp, DetSchedSchedule_AI_assms]: valid_sched
  (ignore: set_object set_object wp: crunch_wps subset_refl simp: if_fun_split crunch_simps)

lemma activate_thread_valid_sched [DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_sched\<rbrace> activate_thread \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: activate_thread_def)
  apply (wp set_thread_state_runnable_valid_sched gts_wp | wpc | simp add: arch_activate_idle_thread_def)+
  apply (force elim: st_tcb_weakenE)
  done

lemma store_asid_pool_entry_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> store_asid_pool_entry ptr pool a \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: store_asid_pool_entry_def set_arch_obj_simps)+

crunch
  perform_page_invocation, perform_page_table_invocation, perform_asid_pool_invocation,
  perform_page_directory_invocation, perform_io_port_invocation, perform_pdpt_invocation,
  perform_ioport_control_invocation
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
  handle_arch_fault_reply, handle_vm_fault, arch_mask_irq_signal, arch_invoke_irq_handler
  for valid_sched[wp, DetSchedSchedule_AI_assms]: valid_sched
  (ignore: )

crunch
  handle_vm_fault, handle_arch_fault_reply
  for not_queued[wp, DetSchedSchedule_AI_assms]: "not_queued t"
  (ignore: )

crunch
  handle_arch_fault_reply, handle_vm_fault
  for sched_act_not[wp, DetSchedSchedule_AI_assms]: "scheduler_act_not t"
  (ignore: )

lemma hvmf_st_tcb_at [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>st_tcb_at P t' \<rbrace> handle_vm_fault t w \<lbrace>\<lambda>rv. st_tcb_at P t' \<rbrace>"
  unfolding handle_vm_fault_def by (cases w, simp_all) ((wp | simp)+)

lemma handle_vm_fault_st_tcb_cur_thread [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace> \<lambda>s. st_tcb_at P (cur_thread s) s \<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_ s. st_tcb_at P (cur_thread s) s \<rbrace>"
  unfolding handle_vm_fault_def
  apply (fold ct_in_state_def)
  apply (rule ct_in_state_thread_state_lift; cases f; wpsimp)
  done

crunch arch_invoke_irq_control
  for valid_sched[wp, DetSchedSchedule_AI_assms]: "valid_sched"

crunch
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread, arch_prepare_next_domain
  for valid_list[wp, DetSchedSchedule_AI_assms]: "valid_list"

crunch
  handle_arch_fault_reply, handle_vm_fault, arch_get_sanitise_register_info, arch_post_modify_registers
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
  and ct_not_in_q[wp, DetSchedSchedule_AI_assms]: ct_not_in_q
  and simple_sched_action[wp, DetSchedSchedule_AI_assms]: simple_sched_action
  and not_cur_thread[wp, DetSchedSchedule_AI_assms]: "not_cur_thread t"
  and not_queued[wp, DetSchedSchedule_AI_assms]: "not_queued t"
  and sched_act_not[wp, DetSchedSchedule_AI_assms]: "scheduler_act_not t"
  and weak_valid_sched_action[wp, DetSchedSchedule_AI_assms]: weak_valid_sched_action
  and valid_idle[wp, DetSchedSchedule_AI_assms]: valid_idle

lemma flush_table_idle_thread[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> flush_table param_a param_b param_c param_d \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  unfolding flush_table_def
  apply (wpsimp wp: mapM_x_wp')
  done

crunch
  delete_asid_pool, unmap_page
  for delete_asid_pool[wp]: "\<lambda>(s:: det_ext state). P (idle_thread s)"
  (wp: crunch_wps simp: if_apply_def2)

crunch
  arch_finalise_cap
  for idle_thread[wp, DetSchedSchedule_AI_assms]: "\<lambda> (s:: det_ext state). P (idle_thread s)"
  (wp: crunch_wps crunch_simps)

declare make_arch_fault_msg_invs[DetSchedSchedule_AI_assms]

crunch handle_spurious_irq
  for valid_sched[wp, DetSchedSchedule_AI_assms]: valid_sched
  and valid_idle[wp, DetSchedSchedule_AI_assms]: valid_idle

crunch arch_switch_to_thread
  for cur_domain[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (cur_domain s)"
  and etcbs_of[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (etcbs_of s)"

crunch prepare_thread_delete, arch_post_cap_deletion, arch_finalise_cap
  for cur_thread[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (cur_thread s)"
  and cur_domain[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (cur_domain s)"
  and etcbs_of[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (etcbs_of s)"
  (wp: mapM_x_wp_inv_weak crunch_wps simp: crunch_simps ignore: set_object)

end

global_interpretation DetSchedSchedule_AI?: DetSchedSchedule_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedSchedule_AI_assms)?)
  qed

context Arch begin arch_global_naming

lemma handle_hyp_fault_valid_sched[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_sched and invs and st_tcb_at active t and not_queued t and scheduler_act_not t
     and (ct_active or ct_idle)\<rbrace>
   handle_hypervisor_fault t fault \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (cases fault; wpsimp wp: handle_fault_valid_sched simp: valid_fault_def)

lemma handle_reserved_irq_valid_sched[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_sched and invs and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow>  scheduler_act_sane s \<and> ct_not_queued s)\<rbrace>
  handle_reserved_irq irq \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding handle_reserved_irq_def by (wpsimp simp: non_kernel_IRQs_def)

end

global_interpretation DetSchedSchedule_AI_handle_hypervisor_fault?: DetSchedSchedule_AI_handle_hypervisor_fault
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedSchedule_AI_assms)?)
  qed

end
