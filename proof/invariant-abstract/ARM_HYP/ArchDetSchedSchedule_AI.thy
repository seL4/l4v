(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDetSchedSchedule_AI
imports DetSchedSchedule_AI
begin

context Arch begin global_naming ARM_HYP

named_theorems DetSchedSchedule_AI_assms

crunch prepare_thread_delete_idle_thread[wp, DetSchedSchedule_AI_assms]:
  prepare_thread_delete "\<lambda>(s:: det_ext state). P (idle_thread s)"
  (wp: crunch_wps)

crunch exst[wp]: set_vcpu "\<lambda>s. P (exst s)" (wp: crunch_wps)

crunch exst[wp]: vcpu_disable,vcpu_restore,vcpu_save "\<lambda>s. P (exst s)"
  (wp: crunch_wps)

lemma vcpu_switch_exst[wp]:
  "\<lbrace>\<lambda>s. P (exst s)\<rbrace> vcpu_switch param_a \<lbrace>\<lambda>_ s. P (exst s)\<rbrace>"
  unfolding vcpu_switch_def by (rule hoare_pre) wpsimp+

crunch exst[wp]: switch_to_idle_thread,set_vm_root "\<lambda>s. P (exst s)"
  (simp: crunch_simps ignore: set_object do_machine_op wp: crunch_wps)

lemma set_vcpu_etcbs [wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_vcpu a b \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  by (rule valid_etcbs_lift; wp)

lemma vcpu_switch_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> vcpu_switch param_a \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  by (rule valid_etcbs_lift; wp)

crunch valid_etcbs [wp, DetSchedSchedule_AI_assms]:
  arch_switch_to_idle_thread, arch_switch_to_thread, vcpu_disable, vcpu_restore, vcpu_save, set_vm_root, arch_get_sanitise_register_info, arch_post_modify_registers
  valid_etcbs
  (simp: crunch_simps ignore: clearExMonitor set_object do_machine_op wp: crunch_wps)

lemma pred_tcb_atP[wp]:
  "\<lbrace>\<lambda>s. P (pred_tcb_at proj Q t s)\<rbrace> set_vcpu prt vcpu \<lbrace>\<lambda>_ s. P (pred_tcb_at proj Q t s)\<rbrace>"
  unfolding set_vcpu_def set_object_def
  apply (wp get_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def split: kernel_object.splits)
  done

crunch pred_tcb_atP[wp]: vcpu_disable, vcpu_enable, vcpu_restore, vcpu_save
  "\<lambda>s. P (pred_tcb_at proj Q t s)"
  (wp: crunch_wps simp: crunch_simps)

lemma vcpu_switch_pred_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (pred_tcb_at proj Q t s)\<rbrace> vcpu_switch vcpu \<lbrace>\<lambda>_ s. P (pred_tcb_at proj Q t s)\<rbrace>"
  unfolding vcpu_switch_def by (rule hoare_pre) wpsimp+

crunch pred_tcb_atP[wp]: set_vm_root "\<lambda>s. P (pred_tcb_at proj Q t s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_vcpu_valid_queues [wp]:
  "\<lbrace>valid_queues\<rbrace> set_vcpu ptr vcpu \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  by (rule valid_queues_lift; wp)

lemma vcpu_switch_valid_queues[wp]:
  "\<lbrace>valid_queues\<rbrace> vcpu_switch v \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  by (rule valid_queues_lift; wp)

crunch valid_queues[wp, DetSchedSchedule_AI_assms]:
  arch_switch_to_idle_thread, arch_switch_to_thread, vcpu_disable, vcpu_restore, vcpu_save, set_vm_root, arch_get_sanitise_register_info, arch_post_modify_registers
  valid_queues
  (simp: crunch_simps ignore: set_tcb_queue tcb_sched_action clearExMonitor wp: crunch_wps)

lemma set_vcpu_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace> set_vcpu ptr vcpu \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (rule weak_valid_sched_action_lift; wp)

lemma vcpu_switch_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace> vcpu_switch v \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (rule weak_valid_sched_action_lift; wp)

crunch weak_valid_sched_action[wp, DetSchedSchedule_AI_assms]:
  arch_switch_to_idle_thread, arch_switch_to_thread, vcpu_disable, vcpu_restore, vcpu_save, set_vm_root, arch_get_sanitise_register_info, arch_post_modify_registers
  weak_valid_sched_action
  (simp: crunch_simps wp: crunch_wps)

lemma switch_to_idle_thread_ct_not_in_q[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_queues and valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: switch_to_idle_thread_def)
  apply wp
   apply (simp add: arch_switch_to_idle_thread_def)
   apply wp+
  apply (fastforce simp: valid_queues_def ct_not_in_q_def not_queued_def
                         valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma vcpu_switch_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace> vcpu_switch v \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  unfolding valid_sched_action_def is_activatable_def st_tcb_at_kh_simp
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp wp: hoare_vcg_imp_lift)

lemma vcpu_switch_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> vcpu_switch v \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  unfolding valid_idle_def by (rule hoare_lift_Pf[where f=idle_thread]; wp)

lemma set_vm_root_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> set_vm_root v \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  unfolding valid_idle_def by (rule hoare_lift_Pf[where f=idle_thread]; wp)

lemma valid_sched_action_idle_strg:
  "thread = idle_thread s \<and> valid_sched_action s \<and> valid_idle s \<Longrightarrow>
   valid_sched_action (s\<lparr>cur_thread := thread\<rparr>)"
  by (auto simp: valid_sched_action_def is_activatable_def valid_idle_def pred_tcb_at_def obj_at_def)

crunch valid_sched_action[wp]: set_vm_root "valid_sched_action"
  (simp: crunch_simps wp: crunch_wps)

lemma switch_to_idle_thread_valid_sched_action[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_sched_action and valid_idle\<rbrace>
     switch_to_idle_thread
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def)
  apply (wp | strengthen valid_sched_action_idle_strg)+
  apply simp
  done

lemma switch_to_idle_thread_ct_in_cur_domain[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  by (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def ct_in_cur_domain_def
       | wp hoare_vcg_imp_lift hoare_vcg_disj_lift)+

lemma set_vm_root_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> set_vm_root param_a \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (rule ct_not_in_q_lift; wp)

lemma do_machine_op_activatable[wp]:
  "\<lbrace>is_activatable t\<rbrace> do_machine_op oper \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  unfolding do_machine_op_def by wpsimp

lemma set_vcpu_is_activatable[wp]:
  "\<lbrace>is_activatable t\<rbrace> set_vcpu ptr vcpu \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  unfolding is_activatable_def set_vcpu_def set_object_def
  apply (wp get_object_wp)
  apply (clarsimp simp: st_tcb_at_kh_def obj_at_kh_def obj_at_def)
  done

crunches vcpu_disable, vcpu_restore, vcpu_save, vcpu_switch, set_vm_root
  for is_activatable[wp]: "is_activatable t"
  and valid_sched[wp, DetSchedSchedule_AI_assms]: valid_sched
  (wp: crunch_wps valid_sched_lift simp: crunch_simps)

crunches arch_switch_to_thread, arch_get_sanitise_register_info, arch_post_modify_registers
  for ct_not_in_q[wp, DetSchedSchedule_AI_assms]: ct_not_in_q
  and is_activatable[wp, DetSchedSchedule_AI_assms]: "is_activatable t"
  and valid_sched_action[wp, DetSchedSchedule_AI_assms]: valid_sched_action
  and valid_sched[wp, DetSchedSchedule_AI_assms]: valid_sched
  (wp: crunch_wps valid_sched_lift simp: crunch_simps)

lemma set_vm_rootct_in_cur_domain_2[wp]:
  "\<lbrace>\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (ekheap s)\<rbrace>
    set_vm_root param_a
   \<lbrace>\<lambda>_ s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (ekheap s)\<rbrace>"
  apply (rule hoare_lift_Pf[where f="\<lambda>s. ekheap s", rotated], wp)
  apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_domain s", rotated], wp)
  apply (rule hoare_lift_Pf[where f="\<lambda>s. scheduler_action s", rotated], wp)
  apply (rule hoare_lift_Pf[where f="\<lambda>s. idle_thread s", rotated], wp)
  apply wp
  done

crunches arch_switch_to_thread
  for ct_in_cur_domain_2[wp, DetSchedSchedule_AI_assms]:
    "\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (ekheap s)"
  (wp: crunch_wps simp: crunch_simps)

lemma vcpu_switch_ct_in_q[wp]:
  "\<lbrace>ct_in_q\<rbrace> vcpu_switch vcpu \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  unfolding ct_in_q_def
  apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_thread s", rotated], wp)
  apply (rule hoare_lift_Pf[where f="\<lambda>s. ready_queues s", rotated], wp)
  apply wp
  done

crunches do_machine_op, set_vm_root, vcpu_switch
  for valid_blocked[wp]: valid_blocked
  and ct_in_q[wp]: ct_in_q
  (wp: valid_blocked_lift simp: crunch_simps)

lemma set_vm_root_valid_blocked_ct_in_q[wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> set_vm_root p \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  by wpsimp

lemma arch_switch_to_thread_valid_blocked[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> arch_switch_to_thread thread \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply (rule hoare_seq_ext)+
     apply (rule do_machine_op_valid_blocked)
    apply wpsimp+
  done

crunch etcb_at [wp, DetSchedSchedule_AI_assms]:
  arch_switch_to_thread, arch_switch_to_idle_thread "etcb_at P t"

crunch scheduler_action [wp, DetSchedSchedule_AI_assms]:
  arch_switch_to_idle_thread, next_domain "\<lambda>s. P (scheduler_action s)"
  (simp: Let_def)

lemma switch_to_idle_thread_ct_not_queued[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_queues and valid_etcbs and valid_idle\<rbrace>
     switch_to_idle_thread
   \<lbrace>\<lambda>rv s. not_queued (cur_thread s) s\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def
                   tcb_sched_action_def | wp)+
  apply (fastforce simp: valid_sched_2_def valid_queues_2_def valid_idle_def
                         pred_tcb_at_def obj_at_def not_queued_def)
  done

lemma valid_blocked_idle_strg:
  "thread = idle_thread s \<and> valid_blocked s \<and> ct_in_q s \<Longrightarrow> valid_blocked (s\<lparr>cur_thread := thread\<rparr>)"
  apply clarsimp
  apply (drule(1) ct_in_q_valid_blocked_ct_upd)
  apply simp
  done

lemma switch_to_idle_thread_valid_blocked[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  by (strengthen valid_blocked_idle_strg
       | simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def do_machine_op_def
       | wp | wpc )+

crunch exst[wp, DetSchedSchedule_AI_assms]: arch_switch_to_thread "\<lambda>s. P (exst s)"

crunch valid_idle [wp, DetSchedSchedule_AI_assms]:
  arch_switch_to_idle_thread "valid_idle :: det_ext state \<Rightarrow> bool"

lemma ct_in_state_cur_update[simp]:
  "ct_in_state P (s\<lparr>cur_thread := thread\<rparr>) = st_tcb_at P thread s"
  by (simp add: ct_in_state_def)

lemma stit_activatable' [DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv . ct_in_state activatable\<rbrace>"
  unfolding switch_to_idle_thread_def arch_switch_to_idle_thread_def
  apply wpsimp
  apply (clarsimp simp: valid_idle_def ct_in_state_def pred_tcb_at_def obj_at_def)
  done

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

crunch exst[wp]: arch_thread_set "\<lambda>s. P (exst s)"

crunch valid_etcbs[wp]: arch_thread_set valid_etcbs
  (wp: valid_etcbs_lift)

lemma set_pt_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_pt ptr pt \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: set_pt_def)+

lemma set_pd_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_pd ptr pd \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: set_pd_def)+

lemma set_asid_pool_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_asid_pool ptr pool \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: set_asid_pool_def)+

lemma set_vcpu_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_vcpu t vr \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (rule valid_sched_lift; wp)

crunch cur_thread[wp]: arch_thread_set "\<lambda>s. P (cur_thread s)"

lemma arch_thread_set_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> arch_thread_set f t \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (rule valid_sched_lift; wpsimp wp: arch_thread_set_pred_tcb_at)

crunch ct_not_in_q [wp, DetSchedSchedule_AI_assms]:
  arch_finalise_cap, prepare_thread_delete ct_not_in_q
  (wp: crunch_wps hoare_drop_imps unless_wp select_inv mapM_wp
       subset_refl if_fun_split simp: crunch_simps ignore: tcb_sched_action)

crunch valid_etcbs [wp, DetSchedSchedule_AI_assms]:
  arch_finalise_cap, prepare_thread_delete valid_etcbs
  (wp: hoare_drop_imps unless_wp select_inv mapM_x_wp mapM_wp subset_refl
       if_fun_split simp: crunch_simps ignore: set_object thread_set)

crunch simple_sched_action [wp, DetSchedSchedule_AI_assms]:
  arch_finalise_cap, prepare_thread_delete simple_sched_action
  (wp: hoare_drop_imps mapM_x_wp mapM_wp select_wp subset_refl
   simp: unless_def if_fun_split)

crunches arch_finalise_cap, prepare_thread_delete, arch_invoke_irq_handler
  for valid_sched [wp, DetSchedSchedule_AI_assms]: valid_sched
  (ignore: set_object wp: crunch_wps subset_refl simp: if_fun_split)

lemma activate_thread_valid_sched [DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_sched\<rbrace> activate_thread \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: activate_thread_def)
  apply (wp set_thread_state_runnable_valid_sched gts_wp | wpc | simp add: arch_activate_idle_thread_def)+
  apply (force elim: st_tcb_weakenE)
  done

crunch valid_sched[wp]:
  perform_page_invocation, perform_page_table_invocation, perform_asid_pool_invocation,
  perform_page_directory_invocation
  valid_sched
  (wp: crunch_wps)

crunches
  vcpu_read_reg,vcpu_write_reg,read_vcpu_register,write_vcpu_register,set_message_info,as_user
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and valid_sched[wp]: valid_sched
  and ct_in_state[wp]: "ct_in_state st"
  (simp: crunch_simps wp: ct_in_state_thread_state_lift)

lemma invoke_vcpu_read_register_valid_sched[wp]:
  "\<lbrace>valid_sched and ct_active\<rbrace> invoke_vcpu_read_register v reg \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding invoke_vcpu_read_register_def by (wpsimp wp: set_thread_state_Running_valid_sched)

lemma invoke_vcpu_write_register_valid_sched[wp]:
  "\<lbrace>valid_sched and ct_active\<rbrace> invoke_vcpu_write_register v reg val \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding invoke_vcpu_write_register_def by (wpsimp wp: set_thread_state_Restart_valid_sched)

crunch valid_sched[wp]: perform_vcpu_invocation valid_sched
  (wp: crunch_wps simp: crunch_simps ignore: set_thread_state)

lemma arch_perform_invocation_valid_sched[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>invs and valid_sched and ct_active and valid_arch_inv a\<rbrace>
     arch_perform_invocation a
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (cases a, simp_all add: arch_perform_invocation_def)
     apply (wp perform_asid_control_invocation_valid_sched | wpc |
            simp add: valid_arch_inv_def invs_valid_idle)+
  done

crunch valid_sched [wp, DetSchedSchedule_AI_assms]:
  handle_arch_fault_reply, handle_vm_fault valid_sched
  (ignore: getFAR getDFSR getIFSR)

crunch not_queued [wp, DetSchedSchedule_AI_assms]:
  handle_vm_fault, handle_arch_fault_reply "not_queued t"
  (ignore: getFAR getDFSR getIFSR)

crunch sched_act_not [wp, DetSchedSchedule_AI_assms]:
  handle_arch_fault_reply, handle_vm_fault "scheduler_act_not t"
  (ignore: getFAR getDFSR getIFSR)

lemma hvmf_st_tcb_at [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>st_tcb_at P t' \<rbrace> handle_vm_fault t w \<lbrace>\<lambda>rv. st_tcb_at P t' \<rbrace>"
  by (cases w, simp_all) ((wp | simp)+)

lemma handle_vm_fault_st_tcb_cur_thread[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace> \<lambda>s. st_tcb_at P (cur_thread s) s \<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_ s. st_tcb_at P (cur_thread s) s \<rbrace>"
  apply (fold ct_in_state_def)
  apply (rule ct_in_state_thread_state_lift)
   apply (cases f)
    apply (wp|simp)+
  done

crunch valid_sched [wp, DetSchedSchedule_AI_assms]: arch_invoke_irq_control "valid_sched"

crunch valid_list [wp, DetSchedSchedule_AI_assms]:
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread "valid_list"

crunch cur_tcb [wp, DetSchedSchedule_AI_assms]: handle_arch_fault_reply, handle_vm_fault, arch_get_sanitise_register_info, arch_post_modify_registers cur_tcb

crunch not_cur_thread [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg, arch_get_sanitise_register_info, arch_post_modify_registers "not_cur_thread t'"
crunch valid_sched    [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg, arch_mask_irq_signal valid_sched
crunch ready_queues   [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg, arch_get_sanitise_register_info, arch_post_modify_registers "\<lambda>s. P (ready_queues s)"
crunch valid_etcbs    [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg valid_etcbs
crunch scheduler_action [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg, arch_get_sanitise_register_info, arch_post_modify_registers "\<lambda>s. P (scheduler_action s)"
declare arch_switch_to_idle_thread_exst[DetSchedSchedule_AI_assms]

lemma arch_post_modify_registers_not_idle_thread[DetSchedSchedule_AI_assms]:
  "\<lbrace>\<lambda>s::det_ext state. t \<noteq> idle_thread s\<rbrace> arch_post_modify_registers c t \<lbrace>\<lambda>_ s. t \<noteq> idle_thread s\<rbrace>"
  by (wpsimp simp: arch_post_modify_registers_def)

crunches arch_post_cap_deletion
  for valid_sched[wp, DetSchedSchedule_AI_assms]: valid_sched
  and valid_etcbs[wp, DetSchedSchedule_AI_assms]: valid_etcbs
  and ct_not_in_q[wp, DetSchedSchedule_AI_assms]: ct_not_in_q
  and simple_sched_action[wp, DetSchedSchedule_AI_assms]: simple_sched_action
  and not_cur_thread[wp, DetSchedSchedule_AI_assms]: "not_cur_thread t"
  and is_etcb_at[wp, DetSchedSchedule_AI_assms]: "is_etcb_at t"
  and not_queued[wp, DetSchedSchedule_AI_assms]: "not_queued t"
  and sched_act_not[wp, DetSchedSchedule_AI_assms]: "scheduler_act_not t"
  and weak_valid_sched_action[wp, DetSchedSchedule_AI_assms]: weak_valid_sched_action
  and valid_idle[wp, DetSchedSchedule_AI_assms]: valid_idle

crunches flush_space, invalidate_asid_entry, get_asid_pool
  for flush_space_valid_idle[wp]: "\<lambda>(s:: det_ext state). P (idle_thread s)"

crunch delete_asid_pool[wp]:
  delete_asid_pool "\<lambda>(s:: det_ext state). P (idle_thread s)"
  (wp: crunch_wps simp: if_apply_def2)

crunch idle_thread[wp, DetSchedSchedule_AI_assms]:
  arch_finalise_cap "\<lambda> (s:: det_ext state). P (idle_thread s)"
  (wp: crunch_wps)

end

global_interpretation DetSchedSchedule_AI?: DetSchedSchedule_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedSchedule_AI_assms)?)
  qed

context Arch begin global_naming ARM_HYP

lemma dmo_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane\<rbrace> do_machine_op f \<lbrace>\<lambda>rv. scheduler_act_sane\<rbrace>"
  unfolding scheduler_act_sane_def
  by (rule hoare_lift_Pf[where f=cur_thread]; wp)

lemma dmo_ct_idle[wp]:
  "\<lbrace>ct_idle\<rbrace> do_machine_op f \<lbrace>\<lambda>rv. ct_idle\<rbrace>"
  unfolding ct_in_state_def by wp

lemma vgic_maintenance_irq_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and scheduler_act_sane and ct_not_queued\<rbrace>
   vgic_maintenance
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding vgic_maintenance_def
  supply if_split[split del] valid_fault_def[simp]
  apply (wpsimp simp: get_gic_vcpu_ctrl_misr_def get_gic_vcpu_ctrl_eisr1_def
                      get_gic_vcpu_ctrl_eisr0_def if_apply_def2
                 wp: thread_get_wp'
                     ct_in_state_thread_state_lift ct_not_queued_lift sch_act_sane_lift
                     hoare_vcg_imp_lift' gts_wp hoare_vcg_all_lift
                     handle_fault_valid_sched hoare_vcg_disj_lift
         | wp (once) hoare_drop_imp[where f="do_machine_op m" for m]
                   hoare_drop_imp[where f="return $ m" for m]
         | wps
         | strengthen not_pred_tcb_at_strengthen)+
  apply (frule tcb_at_invs)
  apply (clarsimp simp: runnable_eq halted_eq not_pred_tcb)
  apply (fastforce intro!: st_tcb_ex_cap[where P=active]
                   simp: st_tcb_at_def ct_in_state_def obj_at_def)
  done

lemma vppi_event_irq_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and scheduler_act_sane and ct_not_queued\<rbrace>
   vppi_event irq
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding vppi_event_def
  supply if_split[split del] valid_fault_def[simp]
  apply (wpsimp simp: if_apply_def2
                wp: hoare_vcg_imp_lift' gts_wp hoare_vcg_all_lift maskInterrupt_invs
                    hoare_vcg_disj_lift
                    handle_fault_valid_sched
                    ct_in_state_thread_state_lift ct_not_queued_lift sch_act_sane_lift
                cong: vcpu.fold_congs
         | wps
         | strengthen not_pred_tcb_at_strengthen)+
  apply (frule tcb_at_invs)
  apply (clarsimp simp: runnable_eq halted_eq not_pred_tcb)
  apply (fastforce intro!: st_tcb_ex_cap[where P=active]
                   simp: not_pred_tcb st_tcb_at_def obj_at_def ct_in_state_def)
  done

lemma handle_reserved_irq_valid_sched:
  "\<lbrace>valid_sched and invs and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow>  scheduler_act_sane s \<and> ct_not_queued s)\<rbrace>
  handle_reserved_irq irq \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding handle_reserved_irq_def irq_vppi_event_index_def
  by (wpsimp simp: non_kernel_IRQs_def)

lemma handle_hyp_fault_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and st_tcb_at active t and not_queued t and scheduler_act_not t
      and (ct_active or ct_idle)\<rbrace>
    handle_hypervisor_fault t fault \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (cases fault; wpsimp wp: handle_fault_valid_sched simp: valid_fault_def)

end

global_interpretation DetSchedSchedule_AI_handle_hypervisor_fault?: DetSchedSchedule_AI_handle_hypervisor_fault
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact handle_hyp_fault_valid_sched handle_reserved_irq_valid_sched)?)
  qed

end
