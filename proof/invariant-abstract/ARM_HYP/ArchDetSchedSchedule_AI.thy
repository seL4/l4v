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
  for prepare_thread_delete_idle_thread[wp, DetSchedSchedule_AI_assms]: "\<lambda>(s:: det_ext state). P (idle_thread s)"
  (wp: crunch_wps)

crunch set_vcpu
  for exst[wp]: "\<lambda>s. P (exst s)" (wp: crunch_wps)

crunch vcpu_disable,vcpu_restore,vcpu_save
  for exst[wp]: "\<lambda>s. P (exst s)"
  (wp: crunch_wps)

lemma vcpu_switch_exst[wp]:
  "\<lbrace>\<lambda>s. P (exst s)\<rbrace> vcpu_switch param_a \<lbrace>\<lambda>_ s. P (exst s)\<rbrace>"
  unfolding vcpu_switch_def by (rule hoare_pre) wpsimp+

crunch switch_to_idle_thread,set_vm_root
  for exst[wp]: "\<lambda>s. P (exst s)"
  (simp: crunch_simps ignore: set_object do_machine_op wp: crunch_wps)

lemma pred_tcb_atP[wp]:
  "\<lbrace>\<lambda>s. P (pred_tcb_at proj Q t s)\<rbrace> set_vcpu prt vcpu \<lbrace>\<lambda>_ s. P (pred_tcb_at proj Q t s)\<rbrace>"
  unfolding set_vcpu_def set_object_def
  apply (wp get_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def split: kernel_object.splits)
  done

crunch vcpu_disable, vcpu_enable, vcpu_restore, vcpu_save
  for pred_tcb_atP[wp]: "\<lambda>s. P (pred_tcb_at proj Q t s)"
  (wp: crunch_wps simp: crunch_simps)

lemma vcpu_switch_pred_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (pred_tcb_at proj Q t s)\<rbrace> vcpu_switch vcpu \<lbrace>\<lambda>_ s. P (pred_tcb_at proj Q t s)\<rbrace>"
  unfolding vcpu_switch_def by (rule hoare_pre) wpsimp+

crunch set_vm_root
  for pred_tcb_atP[wp]: "\<lambda>s. P (pred_tcb_at proj Q t s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_vcpu_etcbs_of[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_vcpu_def
  apply (wpsimp wp: set_object_wp_strong)
  by (auto elim!: rsubst[where P=P] simp: etcbs_of'_def obj_at_def a_type_def
           split: kernel_object.splits)

crunch set_vcpu
  for ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"

lemma set_vcpu_valid_queues [wp]:
  "\<lbrace>valid_queues\<rbrace> set_vcpu ptr vcpu \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  by (rule valid_queues_lift; wp)

crunch vcpu_switch
  for etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps)

lemma vcpu_switch_valid_queues[wp]:
  "\<lbrace>valid_queues\<rbrace> vcpu_switch v \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  by (rule valid_queues_lift; wp)

crunch
  arch_switch_to_idle_thread, arch_switch_to_thread, vcpu_disable, vcpu_restore, vcpu_save, set_vm_root, arch_get_sanitise_register_info, arch_post_modify_registers
  for valid_queues[wp, DetSchedSchedule_AI_assms]: valid_queues
  (simp: crunch_simps ignore: set_tcb_queue tcb_sched_action clearExMonitor wp: crunch_wps)

lemma set_vcpu_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace> set_vcpu ptr vcpu \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (rule weak_valid_sched_action_lift; wp)

lemma vcpu_switch_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace> vcpu_switch v \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (rule weak_valid_sched_action_lift; wp)

crunch
  arch_switch_to_idle_thread, arch_switch_to_thread, vcpu_disable, vcpu_restore, vcpu_save, set_vm_root, arch_get_sanitise_register_info, arch_post_modify_registers
  for weak_valid_sched_action[wp, DetSchedSchedule_AI_assms]: weak_valid_sched_action
  (simp: crunch_simps wp: crunch_wps)

crunch set_vm_root
  for ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and ct_not_in_q[wp]: "ct_not_in_q"
  and ct_not_in_q'[wp]: "\<lambda>s. ct_not_in_q_2 (ready_queues s) (scheduler_action s) t"
  (wp: crunch_wps simp: crunch_simps)

lemma vcpu_switch_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace> vcpu_switch v \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  unfolding valid_sched_action_def is_activatable_def st_tcb_at_kh_simp
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp wp: hoare_vcg_imp_lift switch_in_cur_domain_lift)

lemma switch_to_idle_thread_ct_not_in_q[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_queues and valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  unfolding switch_to_idle_thread_def arch_switch_to_idle_thread_def
  apply (wpsimp | wps)+
  apply (fastforce simp: valid_queues_def ct_not_in_q_def not_queued_def
                         valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma set_vm_root_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> set_vm_root v \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  unfolding valid_idle_def by (rule hoare_lift_Pf[where f=idle_thread]; wp)

lemma valid_sched_action_idle_strg:
  "thread = idle_thread s \<and> valid_sched_action s \<and> valid_idle s \<Longrightarrow>
   valid_sched_action (s\<lparr>cur_thread := thread\<rparr>)"
  by (auto simp: valid_sched_action_def is_activatable_def valid_idle_def pred_tcb_at_def obj_at_def)

crunch set_vm_root
  for valid_sched_action[wp]: "valid_sched_action"
  (simp: crunch_simps wp: crunch_wps)

lemma switch_to_idle_thread_valid_sched_action[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_sched_action and valid_idle\<rbrace>
     switch_to_idle_thread
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def)
  apply (wp | strengthen valid_sched_action_idle_strg)+
  apply simp
  done

crunch set_vm_root
  for ct_in_cur_domain'[wp]: "\<lambda>s. ct_in_cur_domain_2 t (idle_thread s)
                                                   (scheduler_action s) (cur_domain s) (etcbs_of s)"
  (wp: crunch_wps simp: crunch_simps)

lemma switch_to_idle_thread_ct_in_cur_domain[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  unfolding switch_to_idle_thread_def arch_switch_to_idle_thread_def
  by (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_disj_lift | simp add: ct_in_cur_domain_def | wps)+

lemma do_machine_op_activatable[wp]:
  "\<lbrace>is_activatable t\<rbrace> do_machine_op oper \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  unfolding do_machine_op_def by wpsimp

lemma set_vcpu_is_activatable[wp]:
  "\<lbrace>is_activatable t\<rbrace> set_vcpu ptr vcpu \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  unfolding is_activatable_def set_vcpu_def set_object_def
  apply (wp get_object_wp)
  apply (clarsimp simp: st_tcb_at_kh_def obj_at_kh_def obj_at_def)
  done

crunch set_vm_root
  for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"

crunch vcpu_disable, vcpu_restore, vcpu_save, vcpu_switch, set_vm_root
  for etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  and is_activatable[wp]: "is_activatable t"
  and valid_sched[wp, DetSchedSchedule_AI_assms]: valid_sched
  (wp: crunch_wps valid_sched_lift simp: crunch_simps)

crunch arch_switch_to_thread, arch_get_sanitise_register_info, arch_post_modify_registers
  for ct_not_in_q[wp, DetSchedSchedule_AI_assms]: ct_not_in_q
  and is_activatable[wp, DetSchedSchedule_AI_assms]: "is_activatable t"
  and valid_sched_action[wp, DetSchedSchedule_AI_assms]: valid_sched_action
  and valid_sched[wp, DetSchedSchedule_AI_assms]: valid_sched
  (wp: crunch_wps valid_sched_lift simp: crunch_simps)

crunch arch_switch_to_thread
  for ct_in_cur_domain_2[wp, DetSchedSchedule_AI_assms]:
    "\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)"
  (simp: crunch_simps wp: assert_inv crunch_wps ignore: set_vcpu)

lemma vcpu_switch_ct_in_q[wp]:
  "\<lbrace>ct_in_q\<rbrace> vcpu_switch vcpu \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  unfolding ct_in_q_def
  apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_thread s", rotated], wp)
  apply (rule hoare_lift_Pf[where f="\<lambda>s. ready_queues s", rotated], wp)
  apply wp
  done

crunch do_machine_op, set_vm_root, vcpu_switch
  for valid_blocked[wp]: valid_blocked
  and ct_in_q[wp]: ct_in_q
  (wp: valid_blocked_lift simp: crunch_simps)

lemma set_vm_root_valid_blocked_ct_in_q[wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> set_vm_root p \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  by wpsimp

lemma arch_switch_to_thread_valid_blocked[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> arch_switch_to_thread thread \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply (rule bind_wp)+
     apply (rule do_machine_op_valid_blocked)
    apply wpsimp+
  done

crunch
  arch_switch_to_thread, arch_switch_to_idle_thread
  for etcb_at[wp, DetSchedSchedule_AI_assms]: "etcb_at P t"

crunch
  arch_switch_to_idle_thread, next_domain
  for scheduler_action[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (scheduler_action s)"
  (simp: Let_def)

lemma switch_to_idle_thread_ct_not_queued[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_queues and valid_idle\<rbrace>
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

crunch arch_switch_to_thread
  for exst[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (exst s)"

crunch
  arch_switch_to_idle_thread
  for valid_idle[wp, DetSchedSchedule_AI_assms]: "valid_idle :: det_ext state \<Rightarrow> bool"

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

lemma set_pt_etcbs[wp]:
  "set_pt ptr pt \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_pt_def
  apply (wpsimp wp: set_object_wp_strong)
  by (auto elim!: rsubst[where P=P] simp: etcbs_of'_def obj_at_def a_type_def
           split: kernel_object.splits)

lemma set_asid_pool_etcbs[wp]:
  "set_asid_pool ptr pool \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_asid_pool_def
  apply (wpsimp wp: set_object_wp_strong)
  by (auto elim!: rsubst[where P=P] simp: etcbs_of'_def obj_at_def a_type_def
           split: kernel_object.splits)

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

crunch arch_thread_set
  for etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  (wp: set_object_wp)

lemma arch_thread_set_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> arch_thread_set f t \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp wp: valid_sched_lift arch_thread_set_pred_tcb_at)

crunch
  arch_finalise_cap, prepare_thread_delete
  for ct_not_in_q[wp, DetSchedSchedule_AI_assms]: ct_not_in_q
  (wp: crunch_wps hoare_drop_imps unless_wp select_inv mapM_wp
       subset_refl if_fun_split simp: crunch_simps ignore: tcb_sched_action)

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
  (wp: crunch_wps)

crunch
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

crunch perform_vcpu_invocation
  for valid_sched[wp]: valid_sched
  (wp: crunch_wps simp: crunch_simps ignore: set_thread_state)

lemma arch_perform_invocation_valid_sched[wp, DetSchedSchedule_AI_assms]:
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

lemma handle_vm_fault_st_tcb_cur_thread[wp, DetSchedSchedule_AI_assms]:
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

crunch make_arch_fault_msg, arch_get_sanitise_register_info, arch_post_modify_registers
  for not_cur_thread[wp, DetSchedSchedule_AI_assms]: "not_cur_thread t'"
crunch make_arch_fault_msg, arch_mask_irq_signal
  for valid_sched[wp, DetSchedSchedule_AI_assms]: valid_sched
crunch make_arch_fault_msg, arch_get_sanitise_register_info, arch_post_modify_registers
  for ready_queues[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (ready_queues s)"
crunch make_arch_fault_msg, arch_get_sanitise_register_info, arch_post_modify_registers
  for scheduler_action[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (scheduler_action s)"
declare arch_switch_to_idle_thread_exst[DetSchedSchedule_AI_assms]

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

crunch flush_space, invalidate_asid_entry, get_asid_pool
  for flush_space_valid_idle[wp]: "\<lambda>(s:: det_ext state). P (idle_thread s)"

crunch
  delete_asid_pool
  for delete_asid_pool[wp]: "\<lambda>(s:: det_ext state). P (idle_thread s)"
  (wp: crunch_wps simp: if_apply_def2)

crunch
  arch_finalise_cap
  for idle_thread[wp, DetSchedSchedule_AI_assms]: "\<lambda> (s:: det_ext state). P (idle_thread s)"
  (wp: crunch_wps)

crunch arch_switch_to_thread
  for etcbs_of[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (etcbs_of s)"
  and cur_domain[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (cur_domain s)"

crunch arch_switch_to_thread
  for etcbs_of[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (etcbs_of s)"
  and cur_domain[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (cur_domain s)"

end

global_interpretation DetSchedSchedule_AI?: DetSchedSchedule_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedSchedule_AI_assms)?)
  qed

context Arch begin arch_global_naming

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
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
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
         | strengthen Not_pred_tcb_at_strengthen)+
  apply (frule tcb_at_invs)
  apply (clarsimp simp: runnable_eq halted_eq not_pred_tcb)
  apply (fastforce intro!: st_tcb_ex_cap[where P=active]
                   simp: st_tcb_at_def ct_in_state_def obj_at_def)
  done

lemma vppi_event_irq_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and scheduler_act_sane and ct_not_queued\<rbrace>
   vppi_event irq
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding vppi_event_def
  supply if_split[split del] valid_fault_def[simp]
  apply (wpsimp simp: if_apply_def2
                wp: hoare_vcg_imp_lift' gts_wp hoare_vcg_all_lift maskInterrupt_invs
                    hoare_vcg_disj_lift
                    handle_fault_valid_sched
                    ct_in_state_thread_state_lift ct_not_queued_lift sch_act_sane_lift
                cong: vcpu.fold_congs
         | wps
         | strengthen Not_pred_tcb_at_strengthen)+
  apply (frule tcb_at_invs)
  apply (clarsimp simp: runnable_eq halted_eq not_pred_tcb)
  apply (fastforce intro!: st_tcb_ex_cap[where P=active]
                   simp: not_pred_tcb st_tcb_at_def obj_at_def ct_in_state_def)
  done

lemma handle_reserved_irq_valid_sched:
  "\<lbrace>valid_sched and invs and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow>  scheduler_act_sane s \<and> ct_not_queued s)\<rbrace>
  handle_reserved_irq irq \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding handle_reserved_irq_def irq_vppi_event_index_def
  by (wpsimp simp: non_kernel_IRQs_def)

lemma handle_hyp_fault_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and st_tcb_at active t and not_queued t and scheduler_act_not t
      and (ct_active or ct_idle)\<rbrace>
    handle_hypervisor_fault t fault \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  by (cases fault; wpsimp wp: handle_fault_valid_sched simp: valid_fault_def)

end

global_interpretation DetSchedSchedule_AI_handle_hypervisor_fault?: DetSchedSchedule_AI_handle_hypervisor_fault
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact handle_hyp_fault_valid_sched handle_reserved_irq_valid_sched)?)
  qed

end
