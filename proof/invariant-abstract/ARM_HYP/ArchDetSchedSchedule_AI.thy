(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory ArchDetSchedSchedule_AI
imports "../DetSchedSchedule_AI"
begin

context Arch begin global_naming ARM_HYP

named_theorems DetSchedSchedule_AI_assms

crunch exst[wp]: set_vcpu "\<lambda>s. P (exst s)" (wp: crunch_wps)
crunch exst[wp]: vcpu_disable,vcpu_restore,vcpu_save "\<lambda>s. P (exst s)"

lemma vcpu_switch_exst[wp]:
  "\<lbrace>\<lambda>s. P (exst s)\<rbrace> vcpu_switch param_a \<lbrace>\<lambda>_ s. P (exst s)\<rbrace>"
  unfolding vcpu_switch_def by (rule hoare_pre) wpsimp+

crunch exst[wp]: switch_to_idle_thread,set_vm_root "\<lambda>s. P (exst s)"
  (simp: whenE_def ignore: set_object do_machine_op wp: crunch_wps)

lemma set_vcpu_etcbs [wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_vcpu a b \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  by (rule valid_etcbs_lift; wp)

lemma vcpu_switch_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> vcpu_switch param_a \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  by (rule valid_etcbs_lift; wp)

crunch valid_etcbs [wp, DetSchedSchedule_AI_assms]:
  arch_switch_to_idle_thread, arch_switch_to_thread, vcpu_disable, vcpu_restore, vcpu_save, set_vm_root
  valid_etcbs
  (simp: whenE_def ignore: clearExMonitor set_object do_machine_op wp: crunch_wps)

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
  arch_switch_to_idle_thread, arch_switch_to_thread, vcpu_disable, vcpu_restore, vcpu_save, set_vm_root
  valid_queues
  (simp: whenE_def ignore: set_tcb_queue tcb_sched_action clearExMonitor wp: crunch_wps)

lemma set_vcpu_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace> set_vcpu ptr vcpu \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (rule weak_valid_sched_action_lift; wp)

lemma vcpu_switch_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace> vcpu_switch v \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (rule weak_valid_sched_action_lift; wp)

crunch weak_valid_sched_action[wp, DetSchedSchedule_AI_assms]:
  arch_switch_to_idle_thread, arch_switch_to_thread, vcpu_disable, vcpu_restore, vcpu_save, set_vm_root
  weak_valid_sched_action
  (simp: whenE_def wp: crunch_wps)

crunch cur_thread[wp]: set_vcpu, vcpu_disable, vcpu_restore, vcpu_save "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps)

lemma vcpu_switch_cur_thread [wp]:
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> vcpu_switch param_a \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
  unfolding vcpu_switch_def by (rule hoare_pre) wpsimp+

crunch cur_thread[wp]: set_vm_root "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps simp: crunch_simps)

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

lemma valid_sched_action_idle_strg:
  "thread = idle_thread s \<and> valid_sched_action s \<and> valid_idle s \<Longrightarrow>
   valid_sched_action (s\<lparr>cur_thread := thread\<rparr>)"
  by (auto simp: valid_sched_action_def is_activatable_def valid_idle_def pred_tcb_at_def obj_at_def)

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

crunch is_activatable[wp]: vcpu_disable,vcpu_restore,vcpu_save "is_activatable t"
  (wp: crunch_wps simp: crunch_simps)

lemma vcpu_switch_is_activatable[wp]:
  "\<lbrace>is_activatable t\<rbrace> vcpu_switch v \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  unfolding vcpu_switch_def by (rule hoare_pre) wpsimp+

crunch is_activatable[wp]: set_vm_root "is_activatable t"
  (wp: crunch_wps simp: crunch_simps)

lemma set_vm_root_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace> set_vm_root param_a \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (rule valid_sched_action_lift; wp)

crunch ct_not_in_q[wp, DetSchedSchedule_AI_assms]: arch_switch_to_thread ct_not_in_q
  (simp: whenE_def ignore: clearExMonitor)

crunch is_activatable[wp, DetSchedSchedule_AI_assms]: arch_switch_to_thread "is_activatable t"
  (simp: whenE_def ignore: clearExMonitor)

crunch valid_sched_action[wp, DetSchedSchedule_AI_assms]: arch_switch_to_thread valid_sched_action
  (simp: whenE_def ignore: clearExMonitor)

crunch it[wp]: set_vm_root "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_vm_root_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_vm_root tcb \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (rule valid_sched_lift; wp)

crunch valid_sched[wp, DetSchedSchedule_AI_assms]: arch_switch_to_thread valid_sched
  (simp: whenE_def ignore: clearExMonitor)

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

crunch ct_in_cur_domain_2[wp, DetSchedSchedule_AI_assms]: arch_switch_to_thread
  "\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (ekheap s)"
  (simp: whenE_def)

crunch valid_blocked[wp]: do_machine_op valid_blocked
  (simp: crunch_simps)

lemma set_vm_root_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> set_vm_root param_a \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  by (rule valid_blocked_lift; wp)

crunch ct_in_q[wp]: do_machine_op ct_in_q

lemma set_vm_root_ct_in_q[wp]:
  "\<lbrace>ct_in_q\<rbrace> set_vm_root param_a \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  unfolding ct_in_q_def
  apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_thread s", rotated], wp)
  apply (rule hoare_lift_Pf[where f="\<lambda>s. ready_queues s", rotated], wp)
  apply wp
  done

lemma set_vm_root_valid_blocked_ct_in_q[wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> set_vm_root p \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  by (wp | wpc | auto)+

lemma arch_switch_to_thread_valid_blocked[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> arch_switch_to_thread thread \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply (rule hoare_seq_ext)+
   apply (rule do_machine_op_valid_blocked)
  apply wp
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

lemma vcpu_switch_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> vcpu_switch v \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  unfolding valid_blocked_def not_queued_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift) auto

lemma vcpu_switch_ct_in_q[wp]:
  "\<lbrace>ct_in_q\<rbrace> vcpu_switch v \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  unfolding ct_in_q_def
  apply (rule hoare_lift_Pf[where f=cur_thread])
   apply (rule hoare_lift_Pf[where f=ready_queues])
    apply wpsimp+
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
  by (rule valid_sched_lift; wp)

crunch ct_not_in_q [wp, DetSchedSchedule_AI_assms]:
  arch_finalise_cap, prepare_thread_delete ct_not_in_q
  (wp: crunch_wps hoare_drop_imps hoare_unless_wp select_inv mapM_wp
       subset_refl if_fun_split simp: crunch_simps ignore: tcb_sched_action)

crunch valid_etcbs [wp, DetSchedSchedule_AI_assms]:
  arch_finalise_cap, prepare_thread_delete valid_etcbs
  (wp: hoare_drop_imps hoare_unless_wp select_inv mapM_x_wp mapM_wp subset_refl
       if_fun_split simp: crunch_simps ignore: set_object thread_set)

crunch simple_sched_action [wp, DetSchedSchedule_AI_assms]:
  arch_finalise_cap, prepare_thread_delete simple_sched_action
  (wp: hoare_drop_imps mapM_x_wp mapM_wp select_wp subset_refl
   simp: unless_def if_fun_split)

crunch valid_sched [wp, DetSchedSchedule_AI_assms]:
  arch_tcb_set_ipc_buffer, arch_finalise_cap, prepare_thread_delete valid_sched
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
  (wp: mapM_x_wp' mapM_wp')

crunch cur_thread[wp]: read_vcpu_register "\<lambda>s. P (cur_thread s)"

crunch ct_active[wp]:
  write_vcpu_register,read_vcpu_register,set_message_info,as_user
  ct_active
  (wp: ct_in_state_thread_state_lift)

crunch valid_sched[wp]: read_vcpu_register,write_vcpu_register valid_sched

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

crunch cur_tcb [wp, DetSchedSchedule_AI_assms]: handle_arch_fault_reply, handle_vm_fault cur_tcb

crunch not_cur_thread [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg "not_cur_thread t'"
crunch valid_sched    [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg valid_sched
crunch ready_queues   [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg "\<lambda>s. P (ready_queues s)"
crunch valid_etcbs    [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg valid_etcbs

crunch scheduler_action [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg "\<lambda>s. P (scheduler_action s)"

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

lemma vgic_maintenance_irq_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and scheduler_act_sane and ct_not_queued\<rbrace>
  vgic_maintenance \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding vgic_maintenance_def
            get_gic_vcpu_ctrl_misr_def get_gic_vcpu_ctrl_eisr1_def get_gic_vcpu_ctrl_eisr0_def
  apply (wpsimp wp: handle_fault_valid_sched thread_get_wp'
              simp: do_machine_op_bind valid_fault_def
         | rule conjI | strengthen conj_imp_strg)+
  apply (clarsimp simp: st_tcb_at_def obj_at_def runnable_eq)
  done

lemma handle_reserved_irq_valid_sched:
  "\<lbrace>valid_sched and invs and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow>  scheduler_act_sane s \<and> ct_not_queued s)\<rbrace>
  handle_reserved_irq irq \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding handle_reserved_irq_def by (wpsimp simp: non_kernel_IRQs_def)

lemma handle_hyp_fault_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and st_tcb_at active t and not_queued t and scheduler_act_not t\<rbrace>
    handle_hypervisor_fault t fault \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (cases fault; wpsimp wp: handle_fault_valid_sched simp: valid_fault_def)

end

global_interpretation DetSchedSchedule_AI_handle_hypervisor_fault?: DetSchedSchedule_AI_handle_hypervisor_fault
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact handle_hyp_fault_valid_sched handle_reserved_irq_valid_sched)?)
  qed

end
