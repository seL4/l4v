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

context Arch begin global_naming ARM

named_theorems DetSchedSchedule_AI_assms

crunch valid_ready_qs [wp, DetSchedSchedule_AI_assms]:
  switch_to_idle_thread, switch_to_thread, set_vm_root, arch_get_sanitise_register_info, arch_post_modify_registers valid_ready_qs
  (simp: whenE_def ignore: set_tcb_queue tcb_sched_action clearExMonitor wp: hoare_drop_imp tcb_sched_action_dequeue_valid_ready_qs)

crunch valid_release_q [wp, DetSchedSchedule_AI_assms]:
  switch_to_idle_thread, switch_to_thread, set_vm_root, arch_get_sanitise_register_info, arch_post_modify_registers valid_release_q
  (simp: whenE_def ignore: set_tcb_queue tcb_sched_action clearExMonitor wp: hoare_drop_imp)

crunch weak_valid_sched_action [wp, DetSchedSchedule_AI_assms]:
  switch_to_idle_thread, switch_to_thread, set_vm_root, arch_get_sanitise_register_info, arch_post_modify_registers "weak_valid_sched_action"
  (simp: whenE_def ignore: clearExMonitor wp: hoare_drop_imp)

crunch active_sc_tcb_at [wp, DetSchedSchedule_AI_assms]:
   set_vm_root, arch_get_sanitise_register_info, arch_post_modify_registers, handle_arch_fault_reply "active_sc_tcb_at t"
  (simp: whenE_def active_sc_tcb_at_defs ignore: clearExMonitor)
(*
crunch active_sc_tcb_at [wp, DetSchedSchedule_AI_assms]:
  switch_to_idle_thread, switch_to_thread "active_sc_tcb_at t"
  (simp: whenE_def active_sc_tcb_at_def pred_tcb_at_def obj_at_def ignore: clearExMonitor)
*)
crunch ct_not_in_q[wp]: set_vm_root "ct_not_in_q"
  (wp: crunch_wps simp: crunch_simps)

crunch ct_not_in_q'[wp]: set_vm_root "\<lambda>s. ct_not_in_q_2 (ready_queues s) (scheduler_action s) t"
  (wp: crunch_wps simp: crunch_simps)

lemma switch_to_idle_thread_ct_not_in_q [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_ready_qs and valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: switch_to_idle_thread_def)
  apply wp
   apply (simp add: arch_switch_to_idle_thread_def)
   apply wp+
  apply (fastforce simp: valid_ready_qs_def ct_not_in_q_def not_queued_def
                         valid_idle_def pred_tcb_at_def obj_at_def)
  done

crunches arch_switch_to_idle_thread, prepare_thread_delete
  for release_queue[wp]: "\<lambda>s. P (release_queue s)"

crunch valid_sched_action'[wp]: set_vm_root "\<lambda>s. valid_sched_action_2 (scheduler_action s)
                                                 (kheap s) thread (cur_domain s) (release_queue s)"
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

crunch ct_in_cur_domain'[wp]: set_vm_root "\<lambda>s. ct_in_cur_domain_2 t (idle_thread s)
                                                   (scheduler_action s) (cur_domain s) (etcbs_of s)"
  (wp: crunch_wps simp: crunch_simps)

lemma switch_to_idle_thread_ct_in_cur_domain [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  by (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def do_machine_op_def
                split_def
      | wp
      | simp add: ct_in_cur_domain_def)+

crunch ct_not_in_q [wp, DetSchedSchedule_AI_assms]: arch_switch_to_thread, arch_get_sanitise_register_info, arch_post_modify_registers ct_not_in_q
  (simp: crunch_simps ignore: clearExMonitor)

crunch is_activatable [wp, DetSchedSchedule_AI_assms]: arch_switch_to_thread, arch_get_sanitise_register_info, arch_post_modify_registers "is_activatable t"
  (simp: crunch_simps ignore: clearExMonitor)

crunch valid_sched_action [wp, DetSchedSchedule_AI_assms]: arch_switch_to_thread, arch_get_sanitise_register_info, arch_post_modify_registers valid_sched_action
  (simp: crunch_simps ignore: clearExMonitor)

crunch valid_sched [wp, DetSchedSchedule_AI_assms]: arch_switch_to_thread, arch_get_sanitise_register_info, arch_post_modify_registers "valid_sched::det_state \<Rightarrow> _"
  (simp: whenE_def ignore: clearExMonitor)

crunch exst[wp]: set_vm_root "\<lambda>s. P (exst s)"
  (wp: crunch_wps hoare_whenE_wp simp: crunch_simps)

crunch ct_in_cur_domain_2[wp]: set_vm_root
  "\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)"
  (simp: whenE_def crunch_simps)

crunch ct_in_cur_domain_2 [wp, DetSchedSchedule_AI_assms]: arch_switch_to_thread
  "\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)"
  (simp: whenE_def crunch_simps)

crunch valid_blocked'[wp]: set_vm_root valid_blocked
  (simp: crunch_simps)

crunch ct_in_q[wp]: set_vm_root ct_in_q
  (simp: crunch_simps)

crunch etcb_at [wp, DetSchedSchedule_AI_assms]: switch_to_thread "etcb_at P t"
  (wp: hoare_drop_imp)

crunch valid_idle [wp, DetSchedSchedule_AI_assms]:
  arch_switch_to_idle_thread "valid_idle"
  (wp: crunch_wps simp: crunch_simps)

crunch etcb_at [wp, DetSchedSchedule_AI_assms]: arch_switch_to_idle_thread "etcb_at P t"

crunch scheduler_action [wp, DetSchedSchedule_AI_assms]:
  arch_switch_to_idle_thread, next_domain "\<lambda>s. P (scheduler_action s)"
  (simp: Let_def crunch_simps wp: dxo_wp_weak crunch_wps)

lemma set_vm_root_valid_blocked_ct_in_q [wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> set_vm_root p \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  by (wp | wpc | auto)+

lemma arch_switch_to_thread_valid_blocked [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> arch_switch_to_thread thread \<lbrace>\<lambda>_. valid_blocked and ct_in_q::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply (rule hoare_seq_ext)+
   apply (rule do_machine_op_valid_blocked)
  apply wp
  done

crunch not_queued[wp]: set_vm_root "not_queued t"
  (simp: crunch_simps)

(*  FIXME: Move *)
lemma not_in_release_q_arch_state_update[simp]:
  "not_in_release_q t (s\<lparr>arch_state := as \<rparr>) = not_in_release_q t s"
  by (clarsimp simp: not_in_release_q_def)

(*  FIXME: Move *)
lemma not_in_release_q_machine_state_update[simp]:
  "not_in_release_q t (s\<lparr>machine_state := as \<rparr>) = not_in_release_q t s"
  by (clarsimp simp: not_in_release_q_def)

crunch not_in_release_q[wp]: set_vm_root "not_in_release_q t"
  (simp: crunch_simps )

lemma switch_to_idle_thread_ct_not_queued [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_ready_qs and valid_idle\<rbrace>
     switch_to_idle_thread
   \<lbrace>\<lambda>rv s. not_queued (cur_thread s) s\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def
                   tcb_sched_action_def | wp)+
  apply (fastforce simp: valid_sched_2_def valid_ready_qs_2_def valid_idle_def
                         pred_tcb_at_def obj_at_def not_queued_def)
  done

crunch valid_blocked_2[wp]: set_vm_root "\<lambda>s.
           valid_blocked_2 (ready_queues s) (release_queue s) (kheap s)
            (scheduler_action s) thread"
  (wp: crunch_wps simp: crunch_simps)

lemma switch_to_idle_thread_valid_blocked [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def do_machine_op_def | wp | wpc)+
  apply clarsimp
  apply (drule(1) ct_in_q_valid_blocked_ct_upd)
  apply simp
  done

crunch exst [wp, DetSchedSchedule_AI_assms]: arch_switch_to_thread "\<lambda>s. P (exst s :: det_ext)"
  (ignore: clearExMonitor)

crunch cur_thread[wp]: arch_switch_to_idle_thread "\<lambda>s. P (cur_thread s)"

crunch inv[wp]: arch_switch_to_idle_thread "\<lambda>s. P"
  (wp: crunch_wps simp: crunch_simps)

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

crunches set_vm_root
for it[wp]: "\<lambda>s. P (idle_thread s)"
  (simp: crunch_simps)

lemma switch_to_idle_thread_cur_thread_idle_thread [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_ s. cur_thread s = idle_thread s\<rbrace>"
  by (wp | simp add:switch_to_idle_thread_def arch_switch_to_idle_thread_def)+

lemma set_pt_etcbs[wp]:
  "set_pt ptr pt \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_pt_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (auto elim!: rsubst[where P=P] simp: obj_at_def etcbs_of'_def split: kernel_object.splits)
  done

lemma set_pt_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_pt ptr pt \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: set_pt_def)+

lemma set_pd_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_pd ptr pd \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: set_pd_def)+

lemma set_asid_pool_etcbs[wp]:
  "set_asid_pool ptr pool \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_asid_pool_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (auto elim!: rsubst[where P=P] simp: obj_at_def etcbs_of'_def split: kernel_object.splits)
  done

lemma set_asid_pool_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_asid_pool ptr pool \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wpsimp wp: hoare_drop_imps valid_sched_lift simp: set_asid_pool_def)

crunch ct_not_in_q [wp, DetSchedSchedule_AI_assms]:
  arch_finalise_cap, prepare_thread_delete ct_not_in_q
  (wp: crunch_wps hoare_drop_imps hoare_unless_wp select_inv mapM_wp
       subset_refl if_fun_split simp: crunch_simps ignore: tcb_sched_action)

crunch simple_sched_action [wp, DetSchedSchedule_AI_assms]:
  arch_finalise_cap, prepare_thread_delete simple_sched_action
  (wp: hoare_drop_imps mapM_x_wp mapM_wp select_wp subset_refl
   simp: unless_def if_fun_split)

crunch valid_sched [wp, DetSchedSchedule_AI_assms]:
  arch_finalise_cap, prepare_thread_delete "valid_sched::det_state \<Rightarrow> _"
  (ignore: set_object as_user wp: crunch_wps subset_refl simp: if_fun_split)

crunches arch_tcb_set_ipc_buffer
for valid_sched [wp, DetSchedSchedule_AI_assms]: valid_sched
and simple_sched_action [wp, DetSchedSchedule_AI_assms]: simple_sched_action
  (ignore: set_object as_user wp: valid_sched_lift crunch_wps subset_refl simp: if_fun_split)

lemma set_thread_state_cur_thread_valid_blocked:
  "\<lbrace>valid_blocked and (\<lambda>s. ref = cur_thread s)\<rbrace> set_thread_state ref ts
  \<lbrace>\<lambda>_. valid_blocked :: det_state \<Rightarrow> _\<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_blocked_def
                 dest!: get_tcb_SomeD)
  apply (drule_tac x=t in spec,
         clarsimp simp: get_tcb_rev active_sc_tcb_at_defs st_tcb_at_kh_if_split
                 split: option.splits if_splits)
  done

lemma set_thread_state_cur_thread_runnable_valid_sched:
  "\<lbrace>valid_sched and (\<lambda>s. ref = cur_thread s) and K (runnable ts)\<rbrace>
   set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding valid_sched_def
  apply (wpsimp wp: set_thread_state_runnable_valid_ready_qs
                    set_thread_state_runnable_valid_release_q
                    set_thread_state_runnable_valid_sched_action
                    set_thread_state_cur_thread_valid_blocked)
  done

lemma activate_thread_valid_sched [DetSchedSchedule_AI_assms]:
  "\<lbrace>valid_sched\<rbrace>
   activate_thread
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding activate_thread_def
  by (wpsimp wp: set_thread_state_cur_thread_runnable_valid_sched gts_wp hoare_vcg_all_lift
                 get_tcb_obj_ref_wp hoare_drop_imps
           simp: arch_activate_idle_thread_def)

crunch valid_sched[wp]:
  perform_page_invocation, perform_page_table_invocation, perform_asid_pool_invocation,
  perform_page_directory_invocation
  "valid_sched::det_state \<Rightarrow> _"
  (wp: mapM_x_wp' mapM_wp')

lemma arch_perform_invocation_valid_sched [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>invs and valid_sched and ct_active and (\<lambda>s. scheduler_action s = resume_cur_thread) and
    valid_arch_inv a\<rbrace>
     arch_perform_invocation a
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (cases a, simp_all add: arch_perform_invocation_def)
      apply (wpsimp simp: valid_arch_inv_def invs_valid_idle
                      wp: perform_asid_control_invocation_valid_sched)+
  done

crunch valid_sched [wp, DetSchedSchedule_AI_assms]:
  handle_arch_fault_reply, handle_vm_fault "valid_sched::det_state \<Rightarrow> _"
  (ignore: getFAR getDFSR getIFSR wp: valid_sched_lift)

crunch not_queued [wp, DetSchedSchedule_AI_assms]:
  handle_vm_fault, handle_arch_fault_reply "not_queued t"
  (ignore: getFAR getDFSR getIFSR)

crunch not_in_release_q [wp, DetSchedSchedule_AI_assms]:
  handle_vm_fault, handle_arch_fault_reply "not_in_release_q t"
  (ignore: getFAR getDFSR getIFSR simp: not_in_release_q_def)

crunch sched_act_not [wp, DetSchedSchedule_AI_assms]:
  handle_arch_fault_reply, handle_vm_fault "scheduler_act_not t"
  (ignore: getFAR getDFSR getIFSR)

crunches handle_arch_fault_reply
 for simple_sched_action [wp, DetSchedSchedule_AI_assms]: simple_sched_action

crunches handle_arch_fault_reply, arch_get_sanitise_register_info
 for valid_ep_q [wp, DetSchedSchedule_AI_assms]: valid_ep_q

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

crunch valid_sched [wp, DetSchedSchedule_AI_assms]:
  arch_invoke_irq_control "valid_sched :: det_ext state \<Rightarrow> bool"

crunch valid_list [wp, DetSchedSchedule_AI_assms]:
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread "valid_list"

crunch cur_tcb [wp, DetSchedSchedule_AI_assms]: handle_arch_fault_reply, handle_vm_fault, arch_get_sanitise_register_info, arch_post_modify_registers cur_tcb

crunch not_cur_thread [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg, arch_get_sanitise_register_info, arch_post_modify_registers "not_cur_thread t'"
crunch ready_queues   [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg, arch_get_sanitise_register_info, arch_post_modify_registers "\<lambda>s. P (ready_queues s)"
crunch ct_not_queued   [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg, arch_get_sanitise_register_info, handle_arch_fault_reply "ct_not_queued"
crunch release_queue   [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg, arch_get_sanitise_register_info, arch_post_modify_registers "\<lambda>s. P (release_queue s)"
crunch ct_not_in_release_q   [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg, arch_get_sanitise_register_info, handle_arch_fault_reply "ct_not_in_release_q"

crunch scheduler_action [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg, arch_get_sanitise_register_info, arch_post_modify_registers "\<lambda>s. P (scheduler_action s)"
declare make_arch_fault_msg_inv[DetSchedSchedule_AI_assms]
crunch budget_ready [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg, arch_get_sanitise_register_info, arch_post_modify_registers "budget_ready t"
crunch budget_sufficient [wp, DetSchedSchedule_AI_assms]: make_arch_fault_msg, arch_get_sanitise_register_info, arch_post_modify_registers "budget_sufficient t"

lemma arch_post_modify_registers_not_idle_thread[DetSchedSchedule_AI_assms]:
  "\<lbrace>\<lambda>s::det_ext state. t \<noteq> idle_thread s\<rbrace> arch_post_modify_registers c t \<lbrace>\<lambda>_ s. t \<noteq> idle_thread s\<rbrace>"
  by (wpsimp simp: arch_post_modify_registers_def)

crunches arch_post_cap_deletion
  for valid_sched[wp, DetSchedSchedule_AI_assms]: valid_sched
  and valid_ready_qs[wp, DetSchedSchedule_AI_assms]: valid_ready_qs
  and valid_release_q[wp, DetSchedSchedule_AI_assms]: valid_release_q
  and ct_not_in_q[wp, DetSchedSchedule_AI_assms]: ct_not_in_q
  and simple_sched_action[wp, DetSchedSchedule_AI_assms]: simple_sched_action
  and not_cur_thread[wp, DetSchedSchedule_AI_assms]: "not_cur_thread t"
  and not_queued[wp, DetSchedSchedule_AI_assms]: "not_queued t"
  and not_in_release_q[wp, DetSchedSchedule_AI_assms]: "not_in_release_q t"
  and sched_act_not[wp, DetSchedSchedule_AI_assms]: "scheduler_act_not t"
  and weak_valid_sched_action[wp, DetSchedSchedule_AI_assms]: weak_valid_sched_action

crunches arch_switch_to_thread
  for etcbs[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (etcbs_of s)"
  and cur_domain[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (cur_domain s)"
  and scheduler_action[wp, DetSchedSchedule_AI_assms]: "\<lambda>s. P (scheduler_action s)"
  (simp: crunch_simps)

lemma handle_vm_fault_valid_machine_time[DetSchedSchedule_AI_assms]:
  "handle_vm_fault a b \<lbrace>valid_machine_time\<rbrace>"
  apply (case_tac b; simp)
   apply (wpsimp simp: do_machine_op_def |
          clarsimp simp: in_monad getFAR_def getDFSR_def getIFSR_def)+
  done

crunches as_user, arch_post_modify_registers, prepare_thread_delete, arch_post_cap_deletion
  for valid_machine_time[wp]: "valid_machine_time:: det_state \<Rightarrow> _"
  (wp: crunch_wps)

crunches setHardwareASID, set_current_pd, invalidateLocalTLB_ASID, cleanByVA, invalidateByVA,
  invalidateL2Range, cleanInvalByVA, cleanInvalidateL2Range, isb, branchFlush, invalidateByVA_I,
  cleanByVA_PoU, cleanL2Range, cleanCacheRange_PoC, branchFlushRange, invalidateCacheRange_I,
  cleanCacheRange_PoU, cleanInvalidateCacheRange_RAM, cleanInvalidateCacheRange_RAM,
  invalidateCacheRange_RAM, cleanCacheRange_RAM, setIRQTrigger, maskInterrupt,
  invalidateLocalTLB_VAASID, do_flush, storeWord, freeMemory, ackDeadlineIRQ, clearMemory
  for last_machine_time[wp]: "\<lambda>a. P (last_machine_time a)"
  (simp: isb_def writeTTBR0_def wp: crunch_wps)

lemma misc_dmo_valid_machine_time[wp]:
  "do_machine_op cleanCaches_PoU \<lbrace>valid_machine_time\<rbrace>"
  "do_machine_op ackDeadlineIRQ  \<lbrace>valid_machine_time\<rbrace>"
  "\<And>a. do_machine_op (set_current_pd a) \<lbrace>valid_machine_time\<rbrace>"
  "\<And>a. do_machine_op (invalidateLocalTLB_ASID a) \<lbrace>valid_machine_time\<rbrace>"
  "\<And>a. do_machine_op (invalidateLocalTLB_VAASID a) \<lbrace>valid_machine_time\<rbrace>"
  "\<And>a. do_machine_op (setHardwareASID a) \<lbrace>valid_machine_time\<rbrace>"
  "\<And>a. do_machine_op (ackInterrupt a) \<lbrace>valid_machine_time\<rbrace>"
  "\<And>a b. do_machine_op (clearMemory a b) \<lbrace>valid_machine_time\<rbrace>"
  "\<And>a b. do_machine_op (setIRQTrigger a b) \<lbrace>valid_machine_time\<rbrace>"
  "\<And>a b. do_machine_op (maskInterrupt a b) \<lbrace>valid_machine_time\<rbrace>"
  "\<And>a b. do_machine_op (cleanByVA_PoU a b) \<lbrace>valid_machine_time\<rbrace>"
  "\<And>a b. do_machine_op (freeMemory a b) \<lbrace>valid_machine_time\<rbrace>"
  "\<And>a b. do_machine_op (storeWord a b) \<lbrace>valid_machine_time\<rbrace>"
  "\<And>a b c. do_machine_op (cleanCacheRange_PoU a b c) \<lbrace>valid_machine_time\<rbrace>"
  "\<And>a b c d. do_machine_op (do_flush a b c d) \<lbrace>valid_machine_time\<rbrace>"
  apply (wpsimp wp: valid_machine_time_lift do_machine_op_machine_state)+
  done

crunches get_hw_asid, set_vm_root
  for last_machine_time[wp]: "\<lambda>a. P (last_machine_time (machine_state a))"
  and cur_time[wp]:  "\<lambda>a. Q (cur_time a)"
  (simp: wp: do_machine_op_machine_state)

lemma arm_context_switch_valid_machine_time[wp]:
  "arm_context_switch a b \<lbrace>valid_machine_time\<rbrace>"
  unfolding arm_context_switch_def
  by (wpsimp wp: valid_machine_time_lift do_machine_op_machine_state simp: )

crunches arch_invoke_irq_control
  for valid_machine_time[wp]: "valid_machine_time:: det_state \<Rightarrow> _"
  (wp: crunch_wps ignore: do_machine_op simp: crunch_simps)

crunches delete_asid, delete_asid_pool, unmap_page_table, unmap_page
  for valid_machine_time[wp]: "valid_machine_time:: det_state \<Rightarrow> _"
  (wp: crunch_wps do_machine_op_machine_state ignore: do_machine_op simp: crunch_simps)

lemma arch_finalise_cap_valid_machine_time[DetSchedSchedule_AI_assms]:
  "\<And>a b. arch_finalise_cap a b  \<lbrace>valid_machine_time:: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: do_machine_op_machine_state
              simp: arch_finalise_cap_def)

crunches invalidate_tlb_by_asid, set_message_info, set_mrs, retype_region
  for valid_machine_time[wp]: "valid_machine_time:: det_state \<Rightarrow> _"
  (wp: crunch_wps ignore: do_machine_op simp: crunch_simps)

lemma machine_state_detype[simp]:
  "machine_state (detype S s) = machine_state (s)"
  by (clarsimp simp: valid_machine_time_def detype_def)

crunches delete_objects
  for valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"
  (wp: crunch_wps hoare_vcg_all_lift ignore: do_machine_op)

lemma arch_perform_invocation_valid_machine_time[DetSchedSchedule_AI_assms]:
"\<And>a. arch_perform_invocation a \<lbrace>valid_machine_time:: det_state \<Rightarrow> _\<rbrace>"
  unfolding arch_perform_invocation_def
  apply (wpsimp)
       apply (wpsimp simp: perform_page_table_invocation_def wp: mapM_x_wp_inv)
      apply (wpsimp simp: perform_page_directory_invocation_def wp: )
     apply (wpsimp simp: perform_page_invocation_def wp: mapM_wp_inv hoare_drop_imps mapM_x_wp_inv)
    apply (wpsimp simp: perform_asid_control_invocation_def wp: hoare_drop_imps)
   apply (wpsimp simp: perform_asid_pool_invocation_def  wp: hoare_drop_imps hoare_vcg_all_lift)
  apply clarsimp
  done

crunches arch_get_sanitise_register_info, handle_arch_fault_reply
  for valid_machine_time[DetSchedSchedule_AI_assms]: valid_machine_time

crunches handle_hypervisor_fault, handle_reserved_irq
  for valid_machine_time: valid_machine_time

lemma valid_machine_time_getCurrentTime:
  "\<And>s x s'. valid_machine_time s \<Longrightarrow> (x, s') \<in> fst (getCurrentTime (machine_state s)) \<Longrightarrow>
            valid_machine_time_2 x s'"
  apply (clarsimp simp: valid_machine_time_def getCurrentTime_def in_monad)
  apply (rule word_of_nat_le)
  apply (rule Lattices.linorder_class.min.coboundedI1)
  apply (subst unat_minus_one)
   using kernelWCET_ticks_pos2 apply fastforce
  apply (subst unat_minus')
   using kernelWCET_ticks_pos2 apply fastforce
  apply clarsimp
  done

lemma dmo_getCurrentTime_vmt_sp[wp]:
  "\<lbrace>valid_machine_time\<rbrace>
   do_machine_op getCurrentTime
   \<lbrace>\<lambda>rv s. (cur_time s \<le> rv) \<and> (rv \<le> - kernelWCET_ticks - 1)\<rbrace>"
  apply (wpsimp simp: do_machine_op_def)
  apply (clarsimp simp: valid_machine_time_def getCurrentTime_def in_monad)
  apply (intro conjI)
   apply (clarsimp simp: min_def, intro conjI impI)
  subgoal
    apply (rule_tac order.trans, assumption)
    apply (rule_tac order.trans, assumption)
    apply (rule preorder_class.eq_refl)
    apply (subst group_add_class.diff_conv_add_uminus)
    apply (subst minus_one_norm_num)
    apply clarsimp
    apply (rule word_unat.Rep_inverse'[symmetric])
    apply (subst unat_sub)
     apply (rule order.trans[OF word_up_bound])
     apply (rule preorder_class.eq_refl)
     apply simp
    apply simp
    done
  subgoal for s
    apply (subst (asm) linorder_class.not_le)
    apply (rule_tac order.trans, assumption)
    apply (rule no_plus_overflow_unat_size2)
    apply (rule_tac order.trans)
     apply (rule add_le_mono)
      apply (rule preorder_class.eq_refl, simp)
     apply (rule unat_of_nat_closure)
    apply (rule_tac order.trans)
     apply (rule order_class.order.strict_implies_order, assumption)
    apply simp
    done
  apply (clarsimp simp: min_def, intro conjI impI)
  subgoal
    apply (rule preorder_class.eq_refl)
    apply (subst group_add_class.diff_conv_add_uminus)
    apply (subst minus_one_norm_num)
    apply clarsimp
    apply (rule word_unat.Rep_inverse')
    apply (subst unat_sub)
     apply (rule order.trans[OF word_up_bound])
     apply (rule preorder_class.eq_refl)
     apply simp
    apply simp
    done
  subgoal for s
    apply (subst (asm) linorder_class.not_le)
    apply (rule_tac b="of_nat (unat (last_machine_time (machine_state s)) +
      time_oracle (Suc (time_state (machine_state s))))" in order.trans[rotated])
     apply (rule Word_Lemmas.word_of_nat_le)
     apply (rule_tac order.trans)
      apply (rule order.strict_implies_order, assumption)
     apply (subst group_add_class.diff_conv_add_uminus)
     apply (subst minus_one_norm_num)
     apply clarsimp
     apply (subst unat_sub)
      apply (rule order.trans[OF word_up_bound])
      apply (rule preorder_class.eq_refl)
      apply simp
     apply simp
    apply (clarsimp simp: of_nat_add)
    done
  done

lemma update_time_stamp_valid_machine_time[wp]:
  "update_time_stamp \<lbrace>valid_machine_time:: det_state \<Rightarrow> _\<rbrace>"
  unfolding update_time_stamp_def
  apply (wpsimp simp: do_machine_op_def)
  apply (fastforce simp: getCurrentTime_def elim: valid_machine_time_getCurrentTime)
  done

end

global_interpretation DetSchedSchedule_AI?: DetSchedSchedule_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case
    apply (unfold_locales)
    by ((fact DetSchedSchedule_AI_assms)+ | wpsimp)+
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
  case 1 show ?case by (unfold_locales; (fact handle_hyp_fault_valid_sched handle_reserved_irq_valid_sched
                                              handle_hypervisor_fault_valid_machine_time handle_reserved_irq_valid_machine_time)?)
  qed

end
