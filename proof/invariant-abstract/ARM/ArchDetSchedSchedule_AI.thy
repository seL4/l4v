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

(* trivial functions *)
crunches arch_post_cap_deletion,
         prepare_thread_delete,
         arch_post_modify_registers,
         arch_get_sanitise_register_info,
         arch_activate_idle_thread, handle_arch_fault_reply
  for inv[wp]: P

(* effects on last_machine_time *)
crunches setHardwareASID, set_current_pd, invalidateLocalTLB_ASID, cleanByVA, invalidateByVA,
  invalidateL2Range, cleanInvalByVA, cleanInvalidateL2Range, isb, branchFlush, invalidateByVA_I,
  cleanByVA_PoU, cleanL2Range, cleanCacheRange_PoC, branchFlushRange, invalidateCacheRange_I,
  cleanCacheRange_PoU, cleanInvalidateCacheRange_RAM, cleanInvalidateCacheRange_RAM,
  invalidateCacheRange_RAM, cleanCacheRange_RAM, setIRQTrigger, maskInterrupt, clearExMonitor,
  invalidateLocalTLB_VAASID, do_flush, storeWord, freeMemory, ackDeadlineIRQ, clearMemory,
  getDFSR, getFAR, getIFSR
  for machine_times[wp]: "\<lambda>s. P (last_machine_time s) (time_state s)"
  (simp: isb_def writeTTBR0_def wp: crunch_wps
   ignore_del: setHardwareASID invalidateLocalTLB_ASID cleanByVA invalidateL2Range invalidateByVA
               cleanInvalByVA cleanInvalidateL2Range branchFlush invalidateByVA_I cleanL2Range
               invalidateLocalTLB_VAASID)

lemma misc_dmo_valid_sched_pred_strong[wp]:
  "do_machine_op cleanCaches_PoU \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "do_machine_op ackDeadlineIRQ  \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "do_machine_op clearExMonitor \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a. do_machine_op (set_current_pd a) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a. do_machine_op (invalidateLocalTLB_ASID a) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a. do_machine_op (invalidateLocalTLB_VAASID a) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a. do_machine_op (setHardwareASID a) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a. do_machine_op (ackInterrupt a) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b. do_machine_op (clearMemory a b) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b. do_machine_op (setIRQTrigger a b) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b. do_machine_op (maskInterrupt a b) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b. do_machine_op (cleanByVA_PoU a b) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b. do_machine_op (freeMemory a b) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b. do_machine_op (storeWord a b) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b c. do_machine_op (cleanCacheRange_PoU a b c) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b c d. do_machine_op (do_flush a b c d) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b. do_machine_op (do set_current_pd (addrFromPPtr a);
                            setHardwareASID b
                         od) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  apply (wpsimp wp: dmo_valid_sched_pred )+
  done

crunches arch_switch_to_thread,
         arch_switch_to_idle_thread,
         arch_finalise_cap,
         arch_invoke_irq_control,
         handle_vm_fault
  for valid_sched_pred_strong[wp, DetSchedSchedule_AI_assms]: "valid_sched_pred_strong P"
  (wp: dmo_valid_sched_pred crunch_wps simp: crunch_simps)

crunches
  perform_page_table_invocation, perform_page_directory_invocation,
  perform_page_invocation, perform_asid_pool_invocation
  for valid_sched_misc[wp]: "valid_sched_pred_strong P"
  (wp: dmo_valid_sched_pred crunch_wps simp: crunch_simps detype_def ignore: do_machine_op)

crunches arch_perform_invocation
  for valid_sched_misc[wp, DetSchedSchedule_AI_assms]:
        "\<lambda>s. P (consumed_time s) (cur_time s) (cur_domain s) (cur_thread s)
               (cur_sc s) (idle_thread s) (ready_queues s) (release_queue s)
               (scheduler_action s) (last_machine_time_of s) (time_state_of s)"
  (wp: dmo_valid_sched_pred crunch_wps simp: crunch_simps detype_def ignore: do_machine_op)

lemma switch_to_idle_thread_ct_in_cur_domain [wp]:
  "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  by (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def do_machine_op_def
                split_def
      | wp
      | simp add: ct_in_cur_domain_def)+

crunch exst[wp]: set_vm_root "\<lambda>s. P (exst s)"
  (wp: crunch_wps whenE_wp simp: crunch_simps)

crunch etcb_at[wp]: switch_to_thread "etcb_at P t"
  (wp: hoare_drop_imp)

crunch valid_idle [wp]:
  arch_switch_to_idle_thread "valid_idle"
  (wp: crunch_wps simp: crunch_simps)

lemma set_vm_root_valid_blocked_ct_in_q [wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> set_vm_root p \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  by (wp | wpc | auto)+

lemma arch_switch_to_thread_valid_blocked [wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> arch_switch_to_thread thread \<lbrace>\<lambda>_. valid_blocked and ct_in_q::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply (rule hoare_seq_ext)+
  apply wpsimp+
  done

lemma switch_to_idle_thread_ct_not_queued [wp]:
  "\<lbrace>valid_ready_qs and valid_idle\<rbrace>
     switch_to_idle_thread
   \<lbrace>\<lambda>rv s. not_queued (cur_thread s) s\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def
                   tcb_sched_action_def | wp)+
  apply (clarsimp simp: valid_sched_def valid_ready_qs_def valid_idle_def
                        pred_tcb_at_def obj_at_def not_queued_def pred_map_simps vs_all_heap_simps
         , fastforce)
  done

crunch exst [wp]: arch_switch_to_thread "\<lambda>s. P (exst s :: det_ext)"
  (ignore: clearExMonitor)

lemma astit_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (simp add: arch_switch_to_idle_thread_def)
  by (wpsimp)

lemma stit_activatable':
  "\<lbrace>valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv . ct_in_state activatable\<rbrace>"
  apply (simp add: switch_to_idle_thread_def ct_in_state_def do_machine_op_def split_def)
  apply wpsimp
  apply (clarsimp simp: valid_idle_def ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma switch_to_idle_thread_cur_thread_idle_thread [wp]:
  "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_ s. cur_thread s = idle_thread s\<rbrace>"
  by (wp | simp add:switch_to_idle_thread_def arch_switch_to_idle_thread_def)+

lemma set_thread_state_cur_thread_valid_blocked:
  "\<lbrace>valid_blocked and (\<lambda>s. ref = cur_thread s)\<rbrace> set_thread_state ref ts
  \<lbrace>\<lambda>_. valid_blocked :: det_state \<Rightarrow> _\<rbrace>"
  by (wp set_thread_state_valid_blocked_const | wps)+ clarsimp

(* FIXME: move out of arch *)
lemma set_thread_state_cur_thread_runnable_valid_sched:
  "\<lbrace>valid_sched and (\<lambda>s. ref = cur_thread s) and K (runnable ts)\<rbrace>
   set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_thread_state_valid_sched)
  by (clarsimp simp: valid_sched_def runnable_eq, fastforce)

lemma activate_thread_valid_sched:
  "\<lbrace>valid_sched\<rbrace>
   activate_thread
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding activate_thread_def
  by (wpsimp wp: set_thread_state_cur_thread_runnable_valid_sched gts_wp hoare_vcg_all_lift
                 get_tcb_obj_ref_wp hoare_drop_imps)

lemma arch_perform_invocation_valid_sched [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>invs and valid_sched and valid_machine_time and ct_active and (\<lambda>s. scheduler_action s = resume_cur_thread) and
    valid_arch_inv a\<rbrace>
     arch_perform_invocation a
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (cases a, simp_all add: arch_perform_invocation_def)
      apply (wpsimp simp: valid_arch_inv_def invs_valid_idle
                      wp: perform_asid_control_invocation_valid_sched)+
  done

lemma arch_perform_invocation_cur_sc_active[wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>cur_sc_active and invs and ct_active and schact_is_rct and valid_arch_inv i\<rbrace>
   arch_perform_invocation i
   \<lbrace>\<lambda>_. cur_sc_active\<rbrace>"
  apply (cases i, simp_all add: arch_perform_invocation_def)
      apply (wpsimp simp: valid_arch_inv_def invs_valid_idle
                      wp: perform_asid_control_invocation_cur_sc_active)+
  done

lemma handle_vm_fault_st_tcb_cur_thread [wp]:
  "\<lbrace> \<lambda>s. st_tcb_at P (cur_thread s) s \<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_ s. st_tcb_at P (cur_thread s) s \<rbrace>"
  apply (fold ct_in_state_def)
  apply (rule ct_in_state_thread_state_lift)
   apply (cases f)
    apply (wp|simp)+
  done

crunches arch_switch_to_thread, arch_switch_to_idle_thread
  for valid_list [wp]: "valid_list"

crunch cur_tcb [wp]: handle_arch_fault_reply, handle_vm_fault, arch_post_modify_registers cur_tcb

declare make_arch_fault_msg_inv[DetSchedSchedule_AI_assms]

(* FIXME: move out of arch *)
lemma valid_idle_thread_state_contradiction:
  "valid_idle s \<Longrightarrow> pred_map P (tcb_sts_of s) (idle_thread s) \<Longrightarrow> \<not> P (IdleThreadState) \<Longrightarrow> False"
  unfolding valid_idle_def
  by (clarsimp simp: tcb_at_kh_simps vs_all_heap_simps pred_tcb_at_def obj_at_def)

lemma switch_to_idle_thread_ct_not_in_release_q[wp]:
    "\<lbrace>valid_release_q and valid_idle\<rbrace>
      switch_to_idle_thread
     \<lbrace>\<lambda>rv s::det_state. ct_not_in_release_q s\<rbrace>"
  apply (clarsimp simp: switch_to_idle_thread_def)
  apply wpsimp
  by (fastforce simp: valid_release_q_def not_in_release_q_def in_queue_2_def dest!: valid_idle_thread_state_contradiction)

crunches arch_switch_to_thread, arch_switch_to_idle_thread
  for sc_at_period[wp]: "sc_at_period P p::det_state \<Rightarrow> _"
  (simp: crunch_simps)

lemma machine_state_detype[simp]:
  "machine_state (detype S s) = machine_state s"
  by (clarsimp simp: valid_machine_time_def detype_def)

crunches handle_hypervisor_fault, handle_reserved_irq
  for valid_machine_time: valid_machine_time

(* Note: Proving that retype_region preserves bound_sc_tcb_at is much harder *)
lemma retype_region_not_bound_sc[wp]:
  "\<lbrace>\<lambda>s. \<not> bound_sc_tcb_at P t s\<rbrace>
   retype_region ptr' 1 us (ArchObject aobj) dev
   \<lbrace>\<lambda>rv (s). \<not> bound_sc_tcb_at P t s\<rbrace>"
  by (wpsimp simp: retype_region_def,
         clarsimp simp: pred_tcb_at_def sc_at_pred_def obj_at_def default_object_def
                 split: if_splits)

crunches arch_perform_invocation
  for not_bound_sc_tcb_at[wp]: "(\<lambda>s. \<not> bound_sc_tcb_at P t s)"
  (wp: crunch_wps cur_sc_tcb_only_sym_bound_lift ignore: retype_region delete_objects)

lemma arch_perform_invocation_cur_sc_tcb_only_sym_bound[DetSchedSchedule_AI_assms]:
  "arch_perform_invocation i \<lbrace>cur_sc_tcb_only_sym_bound\<rbrace>"
  by (wpsimp wp: cur_sc_tcb_only_sym_bound_lift)

lemma arch_perform_invocation_bound_sc_obj_tcb_at[DetSchedSchedule_AI_assms]:
  "\<lbrace>\<lambda>s. bound_sc_obj_tcb_at (P (cur_time s)) t s
        \<and> ex_nonz_cap_to t s \<and> invs s \<and> ct_active s \<and> valid_arch_inv i s
        \<and> scheduler_action s = resume_cur_thread\<rbrace>
   arch_perform_invocation i
   \<lbrace>\<lambda>_ s. bound_sc_obj_tcb_at (P (cur_time s)) t s\<rbrace>"
  unfolding arch_perform_invocation_def
  by (cases i; wpsimp simp: valid_arch_inv_def)

lemma arch_finalise_cap_ct_in_state:
  "arch_finalise_cap c x \<lbrace>ct_in_state P :: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac c; case_tac x; simp add: arch_finalise_cap_def)
  by (wpsimp wp: ct_in_state_thread_state_lift)+

lemma kernel_irq_timer_kernel_IRQ[simp]:
  "kernel_irq_timer \<notin> non_kernel_IRQs"
  by (simp add: non_kernel_IRQs_def)

lemma arch_perform_invocationE_E_inv[wp]:
  "\<lbrace>\<top>\<rbrace> arch_perform_invocation i -, \<lbrace>Q\<rbrace>"
   unfolding arch_perform_invocation_def by wpsimp

lemma retype_region_cur_sc_more_than_ready [wp]:
  "retype_region ptr numObjects o_bits type dev \<lbrace>cur_sc_more_than_ready\<rbrace>"
  apply (rule_tac Q="\<lambda>_ s. \<forall>cons_time csc c_time.
    cons_time = consumed_time s \<and> csc = cur_sc s \<and> csc \<noteq> idle_sc_ptr \<and> c_time = cur_time s \<longrightarrow>
    (cons_time \<noteq> 0
    \<longrightarrow> pred_map active_scrc (sc_refill_cfgs_of s) csc
    \<longrightarrow> pred_map (refill_ready_no_overflow_sc cons_time c_time) (sc_refill_cfgs_of s) csc
         \<and> pred_map (refill_sufficient_sc cons_time) (sc_refill_cfgs_of s) csc)" in hoare_strengthen_post)
   apply (wp hoare_vcg_all_lift)
    apply (rule hoare_vcg_imp_lift'[rotated])
     apply (rule hoare_vcg_imp_lift'[rotated])
      apply (subst imp_conjR)
      apply (wp retype_region_active_sc_props)
     apply wpsimp+
   apply (clarsimp simp: cur_sc_more_than_ready_def)
  apply (clarsimp simp: cur_sc_more_than_ready_def)
  done

lemma delete_objects_cur_sc_more_than_ready [wp]:
  "delete_objects ptr pagebits \<lbrace>cur_sc_more_than_ready\<rbrace>"
  apply (rule_tac Q="\<lambda>_ s. \<forall>cons_time csc c_time.
    cons_time = consumed_time s \<and> csc = cur_sc s \<and> csc \<noteq> idle_sc_ptr \<and> c_time = cur_time s \<longrightarrow>
    (cons_time \<noteq> 0
    \<longrightarrow> pred_map active_scrc (sc_refill_cfgs_of s) csc
    \<longrightarrow> pred_map (refill_ready_no_overflow_sc cons_time c_time) (sc_refill_cfgs_of s) csc
         \<and> pred_map (refill_sufficient_sc cons_time) (sc_refill_cfgs_of s) csc)" in hoare_strengthen_post)
   apply (wp hoare_vcg_all_lift)
    apply (rule hoare_vcg_imp_lift'[rotated])
     apply (rule hoare_vcg_imp_lift'[rotated])
      apply (subst imp_conjR)
      apply (wp delete_objects_pred_map_sc_refill_cfgs_of)
     apply wpsimp+
   apply (clarsimp simp: cur_sc_more_than_ready_def)
  apply (clarsimp simp: cur_sc_more_than_ready_def)
  done

lemma perform_asid_control_invocation_cur_sc_more_than_ready [wp]:
  "perform_asid_control_invocation iv \<lbrace>cur_sc_more_than_ready\<rbrace>"
  unfolding perform_asid_control_invocation_def
  by (wpsimp wp: hoare_drop_imp)

lemma arch_perform_invocation_cur_sc_more_than_ready [wp, DetSchedSchedule_AI_assms]:
  "arch_perform_invocation iv \<lbrace>cur_sc_more_than_ready\<rbrace>"
  unfolding arch_perform_invocation_def
  by (cases iv; wpsimp)

lemma perform_asid_control_invocation_cur_sc_in_release_q_imp_zero_consumed [wp]:
  "perform_asid_control_invocation iv \<lbrace>cur_sc_in_release_q_imp_zero_consumed\<rbrace>"
  unfolding perform_asid_control_invocation_def
  by (wpsimp wp: hoare_drop_imp)

lemma arch_perform_invocation_cur_sc_in_release_q_imp_zero_consumed [wp, DetSchedSchedule_AI_assms]:
  "arch_perform_invocation iv \<lbrace>cur_sc_in_release_q_imp_zero_consumed\<rbrace>"
  unfolding arch_perform_invocation_def
  by (cases iv; wpsimp wp: hoare_drop_imps)

crunches arch_invoke_irq_handler, arch_mask_irq_signal, handle_reserved_irq
  for ct_in_state[wp]: "ct_in_state P"

lemma arch_invoke_irq_handler_valid_sched_pred_strong[wp]:
  "arch_invoke_irq_handler i \<lbrace> valid_sched_pred_strong P \<rbrace>"
  by (cases i; wpsimp)

lemma arch_mask_irq_signal_valid_sched_pred_strong[wp]:
  "arch_mask_irq_signal i \<lbrace> valid_sched_pred_strong P \<rbrace>"
  unfolding arch_mask_irq_signal_def by wpsimp

crunches arch_switch_to_thread, arch_switch_to_idle_thread
for cdt_cdt_list_exst [wp]:  "\<lambda>s. P (cdt s) (cdt_list_internal (exst s))"

lemma handle_hyp_fault_trivial[wp]:
  "handle_hypervisor_fault t fault \<lbrace>Q\<rbrace>"
  by (cases fault; wpsimp)

end

global_interpretation DetSchedSchedule_AI?: DetSchedSchedule_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedSchedule_AI_assms)?; wpsimp)
  qed

global_interpretation DetSchedSchedule_AI_det_ext?: DetSchedSchedule_AI_det_ext
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedSchedule_AI_assms)?; wpsimp)
qed

context Arch begin global_naming ARM

lemma handle_reserved_irq_trivial[wp]:
  "handle_reserved_irq irq \<lbrace>Q\<rbrace>"
  unfolding handle_reserved_irq_def
  by (wpsimp)

lemma handle_vm_fault_not_timeout_fault[wp]:
  "\<lbrace>\<top>\<rbrace> handle_vm_fault thread ft -,\<lbrace>\<lambda>rv s. \<not> is_timeout_fault rv\<rbrace>"
  apply (cases ft, simp_all)
   apply (wp no_irq_getDFSR no_irq_getIFSR | simp add: is_timeout_fault_def)+
  done

end

global_interpretation DetSchedSchedule_AI_handle_hypervisor_fault?: DetSchedSchedule_AI_handle_hypervisor_fault
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; wpsimp)
  qed

global_interpretation DetSchedSchedule_AI_handle_hypervisor_fault_det_ext?: DetSchedSchedule_AI_handle_hypervisor_fault_det_ext
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; wpsimp)
  qed

end
