(*
 * Copyright 2026, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDetSchedSchedule_AI
imports DetSchedSchedule_AI
begin

context Arch begin arch_global_naming

named_theorems DetSchedSchedule_AI_assms

(* trivial functions *)
crunch
  arch_post_cap_deletion, arch_post_modify_registers, arch_get_sanitise_register_info,
  arch_activate_idle_thread, handle_arch_fault_reply
  for inv[wp]: P

(* effects on last_machine_time *)
crunch
  setIRQTrigger, maskInterrupt, storeWord, freeMemory, ackDeadlineIRQ, clearMemory,
  ackInterrupt, setVSpaceRoot, readVCPUHardwareReg,
  check_export_arch_timer, writeVCPUHardwareReg, enableFpuEL01, isb, setHCR, setSCTLR,
  set_gic_vcpu_ctrl_hcr, get_gic_vcpu_ctrl_hcr, dsb, set_gic_vcpu_ctrl_lr,
  set_gic_vcpu_ctrl_apr, set_gic_vcpu_ctrl_vmcr, get_gic_vcpu_ctrl_lr, get_gic_vcpu_ctrl_apr,
  get_gic_vcpu_ctrl_vmcr, invalidateTranslationASID, readFpuState, writeFpuState, disableFpu,
  enableFpu, invalidateTranslationSingle, cleanByVA_PoU, addressTranslateS1, do_flush, sendSGI,
  doSMC_mop, get_gic_vcpu_ctrl_misr, get_gic_vcpu_ctrl_eisr1, get_gic_vcpu_ctrl_eisr0,
  deactivateInterrupt
  for machine_times[wp]: "\<lambda>s. P (last_machine_time s) (time_state s)"

lemma misc_dmo_valid_sched_pred_strong[wp]:
  "do_machine_op ackDeadlineIRQ  \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a. do_machine_op (ackInterrupt a) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b. do_machine_op (setVSpaceRoot a b) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b. do_machine_op (clearMemory a b) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b. do_machine_op (setIRQTrigger a b) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b. do_machine_op (maskInterrupt a b) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b. do_machine_op (freeMemory a b) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b. do_machine_op (storeWord a b) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a. do_machine_op (deactivateInterrupt a) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b. do_machine_op (maskInterrupt a b) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a b. do_machine_op (set_gic_vcpu_ctrl_lr a b) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "\<And>a. do_machine_op (get_gic_vcpu_ctrl_lr a) \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "do_machine_op get_gic_vcpu_ctrl_misr \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "do_machine_op get_gic_vcpu_ctrl_eisr1 \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  "do_machine_op get_gic_vcpu_ctrl_eisr0 \<lbrace>valid_sched_pred_strong Q\<rbrace>"
  by (wpsimp wp: dmo_valid_sched_pred)+

lemma set_vcpu_sc_tcbs_of[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. P (sc_tcbs_of s)\<rbrace>"
  unfolding set_vcpu_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (fastforce elim!: rsubst[where P=P]
                    simp: vs_all_heap_simps obj_at_kh_kheap_simps map_project_def
                          opt_map_def sc_tcbs_of_scs_def scs_of_kh_def sc_of_def
                   split: kernel_object.splits if_splits)
  done

lemma set_vcpu_sc_refill_cfgs_of[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. P (sc_refill_cfgs_of s)\<rbrace>"
  unfolding set_vcpu_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (fastforce elim!: rsubst[where P=P]
                    simp: vs_all_heap_simps obj_at_kh_kheap_simps map_project_def
                          opt_map_def scs_of_kh_def sc_of_def sc_refill_cfgs_of_scs_def
                   split: kernel_object.splits if_splits)
  done

lemma set_vcpu_sc_replies_of[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. P (sc_replies_of s)\<rbrace>"
  unfolding set_vcpu_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (fastforce elim!: rsubst[where P=P]
                    simp: vs_all_heap_simps obj_at_kh_kheap_simps map_project_def
                          opt_map_def scs_of_kh_def sc_of_def sc_replies_of_scs_def
                   split: kernel_object.splits if_splits)
  done

lemma set_vcpu_tcb_sts_of[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. P (tcb_sts_of s)\<rbrace>"
  unfolding set_vcpu_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (fastforce elim!: rsubst[where P=P]
                    simp: vs_all_heap_simps obj_at_kh_kheap_simps map_project_def
                          tcbs_of_kh_def opt_map_def tcb_of_def tcb_sts_of_tcbs_def
                   split: kernel_object.splits)
  done

lemma set_vcpu_tcb_scps_of[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. P (tcb_scps_of s)\<rbrace>"
  unfolding set_vcpu_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (fastforce elim!: rsubst[where P=P]
                    simp: vs_all_heap_simps obj_at_kh_kheap_simps map_project_def
                          tcbs_of_kh_def opt_map_def tcb_of_def tcb_scps_of_tcbs_def
                   split: kernel_object.splits)
  done

lemma set_vcpu_tcb_faults_of[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. P (tcb_faults_of s)\<rbrace>"
  unfolding set_vcpu_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (fastforce elim!: rsubst[where P=P]
                    simp: vs_all_heap_simps obj_at_kh_kheap_simps map_project_def
                          tcbs_of_kh_def opt_map_def tcb_of_def tcb_faults_of_tcbs_def
                   split: kernel_object.splits)
  done

crunch set_vcpu, arch_thread_set
  for consumed_time[wp]: "\<lambda>s. P (consumed_time s)"
  and time_state_of[wp]: "\<lambda>s. P (time_state_of s)"
  and cur_time[wp]: "\<lambda>s. P (cur_time s)"
  and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and last_machine_time_of[wp]: "\<lambda>s. P (last_machine_time_of s)"
  and release_queue[wp]: "\<lambda>s. P (release_queue s)"
  (wp: crunch_wps)

lemma set_vcpu_valid_sched_pred_strong[wp]:
  "set_vcpu ptr vcpu \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (rule valid_sched_pred_strong_lift; wpsimp)

lemma arch_thread_set_eps_of[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. P (eps_of s)\<rbrace>"
  by (wpsimp simp: arch_thread_set_is_thread_set)

lemma arch_thread_set_ntfns_of[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. P (ntfns_of s)\<rbrace>"
  by (wpsimp simp: arch_thread_set_is_thread_set)

lemma arch_thread_set_prios_of[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. P (prios_of s)\<rbrace>"
  apply (wpsimp simp: arch_thread_set_is_thread_set wp: thread_set_wp)
  apply (erule rsubst[where P=P])
  apply (fastforce simp: tcbs_of_kh_def get_tcb_def opt_map_def
                  split: option.splits kernel_object.splits)
  done

lemma arch_thread_set_etcbs_of[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding arch_thread_set_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (auto elim!: rsubst[where P=P]
               simp: etcbs_of_tcbs_def tcbs_of_kh_def opt_map_def get_tcb_def map_project_def
                     obj_at_def a_type_def
              split: kernel_object.splits)
  done

crunch set_asid_pool, set_vm_root, vcpu_flush
  for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps)

lemma set_asid_pool_weak_valid_sched_action[wp]:
  "set_asid_pool ptr pool \<lbrace>weak_valid_sched_action\<rbrace>"
  by (rule weak_valid_sched_action_lift; wp)

crunch set_vm_root
  for ct_not_in_q[wp]: "ct_not_in_q"
  and ct_not_in_q'[wp]: "\<lambda>s. ct_not_in_q_2 (ready_queues s) (scheduler_action s) t"
  (wp: crunch_wps simp: crunch_simps)

lemma arch_thread_set_sc_tcbs_of[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. P (sc_tcbs_of s)\<rbrace>"
  unfolding arch_thread_set_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (fastforce elim!: rsubst[where P=P]
                    simp: vs_all_heap_simps obj_at_kh_kheap_simps map_project_def
                          opt_map_def sc_tcbs_of_scs_def scs_of_kh_def sc_of_def
                   split: kernel_object.splits if_splits)
  done

lemma arch_thread_set_sc_refill_cfgs_of[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. P (sc_refill_cfgs_of s)\<rbrace>"
  unfolding arch_thread_set_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (fastforce elim!: rsubst[where P=P]
                    simp: vs_all_heap_simps obj_at_kh_kheap_simps map_project_def
                          opt_map_def scs_of_kh_def sc_of_def sc_refill_cfgs_of_scs_def
                   split: kernel_object.splits if_splits)
  done

lemma arch_thread_set_sc_replies_of[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. P (sc_replies_of s)\<rbrace>"
  unfolding arch_thread_set_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (fastforce elim!: rsubst[where P=P]
                    simp: vs_all_heap_simps obj_at_kh_kheap_simps map_project_def
                          opt_map_def scs_of_kh_def sc_of_def sc_replies_of_scs_def
                   split: kernel_object.splits if_splits)
  done

lemma arch_thread_set_tcb_sts_of[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. P (tcb_sts_of s)\<rbrace>"
  unfolding arch_thread_set_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (fastforce elim!: rsubst[where P=P]
                    simp: vs_all_heap_simps obj_at_kh_kheap_simps map_project_def
                          tcbs_of_kh_def opt_map_def tcb_of_def tcb_sts_of_tcbs_def
                   split: kernel_object.splits)
  done

lemma arch_thread_set_tcb_scps_of[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. P (tcb_scps_of s)\<rbrace>"
  unfolding arch_thread_set_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (fastforce elim!: rsubst[where P=P]
                    simp: vs_all_heap_simps obj_at_kh_kheap_simps map_project_def
                          tcbs_of_kh_def opt_map_def tcb_of_def tcb_scps_of_tcbs_def
                   split: kernel_object.splits)
  done

lemma arch_thread_set_tcb_faults_of[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. P (tcb_faults_of s)\<rbrace>"
  unfolding arch_thread_set_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (fastforce elim!: rsubst[where P=P]
                    simp: vs_all_heap_simps obj_at_kh_kheap_simps map_project_def
                          tcbs_of_kh_def opt_map_def tcb_of_def tcb_faults_of_tcbs_def
                   split: kernel_object.splits)
  done

lemma arch_thread_set_valid_sched_pred_strong[wp]:
  "arch_thread_set f tptr \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (rule valid_sched_pred_strong_lift; wpsimp)

crunch vcpu_disable, vcpu_restore, prepare_thread_delete
  for valid_sched_pred_strong[wp, DetSchedSchedule_AI_assms]: "valid_sched_pred_strong P"
  (wp: dmo_valid_sched_pred crunch_wps simp: crunch_simps)

crunch
  arch_switch_to_thread, arch_switch_to_idle_thread, arch_finalise_cap, arch_invoke_irq_control
  for valid_sched_pred_strong[wp, DetSchedSchedule_AI_assms]: "valid_sched_pred_strong P"
  (wp: dmo_valid_sched_pred crunch_wps simp: crunch_simps)

lemma handle_vm_fault_valid_sched_pred_strong[wp, DetSchedSchedule_AI_assms]:
  "handle_vm_fault thread fault_type \<lbrace>valid_sched_pred_strong P\<rbrace>"
  unfolding handle_vm_fault_def
  by (wp dmo_valid_sched_pred | simp add: Let_def | cases fault_type)+

crunch
  perform_page_table_invocation, perform_vcpu_invocation,
  perform_page_invocation, perform_asid_pool_invocation, perform_vspace_invocation,
  perform_sgi_invocation, perform_smc_invocation
  for valid_sched_misc[wp]: "valid_sched_pred_strong P"
  (wp: dmo_valid_sched_pred crunch_wps simp: crunch_simps detype_def ignore: do_machine_op)

crunch arch_perform_invocation
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

crunch set_vm_root
  for exst[wp]: "\<lambda>s. P (exst s)"
  (wp: crunch_wps whenE_wp simp: crunch_simps)

crunch switch_to_thread
  for etcb_at[wp]: "etcb_at P t"
  (wp: crunch_wps hoare_drop_imp)

crunch arch_switch_to_idle_thread
  for valid_idle[wp]: valid_idle
  (wp: crunch_wps simp: crunch_simps)

lemma set_vm_root_valid_blocked_ct_in_q[wp]:
  "set_vm_root p \<lbrace>valid_blocked and ct_in_q\<rbrace>"
  by wpsimp

lemma arch_switch_to_thread_valid_blocked [wp]:
  "arch_switch_to_thread thread \<lbrace>valid_blocked and ct_in_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding arch_switch_to_thread_def
  by wpsimp

lemma switch_to_idle_thread_ct_not_queued[wp]:
  "\<lbrace>valid_ready_qs and valid_idle\<rbrace>
   switch_to_idle_thread
   \<lbrace>\<lambda>_ s. not_queued (cur_thread s) s\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def
                   tcb_sched_action_def
         | wp)+
  apply (clarsimp simp: valid_sched_def valid_ready_qs_def valid_idle_def
                        pred_tcb_at_def obj_at_def not_queued_def pred_map_simps vs_all_heap_simps)
  apply fastforce
  done

crunch arch_switch_to_thread
  for exst[wp]: "\<lambda>s. P (exst s :: det_ext)"
  (wp: crunch_wps)

lemma astit_st_tcb_at[wp]:
  "arch_switch_to_idle_thread \<lbrace>st_tcb_at P t\<rbrace>"
  unfolding arch_switch_to_idle_thread_def
  by wpsimp

lemma stit_activatable':
  "\<lbrace>valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv . ct_in_state activatable\<rbrace>"
  apply (simp add: switch_to_idle_thread_def ct_in_state_def do_machine_op_def split_def)
  apply wpsimp
  apply (clarsimp simp: valid_idle_def ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma switch_to_idle_thread_cur_thread_idle_thread [wp]:
  "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_ s. cur_thread s = idle_thread s\<rbrace>"
  by (wp | simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def)+

lemma set_thread_state_cur_thread_valid_blocked:
  "\<lbrace>valid_blocked and (\<lambda>s. ref = cur_thread s)\<rbrace>
   set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_blocked :: det_state \<Rightarrow> _\<rbrace>"
  by (wp set_thread_state_valid_blocked_const | wps)+ clarsimp

(* FIXME: move out of arch *)
lemma set_thread_state_cur_thread_runnable_valid_sched:
  "\<lbrace>valid_sched and (\<lambda>s. ref = cur_thread s) and K (runnable ts)\<rbrace>
   set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_thread_state_valid_sched)
  apply (clarsimp simp: valid_sched_def runnable_eq, fastforce)
  done

lemma activate_thread_valid_sched:
  "activate_thread \<lbrace>valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding activate_thread_def
  by (wpsimp wp: set_thread_state_cur_thread_runnable_valid_sched gts_wp hoare_vcg_all_lift
                 get_tcb_obj_ref_wp hoare_drop_imps)

lemma arch_perform_invocation_valid_sched [wp, DetSchedSchedule_AI_assms]:
  "\<lbrace>invs and valid_machine_time and valid_sched and ct_active
    and (\<lambda>s. scheduler_action s = resume_cur_thread) and valid_arch_inv a\<rbrace>
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
  "handle_vm_fault t f \<lbrace>\<lambda>s. st_tcb_at P (cur_thread s) s\<rbrace>"
  apply (fold ct_in_state_def)
  apply (rule ct_in_state_thread_state_lift)
   apply (cases f)
    apply wpsimp+
  done

crunch arch_switch_to_thread, arch_switch_to_idle_thread
  for valid_list[wp]: valid_list

crunch handle_arch_fault_reply, handle_vm_fault, arch_post_modify_registers
  for cur_tcb[wp]: cur_tcb

(* FIXME: move out of arch *)
lemma valid_idle_thread_state_contradiction:
  "valid_idle s \<Longrightarrow> pred_map P (tcb_sts_of s) (idle_thread s) \<Longrightarrow> \<not> P (IdleThreadState) \<Longrightarrow> False"
  unfolding valid_idle_def
  by (clarsimp simp: tcb_at_kh_simps vs_all_heap_simps pred_tcb_at_def obj_at_def)

lemma switch_to_idle_thread_ct_not_in_release_q[wp]:
  "\<lbrace>valid_release_q and valid_idle\<rbrace>
   switch_to_idle_thread
   \<lbrace>\<lambda>_ s :: det_state. ct_not_in_release_q s\<rbrace>"
  unfolding switch_to_idle_thread_def
  apply wpsimp
  apply (fastforce simp: valid_release_q_def not_in_release_q_def in_queue_2_def
                  dest!: valid_idle_thread_state_contradiction)
  done

lemma arch_thread_set_sc_at_pred_n[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. P (sc_at_pred_n N proj Q p s)\<rbrace>"
  unfolding arch_thread_set_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: sc_at_pred_n_def obj_at_def split: if_splits)
  done

crunch arch_switch_to_thread, arch_switch_to_idle_thread
  for sc_at_pred_n[wp]: "\<lambda>s :: det_state. P (sc_at_pred_n N proj Q p s)"
  (simp: crunch_simps wp: crunch_wps)

lemma machine_state_detype[simp]:
  "machine_state (detype S s) = machine_state s"
  by (clarsimp simp: valid_machine_time_def detype_def)

crunch handle_hypervisor_fault, handle_reserved_irq
  for lmt[wp]: "\<lambda>s. P (last_machine_time (machine_state s))"
  and cur_time[wp]: "\<lambda>s. P (cur_time s)"
  (wp: dmo_machine_state_lift crunch_wps)

crunch handle_hypervisor_fault, handle_reserved_irq
  for valid_machine_time[wp]: valid_machine_time
  (wp: valid_machine_time_lift)

(* Note: Proving that retype_region preserves bound_sc_tcb_at is much harder *)
lemma retype_region_not_bound_sc[wp]:
  "retype_region ptr' 1 us (ArchObject aobj) dev \<lbrace>\<lambda>s. \<not> bound_sc_tcb_at P t s\<rbrace>"
  by (wpsimp simp: retype_region_def,
      clarsimp simp: pred_tcb_at_def sc_at_pred_def obj_at_def default_object_def
              split: if_splits)

lemma arch_thread_set_bound_sc_tcb_at[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. Q (bound_sc_tcb_at P t s)\<rbrace>"
  unfolding arch_thread_set_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (erule rsubst[where P=Q])
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def split: kernel_object.splits)
  done

crunch arch_perform_invocation
  for not_bound_sc_tcb_at[wp]: "\<lambda>s. \<not> bound_sc_tcb_at P t s"
  (wp: crunch_wps cur_sc_tcb_only_sym_bound_lift ignore: retype_region delete_objects
   simp: crunch_simps)

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
       by (wpsimp wp: ct_in_state_thread_state_lift vcpu_finalise_pred_tcb_at)+

lemma arch_perform_invocationE_E_inv[wp]:
  "\<lbrace>\<top>\<rbrace> arch_perform_invocation i -, \<lbrace>Q\<rbrace>"
  unfolding arch_perform_invocation_def
  by wpsimp

lemma retype_region_cur_sc_more_than_ready[wp]:
  "retype_region ptr numObjects o_bits type dev \<lbrace>cur_sc_more_than_ready\<rbrace>"
  apply (rule_tac Q'="\<lambda>_ s. \<forall>cons_time csc c_time.
                              cons_time = consumed_time s \<and> csc = cur_sc s \<and> csc \<noteq> idle_sc_ptr
                              \<and> c_time = cur_time s
                              \<longrightarrow> (cons_time \<noteq> 0
                                   \<longrightarrow> pred_map active_scrc (sc_refill_cfgs_of s) csc
                                   \<longrightarrow> pred_map (refill_ready_no_overflow_sc
                                                   cons_time c_time)  (sc_refill_cfgs_of s) csc
                                       \<and> pred_map (refill_sufficient_sc cons_time)
                                                  (sc_refill_cfgs_of s) csc)"
               in hoare_strengthen_post)
   apply (wp hoare_vcg_all_lift)
    apply (rule hoare_vcg_imp_lift'[rotated])
     apply (rule hoare_vcg_imp_lift'[rotated])
      apply (subst imp_conjR)
      apply (wp retype_region_active_sc_props)
     apply wpsimp+
   apply (clarsimp simp: cur_sc_more_than_ready_def)
  apply (clarsimp simp: cur_sc_more_than_ready_def)
  done

lemma delete_objects_cur_sc_more_than_ready[wp]:
  "delete_objects ptr pagebits \<lbrace>cur_sc_more_than_ready\<rbrace>"
  apply (rule_tac Q'="\<lambda>_ s. \<forall>cons_time csc c_time.
                              cons_time = consumed_time s \<and> csc = cur_sc s \<and> csc \<noteq> idle_sc_ptr
                              \<and> c_time = cur_time s
                              \<longrightarrow> (cons_time \<noteq> 0
                                   \<longrightarrow> pred_map active_scrc (sc_refill_cfgs_of s) csc
                                   \<longrightarrow> pred_map (refill_ready_no_overflow_sc
                                                   cons_time c_time)  (sc_refill_cfgs_of s) csc
                                       \<and> pred_map (refill_sufficient_sc cons_time)
                                                  (sc_refill_cfgs_of s) csc)"
               in hoare_strengthen_post)
   apply (wp hoare_vcg_all_lift)
    apply (rule hoare_vcg_imp_lift'[rotated])
     apply (rule hoare_vcg_imp_lift'[rotated])
      apply (subst imp_conjR)
      apply (wp delete_objects_pred_map_sc_refill_cfgs_of)
     apply wpsimp+
   apply (clarsimp simp: cur_sc_more_than_ready_def)
  apply (clarsimp simp: cur_sc_more_than_ready_def)
  done

lemma perform_asid_control_invocation_cur_sc_more_than_ready[wp]:
  "perform_asid_control_invocation iv \<lbrace>cur_sc_more_than_ready\<rbrace>"
  unfolding perform_asid_control_invocation_def
  by (wpsimp wp: hoare_drop_imp)

lemma arch_perform_invocation_cur_sc_more_than_ready[wp, DetSchedSchedule_AI_assms]:
  "arch_perform_invocation iv \<lbrace>cur_sc_more_than_ready\<rbrace>"
  unfolding arch_perform_invocation_def
  by (cases iv; wpsimp)

lemma perform_asid_control_invocation_cur_sc_in_release_q_imp_zero_consumed[wp]:
  "perform_asid_control_invocation iv \<lbrace>cur_sc_in_release_q_imp_zero_consumed\<rbrace>"
  unfolding perform_asid_control_invocation_def
  by (wpsimp wp: hoare_drop_imp)

lemma arch_perform_invocation_cur_sc_in_release_q_imp_zero_consumed[wp, DetSchedSchedule_AI_assms]:
  "arch_perform_invocation iv \<lbrace>cur_sc_in_release_q_imp_zero_consumed\<rbrace>"
  unfolding arch_perform_invocation_def
  by (cases iv; wpsimp wp: hoare_drop_imps)

crunch vcpu_update, set_vcpu
  for ct_in_state[wp]: "ct_in_state P"
  (simp: ct_in_state_def ignore: set_vcpu)

lemma arch_thread_set_ct_in_state[wp]:
  "arch_thread_set f tptr \<lbrace>ct_in_state P\<rbrace>"
  unfolding arch_thread_set_is_thread_set
  by (wpsimp wp: thread_set_ct_in_state)

lemma ct_in_state_arch_state_update[simp]:
  "ct_in_state P (arch_state_update f s) = ct_in_state P s"
  by (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)

crunch prepare_thread_delete, arch_mask_irq_signal
  for ct_in_state[wp]: "ct_in_state P"
  (wp: crunch_wps)

lemma arch_invoke_irq_handler_valid_sched_pred_strong[wp]:
  "arch_invoke_irq_handler i \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (cases i; (wpsimp split: if_splits | intro conjI impI)+)

lemma arch_mask_irq_signal_valid_sched_pred_strong[wp]:
  "arch_mask_irq_signal i \<lbrace>valid_sched_pred_strong P\<rbrace>"
  unfolding arch_mask_irq_signal_def
  by wpsimp

crunch arch_switch_to_thread, arch_switch_to_idle_thread
  for cdt_cdt_list_exst[wp]: "\<lambda>s. P (cdt s) (cdt_list_internal (exst s))"
  (wp: crunch_wps)

crunch arch_prepare_next_domain, arch_prepare_set_domain, arch_post_set_flags, handle_spurious_irq
  for valid_sched_pred_strong[wp, DetSchedSchedule_AI_assms]: "valid_sched_pred_strong P"

crunch arch_prepare_set_domain, handle_spurious_irq
  for valid_idle[wp]: valid_idle

crunch arch_prepare_next_domain
  for valid_list[wp]: valid_list

end

global_interpretation DetSchedSchedule_AI?: DetSchedSchedule_AI
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedSchedule_AI_assms)?; wpsimp?)
qed

context Arch begin arch_global_naming

lemma handle_vm_fault_not_timeout_fault[wp]:
  "\<lbrace>\<top>\<rbrace> handle_vm_fault thread ft -, \<lbrace>\<lambda>rv s. \<not> is_timeout_fault rv\<rbrace>"
  unfolding handle_vm_fault_def
  by (wpsimp simp: is_timeout_fault_def)

lemma handle_hypervisor_fault_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and st_tcb_at activatable t and scheduler_act_not t
    and not_queued t and not_in_release_q t and released_if_bound_sc_tcb_at t
    and current_time_bounded\<rbrace>
   handle_hypervisor_fault t fault
   \<lbrace>\<lambda>_ (s::'state_ext::state_ext state). valid_sched s\<rbrace>"
  supply if_split[split del]
  apply (cases fault; clarsimp)
  apply (wpsimp wp: handle_fault_valid_sched simp: getESR_def)
  apply (clarsimp simp: is_timeout_fault_def valid_fault_def)
  done

crunch vcpu_update, vgic_update_lr
  for pred_map_tcb_sts_of[wp]: "\<lambda>s. Q (pred_map P (tcb_sts_of s) t)"
  and tcb_scps_of[wp]: "\<lambda>s. Q (tcb_scps_of s)"
  and sc_refill_cfgs_of[wp]: "\<lambda>s. P (sc_refill_cfgs_of s)"
  and vcpu_update[wp]: "not_queued t"
  and not_in_release_q[wp]: "not_in_release_q t"
  and released_if_bound_sc_tcb_at[wp]: "released_if_bound_sc_tcb_at t"
  and released_sc_tcb_at[wp]: "released_sc_tcb_at sc_ptr"
  (wp: crunch_wps)

lemma dmo_isb_invs[wp]: "do_machine_op isb \<lbrace>invs\<rbrace>"
  and dmo_dsb_invs[wp]: "do_machine_op dsb \<lbrace>invs\<rbrace>"
  and dmo_setHCR_invs[wp]: "do_machine_op (setHCR w) \<lbrace>invs\<rbrace>"
  and dmo_setSCTLR_invs[wp]: "do_machine_op (setSCTLR x) \<lbrace>invs\<rbrace>"
  and dmo_getSCTLR_invs[wp]: "do_machine_op getSCTLR \<lbrace>invs\<rbrace>"
  and dmo_get_gic_vcpu_ctrl_vmcr_invs[wp]: "do_machine_op get_gic_vcpu_ctrl_vmcr \<lbrace>invs\<rbrace>"
  and dmo_set_gic_vcpu_ctrl_vmcr_invs[wp]: "\<And>x. do_machine_op (set_gic_vcpu_ctrl_vmcr x) \<lbrace>invs\<rbrace>"
  and dmo_get_gic_vcpu_ctrl_apr_invs[wp]: "do_machine_op get_gic_vcpu_ctrl_apr \<lbrace>invs\<rbrace>"
  and dmo_set_gic_vcpu_ctrl_apr_invs[wp]: "\<And>x. do_machine_op (set_gic_vcpu_ctrl_apr x) \<lbrace>invs\<rbrace>"
  and dmo_get_gic_vcpu_ctrl_lr_invs[wp]: "do_machine_op (get_gic_vcpu_ctrl_lr n) \<lbrace>invs\<rbrace>"
  and dmo_get_gic_vcpu_ctrl_misr[wp]: "do_machine_op get_gic_vcpu_ctrl_misr \<lbrace>invs\<rbrace>"
  and dmo_get_gic_vcpu_ctrl_eisr1[wp]: "do_machine_op get_gic_vcpu_ctrl_eisr1 \<lbrace>invs\<rbrace>"
  and dmo_get_gic_vcpu_ctrl_eisr0[wp]: "do_machine_op get_gic_vcpu_ctrl_eisr0 \<lbrace>invs\<rbrace>"
  and dmo_writeVCPUHardwareReg_invs[wp]: "do_machine_op (writeVCPUHardwareReg r v) \<lbrace>invs\<rbrace>"
  and dmo_readVCPUHardwareReg_invs[wp]: "do_machine_op (readVCPUHardwareReg r) \<lbrace>invs\<rbrace>"
  by (all \<open>wp dmo_invs_lift\<close>)

lemma do_machine_op_schedulable[wp]:
  "do_machine_op mop \<lbrace>\<lambda>s. P (schedulable t s)\<rbrace>"
  unfolding do_machine_op_def
  apply wpsimp
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: schedulable_def2)
  done

lemma set_vcpu_schedulable[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. P (schedulable t s)\<rbrace>"
  unfolding set_vcpu_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: schedulable_def opt_pred_def opt_map_def vs_all_heap_simps obj_at_def
                        tcbs_of_kh_def
                 split: option.splits)
  by (rename_tac ko, case_tac ko; clarsimp split: if_splits)

crunch vgic_update_lr
  for schedulable[wp]: "\<lambda>s. P (schedulable t s)"
  and arch_state[wp]: "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps)

lemma vgic_maintenance_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and scheduler_act_sane and ct_ready_if_schedulable and current_time_bounded\<rbrace>
   vgic_maintenance
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding vgic_maintenance_def get_tcb_queue_def bind_assoc
  apply (intro bind_wp[OF _ gets_sp] bind_wp[OF _ thread_get_sp] bind_wp[OF _ return_sp])
  by (wpsimp wp: handle_fault_valid_sched gts_wp hoare_vcg_all_lift hoare_drop_imps
                 hoare_vcg_if_lift2
           simp: get_gic_vcpu_ctrl_eisr1_def is_timeout_fault_def valid_fault_def)
     (fastforce dest: valid_ready_qs_etcb_eq[OF valid_sched_valid_ready_qs]
                simp: ct_in_state_def in_ready_q_def vs_all_heap_simps obj_at_kh_kheap_simps
                      schedulable_def2 ct_ready_if_schedulable_def2
               split: if_splits)

crunch vgic_maintenance
  for interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps transfer_caps_loop_pres)

lemma handle_reserved_irq_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and scheduler_act_sane
    and ct_ready_if_schedulable
    and current_time_bounded\<rbrace>
   handle_reserved_irq irq
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding handle_reserved_irq_def vppi_event_def pred_map_eq_def
  apply (cases "irq = irqVGICMaintenance")
   apply (clarsimp simp: when_def irq_vppi_event_index_def irqVGICMaintenance_def
                         irqVTimerEvent_def)
   apply wpsimp
  apply (wpsimp wp: handle_fault_valid_sched maskInterrupt_invs thread_get_wp' gts_wp' hoare_vcg_all_lift
                    hoare_vcg_imp_lift' hoare_vcg_if_lift2
              simp: getESR_def pred_map_eq_def
              cong: vcpu.fold_congs)
  apply (frule valid_sched_valid_ready_qs)
  apply (frule valid_ready_qs_etcb_eq)
  by (fastforce simp: vs_all_heap_simps in_ready_q_def obj_at_kh_kheap_simps
                      schedulable_def2 ct_ready_if_schedulable_def2
                      is_timeout_fault_def valid_fault_def)

crunch handle_hypervisor_fault
  for consumed_time_bounded[wp]: consumed_time_bounded

lemma handle_hypervisor_fault_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and ct_not_blocked_on_ntfn and ct_not_blocked_on_receive\<rbrace>
   handle_hypervisor_fault t fault
   \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  by (cases fault; wpsimp split_del: if_split)

crunch vppi_event
  for scheduler_act_sane[wp]: scheduler_act_sane
  (simp: crunch_simps wp: crunch_wps)

crunch vgic_update_lr
  for ct_in_state[wp]: "ct_in_state P"

lemma vgic_maintenance_scheduler_act_sane[wp]:
  "vgic_maintenance \<lbrace>scheduler_act_sane\<rbrace>"
  unfolding vgic_maintenance_def get_tcb_queue_def bind_assoc
  apply (intro bind_wp[OF _ gets_sp] bind_wp[OF _ thread_get_sp] bind_wp[OF _ return_sp])
  apply (wpsimp wp: handle_fault_valid_sched gts_wp hoare_vcg_all_lift hoare_drop_imps
                    hoare_vcg_if_lift2)
  apply (fastforce simp: ct_in_state_def vs_all_heap_simps obj_at_kh_kheap_simps
                         schedulable_def2  is_blocked_thread_state_defs)
  done

lemma handle_reserved_irq_scheduler_act_sane[wp]:
  "handle_reserved_irq irq \<lbrace>scheduler_act_sane\<rbrace>"
  unfolding handle_reserved_irq_def vppi_event_def get_tcb_queue_def
  apply (cases "irq = irqVGICMaintenance")
   apply (clarsimp simp: when_def irq_vppi_event_index_def irqVGICMaintenance_def
                         irqVTimerEvent_def)
   apply wpsimp
  apply clarsimp
  apply (rule hoare_when_cases)
   apply fastforce
  apply (rule bind_wp[OF _ gets_sp] bind_wp[OF _ thread_get_sp])+
  apply (wpsimp wp: gts_wp' hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_if_lift2
                    thread_get_wp)
  apply (fastforce elim!: st_tcb_weakenE
                    simp: ct_in_state_def schedulable_def2 is_blocked_thread_state_defs)
  done

lemma handle_hypervisor_fault_ct_ready_if_schedulable[wp]:
  "\<lbrace>\<lambda>s. t = cur_thread s \<and> ct_not_blocked_on_ntfn s \<and> ct_not_blocked_on_receive s
        \<and> heap_refs_inv (sc_tcbs_of s) (tcb_scps_of s)\<rbrace>
   handle_hypervisor_fault t fault
   \<lbrace>\<lambda>_ s. ct_ready_if_schedulable s\<rbrace>"
  supply if_split[split del]
  apply (cases fault; clarsimp)
  apply (wpsimp wp: handle_fault_ct_ready_if_schedulable_not_blocked_on_receive)
  done

lemma vgic_maintenance_ct_ready_if_schedulable[wp]:
  "\<lbrace>\<lambda>s. ct_ready_if_schedulable s \<and> heap_refs_inv (sc_tcbs_of s) (tcb_scps_of s)\<rbrace>
   vgic_maintenance
   \<lbrace>\<lambda>_. ct_ready_if_schedulable\<rbrace>"
  unfolding vgic_maintenance_def
  apply (clarsimp simp: get_tcb_queue_def)
  apply (intro bind_wp[OF _ gets_sp] bind_wp[OF _ thread_get_sp] bind_wp[OF _ return_sp])
  apply (wpsimp wp: handle_fault_ct_ready_if_schedulable_not_blocked_on_receive
                    gts_wp hoare_vcg_all_lift hoare_drop_imps hoare_vcg_if_lift2)
  apply (fastforce elim!: st_tcb_weakenE
                    simp: ct_in_state_def schedulable_def2 is_blocked_thread_state_defs)
  done

lemma vppi_event_ct_ready_if_schedulable[wp]:
  "\<lbrace>\<lambda>s. ct_ready_if_schedulable s \<and> heap_refs_inv (sc_tcbs_of s) (tcb_scps_of s)\<rbrace>
   vppi_event irq
   \<lbrace>\<lambda>_. ct_ready_if_schedulable\<rbrace>"
  unfolding vppi_event_def
  apply (wpsimp wp: handle_fault_ct_ready_if_schedulable_not_blocked_on_receive
                    gts_wp' hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_if_lift2
                    thread_get_wp')
  apply (fastforce elim!: st_tcb_weakenE
                    simp: ct_in_state_def schedulable_def2 is_blocked_thread_state_defs)
  done

lemma handle_reserved_irq_ct_ready_if_schedulable[wp]:
  "\<lbrace>\<lambda>s. ct_ready_if_schedulable s \<and> heap_refs_inv (sc_tcbs_of s) (tcb_scps_of s)\<rbrace>
   handle_reserved_irq irq
   \<lbrace>\<lambda>_. ct_ready_if_schedulable\<rbrace>"
  unfolding handle_reserved_irq_def
  apply (cases "irq = irqVGICMaintenance")
   apply (clarsimp simp: when_def irq_vppi_event_index_def irqVGICMaintenance_def
                         irqVTimerEvent_def)
   apply wpsimp
  apply wpsimp
  done

crunch handle_hypervisor_fault, handle_reserved_irq
  for cur_sc_more_than_ready[wp]: cur_sc_more_than_ready
  (wp: crunch_wps)

lemma handle_hypervisor_fault_cur_sc_in_release_q_imp_zero_consumed[wp]:
  "\<lbrace>cur_sc_in_release_q_imp_zero_consumed
    and ct_not_blocked_on_receive
    and ct_not_in_release_q and valid_release_q
    and (\<lambda>s. t = cur_thread s)\<rbrace>
   handle_hypervisor_fault t fault
   \<lbrace>\<lambda>_. cur_sc_in_release_q_imp_zero_consumed\<rbrace>"
  supply if_split[split del]
  apply (cases fault; clarsimp)
  apply (wpsimp wp: handle_fault_cur_sc_in_release_q_imp_zero_consumed)
  apply (clarsimp simp: vs_all_heap_simps ct_in_state_def pred_tcb_at_def obj_at_def
                        is_blocked_thread_state_defs receive_blocked_def)
  apply (rename_tac tcb, case_tac "tcb_state tcb"; clarsimp)
  done

lemma vgic_maintenance_cur_sc_in_release_q_imp_zero_consumed[wp]:
  "\<lbrace>cur_sc_in_release_q_imp_zero_consumed
    and ct_not_blocked_on_ntfn and ct_not_blocked_on_receive
    and valid_release_q\<rbrace>
   vgic_maintenance
   \<lbrace>\<lambda>_. cur_sc_in_release_q_imp_zero_consumed\<rbrace>"
  unfolding vgic_maintenance_def get_tcb_queue_def
  supply if_split[split del]
  by (wpsimp wp: thread_get_wp' gts_wp hoare_vcg_all_lift hoare_vcg_disj_lift
                 hoare_vcg_if_lift2
      | wp (once) hoare_drop_imps)+
     (clarsimp simp: schedulable_def2 vs_all_heap_simps pred_tcb_at_def obj_at_def
                     is_blocked_thread_state_defs receive_blocked_def
              split: thread_state.splits)

lemma vppi_event_cur_sc_in_release_q_imp_zero_consumed[wp]:
  "\<lbrace>cur_sc_in_release_q_imp_zero_consumed
    and ct_not_blocked_on_ntfn and ct_not_blocked_on_receive
    and valid_release_q\<rbrace>
   vppi_event irq
   \<lbrace>\<lambda>_. cur_sc_in_release_q_imp_zero_consumed\<rbrace>"
  unfolding vppi_event_def
  apply (wpsimp wp: gts_wp' hoare_vcg_imp_lift' hoare_vcg_if_lift2 thread_get_wp')
  apply (clarsimp simp: schedulable_def2 vs_all_heap_simps obj_at_def
                        is_blocked_thread_state_defs receive_blocked_def)
  apply (rename_tac tcb a bool ref' sc n, case_tac "tcb_state tcb"; clarsimp)
  done

lemma handle_reserved_irq_cur_sc_in_release_q_imp_zero_consumed[wp]:
  "\<lbrace>cur_sc_in_release_q_imp_zero_consumed
    and ct_not_blocked_on_ntfn and ct_not_blocked_on_receive
    and valid_release_q\<rbrace>
   handle_reserved_irq irq
   \<lbrace>\<lambda>_. cur_sc_in_release_q_imp_zero_consumed\<rbrace>"
  unfolding handle_reserved_irq_def
  apply (cases "irq = irqVGICMaintenance")
   apply (clarsimp simp: when_def irq_vppi_event_index_def irqVGICMaintenance_def
                         irqVTimerEvent_def)
   apply wpsimp
  apply wpsimp
  done

lemma vgic_maintenance_vmt[wp]:
  "vgic_maintenance \<lbrace>\<lambda>s. P (last_machine_time_of s) (cur_time s)\<rbrace>"
  unfolding vgic_maintenance_def
  by (wpsimp wp: thread_get_wp' hoare_drop_imps)

lemma vppi_event_vmt[wp]:
  "vppi_event irq \<lbrace>\<lambda>s. P (last_machine_time_of s) (cur_time s)\<rbrace>"
  unfolding vppi_event_def
  by (wpsimp wp: thread_get_wp' hoare_drop_imps)

lemma handle_reserved_irq_vmt[wp]:
  "handle_reserved_irq irq \<lbrace>\<lambda>s. P (last_machine_time_of s) (cur_time s)\<rbrace>"
  unfolding handle_reserved_irq_def
  apply (cases "irq = irqVGICMaintenance")
   apply (clarsimp simp: when_def irq_vppi_event_index_def irqVGICMaintenance_def
                         irqVTimerEvent_def)
   apply wpsimp
  apply wpsimp
  done

lemma vgic_maintenance_pnt[wp]:
  "vgic_maintenance \<lbrace>\<lambda>s. P (last_machine_time_of s) (time_state_of s)\<rbrace>"
  unfolding vgic_maintenance_def
  by (wpsimp wp: thread_get_wp' hoare_drop_imps)

lemma vppi_event_pnt[wp]:
  "vppi_event irq \<lbrace>\<lambda>s. P (last_machine_time_of s) (time_state_of s)\<rbrace>"
  unfolding vppi_event_def
  by (wpsimp wp: thread_get_wp' hoare_drop_imps)

lemma handle_reserved_irq_pnt[wp]:
  "handle_reserved_irq irq \<lbrace>\<lambda>s. P (last_machine_time_of s) (time_state_of s)\<rbrace>"
  unfolding handle_reserved_irq_def
  apply (cases "irq = irqVGICMaintenance")
   apply (clarsimp simp: when_def irq_vppi_event_index_def irqVGICMaintenance_def
                         irqVTimerEvent_def)
   apply wpsimp
  apply wpsimp
  done

crunch handle_reserved_irq
  for cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  and is_active_sc[wp]: "\<lambda>s. P (is_active_sc sc_ptr s)"
  (wp: crunch_wps)

end

global_interpretation DetSchedSchedule_AI_det_ext?: DetSchedSchedule_AI_det_ext
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedSchedule_AI_assms)?; wpsimp?)
qed

global_interpretation DetSchedSchedule_AI_handle_hypervisor_fault?: DetSchedSchedule_AI_handle_hypervisor_fault
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (solves wpsimp)?)
qed

global_interpretation DetSchedSchedule_AI_handle_hypervisor_fault_det_ext?: DetSchedSchedule_AI_handle_hypervisor_fault_det_ext
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; wpsimp)
qed

end
