(*
 * Copyright 2025, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchFPU_AI
imports ArchDetSchedSchedule_AI
begin

context Arch begin arch_global_naming

section \<open>cur_fpu_in_cur_domain\<close>

text \<open>Show that the TCB that owns the current FPU is in the current domain.\<close>

definition cur_fpu_in_cur_domain :: "det_ext state \<Rightarrow> bool" where
  "cur_fpu_in_cur_domain s \<equiv> none_top (\<lambda>t. in_cur_domain t s) (arm_current_fpu_owner (arch_state s))"

lemma cur_fpu_in_cur_domain_lift_strong:
  assumes [wp]: "\<And>P. f \<lbrace>\<lambda>s. P (arm_current_fpu_owner (arch_state s))\<rbrace>"
                "\<And>P. f \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
                "\<And>P t. f \<lbrace>etcb_at (\<lambda>t. P (etcb_domain t)) t\<rbrace>"
  shows "f \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
  unfolding cur_fpu_in_cur_domain_def in_cur_domain_def
  by (wp_pre, wps, wpsimp wp: valid_none_top_post_wp)

lemma cur_fpu_in_cur_domain_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arm_current_fpu_owner (arch_state s))\<rbrace>"
          "\<And>P. f \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
          "\<And>P. f \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  shows "f \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
 by (rule cur_fpu_in_cur_domain_lift_strong assms)+

lemma cur_fpu_in_cur_domain_current_fpu_owner_update[simp]:
  "cur_fpu_in_cur_domain (s\<lparr>arch_state := arch_state s\<lparr>arm_current_fpu_owner := new_owner\<rparr>\<rparr>)
   = none_top (\<lambda>t. in_cur_domain t s) new_owner"
  by (clarsimp simp: cur_fpu_in_cur_domain_def split: option.splits)

\<comment> \<open>FIXME: defining cur_fpu_in_cur_domain with projections would remove the need for these\<close>
lemma cur_fpu_in_cur_domain_updates[simp]:
  "\<And>f. cur_fpu_in_cur_domain (trans_state f s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (cur_thread_update f s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (ready_queues_update f s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (machine_state_update f s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (cdt_update f s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (cdt_list_update f s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (work_units_completed_update f s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (interrupt_states_update f s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (is_original_cap_update f s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (arch_state_update (arm_asid_table_update f) s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (s\<lparr>arch_state := (arm_asid_table_update f) (arch_state s)\<rparr>) = cur_fpu_in_cur_domain s" \<comment> \<open>FIXME: previous line doesn't work for this, can it be generalised?\<close>
  "\<And>f. cur_fpu_in_cur_domain (reprogram_timer_update f s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (cur_sc_update f s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (consumed_time_update f s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (release_queue_update f s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (domain_time_update f s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (cur_time_update f s) = cur_fpu_in_cur_domain s"
  by (auto simp: cur_fpu_in_cur_domain_def)

\<comment> \<open>schedule\<close>

crunch arch_thread_set, load_fpu_state
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  and arm_current_fpu_owner[wp]: "\<lambda>s. P (arm_current_fpu_owner (arch_state s))"
  (wp: cur_fpu_in_cur_domain_lift)

crunch arch_thread_set, load_fpu_state, save_fpu_state, do_machine_op
  for in_cur_domain[wp]: "in_cur_domain t"
  (ignore: arch_thread_set as_user)

lemma switch_local_fpu_owner_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_fpu_in_cur_domain s \<and> none_top (\<lambda>t. in_cur_domain t s) new_owner\<rbrace>
   switch_local_fpu_owner new_owner
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding switch_local_fpu_owner_def set_arm_current_fpu_owner_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' valid_none_top_post_wp)
  by auto

lemma lazy_fpu_restore_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>cur_fpu_in_cur_domain and in_cur_domain thread_ptr\<rbrace>
   lazy_fpu_restore thread_ptr
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding lazy_fpu_restore_def
  by (wpsimp wp: thread_get_wp')

crunch set_vm_root, vcpu_switch
  for arm_current_fpu_owner[wp]: "\<lambda>s. P (arm_current_fpu_owner (arch_state s))"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift)

lemma arch_switch_to_thread_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>cur_fpu_in_cur_domain and in_cur_domain t\<rbrace>
   arch_switch_to_thread t
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding arch_switch_to_thread_def
  by (wpsimp | wps)+

crunch tcb_sched_action
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps)

lemma guarded_switch_to_cur_fpu_in_cur_domain[wp]:
  "guarded_switch_to t \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
  unfolding guarded_switch_to_def switch_to_thread_def
  apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: get_tcb_def in_cur_domain_def etcb_at'_def vs_all_heap_simps
                        obj_at_kh_kheap_simps)
  done

crunch choose_thread
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps)

lemma next_domain_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. arm_current_fpu_owner (arch_state s) = None\<rbrace> next_domain \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding next_domain_def Let_def
  by (wpsimp wp: dxo_wp_weak simp: cur_fpu_in_cur_domain_def)

lemma switch_local_fpu_owner_arm_current_fpu_owner_None[wp]:
  "\<lbrace>\<top>\<rbrace> switch_local_fpu_owner None \<lbrace>\<lambda>_ s. arm_current_fpu_owner (arch_state s) = None\<rbrace>"
  unfolding switch_local_fpu_owner_def set_arm_current_fpu_owner_def
  by wpsimp

crunch set_scheduler_action
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift)

lemma schedule_choose_new_thread_cur_fpu_in_cur_domain[wp]:
  "schedule_choose_new_thread \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
  unfolding schedule_choose_new_thread_def arch_prepare_next_domain_def
  by wpsimp

lemma update_sched_context_cur_fpu_in_cur_domain[wp]:
  "update_sched_context ptr f \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: in_cur_domain_def cur_fpu_in_cur_domain_def etcb_at'_def vs_all_heap_simps)
  done

crunch sc_and_timer, check_domain_time, awaken
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps simp: crunch_simps)

crunch check_domain_time
  for st_tcb_at[wp]: "st_tcb_at P t"
  and st_tcb_at_cur_thread[wp]: "\<lambda>s. st_tcb_at P (cur_thread s) s"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and valid_ready_qs[wp]: valid_ready_qs
  and released_sc_tcb_at[wp]: "released_sc_tcb_at t"
  and cur_time[wp]: "\<lambda>s. P (cur_time s)"
  and ct_released[wp]: ct_released
  (wp: crunch_wps)

crunch awaken
  for st_tcb_at[wp]: "st_tcb_at P t"
  and st_tcb_at_cur_thread[wp]: "\<lambda>s. st_tcb_at P (cur_thread s) s"
  (wp: crunch_wps)

crunch schedule
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps)

\<comment> \<open>handle_interrupt\<close>

crunch send_signal, set_extra_badge, handle_reserved_irq
  for etcb_at[wp]: "etcb_at P t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and arm_current_fpu_owner[wp]: "\<lambda>s. P (arm_current_fpu_owner (arch_state s))"
  (wp: crunch_wps transfer_caps_loop_pres dxo_wp_weak
   simp: crunch_simps etcb_of_def)

crunch handle_interrupt
  for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and etcb_at_domain[wp]: "etcb_at (\<lambda>t. P (etcb_domain t)) t"
  and arm_current_fpu_owner[wp]: "\<lambda>s. P (arm_current_fpu_owner (arch_state s))"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift_strong)


\<comment> \<open>handle_event\<close>

lemma retype_region_valid_cur_fpu[wp]:
  "retype_region ptr numObjects o_bits type dev \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
  unfolding retype_region_def
  apply (wpsimp simp_del: fun_upd_apply simp: foldr_fun_upd_value)
  by (auto simp: cur_fpu_in_cur_domain_def in_cur_domain_def etcb_at'_def
                 default_object_def default_tcb_def vs_all_heap_simps
          split: option.splits apiobject_type.splits)

crunch do_machine_op, create_cap, init_arch_objects, set_cap
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift crunch_wps simp: crunch_simps)

lemma delete_objects_valid_cur_fpu[wp]:
  "delete_objects ptr bits \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
  unfolding delete_objects_def
  apply wpsimp
   apply (rule hoare_strengthen_post, rule do_machine_op_cur_fpu_in_cur_domain)
  by (auto simp: cur_fpu_in_cur_domain_def in_cur_domain_def etcb_at'_def detype_def vs_all_heap_simps
          split: option.splits)

crunch invoke_untyped
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps mapME_x_wp' preemption_point_inv' simp: crunch_simps mapM_x_def_bak) \<comment> \<open>FIXME: change invoke_untyped to use mapM_x\<close>

crunch cap_move, suspend, delete_asid_pool, unmap_page, cancel_badged_sends
  for etcb_at[wp]: "etcb_at P t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps filterM_mapM)

crunch
  cap_insert, cap_move, cap_swap, set_thread_state, unbind_maybe_notification, unbind_notification,
  cancel_all_ipc, suspend, cancel_all_signals, delete_asid_pool, unmap_page, delete_asid,
  unmap_page_table, cancel_badged_sends, empty_slot, dissociate_vcpu_tcb, associate_vcpu_tcb
  for arm_current_fpu_owner[wp]: "\<lambda>s. P (arm_current_fpu_owner (arch_state s))"
  and etcb_at_domain[wp]: "etcb_at (\<lambda>t. P (etcb_domain t)) t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift_strong crunch_wps dxo_wp_weak
   simp: crunch_simps filterM_mapM)

lemma thread_set_no_etcb_change_cur_fpu_in_cur_domain:
  "(\<And>P tcb. P (tcb_domain (f tcb)) = (P (tcb_domain tcb) :: bool))
   \<Longrightarrow> thread_set f t' \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
  by (wpsimp wp: cur_fpu_in_cur_domain_lift_strong thread_set_etcb_domain)

crunch sched_context_bind_tcb
  for etcb_at_domain[wp]: "etcb_at (\<lambda>t. P (etcb_domain t)) t"
  (wp: crunch_wps ignore: thread_set)

crunch sched_context_bind_tcb
  for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (simp: crunch_simps filterM_mapM wp: cur_fpu_in_cur_domain_lift_strong)

crunch
  cancel_ipc, reply_remove, sched_context_maybe_unbind_ntfn, unbind_from_sc,
  sched_context_unbind_all_tcbs, sched_context_unbind_ntfn, sched_context_unbind_reply,
  sched_context_unbind_yield_from, sched_context_unbind_tcb, sched_context_bind_tcb
  for arm_current_fpu_owner[wp]: "\<lambda>s. P (arm_current_fpu_owner (arch_state s))"
  and etcb_at_domain[wp]: "etcb_at (\<lambda>t. P (etcb_domain t)) t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift_strong crunch_wps dxo_wp_weak
   simp: crunch_simps filterM_mapM)

crunch invoke_cnode
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps preemption_point_inv' cap_revoke_preservation simp: crunch_simps)

crunch cancel_ipc, set_mcpriority, set_priority, bind_notification
  for arm_current_fpu_owner[wp]: "\<lambda>s. P (arm_current_fpu_owner (arch_state s))"
  and etcb_at_domain[wp]: "etcb_at (\<lambda>t. P (etcb_domain t)) t"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps cur_fpu_in_cur_domain_lift_strong thread_set_etcb_domain)

lemma option_update_thread_no_etcb_change_cur_fpu_in_cur_domain:
  "(\<And>P val tcb. P (tcb_domain (f val tcb)) = (P (tcb_domain tcb) :: bool))
   \<Longrightarrow> option_update_thread t f opt \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
  unfolding option_update_thread_def
  apply (wpsimp wp: cur_fpu_in_cur_domain_lift_strong thread_set_wp)
   apply (clarsimp simp: etcb_at'_def etcb_at_def vs_all_heap_simps get_tcb_def
                  split: option.splits kernel_object.splits)
   apply blast
  apply fastforce
  done

lemma arch_post_set_flags_in_cur_domain[wp]:
  "\<lbrace>cur_fpu_in_cur_domain and (\<lambda>s. in_cur_domain (cur_thread s) s)\<rbrace>
   arch_post_set_flags t flags
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding arch_post_set_flags_def
  by wpsimp

crunch invoke_tcb
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps check_cap_inv thread_set_no_etcb_change_cur_fpu_in_cur_domain
       option_update_thread_no_etcb_change_cur_fpu_in_cur_domain)

crunch store_pte, store_asid_pool_entry, set_vcpu
  for arm_current_fpu_owner[wp]: "\<lambda>s. P (arm_current_fpu_owner (arch_state s))"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift)

crunch
  perform_vspace_invocation, perform_page_table_invocation, perform_page_invocation,
  perform_asid_control_invocation, perform_asid_pool_invocation, perform_vcpu_invocation,
  perform_sgi_invocation, perform_smc_invocation
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps  simp: crunch_simps)

lemma arch_perform_invocation_valid_cur_fpu[wp]:
  "\<lbrace>cur_fpu_in_cur_domain and valid_arch_inv ai\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding arch_perform_invocation_def
  by (wpsimp simp: valid_arch_inv_def)

lemma thread_set_domain_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_fpu_in_cur_domain s \<and>
        (arm_current_fpu_owner (arch_state s) \<noteq> Some tptr \<or> cur_domain s = new_dom)\<rbrace>
   thread_set_domain tptr new_dom
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (auto simp: cur_fpu_in_cur_domain_def in_cur_domain_def etcb_at_def vs_all_heap_simps
                    etcb_at'_def
             split: option.splits)
  done

lemma set_domain_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_fpu_in_cur_domain s \<and>
        (arm_current_fpu_owner (arch_state s) \<noteq> Some tptr \<or> cur_domain s = new_dom)\<rbrace>
   set_domain tptr new_dom
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding set_domain_def
  by (wpsimp | wps)+

lemma fpu_release_arm_current_fpu_owner_n[wp]:
  "\<lbrace>\<top>\<rbrace> fpu_release t \<lbrace>\<lambda>_ s. arm_current_fpu_owner (arch_state s) \<noteq> Some t\<rbrace>"
  unfolding fpu_release_def
  by (wpsimp wp: switch_local_fpu_owner_arm_current_fpu_owner_None[THEN hoare_strengthen_post])

lemma arch_prepare_set_domain_make_fpu_safe[wp]:
  "\<lbrace>\<top>\<rbrace>
   arch_prepare_set_domain tptr new_dom
   \<lbrace>\<lambda>_ s. arm_current_fpu_owner (arch_state s) \<noteq> Some tptr \<or> cur_domain s = new_dom\<rbrace>"
  unfolding arch_prepare_set_domain_def vcpu_flush_if_current_def
  by (wpsimp wp: hoare_vcg_disj_lift)

crunch vcpu_flush
  for arm_current_fpu_owner[wp]: "\<lambda>s. P (arm_current_fpu_owner (arch_state s))"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift)

crunch arch_prepare_set_domain
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps simp: crunch_simps)

lemma cur_fpu_in_cur_domain_domain_list_update[simp]:
  "cur_fpu_in_cur_domain (domain_list_update f s) = cur_fpu_in_cur_domain s"
  by (simp add: cur_fpu_in_cur_domain_def)

lemma cur_fpu_in_cur_domain_domain_start_index_update[simp]:
  "cur_fpu_in_cur_domain (domain_start_index_update f s) = cur_fpu_in_cur_domain s"
  by (simp add: cur_fpu_in_cur_domain_def)

lemma cur_fpu_in_cur_domain_domain_index_update[simp]:
  "cur_fpu_in_cur_domain (domain_index_update f s) = cur_fpu_in_cur_domain s"
  by (simp add: cur_fpu_in_cur_domain_def)

lemma invoke_domain_cur_fpu_in_cur_domain[wp]:
  "invoke_domain di \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
  unfolding invoke_domain_def
  by (wpsimp simp: invoke_set_domain_def domain_set_start_def domain_schedule_configure_def)

lemma thread_set_etcb_at_inv:
  "\<lbrakk>\<And>P tcb. P (tcb_domain (f tcb)) = (P (tcb_domain tcb) :: bool);
    \<And>P tcb. P (tcb_priority (f tcb)) = (P (tcb_priority tcb) :: bool)\<rbrakk>
   \<Longrightarrow> thread_set f t' \<lbrace>etcb_at P t\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  apply (clarsimp simp: vs_all_heap_simps etcb_at'_def get_tcb_def
                 split: option.splits kernel_object.splits)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: etcb_of_def)
  apply blast
  done

crunch do_reply_transfer, handle_recv, handle_vm_fault
  for etcb_at[wp]: "etcb_at P t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps hoare_vcg_all_lift thread_set_etcb_at_inv
   simp: crunch_simps etcb_of_def)

crunch do_reply_transfer, handle_recv, handle_vm_fault, cap_delete_one
  for arm_current_fpu_owner[wp]: "\<lambda>s. P (arm_current_fpu_owner (arch_state s))"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and etcb_at[wp]: "etcb_at P t"
  (wp: cur_fpu_in_cur_domain_lift_strong crunch_wps hoare_vcg_all_lift
   simp: crunch_simps)

crunch
  sched_context_bind_tcb, invoke_sched_context, invoke_sched_control_configure_flags,
  charge_budget, check_budget_restart, receive_ipc, receive_signal, sched_context_cancel_yield_to,
  sched_context_yield_to
  for arm_current_fpu_owner[wp]: "\<lambda>s. P (arm_current_fpu_owner (arch_state s))"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and etcb_at[wp]: "etcb_at P t"
  (wp: cur_fpu_in_cur_domain_lift_strong crunch_wps thread_set_etcb_at_inv hoare_vcg_all_lift
   simp: crunch_simps)

crunch
  set_mrs, charge_budget, check_budget_restart, receive_ipc, receive_signal,
  handle_fault, reply_from_kernel, send_ipc, send_signal, invoke_irq_control,
  invoke_irq_handler, reschedule_required, handle_hypervisor_fault, invoke_sched_context,
  invoke_sched_control_configure_flags, sched_context_cancel_yield_to
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift_strong crunch_wps hoare_vcg_all_lift
   simp: sched_context_yield_to_def crunch_simps)

lemma perform_invocation_valid_cur_fpu[wp]:
  "\<lbrace>cur_fpu_in_cur_domain and valid_invocation iv
    and (\<lambda>s. in_cur_domain (cur_thread s) s)\<rbrace>
   perform_invocation block call can_donate iv
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  by (case_tac iv, simp_all; (solves wpsimp)?)

lemma handle_invocation_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>cur_fpu_in_cur_domain and invs and ct_in_cur_domain
    and ct_active and schact_is_rct\<rbrace>
   handle_invocation calling blocking can_donate first_phase cptr
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding handle_invocation_def
  apply (wpsimp wp: syscall_valid)
         apply (wp gts_wp hoare_vcg_all_lift hoare_drop_imps
                | simp add: split_def | wps)+
  apply (fastforce intro!: ct_in_cur_domain_active_resume_cur_thread)
  done

crunch
  maybe_handle_interrupt, update_time_stamp, receive_ipc, lookup_reply, check_budget,
  check_budget_restart, check_budget, check_budget_restart
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps)

lemma handle_event_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>cur_fpu_in_cur_domain and invs and ct_in_cur_domain and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
    and schact_is_rct and valid_list\<rbrace>
   handle_event e
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  apply (cases e; clarsimp; (solves wpsimp)?)
  unfolding handle_call_def handle_send_def handle_recv_def handle_yield_def
  by (wpsimp wp: check_budget_restart_false check_budget_restart_true
                 update_time_stamp_current_time_bounded hoare_vcg_if_lift2 hoare_drop_imps
           simp: Let_def)

crunch activate_thread, preemption_path
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps ignore: thread_set)

lemma call_kernel_cur_fpu_in_cur_domain:
  "\<lbrace>cur_fpu_in_cur_domain and invs and ct_in_cur_domain and valid_list
    and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)
    and cur_sc_active and ct_not_in_release_q
    and schact_is_rct\<rbrace>
   call_kernel e
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding call_kernel_def maybe_handle_interrupt_def
  apply (wpsimp wp: handle_spurious_irq_invs
         | strengthen invs_valid_objs invs_hyp_sym_refs)+
  apply (fastforce elim: st_tcb_weakenE simp: schedulable_def2 ct_in_state_def)
  done

end

end
