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
  "cur_fpu_in_cur_domain s \<equiv> none_top (\<lambda>t. in_cur_domain t s) (x64_current_fpu_owner (arch_state s))"

lemma cur_fpu_in_cur_domain_lift_strong:
  assumes [wp]: "\<And>P. f \<lbrace>\<lambda>s. P (x64_current_fpu_owner (arch_state s))\<rbrace>"
                "\<And>P. f \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
                "\<And>P t. f \<lbrace>etcb_at (\<lambda>t. P (etcb_domain t)) t\<rbrace>"
  shows "f \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
  unfolding cur_fpu_in_cur_domain_def in_cur_domain_def
  by (wp_pre, wps, wpsimp wp: valid_none_top_post_wp)

lemma cur_fpu_in_cur_domain_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (x64_current_fpu_owner (arch_state s))\<rbrace>"
          "\<And>P. f \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
          "\<And>P. f \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  shows "f \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
 by (rule cur_fpu_in_cur_domain_lift_strong assms)+

lemma cur_fpu_in_cur_domain_current_fpu_owner_update[simp]:
  "cur_fpu_in_cur_domain (s\<lparr>arch_state := arch_state s\<lparr>x64_current_fpu_owner := new_owner\<rparr>\<rparr>)
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
  "\<And>f. cur_fpu_in_cur_domain (arch_state_update (x64_asid_table_update f) s) = cur_fpu_in_cur_domain s"
  "\<And>f. cur_fpu_in_cur_domain (s\<lparr>arch_state := (x64_asid_table_update f) (arch_state s)\<rparr>) = cur_fpu_in_cur_domain s" \<comment> \<open>FIXME: previous line doesn't work for this, can it be generalised?\<close>
  by (auto simp: cur_fpu_in_cur_domain_def)

\<comment> \<open>schedule\<close>

crunch arch_thread_set, load_fpu_state
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  and x64_current_fpu_owner[wp]: "\<lambda>s. P (x64_current_fpu_owner (arch_state s))"
  (wp: cur_fpu_in_cur_domain_lift)

crunch arch_thread_set, load_fpu_state, save_fpu_state, do_machine_op
  for in_cur_domain[wp]: "in_cur_domain t"
  (ignore: arch_thread_set as_user)

lemma switch_local_fpu_owner_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_fpu_in_cur_domain s \<and> none_top (\<lambda>t. in_cur_domain t s) new_owner\<rbrace>
   switch_local_fpu_owner new_owner
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding switch_local_fpu_owner_def set_x64_current_fpu_owner_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' valid_none_top_post_wp)
  by auto

lemma lazy_fpu_restore_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>cur_fpu_in_cur_domain and in_cur_domain thread_ptr\<rbrace>
   lazy_fpu_restore thread_ptr
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding lazy_fpu_restore_def
  by (wpsimp wp: thread_get_wp')

crunch set_vm_root
  for x64_current_fpu_owner[wp]: "\<lambda>s. P (x64_current_fpu_owner (arch_state s))"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift)

lemma arch_switch_to_thread_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>cur_fpu_in_cur_domain and in_cur_domain t\<rbrace>
   arch_switch_to_thread t
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding arch_switch_to_thread_def
  by (wpsimp | wps)+

crunch guarded_switch_to, switch_to_idle_thread
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps)

lemma choose_thread_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>cur_fpu_in_cur_domain and valid_queues\<rbrace>
   choose_thread
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding choose_thread_def
  apply wpsimp
  apply (fastforce dest!: next_thread_queued split: option.splits
                   simp: etcb_at_def next_thread_def valid_queues_def in_cur_domain_def)
  done

lemma next_domain_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. x64_current_fpu_owner (arch_state s) = None\<rbrace> next_domain \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding next_domain_def Let_def
  by (wpsimp wp: dxo_wp_weak simp: cur_fpu_in_cur_domain_def)

lemma switch_local_fpu_owner_x64_current_fpu_owner_None[wp]:
  "\<lbrace>\<top>\<rbrace> switch_local_fpu_owner None \<lbrace>\<lambda>_ s. x64_current_fpu_owner (arch_state s) = None\<rbrace>"
  unfolding switch_local_fpu_owner_def set_x64_current_fpu_owner_def
  by wpsimp

crunch set_scheduler_action
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift)

lemma schedule_choose_new_thread_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_fpu_in_cur_domain s \<and> valid_queues s\<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding schedule_choose_new_thread_def arch_prepare_next_domain_def
  by wpsimp

lemma schedule_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_fpu_in_cur_domain s \<and> valid_sched s \<and> valid_objs s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   schedule
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding schedule_def schedule_switch_thread_fastfail_def
  apply (wpsimp wp: hoare_drop_imps gts_wp)
  by (safe; (fastforce simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                             switch_in_cur_domain_def st_tcb_at_def obj_at_def)?)


\<comment> \<open>handle_interrupt\<close>

crunch send_signal, set_extra_badge, handle_reserved_irq
  for etcb_at[wp]: "etcb_at P t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps transfer_caps_loop_pres thread_set_no_change_etcb_at dxo_wp_weak
   simp: crunch_simps etcb_of_def)

crunch handle_interrupt
  for x64_current_fpu_owner[wp]: "\<lambda>s. P (x64_current_fpu_owner (arch_state s))"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and etcb_at_domain[wp]: "etcb_at (\<lambda>t. P (etcb_domain t)) t"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps thread_set_no_change_etcb_at dxo_wp_weak
       cur_fpu_in_cur_domain_lift_strong
   simp: crunch_simps)


\<comment> \<open>handle_event\<close>

lemma retype_region_valid_cur_fpu[wp]:
  "retype_region ptr numObjects o_bits type dev \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
  unfolding retype_region_def
  apply (wpsimp simp_del: fun_upd_apply simp: foldr_fun_upd_value)
  by (auto simp: cur_fpu_in_cur_domain_def in_cur_domain_def etcb_at'_def
                 default_object_def default_tcb_def etcbs_of'_def
          split: option.splits apiobject_type.splits)

crunch do_machine_op, create_cap, init_arch_objects, set_cap
  for x64_current_fpu_owner[wp]: "\<lambda>s. P (x64_current_fpu_owner (arch_state s))"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift crunch_wps simp: crunch_simps)

lemma delete_objects_valid_cur_fpu[wp]:
  "delete_objects ptr bits \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
  unfolding delete_objects_def
  apply wpsimp
   apply (rule hoare_strengthen_post, rule do_machine_op_cur_fpu_in_cur_domain)
  by (auto simp: cur_fpu_in_cur_domain_def in_cur_domain_def etcb_at'_def detype_def etcbs_of'_def
          split: option.splits)

crunch invoke_untyped
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps mapME_x_wp' preemption_point_inv' simp: crunch_simps mapM_x_def_bak) \<comment> \<open>FIXME: change invoke_untyped to use mapM_x\<close>

crunch cap_move, suspend, delete_asid_pool, unmap_page, cancel_badged_sends
  for etcb_at[wp]: "etcb_at P t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps filterM_mapM ignore: set_object)

crunch
  cap_insert, cap_move, cap_swap, set_thread_state, unbind_maybe_notification, unbind_notification,
  cancel_all_ipc, suspend, cancel_all_signals, delete_asid_pool, unmap_page, delete_asid,
  unmap_page_table, cancel_badged_sends, empty_slot, arch_finalise_cap
  for x64_current_fpu_owner[wp]: "\<lambda>s. P (x64_current_fpu_owner (arch_state s))"
  and etcb_at_domain[wp]: "etcb_at (\<lambda>t. P (etcb_domain t)) t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: mapM_x_wp_inv_weak cur_fpu_in_cur_domain_lift_strong crunch_wps dxo_wp_weak
   simp: crunch_simps filterM_mapM ignore: set_object)

crunch invoke_cnode
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps preemption_point_inv' cap_revoke_preservation
   simp: crunch_simps)

crunch set_priority
  for etcb_at_domain[wp]: "etcb_at (\<lambda>t. P (etcb_domain t)) t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: thread_set_no_change_etcb_at)

crunch set_mcpriority, bind_notification
  for etcb_at[wp]: "etcb_at P t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps thread_set_no_change_etcb_at simp: crunch_simps etcb_of_def)

crunch cancel_ipc, set_mcpriority, set_priority, bind_notification
  for x64_current_fpu_owner[wp]: "\<lambda>s. P (x64_current_fpu_owner (arch_state s))"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift_strong)

lemma thread_set_no_etcb_change_cur_fpu_in_cur_domain:
  assumes x: "\<And>P tcb. P (tcb_domain (f tcb)) = (P (tcb_domain tcb) :: bool)"
  shows      "thread_set f t' \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
  by (wpsimp wp: cur_fpu_in_cur_domain_lift_strong thread_set_no_change_etcb_at simp: x)

lemma option_update_thread_no_etcb_change_cur_fpu_in_cur_domain:
  assumes x: "\<And>P val tcb. P (tcb_domain (f val tcb)) = (P (tcb_domain tcb) :: bool)"
  shows      "option_update_thread t f opt \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
  unfolding option_update_thread_def
  by (wpsimp wp: cur_fpu_in_cur_domain_lift_strong thread_set_no_change_etcb_at simp: x)

lemma arch_post_set_flags_in_cur_domain[wp]:
  "\<lbrace>cur_fpu_in_cur_domain and (\<lambda>s. in_cur_domain (cur_thread s) s)\<rbrace>
   arch_post_set_flags t flags
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding arch_post_set_flags_def
  by wpsimp

lemma set_flags_in_cur_domain[wp]:
  "set_flags param_a param_b \<lbrace>in_cur_domain t\<rbrace>"
  unfolding set_flags_def in_cur_domain_def
  by (wpsimp wp: thread_set_no_change_etcb_at | wps)+

crunch set_flags
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"

crunch invoke_tcb
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps check_cap_inv thread_set_no_etcb_change_cur_fpu_in_cur_domain
       option_update_thread_no_etcb_change_cur_fpu_in_cur_domain)

crunch store_pte, store_pde, store_pdpte, store_pml4e, store_asid_pool_entry, set_ioport_mask
  for etcb_at[wp]: "etcb_at P t"
  and x64_current_fpu_owner[wp]: "\<lambda>s. P (x64_current_fpu_owner (arch_state s))"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift_strong ignore: set_object)

crunch
  perform_page_table_invocation, perform_page_directory_invocation, perform_pdpt_invocation,
  perform_page_invocation, perform_asid_control_invocation, perform_asid_pool_invocation,
  perform_io_port_invocation, perform_ioport_control_invocation
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
        (x64_current_fpu_owner (arch_state s) \<noteq> Some tptr \<or> cur_domain s = new_dom)\<rbrace>
   thread_set_domain tptr new_dom
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  by (auto simp: cur_fpu_in_cur_domain_def in_cur_domain_def etcb_at_def etcbs_of'_def
          split: option.splits)

lemma set_domain_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_fpu_in_cur_domain s \<and>
        (x64_current_fpu_owner (arch_state s) \<noteq> Some tptr \<or> cur_domain s = new_dom)\<rbrace>
   set_domain tptr new_dom
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding set_domain_def
  by (wpsimp | wps)+

lemma fpu_release_x64_current_fpu_owner_n[wp]:
  "\<lbrace>\<top>\<rbrace> fpu_release t \<lbrace>\<lambda>_ s. x64_current_fpu_owner (arch_state s) \<noteq> Some t\<rbrace>"
  unfolding fpu_release_def
  by (wpsimp wp: switch_local_fpu_owner_x64_current_fpu_owner_None[THEN hoare_strengthen_post])

crunch fpu_release
  for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"

lemma arch_prepare_set_domain_make_fpu_safe[wp]:
  "\<lbrace>\<top>\<rbrace>
   arch_prepare_set_domain tptr new_dom
   \<lbrace>\<lambda>_ s. x64_current_fpu_owner (arch_state s) \<noteq> Some tptr \<or> cur_domain s = new_dom\<rbrace>"
  unfolding arch_prepare_set_domain_def
  by (wpsimp wp: hoare_vcg_disj_lift)

crunch arch_prepare_set_domain
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: crunch_wps simp: crunch_simps)

lemma cur_fpu_in_cur_domain_domain_list_update[simp]:
  "cur_fpu_in_cur_domain (domain_list_update f s) = cur_fpu_in_cur_domain s"
  by (simp add: cur_fpu_in_cur_domain_def)

lemma cur_fpu_in_cur_domain_domain_time_update[simp]:
  "cur_fpu_in_cur_domain (domain_time_update f s) = cur_fpu_in_cur_domain s"
  by (simp add: cur_fpu_in_cur_domain_def)

lemma cur_fpu_in_cur_domain_domain_start_index_update[simp]:
  "cur_fpu_in_cur_domain (domain_start_index_update f s) = cur_fpu_in_cur_domain s"
  by (simp add: cur_fpu_in_cur_domain_def)

lemma invoke_domain_cur_fpu_in_cur_domain[wp]:
  "invoke_domain di \<lbrace>cur_fpu_in_cur_domain\<rbrace>"
  unfolding invoke_domain_def
  by (wpsimp simp: invoke_set_domain_def domain_set_start_def domain_schedule_configure_def)

crunch do_reply_transfer, handle_recv, handle_vm_fault
  for etcb_at[wp]: "etcb_at P t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps thread_set_no_change_etcb_at transfer_caps_loop_pres
   simp: crunch_simps etcb_of_def)

crunch do_reply_transfer, handle_recv, handle_vm_fault
  for x64_current_fpu_owner[wp]: "\<lambda>s. P (x64_current_fpu_owner (arch_state s))"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift_strong crunch_wps
   simp: crunch_simps)

crunch
  handle_fault, reply_from_kernel, send_ipc, send_signal, invoke_irq_control, invoke_irq_handler,
  reschedule_required, handle_hypervisor_fault
  for x64_current_fpu_owner[wp]: "\<lambda>s. P (x64_current_fpu_owner (arch_state s))"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and etcb_at[wp]: "etcb_at P t"
  and cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain
  (wp: cur_fpu_in_cur_domain_lift_strong crunch_wps
   simp: crunch_simps)

lemma perform_invocation_valid_cur_fpu[wp]:
  "\<lbrace>cur_fpu_in_cur_domain and valid_invocation iv
    and (\<lambda>s. in_cur_domain (cur_thread s) s)\<rbrace>
   perform_invocation blocking call iv
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  by (case_tac iv, simp_all; (solves wpsimp)?)

lemma set_thread_state_runnable_scheduler_action:
  "\<lbrace>\<lambda>s. P (scheduler_action s) \<and> runnable ts\<rbrace> set_thread_state t ts \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
  unfolding set_thread_state_def set_thread_state_act_def set_object_def get_object_def
            set_scheduler_action_def
  apply (wpsimp wp: gts_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemma handle_invocation_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>cur_fpu_in_cur_domain and einvs and ct_active and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   handle_invocation calling blocking
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding handle_invocation_def
  apply (wpsimp wp: syscall_valid)
          apply (wp gts_wp hoare_vcg_all_lift hoare_drop_imps
                    set_thread_state_runnable_scheduler_action
                 | simp add: split_def | wps)+
  apply (fastforce simp: invs_def valid_state_def valid_arch_state_def valid_pspace_def
                         valid_tcb_state_def ct_in_state_def valid_sched_def
                  elim!: pred_tcb_weakenE
                 intro!: ct_in_cur_domain_active_resume_cur_thread)
  done

crunch maybe_handle_interrupt
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain

lemma handle_event_cur_fpu_in_cur_domain[wp]:
  "\<lbrace>cur_fpu_in_cur_domain and einvs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   handle_event e
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  apply (cases e; clarsimp; (solves wpsimp)?)
  unfolding handle_call_def handle_send_def handle_reply_def handle_yield_def
  by (wpsimp wp: get_cap_wp)+

crunch activate_thread
  for cur_fpu_in_cur_domain[wp]: cur_fpu_in_cur_domain

lemma call_kernel_cur_fpu_in_cur_domain:
  "\<lbrace>cur_fpu_in_cur_domain and einvs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   call_kernel e
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding call_kernel_def maybe_handle_interrupt_def
  apply (wpsimp wp: handle_spurious_irq_invs | strengthen invs_valid_objs invs_hyp_sym_refs)+
    apply (rule hoare_post_imp[where Q'="\<lambda>irq s. irq \<notin> Some ` non_kernel_IRQs \<and> cur_fpu_in_cur_domain s \<and> valid_sched s \<and> invs s"])
     apply fastforce
    apply (wpsimp wp: getActiveIRQ_neq_non_kernel handle_event_valid_sched
           | strengthen invs_valid_objs invs_hyp_sym_refs)+
  done

end

end
