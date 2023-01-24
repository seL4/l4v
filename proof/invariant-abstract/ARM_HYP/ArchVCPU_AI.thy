(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2022, UNSW (ABN 57 195 873 197)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchVCPU_AI
imports AInvs
begin

context Arch begin global_naming ARM_HYP (*FIXME: arch_split*)

definition active_cur_vcpu_of :: "'z state \<Rightarrow> obj_ref option" where
  "active_cur_vcpu_of s \<equiv> case arm_current_vcpu (arch_state s) of Some (vr, True) \<Rightarrow> Some vr
                                                                 | _  \<Rightarrow> None"

definition valid_cur_vcpu :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_cur_vcpu s \<equiv> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = active_cur_vcpu_of s) (cur_thread s) s"

lemma valid_cur_vcpu_lift_ct_Q:
  assumes arch_tcb_of_cur_thread: "\<And>P. \<lbrace>\<lambda>s. arch_tcb_at P (cur_thread s) s \<and> Q s\<rbrace>
                                        f \<lbrace>\<lambda>_ s. arch_tcb_at P (cur_thread s) s\<rbrace>"
  and active_cur_vcpu_of: "\<And>P. \<lbrace>\<lambda>s. P (active_cur_vcpu_of s) \<and> Q s\<rbrace>
                                f \<lbrace>\<lambda>_ s. P (active_cur_vcpu_of s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> Q s\<rbrace> f \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding valid_cur_vcpu_def valid_def
  using use_valid[OF _ active_cur_vcpu_of] use_valid[OF _ arch_tcb_of_cur_thread]
  by (fastforce simp: active_cur_vcpu_of_def)

lemmas valid_cur_vcpu_lift_ct = valid_cur_vcpu_lift_ct_Q[where Q=\<top>, simplified]

lemma valid_cur_vcpu_lift:
  "\<lbrakk>\<And>P. f \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>; \<And>P t. f \<lbrace>\<lambda>s. arch_tcb_at P t s\<rbrace>;
    \<And>P. f \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>\<rbrakk> \<Longrightarrow>
   f \<lbrace>valid_cur_vcpu\<rbrace>"
  apply (rule valid_cur_vcpu_lift_ct)
   apply (rule_tac f=cur_thread in hoare_lift_Pf3)
   apply fastforce+
  done

lemma valid_cur_vcpu_lift_weak:
  "\<lbrakk>\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>; \<And>P t. f \<lbrace>\<lambda>s. arch_tcb_at P t s\<rbrace>;
    \<And>P. f \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>\<rbrakk> \<Longrightarrow>
   f \<lbrace>valid_cur_vcpu\<rbrace>"
  apply (rule valid_cur_vcpu_lift_ct)
   apply (rule_tac f=cur_thread in hoare_lift_Pf3)
   apply fastforce+
  apply (clarsimp simp: valid_cur_vcpu_def valid_def)
  by (fastforce simp: active_cur_vcpu_of_def)

lemma valid_cur_vcpu_lift_cur_thread_update:
  assumes arch_tcb_at: "\<And>P. f \<lbrace>arch_tcb_at P t\<rbrace>"
  and active_cur_vcpu_of: "\<And>P. f \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. valid_cur_vcpu (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  unfolding valid_cur_vcpu_def valid_def
  using use_valid[OF _ active_cur_vcpu_of] use_valid[OF _ arch_tcb_at]
  by (fastforce simp: active_cur_vcpu_of_def)

crunches as_user
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (wp: crunch_wps simp: active_cur_vcpu_of_def)

lemma as_user_valid_cur_vcpu[wp]:
  "as_user tptr f \<lbrace>valid_cur_vcpu\<rbrace>"
  by (rule valid_cur_vcpu_lift; wpsimp wp: as_user_pred_tcb_at)

lemma machine_state_update_active_cur_vcpu_of[simp]:
  "P (active_cur_vcpu_of (s\<lparr>machine_state := ms\<rparr>)) = P (active_cur_vcpu_of s)"
  by (fastforce simp: active_cur_vcpu_of_def)

crunches do_machine_op
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  and valid_cur_vcpu_cur_thread_update[wp]: "\<lambda>s. valid_cur_vcpu (s\<lparr>cur_thread := t\<rparr>)"
  (wp: valid_cur_vcpu_lift_cur_thread_update valid_cur_vcpu_lift crunch_wps)

lemma valid_cur_vcpu_vcpu_update[simp]:
  "vcpu_at v s \<Longrightarrow> valid_cur_vcpu (s\<lparr>kheap := kheap s(v \<mapsto> ArchObj (VCPU vcpu))\<rparr>) = valid_cur_vcpu s"
  by (clarsimp simp: valid_cur_vcpu_def active_cur_vcpu_of_def pred_tcb_at_def obj_at_def)

crunches vcpu_save_reg, vcpu_write_reg, save_virt_timer, vgic_update, vcpu_disable
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: set_vcpu_wp)

lemma set_vcpu_arch_tcb_at_cur_thread[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. arch_tcb_at P (cur_thread s) s\<rbrace>"
  apply (wpsimp wp: set_vcpu_wp get_vcpu_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

crunches vcpu_disable, vcpu_restore, vcpu_save, set_vm_root
  for arch_tcb_at_cur_thread[wp]: "\<lambda>s. arch_tcb_at P (cur_thread s) s"
  (wp: crunch_wps)

crunches vcpu_update, do_machine_op, invalidate_hw_asid_entry, invalidate_asid
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (simp: active_cur_vcpu_of_def)

lemma vcpu_save_reg_active_cur_vcpu_of[wp]:
  "vcpu_save_reg vr reg \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  by (wpsimp simp: vcpu_save_reg_def)

crunches vcpu_restore, do_machine_op, vcpu_save_reg, vgic_update, save_virt_timer,
         vcpu_save_reg_range, vgic_update_lr, vcpu_enable, vcpu_save, set_vcpu
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift crunch_wps simp: active_cur_vcpu_of_def)

lemma switch_vcpu_valid_cur_vcpu_cur_thread_update[wp]:
  "\<lbrace>arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = v) t\<rbrace>
   vcpu_switch v
   \<lbrace>\<lambda>_ s. valid_cur_vcpu (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  unfolding vcpu_switch_def
  apply (wpsimp simp: valid_cur_vcpu_def active_cur_vcpu_of_def)
  by fastforce

lemma switch_vcpu_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = v) (cur_thread s) s\<rbrace>
   vcpu_switch v
   \<lbrace>\<lambda>_ s. valid_cur_vcpu s\<rbrace>"
  unfolding vcpu_switch_def
  apply (wpsimp simp: valid_cur_vcpu_def active_cur_vcpu_of_def)
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

crunches store_hw_asid
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (wp: crunch_wps simp: active_cur_vcpu_of_def)

lemma active_cur_vcpu_of_next_asid[simp]:
  "active_cur_vcpu_of (s\<lparr>arch_state := arch_state s\<lparr>arm_next_asid := v\<rparr>\<rparr>) = active_cur_vcpu_of s"
  by (clarsimp simp: active_cur_vcpu_of_def pred_tcb_at_def obj_at_def valid_cur_vcpu_def)

lemma find_free_hw_asid_active_cur_vcpu_of[wp]:
  "find_free_hw_asid \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  by (wpsimp simp: find_free_hw_asid_def find_pd_for_asid_assert_def)

lemma arm_context_switch_active_cur_vcpu_of[wp]:
  "arm_context_switch pd asid \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  unfolding arm_context_switch_def get_hw_asid_def
  by (wpsimp wp: load_hw_asid_wp)

lemma set_vm_root_active_cur_vcpu_of[wp]:
  "set_vm_root tcb \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  by (wpsimp simp: set_vm_root_def find_pd_for_asid_def wp: get_cap_wp)

crunches set_vm_root
  for valid_cur_vcpu_cur_thread_update[wp]: "\<lambda>s. valid_cur_vcpu (s\<lparr>cur_thread := t\<rparr>)"
  (wp: valid_cur_vcpu_lift_cur_thread_update)

lemma arch_switch_to_thread_valid_cur_vcpu_cur_thread_update[wp]:
  "\<lbrace>valid_cur_vcpu\<rbrace>
   arch_switch_to_thread t
   \<lbrace>\<lambda>_ s. valid_cur_vcpu (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  unfolding arch_switch_to_thread_def
  apply wpsimp
  by (fastforce simp: active_cur_vcpu_of_def pred_tcb_at_def obj_at_def get_tcb_def
               split: option.splits kernel_object.splits)

lemma switch_to_thread_valid_cur_vcpu[wp]:
  "switch_to_thread t \<lbrace>valid_cur_vcpu\<rbrace>"
  unfolding switch_to_thread_def
  by (wpsimp simp: valid_cur_vcpu_def active_cur_vcpu_of_def)

lemma arch_switch_to_idle_thread_valid_cur_vcpu_cur_thread_update[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> valid_idle s \<and> t = idle_thread s\<rbrace>
   arch_switch_to_idle_thread
   \<lbrace>\<lambda>_ s. valid_cur_vcpu (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  unfolding arch_switch_to_idle_thread_def
  apply wpsimp
  by (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def valid_arch_idle_def)

lemma switch_to_idle_thread_valid_cur_vcpu[wp]:
  "\<lbrace>valid_cur_vcpu and valid_idle\<rbrace>
   switch_to_idle_thread
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  by (wpsimp simp: switch_to_idle_thread_def)

lemma tcb_vcpu_update_empty_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. if t = cur_thread s
        then arm_current_vcpu (arch_state s) = None
        else valid_cur_vcpu s\<rbrace>
   arch_thread_set (tcb_vcpu_update Map.empty) t
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  apply (wpsimp wp: arch_thread_set_wp)
  by (clarsimp simp: valid_cur_vcpu_def pred_tcb_at_def active_cur_vcpu_of_def obj_at_def)

lemma vcpu_invalidate_active_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. arm_current_vcpu (arch_state s) \<noteq> None
        \<and> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = None) (cur_thread s) s\<rbrace>
   vcpu_invalidate_active
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding vcpu_invalidate_active_def
  by (wpsimp simp: valid_cur_vcpu_def active_cur_vcpu_of_def)

lemma vcpu_invalid_active_arm_current_vcpu_None[wp]:
  "\<lbrace>\<top>\<rbrace> vcpu_invalidate_active \<lbrace>\<lambda>_ s. arm_current_vcpu (arch_state s) = None\<rbrace>"
  unfolding vcpu_invalidate_active_def
  by wpsimp

lemma dissociate_vcpu_tcb_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   dissociate_vcpu_tcb vr t
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding dissociate_vcpu_tcb_def
  apply (wpsimp wp: hoare_vcg_imp_lift' arch_thread_get_wp get_vcpu_wp)
  by (fastforce simp: valid_cur_vcpu_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def
                      sym_refs_def state_hyp_refs_of_def
               split: bool.splits option.splits)

lemma associate_vcpu_tcb_valid_cur_vcpu:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   associate_vcpu_tcb vr t
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding associate_vcpu_tcb_def
  apply (wpsimp wp: hoare_vcg_imp_lift')
        apply (wpsimp wp: arch_thread_set_wp)
       apply (wpsimp wp: arch_thread_set_wp)
      apply (rule_tac Q="\<lambda>_ s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s)" in hoare_post_imp)
       apply (clarsimp simp: pred_tcb_at_def obj_at_def valid_cur_vcpu_def active_cur_vcpu_of_def)
      by (wpsimp wp: get_vcpu_wp hoare_drop_imps)+

lemma set_thread_state_arch_tcb_at[wp]:
  "set_thread_state ts ref \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)

crunches set_thread_state
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak)

crunches activate_thread
  for valid_cur_vcpu[wp]: valid_cur_vcpu

crunches tcb_sched_action
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  (simp: tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def)

crunches tcb_sched_action
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak)

crunches schedule_choose_new_thread
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (simp: crunch_simps valid_cur_vcpu_def active_cur_vcpu_of_def wp: crunch_wps)

lemma schedule_valid_cur_vcpu_det_ext[wp]:
  "\<lbrace>valid_cur_vcpu and valid_idle\<rbrace>
   (schedule :: (unit, det_ext) s_monad)
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding schedule_def schedule_switch_thread_fastfail_def ethread_get_when_def ethread_get_def
  by (wpsimp wp: hoare_drop_imps gts_wp)

lemma schedule_valid_cur_vcpu[wp]:
  "\<lbrace>valid_cur_vcpu and valid_idle\<rbrace>
   (schedule :: (unit, unit) s_monad)
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding schedule_def allActiveTCBs_def
  by (wpsimp wp: alternative_wp select_wp)

crunches cancel_all_ipc, blocked_cancel_ipc, unbind_maybe_notification, cancel_all_signals,
         bind_notification, fast_finalise, deleted_irq_handler, post_cap_deletion, cap_delete_one,
         reply_cancel_ipc, cancel_ipc, update_waiting_ntfn, send_signal, send_ipc, send_fault_ipc,
         receive_ipc, handle_fault, handle_interrupt, handle_vm_fault, handle_hypervisor_fault,
         send_signal, do_reply_transfer, unbind_notification, suspend, cap_swap, bind_notification,
         restart, reschedule_required, possible_switch_to, thread_set_priority, reply_from_kernel
  for arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: mapM_x_wp_inv thread_set.arch_state select_wp crunch_wps
   simp: crunch_simps possible_switch_to_def reschedule_required_def)

lemma do_unbind_notification_arch_tcb_at[wp]:
  "do_unbind_notification ntfnptr ntfn tcbptr \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding set_bound_notification_def set_simple_ko_def
  apply (wpsimp wp: set_object_wp get_object_wp get_simple_ko_wp thread_get_wp)
  by (fastforce simp: pred_tcb_at_def obj_at_def get_tcb_def)

lemma unbind_notification_arch_tcb_at[wp]:
  "unbind_notification tcb \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding unbind_notification_def
  by wpsimp

lemma bind_notification_arch_tcb_at[wp]:
  "bind_notification tcbptr ntfnptr \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding bind_notification_def set_bound_notification_def set_simple_ko_def
  apply (wpsimp wp: set_object_wp get_object_wp get_simple_ko_wp)
  by (fastforce simp: pred_tcb_at_def obj_at_def get_tcb_def)

lemma unbind_maybe_notification_arch_tcb_at[wp]:
  "unbind_maybe_notification ntfnptr \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding unbind_maybe_notification_def
  by wpsimp

crunches blocked_cancel_ipc, cap_delete_one, cancel_signal
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  (wp: crunch_wps simp: crunch_simps)

lemma reply_cancel_ipc_arch_tcb_at[wp]:
  "reply_cancel_ipc ntfnptr \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding reply_cancel_ipc_def thread_set_def
  apply (wpsimp wp: set_object_wp select_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)

crunches cancel_ipc, send_ipc, receive_ipc
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  (wp: crunch_wps simp: crunch_simps)

lemma send_fault_ipc_arch_tcb_at[wp]:
  "send_fault_ipc tptr fault \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding send_fault_ipc_def thread_set_def Let_def
  by (wpsimp wp: set_object_wp hoare_drop_imps hoare_vcg_all_lift_R
           simp: pred_tcb_at_def obj_at_def get_tcb_def)

crunches handle_fault, handle_interrupt, handle_vm_fault, handle_hypervisor_fault, send_signal
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  (wp: mapM_x_wp_inv crunch_wps)

crunches reschedule_required, set_scheduler_action, tcb_sched_action
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  (simp: reschedule_required_def set_scheduler_action_def tcb_sched_action_def set_tcb_queue_def
         get_tcb_queue_def)

lemma thread_set_fault_arch_tcb_at[wp]:
  "thread_set (tcb_fault_update f) r \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding thread_set_def
  by (wpsimp wp: set_object_wp simp: pred_tcb_at_def obj_at_def get_tcb_def)

lemma do_reply_transfer_arch_tcb_at[wp]:
  "do_reply_transfer sender receiver slot grant \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding do_reply_transfer_def
  by (wpsimp wp: gts_wp split_del: if_split)

crunches send_ipc, send_fault_ipc, receive_ipc, handle_fault, handle_interrupt, handle_vm_fault,
         handle_hypervisor_fault, send_signal, do_reply_transfer, cancel_all_ipc,
         cancel_all_signals, unbind_maybe_notification, suspend, deleting_irq_handler,
         unbind_notification
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak crunch_wps)

crunches init_arch_objects, reset_untyped_cap
  for arch_state[wp]: "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps preemption_point_inv unless_wp mapME_x_wp'
   simp: crunch_simps)

crunches invoke_untyped
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv
   simp: crunch_simps mapM_x_def[symmetric] active_cur_vcpu_of_def)

lemma invoke_untyped_valid_cur_vcpu:
  "\<lbrace>valid_cur_vcpu and invs and valid_untyped_inv ui and ct_active\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule valid_cur_vcpu_lift_ct_Q)
    apply (rule_tac f=cur_thread in hoare_lift_Pf2)
     apply (rule invoke_untyped_pred_tcb_at)
    apply clarsimp
    apply wpsimp
   apply wpsimp
  apply (fastforce simp: pred_tcb_at_def obj_at_def ct_in_state_def)
  done

lemma valid_cur_vcpu_is_original_cap_update[simp]:
  "valid_cur_vcpu (is_original_cap_update f s) = valid_cur_vcpu s"
  by (clarsimp simp: valid_cur_vcpu_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def)

lemma active_cur_vcpu_of_arm_asid_table_update[simp]:
  "P (active_cur_vcpu_of (s\<lparr>arch_state := arm_asid_table_update f (arch_state s)\<rparr>))
   = P (active_cur_vcpu_of s)"
  by (clarsimp simp: active_cur_vcpu_of_def)

crunches cap_insert, cap_move
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak)

crunches suspend, unbind_notification, cap_swap_for_delete
  for state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  (wp: crunch_wps thread_set_hyp_refs_trivial select_wp simp: crunch_simps)

lemma prepare_thread_delete_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   prepare_thread_delete p
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding prepare_thread_delete_def arch_thread_get_def
  by (wpsimp wp: dissociate_vcpu_tcb_valid_cur_vcpu)

crunches delete_asid_pool
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps simp: crunch_simps)

crunches store_pte, store_pde, set_asid_pool
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps simp: crunch_simps active_cur_vcpu_of_def)

crunches unmap_page, unmap_page_table, delete_asid
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps valid_cur_vcpu_lift)

crunches delete_asid_pool, unmap_page, unmap_page_table, delete_asid
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift)

crunches vcpu_finalise, arch_finalise_cap, finalise_cap
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (simp: crunch_simps)

crunches prepare_thread_delete, deleting_irq_handler, delete_asid_pool, flush_page
  for sym_refs_state_hyp_refs_of[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of s)"
  (wp: crunch_wps simp: crunch_simps)

lemma store_pte_state_hyp_refs_of[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (rule_tac P=P in back_subst)
   apply fastforce
  by (auto simp: state_hyp_refs_of_def  hyp_refs_of_def obj_at_def
          split: if_splits intro!: ext)

crunches flush_page
  for state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  (wp: crunch_wps simp: crunch_simps)

lemma unmap_page_state_hyp_refs_of[wp]:
  "unmap_page pgsz asid vptr pptr \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  unfolding unmap_page_def lookup_pt_slot_def find_pd_for_asid_def
  by (wpsimp wp: hoare_drop_imps mapM_wp_inv get_pde_wp store_pde_state_hyp_refs_of)

crunches flush_table, page_table_mapped, delete_asid, vcpu_finalise, unmap_page_table, finalise_cap
  for state_hyp_refs_of[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of s)"

lemma preemption_point_state_hyp_refs_of[wp]:
  "preemption_point \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp wp: preemption_point_inv)

lemma preemption_point_valid_cur_vcpu[wp]:
  "preemption_point \<lbrace>valid_cur_vcpu\<rbrace>"
  apply (wpsimp wp: preemption_point_inv)
    by (clarsimp simp: valid_cur_vcpu_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def)+

crunches cap_swap_for_delete, empty_slot
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak)

lemma rec_del_sym_refs_state_hyp_refs_of[wp]:
  "rec_del call \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  by (rule rec_del_preservation; wpsimp)

crunches cap_delete
  for state_hyp_refs_of[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of s)"

lemma rec_del_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   rec_del call
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (rule_tac Q="\<lambda>_. ?pre" in hoare_post_imp, fastforce)
  by (rule rec_del_preservation; wpsimp)

crunches cap_delete
  for valid_cur_vcpu[wp]: valid_cur_vcpu

lemma cap_revoke_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   cap_revoke slot
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (rule_tac Q="\<lambda>_. ?pre" in hoare_post_imp, fastforce)
  by (wpsimp wp: cap_revoke_preservation)

crunches cancel_badged_sends, invoke_irq_control, invoke_irq_handler
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and arch_state[wp]: "\<lambda>s. P (arch_state s)"
  (wp: filterM_preserved)

crunches store_pte, set_cap, set_mrs
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (simp: active_cur_vcpu_of_def)

crunches perform_page_table_invocation, perform_page_directory_invocation, perform_page_invocation,
         perform_asid_pool_invocation, invoke_vcpu_inject_irq, invoke_vcpu_read_register,
         invoke_vcpu_write_register, invoke_vcpu_ack_vppi
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (wp: crunch_wps simp: crunch_simps)

crunches cancel_badged_sends, invoke_irq_control, invoke_irq_handler, invoke_vcpu_inject_irq,
         bind_notification
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak)

crunches perform_asid_pool_invocation, perform_page_table_invocation,
         perform_page_directory_invocation, perform_page_invocation, invoke_vcpu_read_register,
         invoke_vcpu_write_register, invoke_vcpu_ack_vppi
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift)

lemma invoke_cnode_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   invoke_cnode i
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding invoke_cnode_def
  by (wpc | wpsimp wp: hoare_drop_imps hoare_vcg_all_lift)+

lemma valid_cur_vcpu_trans_state[simp]:
  "valid_cur_vcpu (trans_state f s) = valid_cur_vcpu s"
  by (clarsimp simp: valid_cur_vcpu_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def)

crunches restart, reschedule_required, possible_switch_to, thread_set_priority
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  (simp: possible_switch_to_def set_tcb_queue_def get_tcb_queue_def)

crunches restart, reschedule_required, possible_switch_to, thread_set_priority
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak)

crunches restart, arch_post_modify_registers, arch_get_sanitise_register_info
  for valid_cur_vcpu[wp]: valid_cur_vcpu

lemma thread_set_valid_cur_vcpu:
  "(\<And>tcb. tcb_arch (f tcb) = tcb_arch tcb) \<Longrightarrow> thread_set f tptr \<lbrace>valid_cur_vcpu\<rbrace>"
  apply (rule valid_cur_vcpu_lift_weak; (solves wpsimp)?)
  unfolding thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (fastforce simp: pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma fault_handler_update_valid_cur_vcpu[wp]:
  "option_update_thread thread (tcb_fault_handler_update \<circ> f) opt \<lbrace>valid_cur_vcpu\<rbrace>"
  unfolding option_update_thread_def
  by (wpsimp wp: thread_set_valid_cur_vcpu)

lemma fault_handler_update_state_hyp_refs_of[wp]:
  "option_update_thread thread (tcb_fault_handler_update \<circ> f) opt \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  unfolding option_update_thread_def
  by (fastforce intro: thread_set_hyp_refs_trivial split: option.splits)

crunches set_mcpriority, set_priority
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (simp: set_priority_def)

lemma ethread_set_state_hyp_refs_of[wp]:
  "ethread_set f t \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  unfolding ethread_set_def set_eobject_def
  apply wp
  apply (clarsimp dest!: get_tcb_SomeD)
  done

crunches tcb_sched_action, possible_switch_to, set_scheduler_action, reschedule_required
  for state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  (simp: tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def possible_switch_to_def
         reschedule_required_def set_scheduler_action_def)

crunches set_mcpriority, set_priority
  for state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  (wp: thread_set_hyp_refs_trivial simp: set_priority_def thread_set_priority_def)

lemma invoke_tcb_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   invoke_tcb iv
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  apply (cases iv; clarsimp; (solves \<open>wpsimp wp: mapM_x_wp_inv\<close>)?)
   defer
   subgoal for tcb_ptr ntfn_ptr_opt
     by (case_tac ntfn_ptr_opt; wpsimp)
  \<comment> \<open>ThreadControl\<close>
  apply (forward_inv_step wp: check_cap_inv)+
  by (wpsimp wp: check_cap_inv hoare_drop_imps thread_set_hyp_refs_trivial thread_set_valid_cur_vcpu)

crunches invoke_domain
  for arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and arch_tcb_at[wp]: "arch_tcb_at P t"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak)

crunches perform_asid_control_invocation
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s )"
  and active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (simp: active_cur_vcpu_of_def)

lemma perform_asid_control_invocation_valid_cur_vcpu:
  "\<lbrace>valid_cur_vcpu and invs and valid_aci iv and ct_active\<rbrace>
   perform_asid_control_invocation iv
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule valid_cur_vcpu_lift_ct_Q)
    apply (rule_tac f=cur_thread in hoare_lift_Pf2)
     apply (rule perform_asid_control_invocation_pred_tcb_at)
    apply wpsimp
   apply wpsimp
  apply (fastforce simp: pred_tcb_at_def obj_at_def ct_in_state_def)
  done

lemma perform_vcpu_invocation_valid_cur_vcpu:
  "\<lbrace>valid_cur_vcpu and invs\<rbrace> perform_vcpu_invocation iv \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding perform_vcpu_invocation_def
  by (wpsimp wp: associate_vcpu_tcb_valid_cur_vcpu)

lemma perform_invocation_valid_cur_vcpu[wp]:
  "\<lbrace>valid_cur_vcpu and invs and valid_invocation iv and ct_active\<rbrace>
   perform_invocation blocking call iv
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  apply (case_tac iv, simp_all; (solves wpsimp)?)
   apply (wpsimp wp: invoke_untyped_valid_cur_vcpu)
  unfolding arch_perform_invocation_def
  apply (wpsimp wp: perform_vcpu_invocation_valid_cur_vcpu
                    perform_asid_control_invocation_valid_cur_vcpu)
  apply (fastforce simp: valid_arch_inv_def)
  done

crunches reply_from_kernel, receive_signal
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak)

lemma handle_invocation_valid_cur_vcpu[wp]:
  "\<lbrace>valid_cur_vcpu and invs and ct_active\<rbrace> handle_invocation calling blocking \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding handle_invocation_def
  by (wp syscall_valid set_thread_state_ct_st
      | simp add: split_def | wpc
      | wp (once) hoare_drop_imps)+
     (auto simp: ct_in_state_def elim: st_tcb_ex_cap)

lemma handle_recv_valid_cur_vcpu[wp]:
  "handle_recv is_blocking \<lbrace>valid_cur_vcpu\<rbrace>"
  unfolding handle_recv_def Let_def ep_ntfn_cap_case_helper delete_caller_cap_def
  by (wpsimp wp: hoare_drop_imps)

lemma handle_event_valid_cur_vcpu:
  "\<lbrace>valid_cur_vcpu and invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
   handle_event e
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  apply (cases e; clarsimp; (solves wpsimp)?)
  unfolding handle_call_def handle_send_def handle_reply_def handle_yield_def
  by (wpsimp wp: get_cap_wp)+

lemma call_kernel_valid_cur_vcpu:
  "\<lbrace>valid_cur_vcpu and invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
   (call_kernel e) :: (unit, unit) s_monad
   \<lbrace>\<lambda>_ . valid_cur_vcpu\<rbrace>"
  unfolding call_kernel_def
  apply (simp flip: bind_assoc)
  by (wpsimp wp: handle_event_valid_cur_vcpu hoare_vcg_if_lift2 hoare_drop_imps
      | strengthen invs_valid_idle)+

lemma call_kernel_valid_cur_vcpu_det_ext:
  "\<lbrace>valid_cur_vcpu and invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
   (call_kernel e) :: (unit, det_ext) s_monad
   \<lbrace>\<lambda>_ . valid_cur_vcpu\<rbrace>"
  unfolding call_kernel_def
  apply (simp flip: bind_assoc)
  by (wpsimp wp: handle_event_valid_cur_vcpu hoare_vcg_if_lift2 hoare_drop_imps
      | strengthen invs_valid_idle)+

end

end
