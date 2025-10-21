(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2022, UNSW (ABN 57 195 873 197)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchVCPU_AI
imports ArchDetSchedSchedule_AI
begin

context Arch begin arch_global_naming

section \<open>valid_cur_vcpu\<close>

text \<open>
  Show that the current thread's VCPU is consistent with the current VCPU,
  unless the current thread is in a different domain.

  The exception is to handle this invariant possibly being temporarily broken
  if the current thread has its VCPU changed. The idle thread then has to be
  explicitly included as it is a special case for domains.\<close>

(* This is similar to cur_vcpu_2, but not close enough to reuse. *)
definition active_cur_vcpu_of :: "'z state \<Rightarrow> obj_ref option" where
  "active_cur_vcpu_of s \<equiv> case arm_current_vcpu (arch_state s) of Some (vr, True) \<Rightarrow> Some vr
                                                                 | _  \<Rightarrow> None"

definition valid_cur_vcpu :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_cur_vcpu s \<equiv>
     in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s
     \<longrightarrow> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = active_cur_vcpu_of s) (cur_thread s) s"

lemma valid_cur_vcpu_lift_ct_Q:
  assumes in_cur_domain_cur_thread: "\<lbrace>\<lambda>s. \<not> in_cur_domain (cur_thread s) s \<and> Q s\<rbrace>
                                     f \<lbrace>\<lambda>_ s. \<not> in_cur_domain (cur_thread s) s\<rbrace>"
  assumes cur_thread_idle_thread: "\<lbrace>\<lambda>s. cur_thread s \<noteq> idle_thread s \<and> Q s\<rbrace>
                                        f \<lbrace>\<lambda>_ s. cur_thread s \<noteq> idle_thread s\<rbrace>"
  assumes tcb_vcpu_of_cur_thread: "\<And>P. \<lbrace>\<lambda>s. arch_tcb_at (\<lambda>itcb. P (itcb_vcpu itcb)) (cur_thread s) s \<and> Q s\<rbrace>
                                        f \<lbrace>\<lambda>_ s. arch_tcb_at (\<lambda>itcb. P (itcb_vcpu itcb)) (cur_thread s) s\<rbrace>"
  and active_cur_vcpu_of: "\<And>P. \<lbrace>\<lambda>s. P (active_cur_vcpu_of s) \<and> Q s\<rbrace>
                                f \<lbrace>\<lambda>_ s. P (active_cur_vcpu_of s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> Q s\<rbrace> f \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding valid_cur_vcpu_def valid_def
  using use_valid[OF _ in_cur_domain_cur_thread] use_valid[OF _ cur_thread_idle_thread]
        use_valid[OF _ tcb_vcpu_of_cur_thread] use_valid[OF _ active_cur_vcpu_of]
  by (fastforce simp: active_cur_vcpu_of_def)

lemmas valid_cur_vcpu_lift_ct = valid_cur_vcpu_lift_ct_Q[where Q=\<top>, simplified]

lemma valid_cur_vcpu_lift:
  "\<lbrakk>\<And>P. f \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>; \<And>P t. f \<lbrace>\<lambda>s. arch_tcb_at (\<lambda>itcb. P (itcb_vcpu itcb)) t s\<rbrace>;
    \<And>P. f \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>; \<And>P. f \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace>; \<And>t. f \<lbrace>\<lambda>s. \<not> (in_cur_domain t s)\<rbrace>\<rbrakk> \<Longrightarrow>
   f \<lbrace>valid_cur_vcpu\<rbrace>"
  apply (rule valid_cur_vcpu_lift_ct)
     apply (rule_tac f=cur_thread in hoare_lift_Pf3; fastforce)
    apply (rule_tac f=cur_thread in hoare_lift_Pf3; fastforce)
   apply (rule_tac f=cur_thread in hoare_lift_Pf3; fastforce)
  apply fastforce
  done

lemma valid_cur_vcpu_lift_weak:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  assumes "\<And>P t. f \<lbrace>\<lambda>s. arch_tcb_at (\<lambda>itcb. P (itcb_vcpu itcb)) t s\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace>"
  assumes "\<And>t. f \<lbrace>\<lambda>s. \<not> (in_cur_domain t s)\<rbrace>"
  shows "f \<lbrace>valid_cur_vcpu\<rbrace>"
  apply (rule valid_cur_vcpu_lift_ct)
     apply (wp_pre, wps assms, wp assms, assumption)
    apply (wp_pre, wps assms, wp assms, assumption)
   apply (wp_pre, wps assms, wp assms, assumption)
  apply (wpsimp simp: active_cur_vcpu_of_def wp: assms)
  done

lemma valid_cur_vcpu_lift_cur_thread_update:
  assumes tcb_vcpu_at: "\<And>P. f \<lbrace>arch_tcb_at (\<lambda>itcb. P (itcb_vcpu itcb)) t\<rbrace>"
  and active_cur_vcpu_of: "\<And>P. f \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  and in_cur_domain: "f \<lbrace>\<lambda>s. \<not> (in_cur_domain t s)\<rbrace>"
  and idle_thread: "f \<lbrace>\<lambda>s. t \<noteq> idle_thread s\<rbrace>"
  shows "f \<lbrace>\<lambda>s. valid_cur_vcpu (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  unfolding valid_cur_vcpu_def valid_def
  using use_valid[OF _ active_cur_vcpu_of] use_valid[OF _ tcb_vcpu_at] use_valid[OF _ in_cur_domain]
        use_valid[OF _ idle_thread]
  by (fastforce simp: active_cur_vcpu_of_def)

lemma active_cur_vcpu_of_simps[simp]:
  "\<And>f. active_cur_vcpu_of (scheduler_action_update f s) = active_cur_vcpu_of s"
  "\<And>f. active_cur_vcpu_of (ready_queues_update f s) = active_cur_vcpu_of s"
  "\<And>x. active_cur_vcpu_of (s\<lparr>arch_state := arch_state s \<lparr>arm_vmid_table := x \<rparr>\<rparr>) = active_cur_vcpu_of s"
  "\<And>x. active_cur_vcpu_of (s\<lparr>arch_state := arch_state s \<lparr>arm_current_fpu_owner := x \<rparr>\<rparr>) = active_cur_vcpu_of s"
  by (clarsimp simp: active_cur_vcpu_of_def pred_tcb_at_def obj_at_def valid_cur_vcpu_def)+

lemma valid_cur_vcpu_simps[simp]:
  "\<And>f. valid_cur_vcpu (trans_state f s) = valid_cur_vcpu s"
  "\<And>x. valid_cur_vcpu (s\<lparr>arch_state := arch_state s \<lparr>arm_vmid_table := x \<rparr>\<rparr>) = valid_cur_vcpu s"
  by (clarsimp simp: valid_cur_vcpu_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def)+

crunch as_user
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (wp: crunch_wps simp: active_cur_vcpu_of_def)

lemma as_user_valid_cur_vcpu[wp]:
  "as_user tptr f \<lbrace>valid_cur_vcpu\<rbrace>"
  by (rule valid_cur_vcpu_lift; wpsimp wp: as_user_pred_tcb_at in_cur_domain_lift_weak)

lemma machine_state_update_active_cur_vcpu_of[simp]:
  "P (active_cur_vcpu_of (s\<lparr>machine_state := ms\<rparr>)) = P (active_cur_vcpu_of s)"
  by (fastforce simp: active_cur_vcpu_of_def)

crunch do_machine_op
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  and valid_cur_vcpu_cur_thread_update[wp]: "\<lambda>s. valid_cur_vcpu (s\<lparr>cur_thread := t\<rparr>)"
  (wp: valid_cur_vcpu_lift_cur_thread_update valid_cur_vcpu_lift crunch_wps)

lemma valid_cur_vcpu_vcpu_update[simp]:
  "vcpu_at v s \<Longrightarrow> valid_cur_vcpu (s\<lparr>kheap := (kheap s)(v \<mapsto> ArchObj (VCPU vcpu))\<rparr>) = valid_cur_vcpu s"
  by (clarsimp simp: valid_cur_vcpu_def active_cur_vcpu_of_def pred_tcb_at_def obj_at_def
                     in_cur_domain_def etcb_at_def etcbs_of'_def)

crunch vcpu_save_reg, vcpu_write_reg, save_virt_timer, vgic_update, vcpu_disable
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: set_vcpu_wp)

lemma set_vcpu_arch_tcb_at_cur_thread[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. arch_tcb_at P (cur_thread s) s\<rbrace>"
  apply (wpsimp wp: set_vcpu_wp get_vcpu_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

crunch vcpu_disable, vcpu_restore, vcpu_save, set_vm_root
  for arch_tcb_at_cur_thread[wp]: "\<lambda>s. arch_tcb_at P (cur_thread s) s"
  (wp: crunch_wps ignore: set_object)

crunch vcpu_update, do_machine_op, invalidate_asid, invalidate_vmid_entry
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (simp: active_cur_vcpu_of_def)

lemma active_cur_vcpu_of_arch_upd_eq:
  "arm_current_vcpu s' = arm_current_vcpu (arch_state s) \<Longrightarrow>
  active_cur_vcpu_of (s\<lparr>arch_state := s'\<rparr>) = active_cur_vcpu_of s"
  unfolding active_cur_vcpu_of_def by simp

crunch get_vmid, set_vm_root
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (simp: active_cur_vcpu_of_arch_upd_eq)

lemma vcpu_save_reg_active_cur_vcpu_of[wp]:
  "vcpu_save_reg vr reg \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  by (wpsimp simp: vcpu_save_reg_def)

crunch vcpu_restore, do_machine_op, vcpu_save_reg, vgic_update, save_virt_timer,
         vcpu_save_reg_range, vgic_update_lr, vcpu_enable, vcpu_save, set_vcpu
  for in_cur_domain[wp]: "in_cur_domain t"
  and valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift in_cur_domain_lift_weak crunch_wps simp: active_cur_vcpu_of_def)

lemma switch_vcpu_valid_cur_vcpu_cur_thread_update[wp]:
  "\<lbrace>arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = v) t\<rbrace>
   vcpu_switch v
   \<lbrace>\<lambda>_ s. valid_cur_vcpu (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  unfolding vcpu_switch_def
  apply (wpsimp simp: valid_cur_vcpu_def active_cur_vcpu_of_def wp: hoare_vcg_imp_lift' in_cur_domain_lift_weak
         | wps)+
  by fastforce

lemma switch_vcpu_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = v) (cur_thread s) s\<rbrace>
   vcpu_switch v
   \<lbrace>\<lambda>_ s. valid_cur_vcpu s\<rbrace>"
  unfolding vcpu_switch_def
  apply (wpsimp simp: valid_cur_vcpu_def active_cur_vcpu_of_def wp: hoare_vcg_imp_lift' | wps)+
  by fastforce

lemma tcb_cur_fpu_update_tcb_vcpu_at[wp]:
  "arch_thread_set (tcb_cur_fpu_update f) t' \<lbrace>arch_tcb_at (\<lambda>itcb. P (itcb_vcpu itcb)) t\<rbrace>"
  apply (simp add: arch_thread_set_def set_object_def get_object_def)
  apply wp
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_rev arch_tcb_update_aux3)
  done

lemma tcb_cur_fpu_update_active_cur_vcpu_of[wp]:
  "arch_thread_set (tcb_cur_fpu_update f) t \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  apply (wpsimp wp: arch_thread_set_wp)
  by (clarsimp simp: active_cur_vcpu_of_def)

crunch lazy_fpu_restore
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  and arch_tcb_vcpu_at[wp]: "arch_tcb_at (\<lambda>itcb. P (itcb_vcpu itcb)) t"
  (ignore: arch_thread_set wp: crunch_wps)

crunch set_vm_root, set_tcb_queue, lazy_fpu_restore
  for valid_cur_vcpu_cur_thread_update[wp]: "\<lambda>s. valid_cur_vcpu (s\<lparr>cur_thread := t\<rparr>)"
  (wp: valid_cur_vcpu_lift_cur_thread_update in_cur_domain_lift_weak wp_del: set_tcb_queue_wp)

crunch tcb_sched_action
  for valid_cur_vcpu_cur_thread_update[wp]: "\<lambda>s. valid_cur_vcpu (s\<lparr>cur_thread := t\<rparr>)"

lemma arch_switch_to_thread_valid_cur_vcpu_cur_thread_update[wp]:
  "\<lbrace>\<top>\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_ s. valid_cur_vcpu (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  unfolding arch_switch_to_thread_def
  apply wpsimp
  by (fastforce simp: active_cur_vcpu_of_def pred_tcb_at_def obj_at_def get_tcb_def
               split: option.splits kernel_object.splits)

lemma switch_to_thread_valid_cur_vcpu[wp]:
  "\<lbrace>\<top>\<rbrace> switch_to_thread t \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding switch_to_thread_def
  by wpsimp

lemma arch_switch_to_idle_thread_valid_cur_vcpu_cur_thread_update[wp]:
  "\<lbrace>\<lambda>s. valid_idle s \<and> t = idle_thread s\<rbrace>
   arch_switch_to_idle_thread
   \<lbrace>\<lambda>_ s. valid_cur_vcpu (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  unfolding arch_switch_to_idle_thread_def set_global_user_vspace_def
  apply wpsimp
  by (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def valid_arch_idle_def)

lemma switch_to_idle_thread_valid_cur_vcpu[wp]:
  "\<lbrace>valid_idle\<rbrace>
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
  by (clarsimp simp: valid_cur_vcpu_def pred_tcb_at_def active_cur_vcpu_of_def obj_at_def
                     in_cur_domain_def etcb_at_def etcbs_of'_def)

lemma vcpu_invalidate_active_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. arm_current_vcpu (arch_state s) \<noteq> None
        \<and> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = None) (cur_thread s) s\<rbrace>
   vcpu_invalidate_active
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding vcpu_invalidate_active_def
  by (wpsimp simp: valid_cur_vcpu_def active_cur_vcpu_of_def | wps)+

lemma vcpu_invalid_active_arm_current_vcpu_None[wp]:
  "\<lbrace>\<top>\<rbrace> vcpu_invalidate_active \<lbrace>\<lambda>_ s. arm_current_vcpu (arch_state s) = None\<rbrace>"
  unfolding vcpu_invalidate_active_def
  by wpsimp

lemma dissociate_vcpu_tcb_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s) \<and> in_cur_domain (cur_thread s) s\<rbrace>
   dissociate_vcpu_tcb vcpu_ptr t
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding dissociate_vcpu_tcb_def
  apply (wpsimp wp: hoare_vcg_imp_lift' arch_thread_get_wp get_vcpu_wp)
  by (fastforce simp: valid_cur_vcpu_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def
                      sym_refs_def state_hyp_refs_of_def in_omonad
               split: bool.splits option.splits)

crunch dissociate_vcpu_tcb
  for etcbs[wp]: "\<lambda>s. P (etcbs_of s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps)

lemma associate_vcpu_tcb_valid_cur_vcpu:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s) \<and> in_cur_domain (cur_thread s) s\<rbrace>
   associate_vcpu_tcb vcpu_ptr t
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding associate_vcpu_tcb_def
  apply (wpsimp wp: hoare_vcg_imp_lift')
        apply (wpsimp wp: arch_thread_set_wp)
       apply (wpsimp wp: arch_thread_set_wp)
      apply (rule_tac Q'="\<lambda>_ s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s)" in hoare_post_imp)
       apply (clarsimp simp: pred_tcb_at_def obj_at_def valid_cur_vcpu_def active_cur_vcpu_of_def
                             in_cur_domain_def etcb_at_def etcbs_of'_def)
      by (wpsimp wp: get_vcpu_wp hoare_drop_imps hoare_vcg_all_lift | wps)+

crunch set_thread_state, tcb_sched_action
  for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak in_cur_domain_lift_weak)

crunch activate_thread
  for valid_cur_vcpu[wp]: valid_cur_vcpu

crunch switch_local_fpu_owner
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift in_cur_domain_lift_weak)

lemma guarded_switch_to_cur_vcpu[wp]:
  "\<lbrace>\<top>\<rbrace> guarded_switch_to t \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  by (wpsimp simp: guarded_switch_to_def)

lemma choose_thread_valid_cur_vcpu[wp]:
  "\<lbrace>valid_idle\<rbrace> choose_thread \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  by (wpsimp simp: choose_thread_def)

crunch set_scheduler_action
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (simp: valid_cur_vcpu_def)

lemma schedule_choose_new_thread_cur_vcpu[wp]:
  "\<lbrace>valid_idle\<rbrace> schedule_choose_new_thread \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  by (wpsimp simp: schedule_choose_new_thread_def)

crunch schedule
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (simp: valid_cur_vcpu_def active_cur_vcpu_of_def wp: crunch_wps)

crunch cancel_all_ipc, blocked_cancel_ipc, unbind_maybe_notification, cancel_all_signals,
         bind_notification, fast_finalise, deleted_irq_handler, post_cap_deletion, cap_delete_one,
         reply_cancel_ipc, cancel_ipc, update_waiting_ntfn, send_signal, send_ipc, send_fault_ipc,
         receive_ipc, handle_fault, handle_interrupt, handle_vm_fault, handle_hypervisor_fault,
         send_signal, do_reply_transfer, unbind_notification, suspend, cap_swap, bind_notification,
         restart, reschedule_required, possible_switch_to, thread_set_priority, reply_from_kernel
  for arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: mapM_x_wp_inv thread_set.arch_state crunch_wps dxo_wp_weak
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

crunch blocked_cancel_ipc, cap_delete_one, cancel_signal
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  (wp: crunch_wps simp: crunch_simps)

lemma reply_cancel_ipc_arch_tcb_at[wp]:
  "reply_cancel_ipc ntfnptr \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding reply_cancel_ipc_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)

crunch cancel_ipc, send_ipc, receive_ipc
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  (wp: crunch_wps simp: crunch_simps)

lemma send_fault_ipc_arch_tcb_at[wp]:
  "send_fault_ipc tptr fault \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding send_fault_ipc_def thread_set_def Let_def
  by (wpsimp wp: set_object_wp hoare_drop_imps hoare_vcg_all_liftE_R
           simp: pred_tcb_at_def obj_at_def get_tcb_def)

crunch handle_fault, handle_interrupt, handle_vm_fault, handle_hypervisor_fault, send_signal
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  (wp: mapM_x_wp_inv crunch_wps thread_set_no_change_tcb_pred)

lemma thread_set_fault_arch_tcb_at[wp]:
  "thread_set (tcb_fault_update f) r \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding thread_set_def
  by (wpsimp wp: set_object_wp simp: pred_tcb_at_def obj_at_def get_tcb_def)

lemma do_reply_transfer_arch_tcb_at[wp]:
  "do_reply_transfer sender receiver slot grant \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding do_reply_transfer_def
  by (wpsimp wp: gts_wp split_del: if_split)

crunch set_extra_badge, send_ipc
  for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  (wp: crunch_wps transfer_caps_loop_pres simp: crunch_simps)

crunch send_fault_ipc, receive_ipc, handle_fault, handle_interrupt, handle_vm_fault,
         handle_hypervisor_fault, send_signal, do_reply_transfer, cancel_all_ipc,
         cancel_all_signals, unbind_maybe_notification, suspend, deleting_irq_handler,
         unbind_notification
  for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak crunch_wps in_cur_domain_lift_weak thread_set_etcbs hoare_vcg_all_liftE_R dxo_wp_weak
   simp: crunch_simps)

crunch init_arch_objects, reset_untyped_cap
  for arch_state[wp]: "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps preemption_point_inv unless_wp mapME_x_wp'
   simp: crunch_simps)

crunch invoke_untyped
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv
   simp: crunch_simps mapM_x_def[symmetric] active_cur_vcpu_of_def)

\<comment> \<open>The following @{term etcb_at} lemmas extend earlier ones that don't have the Qs. These have
   extra preconditions however, so we keep the other lemmas around.\<close>
lemma delete_objects_etcb_at':
  "\<lbrace>\<lambda>s. Q (etcb_at P t s) \<and> (t \<notin> {ptr..ptr + 2 ^ bits - 1})\<rbrace>
   delete_objects ptr bits
   \<lbrace>\<lambda>_ s. Q (etcb_at P t s)\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (wpsimp simp: detype_def)
  apply (auto simp: detype_def etcbs_of'_def etcb_at'_def)
  done

lemma reset_untyped_cap_etcb_at':
  "\<lbrace>\<lambda>s. Q (etcb_at P t s) \<and> invs s \<and> cte_wp_at (\<lambda>cp. t \<notin> cap_range cp \<and> is_untyped_cap cp) slot s\<rbrace>
   reset_untyped_cap slot
   \<lbrace>\<lambda>_ s. Q (etcb_at P t s)\<rbrace>"
  apply (simp add: reset_untyped_cap_def)
   apply (wpsimp wp: mapME_x_inv_wp preemption_point_inv get_cap_wp delete_objects_etcb_at')
  apply (auto simp: cte_wp_at_caps_of_state bits_of_def is_cap_simps)
  done

lemma invoke_untyped_etcb_at':
  "\<lbrace>\<lambda>s. Q (etcb_at P t s) \<and> invs s \<and> st_tcb_at (Not o inactive and Not \<circ> idle) t s \<and> ct_active s
        \<and> valid_untyped_inv ui s\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>_ s. st_tcb_at (Not o inactive) t s \<longrightarrow> Q (etcb_at P t s)\<rbrace>"
  apply (cases ui)
  apply (simp add: mapM_x_def[symmetric] invoke_untyped_def)
  apply (wpsimp wp: mapM_x_wp'
                    create_cap_no_pred_tcb_at typ_at_pred_tcb_at_lift
                    hoare_convert_imp[OF create_cap_no_pred_tcb_at]
                    hoare_convert_imp[OF _ init_arch_objects_etcbs_of]
                    hoare_drop_impE_E reset_untyped_cap_etcb_at'[where Q=Q])
  apply (cases ui, clarsimp)
  apply (frule(1) st_tcb_ex_cap[OF _ invs_iflive])
   apply (clarsimp split: Structures_A.thread_state.splits)
  apply (drule ex_nonz_cap_to_overlap,
         ((simp add: cte_wp_at_caps_of_state descendants_range_def2 empty_descendants_range_in)+))
  done

lemma invoke_untyped_etcb_at'':
  "\<lbrace>\<lambda>s. Q (etcb_at P t s) \<and> invs s \<and> st_tcb_at (Not o inactive and Not \<circ> idle) t s \<and> ct_active s \<and> valid_untyped_inv ui s\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>_ s. Q (etcb_at P t s)\<rbrace>"
  apply (rule hoare_post_imp[where Q'="\<lambda>_ s. st_tcb_at (Not \<circ> inactive) t s \<and> (st_tcb_at (Not \<circ> inactive) t s \<longrightarrow> Q (etcb_at P t s))"])
   apply simp
  apply (wpsimp wp: invoke_untyped_etcb_at')+
  done

lemma invoke_untyped_valid_cur_vcpu:
  "\<lbrace>valid_cur_vcpu and invs and valid_untyped_inv ui and ct_active\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule valid_cur_vcpu_lift_ct_Q)
      apply (clarsimp simp: in_cur_domain_def)
      apply (rule_tac f=cur_thread in hoare_lift_Pf2)
       apply (rule_tac f=cur_domain in hoare_lift_Pf2)
        apply (rule invoke_untyped_etcb_at'')
       apply wpsimp
      apply wpsimp
     apply (rule_tac f=cur_thread in hoare_lift_Pf2; wpsimp)
    apply (rule_tac f=cur_thread in hoare_lift_Pf2)
     apply (rule invoke_untyped_pred_tcb_at)
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

crunch cap_insert, cap_move
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak in_cur_domain_lift_weak dxo_wp_weak)

crunch suspend, unbind_notification, cap_swap_for_delete, fpu_release
  for state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  (wp: crunch_wps thread_set_hyp_refs_trivial dxo_wp_weak simp: crunch_simps ignore: arch_thread_set)

crunch fpu_release
  for valid_cur_vcpu[wp]: valid_cur_vcpu

lemma prepare_thread_delete_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s) \<and> in_cur_domain (cur_thread s) s\<rbrace>
   prepare_thread_delete t
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding prepare_thread_delete_def
  by (wpsimp wp: dissociate_vcpu_tcb_valid_cur_vcpu arch_thread_get_wp
                 hoare_drop_imps hoare_vcg_all_lift)

crunch delete_asid_pool
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  (wp: crunch_wps simp: crunch_simps)

crunch store_pte, set_asid_pool
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps simp: crunch_simps active_cur_vcpu_of_def)

crunch unmap_page, unmap_page_table, delete_asid
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  (wp: crunch_wps valid_cur_vcpu_lift simp: crunch_simps)

crunch delete_asid_pool, unmap_page, unmap_page_table, delete_asid
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift in_cur_domain_lift_weak crunch_wps simp: crunch_simps)

crunch vcpu_finalise, arch_finalise_cap, finalise_cap
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (simp: crunch_simps)

crunch prepare_thread_delete
  for sym_refs_state_hyp_refs_of[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of s)"
  (wp: crunch_wps simp: crunch_simps)

crunch invalidate_tlb_by_asid_va, delete_asid_pool, deleting_irq_handler
  for state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  (wp: crunch_wps simp: crunch_simps)

lemma unmap_page_state_hyp_refs_of[wp]:
  "unmap_page pgsz asid vptr pptr \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  unfolding unmap_page_def
  by (wpsimp wp: hoare_drop_imps mapM_wp_inv get_pte_wp store_pte_state_hyp_refs_of)

crunch delete_asid, vcpu_finalise, unmap_page_table, finalise_cap
  for state_hyp_refs_of[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of s)"
  (wp: crunch_wps)

lemma preemption_point_state_hyp_refs_of[wp]:
  "preemption_point \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp wp: preemption_point_inv)

lemma preemption_point_valid_cur_vcpu[wp]:
  "preemption_point \<lbrace>valid_cur_vcpu\<rbrace>"
  apply (wpsimp wp: preemption_point_inv)
    by (clarsimp simp: valid_cur_vcpu_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def)+

crunch cap_swap_for_delete, empty_slot, finalise_cap
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak in_cur_domain_lift_weak dxo_wp_weak)

lemma rec_del_sym_refs_state_hyp_refs_of[wp]:
  "rec_del call \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  by (rule rec_del_preservation; wpsimp)

crunch cap_delete
  for state_hyp_refs_of[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of s)"

lemma rec_del_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s) \<and> in_cur_domain (cur_thread s) s\<rbrace>
   rec_del call
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (rule_tac Q'="\<lambda>_. ?pre" in hoare_post_imp, fastforce)
  by (rule rec_del_preservation; (wpsimp wp: in_cur_domain_lift_weak | wps)+)

crunch cap_delete
  for valid_cur_vcpu[wp]: valid_cur_vcpu

lemma cap_revoke_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s) \<and> in_cur_domain (cur_thread s) s\<rbrace>
   cap_revoke slot
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (rule_tac Q'="\<lambda>_. ?pre" in hoare_post_imp, fastforce)
  by (wpsimp wp: cap_revoke_preservation)

crunch cancel_badged_sends, invoke_irq_control, invoke_irq_handler
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  (wp: filterM_preserved)

crunch store_pte, set_cap, set_mrs
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (simp: active_cur_vcpu_of_def)

crunch perform_page_table_invocation, perform_page_invocation,
         perform_asid_pool_invocation, invoke_vcpu_inject_irq, invoke_vcpu_read_register,
         invoke_vcpu_write_register, invoke_vcpu_ack_vppi
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  and active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (wp: crunch_wps simp: crunch_simps)

crunch cancel_badged_sends, invoke_irq_control, invoke_irq_handler, invoke_vcpu_inject_irq,
         bind_notification
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak in_cur_domain_lift_weak filterM_preserved)

crunch perform_asid_pool_invocation, perform_page_table_invocation,
         perform_page_invocation, invoke_vcpu_read_register,
         invoke_vcpu_write_register, invoke_vcpu_ack_vppi
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift in_cur_domain_lift_weak)

lemma invoke_cnode_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s) \<and> in_cur_domain (cur_thread s) s\<rbrace>
   invoke_cnode i
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding invoke_cnode_def
  by (wpc | wpsimp wp: hoare_drop_imps hoare_vcg_all_lift)+

lemma thread_set_valid_cur_vcpu_unchanged:
  "\<lbrakk>\<And>tcb. tcb_arch (f tcb) = tcb_arch tcb; \<And>tcb. tcb_domain (f tcb) = tcb_domain tcb\<rbrakk>
   \<Longrightarrow> thread_set f tptr \<lbrace>valid_cur_vcpu\<rbrace>"
  apply (rule valid_cur_vcpu_lift_weak; (solves wpsimp)?)
   apply (clarsimp simp: thread_set_def)
   apply (wpsimp wp: set_object_wp)
   apply (fastforce simp: pred_tcb_at_def obj_at_def get_tcb_def)
  apply (clarsimp simp: in_cur_domain_def)
  apply (wp_pre, wps, wpsimp wp: thread_set_no_change_etcb_at, clarsimp)
  done

crunch restart, reschedule_required, possible_switch_to
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  (wp: thread_set_no_change_tcb_pred)

crunch restart, reschedule_required, possible_switch_to, thread_set_priority
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak in_cur_domain_lift_weak thread_set_valid_cur_vcpu_unchanged)

crunch restart, arch_post_modify_registers, arch_get_sanitise_register_info
  for valid_cur_vcpu[wp]: valid_cur_vcpu

lemma fault_handler_update_valid_cur_vcpu[wp]:
  "option_update_thread thread (tcb_fault_handler_update \<circ> f) opt \<lbrace>valid_cur_vcpu\<rbrace>"
  unfolding option_update_thread_def
  by (wpsimp wp: thread_set_valid_cur_vcpu_unchanged)

crunch set_mcpriority, set_priority, set_flags, arch_post_set_flags
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (simp: set_priority_def wp: thread_set_valid_cur_vcpu_unchanged)

crunch set_mcpriority, set_priority
  for state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and in_cur_domain[wp]: "\<lambda>s. P (in_cur_domain t s)"
  (wp: thread_set_hyp_refs_trivial thread_set_no_change_etcb_at
   simp: thread_set_priority_def in_cur_domain_def
   ignore: thread_set)

lemma invoke_tcb_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s) \<and> in_cur_domain (cur_thread s) s\<rbrace>
   invoke_tcb iv
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  apply (cases iv; clarsimp; (solves \<open>wpsimp wp: mapM_x_wp_inv\<close>)?)
   defer
   subgoal for tcb_ptr ntfn_ptr_opt
     by (case_tac ntfn_ptr_opt; wpsimp)
  \<comment> \<open>ThreadControl\<close>
  by (wpsimp wp: hoare_drop_imps check_cap_inv)
     (wpsimp wp: hoare_drop_imps | wpsimp wp: check_cap_inv thread_set_valid_cur_vcpu_unchanged | wp_pre, wps)+

lemma thread_set_domain_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. (valid_cur_vcpu s \<or> (tptr = cur_thread s \<and> cur_domain s \<noteq> new_dom))
        \<and> in_cur_domain (cur_thread s) s \<and> tptr \<noteq> idle_thread s\<rbrace>
   thread_set_domain tptr new_dom
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  by (auto simp: valid_cur_vcpu_def active_cur_vcpu_of_def in_cur_domain_def pred_tcb_at_def
                 obj_at_def get_tcb_def etcb_at_def etcbs_of'_def)

lemma set_domain_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. (valid_cur_vcpu s \<or> (tptr = cur_thread s \<and> cur_domain s \<noteq> new_dom))
        \<and> in_cur_domain (cur_thread s) s \<and> tptr \<noteq> idle_thread s\<rbrace>
   set_domain tptr new_dom
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding set_domain_def
  by (wpsimp wp: hoare_vcg_disj_lift | wps)+

lemma vcpu_flush_valid_cur_vcpu_not_active:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> active_cur_vcpu_of s = None \<and> in_cur_domain (cur_thread s) s\<rbrace>
   vcpu_flush
   \<lbrace>\<lambda>_ s. valid_cur_vcpu s\<rbrace>"
  unfolding vcpu_flush_def
  apply wpsimp
  by (auto simp: valid_cur_vcpu_def)

crunch arch_prepare_set_domain
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  (wp: crunch_wps simp: crunch_simps)

\<comment> \<open>FIXME: move earlier, along with sym_refs_tcb_vcpu and sym_refs_vcpu_tcb from Refine\<close>
lemma sym_refs_kheap_tcb_vcpu:
  "\<lbrakk>kheap s tptr = Some (TCB tcb); tcb_vcpu (tcb_arch tcb) = Some vcpuptr; sym_refs (state_hyp_refs_of s)\<rbrakk>
   \<Longrightarrow> \<exists>vcpu. kheap s vcpuptr = Some (ArchObj (VCPU vcpu)) \<and> vcpu_tcb vcpu = Some tptr"
  apply (drule_tac x=tptr in sym_refsD[rotated])
   apply (fastforce simp: state_hyp_refs_of_def)
  apply (auto simp: state_hyp_refs_of_def hyp_refs_of_def refs_of_ao_def tcb_vcpu_refs_def vcpu_tcb_refs_def
             split: option.splits kernel_object.splits arch_kernel_obj.splits)
  done

lemma arch_prepare_set_domain_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s) \<and> in_cur_domain (cur_thread s) s\<rbrace>
   arch_prepare_set_domain t new_dom
   \<lbrace>\<lambda>_ s. valid_cur_vcpu s \<or> t = cur_thread s \<and> cur_domain s \<noteq> new_dom\<rbrace>"
  unfolding arch_prepare_set_domain_def vcpu_flush_if_current_def
  apply (wpsimp wp: hoare_vcg_disj_lift vcpu_flush_valid_cur_vcpu_not_active arch_thread_get_wp)
  apply (auto simp: valid_cur_vcpu_def active_cur_vcpu_of_def in_cur_domain_def pred_tcb_at_def
                    obj_at_def get_tcb_def etcb_at_def etcbs_of'_def
             dest!: sym_refs_kheap_tcb_vcpu
             split: bool.splits option.splits)
  done

lemma invoke_domain_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> sym_refs (state_hyp_refs_of s) \<and> in_cur_domain (cur_thread s) s \<and> t \<noteq> idle_thread s\<rbrace>
   invoke_domain t new_dom
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding invoke_domain_def
  by (wpsimp | wps)+

crunch perform_asid_control_invocation
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (simp: active_cur_vcpu_of_def)

crunch perform_vspace_invocation, perform_sgi_invocation, handle_spurious_irq,
       perform_smc_invocation
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  and valid_cur_vcpu[wp]: valid_cur_vcpu

\<comment> \<open>The following @{term etcb_at} lemmas extend earlier ones that don't have the Qs. These have
   extra preconditions however, so we keep the other lemmas around.\<close>
lemma perform_asid_control_etcb_at':
  "\<lbrace>\<lambda>s. Q (etcb_at P t s) \<and> st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t s \<and> invs s \<and> valid_aci aci s \<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>r s. st_tcb_at (Not \<circ> inactive) t s \<longrightarrow> Q (etcb_at P t s)\<rbrace>"
  apply (simp add: perform_asid_control_invocation_def)
  apply wpsimp
       apply (wp hoare_imp_lift_something typ_at_pred_tcb_at_lift)[1]
      apply (rule hoare_drop_imps)
      apply (wpsimp wp: delete_objects_etcb_at')+
  apply (rename_tac parent_oref parent_cref base)
  apply (frule st_tcb_ex_cap)
    apply fastforce
   apply (clarsimp split: Structures_A.thread_state.splits)
  apply (clarsimp simp: ex_nonz_cap_to_def valid_aci_def)
  apply (frule invs_untyped_children)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (erule_tac ptr="(parent_oref, parent_cref)"
                in untyped_children_in_mdbE[where P="\<lambda>c. t \<in> zobj_refs c" for t])
      apply (simp add: cte_wp_at_caps_of_state)
     apply simp
    apply (simp add: cte_wp_at_caps_of_state)
    apply fastforce
   apply (clarsimp simp: zobj_refs_to_obj_refs)
   apply (erule(1) in_empty_interE)
   apply (clarsimp simp: pageBits_def)
  apply simp
  done

lemma perform_asid_control_etcb_at'':
  "\<lbrace>\<lambda>s. Q (etcb_at P t s) \<and> st_tcb_at (Not \<circ> inactive and Not \<circ> idle) t s \<and> ct_active s \<and> invs s \<and> valid_aci aci s\<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>r s. Q (etcb_at P t s)\<rbrace>"
  apply (rule hoare_post_imp[where Q'="\<lambda>_ s. st_tcb_at (Not \<circ> inactive) t s \<and> (st_tcb_at (Not \<circ> inactive) t s \<longrightarrow> Q (etcb_at P t s))"])
   apply simp
  apply (wpsimp wp: perform_asid_control_invocation_st_tcb_at perform_asid_control_etcb_at')+
  done

lemma perform_asid_control_invocation_valid_cur_vcpu:
  "\<lbrace>valid_cur_vcpu and invs and valid_aci iv and ct_active\<rbrace>
   perform_asid_control_invocation iv
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule valid_cur_vcpu_lift_ct_Q)
      apply (clarsimp simp: in_cur_domain_def)
      apply (rule_tac f=cur_thread in hoare_lift_Pf2)
       apply (rule_tac f=cur_domain in hoare_lift_Pf2)
        apply (rule perform_asid_control_etcb_at'')
       apply wpsimp
      apply wpsimp
     apply (rule_tac f=cur_thread in hoare_lift_Pf2; wpsimp)
    apply (rule_tac f=cur_thread in hoare_lift_Pf2)
     apply (rule perform_asid_control_invocation_pred_tcb_at)
    apply wpsimp
   apply wpsimp
  apply (fastforce simp: pred_tcb_at_def obj_at_def ct_in_state_def)
  done

lemma perform_vcpu_invocation_valid_cur_vcpu:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> invs s \<and> sym_refs (state_hyp_refs_of s) \<and> in_cur_domain (cur_thread s) s\<rbrace>
   perform_vcpu_invocation iv
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding perform_vcpu_invocation_def
  by (wpsimp wp: associate_vcpu_tcb_valid_cur_vcpu)

crunch send_ipc
  for valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift in_cur_domain_lift_weak simp: active_cur_vcpu_of_def)

lemma perform_invocation_valid_cur_vcpu[wp]:
  "\<lbrace>\<lambda>s. valid_cur_vcpu s \<and> invs s \<and> valid_invocation iv s \<and> ct_active s \<and>
        in_cur_domain (cur_thread s) s\<rbrace>
   perform_invocation blocking call iv
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  apply (case_tac iv, simp_all; (solves wpsimp)?)
   apply (wpsimp wp: invoke_untyped_valid_cur_vcpu)
  unfolding arch_perform_invocation_def
  apply (wpsimp wp: perform_vcpu_invocation_valid_cur_vcpu
                    perform_asid_control_invocation_valid_cur_vcpu)
  apply (fastforce simp: valid_arch_inv_def)
  done

crunch reply_from_kernel, receive_signal
  for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  and valid_cur_vcpu[wp]: valid_cur_vcpu
  (wp: valid_cur_vcpu_lift_weak in_cur_domain_lift_weak simp: crunch_simps)

lemma handle_invocation_valid_cur_vcpu[wp]:
  "\<lbrace>valid_cur_vcpu and einvs and ct_active and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   handle_invocation calling blocking
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding handle_invocation_def
  by (wp syscall_valid set_thread_state_ct_st
      | simp add: split_def | wpc | wps
      | wp (once) hoare_drop_imps)+
     (auto simp: ct_in_state_def valid_sched_def elim: st_tcb_ex_cap
         intro!: ct_in_cur_domain_active_resume_cur_thread)

lemma handle_recv_valid_cur_vcpu[wp]:
  "handle_recv is_blocking \<lbrace>valid_cur_vcpu\<rbrace>"
  unfolding handle_recv_def Let_def ep_ntfn_cap_case_helper delete_caller_cap_def
  by (wpsimp wp: hoare_drop_imps)

lemma maybe_handle_interrupt_valid_cur_vcpu[wp]:
  "\<lbrace>valid_cur_vcpu and invs\<rbrace>
   maybe_handle_interrupt in_kernel
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  unfolding maybe_handle_interrupt_def
  by wpsimp

lemma handle_event_valid_cur_vcpu:
  "\<lbrace>valid_cur_vcpu and einvs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   handle_event e
   \<lbrace>\<lambda>_. valid_cur_vcpu\<rbrace>"
  apply (cases e; clarsimp; (solves wpsimp)?)
  unfolding handle_call_def handle_send_def handle_reply_def handle_yield_def
  by (wpsimp wp: get_cap_wp)+

lemma call_kernel_valid_cur_vcpu:
  "\<lbrace>valid_cur_vcpu and einvs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   call_kernel e
   \<lbrace>\<lambda>_ . valid_cur_vcpu\<rbrace>"
  unfolding call_kernel_def
  apply (simp flip: bind_assoc)
  by (wpsimp wp: handle_event_valid_cur_vcpu hoare_vcg_if_lift2 hoare_drop_imps
      | strengthen invs_valid_idle)+


section \<open>cur_vcpu_in_cur_domain\<close>

\<comment> \<open> Show that the TCB bound to the current VCPU is in the current domain. \<close>

\<comment> \<open>FIXME: @{term cur_vcpu} could be reworked so that it could be reused here\<close>
definition cur_vcpu_tcb :: "'z::state_ext state \<Rightarrow> obj_ref option" where
  "cur_vcpu_tcb s \<equiv>
     case arm_current_vcpu (arch_state s) of
       Some (v, _) \<Rightarrow> vcpu_tcbs_of s v
     | None \<Rightarrow> None"

definition cur_vcpu_in_cur_domain :: "det_ext state \<Rightarrow> bool" where
  "cur_vcpu_in_cur_domain s \<equiv>
     case cur_vcpu_tcb s of
       Some t \<Rightarrow> in_cur_domain t s
     | None \<Rightarrow> True"

lemmas cur_vcpu_in_cur_domain_defs = cur_vcpu_in_cur_domain_def cur_vcpu_tcb_def in_cur_domain_def

lemma cur_vcpu_in_cur_domain_lift_strong:
  assumes [wp]: "\<And>P. f \<lbrace>\<lambda>s. P (arm_current_vcpu (arch_state s))\<rbrace>"
                "\<And>P. f \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
                "\<And>P. f \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
                "\<And>P t. f \<lbrace>etcb_at (\<lambda>t. P (etcb_domain t)) t\<rbrace>"
  shows "f \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
  unfolding cur_vcpu_in_cur_domain_defs
  by (wp_pre, wps, wpsimp wp: valid_case_option_post_wp split: option.splits)

lemma cur_vcpu_in_cur_domain_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arm_current_vcpu (arch_state s))\<rbrace>"
          "\<And>P. f \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
          "\<And>P. f \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
          "\<And>P. f \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  shows "f \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
 by (rule cur_vcpu_in_cur_domain_lift_strong assms)+

\<comment> \<open>This simp could possibly be avoided if arm_current_vcpu updates were wrapped in a function
    instead of directly using modifies.\<close>
lemma cur_vcpu_in_cur_domain_current_vcpu_update[simp]:
  "cur_vcpu_in_cur_domain (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := Some (v, b)\<rparr>\<rparr>)
   = (\<forall>t. vcpu_tcbs_of s v = Some t \<longrightarrow> in_cur_domain t s)"
  "cur_vcpu_in_cur_domain (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := None\<rparr>\<rparr>)"
  by (auto simp: cur_vcpu_in_cur_domain_defs split: option.splits)

\<comment> \<open>FIXME: use projections instead of this\<close>
lemma cur_vcpu_in_cur_domain_updates[simp]:
  "cur_vcpu_in_cur_domain (cur_thread_update f_ct s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (machine_state_update f_ms s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (cdt_update f_cdt s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (cdt_list_update f_cdt_list s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (work_units_completed_update f_work_units s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (interrupt_states_update f_interrupt_states s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (is_original_cap_update f_orig_cap s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (arch_state_update (arm_asid_table_update f_asid_table) s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (s\<lparr>arch_state := (arm_asid_table_update f_asid_table) (arch_state s)\<rparr>) = cur_vcpu_in_cur_domain s"
  by (auto simp: cur_vcpu_in_cur_domain_defs)

\<comment> \<open>schedule\<close>

lemma as_user_vcpus_of[wp]:
  "as_user t f \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding as_user_def
  by (wpsimp wp: set_object_wp_strong)
     (fastforce simp: opt_map_def obj_at_def split: option.splits elim!: rsubst[where P=P])

crunch set_scheduler_action, tcb_sched_action, as_user
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift)

lemma vcpu_write_reg_vcpu_tcbs_of[wp]:
  "vcpu_write_reg vr reg val \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
  unfolding vcpu_write_reg_def
  by wpsimp (fastforce simp: opt_map_def elim!: rsubst[where P=P])

lemma vgic_update_vcpu_tcbs_of[wp]:
  "vgic_update vr f \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
  unfolding vgic_update_def
  by wpsimp (fastforce simp: opt_map_def elim!: rsubst[where P=P])

lemma vcpu_save_reg_vcpu_tcbs_of[wp]:
  "vcpu_save_reg vr reg \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
  unfolding vcpu_save_reg_def
  apply wpsimp
  by (fastforce simp: opt_map_def elim!: rsubst[where P=P])

lemma save_virt_timer_vcpu_tcbs_of[wp]:
  "save_virt_timer vcpu_ptr \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
  unfolding save_virt_timer_def
  apply wpsimp
         apply (rule hoare_post_imp[where Q'="\<lambda>_ s. P (vcpu_tcbs_of s)"])
          apply (fastforce simp: opt_map_def elim!: rsubst[where P=P])
         by wpsimp+

crunch vcpu_disable, vcpu_restore, vcpu_save
  for vcpu_tcbs_of[wp]: "\<lambda>s. P (vcpu_tcbs_of s)"
  (wp: crunch_wps)

lemma vcpu_switch_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> none_top ((\<lambda>t. in_cur_domain t s) |< vcpu_tcbs_of s) v\<rbrace>
   vcpu_switch v
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding vcpu_switch_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift in_cur_domain_lift_weak)
  by (auto simp: cur_vcpu_in_cur_domain_defs opt_pred_def)

crunch set_vm_root, lazy_fpu_restore
  for vcpus_of[wp]: "\<lambda>s. P (vcpus_of s)"
  and arm_current_vcpu[wp]: "\<lambda>s. P (arm_current_vcpu (arch_state s))"
  (wp: crunch_wps set_object_wp_strong simp: crunch_simps)

crunch set_vm_root, set_global_user_vspace, lazy_fpu_restore
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift)

lemma arch_switch_to_thread_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> valid_objs s \<and> in_cur_domain t s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   arch_switch_to_thread t
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding arch_switch_to_thread_def
  apply wpsimp
  apply (frule (1) valid_tcb_objs)
  apply (clarsimp simp: valid_tcb_def valid_arch_tcb_def typ_at_eq_kheap_obj)
  apply (drule (1) bound_tcb_bound_vcpu_at[where tcbptr=t])
   apply (fastforce simp: pred_tcb_def2)
  apply (auto simp: in_omonad)
  done

crunch guarded_switch_to, switch_to_idle_thread
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: crunch_wps)

lemma choose_thread_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> valid_queues s \<and> valid_objs s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   choose_thread
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding choose_thread_def
  apply wpsimp
  apply (fastforce dest!: next_thread_queued split: option.splits
                   simp: etcb_at_def next_thread_def valid_queues_def in_cur_domain_def)
  done

lemma next_domain_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. arm_current_vcpu (arch_state s) = None\<rbrace> next_domain \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding next_domain_def Let_def
  by (wpsimp wp: dxo_wp_weak simp: cur_vcpu_in_cur_domain_defs)

lemma vcpu_flush_arm_current_vcpu_None[wp]:
  "\<lbrace>\<top>\<rbrace> vcpu_flush \<lbrace>\<lambda>_ s. arm_current_vcpu (arch_state s) = None\<rbrace>"
  unfolding vcpu_flush_def
  by wpsimp

crunch next_domain, vcpu_flush, switch_local_fpu_owner
  for hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  and valid_objs[wp]: valid_objs
  (simp: crunch_simps wp: dxo_wp_weak crunch_wps ignore: arch_thread_set)

lemma schedule_choose_new_thread_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> valid_queues s \<and> valid_objs s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding schedule_choose_new_thread_def arch_prepare_next_domain_def
  by wpsimp

lemma schedule_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> valid_sched s \<and> valid_objs s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   schedule
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding schedule_def schedule_switch_thread_fastfail_def
  apply (wpsimp wp: hoare_drop_imps gts_wp)
  by (safe; (fastforce simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                             switch_in_cur_domain_def st_tcb_at_def obj_at_def)?)


\<comment> \<open>handle_interrupt\<close>

lemma set_endpoint_vcpus_of[wp]:
  "set_endpoint p ep \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding set_simple_ko_def
  by (wpsimp wp: set_object_wp get_object_wp)
     (fastforce simp: opt_map_def obj_at_def elim!: rsubst[where P=P])

lemma set_notification_vcpus_of[wp]:
  "set_notification p ntfn \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding set_simple_ko_def
  by (wpsimp wp: set_object_wp get_object_wp)
     (fastforce simp: opt_map_def obj_at_def elim!: rsubst[where P=P])

lemma thread_set_vcpus_of[wp]:
  "thread_set p t \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding thread_set_def
  by (wpsimp wp: set_object_wp)
     (fastforce simp: opt_map_def get_tcb_def split: option.splits elim!: rsubst[where P=P])

lemma set_bound_notification_vcpus_of[wp]:
  "set_bound_notification p ntfn \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding set_bound_notification_def
  by (wpsimp wp: set_object_wp)
     (fastforce simp: opt_map_def get_tcb_def split: option.splits elim!: rsubst[where P=P])

crunch store_word_offs
  for vcpus_of[wp]: "\<lambda>s. P (vcpus_of s)"

lemma set_mrs_vcpus_of[wp]:
  "set_mrs thread buf msgs \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding set_mrs_def zipWithM_x_mapM
  by (wpsimp wp: mapM_wp[where S=UNIV] set_object_wp)
     (fastforce simp: opt_map_def get_tcb_def split: option.splits elim!: rsubst[where P=P])

crunch set_extra_badge, handle_fault
  for vcpus_of[wp]: "\<lambda>s. P (vcpus_of s)"
  (wp: crunch_wps transfer_caps_loop_pres
   simp: crunch_simps
   ignore: set_simple_ko)

lemma vppi_event_vcpu_tcbs_of[wp]:
  "vppi_event irq \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
  unfolding vppi_event_def
  by (wpsimp)
     (fastforce simp: opt_map_def get_tcb_def split: option.splits elim!: rsubst[where P=P])

crunch handle_interrupt
  for vcpu_tcbs_of[wp]: "\<lambda>s. P (vcpu_tcbs_of s)"
  and cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift_strong dxo_wp_weak crunch_wps
   simp: crunch_simps
   ignore: set_simple_ko)


\<comment> \<open>handle_event\<close>

lemma retype_region_cur_vcpu_in_cur_domain[wp]:
  "retype_region ptr numObjects o_bits type dev \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
  unfolding retype_region_def
  apply (wpsimp simp_del: fun_upd_apply simp: foldr_fun_upd_value)
  by (auto simp: cur_vcpu_in_cur_domain_defs etcb_at'_def
                 default_object_def default_arch_object_def default_tcb_def default_arch_tcb_def
                 default_vcpu_def opt_map_def etcbs_of'_def
          split: option.splits apiobject_type.splits aobject_type.splits)

crunch do_machine_op, create_cap, init_arch_objects
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift crunch_wps simp: crunch_simps)

lemma delete_objects_cur_vcpu_in_cur_domain[wp]:
  "delete_objects ptr bits \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
  unfolding delete_objects_def
  apply wpsimp
   apply (rule hoare_strengthen_post, rule do_machine_op_cur_vcpu_in_cur_domain)
  by (auto simp: cur_vcpu_in_cur_domain_defs etcb_at'_def detype_def opt_map_def etcbs_of'_def
          split: option.splits)

crunch invoke_untyped
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: crunch_wps mapME_x_wp' preemption_point_inv' simp: crunch_simps mapM_x_def_bak) \<comment> \<open>FIXME: change invoke_untyped to use mapM_x\<close>

lemma set_vcpu_None_cur_vcpu_in_cur_domain[wp]:
  "set_vcpu vcpu_ptr (v\<lparr>vcpu_tcb := None\<rparr>) \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
  unfolding cur_vcpu_in_cur_domain_defs
  apply (wp_pre, wps, wpsimp)
  by (auto split: option.splits simp: opt_map_def)

crunch arch_thread_set, vcpu_disable
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift crunch_wps simp: crunch_simps)

lemma vcpu_invalidate_active_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<top>\<rbrace> vcpu_invalidate_active \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding vcpu_invalidate_active_def
  by wpsimp

lemma dissociate_vcpu_tcb_cur_vcpu_in_cur_domain[wp]:
  "dissociate_vcpu_tcb vcpu_ptr tcb_ptr \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
  unfolding dissociate_vcpu_tcb_def
  by (wpsimp wp: hoare_drop_imps)

crunch cap_move, suspend, delete_asid_pool, unmap_page, cancel_badged_sends
  for etcb_at[wp]: "etcb_at P t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps filterM_mapM)

crunch
  cap_insert, cap_move, cap_swap, set_thread_state, unbind_maybe_notification, unbind_notification,
  cancel_all_ipc, suspend, cancel_all_signals, delete_asid_pool, unmap_page, delete_asid,
  unmap_page_table, cancel_badged_sends, empty_slot, fpu_release
  for vcpu_tcbs_of[wp]: "\<lambda>s. P (vcpu_tcbs_of s)"
  and arm_current_vcpu[wp]: "\<lambda>s. P (arm_current_vcpu (arch_state s))"
  and cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift_strong crunch_wps dxo_wp_weak
   simp: crunch_simps filterM_mapM
   ignore: set_simple_ko tcb_sched_action)

crunch invoke_cnode
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: crunch_wps preemption_point_inv' cap_revoke_preservation dxo_wp_weak
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
  for vcpu_tcbs_of[wp]: "\<lambda>s. P (vcpu_tcbs_of s)"
  and arm_current_vcpu[wp]: "\<lambda>s. P (arm_current_vcpu (arch_state s))"
  and cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift_strong ignore: set_simple_ko)

lemma thread_set_no_etcb_change_cur_vcpu_in_cur_domain:
  assumes x: "\<And>P tcb. P (tcb_domain (f tcb)) = (P (tcb_domain tcb) :: bool)"
  shows      "thread_set f t' \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
  by (wpsimp wp: cur_vcpu_in_cur_domain_lift_strong thread_set_no_change_etcb_at simp: x)

lemma option_update_thread_no_etcb_change_cur_vcpu_in_cur_domain:
  assumes x: "\<And>P val tcb. P (tcb_domain (f val tcb)) = (P (tcb_domain tcb) :: bool)"
  shows      "option_update_thread t f opt \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
  unfolding option_update_thread_def
  by (wpsimp wp: cur_vcpu_in_cur_domain_lift_strong thread_set_no_change_etcb_at simp: x)

crunch invoke_tcb
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: crunch_wps check_cap_inv thread_set_no_etcb_change_cur_vcpu_in_cur_domain
       option_update_thread_no_etcb_change_cur_vcpu_in_cur_domain)

lemma set_vcpu_not_current_cur_vcpu_in_cur_domain:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> map_option fst (arm_current_vcpu (arch_state s)) \<noteq> Some vcpu_ptr\<rbrace>
   set_vcpu vcpu_ptr v
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding cur_vcpu_in_cur_domain_defs
  apply (wp_pre, wps, wpsimp)
  by (auto split: option.splits simp: opt_map_def)

lemma dissociate_vcpu_tcb_not_current_vcpu[wp]:
  "\<lbrace>\<top>\<rbrace> dissociate_vcpu_tcb vcpu_ptr tcb_ptr \<lbrace>\<lambda>_ s. map_option fst (arm_current_vcpu (arch_state s)) \<noteq> Some vcpu_ptr\<rbrace>"
  unfolding dissociate_vcpu_tcb_def
  by (wpsimp wp: get_vcpu_wp arch_thread_get_wp vcpu_invalid_active_arm_current_vcpu_None[THEN hoare_strengthen_post])

crunch dissociate_vcpu_tcb
  for vcpus_of_None[wp]: "\<lambda>s. vcpus_of s vcpu_ptr = None"
  (wp: hoare_vcg_imp_lift' get_vcpu_wp arch_thread_get_wp simp: if_option_eq)

crunch dissociate_vcpu_tcb
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps)

lemma vcpu_invalidate_active_cur_vcpu[wp]:
  "\<lbrace>\<top>\<rbrace> vcpu_invalidate_active \<lbrace>\<lambda>_ s. cur_vcpu_2 (arm_current_vcpu (arch_state s)) (P s)\<rbrace>"
  unfolding vcpu_invalidate_active_def cur_vcpu_def
  by wpsimp

lemma dissociate_vcpu_tcb_cur_vcpu[wp]:
  "dissociate_vcpu_tcb vcpu_ptr tcb_ptr \<lbrace>cur_vcpu\<rbrace>"
  unfolding dissociate_vcpu_tcb_def
  apply (wpsimp wp: hoare_vcg_imp_lift' get_vcpu_wp arch_thread_get_wp | wps)+
  apply (clarsimp simp: cur_vcpu_def in_omonad split: option.splits)
  done

lemma associate_vcpu_tcb_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>cur_vcpu_in_cur_domain and ct_in_cur_domain and cur_vcpu and (\<lambda>s. tcb_ptr \<noteq> idle_thread s)
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   associate_vcpu_tcb vcpu_ptr tcb_ptr
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>" (is "\<lbrace>?P\<rbrace> _ \<lbrace>_\<rbrace>")
  unfolding associate_vcpu_tcb_def
  apply wpsimp
        apply (solves \<open>(wpsimp wp: hoare_vcg_imp_lift' set_vcpu_not_current_cur_vcpu_in_cur_domain get_vcpu_wp
                        | wps
                        | clarsimp simp: in_omonad)+\<close>)+
    apply (rule_tac Q'="\<lambda>_. ?P" in hoare_post_imp)
     apply (fastforce simp: in_omonad ct_in_cur_domain_def cur_vcpu_def)
    apply (wpsimp | wps)+
  done

lemma invoke_vcpu_ack_vppi_vcpu_tcbs_of[wp]:
  "invoke_vcpu_ack_vppi vcpu_ptr vppi \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
  unfolding invoke_vcpu_ack_vppi_def
  apply wpsimp
  by (fastforce simp: opt_map_def elim!: rsubst[where P=P])

crunch invoke_vcpu_inject_irq, invoke_vcpu_write_register, invoke_vcpu_ack_vppi
  for vcpu_tcbs_of[wp]: "\<lambda>s. P (vcpu_tcbs_of s)"
  and arm_current_vcpu[wp]: "\<lambda>s. P (arm_current_vcpu (arch_state s))"
  and cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift_strong)

crunch invoke_vcpu_read_register
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain

lemma perform_vcpu_invocation_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>cur_vcpu_in_cur_domain and ct_in_cur_domain and cur_vcpu and valid_vcpu_invocation vi
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   perform_vcpu_invocation vi
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding perform_vcpu_invocation_def
  by (wpsimp simp: valid_vcpu_invocation_def)

crunch store_pte, store_asid_pool_entry
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift)

crunch
  perform_vspace_invocation, perform_page_table_invocation, perform_page_invocation,
  perform_asid_control_invocation, perform_asid_pool_invocation, perform_sgi_invocation,
  perform_smc_invocation
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: crunch_wps  simp: crunch_simps)

lemma arch_perform_invocation_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>cur_vcpu_in_cur_domain and ct_in_cur_domain and cur_vcpu and valid_arch_inv ai
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding arch_perform_invocation_def
  by (wpsimp simp: valid_arch_inv_def)

lemma thread_set_domain_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> sym_refs (state_hyp_refs_of s) \<and> valid_objs s
        \<and> (arm_current_vcpu (arch_state s) = None
           \<or> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb \<noteq> map_option fst (arm_current_vcpu (arch_state s))) tptr s
           \<or> cur_domain s = new_dom)\<rbrace>
   thread_set_domain tptr new_dom
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  by (auto simp: cur_vcpu_in_cur_domain_defs pred_tcb_at_def obj_at_def etcb_at_def etcbs_of'_def
          split: option.splits dest: bound_vcpu_bound_tcb_at)

lemma set_domain_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> sym_refs (state_hyp_refs_of s) \<and> valid_objs s
        \<and> (arm_current_vcpu (arch_state s) = None
           \<or> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb \<noteq> map_option fst (arm_current_vcpu (arch_state s))) tptr s
           \<or> cur_domain s = new_dom)\<rbrace>
   set_domain tptr new_dom
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding set_domain_def
  by (wpsimp wp: thread_set_domain_cur_vcpu_in_cur_domain hoare_vcg_disj_lift | wps)+

crunch fpu_release
  for arch_tcb_vcpu_at[wp]: "\<lambda>s. (arch_tcb_at (\<lambda>itcb. P (itcb_vcpu itcb)) t s)"
  (simp: crunch_simps wp: crunch_wps)

lemma vcpu_flush_if_current_make_vcpu_safe[wp]:
  "\<lbrace>\<top>\<rbrace>
   vcpu_flush_if_current tptr
   \<lbrace>\<lambda>_ s. arm_current_vcpu (arch_state s) = None
          \<or> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb \<noteq> map_option fst (arm_current_vcpu (arch_state s))) tptr s\<rbrace>"
  unfolding vcpu_flush_if_current_def
  apply (wpsimp wp: vcpu_flush_arm_current_vcpu_None[THEN hoare_strengthen_post] arch_thread_get_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma arch_prepare_set_domain_make_vcpu_safe[wp]:
  "\<lbrace>\<top>\<rbrace>
   arch_prepare_set_domain tptr new_dom
   \<lbrace>\<lambda>_ s. arm_current_vcpu (arch_state s) = None
          \<or> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb \<noteq> map_option fst (arm_current_vcpu (arch_state s))) tptr s
          \<or> cur_domain s = new_dom\<rbrace>"
  unfolding arch_prepare_set_domain_def
  by (wpsimp wp: hoare_vcg_disj_lift[where f="fpu_release tptr"]
                 vcpu_flush_if_current_make_vcpu_safe[THEN hoare_strengthen_post]
      | wps)+

lemma vcpu_flush_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<top>\<rbrace> vcpu_flush \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding vcpu_flush_def
  by (wpsimp simp: cur_vcpu_in_cur_domain_defs)

crunch arch_prepare_set_domain
  for hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  and valid_objs[wp]: valid_objs
  and cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: crunch_wps simp: crunch_simps)

lemma invoke_domain_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> sym_refs (state_hyp_refs_of s) \<and> valid_objs s\<rbrace>
   invoke_domain thread domain
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding invoke_domain_def
  by wpsimp

crunch do_reply_transfer, handle_recv, handle_vm_fault
  for etcb_at[wp]: "etcb_at P t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps preemption_point_inv' simp: crunch_simps filterM_mapM)

crunch do_reply_transfer, handle_recv, handle_vm_fault
  for vcpu_tcbs_of[wp]: "\<lambda>s. P (vcpu_tcbs_of s)"
  and arm_current_vcpu[wp]: "\<lambda>s. P (arm_current_vcpu (arch_state s))"
  and cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift_strong crunch_wps dxo_wp_weak
   simp: crunch_simps
   ignore: set_simple_ko)

crunch
  handle_fault, reply_from_kernel, send_ipc, send_signal, invoke_irq_control, invoke_irq_handler,
  reschedule_required, handle_hypervisor_fault
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift_strong dxo_wp_weak crunch_wps
   simp: crunch_simps)

lemma perform_invocation_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>cur_vcpu_in_cur_domain and ct_in_cur_domain and cur_vcpu and valid_invocation iv
    and valid_objs and (\<lambda>s. sym_refs (state_hyp_refs_of s))
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   perform_invocation blocking call iv
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  by (case_tac iv, simp_all; (solves wpsimp)?)

lemma set_thread_state_runnable_scheduler_action:
  "\<lbrace>\<lambda>s. P (scheduler_action s) \<and> runnable ts\<rbrace> set_thread_state t ts \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_act_def set_object_def get_object_def set_scheduler_action_def)
  apply (wpsimp wp: gts_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemma handle_invocation_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>cur_vcpu_in_cur_domain and invs and ct_in_cur_domain and ct_active
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   handle_invocation calling blocking
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding handle_invocation_def
  apply (wpsimp wp: syscall_valid)
          apply (wp gts_wp hoare_vcg_all_lift hoare_drop_imps cur_vcpu_typ_lift
                    set_thread_state_runnable_scheduler_action
                | simp add: split_def)+
  apply (fastforce simp: invs_def valid_state_def valid_arch_state_def valid_pspace_def
                         valid_tcb_state_def ct_in_state_def
                  elim!: pred_tcb_weakenE)
  done

crunch maybe_handle_interrupt
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain

lemma handle_event_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>cur_vcpu_in_cur_domain and invs and ct_in_cur_domain and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   handle_event e
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  apply (cases e; clarsimp; (solves wpsimp)?)
  unfolding handle_call_def handle_send_def handle_reply_def handle_yield_def
  by (wpsimp wp: get_cap_wp)+

crunch activate_thread
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain

lemma call_kernel_cur_vcpu_in_cur_domain:
  "\<lbrace>cur_vcpu_in_cur_domain and invs and valid_sched and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   call_kernel e
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding call_kernel_def maybe_handle_interrupt_def
  apply (wpsimp wp: handle_spurious_irq_invs| strengthen invs_valid_objs invs_hyp_sym_refs)+
    (* simplify postcondition by ruling out non_kernel_IRQs *)
    apply (rule hoare_post_imp[where Q'="\<lambda>irq s. irq \<notin> Some ` non_kernel_IRQs \<and> cur_vcpu_in_cur_domain s \<and> valid_sched s \<and> invs s"])
     apply fastforce
    apply (wpsimp wp: getActiveIRQ_neq_non_kernel handle_event_valid_sched
           | strengthen invs_valid_objs invs_hyp_sym_refs)+
  apply (clarsimp simp: valid_sched_def)
  done

end

end
