(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory DetSchedDomainTime_AI
imports "$L4V_ARCH/ArchDetSchedAux_AI"
begin

text {*
  This theory deals with the preservation of domain_list validity over kernel invocations,
  as well as ensuring preserving that the domain time is never zero at kernel exit.
*}

(* Note: domains in the domain list should also be \<le> maxDomain, but this is not needed right now *)
definition
  "valid_domain_list_2 dlist \<equiv> 0 < length dlist \<and> (\<forall>(d,time) \<in> set dlist. 0 < time)"

abbreviation
  valid_domain_list :: "det_ext state \<Rightarrow> bool"
where
  "valid_domain_list \<equiv> (\<lambda>s. valid_domain_list_2 (domain_list s))"

lemmas valid_domain_list_def = valid_domain_list_2_def


section {* Preservation of domain list validity *}

lemma ethread_get_wp[wp]:
  "\<lbrace>\<lambda>s. etcb_at (\<lambda>t. P (f t) s) ptr s\<rbrace> ethread_get f ptr \<lbrace>P\<rbrace>"
  unfolding ethread_get_def
  by (wp | clarsimp simp add: get_etcb_def etcb_at'_def is_etcb_at'_def)+

crunch domain_list_inv[wp]:
  cap_swap_for_delete, empty_slot, get_object, get_cap, tcb_sched_action
  "\<lambda>s. P (domain_list s)"

context begin interpretation Arch . (*FIXME: arch_split*)

crunch domain_list_inv[wp]: finalise_cap "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps hoare_drop_imps hoare_unless_wp select_inv mapM_wp
       subset_refl if_fun_split simp: crunch_simps ignore: tcb_sched_action)

lemma rec_del_domain_list[wp]:
  "\<lbrace>\<lambda>s. P (domain_list s)\<rbrace> rec_del call \<lbrace>\<lambda>rv s. P (domain_list s)\<rbrace>"
  by (wp rec_del_preservation preemption_point_inv' | simp)+

crunch domain_list_inv[wp]: cap_delete, activate_thread "\<lambda>s. P (domain_list s)"

crunch domain_list_inv[wp]: schedule "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imp simp: Let_def)

end

crunch domain_list_inv[wp]: handle_interrupt "\<lambda>s. P (domain_list s)"

crunch domain_list_inv[wp]:
  lookup_cap_and_slot, cap_insert, set_extra_badge "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps)

crunch domain_list_inv[wp]: do_ipc_transfer "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps transfer_caps_loop_pres simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch domain_list_inv[wp]: copy_mrs "\<lambda>s. P (domain_list s)"

crunch domain_list_inv[wp]: handle_fault "\<lambda>s. P (domain_list s)"
  (wp: mapM_wp hoare_drop_imps simp: crunch_simps ignore:copy_mrs)

crunch domain_list_inv[wp]:
  reply_from_kernel, create_cap, retype_region, do_reply_transfer
  "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps)

crunch domain_list_inv[wp]: delete_objects "\<lambda>s :: det_ext state. P (domain_list s)"
  (wp: crunch_wps
   simp: detype_def detype_ext_def wrap_ext_det_ext_ext_def cap_insert_ext_def
   ignore: freeMemory)

crunch domain_list_inv[wp]: update_work_units "\<lambda>s. P (domain_list s)"

crunch domain_list_inv[wp]: preemption_point "\<lambda>s. P (domain_list s)"
  (wp: select_inv OR_choiceE_weak_wp ignore: OR_choiceE)

crunch domain_list_inv[wp]: reset_untyped_cap "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps hoare_unless_wp mapME_x_inv_wp select_inv
   simp: crunch_simps)

context begin interpretation Arch . (*FIXME: arch_split*)

crunch domain_list_inv[wp]: invoke_untyped "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps
    simp: crunch_simps mapM_x_defsym)

crunch domain_list_inv[wp]:
  invoke_tcb, invoke_domain, invoke_irq_control, invoke_irq_handler
  "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps check_cap_inv)

crunch domain_list_inv[wp]: arch_perform_invocation "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps check_cap_inv)

end

crunch domain_list_inv[wp]: cap_move "\<lambda>s. P (domain_list s)"

lemma cap_revoke_domain_list_inv[wp]:
  "\<lbrace>(\<lambda>s :: det_ext state. P (domain_list s))\<rbrace> cap_revoke a \<lbrace>\<lambda>rv s. P (domain_list s)\<rbrace>"
  by (rule cap_revoke_preservation2)
     (wp preemption_point_inv'|simp)+

crunch domain_list_inv[wp]: cancel_badged_sends "\<lambda>s. P (domain_list s)"
  (ignore: filterM clearMemory
     simp: filterM_mapM crunch_simps
       wp: crunch_wps)

lemma invoke_cnode_domain_list_inv[wp]:
  "\<lbrace>\<lambda>s :: det_ext state. P (domain_list s)\<rbrace>
     invoke_cnode i
   \<lbrace>\<lambda>rv s. P (domain_list s) \<rbrace>"
  apply (rule hoare_pre)
   apply (wp crunch_wps cap_move_src_slot_Null hoare_drop_imps hoare_vcg_all_lift
          | wpc | simp add: invoke_cnode_def crunch_simps split del: split_if)+
  done

crunch domain_list_inv[wp]: perform_invocation, handle_invocation "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps syscall_valid simp: crunch_simps ignore: without_preemption)

context begin interpretation Arch . (*FIXME: arch_split*)

crunch domain_list_inv[wp]:
  handle_recv, handle_yield, handle_call, handle_reply, handle_vm_fault
    "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps simp: crunch_simps)

end

lemma handle_event_domain_list_inv[wp]:
  "\<lbrace>\<lambda>s. P (domain_list s) \<rbrace>
   handle_event e
   \<lbrace>\<lambda>_ s. P (domain_list s) \<rbrace>"
  apply (cases e, simp_all)
      apply (rename_tac syscall)
      apply (case_tac syscall, simp_all add: handle_send_def)
             apply (wp|simp|wpc)+
  done

(* no one modifies domain_list - supplied at compile time *)
lemma call_kernel_domain_list_inv_det_ext:
  "\<lbrace> \<lambda>s. P (domain_list s) \<rbrace>
     (call_kernel e) :: (unit,det_ext) s_monad
   \<lbrace>\<lambda>_ s. P (domain_list s) \<rbrace>"
  unfolding call_kernel_def
  apply (wp)
   apply (simp add: schedule_def)
   apply (wp without_preemption_wp|wpc|simp add: if_apply_def2)+
  done


section {* Preservation of domain time remaining *}

crunch domain_time_inv[wp]: do_user_op "(\<lambda>s. P (domain_time s))"
  (wp: select_wp)

context begin interpretation Arch . (*FIXME: arch_split*)

crunch domain_time_inv[wp]:
  get_cap, activate_thread, set_scheduler_action, tcb_sched_action
  "\<lambda>s. P (domain_time s)"

crunch domain_time_inv[wp]: guarded_switch_to "\<lambda>s. P (domain_time s)"
  (wp: hoare_drop_imp whenE_inv)

crunch domain_time_inv[wp]: choose_thread "\<lambda>s. P (domain_time s)"

end

crunch domain_time_inv[wp]: send_signal "\<lambda>s. P (domain_time s)"
  (wp: hoare_drop_imps mapM_x_wp_inv select_wp simp: crunch_simps unless_def)

crunch domain_time_inv[wp]:
  cap_swap_for_delete, empty_slot, get_object, get_cap, tcb_sched_action
  "\<lambda>s. P (domain_time s)"

context begin interpretation Arch . (*FIXME: arch_split*)

crunch domain_time_inv[wp]: finalise_cap "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps hoare_drop_imps hoare_unless_wp select_inv mapM_wp
       subset_refl if_fun_split simp: crunch_simps ignore: tcb_sched_action)

end

lemma rec_del_domain_time[wp]:
  "\<lbrace>\<lambda>s. P (domain_time s)\<rbrace> rec_del call \<lbrace>\<lambda>rv s. P (domain_time s)\<rbrace>"
  by (wp rec_del_preservation preemption_point_inv' | simp)+

crunch domain_time_inv[wp]:
  cap_delete, activate_thread, lookup_cap_and_slot
  "\<lambda>s. P (domain_time s)"

crunch domain_time_inv[wp]: cap_insert "\<lambda>s. P (domain_time s)"
  (wp: hoare_drop_imps)

crunch domain_time_inv[wp]: set_extra_badge "\<lambda>s. P (domain_time s)"

crunch domain_time_inv[wp]: do_ipc_transfer "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps transfer_caps_loop_pres simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch domain_time_inv[wp]: copy_mrs "\<lambda>s. P (domain_time s)"

crunch domain_time_inv[wp]: handle_fault "\<lambda>s. P (domain_time s)"
  (wp: mapM_wp hoare_drop_imps simp: crunch_simps ignore:copy_mrs) 

crunch domain_time_inv[wp]:
  reply_from_kernel, create_cap, retype_region
  "\<lambda>s. P (domain_time s)"

crunch domain_time_inv[wp]: do_reply_transfer "\<lambda>s. P (domain_time s)"
  (wp: hoare_drop_imps)

crunch domain_time_inv[wp]: delete_objects "\<lambda>s :: det_ext state. P (domain_time s)"
  (wp: crunch_wps
   simp: detype_def detype_ext_def wrap_ext_det_ext_ext_def cap_insert_ext_def
   ignore: freeMemory)

crunch domain_time_inv[wp]: update_work_units "\<lambda>s. P (domain_time s)"

crunch domain_time_inv[wp]: preemption_point "\<lambda>s. P (domain_time s)"
  (wp: select_inv OR_choiceE_weak_wp ignore: OR_choiceE)

crunch domain_time_inv[wp]: reset_untyped_cap "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps hoare_unless_wp mapME_x_inv_wp select_inv
   simp: crunch_simps)

context begin interpretation Arch . (*FIXME: arch_split*)

crunch domain_time_inv[wp]: invoke_untyped "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps
    simp: crunch_simps mapM_x_defsym)

crunch domain_time_inv[wp]:
  invoke_tcb, invoke_domain, invoke_irq_control,invoke_irq_handler
  "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps check_cap_inv)

crunch domain_time_inv[wp]: arch_perform_invocation "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps check_cap_inv)

end

crunch domain_time_inv[wp]: cap_move "\<lambda>s. P (domain_time s)"

lemma cap_revoke_domain_time_inv[wp]:
  "\<lbrace>(\<lambda>s :: det_ext state. P (domain_time s))\<rbrace> cap_revoke a \<lbrace>\<lambda>rv s. P (domain_time s)\<rbrace>"
  apply (rule cap_revoke_preservation2)
  apply (wp preemption_point_inv'|simp)+
  done

crunch domain_time_inv[wp]: cancel_badged_sends "\<lambda>s. P (domain_time s)"
  (ignore: filterM clearMemory 
     simp: filterM_mapM crunch_simps
       wp: crunch_wps)
  

lemma invoke_cnode_domain_time_inv[wp]:
  "\<lbrace>\<lambda>s :: det_ext state. P (domain_time s)\<rbrace>
     invoke_cnode i
   \<lbrace>\<lambda>rv s. P (domain_time s) \<rbrace>"
  apply (rule hoare_pre)
   apply (wp crunch_wps cap_move_src_slot_Null hoare_drop_imps hoare_vcg_all_lift
          | wpc | simp add: invoke_cnode_def crunch_simps split del: split_if)+
  done

crunch domain_time_inv[wp]: perform_invocation, handle_invocation "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps syscall_valid simp: crunch_simps ignore: without_preemption)

context begin interpretation Arch . (*FIXME: arch_split*)

crunch domain_time_inv[wp]:
  handle_recv, handle_yield, handle_call, handle_reply, handle_vm_fault
    "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps simp: crunch_simps)

end

lemma handle_event_domain_time_inv:
  "\<lbrace>\<lambda>s. P (domain_time s) \<and> e \<noteq> Interrupt \<rbrace>
   handle_event e
   \<lbrace>\<lambda>_ s. P (domain_time s) \<rbrace>"
  apply (cases e, simp_all)
      apply (rename_tac syscall)
      apply (case_tac syscall, simp_all add: handle_send_def)
             apply (wp|simp|wpc)+
  done

crunch domain_time_inv[wp]: send_fault_ipc, handle_call "\<lambda>s. P (domain_time s)"
  (wp: hoare_drop_imps mapM_x_wp_inv select_wp without_preemption_wp simp: crunch_simps unless_def)

lemma next_domain_domain_time_left[wp]:
  "\<lbrace> valid_domain_list \<rbrace> next_domain \<lbrace>\<lambda>_ s. 0 < domain_time s \<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: next_domain_def Let_def)
    apply wp
   apply (clarsimp simp: valid_domain_list_def)
   apply (simp add: all_set_conv_all_nth)
   apply (erule_tac x="Suc (domain_index s) mod length (domain_list s)" in allE)
   apply clarsimp
   done

lemma schedule_domain_time_left:
  "\<lbrace>valid_domain_list and (\<lambda>s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread) \<rbrace>
   schedule
   \<lbrace>\<lambda>_ s. 0 < domain_time s \<rbrace>" (is "\<lbrace>?P\<rbrace> _ \<lbrace>_\<rbrace>")
  supply word_neq_0_conv[simp]
  apply (simp add: schedule_def)
  apply (wp|wpc)+
     apply (rule_tac Q="\<lambda>_. valid_domain_list" in hoare_post_imp, fastforce)
     apply wp
   apply (rule_tac Q="\<lambda>_. ?P" in hoare_post_imp, fastforce)
   apply wp
  done

lemma reschedule_required_valid_domain_time:
  "\<lbrace> \<top> \<rbrace> reschedule_required
   \<lbrace>\<lambda>x s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding reschedule_required_def set_scheduler_action_def
  by (wp hoare_vcg_imp_lift | simp | wpc)+

(* FIXME: move to where hoare_drop_imp is, add E/R variants etc *)
lemma hoare_false_imp:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. \<not> R r s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. R r s \<longrightarrow> Q r s\<rbrace>"
  by (auto simp: valid_def)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma handle_interrupt_valid_domain_time:
  "\<lbrace>\<lambda>s :: det_ext state. 0 < domain_time s \<rbrace> handle_interrupt i
   \<lbrace>\<lambda>rv s.  domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread \<rbrace>"
   apply (unfold handle_interrupt_def)
   apply (case_tac "maxIRQ < i"; simp)
    subgoal by (wp hoare_false_imp, simp)
   apply (rule hoare_pre)
    apply (wp do_machine_op_exst | simp | wpc)+
       apply (rule_tac Q="\<lambda>_ s. 0 < domain_time s" in hoare_post_imp, fastforce)
       apply wp
      apply (rule_tac Q="\<lambda>_ s. 0 < domain_time s" in hoare_post_imp, fastforce)
      apply wp
     apply simp (* dxo_eq *)
     apply (clarsimp simp: timer_tick_def num_domains_def)
     apply (wp reschedule_required_valid_domain_time | simp | wp_once hoare_drop_imp)+
   done

end

lemma call_kernel_domain_time_inv_det_ext:
  "\<lbrace> (\<lambda>s. 0 < domain_time s) and valid_domain_list and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) \<rbrace>
   (call_kernel e) :: (unit,det_ext) s_monad
   \<lbrace>\<lambda>_ s. 0 < domain_time s \<rbrace>"
  unfolding call_kernel_def
  apply (case_tac "e = Interrupt")
   apply simp
   apply (rule hoare_pre)
   apply ((wp schedule_domain_time_left handle_interrupt_valid_domain_time
           | wpc | simp)+)[1]
   apply (rule_tac Q="\<lambda>_ s. 0 < domain_time s \<and> valid_domain_list s" in hoare_strengthen_post)
    apply wp
   apply fastforce+
  (* now non-interrupt case; may throw but does not touch domain_time in handle_event *)
  apply (rule hoare_pre)
   apply (wp schedule_domain_time_left without_preemption_wp handle_interrupt_valid_domain_time)
    apply (rule_tac Q="\<lambda>_ s. 0 < domain_time s \<and> valid_domain_list s" in hoare_post_imp)
     apply fastforce
    apply (wp handle_event_domain_time_inv)
   apply (rule_tac Q'="\<lambda>_ s. 0 < domain_time s" in hoare_post_imp_R)
    apply (wp handle_event_domain_time_inv)
   apply fastforce+
  done

end
