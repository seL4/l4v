(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDetSchedAux_AI
imports DetSchedAux_AI
begin

context Arch begin arch_global_naming

named_theorems DetSchedAux_AI_assms

crunch init_arch_objects
  for exst[wp]: "\<lambda>s. P (exst s)"
  and valid_queues[wp]: valid_queues
  and valid_sched_action[wp]: valid_sched_action
  and valid_sched[wp]: valid_sched
  and etcbs_of[wp, DetSchedAux_AI_assms]: "\<lambda>s. P (etcbs_of s)"
  and ready_queues[wp, DetSchedAux_AI_assms]: "\<lambda>s. P (ready_queues s)"
  and idle_thread[wp, DetSchedAux_AI_assms]: "\<lambda>s. P (idle_thread s)"
  and schedact[wp, DetSchedAux_AI_assms]: "\<lambda>s. P (scheduler_action s)"
  and cur_domain[wp, DetSchedAux_AI_assms]: "\<lambda>s. P (cur_domain s)"
  (wp: mapM_x_wp')

lemma tcb_sched_action_valid_idle_etcb:
  "tcb_sched_action foo thread \<lbrace>valid_idle_etcb\<rbrace>"
  by (rule valid_idle_etcb_lift)
     (wpsimp simp: tcb_sched_action_def set_tcb_queue_def)

crunch init_arch_objects
  for valid_blocked[wp, DetSchedAux_AI_assms]: valid_blocked
  (wp: valid_blocked_lift crunch_wps)

lemma perform_asid_control_etcb_at:
  "\<lbrace>etcb_at P t\<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>r s. st_tcb_at (Not \<circ> inactive) t s \<longrightarrow> etcb_at P t s\<rbrace>"
  apply (simp add: perform_asid_control_invocation_def)
  apply wpsimp
       apply (wp hoare_imp_lift_something typ_at_pred_tcb_at_lift)[1]
      apply (rule hoare_drop_imps)
      apply (wp retype_region_etcb_at)+
  apply simp
  done

crunch perform_asid_control_invocation
  for idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and valid_blocked[wp]: valid_blocked
  and schedact[wp]: "\<lambda>s. P (scheduler_action s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: hoare_weak_lift_imp simp: detype_def)

lemma perform_asid_control_invocation_valid_sched:
  "\<lbrace>ct_active and invs and valid_aci aci and valid_sched and valid_idle\<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (rule hoare_pre)
   apply (rule_tac I="invs and ct_active and valid_aci aci" in valid_sched_tcb_state_preservation)
          apply (wp perform_asid_control_invocation_st_tcb_at)
          apply simp
         apply (wp perform_asid_control_etcb_at)+
    apply (rule hoare_strengthen_post, rule aci_invs)
    apply (simp add: invs_def valid_state_def)
   apply (rule hoare_lift_Pf[where f="\<lambda>s. scheduler_action s"])
    apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_domain s"])
     apply (rule hoare_lift_Pf[where f="\<lambda>s. idle_thread s"])
      apply wp+
  apply simp
  done

end

global_interpretation DetSchedAux_AI?: DetSchedAux_AI
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedAux_AI_assms)?)
qed

end
