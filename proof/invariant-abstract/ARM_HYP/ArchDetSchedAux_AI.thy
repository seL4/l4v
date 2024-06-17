(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDetSchedAux_AI
imports DetSchedAux_AI
begin

context Arch begin global_naming ARM_HYP

named_theorems DetSchedAux_AI_assms

crunch init_arch_objects
  for exst[wp]: "\<lambda>s. P (exst s)"
  and ct[wp]: "\<lambda>s. P (cur_thread s)"
  and valid_etcbs[wp, DetSchedAux_AI_assms]: valid_etcbs
  (wp: crunch_wps unless_wp)

crunch invoke_untyped
  for ct[wp, DetSchedAux_AI_assms]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps dxo_wp_weak preemption_point_inv mapME_x_inv_wp
   simp: crunch_simps do_machine_op_def detype_def mapM_x_defsym unless_def
   ignore: freeMemory retype_region_ext)
crunch invoke_untyped
  for ready_queues[wp, DetSchedAux_AI_assms]: "\<lambda>s. P (ready_queues s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv'
   simp: detype_def detype_ext_def crunch_simps
         wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: freeMemory)
crunch invoke_untyped
  for scheduler_action[wp, DetSchedAux_AI_assms]: "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv'
   simp: detype_def detype_ext_def crunch_simps
         wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: freeMemory)
crunch invoke_untyped
  for cur_domain[wp, DetSchedAux_AI_assms]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv'
   simp: detype_def detype_ext_def crunch_simps
         wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: freeMemory)
crunch invoke_untyped
  for idle_thread[wp, DetSchedAux_AI_assms]: "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv dxo_wp_weak
   simp: detype_def detype_ext_def crunch_simps
         wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: freeMemory retype_region_ext)

lemma tcb_sched_action_valid_idle_etcb:
  "\<lbrace>valid_idle_etcb\<rbrace>
     tcb_sched_action foo thread
   \<lbrace>\<lambda>_. valid_idle_etcb\<rbrace>"
  apply (rule valid_idle_etcb_lift)
  apply (simp add: tcb_sched_action_def set_tcb_queue_def)
  apply (wp | simp)+
  done

lemma delete_objects_etcb_at[wp, DetSchedAux_AI_assms]:
  "\<lbrace>\<lambda>s::det_ext state. etcb_at P t s\<rbrace> delete_objects a b \<lbrace>\<lambda>r s. etcb_at P t s\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (wp)
  apply (simp add: detype_def detype_ext_def wrap_ext_det_ext_ext_def etcb_at_def|wp)+
  done

crunch reset_untyped_cap
  for etcb_at[wp]: "etcb_at P t"
  (wp: preemption_point_inv' mapME_x_inv_wp crunch_wps
    simp: unless_def)

crunch reset_untyped_cap
  for valid_etcbs[wp]: "valid_etcbs"
  (wp: preemption_point_inv' mapME_x_inv_wp crunch_wps
    simp: unless_def)

lemma invoke_untyped_etcb_at [DetSchedAux_AI_assms]:
  "\<lbrace>(\<lambda>s :: det_ext state. etcb_at P t s) and valid_etcbs\<rbrace> invoke_untyped ui \<lbrace>\<lambda>r s. st_tcb_at (Not o inactive) t s \<longrightarrow> etcb_at P t s\<rbrace>"
  apply (cases ui)
  apply (simp add: mapM_x_def[symmetric] invoke_untyped_def whenE_def
           split del: if_split)
  apply (rule hoare_pre)
   apply (wp retype_region_etcb_at mapM_x_wp'
             create_cap_no_pred_tcb_at typ_at_pred_tcb_at_lift
             hoare_convert_imp[OF create_cap_no_pred_tcb_at]
             hoare_convert_imp[OF _ init_arch_objects_exst]
      | simp
      | (wp (once) hoare_drop_impE_E))+
  done


crunch init_arch_objects
  for valid_blocked[wp, DetSchedAux_AI_assms]: valid_blocked
  (wp: valid_blocked_lift set_cap_typ_at)

lemma perform_asid_control_etcb_at:"\<lbrace>(\<lambda>s. etcb_at P t s) and valid_etcbs\<rbrace>
          perform_asid_control_invocation aci
          \<lbrace>\<lambda>r s. st_tcb_at (Not \<circ> inactive) t s \<longrightarrow> etcb_at P t s\<rbrace>"
  apply (simp add: perform_asid_control_invocation_def)
  apply (rule hoare_pre)
   apply ( wp | wpc | simp)+
       apply (wp hoare_imp_lift_something typ_at_pred_tcb_at_lift)[1]
      apply (rule hoare_drop_imps)
      apply (wp retype_region_etcb_at)+
  apply simp
  done

crunch perform_asid_control_invocation
  for ct[wp]: "\<lambda>s. P (cur_thread s)"

crunch perform_asid_control_invocation
  for idle_thread[wp]: "\<lambda>s. P (idle_thread s)"

crunch perform_asid_control_invocation
  for valid_etcbs[wp]: valid_etcbs (wp: hoare_weak_lift_imp)

crunch perform_asid_control_invocation
  for valid_blocked[wp]: valid_blocked (wp: hoare_weak_lift_imp)

crunch perform_asid_control_invocation
  for schedact[wp]: "\<lambda>s :: det_ext state. P (scheduler_action s)" (wp: crunch_wps simp: detype_def detype_ext_def wrap_ext_det_ext_ext_def cap_insert_ext_def ignore: freeMemory)

crunch perform_asid_control_invocation
  for rqueues[wp]: "\<lambda>s :: det_ext state. P (ready_queues s)" (wp: crunch_wps simp: detype_def detype_ext_def wrap_ext_det_ext_ext_def cap_insert_ext_def ignore: freeMemory)

crunch perform_asid_control_invocation
  for cur_domain[wp]: "\<lambda>s :: det_ext state. P (cur_domain s)" (wp: crunch_wps simp: detype_def detype_ext_def wrap_ext_det_ext_ext_def cap_insert_ext_def ignore: freeMemory)

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

crunch init_arch_objects
  for valid_queues[wp]: valid_queues (wp: valid_queues_lift)

crunch init_arch_objects
  for valid_sched_action[wp]: valid_sched_action (wp: valid_sched_action_lift)

crunch init_arch_objects
  for valid_sched[wp]: valid_sched (wp: valid_sched_lift)

end

lemmas tcb_sched_action_valid_idle_etcb
    = ARM_HYP.tcb_sched_action_valid_idle_etcb

global_interpretation DetSchedAux_AI_det_ext?: DetSchedAux_AI_det_ext
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedAux_AI_assms | wp)?)
  qed

global_interpretation DetSchedAux_AI?: DetSchedAux_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedAux_AI_assms | wp)?)
  qed

end
