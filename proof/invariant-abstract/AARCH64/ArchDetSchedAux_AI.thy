(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDetSchedAux_AI
imports DetSchedAux_AI
begin

context Arch begin global_naming AARCH64

named_theorems DetSchedAux_AI_assms

crunch init_arch_objects
  for exst[wp]: "\<lambda>s. P (exst s)"
  and valid_etcbs[wp, DetSchedAux_AI_assms]: valid_etcbs
  and valid_queues[wp]: valid_queues
  and valid_sched_action[wp]: valid_sched_action
  and valid_sched[wp]: valid_sched

(* already proved earlier *)
declare invoke_untyped_cur_thread[DetSchedAux_AI_assms]

crunch invoke_untyped
  for ready_queues[wp, DetSchedAux_AI_assms]: "\<lambda>s. P (ready_queues s)"
  and scheduler_action[wp, DetSchedAux_AI_assms]: "\<lambda>s. P (scheduler_action s)"
  and cur_domain[wp, DetSchedAux_AI_assms]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv'
   simp: detype_def detype_ext_def crunch_simps wrap_ext_det_ext_ext_def mapM_x_defsym)

crunch invoke_untyped
  for idle_thread[wp, DetSchedAux_AI_assms]: "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv dxo_wp_weak
   simp: detype_def detype_ext_def crunch_simps wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: retype_region_ext)

lemma tcb_sched_action_valid_idle_etcb:
  "tcb_sched_action foo thread \<lbrace>valid_idle_etcb\<rbrace>"
  by (rule valid_idle_etcb_lift)
     (wpsimp simp: tcb_sched_action_def set_tcb_queue_def)

crunch do_machine_op
  for ekheap[wp]: "\<lambda>s. P (ekheap s)"

lemma delete_objects_etcb_at[wp, DetSchedAux_AI_assms]:
  "delete_objects a b \<lbrace>etcb_at P t\<rbrace>"
  unfolding delete_objects_def detype_def detype_ext_def
  by (wpsimp simp: wrap_ext_det_ext_ext_def etcb_at_def)

crunch reset_untyped_cap
  for etcb_at[wp]: "etcb_at P t"
  and valid_etcbs[wp]: "valid_etcbs"
  (wp: preemption_point_inv' mapME_x_inv_wp crunch_wps
    simp: unless_def)

lemma invoke_untyped_etcb_at [DetSchedAux_AI_assms]:
  "\<lbrace>etcb_at P t and valid_etcbs\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>r s. st_tcb_at (Not o inactive) t s \<longrightarrow> etcb_at P t s\<rbrace>"
  apply (cases ui)
  apply (simp add: mapM_x_def[symmetric] invoke_untyped_def)
  apply (wpsimp wp: retype_region_etcb_at mapM_x_wp'
                    create_cap_no_pred_tcb_at typ_at_pred_tcb_at_lift
                    hoare_convert_imp[OF create_cap_no_pred_tcb_at]
                    hoare_convert_imp[OF _ init_arch_objects_exst]
                    hoare_drop_impE_E)
  done


crunch init_arch_objects
  for valid_blocked[wp, DetSchedAux_AI_assms]: valid_blocked
  (wp: valid_blocked_lift set_cap_typ_at)

lemma perform_asid_control_etcb_at:
  "\<lbrace>etcb_at P t and valid_etcbs\<rbrace>
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
  and valid_etcbs[wp]: valid_etcbs
  and valid_blocked[wp]: valid_blocked
  and schedact[wp]: "\<lambda>s. P (scheduler_action s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: hoare_weak_lift_imp)

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

lemmas tcb_sched_action_valid_idle_etcb
    = AARCH64.tcb_sched_action_valid_idle_etcb

global_interpretation DetSchedAux_AI_det_ext?: DetSchedAux_AI_det_ext
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedAux_AI_assms)?)
qed

global_interpretation DetSchedAux_AI?: DetSchedAux_AI
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedAux_AI_assms)?)
qed

end
