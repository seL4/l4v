(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchDetSchedAux_AI
imports "../DetSchedAux_AI"
begin

context Arch begin global_naming ARM

named_theorems DetSchedAux_AI_assms

crunches init_arch_objects
  for exst[wp]: "\<lambda>s. P (exst s)"
  and ct[wp]: "\<lambda>s. P (cur_thread s)"
  and st_tcb_at[wp]: "st_tcb_at Q t"
  and valid_etcbs[wp, DetSchedAux_AI_assms]: valid_etcbs
  (wp: crunch_wps hoare_unless_wp valid_etcbs_lift)

crunch ct[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps dxo_wp_weak preemption_point_inv mapME_x_inv_wp
   simp: crunch_simps do_machine_op_def detype_def mapM_x_defsym unless_def
   ignore: freeMemory retype_region_ext)
crunch ready_queues[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s. P (ready_queues s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv'
   simp: detype_def detype_ext_def crunch_simps
          wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: freeMemory)
crunch scheduler_action[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv'
   simp: detype_def detype_ext_def crunch_simps
         wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: freeMemory)
crunch cur_domain[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv'
      simp: detype_def detype_ext_def whenE_def unless_def
            wrap_ext_det_ext_ext_def mapM_x_defsym
    ignore: freeMemory)
crunch release_queue[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s. P (release_queue s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv'
      simp: detype_def detype_ext_def whenE_def unless_def
            wrap_ext_det_ext_ext_def mapM_x_defsym
    ignore: freeMemory)
crunch idle_thread[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s. P (idle_thread s)"
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

crunch ekheap[wp]: do_machine_op "\<lambda>s. P (ekheap s)"

lemma delete_objects_etcb_at[wp, DetSchedAux_AI_assms]:
  "\<lbrace>\<lambda>s::det_ext state. etcb_at P t s\<rbrace> delete_objects a b \<lbrace>\<lambda>r s. etcb_at P t s\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (wp)
  apply (simp add: detype_def detype_ext_def wrap_ext_det_ext_ext_def etcb_at_def|wp)+
  done

lemma delete_objects_bound_sc_tcb_at[wp, DetSchedAux_AI_assms]:
  "\<lbrace>bound_sc_tcb_at P t and invs
and K (t \<notin> {a..a + 2 ^ b - 1})\<rbrace>
 delete_objects a b \<lbrace>\<lambda>r s. bound_sc_tcb_at P t s\<rbrace>"
  apply (wpsimp wp: delete_objects_st_tcb_at)
  done

crunches reset_untyped_cap
for etcb_at[wp]: "etcb_at P t"
and valid_etcbs[wp]: valid_etcbs
  (wp: preemption_point_inv' mapME_x_inv_wp crunch_wps
    simp: unless_def)

lemma invoke_untyped_etcb_at [DetSchedAux_AI_assms]:
  "\<lbrace>(\<lambda>s :: det_ext state. etcb_at P t s) and valid_etcbs\<rbrace> invoke_untyped ui \<lbrace>\<lambda>r s. st_tcb_at (Not o inactive) t s \<longrightarrow> etcb_at P t s\<rbrace>"
  apply (cases ui)
  apply (simp add: mapM_x_def[symmetric] invoke_untyped_def whenE_def
           split del: if_split)
  apply (wp retype_region_etcb_at mapM_x_wp'
            create_cap_no_pred_tcb_at typ_at_pred_tcb_at_lift
            hoare_convert_imp[OF create_cap_no_pred_tcb_at]
            hoare_convert_imp[OF _ init_arch_objects_exst]
      | simp
      | (wp_once hoare_drop_impE_E))+
  done

lemma invoke_untyped_bound_sc_tcb_at[wp,DetSchedAux_AI_assms]:
  "\<lbrace>invs and st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t
and bound_sc_tcb_at Q t
         and ct_active and valid_untyped_inv ui\<rbrace>
     invoke_untyped ui
   \<lbrace>\<lambda>rv. \<lambda>s . bound_sc_tcb_at Q t s\<rbrace>"
  apply (rule hoare_pre, rule invoke_untyped_Q,
    (wp init_arch_objects_wps | simp)+)
     apply (rule hoare_name_pre_state, clarsimp)
     apply (wp retype_region_st_tcb_at, auto)[1]
    apply (wp reset_untyped_cap_st_tcb_at reset_untyped_cap_bound_sc_tcb_at| simp)+
  apply (cases ui, clarsimp)
  apply (frule(1) st_tcb_ex_cap[OF _ invs_iflive])
   apply (clarsimp split: Structures_A.thread_state.splits)
  apply (drule ex_nonz_cap_to_overlap,
    ((simp add:cte_wp_at_caps_of_state
            is_cap_simps descendants_range_def2
            empty_descendants_range_in)+))
  done

lemma invoke_untyped_schedulable_tcb_at[wp,DetSchedAux_AI_assms]:
  "\<lbrace>invs and st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t
and schedulable_tcb_at t
         and ct_active and valid_untyped_inv ui\<rbrace>
     invoke_untyped ui
   \<lbrace>\<lambda>rv. \<lambda>s . schedulable_tcb_at t s\<rbrace>"
  apply (rule hoare_pre, rule invoke_untyped_Q,
    (wp init_arch_objects_wps | simp)+)
     apply (rule hoare_name_pre_state, clarsimp)
(*     apply (wp retype_region_st_tcb_at, auto)[1]
    apply (wp reset_untyped_cap_st_tcb_at reset_untyped_cap_bound_sc_tcb_at| simp)+
  apply (cases ui, clarsimp)
  apply (frule(1) st_tcb_ex_cap[OF _ invs_iflive])
   apply (clarsimp split: Structures_A.thread_state.splits)
  apply (drule ex_nonz_cap_to_overlap,
    ((simp add:cte_wp_at_caps_of_state
            is_cap_simps descendants_range_def2
            empty_descendants_range_in)+))*)
  sorry

crunch valid_blocked[wp, DetSchedAux_AI_assms]: init_arch_objects valid_blocked
  (wp: valid_blocked_lift set_cap_typ_at)

crunch ct[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps do_machine_op_def detype_def mapM_x_defsym
   ignore: freeMemory ignore: retype_region_ext)

crunch ready_queues[wp, DetSchedAux_AI_assms]:
  invoke_untyped "\<lambda>s :: det_ext state. P (ready_queues s)"
  (wp: crunch_wps
   simp: detype_def detype_ext_def wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: freeMemory)

crunch scheduler_action[wp, DetSchedAux_AI_assms]:
  invoke_untyped "\<lambda>s :: det_ext state. P (scheduler_action s)"
  (wp: crunch_wps
   simp: detype_def detype_ext_def wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: freeMemory)

crunch cur_domain[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s :: det_ext state. P (cur_domain s)"
  (wp: crunch_wps
   simp: detype_def detype_ext_def wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: freeMemory)

crunch idle_thread[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps dxo_wp_weak hoare_unless_wp
   simp: detype_def detype_ext_def wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: freeMemory retype_region_ext)

lemma perform_asid_control_etcb_at:"\<lbrace>(\<lambda>s. etcb_at P t s) and valid_etcbs\<rbrace>
          perform_asid_control_invocation aci
          \<lbrace>\<lambda>r s. st_tcb_at (Not \<circ> inactive) t s \<longrightarrow> etcb_at P t s\<rbrace>"
  apply (simp add: perform_asid_control_invocation_def)
  apply (rule hoare_pre)
   apply (wp | wpc | simp)+
       apply (wp hoare_imp_lift_something typ_at_pred_tcb_at_lift)[1]
      apply (rule hoare_drop_imps)
      apply (wp retype_region_etcb_at)+
  apply simp
  done

lemma perform_asid_control_invocation_bound_sc_tcb_at:
  "\<lbrace>st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t and bound_sc_tcb_at P t
    and ct_active and invs and valid_aci aci\<rbrace>
    perform_asid_control_invocation aci
  \<lbrace>\<lambda>y. bound_sc_tcb_at P t\<rbrace>"
  including no_pre
  apply (clarsimp simp: perform_asid_control_invocation_def split: asid_control_invocation.splits)
  apply (rename_tac word1 a b aa ba word2)
  apply (wp hoare_vcg_const_imp_lift retype_region_st_tcb_at set_cap_no_overlap|simp)+
    apply (strengthen invs_valid_objs invs_psp_aligned)
    apply (clarsimp simp:conj_comms)
    apply (wp max_index_upd_invs_simple get_cap_wp)+
   apply (rule hoare_name_pre_state)
   apply (subgoal_tac "is_aligned word1 page_bits")
   prefer 2
    apply (clarsimp simp: valid_aci_def cte_wp_at_caps_of_state)
    apply (drule(1) caps_of_state_valid[rotated])+
    apply (simp add:valid_cap_simps cap_aligned_def page_bits_def)
   apply (subst delete_objects_rewrite)
      apply (simp add:page_bits_def word_bits_def pageBits_def word_size_bits_def)+
    apply (simp add:is_aligned_neg_mask_eq)
   apply wp
  apply (clarsimp simp: valid_aci_def)
  apply (frule intvl_range_conv)
   apply (simp add:word_bits_def page_bits_def pageBits_def)
  apply (clarsimp simp:detype_clear_um_independent page_bits_def is_aligned_neg_mask_eq)
  apply (rule conjI)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (rule pspace_no_overlap_detype)
     apply (rule caps_of_state_valid_cap)
      apply (simp add:page_bits_def)+
    apply (simp add:invs_valid_objs invs_psp_aligned)+
  apply (rule conjI)
   apply (frule st_tcb_ex_cap)
     apply clarsimp
    apply (clarsimp split: Structures_A.thread_state.splits)
   apply (clarsimp simp: ex_nonz_cap_to_def)
   apply (frule invs_untyped_children)
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (erule_tac ptr="(aa,ba)" in untyped_children_in_mdbE[where P="\<lambda>c. t \<in> zobj_refs c" for t])
       apply (simp add: cte_wp_at_caps_of_state)+
      apply fastforce
    apply (clarsimp simp: zobj_refs_to_obj_refs)
    apply (fastforce simp:page_bits_def)
   apply simp
  apply (clarsimp simp:obj_bits_api_def arch_kobj_size_def cte_wp_at_caps_of_state
    default_arch_object_def empty_descendants_range_in)
  apply (frule_tac cap = "(cap.UntypedCap False word1 pageBits idx)"
    in detype_invariants[rotated 3],clarsimp+)
    apply (simp add:cte_wp_at_caps_of_state
      empty_descendants_range_in descendants_range_def2)+
  apply (thin_tac "x = Some cap.NullCap" for x)+
  apply (drule(1) caps_of_state_valid_cap[OF _ invs_valid_objs])
  apply (intro conjI)
    apply (clarsimp simp:valid_cap_def cap_aligned_def range_cover_full
     invs_psp_aligned invs_valid_objs page_bits_def)
   apply (erule pspace_no_overlap_detype)
  apply (auto simp:page_bits_def detype_clear_um_independent)
  done

lemma perform_asid_control_invocation_schedulable_tcb_at:
  "\<lbrace>st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t and schedulable_tcb_at t
    and ct_active and invs and valid_aci aci\<rbrace>
    perform_asid_control_invocation aci
  \<lbrace>\<lambda>y. schedulable_tcb_at t\<rbrace>"
  including no_pre
  apply (clarsimp simp: perform_asid_control_invocation_def split: asid_control_invocation.splits)
  apply (rename_tac word1 a b aa ba word2)
  apply (wp hoare_vcg_const_imp_lift retype_region_st_tcb_at set_cap_no_overlap|simp)+
(*    apply (strengthen invs_valid_objs invs_psp_aligned)
    apply (clarsimp simp:conj_comms)
    apply (wp max_index_upd_invs_simple get_cap_wp)+
   apply (rule hoare_name_pre_state)
   apply (subgoal_tac "is_aligned word1 page_bits")
   prefer 2
    apply (clarsimp simp: valid_aci_def cte_wp_at_caps_of_state)
    apply (drule(1) caps_of_state_valid[rotated])+
    apply (simp add:valid_cap_simps cap_aligned_def page_bits_def)
   apply (subst delete_objects_rewrite)
      apply (simp add:page_bits_def word_bits_def pageBits_def word_size_bits_def)+
    apply (simp add:is_aligned_neg_mask_eq)
   apply wp
  apply (clarsimp simp: valid_aci_def)
  apply (frule intvl_range_conv)
   apply (simp add:word_bits_def page_bits_def pageBits_def)
  apply (clarsimp simp:detype_clear_um_independent page_bits_def is_aligned_neg_mask_eq)
  apply (rule conjI)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (rule pspace_no_overlap_detype)
     apply (rule caps_of_state_valid_cap)
      apply (simp add:page_bits_def)+
    apply (simp add:invs_valid_objs invs_psp_aligned)+
  apply (rule conjI)
   apply (frule st_tcb_ex_cap)
     apply clarsimp
    apply (clarsimp split: Structures_A.thread_state.splits)
   apply (clarsimp simp: ex_nonz_cap_to_def)
   apply (frule invs_untyped_children)
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (erule_tac ptr="(aa,ba)" in untyped_children_in_mdbE[where P="\<lambda>c. t \<in> zobj_refs c" for t])
       apply (simp add: cte_wp_at_caps_of_state)+
      apply fastforce
    apply (clarsimp simp: zobj_refs_to_obj_refs)
    apply (fastforce simp:page_bits_def)
   apply simp
  apply (clarsimp simp:obj_bits_api_def arch_kobj_size_def cte_wp_at_caps_of_state
    default_arch_object_def empty_descendants_range_in)
  apply (frule_tac cap = "(cap.UntypedCap False word1 pageBits idx)"
    in detype_invariants[rotated 3],clarsimp+)
    apply (simp add:cte_wp_at_caps_of_state
      empty_descendants_range_in descendants_range_def2)+
  apply (thin_tac "x = Some cap.NullCap" for x)+
  apply (drule(1) caps_of_state_valid_cap[OF _ invs_valid_objs])
  apply (intro conjI)
    apply (clarsimp simp:valid_cap_def cap_aligned_def range_cover_full
     invs_psp_aligned invs_valid_objs page_bits_def)
   apply (erule pspace_no_overlap_detype)
  apply (auto simp:page_bits_def detype_clear_um_independent)*)
  sorry

crunches perform_asid_control_invocation
for ct[wp]: "\<lambda>s. P (cur_thread s)"
and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
and valid_etcbs[wp]: valid_etcbs
and valid_blocked[wp]: valid_blocked
 (wp: static_imp_wp)

crunches perform_asid_control_invocation
for rqueues[wp]: "\<lambda>s :: det_ext state. P (ready_queues s)"
and schedact[wp]: "\<lambda>s :: det_ext state. P (scheduler_action s)"
and cur_domain[wp]: "\<lambda>s :: det_ext state. P (cur_domain s)"
and release_queue[wp]: "\<lambda>s :: det_ext state. P (release_queue s)"
 (wp: crunch_wps simp: detype_def detype_ext_def wrap_ext_det_ext_ext_def cap_insert_ext_def ignore: freeMemory)

lemma perform_asid_control_invocation_valid_sched:
  "\<lbrace>ct_active and invs and valid_aci aci and valid_sched and valid_idle\<rbrace>
     perform_asid_control_invocation aci
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (rule hoare_pre)
   apply (rule_tac I="invs and ct_active and valid_aci aci" in valid_sched_tcb_state_preservation_gen)
          apply (wp perform_asid_control_invocation_st_tcb_at)
          apply simp
         apply (wpsimp wp: perform_asid_control_etcb_at perform_asid_control_invocation_schedulable_tcb_at)+
    apply (rule hoare_strengthen_post, rule aci_invs)
    apply (simp add: invs_def valid_state_def)
   apply (rule hoare_lift_Pf[where f="\<lambda>s. scheduler_action s"])
    apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_domain s"])
     apply (rule hoare_lift_Pf[where f="\<lambda>s. idle_thread s"])
     apply (rule hoare_lift_Pf[where f="\<lambda>s. release_queue s"])
      apply wp+
  apply simp
  done

crunch valid_queues[wp]: init_arch_objects valid_queues (wp: valid_queues_lift)

lemma set_pd_schedulable_tcb_at[wp]:
  "\<lbrace>schedulable_tcb_at t\<rbrace> set_pd ptr val \<lbrace>\<lambda>_. schedulable_tcb_at t\<rbrace>"
  apply (simp add: set_pd_def set_object_def)
  apply (wpsimp wp: get_object_wp)
  apply (clarsimp simp: schedulable_tcb_at_def pred_tcb_at_def obj_at_def)
  apply (case_tac "t=ptr"; clarsimp)
  apply (rule_tac x=scp in exI, clarsimp)
  done

lemma set_pt_schedulable_tcb_at[wp]:
  "\<lbrace>schedulable_tcb_at t\<rbrace> set_pt ptr val \<lbrace>\<lambda>_. schedulable_tcb_at t\<rbrace>"
  apply (simp add: set_pt_def set_object_def)
  apply (wpsimp wp: get_object_wp)
  apply (clarsimp simp: schedulable_tcb_at_def pred_tcb_at_def obj_at_def)
  apply (case_tac "t=ptr"; clarsimp)
  apply (rule_tac x=scp in exI, clarsimp)
  done

lemma set_asid_pool_schedulable_tcb_at[wp]:
  "\<lbrace>schedulable_tcb_at t\<rbrace> set_asid_pool ptr val \<lbrace>\<lambda>_. schedulable_tcb_at t\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wpsimp wp: get_object_wp)
  apply (clarsimp simp: schedulable_tcb_at_def pred_tcb_at_def obj_at_def)
  apply (case_tac "t=ptr"; clarsimp)
  apply (rule_tac x=scp in exI, clarsimp)
  done

crunch schedulable_tcb_at[wp]: init_arch_objects "schedulable_tcb_at t"
  (wp: crunch_wps ignore: do_machine_op)

crunch valid_sched_action[wp]: init_arch_objects valid_sched_action (wp: valid_sched_action_lift)

crunch valid_sched[wp]: init_arch_objects valid_sched (wp: valid_sched_lift)

end

lemmas tcb_sched_action_valid_idle_etcb
    = ARM.tcb_sched_action_valid_idle_etcb

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
