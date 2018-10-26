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
  (wp: crunch_wps hoare_unless_wp)

crunch ct[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps dxo_wp_weak preemption_point_inv mapME_x_inv_wp
    simp: crunch_simps do_machine_op_def detype_def mapM_x_defsym unless_def
    ignore: freeMemory)

crunch ready_queues[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s::det_ext state. P (ready_queues s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv'
    simp: detype_def whenE_def unless_def wrap_ext_det_ext_ext_def mapM_x_defsym
  ignore: freeMemory)

crunch scheduler_action[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s::det_ext state. P (scheduler_action s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv'
      simp: detype_def whenE_def unless_def wrap_ext_det_ext_ext_def mapM_x_defsym
    ignore: freeMemory)

crunch cur_domain[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s::det_ext state. P (cur_domain s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv'
      simp: detype_def whenE_def unless_def wrap_ext_det_ext_ext_def mapM_x_defsym
    ignore: freeMemory)

crunch release_queue[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s::det_ext state. P (release_queue s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv'
      simp: detype_def whenE_def unless_def wrap_ext_det_ext_ext_def mapM_x_defsym
    ignore: freeMemory)

crunch idle_thread[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s::det_ext state. P (idle_thread s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv dxo_wp_weak
      simp: detype_def whenE_def unless_def wrap_ext_det_ext_ext_def mapM_x_defsym
    ignore: freeMemory)

lemma tcb_sched_action_valid_idle_etcb:
  "tcb_sched_action sa thread \<lbrace>valid_idle_etcb\<rbrace>"
  by (rule tcb_sched_action_kheap)

crunch ekheap[wp]: do_machine_op "\<lambda>s. P (etcbs_of s)"

lemma delete_objects_etcb_at[wp, DetSchedAux_AI_assms]:
  "\<lbrace>\<lambda>s::det_ext state. etcb_at P t s\<rbrace> delete_objects a b \<lbrace>\<lambda>r s. etcb_at P t s\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (wpsimp simp: detype_def wrap_ext_det_ext_ext_def)
  apply (simp add: etcbs_of'_def etcb_at'_def)
  done

declare delete_objects_st_tcb_at[wp, DetSchedAux_AI_assms]

crunches reset_untyped_cap
for etcb_at[wp]: "etcb_at P t :: det_ext state \<Rightarrow> _"
  (wp: preemption_point_inv' mapME_x_inv_wp crunch_wps
   simp: unless_def)

lemma foldr_kh_eq:
  "foldr (\<lambda>p kh. kh(p \<mapsto> ko')) ptrs kh t = Some ko \<Longrightarrow>
  if t \<in> set ptrs then ko = ko' else kh t = Some ko"
  by (induct ptrs) (auto split: if_split_asm)

lemma TCB_default_objectD[dest!]:
  "\<lbrakk>  TCB tcb = default_object t dev c dm; t \<noteq> Untyped \<rbrakk> \<Longrightarrow> tcb = default_tcb dm"
  by (simp add: default_object_def split: apiobject_type.splits)

declare tcb_state_merge_tcb_state_default[simp]

lemma retype_region_etcb_at[wp]:
  "\<lbrace>etcb_at P t\<rbrace> retype_region a b c d dev \<lbrace>\<lambda>r s. st_tcb_at (Not o inactive) t s \<longrightarrow> etcb_at P t s\<rbrace> "
  apply (simp add: retype_region_def)
  apply wp
  apply (clarsimp simp add: pred_tcb_at_def obj_at_def simp del: fun_upd_apply)
  apply (clarsimp simp: etcbs_of'_def etcb_at'_def etcb_of_def)
  apply (drule foldr_kh_eq)
  apply (auto simp: etcb_of_def split: if_split_asm option.splits elim!: rsubst[where P=P])
  done

lemma set_pd_etcbs[wp]:
  "set_pd p pd \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_pd_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (auto elim!: rsubst[where P=P] simp: etcbs_of'_def obj_at_def split: kernel_object.splits)
  done

crunch etcb_at[wp]: init_arch_objects "\<lambda>s. P (etcbs_of s)"
  (wp: crunch_wps ignore: set_object)

lemma invoke_untyped_etcb_at [DetSchedAux_AI_assms]:
  "\<lbrace>\<lambda>s :: det_ext state. etcb_at P t s\<rbrace> invoke_untyped ui \<lbrace>\<lambda>r s. st_tcb_at (Not o inactive) t s \<longrightarrow> etcb_at P t s\<rbrace>"
  apply (cases ui)
  apply (simp add: mapM_x_def[symmetric] invoke_untyped_def whenE_def
           split del: if_split)
  apply (wp mapM_x_wp'
            create_cap_no_pred_tcb_at typ_at_pred_tcb_at_lift
            hoare_convert_imp[OF create_cap_no_pred_tcb_at]
            hoare_convert_imp[OF _ init_arch_objects_etcb_at]
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

(* FIXME: move *)
lemma schedulable_tcb_at_def2:
  "schedulable_tcb_at t = (\<lambda>s.
          (\<exists>scp. bound_sc_tcb_at (\<lambda>sc. sc = Some scp) t s
                \<and> obj_at (\<lambda>obj. \<exists>sc n. obj = SchedContext sc n
                             \<and> 0 < sc_refill_max sc) scp s))"
  by (auto simp: pred_tcb_at_def schedulable_tcb_at_def obj_at_def)

(* FIEXME: move? *)
lemma init_arch_objects_obj_at_impossible:
  "\<forall>ao. \<not> P (ArchObj ao) \<Longrightarrow>
    \<lbrace>\<lambda>s. Q (obj_at P p s)\<rbrace> init_arch_objects a b c d e \<lbrace>\<lambda>rv s. Q (obj_at P p s)\<rbrace>"
  apply (wpsimp simp: init_arch_objects_def copy_global_mappings_def store_pde_def
                      set_pd_def set_object_def obj_at_def
                  wp: mapM_x_wp' get_object_wp get_pde_wp)
  done

(* FIXME: move? *)
lemma init_arch_objects_schedulable_tcb_at[wp]:
  "\<lbrace>schedulable_tcb_at t\<rbrace>
     init_arch_objects a b c d e
   \<lbrace>\<lambda>rv. schedulable_tcb_at t\<rbrace>"
  apply (rule hoare_pre)
   apply (clarsimp simp: schedulable_tcb_at_def2)
   apply (wpsimp wp: hoare_vcg_ex_lift init_arch_objects_obj_at_impossible)
  apply (clarsimp simp: schedulable_tcb_at_def2)
  done

lemma retype_region_schedulable_tcb_at:
  "\<lbrace>\<lambda>s. pspace_no_overlap (up_aligned_area ptr' sz) s \<and>
      range_cover ptr' sz (obj_bits_api ty us) n \<and>
      valid_objs s \<and> pspace_aligned s
      \<and> schedulable_tcb_at t s\<rbrace>
     retype_region ptr' n us ty dev
   \<lbrace>\<lambda>rv. schedulable_tcb_at t\<rbrace>"
  apply (clarsimp simp: schedulable_tcb_at_def2)
  apply (wpsimp wp: retype_region_obj_at_other3 hoare_vcg_ex_lift
                    retype_region_st_tcb_at)
  by auto

lemma reset_untyped_cap_sched_context_at:
  "\<lbrace>invs and obj_at (\<lambda>obj. (\<exists>sc n. (obj = SchedContext sc n) \<and> P sc n)) t and cte_wp_at (\<lambda>cp. t \<notin> cap_range cp \<and> is_untyped_cap cp) slot\<rbrace>
    reset_untyped_cap slot
  \<lbrace>\<lambda>_. obj_at (\<lambda>obj. (\<exists>sc n. (obj = SchedContext sc n) \<and> P sc n)) t\<rbrace>, \<lbrace>\<lambda>_. obj_at (\<lambda>obj. (\<exists>sc n. (obj = SchedContext sc n) \<and> P sc n)) t\<rbrace>"
  apply (simp add: reset_untyped_cap_def)
  apply (rule hoare_pre)
   apply (wp mapME_x_inv_wp preemption_point_inv set_cap_obj_at_impossible | simp add: unless_def
     | solves \<open>auto simp: caps_of_def cap_of_def\<close>)+
    apply (simp add: delete_objects_def)
    apply (wp get_cap_wp hoare_vcg_const_imp_lift | simp)+
  apply (auto simp: cte_wp_at_caps_of_state cap_range_def
                    bits_of_def is_cap_simps caps_of_def cap_of_def)
  done

lemma reset_untyped_cap_schedulable_tcb_at:
  "\<lbrace>invs and cte_wp_at (\<lambda>cp. t \<notin> cap_range cp \<and> is_untyped_cap cp) slot
         and schedulable_tcb_at t\<rbrace>
     reset_untyped_cap slot
   \<lbrace>\<lambda>rv. schedulable_tcb_at t\<rbrace>, \<lbrace>\<lambda>rv. schedulable_tcb_at t\<rbrace>"
  apply (clarsimp simp: schedulable_tcb_at_def2)
  apply (wpsimp wp: reset_untyped_cap_bound_sc_tcb_at hoare_vcg_ex_lift
                    reset_untyped_cap_sched_context_at)
  sorry (* not entirely sure why this doesnt work *)

lemma invoke_untyped_schedulable_tcb_at[wp,DetSchedAux_AI_assms]:
  "\<lbrace>invs and st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t
and schedulable_tcb_at t
         and ct_active and valid_untyped_inv ui\<rbrace>
     invoke_untyped ui
   \<lbrace>\<lambda>rv. \<lambda>s :: det_ext state . schedulable_tcb_at t s\<rbrace>"
  apply (rule hoare_pre, rule invoke_untyped_Q,
    (wp init_arch_objects_wps | simp)+)
     apply (rule hoare_name_pre_state, clarsimp)
     apply (wp retype_region_schedulable_tcb_at, auto)[1]
    apply (wp reset_untyped_cap_st_tcb_at reset_untyped_cap_schedulable_tcb_at| simp)+
  apply (cases ui, clarsimp)
  apply (frule(1) st_tcb_ex_cap[OF _ invs_iflive])
   apply (clarsimp split: Structures_A.thread_state.splits)
  apply (drule ex_nonz_cap_to_overlap,
    ((simp add:cte_wp_at_caps_of_state
            is_cap_simps descendants_range_def2
            empty_descendants_range_in)+))
  done

crunch valid_blocked[wp, DetSchedAux_AI_assms]: init_arch_objects "valid_blocked::det_ext state \<Rightarrow> _"
  (wp: valid_blocked_lift set_cap_typ_at)

crunch ct[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps do_machine_op_def detype_def mapM_x_defsym
   ignore: freeMemory)

crunch ready_queues[wp, DetSchedAux_AI_assms]:
  invoke_untyped "\<lambda>s :: det_ext state. P (ready_queues s)"
  (wp: crunch_wps
   simp: detype_def wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: freeMemory)

crunch scheduler_action[wp, DetSchedAux_AI_assms]:
  invoke_untyped "\<lambda>s :: det_ext state. P (scheduler_action s)"
  (wp: crunch_wps
   simp: detype_def wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: freeMemory)

crunch cur_domain[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s :: det_ext state. P (cur_domain s)"
  (wp: crunch_wps
   simp: detype_def wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: freeMemory)

lemma perform_asid_control_etcb_at:"\<lbrace>etcb_at P t::det_ext state \<Rightarrow> _\<rbrace>
          perform_asid_control_invocation aci
          \<lbrace>\<lambda>r s. st_tcb_at (Not \<circ> inactive) t s \<longrightarrow> etcb_at P t s\<rbrace>"
  apply (simp add: perform_asid_control_invocation_def)
  apply (rule hoare_pre)
   apply (wp | wpc | simp)+
       apply (wp hoare_convert_imp typ_at_pred_tcb_at_lift)[1]
      apply (rule hoare_drop_imps)
      apply (wp retype_region_etcb_at)+
  apply simp
  done

lemma perform_asid_control_invocation_bound_sc_tcb_at:
  "\<lbrace>st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t and bound_sc_tcb_at P t
    and ct_active and invs and valid_aci aci\<rbrace>
    perform_asid_control_invocation aci
  \<lbrace>\<lambda>_. bound_sc_tcb_at P t::det_ext state \<Rightarrow> _\<rbrace>"
  including no_pre
  supply
    is_aligned_neg_mask_eq[simp del]
    is_aligned_neg_mask_weaken[simp del]
  apply (clarsimp simp: perform_asid_control_invocation_def split: asid_control_invocation.splits)
  apply (rename_tac word1 a b aa ba word2)
  apply (wp hoare_vcg_const_imp_lift retype_region_st_tcb_at
            set_cap_no_overlap|simp)+
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
    apply (clarsimp simp: valid_cap_def cap_aligned_def range_cover_full
                          invs_psp_aligned invs_valid_objs page_bits_def)
   apply (erule pspace_no_overlap_detype)
  apply (auto simp:page_bits_def detype_clear_um_independent)
  done

lemma perform_asid_control_invocation_schedulable_tcb_at:
  "\<lbrace>st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t and schedulable_tcb_at t
    and ct_active and invs and valid_aci aci\<rbrace>
    perform_asid_control_invocation aci
  \<lbrace>\<lambda>_. schedulable_tcb_at t :: det_ext state \<Rightarrow> _\<rbrace>"
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
and idle_thread[wp]: "\<lambda>s::det_ext state. P (idle_thread s)"
and valid_blocked[wp]: valid_blocked
 (wp: static_imp_wp)

crunches perform_asid_control_invocation
for rqueues[wp]: "\<lambda>s :: det_ext state. P (ready_queues s)"
and schedact[wp]: "\<lambda>s :: det_ext state. P (scheduler_action s)"
and cur_domain[wp]: "\<lambda>s :: det_ext state. P (cur_domain s)"
and release_queue[wp]: "\<lambda>s :: det_ext state. P (release_queue s)"
 (wp: crunch_wps simp: detype_def wrap_ext_det_ext_ext_def cap_insert_ext_def ignore: freeMemory)

lemma perform_asid_control_invocation_valid_sched:
  "\<lbrace>ct_active and invs and valid_aci aci and valid_sched and valid_idle\<rbrace>
     perform_asid_control_invocation aci
   \<lbrace>\<lambda>_. valid_sched::det_ext state \<Rightarrow> _\<rbrace>"
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

crunch valid_queues[wp]: init_arch_objects "valid_queues :: det_ext state \<Rightarrow> _"
  (wp: valid_queues_lift crunch_wps)

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

crunch valid_sched_action[wp]: init_arch_objects "valid_sched_action :: det_ext state \<Rightarrow> _"
  (wp: valid_sched_action_lift)

crunch valid_sched[wp]: init_arch_objects "valid_sched :: det_ext state \<Rightarrow> _"
  (wp: valid_sched_lift)

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
