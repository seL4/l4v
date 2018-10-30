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

lemma set_pd_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> set_pd param_a param_b \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
  apply (clarsimp simp: set_pd_def)
  apply (wpsimp simp: set_object_def active_sc_tcb_at_def pred_tcb_at_def obj_at_def wp: get_object_wp)
  apply (intro conjI impI allI; clarsimp elim!: rsubst[where P=P])
  apply (intro iffI; clarsimp simp: test_sc_refill_max_def split: option.splits if_split_asm)
  by (case_tac y; fastforce)+

lemma set_pd_budget_sufficient[wp]:
  "\<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace> set_pd param_a param_b \<lbrace>\<lambda>_ s. P (budget_sufficient t s)\<rbrace>"
  apply (clarsimp simp: set_pd_def)
  apply (wpsimp simp: set_object_def pred_tcb_at_def obj_at_def wp: get_object_wp)
  apply (intro conjI impI allI; clarsimp elim!: rsubst[where P=P])
  by (intro iffI; fastforce simp: is_refill_sufficient_def obj_at_def split: option.splits if_split_asm)

lemma set_pd_budget_ready[wp]:
  "\<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace> set_pd param_a param_b \<lbrace>\<lambda>_ s. P (budget_ready t s)\<rbrace>"
  apply (clarsimp simp: set_pd_def)
  apply (wpsimp simp: set_object_def  pred_tcb_at_def obj_at_def wp: get_object_wp)
  apply (intro conjI impI allI; clarsimp elim!: rsubst[where P=P])
  by (intro iffI; fastforce simp: is_refill_ready_def obj_at_def split: option.splits if_split_asm)

crunches init_arch_objects
for exst[wp]: "\<lambda>s. P (exst s)"
and ct[wp]:  "\<lambda>s. P (cur_thread s)"
and st_tcb_at[wp]:  "st_tcb_at Q t"
and active_sc_tcb_at[wp]:  "\<lambda>s. P (active_sc_tcb_at t s)"
and budget_sufficient[wp]:  "\<lambda>s. P (budget_sufficient t s)"
and budget_ready[wp]:  "\<lambda>s. P (budget_ready t s)"
 (wp: mapM_x_wp' crunch_wps hoare_unless_wp)

crunch ct[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps dxo_wp_weak preemption_point_inv mapME_x_inv_wp
    simp: crunch_simps do_machine_op_def detype_def mapM_x_defsym unless_def
    ignore: freeMemory)

crunch ready_queues[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s::det_ext state. P (ready_queues s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv'
    simp: detype_def whenE_def unless_def wrap_ext_det_ext_ext_def mapM_x_defsym
  ignore: freeMemory)

crunch release_queue[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s::det_ext state. P (release_queue s)"
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
lemma active_sc_tcb_at_def2:
  "active_sc_tcb_at t = (\<lambda>s.
          (\<exists>scp. bound_sc_tcb_at (\<lambda>sc. sc = Some scp) t s
                \<and> obj_at (\<lambda>obj. \<exists>sc n. obj = SchedContext sc n
                             \<and> 0 < sc_refill_max sc) scp s))"
  apply (auto simp: pred_tcb_at_def active_sc_tcb_at_def obj_at_def test_sc_refill_max_def
            split: option.splits intro!: ext)
  apply (case_tac y; clarsimp)
  by fastforce

(* FIXME: move *)
lemma budget_sufficient_def2:
  "budget_sufficient t = (\<lambda>s.
          (\<exists>scp. bound_sc_tcb_at (\<lambda>sc. sc = Some scp) t s
                \<and> obj_at (\<lambda>obj. \<exists>sc n. obj = SchedContext sc n
                             \<and> sufficient_refills 0 (sc_refills sc)) scp s))"
  by (auto simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def
            split: option.splits intro!: ext)

(* FIXME: move *)
lemma budget_ready_def2:
  "budget_ready t = (\<lambda>s.
          (\<exists>scp. bound_sc_tcb_at (\<lambda>sc. sc = Some scp) t s
                \<and> obj_at (\<lambda>obj. \<exists>sc n. obj = SchedContext sc n
                             \<and> (r_time (refill_hd sc)) \<le> (cur_time s) + kernelWCET_ticks) scp s))"
  by (auto simp: pred_tcb_at_def obj_at_def is_refill_ready_def
            split: option.splits intro!: ext)

(* FIEXME: move? *)
lemma init_arch_objects_obj_at_impossible:
  "\<forall>ao. \<not> P (ArchObj ao) \<Longrightarrow>
    \<lbrace>\<lambda>s. Q (obj_at P p s)\<rbrace> init_arch_objects a b c d e \<lbrace>\<lambda>rv s. Q (obj_at P p s)\<rbrace>"
  apply (wpsimp simp: init_arch_objects_def copy_global_mappings_def store_pde_def
                      set_pd_def set_object_def obj_at_def
                  wp: mapM_x_wp' get_object_wp get_pde_wp)
  done

lemma retype_region_active_sc_tcb_at:
  "\<lbrace>\<lambda>s. pspace_no_overlap (up_aligned_area ptr' sz) s \<and>
      range_cover ptr' sz (obj_bits_api ty us) n \<and>
      valid_objs s \<and> pspace_aligned s
      \<and> active_sc_tcb_at t s\<rbrace>
     retype_region ptr' n us ty dev
   \<lbrace>\<lambda>rv. active_sc_tcb_at t\<rbrace>"
  apply (clarsimp simp: active_sc_tcb_at_def2)
  apply (wpsimp wp: retype_region_obj_at_other3 hoare_vcg_ex_lift
                    retype_region_st_tcb_at)
  by auto

lemma reset_untyped_cap_sched_context_at:
  "\<lbrace>invs and cte_wp_at (\<lambda>cp. t \<notin> cap_range cp \<and> is_untyped_cap cp) slot
    and obj_at (\<lambda>obj. (\<exists>sc n. (obj = SchedContext sc n) \<and> P sc)) t\<rbrace>
    reset_untyped_cap slot
  \<lbrace>\<lambda>_. obj_at (\<lambda>obj. (\<exists>sc n. (obj = SchedContext sc n) \<and> P sc)) t\<rbrace>, \<lbrace>\<lambda>_. obj_at (\<lambda>obj. (\<exists>sc n. (obj = SchedContext sc n) \<and> P sc)) t\<rbrace>"
  apply (simp add: reset_untyped_cap_def)
  apply (rule hoare_pre)
   apply (wp mapME_x_inv_wp preemption_point_inv set_cap_obj_at_impossible | simp add: unless_def
     | solves \<open>auto simp: caps_of_def cap_of_def\<close>)+
    apply (simp add: delete_objects_def)
    apply (wp get_cap_wp hoare_vcg_const_imp_lift | simp)+
  apply (auto simp: cte_wp_at_caps_of_state cap_range_def
                    bits_of_def is_cap_simps caps_of_def cap_of_def)
  done

lemma active_sc_tcb_at_machine_state_update_kheap[simp]:
  "active_sc_tcb_at t (s\<lparr>machine_state := f, kheap:=g\<rparr>) = active_sc_tcb_at t (s\<lparr>kheap:=g\<rparr>)"
  by (clarsimp simp: active_sc_tcb_at_defs)

lemma reset_untyped_cap_active_sc_tcb_at:
  "\<lbrace>invs and cte_wp_at (\<lambda>cp. t \<notin> cap_range cp \<and> is_untyped_cap cp) slot
    and (\<lambda>s. bound_sc_tcb_at (\<lambda>p. \<exists>scp. p = Some scp
      \<and> cte_wp_at (\<lambda>cp. scp \<notin> cap_range cp \<and> is_untyped_cap cp) slot s) t s)
         and active_sc_tcb_at t\<rbrace>
     reset_untyped_cap slot
   \<lbrace>\<lambda>rv. active_sc_tcb_at t\<rbrace>, \<lbrace>\<lambda>rv. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: active_sc_tcb_at_def2)
  apply (wpsimp wp: hoare_vcg_ex_lift hoare_vcg_conj_lift
      reset_untyped_cap_sched_context_at[where P="\<lambda>sc. 0 < sc_refill_max sc", simplified]
      reset_untyped_cap_bound_sc_tcb_at)
  apply (rule_tac x=scp in exI)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

(* do we need something like this? 
lemma obj_ref_ex_cap:
   "\<lbrakk>invs s; tcb_sched_context tcb = Some scp;
    kheap s t  = Some (TCB tcb)\<rbrakk> \<Longrightarrow> ex_nonz_cap_to scp s"
  *)

(* FIXME: Move to Invariants_AI *)
lemma sym_ref_tcb_sc: "\<lbrakk> sym_refs (state_refs_of s); kheap s tp = Some (TCB tcb);
   tcb_sched_context tcb = Some scp \<rbrakk> \<Longrightarrow>
  \<exists>sc n. kheap s scp = Some (SchedContext sc n) \<and> sc_tcb sc = Some tp"
  apply (drule sym_refs_obj_atD[rotated, where p=tp])
   apply (clarsimp simp: obj_at_def, simp)
  apply (clarsimp simp: state_refs_of_def get_refs_def2 elim!: sym_refsE)
  apply (drule_tac x="(scp, TCBSchedContext)" in bspec)
   apply fastforce
  apply (clarsimp simp: obj_at_def)
  apply (case_tac koa; clarsimp simp: get_refs_def2)
  done


lemma invoke_untyped_active_sc_tcb_at[wp,DetSchedAux_AI_assms]:
  "\<lbrace>invs and st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t
and active_sc_tcb_at t
         and ct_active and valid_untyped_inv ui\<rbrace>
     invoke_untyped ui
   \<lbrace>\<lambda>rv. \<lambda>s :: det_ext state . active_sc_tcb_at t s\<rbrace>"
  apply (rule hoare_pre, rule invoke_untyped_Q, (wp init_arch_objects_wps | simp)+)
     apply (rule hoare_name_pre_state, clarsimp)
     apply (wp retype_region_active_sc_tcb_at, auto)[1]
    apply (wp reset_untyped_cap_st_tcb_at reset_untyped_cap_active_sc_tcb_at| simp)+
  apply (cases ui, clarsimp simp: active_sc_tcb_at_def)
  apply (rule conjI)
   apply (frule(1) st_tcb_ex_cap[OF _ invs_iflive])
    apply (clarsimp split: Structures_A.thread_state.splits)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (drule ex_nonz_cap_to_overlap,
      ((simp add:cte_wp_at_caps_of_state
          is_cap_simps descendants_range_def2
          empty_descendants_range_in)+)[5])
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (subgoal_tac "ex_nonz_cap_to scp s")
   apply (drule ex_nonz_cap_to_overlap,
      ((simp add:cte_wp_at_caps_of_state
          is_cap_simps descendants_range_def2
          empty_descendants_range_in)+)[5])
  apply (frule invs_sym_refs)
  apply (drule (2) sym_ref_tcb_sc)
  apply clarsimp
  apply (frule invs_iflive)
  apply (erule (1) if_live_then_nonz_capD2)
  apply (clarsimp simp: live_def live_sc_def)
  done

lemma retype_region_budget_sufficient:
  "\<lbrace>(\<lambda>s. pspace_no_overlap (up_aligned_area ptr' sz) s \<and>
      range_cover ptr' sz (obj_bits_api ty us) n \<and>
      valid_objs s \<and> pspace_aligned s)
     and budget_sufficient t\<rbrace>
     retype_region ptr' n us ty dev
   \<lbrace>\<lambda>rv. budget_sufficient t\<rbrace>"
  apply (clarsimp simp: budget_sufficient_def2)
  apply (wpsimp wp: retype_region_obj_at_other3 hoare_vcg_ex_lift
                    retype_region_st_tcb_at)
  by auto

lemma reset_untyped_cap_budget_sufficient:
  "\<lbrace>invs and cte_wp_at (\<lambda>cp. t \<notin> cap_range cp \<and> is_untyped_cap cp) slot
   and (\<lambda>s. bound_sc_tcb_at (\<lambda>p. \<exists>scp. p = Some scp
      \<and> cte_wp_at (\<lambda>cp. scp \<notin> cap_range cp \<and> is_untyped_cap cp) slot s) t s)
         and budget_sufficient t\<rbrace>
     reset_untyped_cap slot
   \<lbrace>\<lambda>rv. budget_sufficient t\<rbrace>, \<lbrace>\<lambda>rv. budget_sufficient t::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: budget_sufficient_def2)
  apply (wpsimp wp: hoare_vcg_ex_lift hoare_vcg_conj_lift
      reset_untyped_cap_sched_context_at[where P="\<lambda>sc. sufficient_refills 0 (sc_refills sc)", simplified]
      reset_untyped_cap_bound_sc_tcb_at)
  apply (rule_tac x=scp in exI)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma invoke_untyped_budget_sufficient[wp,DetSchedAux_AI_assms]:
  "\<lbrace>invs and st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t and
       budget_sufficient t and ct_active and valid_untyped_inv ui\<rbrace>
     invoke_untyped ui
   \<lbrace>\<lambda>rv. \<lambda>s :: det_ext state . budget_sufficient t s\<rbrace>"
  apply (rule hoare_pre, rule invoke_untyped_Q,
    (wp init_arch_objects_wps | simp)+)
     apply (rule hoare_name_pre_state, clarsimp)
     apply (wp retype_region_budget_sufficient, auto)[1]
    apply (wp reset_untyped_cap_st_tcb_at reset_untyped_cap_budget_sufficient| simp)+
  apply (cases ui, clarsimp)
  apply (frule(1) st_tcb_ex_cap[OF _ invs_iflive])
   apply (clarsimp split: Structures_A.thread_state.splits)
  apply (drule ex_nonz_cap_to_overlap,
    ((simp add:cte_wp_at_caps_of_state
            is_cap_simps descendants_range_def2
            empty_descendants_range_in)+))
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (subgoal_tac "ex_nonz_cap_to scp s")
   apply (drule ex_nonz_cap_to_overlap,
      ((simp add:cte_wp_at_caps_of_state
          is_cap_simps descendants_range_def2
          empty_descendants_range_in)+)[5])
  apply (frule invs_sym_refs)
  apply (drule (2) sym_ref_tcb_sc)
  apply clarsimp
  apply (frule invs_iflive)
  apply (erule (1) if_live_then_nonz_capD2)
  apply (clarsimp simp: live_def live_sc_def)
  done

lemma set_cap_obj_at_impossible_cur_time:
  "\<lbrace>\<lambda>s. P (obj_at (P' (cur_time s)) p s) \<and> (\<forall>ko. P' (cur_time s) ko \<longrightarrow> caps_of ko = {})\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv s. P (obj_at (P' (cur_time s)) p s)\<rbrace>"
  apply (simp add: set_cap_def split_def set_object_def)
  apply (wp get_object_wp | wpc)+
  apply (clarsimp simp: obj_at_def)
  apply (subgoal_tac "\<forall>sz cs. well_formed_cnode_n sz cs \<longrightarrow> \<not> P' (cur_time s) (CNode sz cs)")
   apply (subgoal_tac "\<forall>tcb. \<not> P' (cur_time s) (TCB tcb)")
    apply (clarsimp simp: fun_upd_def[symmetric] wf_cs_insert dom_def)
    apply auto[1]
   apply (auto simp:caps_of_def cap_of_def ran_tcb_cnode_map wf_cs_ran_nonempty)
  done

lemma do_machine_op_obj_at_cur_time:
  "\<lbrace>\<lambda>s. P (obj_at (Q (cur_time s)) p s)\<rbrace> do_machine_op f \<lbrace>\<lambda>_ s. P (obj_at (Q (cur_time s)) p s)\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_time], wpsimp+)

lemma retype_region_obj_at_other_cur_time:
  assumes ptrv: "ptr \<notin> set (retype_addrs ptr' ty n us)"
  shows "\<lbrace>\<lambda>s. obj_at (P (cur_time s)) ptr s\<rbrace> retype_region ptr' n us ty dev \<lbrace>\<lambda>r s. obj_at (P (cur_time s)) ptr s\<rbrace>"
  using ptrv unfolding retype_region_def retype_addrs_def
  apply (simp only: foldr_upd_app_if fun_app_def K_bind_def)
  apply (wpsimp simp: obj_at_def)
  done

lemma retype_region_obj_at_other2_cur_time:
  "\<lbrace>\<lambda>s. ptr \<notin> set (retype_addrs ptr' ty n us)
       \<and> obj_at (P (cur_time s)) ptr s\<rbrace> retype_region ptr' n us ty dev \<lbrace>\<lambda>rv s. obj_at (P (cur_time s)) ptr s\<rbrace>"
  by (rule hoare_assume_pre) (wpsimp wp: retype_region_obj_at_other_cur_time)

lemma retype_region_obj_at_other3_cur_time:
  "\<lbrace>\<lambda>s. pspace_no_overlap_range_cover ptr sz s \<and> obj_at (P (cur_time s)) p s \<and> range_cover ptr sz (obj_bits_api ty us) n
           \<and> valid_objs s \<and> pspace_aligned s\<rbrace>
     retype_region ptr n us ty dev
   \<lbrace>\<lambda>rv s. obj_at (P (cur_time s)) p s\<rbrace>"
  apply (rule hoare_pre)
   apply (rule retype_region_obj_at_other2_cur_time)
  apply clarsimp
  apply (drule subsetD [rotated, OF _ retype_addrs_subset_ptr_bits])
   apply simp
  apply (drule(3) pspace_no_overlap_obj_not_in_range)
  apply (simp add: field_simps)
  done

lemma retype_region_budget_ready:
  "\<lbrace>(\<lambda>s. pspace_no_overlap (up_aligned_area ptr' sz) s \<and>
      range_cover ptr' sz (obj_bits_api ty us) n \<and>
      valid_objs s \<and> pspace_aligned s)
     and budget_ready t\<rbrace>
     retype_region ptr' n us ty dev
   \<lbrace>\<lambda>rv. budget_ready t\<rbrace>"
  apply (clarsimp simp: budget_ready_def2)
  apply (wpsimp wp: retype_region_obj_at_other3_cur_time hoare_vcg_ex_lift
                    retype_region_st_tcb_at)
  by auto

lemma cur_time_detype[simp]: "cur_time (detype S s) = cur_time s"
  by (simp add: detype_def)

lemma reset_untyped_cap_sched_context_at_cur_time:
  "\<lbrace>invs and cte_wp_at (\<lambda>cp. t \<notin> cap_range cp \<and> is_untyped_cap cp) slot
    and (\<lambda>s. obj_at (\<lambda>obj. (\<exists>sc n. (obj = SchedContext sc n) \<and> (P (cur_time s) sc))) t s)\<rbrace>
    reset_untyped_cap slot
  \<lbrace>\<lambda>_ s. obj_at (\<lambda>obj. (\<exists>sc n. (obj = SchedContext sc n) \<and> P (cur_time s) sc)) t s\<rbrace>,
             \<lbrace>\<lambda>_ s. obj_at (\<lambda>obj. (\<exists>sc n. (obj = SchedContext sc n) \<and> P (cur_time s) sc)) t s\<rbrace>"
  apply (simp add: reset_untyped_cap_def)
  apply (rule hoare_pre)
   apply (wp mapME_x_inv_wp preemption_point_inv set_cap_obj_at_impossible_cur_time
             do_machine_op_obj_at_cur_time
     | simp add: unless_def
     | solves \<open>auto simp: caps_of_def cap_of_def\<close>)+
    apply (simp add: delete_objects_def)
    apply (wp get_cap_wp hoare_vcg_const_imp_lift do_machine_op_obj_at_cur_time | simp)+
  apply (auto simp: cte_wp_at_caps_of_state cap_range_def
                    bits_of_def is_cap_simps caps_of_def cap_of_def)
  done

lemma reset_untyped_cap_budget_ready:
  "\<lbrace>invs and cte_wp_at (\<lambda>cp. t \<notin> cap_range cp \<and> is_untyped_cap cp) slot
   and (\<lambda>s. bound_sc_tcb_at (\<lambda>p. \<exists>scp. p = Some scp
      \<and> cte_wp_at (\<lambda>cp. scp \<notin> cap_range cp \<and> is_untyped_cap cp) slot s) t s)
         and budget_ready t\<rbrace>
     reset_untyped_cap slot
   \<lbrace>\<lambda>rv. budget_ready t\<rbrace>, \<lbrace>\<lambda>rv. budget_ready t::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: budget_ready_def2)
  apply (wpsimp wp: hoare_vcg_ex_lift hoare_vcg_conj_lift
      reset_untyped_cap_sched_context_at_cur_time[where P="\<lambda>x sc. r_time (refill_hd sc) \<le> x + kernelWCET_ticks", simplified]
      reset_untyped_cap_bound_sc_tcb_at)
  apply (rule_tac x=scp in exI)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma invoke_untyped_budget_ready[wp,DetSchedAux_AI_assms]:
  "\<lbrace>invs and st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t and
budget_ready t
         and ct_active and valid_untyped_inv ui\<rbrace>
     invoke_untyped ui
   \<lbrace>\<lambda>rv. \<lambda>s :: det_ext state . budget_ready t s\<rbrace>"
  apply (rule hoare_pre, rule invoke_untyped_Q,
    (wp init_arch_objects_wps | simp)+)
     apply (rule hoare_name_pre_state, clarsimp)
     apply (wp retype_region_budget_ready, auto)[1]
    apply (wp reset_untyped_cap_st_tcb_at reset_untyped_cap_budget_ready | simp)+
  apply (cases ui, clarsimp)
  apply (frule(1) st_tcb_ex_cap[OF _ invs_iflive])
   apply (clarsimp split: Structures_A.thread_state.splits)
  apply (drule ex_nonz_cap_to_overlap,
    ((simp add:cte_wp_at_caps_of_state
            is_cap_simps descendants_range_def2
            empty_descendants_range_in)+))
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (subgoal_tac "ex_nonz_cap_to scp s")
   apply (drule ex_nonz_cap_to_overlap,
      ((simp add:cte_wp_at_caps_of_state
          is_cap_simps descendants_range_def2
          empty_descendants_range_in)+)[5])
  apply (frule invs_sym_refs)
  apply (drule (2) sym_ref_tcb_sc)
  apply clarsimp
  apply (frule invs_iflive)
  apply (erule (1) if_live_then_nonz_capD2)
  apply (clarsimp simp: live_def live_sc_def)
  done

crunch valid_blocked[wp, DetSchedAux_AI_assms]:
  init_arch_objects "valid_blocked::det_ext state \<Rightarrow> _"
  (wp: valid_blocked_lift set_cap_typ_at)

crunch ct[wp, DetSchedAux_AI_assms]: invoke_untyped "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps do_machine_op_def detype_def mapM_x_defsym
   ignore: freeMemory)

crunch ready_queues[wp, DetSchedAux_AI_assms]:
  invoke_untyped "\<lambda>s :: det_ext state. P (ready_queues s)"
  (wp: crunch_wps
   simp: detype_def wrap_ext_det_ext_ext_def mapM_x_defsym
   ignore: freeMemory)

crunch release_queue[wp, DetSchedAux_AI_assms]:
  invoke_untyped "\<lambda>s :: det_ext state. P (release_queue s)"
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

lemma test_sc_refill_max_detype[simp]:
  "(test_sc_refill_max t (detype S s))
    = (test_sc_refill_max t s \<and> t \<notin> S)"
  by (clarsimp simp add: test_sc_refill_max_def detype_def)

lemma test_sc_refill_max_clear_um[iff]:
  "test_sc_refill_max t (clear_um S s) = test_sc_refill_max t s"
  by (simp add: clear_um_def test_sc_refill_max_def)

lemma active_sc_tcb_at_detype[simp]:
  "(active_sc_tcb_at t (detype S s))
    = (active_sc_tcb_at t s \<and> t \<notin> S
          \<and> bound_sc_tcb_at (\<lambda>p. \<exists>scp.  p = Some scp \<and> scp \<notin> S) t s)"
  apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def)
  apply (rule iffI; fastforce)
  done

lemma active_sc_tcb_at_clear_um[iff]:
  "active_sc_tcb_at t (clear_um S s) = active_sc_tcb_at t s"
  by (simp add: active_sc_tcb_at_def)

lemma perform_asid_control_invocation_active_sc_tcb_at:
  "\<lbrace>st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t and active_sc_tcb_at t
    and ct_active and invs and valid_aci aci\<rbrace>
    perform_asid_control_invocation aci
  \<lbrace>\<lambda>_. active_sc_tcb_at t :: det_ext state \<Rightarrow> _\<rbrace>"
  including no_pre
  apply (clarsimp simp: perform_asid_control_invocation_def split: asid_control_invocation.splits)
  apply (rename_tac word1 a b aa ba word2)
  apply (wp hoare_vcg_const_imp_lift retype_region_st_tcb_at retype_region_active_sc_tcb_at
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
      apply ((simp add:page_bits_def word_bits_def pageBits_def word_size_bits_def)+)[3]
   apply wp
  apply (clarsimp simp: valid_aci_def)
  apply (frule intvl_range_conv)
   apply (simp add:word_bits_def page_bits_def pageBits_def)
  apply (clarsimp simp:detype_clear_um_independent page_bits_def)
  apply (rule conjI)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (rule pspace_no_overlap_detype)
     apply (rule caps_of_state_valid_cap)
      apply (simp add:page_bits_def)+
    apply (simp add:invs_valid_objs invs_psp_aligned)+
  apply_trace (clarsimp simp:obj_bits_api_def arch_kobj_size_def cte_wp_at_caps_of_state
    default_arch_object_def empty_descendants_range_in)
  apply (frule_tac cap = "(cap.UntypedCap False word1 pageBits idx)"
    in detype_invariants[rotated 3],clarsimp+)
    apply (simp add:cte_wp_at_caps_of_state
      empty_descendants_range_in descendants_range_def2)+
  apply (thin_tac "x = Some cap.NullCap" for x)+
  apply (frule(1) caps_of_state_valid_cap[OF _ invs_valid_objs])
  apply (intro conjI)
    apply (clarsimp simp:valid_cap_def cap_aligned_def range_cover_full
     invs_psp_aligned invs_valid_objs page_bits_def)
   apply (frule pspace_no_overlap_detype)
  apply (auto simp:page_bits_def detype_clear_um_independent)[4]

   apply (frule st_tcb_ex_cap)
     apply clarsimp
    apply (clarsimp split: Structures_A.thread_state.splits)
   apply (clarsimp simp: ex_nonz_cap_to_def)
   apply (frule invs_untyped_children)
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (rotate_tac -3)
   apply (erule_tac ptr="(aa,ba)" in
          untyped_children_in_mdbE[where P="\<lambda>c. t \<in> zobj_refs c" for t])
       apply (simp add: cte_wp_at_caps_of_state)+
      apply fastforce
    apply (clarsimp simp: zobj_refs_to_obj_refs)
    apply (fastforce simp:page_bits_def)
   apply simp
  apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def)
   apply (subgoal_tac "ex_nonz_cap_to scp sa")
   apply (clarsimp simp: ex_nonz_cap_to_def)
   apply (frule invs_untyped_children)
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (rotate_tac -3)
   apply (erule_tac ptr="(aa,ba)" in
          untyped_children_in_mdbE[where P="\<lambda>c. t \<in> zobj_refs c" for t])
       apply (simp add: cte_wp_at_caps_of_state)+
      apply fastforce
    apply (clarsimp simp: zobj_refs_to_obj_refs)
    apply (fastforce simp:page_bits_def)
   apply simp
  apply (frule invs_iflive)
  apply (frule invs_sym_refs)
  apply (drule (2) sym_ref_tcb_sc, clarsimp)
  apply (erule_tac p=scp in if_live_then_nonz_capD2)
   by (simp add: live_def live_sc_def)+

lemma perform_asid_control_invocation_budget_sufficient:
  "\<lbrace>st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t and
 budget_sufficient t
(*    and ct_active and invs and valid_aci aci*)\<rbrace>
    perform_asid_control_invocation aci
  \<lbrace>\<lambda>_. budget_sufficient t :: det_ext state \<Rightarrow> _\<rbrace>"
  including no_pre
  apply (clarsimp simp: perform_asid_control_invocation_def split: asid_control_invocation.splits)
  apply (rename_tac word1 a b aa ba word2)
  apply (wp hoare_vcg_const_imp_lift retype_region_st_tcb_at set_cap_no_overlap|simp)+
sorry

lemma perform_asid_control_invocation_budget_ready:
  "\<lbrace>st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t and
 budget_ready t
(*    and ct_active and invs and valid_aci aci*)\<rbrace>
    perform_asid_control_invocation aci
  \<lbrace>\<lambda>_. budget_ready t :: det_ext state \<Rightarrow> _\<rbrace>"
  including no_pre
  apply (clarsimp simp: perform_asid_control_invocation_def split: asid_control_invocation.splits)
  apply (rename_tac word1 a b aa ba word2)
  apply (wp hoare_vcg_const_imp_lift retype_region_st_tcb_at set_cap_no_overlap|simp)+
sorry

lemma perform_asid_control_invocation_budget_sufficient_neg:
  "\<lbrace>st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t and
 (\<lambda>s. \<not> budget_sufficient t s)
(*    and ct_active and invs and valid_aci aci*)\<rbrace>
    perform_asid_control_invocation aci
  \<lbrace>\<lambda>_ s:: det_ext state. \<not> budget_sufficient t s\<rbrace>"
  including no_pre
  apply (clarsimp simp: perform_asid_control_invocation_def split: asid_control_invocation.splits)
  apply (rename_tac word1 a b aa ba word2)
  apply (wp hoare_vcg_const_imp_lift retype_region_st_tcb_at set_cap_no_overlap|simp)+
sorry

lemma perform_asid_control_invocation_budget_ready_neg:
  "\<lbrace>st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t and
 (\<lambda>s. \<not> budget_ready t s)
(*    and ct_active and invs and valid_aci aci*)\<rbrace>
    perform_asid_control_invocation aci
  \<lbrace>\<lambda>_ s :: det_ext state. \<not> budget_ready t s\<rbrace>"
  including no_pre
  apply (clarsimp simp: perform_asid_control_invocation_def split: asid_control_invocation.splits)
  apply (rename_tac word1 a b aa ba word2)
  apply (wp hoare_vcg_const_imp_lift retype_region_st_tcb_at set_cap_no_overlap|simp)+
sorry

crunches perform_asid_control_invocation
for ct[wp]: "\<lambda>s. P (cur_thread s)"
and idle_thread[wp]: "\<lambda>s::det_ext state. P (idle_thread s)"
and valid_blocked[wp]: "valid_blocked::det_state \<Rightarrow> _"
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
         apply (wpsimp wp: perform_asid_control_etcb_at
                           perform_asid_control_invocation_budget_sufficient
                           perform_asid_control_invocation_budget_ready
                           perform_asid_control_invocation_budget_sufficient_neg
                           perform_asid_control_invocation_budget_ready_neg
                           perform_asid_control_invocation_active_sc_tcb_at)+
    apply (rule hoare_strengthen_post, rule aci_invs)
    apply (simp add: invs_def valid_state_def)
   apply (rule hoare_lift_Pf[where f="\<lambda>s. scheduler_action s"])
    apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_domain s"])
     apply (rule hoare_lift_Pf[where f="\<lambda>s. idle_thread s"])
     apply (rule hoare_lift_Pf[where f="\<lambda>s. release_queue s"])
      apply wp+
  apply simp
  done

crunch valid_ready_qs[wp]: init_arch_objects "valid_ready_qs :: det_ext state \<Rightarrow> _"
  (wp: valid_ready_qs_lift crunch_wps)

lemma set_pt_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at t\<rbrace> set_pt ptr val \<lbrace>\<lambda>_. active_sc_tcb_at t\<rbrace>"
  apply (simp add: set_pt_def set_object_def)
  apply (wpsimp wp: get_object_wp)
  apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def)
  apply (case_tac "t=ptr"; clarsimp simp: )
  apply (rule_tac x=scp in exI, clarsimp split: kernel_object.splits)
  done

lemma set_asid_pool_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at t\<rbrace> set_asid_pool ptr val \<lbrace>\<lambda>_. active_sc_tcb_at t\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wpsimp wp: get_object_wp)
  apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def)
  apply (case_tac "t=ptr"; clarsimp)
  apply (rule_tac x=scp in exI, clarsimp split: kernel_object.splits)
  done

crunch active_sc_tcb_at[wp]: init_arch_objects "active_sc_tcb_at t"
  (wp: crunch_wps ignore: do_machine_op)

lemma set_pt_budget_ready[wp]:
  "\<lbrace>budget_ready t\<rbrace> set_pt ptr val \<lbrace>\<lambda>_. budget_ready t\<rbrace>"
  apply (simp add: set_pt_def set_object_def)
  apply (wpsimp wp: get_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def)
  apply (case_tac "t=ptr"; clarsimp simp: )
  apply (rule_tac x=scp in exI, clarsimp split: kernel_object.splits)
  done

lemma set_asid_pool_budget_ready[wp]:
  "\<lbrace>budget_ready t\<rbrace> set_asid_pool ptr val \<lbrace>\<lambda>_. budget_ready t\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wpsimp wp: get_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def)
  apply (case_tac "t=ptr"; clarsimp)
  apply (rule_tac x=scp in exI, clarsimp split: kernel_object.splits)
  done

lemma set_pt_budget_sufficient[wp]:
  "\<lbrace>budget_sufficient t\<rbrace> set_pt ptr val \<lbrace>\<lambda>_. budget_sufficient t\<rbrace>"
  apply (simp add: set_pt_def set_object_def)
  apply (wpsimp wp: get_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def)
  apply (case_tac "t=ptr"; clarsimp simp: )
  apply (rule_tac x=scp in exI, clarsimp split: kernel_object.splits)
  done

lemma set_asid_pool_budget_sufficient[wp]:
  "\<lbrace>budget_sufficient t\<rbrace> set_asid_pool ptr val \<lbrace>\<lambda>_. budget_sufficient t\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wpsimp wp: get_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def)
  apply (case_tac "t=ptr"; clarsimp)
  apply (rule_tac x=scp in exI, clarsimp split: kernel_object.splits)
  done

crunch valid_sched_action[wp]: init_arch_objects "valid_sched_action :: det_ext state \<Rightarrow> _"
  (wp: valid_sched_action_lift)

crunch valid_sched[wp]: init_arch_objects "valid_sched :: det_ext state \<Rightarrow> _"
  (wp: valid_sched_lift crunch_wps)

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
