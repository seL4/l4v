(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory DetSchedAux_AI
imports DetSchedInvs_AI
begin

arch_requalify_facts
  init_arch_objects_typ_at
  init_arch_objects_pred_tcb_at
  init_arch_objects_cur_thread

lemmas [wp] =
  init_arch_objects_typ_at
  init_arch_objects_pred_tcb_at
  init_arch_objects_cur_thread

lemma set_cap_etcbs[wp]:
  "set_cap p c \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_cap_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (auto simp: obj_at_def etcbs_of'_def etcb_of_def elim!: rsubst[where P=P])
  done

crunch update_cdt_list, create_cap, cap_insert
  for etcbs[wp]: "\<lambda>s. P (etcbs_of s)"
  and rqueues[wp]: "\<lambda>s. P (ready_queues s)"
  and schedact[wp]: "\<lambda>s. P (scheduler_action s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and ct[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps dxo_wp_weak)

crunch create_cap, cap_insert
  for valid_queues[wp]: valid_queues
  (wp: valid_queues_lift)

lemma typ_at_pred_tcb_at_lift:
  assumes typ_lift: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>r s. P (typ_at T p s)\<rbrace>"
  assumes pred_lift: "\<And>P. \<lbrace>pred_tcb_at proj P t\<rbrace> f \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<not> pred_tcb_at proj P t s\<rbrace> f \<lbrace>\<lambda>r s. \<not> pred_tcb_at proj P t s\<rbrace>"

  apply (simp add: valid_def obj_at_def pred_tcb_at_def)
  apply clarsimp
  apply (case_tac "kheap s t")
   apply (cut_tac P="\<lambda>x. \<not> x" and p=t and T="ATCB" in typ_lift)
   apply (simp add: valid_def obj_at_def)
   apply force
  apply (cut_tac P="\<lambda>x. x" and p=t and T="a_type aa" in typ_lift)
  apply (cut_tac P="\<lambda>t. \<not> P t" in pred_lift)
  apply (simp add: valid_def obj_at_def pred_tcb_at_def)
  apply (drule_tac x=s in spec)
  apply simp
  apply (drule_tac x="(a,b)" in bspec)
   apply simp
  apply simp
  apply (subgoal_tac "a_type aa = ATCB")
   apply (erule a_type_ATCBE)
   apply simp
   apply force
  apply simp
  done


lemma create_cap_no_pred_tcb_at: "\<lbrace>\<lambda>s. \<not> pred_tcb_at proj P t s\<rbrace>
          create_cap apiobject_type nat' prod'' dev x
          \<lbrace>\<lambda>r s. \<not> pred_tcb_at proj P t s\<rbrace>"
  by (rule typ_at_pred_tcb_at_lift; wp)

lemma cap_insert_no_pred_tcb_at:
  "\<lbrace>\<lambda>s. \<not> pred_tcb_at proj P t s\<rbrace>
     cap_insert cap src dest
   \<lbrace>\<lambda>r s. \<not> pred_tcb_at proj P t s\<rbrace>"
  by (rule typ_at_pred_tcb_at_lift; wp)


\<comment> \<open>FIXME: can some of these be removed\<close>
locale DetSchedAux_AI =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes init_arch_objects_idle_thread[wp]:
    "\<And>t d r n sz refs P. init_arch_objects t d r n sz refs \<lbrace>\<lambda>s::'state_ext state. P (idle_thread s)\<rbrace>"
  assumes init_arch_objects_etcbs_of[wp]:
    "\<And>t d r n sz refs P.
      init_arch_objects t d r n sz refs \<lbrace>\<lambda>s::'state_ext state. P (etcbs_of s)\<rbrace>"
  assumes init_arch_objects_valid_blocked[wp]:
    "\<And>t d r n sz refs. init_arch_objects t d r n sz refs \<lbrace>valid_blocked :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes init_arch_objects_cur_domain[wp]:
    "\<And>t d r n sz refs P. init_arch_objects t d r n sz refs \<lbrace>\<lambda>s::'state_ext state. P (cur_domain s)\<rbrace>"
  assumes init_arch_objects_ready_queues[wp]:
    "\<And>t d r n sz refs P. init_arch_objects t d r n sz refs \<lbrace>\<lambda>s::'state_ext state. P (ready_queues s)\<rbrace>"
  assumes init_arch_objects_scheduler_action[wp]:
    "\<And>t d r n sz refs P. init_arch_objects t d r n sz refs \<lbrace>\<lambda>s::'state_ext state. P (scheduler_action s)\<rbrace>"

lemmas mapM_x_defsym = mapM_x_def[symmetric]

lemma delete_objects_etcb_at[wp]:
  "delete_objects a b \<lbrace>\<lambda>s. etcb_at P t s\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (wpsimp simp: detype_def)
  apply (auto simp: detype_def etcbs_of'_def etcb_at'_def)
  done

crunch reset_untyped_cap
  for etcb_at[wp]: "etcb_at P t"
  (wp: preemption_point_inv mapME_x_inv_wp crunch_wps)

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

crunch do_machine_op
  for ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"

context DetSchedAux_AI begin

crunch invoke_untyped
  for ready_queues[wp]: "\<lambda>s::'state_ext state. P (ready_queues s)"
  and scheduler_action[wp]: "\<lambda>s::'state_ext state. P (scheduler_action s)"
  and cur_domain[wp]: "\<lambda>s::'state_ext state. P (cur_domain s)"
  and idle_thread[wp]: "\<lambda>s::'state_ext state. P (idle_thread s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv
   simp: detype_def crunch_simps mapM_x_defsym)

lemma invoke_untyped_etcb_at:
  "\<lbrace>etcb_at P t\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>_ s::'state_ext state. st_tcb_at (Not o inactive) t s \<longrightarrow> etcb_at P t s\<rbrace>"
  apply (cases ui)
  apply (simp add: mapM_x_def[symmetric] invoke_untyped_def)
  apply (wpsimp wp: mapM_x_wp'
                    create_cap_no_pred_tcb_at typ_at_pred_tcb_at_lift
                    hoare_convert_imp[OF create_cap_no_pred_tcb_at]
                    hoare_convert_imp[OF _ init_arch_objects_etcbs_of]
                    hoare_drop_impE_E)
  done

end

crunch create_cap,cap_insert,set_cap
  for valid_blocked[wp]: valid_blocked
  (wp: valid_blocked_lift set_cap_typ_at)

lemma valid_blocked_fold_update:
  "\<lbrakk> valid_blocked_2 queues kh sa ct; type \<noteq> apiobject_type.Untyped \<rbrakk> \<Longrightarrow>
   valid_blocked_2 queues (foldr (\<lambda>p kh. kh(p \<mapsto> default_object type dev o_bits d)) ptrs kh) sa ct"
  apply (induct ptrs)
   apply simp
  apply (case_tac type)
       apply simp
      apply (clarsimp,
             clarsimp simp: valid_blocked_def st_tcb_at_kh_def obj_at_kh_def obj_at_def
                            default_object_def default_tcb_def)+
  done

lemma retype_region_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> retype_region a b c d dev \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: retype_region_def)
  apply wp
  apply (clarsimp simp del: fun_upd_apply)
  apply (blast intro: valid_blocked_fold_update)
  done

lemma delete_objects_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> delete_objects a b \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (wpsimp simp: detype_def do_machine_op_def)
  apply (simp add: valid_blocked_def st_tcb_at_kh_def obj_at_kh_def obj_at_def is_etcb_at_def)
  done

crunch reset_untyped_cap
  for valid_blocked[wp]: "valid_blocked"
  (wp: preemption_point_inv mapME_x_inv_wp crunch_wps
   simp: unless_def)

context DetSchedAux_AI begin

crunch invoke_untyped
  for valid_blocked[wp]: "valid_blocked :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps simp: mapM_x_defsym crunch_simps)

end

lemma st_tcb_at_is_etcb:
  "st_tcb_at P t s \<Longrightarrow> is_etcb_at' t (etcbs_of s)"
  by (auto simp: etcbs_of'_def is_etcb_at'_def st_tcb_at_def obj_at_def)

(*Leverages the fact that retype only clears out inactive tcbs under
  the invariants*)
lemma valid_sched_tcb_state_preservation:
  assumes st_tcb: "\<And>P t. \<lbrace>I and ct_active and st_tcb_at (P and Not o inactive and Not o idle) t\<rbrace> f \<lbrace>\<lambda>_.st_tcb_at P t\<rbrace>"
  assumes stuff: "\<And>P t. \<lbrace>(\<lambda>s. etcb_at P t s)\<rbrace> f \<lbrace>\<lambda>r s. st_tcb_at (Not o inactive) t s \<longrightarrow> etcb_at P t s\<rbrace>"
  assumes cur_thread: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>r s. P (cur_thread s)\<rbrace>"
  assumes idle_thread: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>r s. P (idle_thread s)\<rbrace>"
  assumes valid_blocked: "\<lbrace>valid_blocked\<rbrace> f \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  assumes valid_idle: "\<lbrace>I\<rbrace> f \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  assumes valid_others: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) (ready_queues s) (cur_domain s)\<rbrace> f \<lbrace>\<lambda>r s. P (scheduler_action s) (ready_queues s) (cur_domain s)\<rbrace>"
  shows "\<lbrace>I and ct_active and valid_sched and valid_idle\<rbrace> f \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp add: valid_sched_def valid_def)
  apply (frule(1) use_valid[OF _ valid_blocked])
  apply simp
  apply (frule_tac P1="\<lambda>sa rq cdom. rq = ready_queues s \<and> sa = scheduler_action s \<and> cdom = cur_domain s" in use_valid[OF _ valid_others])
   apply simp
  apply (rule conjI)
   apply (clarsimp simp add: valid_queues_def)
   apply (drule_tac x=d in spec)
   apply (drule_tac x=p in spec)
   apply clarsimp
   apply (drule_tac x=t in bspec)
    apply simp
   apply clarsimp
   apply (subgoal_tac "st_tcb_at runnable t b")
    apply simp
    apply (rule conjI)
     apply (fastforce simp: st_tcb_at_is_etcb)
    apply (frule_tac P1="\<lambda>t. etcb_priority t = p \<and> etcb_domain t = d" and t1=t in use_valid[OF _ stuff])
     apply simp
    apply (simp add: pred_tcb_at_def obj_at_def)
    apply force
   apply (rule_tac use_valid[OF _ st_tcb],assumption)
   apply simp
   apply (erule pred_tcb_weakenE)
   apply simp
   apply (case_tac "itcb_state tcb")
          apply simp+
  apply (frule_tac P1="\<lambda>ct. ct = (cur_thread s)" in use_valid[OF _ cur_thread])
   apply simp
  apply (rule conjI)
   apply simp
  apply simp
  apply (clarsimp simp add: valid_sched_action_def is_activatable_def weak_valid_sched_action_def)
  apply (rule conjI)
   apply clarsimp
   apply (frule_tac P1="active" and t1="cur_thread s" in use_valid[OF _ st_tcb])
    apply (simp add: ct_in_state_def)
    apply (erule pred_tcb_weakenE)
    apply simp
    apply (case_tac "itcb_state tcb"; simp)
   apply (erule pred_tcb_weakenE)
   apply (case_tac "itcb_state tcb"; simp)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac use_valid[OF _ st_tcb],assumption)
   apply simp
  apply (erule pred_tcb_weakenE)
   apply simp
   apply (case_tac "itcb_state tcb", simp+)
  apply (rule conjI)
   apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def)
   apply (rule use_valid[OF _ stuff, rule_format], assumption)
    apply simp
   apply (rule use_valid[OF _ st_tcb], assumption)
   apply simp
   apply (erule st_tcb_weakenE)
   apply (case_tac st, simp+)
  apply (clarsimp simp: ct_in_cur_domain_2_def in_cur_domain_2_def)
  apply (frule_tac P1="\<lambda>idle. idle = (idle_thread s)" in use_valid[OF _ idle_thread], simp)
  apply (rule conjI)
   apply (rule impI)
   apply (simp, erule disjE, simp)
   apply (frule_tac P1="\<lambda>t. etcb_domain t = cur_domain s" and t1="cur_thread s" in use_valid[OF _ stuff])
    apply (clarsimp simp: etcb_at_def split: option.splits)
   apply clarsimp
   apply (erule notE, rule use_valid[OF _ st_tcb],assumption)
   apply (simp add: ct_in_state_def)
   apply (erule st_tcb_weakenE)
   apply simp
   apply (case_tac st, simp+)
  apply(frule (1) use_valid[OF _ valid_idle])
  apply(simp add: valid_idle_etcb_def)
  apply(frule use_valid[OF _ stuff[where t=idle_thread_ptr]])
   apply simp
  apply(erule mp)
  apply(fastforce simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma valid_idle_etcb_lift:
  assumes "\<And>P t. \<lbrace>\<lambda>s. etcb_at P t s\<rbrace> f \<lbrace>\<lambda>r s. etcb_at P t s\<rbrace>"
  shows "\<lbrace>valid_idle_etcb\<rbrace> f \<lbrace>\<lambda>r. valid_idle_etcb\<rbrace>"
  apply(simp add: valid_idle_etcb_def)
  apply(wp assms)
  done

crunch invoke_untyped
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv
   simp: crunch_simps mapM_x_defsym)

context DetSchedAux_AI begin

lemma invoke_untyped_valid_sched:
  "\<lbrace>invs and valid_untyped_inv ui and ct_active and valid_sched and valid_idle \<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>_ . valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_pre)
   apply (rule_tac I="invs and valid_untyped_inv ui and ct_active"
                in valid_sched_tcb_state_preservation)
          apply (wpsimp wp: invoke_untyped_st_tcb_at invoke_untyped_etcb_at)+
     apply (rule hoare_strengthen_postE, rule invoke_untyp_invs; simp add: invs_valid_idle)
    apply simp
   apply (rule_tac f="\<lambda>s. P (scheduler_action s)" in hoare_lift_Pf)
    apply (rule_tac f="\<lambda>s. x (ready_queues s)" in hoare_lift_Pf)
     apply wp+
  apply simp+
  done

end

lemmas hoare_imp_lift_something = hoare_convert_imp

crunch create_cap,cap_insert
  for valid_sched_action[wp]: valid_sched_action
  (wp: valid_sched_action_lift)

crunch create_cap,cap_insert
  for valid_sched[wp]: valid_sched
  (wp: valid_sched_lift)

crunch thread_set_time_slice, dec_domain_time
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"

crunch get_tcb_queue
  for inv[wp]: "\<lambda>s. P s"

end
