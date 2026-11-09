(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory IpcCancel_R
imports
  Reply_R
  "Lib.SimpStrategy"
begin

arch_requalify_consts (H) prepareThreadDelete

arch_requalify_facts
  asUser_sym_heap_sched_pointers (* free type variable *)

lemmas [wp] = asUser_sym_heap_sched_pointers

defs capHasProperty_def:
  "capHasProperty ptr P \<equiv> cte_wp_at' (\<lambda>c. P (cteCap c)) ptr"

(* FIXME: move *)
lemma when_fail_assert:
  "when P fail = assert (\<not>P)"
  by (simp add: when_def assert_def)

(* FIXME: move *)
lemma opt_case_when:
  "(case x of None \<Rightarrow> return () | Some (c, _) \<Rightarrow> when (c = v) f) =
   when (\<exists>a. x = Some (v, a)) f"
  by (cases x) (auto simp add: split_def)

(* FIXME: move *)
lemma imp_drop_strg:
  "Q \<Longrightarrow> P \<longrightarrow> Q"
  by simp

lemma tcb_ko_at':
  "tcb_at' t s \<Longrightarrow> \<exists>ta::tcb. ko_at' ta t s"
  by (clarsimp simp: obj_at'_def)

lemmas corresK_as_user' =
  asUser_corres'[atomized, THEN corresK_lift_rule, THEN mp]

lemmas setEndpoint_ko_wp_at'
    = setObject_ko_wp_at'[where 'a=endpoint, folded setEndpoint_def, simplified]

crunch updateEndpoint, updateNotification, tcbNTFNDequeue, tcbNTFNAppend, tcbEPDequeue, tcbEPAppend,
       removeAndRestartEPQueuedThread, removeAndRestartNTFNQueuedThread,
       cancelBadgedSends, cancelAllSignals, cancelAllIPC, cancelIPC, cancelSignal
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps)

global_interpretation updateEndpoint: gen_typ_at_all_props' "updateEndpoint epPtr f"
  by typ_at_props'

global_interpretation updateNotification: gen_typ_at_all_props' "updateNotification ntfnPtr f"
  by typ_at_props'

global_interpretation tcbNTFNDequeue: gen_typ_at_all_props' "tcbNTFNDequeue tcbPtr ntfnPtr"
  by typ_at_props'

global_interpretation tcbNTFNAppend: gen_typ_at_all_props' "tcbNTFNAppend tcbPtr ntfnPtr"
  by typ_at_props'

global_interpretation tcbEPDequeue: gen_typ_at_all_props' "tcbEPDequeue tcbPtr epPtr"
  by typ_at_props'

global_interpretation tcbEPAppend: gen_typ_at_all_props' "tcbEPAppend tcbPtr epPtr state"
  by typ_at_props'

global_interpretation tcbQueueRemove: gen_typ_at_all_props' "tcbQueueRemove queue tcbPtr"
  by typ_at_props'

global_interpretation removeAndRestartEPQueuedThread:
  gen_typ_at_all_props' "removeAndRestartEPQueuedThread t epptr"
  by typ_at_props'

global_interpretation removeAndRestartNTFNQueuedThread:
  gen_typ_at_all_props' "removeAndRestartNTFNQueuedThread t ntfnPtr"
  by typ_at_props'

global_interpretation removeAndRestartBadgedThread:
  gen_typ_at_all_props' "removeAndRestartBadgedThread t epptr badge"
  by typ_at_props'

global_interpretation cancelBadgedSends: gen_typ_at_all_props' "cancelBadgedSends epptr badge"
  by typ_at_props'

global_interpretation cancelAllSignals: gen_typ_at_all_props' "cancelAllSignals ntfnPtr"
  by typ_at_props'

global_interpretation cancelAllIPC: gen_typ_at_all_props' "cancelAllIPC epptr"
  by typ_at_props'

global_interpretation cancelIPC: gen_typ_at_all_props' "cancelIPC tptr"
  by typ_at_props'

global_interpretation cancelSignal: gen_typ_at_all_props' "cancelSignal threadPtr ntfnPtr"
  by typ_at_props'

(* FIXME RT: remove *)
declare if_weak_cong [cong]

crunch cancelAllIPC, cancelAllSignals
  for aligned'[wp]: pspace_aligned'
  and distinct'[wp]: pspace_distinct'
  (wp: crunch_wps)

crunch tcbNTFNDequeue, tcbNTFNAppend, tcbEPDequeue, tcbEPAppend
  for pred_tcb_at'[wp]: "\<lambda>s. Q (pred_tcb_at' proj P t s)"
  (wp: crunch_wps)

lemma cancelSignal_st_tcb_at'_cases:
  "\<lbrace>\<lambda>s. (t = t' \<longrightarrow> Q (P Inactive)) \<and> (t \<noteq> t' \<longrightarrow> Q (st_tcb_at' P t s))\<rbrace>
   cancelSignal t' n
   \<lbrace>\<lambda>_ s. Q (st_tcb_at' P t s)\<rbrace>"
  unfolding cancelSignal_def replyRemoveTCB_def
  by (wpsimp wp: sts_st_tcb_at'_cases_strong getNotification_wp hoare_vcg_imp_lift')

lemma cancelSignal_simple[wp]:
  "\<lbrace>\<top>\<rbrace> cancelSignal t ntfn \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  by (wpsimp wp: cancelSignal_st_tcb_at'_cases)

lemma cancelSignal_pred_tcb_at':
  "\<lbrace>pred_tcb_at' proj P t' and K (t \<noteq> t')\<rbrace>
   cancelSignal t ntfnptr
   \<lbrace>\<lambda>rv. pred_tcb_at' proj P t'\<rbrace>"
  unfolding cancelSignal_def
  by (wpsimp wp: sts_pred_tcb_neq' getNotification_wp)

crunch cancelIPC, cancelSignal
  (* FIXME RT: VER-1016 *)
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps)

lemma blockedCancelIPC_st_tcb_at:
  "\<lbrace>\<lambda>s. (t = t' \<longrightarrow> Q (P Inactive)) \<and> (t \<noteq> t' \<longrightarrow> Q (st_tcb_at' P t s))\<rbrace>
   blockedCancelIPC st t' rptr
   \<lbrace>\<lambda>_ s. Q (st_tcb_at' P t s)\<rbrace>"
  unfolding blockedCancelIPC_def getBlockingObject_def
  by (wpsimp wp: sts_st_tcb_at'_cases_strong replyUnlink_st_tcb_at' getEndpoint_wp hoare_vcg_imp_lift')

lemma cancelIPC_st_tcb_at':
  "\<lbrace>\<lambda>s. if t' = t \<and> st_tcb_at' (\<lambda>st. st \<notin> {Running, Restart, IdleThreadState}) t' s
        then P (P' Inactive)
        else P (st_tcb_at' P' t' s)\<rbrace>
   cancelIPC t
   \<lbrace>\<lambda>rv s. P (st_tcb_at' P' t' s)\<rbrace>"
  unfolding cancelIPC_def
  apply (wpsimp wp: blockedCancelIPC_st_tcb_at replyRemoveTCB_st_tcb_at'_cases
                    cancelSignal_st_tcb_at'_cases threadSet_pred_tcb_no_state gts_wp')
  apply (auto simp: pred_tcb_at'_def obj_at'_def split: if_splits)
  done

lemma cancelIPC_simple[wp]:
  "\<lbrace>\<top>\<rbrace> cancelIPC t \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  unfolding cancelIPC_def blockedCancelIPC_def
  apply (wpsimp wp: setThreadState_st_tcb gts_wp' threadSet_wp
              simp: Let_def tcb_obj_at'_pred_tcb'_set_obj'_iff)
  apply (clarsimp simp: st_tcb_at'_def o_def obj_at'_def isBlockedOnReply_def)
  done

lemma cancelIPC_st_tcb_at'_different_thread:
  "\<lbrace>\<lambda>s. P (st_tcb_at' st t' s) \<and> t \<noteq> t'\<rbrace> cancelIPC t \<lbrace>\<lambda>rv s. P (st_tcb_at' st t' s)\<rbrace>"
  by (wpsimp wp: cancelIPC_st_tcb_at')

(* Assume various facts about cteDeleteOne, proved in Finalise_R *)
locale delete_one_conc_pre =
  assumes delete_one_st_tcb_at:
    "\<And>P. (\<And>st. simple' st \<longrightarrow> P st) \<Longrightarrow>
     \<lbrace>st_tcb_at' P t\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  assumes delete_one_typ_at[wp]:
    "\<And>P. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  assumes delete_one_sc_at'_n[wp]:
    "\<And>P. cteDeleteOne slot \<lbrace>\<lambda>s. P (sc_at'_n n p s)\<rbrace>"
  assumes delete_one_aligned:
    "\<lbrace>pspace_aligned'\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  assumes delete_one_distinct:
    "\<lbrace>pspace_distinct'\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  assumes delete_one_it:
    "\<And>P. \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> cteDeleteOne cap \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
  assumes delete_one_ksCurDomain:
    "\<And>P. \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> cteDeleteOne sl \<lbrace>\<lambda>_ s. P (ksCurDomain s)\<rbrace>"
  assumes delete_one_tcbDomain_obj_at':
    "\<And>P. \<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"

lemma cancelSignal_st_tcb_at':
  "\<lbrace>K (P Inactive)\<rbrace>
   cancelSignal t ntfn
   \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  unfolding cancelSignal_def Let_def
  apply (rule hoare_gen_asm_single)
  apply (wpsimp wp: setThreadState_st_tcb_at'_cases)
  done

sublocale delete_one_conc_pre \<subseteq> delete_one: gen_typ_at_all_props' "cteDeleteOne slot"
  by typ_at_props'

declare delete_remove1[simp]
declare delete.simps[simp del]

lemma sch_act_wf_weak_sch_act_wf[elim!]:
  "sch_act_wf (ksSchedulerAction s) s \<Longrightarrow> weak_sch_act_wf (ksSchedulerAction s) s"
  by (clarsimp simp: weak_sch_act_wf_def)

lemma replyUnlink_corres:
  "corres dc
     (valid_tcbs and pspace_aligned and pspace_distinct
      and st_tcb_at (\<lambda>st. \<exists>ep pl. st = Structures_A.BlockedOnReceive ep (Some rp) pl
                                  \<or> st = Structures_A.BlockedOnReply rp) t
      and reply_tcb_reply_at ((=) (Some t)) rp)
     valid_tcbs'
     (reply_unlink_tcb t rp) (replyUnlink rp t)"
  apply add_pspace_adb'
  apply (rule_tac Q'="st_tcb_at' (\<lambda>st. (\<exists>ep pl. st = BlockedOnReceive
                                                       ep (receiver_can_grant pl) (Some rp))
                                                \<or> st = BlockedOnReply (Some rp)) t
                      and reply_at' rp"
               in corres_cross_add_guard)
   apply clarsimp
   apply (drule (1) st_tcb_at_coerce_concrete; clarsimp simp: state_relation_def)
   apply (rule conjI)
    apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
   apply (fastforce intro!: reply_at_cross simp: reply_tcb_reply_at_def obj_at_def is_reply_def)
  apply (simp add: reply_unlink_tcb_def replyUnlink_def liftM_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF get_reply_corres])
      apply (rule corres_assert_gen_asm_l)
      apply (rename_tac reply'; prop_tac "replyTCB reply' = Some t")
       apply (clarsimp simp: reply_relation_def)
      apply simp
      apply (rule corres_split[OF getThreadState_corres])
        apply (rule corres_assert_gen_asm_l)
        apply (rule corres_stateAssert_implied[where P'=\<top>, simplified])
         apply (rule corres_split[OF updateReply_corres]; clarsimp simp: reply_relation_def)
           apply (rule setThreadState_corres)
           apply (clarsimp simp: thread_state_relation_def)
          apply wpsimp
         apply (wpsimp simp: updateReply_def)
        apply (fastforce simp: replyUnlink_assertion_def thread_state_relation_def)
       apply (wpsimp wp: hoare_vcg_disj_lift gts_wp get_simple_ko_wp)+
   apply (clarsimp simp: sk_obj_at_pred_def obj_at_def is_reply pred_tcb_at_def is_tcb)
  apply (clarsimp simp: obj_at'_def st_tcb_at'_def)
  done

lemma setNotification_valid_tcbs'[wp]:
  "setNotification ntfn val \<lbrace>valid_tcbs'\<rbrace>"
  unfolding valid_tcbs'_def
  by (wpsimp wp: set_ntfn'.setObject_wp hoare_vcg_all_lift hoare_vcg_imp_lift'
           simp: setNotification_def)+

lemma setEndpoint_valid_tcbs'[wp]:
  "setEndpoint ePtr val \<lbrace>valid_tcbs'\<rbrace>"
  unfolding valid_tcbs'_def
  by (wpsimp wp: set_ep'.setObject_wp hoare_vcg_all_lift hoare_vcg_imp_lift'
           simp: setEndpoint_def)

lemma replyUnlink_valid_tcbs'[wp]:
  "replyUnlink replyPtr tcbPtr \<lbrace>valid_tcbs'\<rbrace>"
  unfolding replyUnlink_def getReply_def updateReply_def
  by (wpsimp wp: set_reply'.getObject_wp gts_wp')

lemma set_endpoint_dom_eps_of[wp]:
  "set_endpoint ep_ptr ep \<lbrace>\<lambda>s. P (dom (eps_of s))\<rbrace>"
  apply (wpsimp wp: set_simple_ko_wp)
  apply (fastforce elim: rsubst[where P=P] simp: opt_map_red eps_of_kh_def ep_at_pred_def)
  done

lemma set_endpoint_det_wp[wp]:
  "det_wp (ep_at ep_ptr) (set_endpoint ep_ptr ep)"
  apply (wpsimp wp: get_object_wp set_object_det_wp simp: set_simple_ko_def)
  apply (clarsimp simp: gen_obj_at_simps is_ep_def)
  apply (rename_tac ko, case_tac ko; clarsimp)
  done

lemmas set_endpoint_no_fail[wp] = det_wp_no_fail[OF set_endpoint_det_wp]

lemma no_fail_setEndpoint[wp]:
  "no_fail (ep_at' ptr) (setEndpoint ptr new)"
  unfolding setEndpoint_def
  apply (wpsimp wp: no_fail_setObject_other)
  apply (clarsimp simp: gen_objBits_simps)
  done

lemma no_fail_updateEndpoint[wp]:
  "no_fail (ep_at' ptr) (updateEndpoint ptr f)"
  by (wpsimp wp: getEndpoint_wp simp: updateEndpoint_def)

lemma
  shows updateEndpoint_list_queue_relation[wp]:
    "updateEndpoint epPtr f \<lbrace>\<lambda>s. list_queue_relation ls q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)\<rbrace>"
  and updateNotification_list_queue_relation[wp]:
    "updateNotification epPtr g \<lbrace>\<lambda>s. list_queue_relation ls q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)\<rbrace>"
  by (rule hoare_lift_Pf2[where f=tcbSchedNexts_of]; wpsimp)+

lemma updateEndpoint_epQueues_of_other:
  "\<lbrace>\<lambda>s. P (epQueues_of s p) \<and> p \<noteq> epPtr\<rbrace>
   updateEndpoint epPtr F
   \<lbrace>\<lambda>_ s. P (epQueues_of s p)\<rbrace>"
  apply (wpsimp wp: updateEndpoint_wp)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: opt_map_def)
  done

lemma in_ep_queue_sched_flag_set:
  "\<lbrakk>ep_queues_blocked s; (s, s') \<in> state_relation; pspace_aligned' s'; pspace_distinct' s';
    ep_queues_of s p = Some q\<rbrakk>
   \<Longrightarrow> \<forall>t \<in> set q. tcb_at' t s' \<and> sched_flag_set s' t"
  apply (clarsimp simp: ep_queues_blocked_def ep_blocked_def)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (drule_tac x=t in bspec, fastforce)
  apply (frule (3) st_tcb_at_coerce_concrete)
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def opt_pred_def opt_map_def)
  apply (rename_tac st, case_tac st; clarsimp)
  done

abbreviation in_queue_at_2 :: "obj_ref  \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref list) \<Rightarrow> bool" where
  "in_queue_at_2 t p qs \<equiv> \<exists>q. qs p = Some q \<and> t \<in> set q"

definition in_ep_queue_at :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "in_ep_queue_at t p s \<equiv> in_queue_at_2 t p (ep_queues_of s)"

definition ep_queued :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "ep_queued t s \<equiv> \<exists>p. in_ep_queue_at t p s"

lemma ep_queued_lift:
  "(\<And>P. f \<lbrace>\<lambda>s. P (ep_queues_of s)\<rbrace>) \<Longrightarrow> (\<And>P. f \<lbrace>\<lambda>s. P (ep_queued t s)\<rbrace>)"
  apply (clarsimp simp: ep_queued_def in_ep_queue_at_def)
  by (rule hoare_lift_Pf2; wpsimp)

definition in_ntfn_queue_at :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "in_ntfn_queue_at t p s \<equiv> in_queue_at_2 t p (ntfn_queues_of s)"

definition ntfn_queued :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "ntfn_queued t s \<equiv> \<exists>p. in_ntfn_queue_at t p s"

lemma ntfn_queued_lift:
  "(\<And>P. f \<lbrace>\<lambda>s. P (ntfn_queues_of s)\<rbrace>) \<Longrightarrow> (\<And>P. f \<lbrace>\<lambda>s. P (ntfn_queued t s)\<rbrace>)"
  apply (clarsimp simp: ntfn_queued_def in_ntfn_queue_at_def)
  by (rule hoare_lift_Pf2; wpsimp)

lemma ep_queues_relationD:
  "\<lbrakk>ep_queues_of s p = Some ls; epQueues_of s' p = Some q; ep_queues_relation s s'\<rbrakk>
   \<Longrightarrow> list_queue_relation ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
  by (clarsimp simp: ep_queues_relation_def)

crunch tcbAppend
  for eps_of'[wp]: "\<lambda>s. P (eps_of' s)"
  and ntfns_of'[wp]: "\<lambda>s. P (ntfns_of' s)"
  (wp: crunch_wps)

crunch tcbEPAppend, tcbEPDequeue, tcbNTFNAppend, tcbNTFNDequeue
  for ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"
  and inQ_opt_pred[wp]: "\<lambda>s. P (inQ d p |< tcbs_of' s)"
  and tcbInReleaseQueue_tcbs_of'[wp]: "\<lambda>s. P (tcbInReleaseQueue |< tcbs_of' s)"
  and ksArchState[wp]: "\<lambda>s. P (ksArchState s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  and ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  and ksIdleSC[wp]: "\<lambda>s. P (ksIdleSC s)"
  and ksMachineState[wp]: "\<lambda>s. P (ksMachineState s)"
  and ksWorkUnitsCompleted[wp]: "\<lambda>s. P (ksWorkUnitsCompleted s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and ksDomScheduleStart[wp]: "\<lambda>s. P (ksDomScheduleStart s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomainTime[wp]: "\<lambda>s. P (ksDomainTime s)"
  and ksConsumedTime[wp]: "\<lambda>s. P (ksConsumedTime s)"
  and ksCurTime[wp]: "\<lambda>s. P (ksCurTime s)"
  and ksCurSc[wp]: "\<lambda>s. P (ksCurSc s)"
  and ksReprogramTimer[wp]: "\<lambda>s. P (ksReprogramTimer s)"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and gsUserPages[wp]: "\<lambda>s. P (gsUserPages s)"
  and gsCNodes[wp]: "\<lambda>s. P (gsCNodes s)"
  and ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and replies_of'[wp]: "\<lambda>s. P (replies_of' s)"
  and pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and pspace_bounded'[wp]: pspace_bounded'
  and pspace_canonical'[wp]: pspace_canonical'
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  and no_0_obj'[wp]: no_0_obj'
  and valid_mdb'[wp]: valid_mdb'
  and valid_bitmaps[wp]: valid_bitmaps
  and if_unsafe_then_cap'[wp]: if_unsafe_then_cap'
  and valid_global_refs'[wp]: valid_global_refs'
  and valid_arch_state'[wp]: valid_arch_state'
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and valid_irq_states'[wp]: valid_irq_states'
  and valid_machine_state'[wp]: valid_machine_state'
  and pspace_domain_valid[wp]: pspace_domain_valid
  (wp: crunch_wps)

lemma tcbEPDequeue_corres:
  "\<lbrakk>tcb_ptr = tcbPtr; ep_ptr = epPtr\<rbrakk> \<Longrightarrow>
   corres dc
     (in_ep_queue_at tcb_ptr ep_ptr
      and ep_queues_blocked and ntfn_queues_blocked and release_q_runnable
      and valid_objs and in_correct_ready_q and ready_qs_distinct and ready_queues_runnable
      and ready_or_release and pspace_aligned and pspace_distinct)
     (sym_heap_sched_pointers and valid_objs')
     (tcb_ep_dequeue tcb_ptr ep_ptr) (tcbEPDequeue tcbPtr epPtr)"
  supply if_split[split del]
         return_bind[simp del]
  apply add_pspace_adb'
  apply (rule_tac Q="ep_at ep_ptr" in corres_cross_add_abs_guard)
   apply (clarsimp simp: obj_at_def is_ep_def in_ep_queue_at_def eps_of_kh_def opt_map_def
                  split: option.splits)
  apply (rule_tac Q'="ep_at' epPtr" in corres_cross_add_guard, fastforce intro!: ep_at_cross)
  apply (clarsimp simp: tcb_ep_dequeue_def tcbEPDequeue_def)
  apply (rule corres_split_forwards'[OF _ get_simple_ko_sp get_ep_sp'])
   apply (corres corres: getEndpoint_corres)
  apply (rename_tac ep ep')
  apply (rule_tac F="ep_queue ep \<noteq> []" in corres_req)
   apply (fastforce simp: obj_at_def in_ep_queue_at_def eps_of_kh_def opt_map_def)
  apply (rule corres_symb_exec_l[OF _ _ return_sp, rotated]; (solves wpsimp)?)
  apply (rule corres_assert_assume_l_forward)
   apply (clarsimp simp: in_ep_queue_at_def obj_at_def eps_of_kh_def opt_map_def)
  apply clarsimp
  apply (rename_tac ep' q)
  apply (rule_tac Q="\<lambda>s. ep_queues_of s ep_ptr = Some (ep_queue ep) \<and> valid_ep ep s"
               in corres_cross_add_abs_guard)
   apply (intro context_conjI)
    apply (fastforce simp: obj_at_def in_ep_queue_at_def eps_of_kh_def opt_map_def)
   apply (fastforce dest: valid_objs_valid_ep simp: obj_at_def)
  apply (rule_tac Q'="\<lambda>s'. list_queue_relation
                             (ep_queue ep) (epQueue ep') (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
               in corres_cross_add_guard)
   apply (fastforce intro!: ep_queues_relationD simp: opt_map_red obj_at'_def)
  apply (rule corres_underlying_from_rcorres)
   apply (wpsimp wp: tcbQueueRemove_no_fail hoare_vcg_if_lift2 hoare_drop_imps)
   apply (rule_tac x="ep_queue ep" in exI)
   apply (force dest!: in_ep_queue_sched_flag_set[where p=ep_ptr])
  apply (clarsimp simp: state_relation_def ghost_relation_heap_ghost_relation
                        pspace_relation_heap_pspace_relation heap_pspace_relation_def)
  apply (rcorres_conj_lift fastforce)+
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>eps_relation\<close>
   apply (rule_tac Q="\<lambda>ls q s s'. eps_relation s s'
                                  \<and> list_queue_relation
                                      ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                                  \<and> ep_at epPtr s \<and> ko_at' ep' epPtr s'"
                in rcorres_split)
    apply (rule rcorres_from_valid_det; (solves wpsimp)?)
    apply (clarsimp simp: return_bind)
    apply (drule in_set_endpoint)
    apply (wpsimp wp: updateEndpoint_wp)
    apply (frule list_queue_relation_Nil)
    apply (clarsimp simp: eps_of_kh_def projectKO_opts_defs map_relation_def ep_relation_def
                          obj_at'_def
                   split: if_splits list.splits Structures_A.endpoint.splits)
   apply (rcorres rcorres: tcbQueueRemove_rcorres)
   apply blast
  apply (rcorres_conj_lift fastforce)+
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>ep_queues_relation\<close>
   apply (simp only: ep_queues_relation_def)
   apply (rule rcorres_allI_fwd; (solves wpsimp)?)
   apply (rename_tac p)
   apply (case_tac "p \<noteq> epPtr")
    apply (rule_tac Q="\<lambda>_ _ s s'. ep_at epPtr s
                                  \<and> (\<forall>ls q. ep_queues_of s p = Some ls
                                            \<longrightarrow> epQueues_of s' p = Some q
                                            \<longrightarrow> list_queue_relation
                                                  ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
                 in rcorres_split[rotated])
     apply clarsimp
     apply (rcorres rcorres: tcbQueueRemove_rcorres_other rcorres_op_lifts)
     apply (metis ep_queues_disjoint)
    apply (rcorres rcorres: rcorres_op_lifts
                        wp: set_endpoint_ep_queues_of_other
                            updateEndpoint_epQueues_of_other hoare_vcg_if_lift2)
    apply clarsimp
   \<comment> \<open>p = epPtr\<close>
   apply (rule_tac Q="\<lambda>ls q s s'. ep_at epPtr s
                                  \<and> list_queue_relation
                                      ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
                in rcorres_split)
    apply (rule rcorres_from_valid_det; (solves wpsimp)?)
    apply (wpsimp wp: valid_from_rcorres_det_return[OF tcbQueueRemove_rcorres] updateEndpoint_wp)
    apply (clarsimp simp: return_bind)
    apply (drule in_set_endpoint)
    apply (clarsimp simp: projectKO_opts_defs split: if_splits)
    subgoal
      by (fastforce simp: eps_of_kh_def opt_map_def obj_at'_def projectKO_opts_defs
                   split: list.splits kernel_object.splits)
   apply (rcorres rcorres: tcbQueueRemove_rcorres)
   apply blast
  apply (rule rcorres_add_return_l)
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>ntfn_queues_relation\<close>
   apply (simp add: ntfn_queues_relation_def bind_assoc)
   apply (rcorres rcorres: tcbQueueRemove_rcorres_other rcorres_op_lifts)
   apply (fast dest!: ep_queues_ntfn_queues_disjoint)
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>ready_queues_relation\<close>
   apply (simp add: ready_queues_relation_def ready_queue_relation_def Let_def bind_assoc)
   apply (intro rcorres_allI_fwd; (solves wpsimp)?)
   apply (rename_tac d p)
   apply (rule_tac p="\<lambda>s. ready_queues s d p" in rcorres_lift_abs)
    apply (rule_tac p="\<lambda>s'. ksReadyQueues s' (d, p)" in rcorres_lift_conc)
     apply (rcorres rcorres: tcbQueueRemove_rcorres_other rcorres_op_lifts)
     apply (auto dest!: ep_queues_ready_queues_disjoint)[1]
    apply wpsimp
   apply wpsimp
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>release_queue_relation\<close>
   apply (simp only: release_queue_relation_def bind_assoc fun_app_def)
   apply (rule_tac p=release_queue in rcorres_lift_abs)
    apply (rule_tac p=ksReleaseQueue in rcorres_lift_conc)
     apply (rcorres rcorres: tcbQueueRemove_rcorres_other rcorres_op_lifts)
     apply (blast dest!: ep_queues_release_queue_disjoint)
    apply wpsimp
   apply wpsimp
  by (rcorres_conj_lift fastforce)+

crunch tcb_ep_dequeue, tcb_ntfn_dequeue
  for ready_queues_runnable[wp]: ready_queues_runnable
  and in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  and release_q_runnable[wp]: release_q_runnable
  (wp: crunch_wps ready_queues_runnable_lift in_correct_ready_q_lift ready_qs_distinct_lift
       release_q_runnable_lift)

crunch tcbEPDequeue
  for valid_objs'[wp]: valid_objs'

lemma valid_ntfn'_ntfnQueue_update[simp]:
  "valid_obj' (KONotification (ntfnQueue_update f ntfn)) s = valid_obj' (KONotification ntfn) s"
  by (clarsimp simp: valid_obj'_def valid_ntfn'_def)

lemma updateNotification_ntfnQueue_update_valid_objs'[wp]:
  "updateNotification ntfnPtr (ntfnQueue_update f) \<lbrace>valid_objs'\<rbrace>"
  unfolding updateNotification_def
  apply (wpsimp wp: getNotification_wp)
  apply (fastforce dest!: ntfn_ko_at_valid_objs_valid_ntfn' simp: valid_ntfn'_def)
  done

lemma updateNotification_valid_objs'[wp]:
  "\<lbrace>\<lambda>s. valid_objs' s
        \<and> (\<forall>ntfn'. ko_at' ntfn' ntfnPtr s \<and> valid_obj' (injectKO ntfn') s
                   \<longrightarrow> valid_obj' (injectKO (f ntfn')) s)\<rbrace>
   updateNotification ntfnPtr f
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wpsimp simp: updateNotification_def wp: set_ntfn'.valid_objs' getNotification_wp)
  apply (fastforce simp: valid_obj'_def valid_sched_context'_def valid_sched_context_size'_def
                         obj_at'_def opt_map_red)
  done

lemma tcbNTFNDequeue_valid_objs'[wp]:
  "tcbNTFNDequeue tcbPtr ntfnPtr \<lbrace>valid_objs'\<rbrace>"
  supply if_split[split del]
  unfolding tcbNTFNDequeue_def
  apply wpsimp
     apply (rule_tac Q'="\<lambda>_. valid_objs'" in hoare_post_imp)
      apply (clarsimp simp: valid_obj'_def valid_ntfn'_def split: if_splits)
     apply (wpsimp wp: getNotification_wp)+
  done

lemma blocked_cancelIPC_corres:
  "\<lbrakk>st = Structures_A.BlockedOnReceive epPtr reply_opt p'
    \<or> st = Structures_A.BlockedOnSend epPtr p;
    thread_state_relation st st'; st = Structures_A.BlockedOnSend epPtr p \<longrightarrow> reply_opt = None\<rbrakk> \<Longrightarrow>
   corres dc
     (valid_objs and ready_qs_distinct and in_correct_ready_q and ready_queues_runnable
      and release_q_runnable and ready_or_release
      and pspace_aligned and pspace_distinct
      and st_tcb_at ((=) st) t and (\<lambda>s. sym_refs (state_refs_of s)))
     (valid_objs' and sym_heap_sched_pointers and valid_sched_pointers
      and st_tcb_at' ((=) st') t)
     (blocked_cancel_ipc st t reply_opt)
     (blockedCancelIPC st' t reply_opt)"
  (is "\<lbrakk> _ ; _ ; _ \<rbrakk> \<Longrightarrow> corres _ (?abs_guard and _) _ _ _")
  apply add_pspace_adb'
  apply (prop_tac "getBlockingObject st' = return epPtr")
   apply (case_tac st; clarsimp simp: getBlockingObject_def epBlocked_def)
  apply (rule_tac Q="valid_tcb_state st " in corres_cross_add_abs_guard)
   apply (force intro!: st_tcb_at_valid_st2)
  apply (simp add: blocked_cancel_ipc_def blockedCancelIPC_def gbep_ret)
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro!: reply_at_cross simp: valid_bound_obj'_def split: option.splits)
  apply (rule corres_stateAssert_ignore)
   apply (force intro!: ep_at_cross simp: valid_tcb_state_def split: option.splits)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF tcbEPDequeue_corres], simp, simp)
      \<comment>\<open>drop sym_refs assumtions; add reply_tcb link\<close>
      apply (rule_tac P="?abs_guard
                         and (\<lambda>s. bound reply_opt
                                  \<longrightarrow> reply_tcb_reply_at ((=) (Some t)) (the reply_opt) s)"
                  and P'="valid_objs' and st_tcb_at' ((=) st') t
                          and pspace_aligned' and pspace_distinct'"
                   in corres_inst)
      \<comment>\<open>cross over replyTCB\<close>
      apply (rule_tac Q'="\<lambda>s. bound reply_opt \<longrightarrow> obj_at' (\<lambda>r. replyTCB r = Some t) (the reply_opt) s"
                      in corres_cross_add_guard)
       apply clarsimp
       apply (drule state_relationD)
       apply (frule_tac s'=s' in pspace_aligned_cross, simp)
       apply (frule_tac s'=s' in pspace_distinct_cross, simp, simp)
       apply (clarsimp simp: obj_at_def sk_obj_at_pred_def)
       apply (rename_tac rp reply)
       apply (drule_tac x=rp in pspace_relation_absD, simp)
       apply (clarsimp simp: obj_relation_cuts_def obj_at'_def reply_relation_def)
       apply (rename_tac ko)
       apply (case_tac ko; simp)
       apply (rename_tac reply')
       apply (frule_tac x=rp in pspace_alignedD', simp)
       apply (frule_tac x=rp in pspace_distinctD', simp)
       apply (drule_tac x=rp in pspace_boundedD'[OF _ pspace_relation_pspace_bounded'], simp)
       apply (clarsimp simp: reply_relation_def)
       \<comment>\<open>main corres proof\<close>
      apply (erule disjE; clarsimp simp: ep_relation_def split del: if_split)
       apply (cases reply_opt;
              simp split del: if_split add: bind_assoc cong: if_cong)
         \<comment>\<open>reply_opt = None\<close>
        apply (rule corres_guard_imp)
            apply (rule setThreadState_corres)
            apply simp
           apply wpsimp+
         apply (frule (1) Receive_or_Send_ep_at[rotated], fastforce)
         apply (intro conjI;
                clarsimp simp: st_tcb_at_def obj_at_def is_ep is_tcb
                       intro!: valid_ep_remove1_RecvEP)
        apply clarsimp
         \<comment>\<open>reply_opt bound\<close>
       apply (rule corres_guard_imp)
             apply (rule corres_split[OF replyUnlink_corres])
               apply (rule setThreadState_corres, simp)
              apply wpsimp
             apply (wpsimp wp: replyUnlink_valid_objs')
            apply (fastforce simp: pred_tcb_at_def obj_at_def is_tcb)
           apply (fastforce simp: obj_at'_def pred_tcb_at'_def)
      \<comment>\<open>BlockedOnSend\<close>
      apply (rule corres_guard_imp)
          apply (rule setThreadState_corres)
          apply simp
         apply (simp add: valid_tcb_state_def pred_conj_def)
         apply wpsimp+
       apply (frule (1) Receive_or_Send_ep_at[rotated], fastforce)
       apply (intro conjI;
              clarsimp simp: st_tcb_at_def obj_at_def is_ep is_tcb
                     intro!: valid_ep_remove1_SendEP)
      apply (clarsimp split del: if_split)
     apply (wpsimp wp: getEndpoint_wp hoare_vcg_conj_lift get_simple_ko_wp)+
   apply (frule sym_refs_ep_queues_blocked)
   apply (frule sym_refs_ntfn_queues_blocked)
   apply (rule conjI)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def)
    apply (elim disjE)
     apply (fastforce dest!: sym_ref_BlockedOnReceive_RecvEP
                       simp: in_ep_queue_at_def eps_of_kh_def opt_map_def split: option.splits)
    apply (fastforce dest!: sym_ref_BlockedOnSend_SendEP
                      simp: in_ep_queue_at_def eps_of_kh_def opt_map_def split: option.splits)
   apply clarsimp
   apply (drule (1) st_tcb_recv_reply_state_refs)
   apply (clarsimp simp: sk_obj_at_pred_def obj_at_def)
  apply clarsimp
  done

lemma sym_ref_BlockedOnNotification:
  "\<lbrakk>sym_refs (state_refs_of s); kheap s tcb_ptr = Some (TCB tcb);
    tcb_state tcb = Structures_A.BlockedOnNotification ntfn_ptr\<rbrakk>
   \<Longrightarrow> in_ntfn_queue_at tcb_ptr ntfn_ptr s"
  apply (drule sym_refs_obj_atD[rotated, where p=tcb_ptr])
   apply (clarsimp simp: obj_at_def, simp)
  apply (clarsimp simp: state_refs_of_def)
  apply (drule_tac x="(ntfn_ptr, TCBSignal)" in bspec)
   apply (fastforce split: if_split_asm)
  apply (clarsimp simp: obj_at_def ntfn_at_pred_def)
  by (rename_tac ko'; case_tac ko';
      clarsimp simp: in_ntfn_queue_at_def ntfn_q_refs_of_def opt_map_def get_refs_def2
              split: ntfn.splits)

lemma no_fail_setNotification[wp]:
  "no_fail (ntfn_at' ptr) (setNotification ptr new)"
  unfolding setNotification_def
  apply (wpsimp wp: no_fail_setObject_other)
  apply (clarsimp simp: gen_objBits_simps)
  done

lemma no_fail_updateNotification[wp]:
  "no_fail (ntfn_at' ptr) (updateNotification ptr f)"
  by (wpsimp wp: getNotification_wp simp: updateNotification_def)

lemma in_ntfn_queue_sched_flag_set:
  "\<lbrakk>ntfn_queues_blocked s; (s, s') \<in> state_relation; pspace_aligned' s'; pspace_distinct' s';
    ntfn_queues_of s p = Some q\<rbrakk>
   \<Longrightarrow> \<forall>t \<in> set q. tcb_at' t s' \<and> sched_flag_set s' t"
  apply (clarsimp simp: ntfn_queues_blocked_def ntfn_blocked_def)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (drule_tac x=t in bspec, fastforce)
  apply (frule (3) st_tcb_at_coerce_concrete)
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def opt_pred_def opt_map_def split: option.splits)
  apply (rename_tac st ntfn, case_tac st; clarsimp)
  done

lemma set_notification_det_wp[wp]:
  "det_wp (ntfn_at ntfn_ptr) (set_notification ntfn_ptr ntfn)"
  apply (wpsimp wp: get_object_wp set_object_det_wp simp: set_simple_ko_def)
  apply (safe; clarsimp simp: gen_obj_at_simps is_ntfn_def)
  apply (rename_tac ko, case_tac ko; clarsimp)
  done

lemmas set_notification_no_fail[wp] = det_wp_no_fail[OF set_notification_det_wp]

lemma updateNotification_ntfnQueues_of_other:
  "\<lbrace>\<lambda>s. P (ntfnQueues_of s p) \<and> p \<noteq> ntfnPtr\<rbrace>
   updateNotification ntfnPtr F
   \<lbrace>\<lambda>_ s. P (ntfnQueues_of s p)\<rbrace>"
  apply (wpsimp wp: updateNotification_wp)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: opt_map_def)
  done

lemma set_notification_ntfn_queues_of_other:
  "\<lbrace>\<lambda>s. P (ntfn_queues_of s p) \<and> p \<noteq> ntfn_ptr\<rbrace>
   set_notification ntfn_ptr ntfn
   \<lbrace>\<lambda>_ s. P (ntfn_queues_of s p)\<rbrace>"
  by (wpsimp wp: set_simple_ko_wp)

lemma ntfn_queues_relationD:
  "\<lbrakk>ntfn_queues_of s p = Some ls; ntfnQueues_of s' p = Some q; ntfn_queues_relation s s'\<rbrakk>
   \<Longrightarrow> list_queue_relation ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
  by (clarsimp simp: ntfn_queues_relation_def)

lemma tcbNTFNDequeue_corres:
  "\<lbrakk>tcb_ptr = tcbPtr; ntfn_ptr = ntfnPtr\<rbrakk> \<Longrightarrow>
   corres dc
     (in_ntfn_queue_at tcb_ptr ntfn_ptr
      and ep_queues_blocked and ntfn_queues_blocked and release_q_runnable
      and valid_objs and in_correct_ready_q and ready_qs_distinct and ready_queues_runnable
      and ready_or_release and pspace_aligned and pspace_distinct)
     (sym_heap_sched_pointers and valid_objs')
     (tcb_ntfn_dequeue tcb_ptr ntfn_ptr) (tcbNTFNDequeue tcbPtr ntfnPtr)"
  supply if_split[split del] return_bind[simp del]
  apply add_pspace_adb'
  apply (rule_tac Q="ntfn_at ntfn_ptr" in corres_cross_add_abs_guard)
   apply (clarsimp simp: obj_at_def is_ntfn_def in_ntfn_queue_at_def opt_map_def
                  split: option.splits)
  apply (rule_tac Q'="ntfn_at' ntfnPtr" in corres_cross_add_guard)
   apply (fastforce intro!: ntfn_at_cross)
  apply (clarsimp simp: tcb_ntfn_dequeue_def tcbNTFNDequeue_def)
  apply (rule corres_split_forwards'[OF _ get_simple_ko_sp get_ntfn_sp'])
   apply (corres corres: getNotification_corres)
  apply (rename_tac ntfn ntfn')
  apply (rule_tac F="ntfn_queue (ntfn_obj ntfn) \<noteq> []" in corres_req)
   apply (fastforce simp: obj_at_def in_ntfn_queue_at_def opt_map_def)
  apply (rule corres_symb_exec_l[OF _ _ return_sp]; (solves wpsimp)?)
  apply (rule corres_assert_assume_l_forward)
   apply (clarsimp simp: in_ntfn_queue_at_def obj_at_def opt_map_red)
  apply (rule corres_underlying_from_rcorres)
   apply (wpsimp wp: tcbQueueRemove_no_fail hoare_vcg_if_lift2 hoare_drop_imps)
   apply (rule_tac x="ntfn_queue (ntfn_obj ntfn)" in exI)
   apply (frule (3) in_ntfn_queue_sched_flag_set[where p=ntfn_ptr])
    apply (fastforce simp: opt_map_def obj_at_def)
   apply (force dest!: spec[where x=ntfnPtr] state_relation_ntfn_queues_relation
                 simp: ntfn_queues_relation_def in_ntfn_queue_at_def opt_map_red
                       obj_at'_def obj_at_def)
  apply (rule_tac Q="\<lambda>s s'. valid_ntfn ntfn s
                            \<and> ntfn_queues_of s ntfn_ptr = Some (ntfn_queue (ntfn_obj ntfn))
                            \<and> tcbPtr \<in> set (ntfn_queue (ntfn_obj ntfn))
                            \<and> list_queue_relation
                                (ntfn_queue (ntfn_obj ntfn)) (ntfnQueue ntfn')
                                (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
               in rcorres_add_to_pre)
   apply (intro context_conjI)
      apply (fastforce dest: valid_objs_valid_ntfn simp: obj_at_def)
     apply (fastforce simp: obj_at_def in_ntfn_queue_at_def opt_map_def)
    apply (clarsimp simp: in_ntfn_queue_at_def)
   apply (fastforce intro!: ntfn_queues_relationD simp: opt_map_red obj_at'_def)
  apply (simp only: state_relation_def ghost_relation_heap_ghost_relation)
  apply (clarsimp simp: pspace_relation_heap_pspace_relation heap_pspace_relation_def)
  apply (rcorres_conj_lift fastforce)+
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>ntfns_relation\<close>
   apply (rule_tac Q="\<lambda>ls q s s'. ntfns_relation s s'
                                  \<and> list_queue_relation
                                      ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                                  \<and> ntfn_at ntfnPtr s \<and> ko_at' ntfn' ntfnPtr s'"
                in rcorres_split)
    apply (rule rcorres_from_valid_det; (solves wpsimp)?)
    apply (clarsimp simp: return_bind)
    apply (drule in_set_notification)
    apply (wpsimp wp: updateNotification_wp)
    apply (frule list_queue_relation_Nil)
    apply (clarsimp simp: projectKO_opts_defs map_relation_def ntfn_relation_def obj_at'_def
                   split: if_splits list.splits ntfn.splits)
   apply (rcorres rcorres: tcbQueueRemove_rcorres)
   apply blast
  apply (rcorres_conj_lift fastforce)+
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>ep_queues_relation\<close>
   apply (simp only: ep_queues_relation_def fun_app_def)
   apply (rcorres rcorres: tcbQueueRemove_rcorres_other rcorres_op_lifts)
   apply (fast dest!: ep_queues_ntfn_queues_disjoint)
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>ntfn_queues_relation\<close>
   apply (simp only: ntfn_queues_relation_def)
   apply (rule rcorres_allI_fwd; (solves wpsimp)?)
   apply (rename_tac p)
   apply (case_tac "p \<noteq> ntfnPtr")
    apply (rule_tac Q="\<lambda>_ _ s s'. ntfn_at ntfnPtr s
                                  \<and> (\<forall>ls q. ntfn_queues_of s p = Some ls
                                            \<longrightarrow> ntfnQueues_of s' p = Some q
                                            \<longrightarrow> list_queue_relation
                                                  ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
                 in rcorres_split[rotated])
     apply clarsimp
     apply (rcorres rcorres: tcbQueueRemove_rcorres_other rcorres_op_lifts)
     apply clarsimp
     apply (metis ntfn_queues_disjoint)
    apply (rcorres rcorres: rcorres_op_lifts
                        wp: set_notification_ntfn_queues_of_other
                            updateNotification_ntfnQueues_of_other hoare_vcg_if_lift2)
    apply clarsimp
   \<comment> \<open>p = ntfnPtr\<close>
   apply (rule_tac Q="\<lambda>ls q s s'. ntfn_at ntfnPtr s
                                  \<and> list_queue_relation
                                      ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
                in rcorres_split)
    apply (rule rcorres_from_valid_det; (solves wpsimp)?)
    apply (wpsimp wp: valid_from_rcorres_det_return[OF tcbQueueRemove_rcorres] updateNotification_wp)
    apply (clarsimp simp: return_bind)
    apply (drule in_set_notification)
    apply (clarsimp simp: projectKO_opts_defs split: if_splits)
    apply (clarsimp simp: opt_map_def obj_at'_def;
           fastforce simp: projectKO_opts_defs split: list.splits)
   apply (rcorres rcorres: tcbQueueRemove_rcorres)
   apply blast
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>ready_queues_relation\<close>
   apply (simp add: ready_queues_relation_def ready_queue_relation_def Let_def bind_assoc)
   apply (intro rcorres_allI_fwd; (solves wpsimp)?)
   apply (rename_tac d p)
   apply (rule_tac p="\<lambda>s. ready_queues s d p" in rcorres_lift_abs)
    apply (rule_tac p="\<lambda>s'. ksReadyQueues s' (d, p)" in rcorres_lift_conc)
     apply (rcorres rcorres: tcbQueueRemove_rcorres_other rcorres_op_lifts)
     apply (auto dest!: ntfn_queues_ready_queues_disjoint)[1]
    apply wpsimp
   apply wpsimp
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>release_queue_relation\<close>
   apply (simp only: release_queue_relation_def bind_assoc fun_app_def)
   apply (rule_tac p=release_queue in rcorres_lift_abs)
    apply (rule_tac p=ksReleaseQueue in rcorres_lift_conc)
     apply (rcorres rcorres: tcbQueueRemove_rcorres_other rcorres_op_lifts)
     apply (blast dest!: ntfn_queues_release_queue_disjoint)
    apply wpsimp
   apply wpsimp
  by (rcorres_conj_lift fastforce)+

lemma tcb_ntfn_dequeue_valid_tcbs[wp]:
  "tcb_ntfn_dequeue tcb_ptr ntfn_ptr \<lbrace>valid_tcbs\<rbrace>"
  unfolding tcb_ntfn_dequeue_def
  by (wpsimp wp: get_simple_ko_wp)

lemma cancelSignal_corres:
  "corres dc
     (invs and valid_ready_qs and release_q_runnable and ready_or_release
      and st_tcb_at ((=) (Structures_A.BlockedOnNotification ntfnPtr)) t)
     invs'
     (cancel_signal t ntfnPtr) (cancelSignal t ntfnPtr)"
  apply add_ready_qs_runnable
  apply add_sym_refs
  apply (rule_tac Q="ntfn_at ntfnPtr" in corres_cross_add_abs_guard)
   apply (fastforce dest: st_tcb_at_valid_st2 simp: valid_tcb_state_def)
  apply (simp add: cancel_signal_def cancelSignal_def)
  apply (rule corres_stateAssert_add_assertion[rotated], fastforce dest!: sym_refs_cross)
  apply (rule corres_stateAssert_add_assertion[rotated], fastforce)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF tcbNTFNDequeue_corres], simp, simp)
      apply (fastforce intro: setThreadState_corres)
     apply (wpsimp | strengthen valid_objs'_valid_tcbs')+
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (frule invs_sym_refs)
   apply (frule (1) sym_ref_BlockedOnNotification)
    apply (erule sym)
   apply (fastforce simp: is_tcb_def)
  apply fastforce
  done

lemma cte_map_tcb_2:
  "cte_map (t, tcb_cnode_index 2) = t + 2*2^cte_level_bits"
  by (simp add: cte_map_def tcb_cnode_index_def to_bl_1 shiftl_t2n)

locale IpcCancel_R =
  assumes Arch_postCapDeletion_typ_at'[wp]:
    "\<And>acap T p P. Arch.postCapDeletion acap \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace>"
  assumes Arch_postCapDeletion_sc_at'_n[wp]:
    "\<And>acap n p P. Arch.postCapDeletion acap \<lbrace>\<lambda>s. P (sc_at'_n n p s)\<rbrace>"
  assumes Arch_postCapDeletion_st_tcb_at'[wp]: (* can't use pred_tcb_at' due to free type variable *)
    "\<And>acap P t. Arch.postCapDeletion acap \<lbrace>st_tcb_at' P t\<rbrace>"
  assumes arch_post_cap_deletion_pspace_distinct[wp]:
    "\<And>acap. arch_post_cap_deletion acap \<lbrace>\<lambda>s::det_state. pspace_distinct s\<rbrace>"
  assumes arch_post_cap_deletion_pspace_aligned[wp]:
    "\<And>acap. arch_post_cap_deletion acap \<lbrace>\<lambda>s::det_state. pspace_aligned s\<rbrace>"
  assumes prepareThreadDelete_corres[corres]:
    "\<And>t t'. t' = t \<Longrightarrow>
            corres dc (invs and tcb_at t) no_0_obj'
                   (prepare_thread_delete t) (prepareThreadDelete t')"

context IpcCancel_R begin

crunch emptySlot
  for st_tcb_at'[wp]: "st_tcb_at' P t" (* can't use pred_tcb_at' due to locale *)
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: setCTE_pred_tcb_at')

crunch cancel_ipc
  for pspace_aligned[wp]: "pspace_aligned :: det_state \<Rightarrow> _"
  and pspace_distinct[wp]: "pspace_distinct :: det_state \<Rightarrow> _"
  (simp: crunch_simps wp: crunch_wps)

end (* IpcCancel_R *)

lemma reply_mdbNext_is_descendantD:
  assumes sr: "(s, s') \<in> state_relation"
  and   invs: "invs' s'"
  and    tcb: "tcb_at t s"
  and    cte: "ctes_of s' (t + 2*2^cte_level_bits) = Some cte"
  and   desc: "descendants_of (t, tcb_cnode_index 2) (cdt s) = {sl}"
  shows       "mdbNext (cteMDBNode cte) = cte_map sl"
proof -
  from tcb have "cte_at (t, tcb_cnode_index 2) s"
    by (simp add: tcb_at_cte_at dom_tcb_cap_cases)
  hence "descendants_of' (t + 2*2^cte_level_bits) (ctes_of s') = {cte_map sl}"
    using sr desc
    by (fastforce simp: state_relation_def cdt_relation_def cte_map_def tcb_cnode_index_def shiftl_t2n mult_ac)
  thus ?thesis
    using cte invs
    apply (clarsimp simp: descendants_of'_def)
    apply (frule singleton_eqD, drule CollectD)
    apply (erule subtree.cases)
     apply (clarsimp simp: mdb_next_rel_def mdb_next_def)
    apply (subgoal_tac "c' = cte_map sl")
     apply (fastforce del: invs_no_loops dest: invs_no_loops no_loops_direct_simp)
    apply fastforce
    done
qed

locale delete_one_conc = delete_one_conc_pre +
  assumes delete_one_invs:
    "\<And>p. \<lbrace>invs' and sch_act_simple\<rbrace> cteDeleteOne p \<lbrace>\<lambda>_. invs'\<rbrace>"

locale delete_one = delete_one_conc + delete_one_abs +
  assumes delete_one_corres:
    "corres dc
         (einvs and simple_sched_action and cte_wp_at can_fast_finalise ptr
          and current_time_bounded)
         (invs' and cte_at' (cte_map ptr))
         (cap_delete_one ptr) (cteDeleteOne (cte_map ptr))"

locale delete_one_gen = delete_one +
  assumes update_restart_pc_corres:
    "\<And>t. corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
                (update_restart_pc t) (updateRestartPC t)"
  (* results of IpcCancel_R locale *)
  assumes cancel_ipc_pspace_aligned[wp]:
    "\<And>t. cancel_ipc t \<lbrace>\<lambda>s::det_state. pspace_aligned s\<rbrace>"
  assumes cancel_ipc_pspace_distinct[wp]:
    "\<And>t. cancel_ipc t \<lbrace>\<lambda>s::det_state. pspace_distinct s\<rbrace>"

lemma gbep_ret':
  "\<lbrakk> st = BlockedOnReceive epPtr r d \<or> st = BlockedOnSend epPtr p1 p2 p3 p4 \<rbrakk>
      \<Longrightarrow> getBlockingObject st = return epPtr"
  by (auto simp add: getBlockingObject_def epBlocked_def assert_opt_def)

lemma get_reply_obj_ref_det_wp[wp]:
  "det_wp (reply_at reply_ptr) (get_reply_obj_ref reply_sc reply_ptr)"
  by (wpsimp simp: get_sk_obj_ref_def)

crunch break_reply_chain_at
  for (empty_fail) empty_fail[wp, simp]

crunch break_reply_chain_at
  for dom_scs_of[wp]: "\<lambda>s. P (dom (scs_of s))"
  and aobjs_of[wp]: "\<lambda>s. P (aobjs_of s)"
  (wp: crunch_wps ignore: update_sched_context update_sk_obj_ref)

lemma get_reply_obj_ref_exs_valid[wp]:
  "reply_at reply_ptr s \<Longrightarrow> \<lbrace>(=) s\<rbrace> get_reply_obj_ref reply_sc reply_ptr \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  unfolding get_sk_obj_ref_def
  apply wpsimp
   apply (clarsimp simp: obj_at_def is_reply)+
  done

lemma breakReplyChainAt'_no_fail[wp]:
  "no_fail (valid_objs' and reply_at' replyPtr) (breakReplyChainAt' replyPtr)"
  apply (clarsimp simp: breakReplyChainAt'_def)
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')
  apply (fastforce dest: reply_ko_at_valid_objs_valid_reply'
                   simp: valid_reply'_def in_opt_pred opt_map_red obj_at'_def)
  done

crunch breakReplyChainAt
  for (no_fail) no_fail[wp, simp]
  (simp: crunch_simps wp: crunch_wps)

lemma breakReplyChainAt_not_in_reply_stack_corres:
  "corres dc
     (\<lambda>s. reply_at replyPtr s \<and> valid_replies s \<and> sym_refs (state_refs_of s)
          \<and> pspace_aligned s \<and> pspace_distinct s \<and> sc_with_reply replyPtr s = None)
     (valid_objs' and sym_heap_reply_pointers)
     (return ()) (breakReplyChainAt replyPtr)"
  apply add_pspace_adb'
  apply (rule_tac Q'="reply_at' replyPtr" in corres_cross_add_guard)
   apply (fastforce intro!: reply_at_cross)
  apply (clarsimp simp: breakReplyChainAt_def)
  apply (rule corres_symb_exec_r[OF _ get_reply_sp']; (solves wpsimp)?)
  apply (rename_tac reply)
  apply (rule_tac F="replySC reply = None" in corres_req)
   apply clarsimp
   apply (frule (3) sc_with_reply_None_reply_sc_reply_at)
   apply (force dest!: replies_relation_reply_relation_abs_obj_at' state_relation_pspace_relation
                 simp: pspace_relation_heap_pspace_relation reply_at_ppred_def obj_at_def
                       obj_at'_def reply_relation_def)
  apply (rule corres_underlying_from_rcorres; (solves wpsimp)?)
  apply (clarsimp simp: state_relation_def ghost_relation_heap_ghost_relation
                        pspace_relation_heap_pspace_relation heap_pspace_relation_def)
  apply (rcorres_conj_lift clarsimp
                           wp: update_sched_context_det_wp_weak update_sched_context_no_fail_weak
                               updateSchedContext_field_inv updateReply_field_inv
                           simp: breakReplyChainAt'_def)+
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>sc_replies_relation\<close>
   apply (clarsimp simp: breakReplyChainAt'_def)
   apply (rule rcorres_symb_exec_r[OF get_reply_sp'], rename_tac reply')
   apply (rule_tac F="reply' = reply" in rcorres_req)
    apply normalise_obj_at'
   apply (rule_tac Q="\<lambda>s _. \<forall>p replies. sc_replies_of s p = Some replies \<longrightarrow> replyPtr \<notin> set replies"
               in rcorres_add_to_pre)
    apply (force dest!: valid_replies_sc_with_reply_None
                  simp: sc_at_ppred_def obj_at_def scs_of_kh_def opt_map_def
                 split: option.splits)
   apply (simp only: sc_replies_relation_def)
   apply (intro rcorres_allI_fwd; (solves wpsimp)?)
   apply (rename_tac p replies st)
   apply (rule rcorres_imp_lift_fwd)
    apply rcorres
    apply fastforce
   apply (rule rcorres_imp_lift_fwd)
    apply rcorres
    apply fastforce
   apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
    apply (rcorres wp: updateReply_heap_ls_other hoare_vcg_if_lift2 hoare_vcg_const_imp_lift)
    apply normalise_obj_at'
    apply (fastforce elim!: sym_heapD2
                      dest: heap_ls_prev_not_in
                      simp: opt_map_red obj_at'_def)
   apply (rcorres wp: prev_list_head_other hoare_vcg_if_lift2 hoare_vcg_const_imp_lift)
   apply clarsimp
  apply (rcorres_conj_lift clarsimp simp: breakReplyChainAt_def breakReplyChainAt'_def)+
  done

lemma breakReplyChainAt_corres:
  "reply_ptr = replyPtr \<Longrightarrow>
   corres dc
     (reply_at reply_ptr and valid_objs and pspace_aligned and pspace_distinct and valid_replies
      and (\<lambda>s. sym_refs (state_refs_of s)))
     (valid_objs' and sym_heap_reply_pointers)
     (break_reply_chain_at reply_ptr) (breakReplyChainAt replyPtr)"
  supply if_split[split del] heap_path_append[simp del]
         update_sched_context_det_wp_weak[wp] update_sched_context_no_fail_weak[wp]
  apply add_pspace_adb'
  apply (rule_tac Q'="reply_at' replyPtr" in corres_cross_add_guard)
   apply (fastforce intro: reply_at_cross)
  apply (clarsimp simp: break_reply_chain_at_def)
  apply (rule corres_symb_exec_l[OF _ _ gets_sp]; (solves wpsimp)?)
  apply (rename_tac sc_ptr_opt)
  apply (case_tac sc_ptr_opt; clarsimp)
   apply (corres corres: breakReplyChainAt_not_in_reply_stack_corres)
  \<comment> \<open>replyPtr is in the reply stack of some scheduling context\<close>
  apply (clarsimp simp: breakReplyChainAt_def liftM_def)
  apply (rename_tac scPtr)
  apply (rule_tac Q="sc_at scPtr" in corres_cross_add_abs_guard)
   apply (fastforce dest: sc_with_reply_Some_sc_at)
  apply (rule corres_symb_exec_l[OF _ get_sched_context_exs_valid get_sched_context_sp , rotated])
    apply (fastforce dest: sc_atD1)
   apply wpsimp
   apply (fastforce dest: sc_atD1)
  apply (rename_tac sc)
  apply (rule corres_symb_exec_r[OF _ get_reply_sp']; (solves wpsimp)?)
  apply (rename_tac reply')
  apply (rule_tac Q="\<lambda>s. reply_sc_reply_at
                           ((=) (if hd (sc_replies sc) = replyPtr then Some scPtr else None))
                           reply_ptr s"
               in corres_cross_add_abs_guard)
  apply (clarsimp split: if_splits)
   apply (intro conjI impI)
    apply (force dest!: sym_refs_reply_sc_reply_at sc_with_reply_SomeD
                intro!: list.collapse
                  simp: sc_at_ppred_def obj_at_def)
   apply (force dest!: reply_not_head_reply_sc_None sc_with_reply_SomeD1
                 simp: sc_at_ppred_def obj_at_def)
  apply (rule_tac P="\<lambda>_. reply_at replyPtr and pspace_aligned and pspace_distinct"
              and P'="\<lambda>_ _. replyPtr = hd (sc_replies sc) \<longleftrightarrow> (replySC reply' \<noteq> None)"
               in corres_underlying_split_ex_abs[where r=dc and r'=dc, rotated 2])
     apply wpsimp
    apply wpsimp
    apply (force dest: replies_relation_reply_relation_conc state_relation_pspace_relation
                 simp: ex_abs_def pspace_relation_heap_pspace_relation reply_at_ppred_def obj_at_def
                       obj_at'_def reply_relation_def
                split: if_splits)
   apply (rule corres_underlying_from_rcorres; (solves wpsimp)?)
   apply (clarsimp simp: state_relation_def ghost_relation_heap_ghost_relation
                         pspace_relation_heap_pspace_relation heap_pspace_relation_def)
   apply (rcorres_conj_lift \<open>clarsimp split: if_splits\<close>
                            wp: update_sched_context_field_inv updateSchedContext_field_inv
                                hoare_vcg_if_lift2
                            simp: breakReplyChainAt'_def)+
   apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
    \<comment> \<open>sc_replies_relation\<close>
    apply (clarsimp simp: update_sched_context_def breakReplyChainAt'_def)
    apply (rule rcorres_symb_exec_l[OF get_object_sp get_object_exs_valid])
     apply (clarsimp simp: obj_at_def)
    apply (rename_tac ko)
    apply (case_tac ko; clarsimp;
           (solves \<open>rcorres rcorres: rcorres_fail, clarsimp simp: obj_at_def is_sc_obj_def\<close>)?)
    apply (rename_tac abs_sc n)
    apply (rule_tac F="abs_sc = sc" in rcorres_req)
     apply (clarsimp simp: obj_at_def)
    apply (rule_tac Q="\<lambda>s _. sc_obj_at n scPtr s" in rcorres_add_to_pre)
     apply (clarsimp simp: obj_at_def is_sc_obj_def)
    apply (rule rcorres_symb_exec_r[OF get_reply_sp'])
    apply (rename_tac reply')
    apply (rule_tac F="\<forall>ptr. replySC reply' = Some ptr \<longrightarrow> ptr = scPtr" in rcorres_req)
     apply (fastforce dest!: replies_relation_reply_relation_abs_obj_at'
                       simp: obj_at'_def reply_relation_def reply_at_ppred_def obj_at_def
                      split: if_splits)
    apply (simp only: sc_replies_relation_def)
    apply (rule rcorres_allI_fwd; (solves wpsimp)?)
    apply (rename_tac p)
    apply (case_tac "p \<noteq> scPtr")
     apply (intro rcorres_allI_fwd; (solves wpsimp)?)
     apply (rule rcorres_imp_lift_fwd)
      apply (rcorres wp: set_sched_context_scs_of_other)
      apply clarsimp
     apply (rule rcorres_imp_lift_fwd)
      apply (rcorres wp: updateSchedContext_scs_of'_other hoare_vcg_if_lift2)
      apply fastforce
     apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
      apply (rcorres wp: updateReply_heap_ls_other hoare_vcg_if_lift2 hoare_vcg_const_imp_lift)
      apply normalise_obj_at'
      apply (prop_tac "replyPtr \<in> set (sc_replies sc)")
       apply (force dest!: sc_with_reply_SomeD simp: obj_at_def)
      apply (prop_tac "sc_replies_of s scPtr = Some (sc_replies sc)")
       apply (clarsimp simp: scs_of_kh_def opt_map_red obj_at_def)
      apply (frule (3) sc_replies_disjoint)
      apply (drule_tac x=scPtr in spec)+
      apply (rule drop_imp)
      subgoal
        by (auto dest!: heap_ls_neighbour_in_set
                  simp: prev_list_head_def obj_at_def opt_map_red obj_at'_def)
     apply (rcorres wp: prev_list_head_other hoare_vcg_if_lift2 hoare_vcg_const_imp_lift)
     apply (clarsimp split: if_splits)
    \<comment> \<open>p = sc_ptr\<close>
    apply (case_tac "replyPtr \<noteq> hd (sc_replies sc)")
     \<comment> \<open>replyPtr is not the head of the list; takeWhile until the first occurrence of replyPtr\<close>
     apply (rule_tac F="replySC reply' = None" in rcorres_req)
      apply (fastforce dest: replies_relation_reply_relation_abs_obj_at'
                       simp: reply_at_ppred_def obj_at_def reply_relation_def obj_at'_def)
     apply (rule_tac Q="\<lambda>_ s'. list_linked_list_relation
                                 (sc_replies sc) (scReplies_of s' scPtr)
                                 (replyPrevs_of s') (replyNexts_of s')"
                  in rcorres_add_to_pre)
      apply (clarsimp simp: scs_of_kh_def opt_map_red obj_at_def)
     apply (rule_tac F="\<exists>next. replyNext reply' = Some next" in rcorres_req)
      apply (force dest!: sc_with_reply_SomeD not_head_prev_not_None[where p=replyPtr]
                    simp: obj_at'_def obj_at_def opt_map_red)
     apply (rule rcorres_from_valid_det; (solves wpsimp)?)
     apply (drule in_set_object)
     apply (clarsimp simp: all_conj_distrib imp_conjR)
     apply (rule hoare_vcg_conj_lift_pre_fix)
      apply (wpsimp wp: updateReply_wp)
      apply (drule obj_at'_prop)+
      apply (frule sc_with_reply_SomeD1)
      apply (clarsimp simp: obj_at_def scs_of_kh_def sc_at_ppred_def)
      apply (frule split_list)
      apply clarsimp
      apply (rename_tac ys zs)
      apply (prop_tac "ys \<noteq> []", fastforce)
      apply (frule (1) heap_ls_neighbour_in_set[where p=replyPtr])
        apply (clarsimp simp: prev_list_head_def)
       apply fastforce
      apply (frule heap_path_head)
       apply fastforce
      apply (frule (2) heap_path_sym_heap_non_nil_lookup_prev)
      apply (clarsimp split: if_splits)
      apply (drule (1) heap_ls_takeWhile_not_hd)
      apply (frule (1) valid_sched_context_objsI)
      apply (prop_tac "scPtr \<noteq> last ys")
       apply (clarsimp simp: valid_sched_context_def obj_at_def is_reply)
       apply (force dest: last_in_set simp: list_all_iff)
      apply (intro conjI impI allI)
       \<comment> \<open>replyPtr is not the end of the list\<close>
       apply (drule obj_at'_prop)+
       apply clarsimp
       subgoal
         by (auto intro: heap_path_heap_upd_not_in
                   dest: set_takeWhileD
                   simp: opt_map_upd_triv opt_map_red scs_of_kh_def projectKO_opts_defs
                  split: if_splits)
      \<comment> \<open>replyPtr is end of the list\<close>
      apply (clarsimp simp: scs_of_kh_def opt_map_red projectKO_opts_defs obj_at'_def
                     split: if_splits)
     apply (rule_tac f="\<lambda>s'. scReplies_of s' scPtr" in hoare_lift_Pf2[rotated])
      apply wpsimp
     apply (wpsimp wp: prev_list_head_other hoare_vcg_if_lift2 hoare_vcg_const_imp_lift)
     apply (clarsimp split: if_splits)
    \<comment> \<open>replyPtr is the head of the list\<close>
    apply (rule_tac F="replySC reply' = Some scPtr" in rcorres_req)
     apply (fastforce dest: replies_relation_reply_relation_abs_obj_at'
                      simp: reply_at_ppred_def obj_at_def reply_relation_def obj_at'_def)
    apply (rule rcorres_from_valid_det; (solves wpsimp)?)
    apply (wpsimp wp: updateReply_wp updateSchedContext_wp)
    apply (drule in_set_object)
    apply (clarsimp simp: scs_of_kh_def prev_list_head_def split: if_splits)
   apply ((rcorres_conj_lift clarsimp wp: hoare_vcg_if_lift2 simp: breakReplyChainAt'_def)+)[1]
  apply (clarsimp simp: when_def)
  apply (rule corres_if_strong')
    apply fastforce
   apply (corres corres: updateReply_corres simp: reply_relation_def)
  apply clarsimp
  done

lemma replyRemoveTCB_corres:
  "corres dc
     (valid_objs and pspace_aligned and pspace_distinct and valid_replies
      and st_tcb_at ((=) (Structures_A.thread_state.BlockedOnReply rp)) t
      and (\<lambda>s. sym_refs (state_refs_of s)))
     (valid_objs' and sym_heap_reply_pointers)
     (reply_remove_tcb t rp) (replyRemoveTCB t)"
  apply add_pspace_adb'
  apply add_sym_refs
  apply (rule_tac Q'="st_tcb_at' ((=) (BlockedOnReply (Some rp))) t" in corres_cross_add_guard)
   apply (fastforce dest!: st_tcb_at_coerce_concrete elim!: pred_tcb'_weakenE)
  apply (rule_tac Q="reply_at rp" in corres_cross_add_abs_guard)
   apply (fastforce dest: st_tcb_at_valid_st2)
  apply (clarsimp simp: reply_remove_tcb_def replyRemoveTCB_def isReply_def)
  apply (rule corres_stateAssert_ignore, simp)
  apply (rule corres_split_forwards'[OF _ gts_sp gts_sp'])
   apply (corres corres: getThreadState_corres)
  apply (rename_tac ts state)
  apply (rule corres_assert_assume_l_forward)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (rename_tac state)
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (case_tac state; clarsimp)
  apply (rule corres_assert_opt_assume[rotated])
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def split: thread_state.splits)
  apply (rename_tac rptr)
  apply (rule_tac F="rptr = rp" in corres_req)
   apply clarsimp
  apply clarsimp
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF breakReplyChainAt_corres], simp)
      apply (rule replyUnlink_corres)
     apply (wpsimp simp: break_reply_chain_at_def wp: get_sk_obj_ref_wp)
    apply ((wpsimp | strengthen valid_objs'_valid_tcbs')+)[1]
   apply clarsimp
   apply (frule (1) st_tcb_reply_state_refs)
   apply (force simp: reply_at_ppred_def pred_tcb_at_def obj_at_def)
  apply fastforce
  done

lemma replyPop'_corres:
  "corres dc
     (\<lambda>s. reply_at replyPtr s \<and> sc_at scPtr s \<and> (\<exists>ls. sc_replies_of s scPtr = Some (replyPtr # ls))
          \<and> valid_replies s \<and> valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s )
     (\<lambda>s'. valid_objs' s' \<and> sym_heap_reply_pointers s' \<and> is_replyObject replyPtr s'
           \<and> replyPrevs_of s' replyPtr = prevReplyOpt)
     (update_sched_context scPtr (sc_replies_update tl))
     (replyPop' replyPtr scPtr prevReplyOpt)"
  supply if_split[split del] heap_path_append[simp del]
         update_sched_context_det_wp_weak[wp] update_sched_context_no_fail_weak[wp]
  apply add_pspace_adb'
  apply (rule_tac Q="sc_at scPtr" in corres_cross_add_abs_guard)
   apply (fastforce dest: sc_with_reply_Some_sc_at)
  apply (rule_tac Q'="sc_at' scPtr" in corres_cross_add_guard)
   apply (fastforce intro: sc_at_cross)
  apply (rule_tac Q'="reply_at' replyPtr" in corres_cross_add_guard)
   apply (fastforce intro: reply_at_cross)
  apply (clarsimp simp: pred_conj_def)
  apply (rule_tac Q="\<lambda>s. \<exists>sc n. kheap s scPtr = Some (Structures_A.SchedContext sc n)"
               in corres_cross_add_abs_guard)
   apply (fastforce dest: sc_atD1)
  apply (subst pred_conj_comm)
  apply (rule corres_underlying_lift_ex1)
  apply (rename_tac sc)
  apply (rule_tac F="replyPtr = hd (sc_replies sc)" in corres_req)
   apply (clarsimp simp: scs_of_kh_def opt_map_def obj_at_def)
  apply (rule_tac Q'="\<lambda>s'. scReplies_of s' scPtr = Some replyPtr" in corres_cross_add_guard)
   apply (fastforce dest: state_relation_sc_replies_relation sc_replies_relation_scReplies_of
                    simp: opt_map_red obj_at'_def)
  apply (rule_tac Q'="\<lambda>s. heap_ls (replyPrevs_of s) (scReplies_of s scPtr) (sc_replies sc)"
               in corres_cross_add_guard)
   apply (fastforce dest!: state_relation_sc_replies_relation spec[where x=scPtr]
                     simp: sc_replies_relation_def scs_of_kh_def opt_map_red)
  apply (rule_tac Q'="\<lambda>s'. (tl (sc_replies sc) = [] \<longleftrightarrow> (replyPrevs_of s' replyPtr = None))"
               in corres_cross_add_guard)
   apply (case_tac "sc_replies sc"; fastforce)
  apply (rule_tac Q'="\<lambda>s'. \<forall>p. tl (sc_replies sc) \<noteq> [] \<and> hd (tl (sc_replies sc)) = p
                               \<longrightarrow> replyPrevs_of s' replyPtr = Some p"
               in corres_cross_add_guard)
   apply clarsimp
   apply (frule heap_ls_distinct)
   apply (frule (1) heap_ls_next_of_hd)
    apply (case_tac "sc_replies sc"; clarsimp)
   apply (clarsimp simp: opt_map_red obj_at_def obj_at'_def)
  apply (rule corres_underlying_from_rcorres)
   apply (wpsimp simp: replyPop'_def replyPop'_asrt_def
                   wp: no_fail_stateAssert hoare_vcg_if_lift2 hoare_vcg_const_imp_lift)
   apply (intro conjI impI)
      apply (fastforce dest: state_relation_sc_replies_relation
                       simp: sc_replies_relation_def prev_list_head_def)
     apply normalise_obj_at'
     apply (frule (1) reply_ko_at_valid_objs_valid_reply')
     apply (force simp: valid_reply'_def opt_map_red obj_at'_def)
    apply (clarsimp simp: in_opt_pred opt_map_red obj_at'_def)
   apply (clarsimp simp: in_opt_pred opt_map_red obj_at'_def)
  apply (clarsimp simp: state_relation_def ghost_relation_heap_ghost_relation
                        pspace_relation_heap_pspace_relation heap_pspace_relation_def)
  apply (rcorres_conj_lift clarsimp
                           wp: update_sched_context_field_inv updateReply_field_inv
                               updateSchedContext_field_inv
                           simp: replyPop'_def)+
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   apply (clarsimp simp: update_sched_context_def replyPop'_def)
   apply (rule rcorres_symb_exec_l[OF get_object_sp get_object_exs_valid])
    apply (clarsimp simp: obj_at_def)
   apply (rename_tac ko)
   apply (case_tac ko; clarsimp;
          (solves \<open>rcorres rcorres: rcorres_fail, clarsimp simp: obj_at_def is_sc_obj_def\<close>)?)
   apply (rename_tac n)
   apply (rule_tac Q="\<lambda>s _. sc_obj_at n scPtr s" in rcorres_add_to_pre)
    apply (clarsimp simp: obj_at_def is_sc_obj_def)
   apply (simp only: sc_replies_relation_def)
   apply (rule rcorres_allI_fwd; (solves wpsimp)?)
   apply (rename_tac p)
   apply (case_tac "p \<noteq> scPtr")
    apply (intro rcorres_allI_fwd; (solves wpsimp)?)
    apply (rule rcorres_imp_lift_fwd)
     apply (rcorres wp: set_sched_context_scs_of_other)
     apply clarsimp
    apply (rule rcorres_imp_lift_fwd)
     apply (rcorres wp: updateSchedContext_scs_of'_other hoare_vcg_if_lift2)
     apply fastforce
    apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
     apply (rcorres wp: updateReply_heap_ls_other hoare_vcg_const_imp_lift)
     apply clarsimp
     apply (frule (3) sc_replies_disjoint)
     apply force
    apply (rcorres wp: prev_list_head_other hoare_vcg_if_lift2 hoare_vcg_const_imp_lift)
    apply clarsimp
   \<comment> \<open>p = scPtr\<close>
   apply (clarsimp simp: all_conj_distrib imp_conjR)
   apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
    apply (rule rcorres_from_valid_det; (solves wpsimp)?)
    apply (drule in_set_object)
    apply (case_tac "prevReplyOpt = None"; clarsimp)
     \<comment> \<open>the reply stack was originally a singleton\<close>
     apply (wpsimp wp: updateReply_wp updateSchedContext_wp)
     apply (clarsimp simp: scs_of_kh_def obj_at_def opt_map_red obj_at'_def)
    \<comment> \<open>the reply stack was not originally a singleton\<close>
    apply (rename_tac prevPtr)
    apply (wpsimp wp: updateReply_wp updateSchedContext_wp)
    apply normalise_obj_at'
    apply (drule_tac x=scPtr in spec)+
    apply (drule_tac x="hd (sc_replies sc) # ls" in spec)
    apply (clarsimp simp: opt_map_red obj_at'_def)
    apply (clarsimp simp: projectKO_opts_defs)
    apply (prop_tac "ls \<noteq> []")
     apply (force dest: heap_path_last_end simp: opt_map_red obj_at'_def)
    apply (prop_tac "hd (sc_replies sc) \<noteq> hd (tl (sc_replies sc))")
     apply (frule heap_ls_distinct)
     apply (case_tac "sc_replies sc"; clarsimp)
    apply (drule (1) heap_ls_remove_head_not_singleton)
    apply (prop_tac "sc_replies_of s scPtr = Some (sc_replies sc)")
     apply (clarsimp simp: scs_of_kh_def opt_map_red obj_at_def)
    apply (clarsimp simp: scs_of_kh_def)
    apply (rule heap_path_heap_upd_not_in[where r=scPtr])
     apply (erule_tac c="tl (sc_replies sc)" in heap_ls_cong)
       apply (subst fun_upd_swap)
        apply clarsimp
       apply (fastforce simp: opt_map_upd_triv scs_of_kh_def opt_map_red obj_at_def obj_at'_def)
      apply (fastforce dest: heap_path_head)
     apply (case_tac "sc_replies sc"; clarsimp simp: obj_at_def)
    apply (clarsimp simp: obj_at_def)
    apply (frule (1) valid_sched_context_objsI)
    apply (clarsimp simp: valid_sched_context_def list_all_iff is_sc_obj_def)
    apply (force dest!: bspec[where x=scPtr] intro!: list.set_sel
                  simp: obj_at_def is_reply)
   apply (rule rcorres_from_valid_det; (solves wpsimp)?)
   apply (drule in_set_object)
   apply (wpsimp wp: updateReply_wp updateSchedContext_wp)
   apply (force simp: projectKO_opts_defs prev_list_head_def split: if_splits)
  by (rcorres_conj_lift clarsimp simp: replyPop'_def)+

lemma replyPop_corres:
  "corres dc
     (\<lambda>s. reply_at replyPtr s \<and> sc_at scPtr s \<and> (\<exists>ls. sc_replies_of s scPtr = Some (replyPtr # ls))
          \<and> valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_replies s
          \<and> sym_refs (state_refs_of s))
     (valid_objs' and sym_heap_reply_pointers)
     (reply_pop replyPtr scPtr) (replyPop replyPtr)"
  supply if_split[split del]
  apply add_pspace_adb'
  apply (rule_tac Q'="reply_at' replyPtr" in corres_cross_add_guard)
   apply (fastforce intro: reply_at_cross)
  apply (clarsimp simp: reply_pop_def replyPop_def liftM_def)
  apply (rule corres_symb_exec_l[OF _ get_sched_context_exs_valid get_sched_context_sp, rotated])
    apply (fastforce dest: sc_atD1)
   apply wpsimp
   apply (fastforce dest: sc_atD1)
  apply (rename_tac sc)
  apply (rule corres_assert_assume_l_forward)
   apply (clarsimp simp: scs_of_kh_def obj_at_def opt_map_red)
  apply (rule corres_symb_exec_r[OF _ get_reply_sp']; (solves wpsimp)?)
  apply (rename_tac reply')
  apply (rule_tac Q="reply_sc_reply_at ((=) (Some scPtr)) replyPtr" in corres_cross_add_abs_guard)
   apply (force dest!: sym_refs_reply_sc_reply_at intro!: list.collapse
                 simp: sc_at_ppred_def obj_at_def)
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (force dest!: state_relation_pspace_relation replies_relation_reply_relation_abs
                 simp: reply_relation_def reply_at_ppred_def obj_at'_def obj_at_def
                       pspace_relation_heap_pspace_relation)
  apply clarsimp
  apply (rename_tac scPtr')
  apply (rule_tac F="scPtr' = scPtr" in corres_req)
   apply (force dest!: state_relation_pspace_relation replies_relation_reply_relation_abs
                 simp: reply_relation_def reply_at_ppred_def obj_at'_def obj_at_def
                       pspace_relation_heap_pspace_relation)
  apply (rule_tac Q'="\<lambda>s. heap_ls (replyPrevs_of s) (scReplies_of s scPtr) (sc_replies sc)"
               in corres_cross_add_guard)
   apply (fastforce dest!: state_relation_sc_replies_relation spec[where x=scPtr]
                     simp: sc_replies_relation_def scs_of_kh_def opt_map_def obj_at_def)
  apply (rule_tac F="(tl (sc_replies sc) = [] \<longleftrightarrow> (replyPrev reply' = None))"
               in corres_req)
   apply (case_tac "sc_replies sc";
          force dest: heap_path_not_Nil heap_ls_last_None
                simp: opt_map_red obj_at'_def)
  apply (rule_tac F="\<forall>p. tl (sc_replies sc) \<noteq> [] \<and> hd (tl (sc_replies sc)) = p
                         \<longrightarrow> replyPrev reply' = Some p"
               in corres_req)
   apply clarsimp
   apply (frule (1) heap_ls_next_of_hd)
    apply (fastforce elim: tail_nonempty_length)
   apply (fastforce simp: opt_map_red obj_at'_def)
  apply (subst list_case_If2)
  apply (subst if_swap)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF updateReply_corres]; clarsimp simp: reply_relation_def)
      apply (rule corres_split[OF replyPop'_corres])
        apply (simp only: when_def)
        apply (rule corres_if_strong[where R=\<top> and R'=\<top>])
          apply (rule refl)
         apply clarsimp
         apply (rule corres_assert_assume_r)
         apply (rule updateReply_corres[unfolded dc_def]; clarsimp simp: reply_relation_def)
        apply (rule corres_return_trivial)
       apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_if_lift2)
      apply (wpsimp wp: hoare_vcg_if_lift2)
     apply (rule_tac Q'="\<lambda>_ s. reply_at replyPtr s \<and> sc_at scPtr s
                               \<and> (\<exists>ls. sc_replies_of s scPtr = Some (replyPtr # ls))
                               \<and> valid_replies s \<and> valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s
                               \<and> (tl (sc_replies sc) \<noteq> [] \<longrightarrow> reply_at (hd (tl (sc_replies sc))) s)"
                  in hoare_post_imp)
      apply (clarsimp simp: reply_at_ppred_def obj_at_def is_reply)
     apply wpsimp
     apply (wpsimp wp: update_reply_wp)
    apply (wpsimp wp: sym_heap_reply_pointers_lift updateReply_field_inv hoare_vcg_ex_lift)
   apply (force dest!: valid_sched_context_objsI
                 simp: valid_sched_context_def list_all_iff obj_at_def list.set_sel)
  apply clarsimp
  apply (drule_tac p="hd (sc_replies sc)" in heap_ls_no_loops)
   apply fastforce
  apply (fastforce intro!: is_replyObject_cross simp: opt_map_red obj_at'_def)
  done

lemma replyPop_valid_objs'[wp]:
  "replyPop replyPtr \<lbrace>valid_objs'\<rbrace>"
  unfolding replyPop_def replyPop'_def
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_const_imp_lift stateAssert_inv)
  apply (fastforce dest: reply_ko_at_valid_objs_valid_reply' simp: valid_reply'_def)
  done

crunch reply_pop
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  and ready_queues_runnable[wp]: ready_queues_runnable
  and release_q_runnable[wp]: release_q_runnable
  and ep_queues_blocked[wp]: ep_queues_blocked
  and ntfn_queues_blocked[wp]: ntfn_queues_blocked
  (wp: in_correct_ready_q_lift ready_qs_distinct_lift ready_queues_runnable_lift
       release_q_runnable_lift ep_queues_blocked_lift ntfn_queues_blocked_lift)

lemma replyRemove_corres:
  "\<lbrakk>st = Structures_A.thread_state.BlockedOnReply rp; st' = BlockedOnReply (Some rp)\<rbrakk> \<Longrightarrow>
   corres dc
     (valid_objs and pspace_aligned and pspace_distinct and valid_replies
      and weak_valid_sched_action and active_scs_valid and valid_release_q and valid_ready_qs
      and ready_or_release and st_tcb_at ((=) st) t and (\<lambda>s. sym_refs (state_refs_of s)))
     (valid_objs' and sym_heap_sched_pointers and valid_sched_pointers and sym_heap_reply_pointers
      and K (rp' = rp))
     (reply_remove t rp) (replyRemove rp' t)"
  apply (rule corres_gen_asm2')
  apply add_pspace_adb'
  apply add_sym_refs
  apply (rule_tac Q'="st_tcb_at' ((=) st') t" in corres_cross_add_guard)
   apply (fastforce dest!: st_tcb_at_coerce_concrete elim!: pred_tcb'_weakenE)
  apply (rule_tac Q="reply_at rp" in corres_cross_add_abs_guard)
   apply (fastforce dest: st_tcb_at_valid_st2)
  apply (rule_tac Q'="reply_at' rp" in corres_cross_add_guard)
   apply (fastforce intro!: reply_at_cross)
  apply (clarsimp simp: reply_remove_def replyRemove_def)
  apply (rule corres_stateAssert_ignore, clarsimp)
  apply (rule corres_split_forwards'[OF _ get_simple_ko_sp get_reply_sp'])
   apply (corres corres: get_reply_corres)
  apply (rename_tac reply reply')
  apply (rule corres_assert_assume_l_forward)
   apply (fastforce dest: st_tcb_reply_state_refs simp: reply_at_ppred_def obj_at_def)
  apply (rule corres_gen_asm')
  apply (rule corres_assert_opt_assume[rotated])
   apply (clarsimp simp: reply_relation_def)
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (clarsimp simp: reply_relation_def)
  apply (rule corres_symb_exec_r[OF _ gts_sp']; (solves wpsimp)?)
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def isReply_def)
   apply (rename_tac obj, case_tac "tcbState obj"; clarsimp)
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def isReply_def replyObject_def)
   apply (rename_tac obj, case_tac "tcbState obj"; clarsimp)
  apply (rule corres_symb_exec_l[OF _ _ gets_sp]; (solves wpsimp)?)
  apply (rule corres_split_forwards'[OF _ _ _ replyUnlink_corres, where r'=dc])
    apply (case_tac r_sc_opt; clarsimp)
     apply (rule_tac F="replySC reply' = None" in corres_req)
      apply (force dest!: sc_with_reply_None_reply_sc_reply_at
                    simp: reply_at_ppred_def obj_at_def reply_relation_def)
     apply clarsimp
     apply (corres corres: breakReplyChainAt_not_in_reply_stack_corres)
    \<comment> \<open>rp was originally in the reply stack of some scheduling context\<close>
    apply (rename_tac sc_ptr)
    apply (rule_tac Q="sc_at sc_ptr" in corres_cross_add_abs_guard)
     apply (fastforce dest: sc_with_reply_Some_sc_at)
    apply (clarsimp simp: liftM_def)
    apply (rule corres_symb_exec_l[OF _ get_sched_context_exs_valid get_sched_context_sp, rotated])
      apply (fastforce dest: sc_atD1)
     apply wpsimp
     apply (fastforce dest: sc_atD1)
    apply (rename_tac sc)
    apply (case_tac "rp \<noteq> hd (sc_replies sc)"; clarsimp)
     apply (rule_tac F="replySC reply' = None" in corres_req)
      apply clarsimp
      apply (frule_tac sc_ptr=sc_ptr in reply_not_head_reply_sc_None[rotated 3]; fastforce?)
       apply (fastforce dest: sc_with_reply_SomeD simp: sc_at_ppred_def obj_at_def)
      apply (clarsimp simp: reply_at_ppred_def obj_at_def reply_relation_def)
     apply clarsimp
     apply (rule corres_bind_return2)
     apply (corres corres: breakReplyChainAt_corres)
         apply (rule corres_symb_exec_l)
            apply (wpsimp simp: get_tcb_obj_ref_def)+
    apply (rule_tac F="replySC reply' = Some sc_ptr" in corres_req)
     apply (force dest!: sc_with_reply_SomeD1 sym_refs_reply_sc_reply_at
                 intro!: list.collapse
                   simp: sc_at_ppred_def reply_relation_def reply_at_ppred_def obj_at_def)
    apply (clarsimp simp: get_tcb_obj_ref_def)
    apply (rule stronger_corres_guard_imp)
      apply (rule corres_split[OF replyPop_corres], simp)
        apply (rule corres_split[OF threadGet_corres, where r'="(=)"])
           apply (clarsimp simp: tcb_relation_def)
          apply (rule corres_when[OF _ schedContextDonate_corres])
          apply fastforce
         apply (wpsimp wp: thread_get_inv threadGet_inv hoare_drop_imps)+
     apply (case_tac "sc_replies sc";
            fastforce dest!: sc_with_reply_SomeD simp: scs_of_kh_def obj_at_def opt_map_def)
    apply fastforce
   apply ((wpsimp wp: thread_get_inv hoare_vcg_if_lift2 simp: get_tcb_obj_ref_def
           | wp (once) hoare_drop_imps
           | strengthen valid_objs_valid_tcbs)+)[1]
   apply (fastforce elim: pred_tcb_weakenE simp: reply_at_ppred_def obj_at_def)
  apply ((wpsimp wp: hoare_drop_imps hoare_vcg_if_lift2 | strengthen valid_objs'_valid_tcbs')+)[1]
  done

lemma sched_context_donate_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action and bound_sc_tcb_at ((=) None) tcb_ptr\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (wpsimp wp: thread_set_wp update_sched_context_wp test_reschedule_wp
                    tcb_sched_action_wp get_sc_obj_ref_wp
              simp: sched_context_donate_def tcb_release_remove_def)
  apply (frule weak_valid_sched_action_no_sc_sched_act_not)
   apply (fastforce simp: vs_all_heap_simps tcb_at_kh_simps)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps fun_upd_def pred_map_simps tcb_sched_dequeue_def scheduler_act_not_def
                 valid_sched_action_def weak_valid_sched_action_def opt_map_simps map_join_simps
           cong: conj_cong)

crunch sched_context_donate
  for sc_at[wp]: "sc_at scp"
  (simp: crunch_simps wp: crunch_wps)

crunch sched_context_donate, update_reply, update_sched_context
  for ep_queues_blocked[wp]: ep_queues_blocked
  and ntfn_queus_blocked[wp]: ntfn_queues_blocked
  (wp: ep_queues_blocked_lift ntfn_queues_blocked_lift)

lemma get_tcb_obj_ref_exs_valid[wp]:
  "\<exists>tcb. kheap s tp = Some (Structures_A.TCB tcb)
   \<Longrightarrow> \<lbrace>(=) s\<rbrace> get_tcb_obj_ref f tp \<exists>\<lbrace>\<lambda>_. (=) s\<rbrace>"
  by (clarsimp simp: get_tcb_obj_ref_def thread_get_def gets_the_def get_tcb_def bind_def
                     gets_def get_def return_def exs_valid_def
              split: Structures_A.kernel_object.splits)

lemma cancel_ipc_corres:
  "corres dc
     (invs and valid_ready_qs and valid_release_q and ready_or_release and tcb_at t) invs'
     (cancel_ipc t) (cancelIPC t)"
  apply add_sym_refs
  apply add_ready_qs_runnable
  apply (rule_tac Q'="tcb_at' t" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: tcb_at_cross)
  apply (simp add: cancel_ipc_def cancelIPC_def Let_def)
  apply (rule corres_stateAssert_add_assertion[rotated], clarsimp)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getThreadState_corres])
      apply (rule corres_split[OF ])
         apply (rule threadSet_corres; (simp add: inQ_def)?)
         apply (clarsimp simp: tcb_relation_def fault_rel_optionation_def)
        apply (rule_tac P="invs and valid_release_q and valid_ready_qs and ready_or_release
                           and st_tcb_at ((=) state) t" and
                        P'="invs' and st_tcb_at' ((=) statea) t" in corres_inst)
        apply (case_tac state, simp_all add: isTS_defs list_case_If gbep_ret')[1]
           apply (rule corres_guard_imp)
             apply (rename_tac epPtr reply pl)
             apply (rule_tac st = "Structures_A.thread_state.BlockedOnReceive epPtr reply pl"
                    in blocked_cancelIPC_corres[simplified])
               apply simp
              apply (clarsimp simp: thread_state_relation_def)
             apply simp+
            apply fastforce
           apply (clarsimp simp: invs'_implies)
          apply (rule corres_guard_imp)
            apply (rename_tac epPtr data)
            apply (rule_tac st = "Structures_A.thread_state.BlockedOnSend epPtr data"
                   in blocked_cancelIPC_corres[where reply_opt=None, simplified])
             apply simp
            apply (clarsimp simp: thread_state_relation_def)
           apply (fastforce simp: invs_implies)
          apply (clarsimp simp: invs'_implies)
         apply (rule corres_guard_imp)
           apply (rule replyRemoveTCB_corres)
          apply simp
          apply (clarsimp simp: thread_state_relation_def)
          apply (clarsimp simp: invs_implies)
         apply (clarsimp simp: invs'_implies)
        apply (rule corres_guard_imp)
          apply (rule cancelSignal_corres)
         apply fastforce
        apply simp
       apply (wpsimp wp: thread_set_invs_fault_None thread_set_valid_ready_qs
                         thread_set_no_change_tcb_state)
      apply (wpsimp wp: threadSet_pred_tcb_no_state threadSet_invs_trivial)+
     apply (wp gts_sp[where P="\<top>", simplified])+
    apply (rule hoare_strengthen_post)
     apply (rule gts_sp'[where P="\<top>"])
    apply (clarsimp elim!: pred_tcb'_weakenE)
   apply fastforce
  apply (clarsimp simp: inQ_def obj_at'_def)
  done

declare cart_singleton_empty [simp]
declare cart_singleton_empty2[simp]

lemma sch_act_simple_not_t[simp]: "sch_act_simple s \<Longrightarrow> sch_act_not t s"
  by (clarsimp simp: sch_act_simple_def)

crunch tcbNTFNDequeue, tcbEPDequeue
  for valid_replies'[wp]: valid_replies'
  and valid_irq_handlers'[wp]: valid_irq_handlers'
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  (wp: crunch_wps simp: crunch_simps)

crunch tcbEPAppend, tcbNTFNAppend
  for valid_replies'[wp]: valid_replies'
  (wp: crunch_wps valid_irq_handlers_lift' simp: crunch_simps)

lemma tcbNTFNDequeue_valid_sched_pointers[wp]:
  "tcbNTFNDequeue tcbPtr ntfnPtr \<lbrace>valid_sched_pointers\<rbrace>"
  unfolding tcbNTFNDequeue_def
  apply (wpsimp wp: tcbQueueRemove_valid_sched_pointers hoare_drop_imps)
  apply (clarsimp simp: valid_sched_pointers_except_def)
  done

lemma tcbNTFNDequeue_not_sched_linked[wp]:
  "\<lbrace>\<top>\<rbrace> tcbNTFNDequeue t ntfn \<lbrace>\<lambda>_ s. \<not> is_sched_linked t s\<rbrace>"
  unfolding tcbNTFNDequeue_def
  by (wpsimp wp: tcbQueueRemove_not_sched_linked[simplified])

crunch tcbNTFNDequeue, tcbNTFNAppend, tcbEPDequeue, tcbEPAppend
  for untyped_ranges_zero'[wp]: untyped_ranges_zero'
  (wp: threadSet_urz crunch_wps ignore: threadSet)

lemma setThreadState_sched_pointers_valid_sched_pointers:
  "\<lbrace>\<lambda>s. valid_sched_pointers s \<and> \<not> is_sched_linked t s\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  unfolding setThreadState_def
  by (wpsimp wp: tcbState_update_valid_sched_pointers)

lemma cancelSignal_invs':
  "\<lbrace>invs' and st_tcb_at' (\<lambda>st. st = BlockedOnNotification ntfn) t\<rbrace>
   cancelSignal t ntfn
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: cancelSignal_def invs'_def valid_pspace'_def Let_def)
  apply (intro bind_wp[OF _ stateAssert_sp])
  apply (wp valid_irq_node_lift irqs_masked_lift valid_dom_schedule'_lift hoare_vcg_all_lift
            hoare_vcg_imp_lift' setThreadState_sched_pointers_valid_sched_pointers sts'_valid_replies')
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

crunch cancelIPC
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and ksMachineState[wp]: "\<lambda>s. P (ksMachineState s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and ksDomScheduleStart[wp]: "\<lambda>s. P (ksDomScheduleStart s)"
  and sch_act_simple[wp]: "sch_act_simple"
  and ifunsafe'[wp]: "if_unsafe_then_cap'"
  and global_refs'[wp]: "valid_global_refs'"
  and valid_arch'[wp]: "valid_arch_state'"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and vms'[wp]: "valid_machine_state'"
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ntfn_at'[wp]: "ntfn_at' t"
  (wp: hoare_vcg_all_lift crunch_wps simp: crunch_simps)

lemma blockedCancelIPC_valid_pspace'[wp]:
  "\<lbrace>valid_pspace' and st_tcb_at' ((=) st) tptr\<rbrace>
   blockedCancelIPC st tptr rptrOpt
   \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  supply opt_mapE[elim!]
  unfolding valid_pspace'_def blockedCancelIPC_def getBlockingObject_def
  apply (wpsimp wp: valid_mdb'_lift hoare_vcg_imp_lift getEndpoint_wp
                    hoare_vcg_all_lift sts'_valid_replies' replyUnlink_st_tcb_at'
              simp: epBlocked_def)
  apply (case_tac "rptrOpt"; clarsimp simp: pred_tcb_at'_eq_commute)
   apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  apply (rename_tac rptr reply)
  apply (drule_tac rptr=rptr in valid_replies'D[simplified pred_tcb_at'_eq_commute])
   apply clarsimp
  apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  done

crunch getBlockingObject
  for inv: P

crunch blockedCancelIPC
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and untyped_ranges_zero'[wp]: "untyped_ranges_zero'"
  and tcbInReleaseQueue[wp]: "\<lambda>s. P (tcbInReleaseQueue |< tcbs_of' s)"
  (wp: crunch_wps)

lemma tcbEPDequeue_valid_sched_pointers[wp]:
  "tcbEPDequeue tcbPtr epPtr \<lbrace>valid_sched_pointers\<rbrace>"
  unfolding tcbEPDequeue_def updateEndpoint_def
  apply (wpsimp wp: tcbQueueRemove_valid_sched_pointers  hoare_drop_imps hoare_vcg_if_lift2)
  apply (clarsimp simp: valid_sched_pointers_def)
  done

lemma tcbEPDequeue_not_sched_linked[wp]:
  "\<lbrace>\<top>\<rbrace> tcbEPDequeue tcbPtr epPtr \<lbrace>\<lambda>_ s. \<not> is_sched_linked tcbPtr s\<rbrace>"
  unfolding tcbEPDequeue_def
  by (wpsimp wp: tcbQueueRemove_not_sched_linked[simplified])

lemmas tcbEPDequeue_tcbSchedNexts_of[wp] =
  tcbEPDequeue_not_sched_linked[simplified, THEN hoare_conjD1[simplified pred_conj_def]]

lemmas tcbEPDequeue_tcbSchedPrevs_of[wp] =
  tcbEPDequeue_not_sched_linked[simplified, THEN hoare_conjD2[simplified pred_conj_def]]

lemma blockedCancelIPC_valid_sched_pointers:
  "\<lbrace>valid_sched_pointers and tcb_at' tptr\<rbrace>
   blockedCancelIPC st tptr rptrOpt
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  unfolding blockedCancelIPC_def replyUnlink_def getBlockingObject_def
  apply (cases rptrOpt; clarsimp)
   apply (wpsimp wp: setThreadState_sched_pointers_valid_sched_pointers)
  apply wpsimp
      apply (wpsimp wp: setThreadState_not_queued_valid_sched_pointers)
     apply (wpsimp wp: setThreadState_sched_pointers_valid_sched_pointers)
           apply (rule_tac Q'="\<lambda>_ s. \<not> st_tcb_at' inIPCQueueThreadState tptr s \<and> tcb_at' tptr s"
                        in hoare_post_imp)
            apply (clarsimp simp: st_tcb_at'_def obj_at'_def opt_pred_def opt_map_red)
           apply (wpsimp wp: sts_st_tcb_at'_cases_strong)
          apply (wpsimp wp: gts_wp' hoare_vcg_all_lift | wp (once) hoare_drop_imps)+
  done

crunch blockedCancelIPC
  for sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_bitmaps[wp]: valid_bitmaps
  and sym_heap_reply_pointers[wp]: sym_heap_reply_pointers
  (wp: crunch_wps)

lemma valid_irq_node'_ksSchedulerAction[simp]:
  "valid_irq_node' w (ksSchedulerAction_update f s) = valid_irq_node' w s"
  by (simp add: valid_irq_node'_def)

lemma blockedCancelIPC_invs':
  "\<lbrace>invs' and st_tcb_at' ((=) st) tptr\<rbrace>
   blockedCancelIPC st tptr rptrOpt
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def
  apply (wpsimp wp: blockedCancelIPC_valid_sched_pointers
                    valid_irq_node_lift valid_irq_handlers_lift' valid_irq_states_lift'
                    irqs_masked_lift valid_dom_schedule'_lift
              simp: cteCaps_of_def)
  done

lemma threadSet_fault_invs':
  "threadSet (tcbFault_update upd) t \<lbrace>invs'\<rbrace>"
  apply (wpsimp wp: threadSet_invs_trivial)
  done

lemma cancelIPC_invs'[wp]:
  "cancelIPC t \<lbrace>invs'\<rbrace>"
  unfolding cancelIPC_def Let_def
  apply (wpsimp wp: blockedCancelIPC_invs' replyRemoveTCB_invs' cancelSignal_invs'
                    hoare_vcg_all_lift hoare_vcg_imp_lift' threadSet_fault_invs' gts_wp'
              simp: pred_tcb_at'_def)
  apply normalise_obj_at'
  apply (rename_tac tcb)
  apply (case_tac "tcbState tcb"; clarsimp)
  done

lemma cancelSignal_st_tcb_at:
  assumes [simp]: "P Inactive" shows
  "\<lbrace>st_tcb_at' P t\<rbrace>
     cancelSignal t' ntfn
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (simp add: cancelSignal_def Let_def list_case_If)
  apply (wp sts_st_tcb_at'_cases hoare_vcg_const_imp_lift
            hoare_drop_imp[where Q'="%rv s. P' rv" for P'])
   apply clarsimp+
  done

lemma cancelIPC_st_tcb_at:
  assumes [simp]: "\<And>st. simple' st \<longrightarrow> P st" shows
  "cancelIPC t' \<lbrace>st_tcb_at' P t\<rbrace>"
  unfolding cancelIPC_def
  apply (wpsimp wp: blockedCancelIPC_st_tcb_at replyRemoveTCB_st_tcb_at'_cases
                    cancelSignal_st_tcb_at threadSet_pred_tcb_no_state gts_wp')
  done

lemma weak_sch_act_wf_lift_linear:
  "\<lbrakk> \<And>t. f \<lbrace>\<lambda>s. sa s \<noteq> SwitchToThread t\<rbrace>; \<And>t. f \<lbrace>tcb_at' t\<rbrace> \<rbrakk>
   \<Longrightarrow> f \<lbrace>\<lambda>s. weak_sch_act_wf (sa s) s\<rbrace>"
  apply (simp only: weak_sch_act_wf_def imp_conv_disj)
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift hoare_vcg_conj_lift)
  apply simp_all
  done

crunch cancelSignal, setBoundNotification
  for sch_act_not[wp]: "sch_act_not t"
  (wp: crunch_wps)

lemma cancelSignal_tcb_at_runnable':
  "t \<noteq> t' \<Longrightarrow>
  \<lbrace>st_tcb_at' runnable' t'\<rbrace> cancelSignal t ntfnptr \<lbrace>\<lambda>_. st_tcb_at' runnable' t'\<rbrace>"
  unfolding cancelSignal_def
  by (wpsimp wp: sts_pred_tcb_neq' hoare_drop_imp)

lemma setThreadState_st_tcb_at'_test_unaffected:
  "\<lbrace>\<lambda>s. st_tcb_at' test t s \<and> test st\<rbrace>
   setThreadState st t'
   \<lbrace>\<lambda>_. st_tcb_at' test t\<rbrace>"
  apply (wpsimp wp: sts_st_tcb')
  done

crunch unbindNotification, bindNotification, unbindMaybeNotification
  for st_tcb_at'[wp]: "st_tcb_at' P p"
  (wp: threadSet_pred_tcb_no_state ignore: threadSet)

(* FIXME move *)
lemma setBoundNotification_not_ntfn:
  "(\<And>tcb ntfn. P (tcb\<lparr>tcbBoundNotification := ntfn\<rparr>) \<longleftrightarrow> P tcb)
     \<Longrightarrow> \<lbrace>obj_at' P t'\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>_. obj_at' P t'\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp hoare_vcg_conj_lift
     | wpc
     | rule hoare_drop_imps
     | simp)+
  done

text \<open>The suspend operation, significant as called from delete\<close>

lemma sbn_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   setBoundNotification ntfn t
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp weak_sch_act_wf_lift)

lemma setObject_ntfn_sa_unchanged[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
    setObject ptr (ntfn::Structures_H.notification)
   \<lbrace>\<lambda>rv s.  P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp | simp add: updateObject_default_def)+
  done

lemmas ipccancel_weak_sch_act_wfs
    = weak_sch_act_wf_lift[OF _ tcb_at'_typ_at_lift_strong[OF setCTE_typ_at']]

lemma updateObject_ep_inv:
  "\<lbrace>P\<rbrace> updateObject (obj::endpoint) ko p q n \<lbrace>\<lambda>rv. P\<rbrace>"
  by simp (rule updateObject_default_inv)

lemma asUser_tcbQueued_inv[wp]:
  "asUser t m \<lbrace>\<lambda>s. Q (obj_at' (\<lambda>tcb. P (tcbQueued tcb)) tcb_ptr s)\<rbrace>"
  unfolding asUser_def
  by (wpsimp wp: threadSet_obj_at'_no_state threadGet_wp)

crunch asUser
  for valid_sched_pointers[wp]: valid_sched_pointers
  and pspace_bounded'[wp]: pspace_bounded'
  (rule: sym_heap_sched_pointers_lift wp: crunch_wps)

crunch set_thread_state, as_user
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  (wp: crunch_wps in_correct_ready_q_lift ready_qs_distinct_lift)

lemma set_thread_state_ep_queues_blocked_not_queued:
  "\<lbrace>\<lambda>s. ep_queues_blocked s \<and> \<not> ep_queued t s\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>_. ep_queues_blocked\<rbrace>"
  unfolding ep_queues_blocked_def
  apply (wpsimp wp: sts_st_tcb_at_cases_strong hoare_vcg_all_lift hoare_vcg_imp_lift'
                    hoare_vcg_ball_lift)
  apply (clarsimp simp: in_ep_queue_at_def ep_queued_def)
  done

lemma set_thread_state_ntfn_queues_blocked_not_queued:
  "\<lbrace>\<lambda>s. ntfn_queues_blocked s \<and> \<not> ntfn_queued t s\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>_. ntfn_queues_blocked\<rbrace>"
  unfolding ntfn_queues_blocked_def
  apply (wpsimp wp: sts_st_tcb_at_cases_strong hoare_vcg_all_lift hoare_vcg_imp_lift'
                    hoare_vcg_ball_lift)
  apply (clarsimp simp: in_ntfn_queue_at_def ntfn_queued_def)
  done

crunch as_user
  for ep_queues_blocked[wp]: ep_queues_blocked
  and ntfn_queues_blocked[wp]: ntfn_queues_blocked
  and ready_queues_runnable[wp]: ready_queues_runnable
  and release_q_runnable[wp]: release_q_runnable
  (wp: crunch_wps ep_queues_blocked_lift ntfn_queues_blocked_lift ready_queues_runnable_lift
       release_q_runnable_lift)

lemma (in delete_one_gen) suspend_corres:
  "corres dc
     (einvs and tcb_at t) (invs' and tcb_at' t)
     (SchedContext_A.suspend t) (ThreadDecls_H.suspend t)"
  apply (simp add: SchedContext_A.suspend_def Thread_H.suspend_def)
  apply add_sym_refs
  apply (rule corres_stateAssert_add_assertion[rotated], clarsimp)+
   apply (fastforce intro!: weak_sch_act_wf_cross)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor[OF cancel_ipc_corres])
      apply (rule corres_split[OF getThreadState_corres], rename_tac state state')
        apply (simp only: when_def)
        apply (rule corres_split[OF corres_if])
             apply (case_tac state; clarsimp?)
            apply (rule update_restart_pc_corres)
           apply (rule corres_rel_imp)
            apply corres
           apply simp
          apply (rule corres_split[OF tcbSchedDequeue_corres], simp)
            apply (rule corres_split[OF tcbReleaseRemove_corres], simp)
              apply (rule corres_split[OF schedContextCancelYieldTo_corres], simp)
                apply (rule setThreadState_corres)
                apply wpsimp+
               apply (rule hoare_post_imp[where Q'="\<lambda>_ s. invs s \<and> tcb_at t s"])
                apply fastforce
               apply (wpsimp wp: sched_context_cancel_yield_to_invs)
              apply (rule hoare_post_imp[where Q'="\<lambda>_. valid_objs'"])
               apply fastforce
              apply (wpsimp wp: schedContextCancelYieldTo_invs' tcbReleaseRemove_invs')+
          apply (wpsimp simp: update_restart_pc_def | strengthen invs_implies)+
         apply (clarsimp simp: updateRestartPC_def)
         apply (wpsimp wp: gts_wp hoare_vcg_all_lift hoare_drop_imps weak_if_wp
                | strengthen invs_implies valid_ready_qs_in_correct_ready_q
                             valid_ready_qs_ready_qs_distinct
                             valid_sched_valid_ready_qs valid_sched_valid_release_q invs'_implies
                             sym_refs_ep_queues_blocked sym_refs_ntfn_queues_blocked
                             valid_ready_qs_ready_queues_runnable valid_release_q_release_q_runnable)+
   apply (fastforce dest: valid_sched_valid_release_q)
  apply clarsimp
  done

crunch tcbSchedDequeue
  for sch_act_simple[wp]: sch_act_simple
  (wp: crunch_wps sch_act_simple_lift)

lemma asUser_sch_act_simple[wp]:
  "\<lbrace>sch_act_simple\<rbrace> asUser s t \<lbrace>\<lambda>_. sch_act_simple\<rbrace>"
  unfolding sch_act_simple_def
  apply (rule asUser_nosch)
  done

crunch updateRestartPC
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P tcbPtr"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and tcb_at'[wp]: "\<lambda>s. P (tcb_at' t s)"
  and invs'[wp]: invs'

lemma suspend_invs'[wp]:
  "suspend t \<lbrace>invs'\<rbrace>"
  apply (simp add: suspend_def updateRestartPC_def)
  apply (wpsimp wp: tcbReleaseRemove_invs' schedContextCancelYieldTo_invs' sts_invs_minor' gts_wp')
    apply (rule_tac Q'="\<lambda>_. invs' and st_tcb_at' simple' t" in hoare_post_imp)
     apply (fastforce elim: pred_tcb'_weakenE)
    apply wpsimp+
  done

lemma suspend_st_tcb_at':
  assumes x[simp]: "\<And>st. simple' st \<longrightarrow> P st" shows
  "\<lbrace>st_tcb_at' P t\<rbrace>
     suspend thread
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (simp add: suspend_def)
  unfolding updateRestartPC_def
  apply (wp sts_st_tcb_at'_cases threadSet_pred_tcb_no_state
            cancelIPC_st_tcb_at hoare_drop_imps
         | simp)+
  apply clarsimp
  done

lemmas suspend_makes_simple' = suspend_st_tcb_at' [where P=simple', simplified]

lemma suspend_makes_inactive:
  "\<lbrace>K (t = t')\<rbrace> suspend t \<lbrace>\<lambda>rv. st_tcb_at' ((=) Inactive) t'\<rbrace>"
  apply (cases "t = t'", simp_all)
  apply (simp add: suspend_def unless_def)
  apply (wp threadSet_pred_tcb_no_state setThreadState_st_tcb | simp)+
  done

lemma tcbSchedEnqueue_sch_act_not_ct[wp]:
  "\<lbrace>\<lambda>s. sch_act_not (ksCurThread s) s\<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_ s. sch_act_not (ksCurThread s) s\<rbrace>"
  by (rule hoare_weaken_pre, wps, wp, simp)

lemma sts_sch_act_not_ct[wp]:
  "\<lbrace>\<lambda>s. sch_act_not (ksCurThread s) s\<rbrace>
   setThreadState st t \<lbrace>\<lambda>_ s. sch_act_not (ksCurThread s) s\<rbrace>"
  by (rule hoare_weaken_pre, wps, wp, simp)

text \<open>Cancelling all IPC in an endpoint or notification object\<close>

global_interpretation refillUnblockCheck: gen_typ_at_all_props' "refillUnblockCheck scp"
  by typ_at_props'

global_interpretation ifCondRefillUnblockCheck: gen_typ_at_all_props' "ifCondRefillUnblockCheck scp act ast"
  by typ_at_props'

lemma updateSchedContext_valid_tcbs'[wp]:
  "updateSchedContext scp f \<lbrace> valid_tcbs' \<rbrace>"
  unfolding updateSchedContext_def setSchedContext_def getSchedContext_def
  apply (wpsimp wp: setObject_valid_tcbs'[where P=\<top>])
    apply (clarsimp simp:  updateObject_default_def in_monad)
   apply (wpsimp wp: getObject_inv)
  by simp

lemma valid_refills'_tcbQueued_update[simp]:
  "scp \<noteq> t \<Longrightarrow>
   valid_refills' scp
            (s\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbQueued_update (\<lambda>_. True) tcb))\<rparr>)
   = valid_refills' scp s"
  by (clarsimp simp: valid_refills'_def opt_pred_def)

lemma threadSet_valid_refills'[wp]:
  "threadSet f tp \<lbrace> valid_refills' scp \<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  by (clarsimp simp: valid_refills'_def obj_at'_def opt_pred_def
               dest!: opt_predD split: kernel_object.splits option.splits
               elim!: opt_mapE)

crunch setThreadState
  for valid_refills'[wp]: "valid_refills' scp"
  (wp: getSchedulable_wp simp: crunch_simps)

crunch ifCondRefillUnblockCheck
  for valid_tcbs'[wp]: valid_tcbs'
  and tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
  and tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_sched_pointers[wp]: valid_sched_pointers
  (wp: hoare_vcg_if_lift2 crunch_wps simp: crunch_simps)

crunch refill_unblock_check
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  and ep_queues_blocked[wp]: ep_queues_blocked
  and ntfn_queues_blocked[wp]: ntfn_queues_blocked
  and ready_queues_runnable[wp]: ready_queues_runnable
  (rule: in_correct_ready_q_lift ready_qs_distinct_lift
         ep_queues_blocked_lift ntfn_queues_blocked_lift ready_queues_runnable_lift)

lemma set_thread_state_ready_queues_runnable_not_queued:
  "\<lbrace>ready_queues_runnable and not_queued t\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>_. ready_queues_runnable\<rbrace>"
  unfolding ready_queues_runnable_def
  apply (intro hoare_allI, rename_tac d p)
  apply (rule hoare_weaken_pre)
  apply (rule_tac Q="\<lambda>x s. \<forall>t'\<in>set x. t' \<notin> {} \<longrightarrow> st_tcb_at runnable t' s \<and> t \<notin> set x"
              and g="\<lambda>s. ready_queues s d p"
               in hoare_lift_Pf_pre_conj)
    apply (wpsimp wp: hoare_vcg_ball_lift sts_st_tcb_at_other)
   apply wpsimp
  apply (fastforce simp: not_queued_def)
  done

lemma restartThreadIfNoFault_corres:
  "corres dc
     (not ep_queued t and not ntfn_queued t and not_queued t
      and valid_sched_action and tcb_at t and pspace_aligned and pspace_distinct
      and valid_objs and active_scs_valid and current_time_bounded
      and in_correct_ready_q and ready_qs_distinct and ready_or_release
      and ep_queues_blocked and ntfn_queues_blocked and ready_queues_runnable)
     (valid_objs' and valid_sched_pointers and (\<lambda>s. \<not> is_sched_linked t s))
     (restart_thread_if_no_fault t) (restartThreadIfNoFault t)"
  apply add_pspace_adb'
  apply (rule corres_cross_add_guard[where Q'="tcb_at' t"])
   apply (fastforce intro: tcb_at_cross)
  apply (clarsimp simp: restart_thread_if_no_fault_def restartThreadIfNoFault_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF threadGet_corres[where r=fault_rel_optionation]])
       apply (clarsimp simp: tcb_relation_def)
      apply (rule corres_if)
        apply (clarsimp simp: fault_rel_optionation_def)
       apply (rule corres_split[OF setThreadState_corres])
          apply (clarsimp simp: fault_rel_optionation_def)
         apply clarsimp
         apply (rule corres_split_eqr[OF get_tcb_obj_ref_corres])
            apply (clarsimp simp: tcb_relation_def)
           apply (rule corres_split[OF ifCondRefillUnblockCheck_corres])
             apply (rule possibleSwitchTo_corres, simp)
            apply (wpsimp simp: if_cond_refill_unblock_check_def
                            wp: refill_unblock_check_active_scs_valid)
           apply wpsimp
          apply (rule_tac Q'="\<lambda>scopt s. case_option True (\<lambda>p. sc_at p s) scopt
                                        \<and> st_tcb_at runnable t s \<and> valid_sched_action s
                                        \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_objs s
                                        \<and> active_scs_valid s \<and> current_time_bounded s
                                        \<and> in_correct_ready_q s \<and> ready_qs_distinct s
                                        \<and> ready_or_release s \<and> ep_queues_blocked s
                                        \<and> ntfn_queues_blocked s \<and> ready_queues_runnable s"
                       in hoare_post_imp)
           apply (fastforce split: option.splits
                             simp: obj_at_def is_sc_obj opt_map_red opt_pred_def)
          apply (wpsimp wp: thread_get_wp' simp: get_tcb_obj_ref_def)
         apply (clarsimp simp: bool.case_eq_if option.case_eq_if)
         apply (wpsimp wp: threadGet_wp)
        apply (rule_tac Q'="\<lambda>scopt s. st_tcb_at runnable t s \<and> valid_sched_action s
                                      \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_objs s
                                      \<and> active_scs_valid s \<and> current_time_bounded s
                                      \<and> in_correct_ready_q s \<and> ready_qs_distinct s
                                      \<and> ready_or_release s \<and> ep_queues_blocked s
                                      \<and> ntfn_queues_blocked s \<and> ready_queues_runnable s"
                     in hoare_post_imp)
         apply (fastforce dest: valid_objs_ko_at
                          simp: valid_bound_obj_def valid_obj_def valid_tcb_def)
        apply (wpsimp wp: sts_typ_ats set_thread_state_valid_sched_action
                          set_thread_state_ep_queues_blocked_not_queued
                          set_thread_state_ntfn_queues_blocked_not_queued
                          set_thread_state_ready_queues_runnable_not_queued)
       apply (rule hoare_strengthen_post[where Q'="\<lambda>_ s. tcb_at' t s \<and> valid_objs' s
                                                         \<and> valid_sched_pointers s
                                                         \<and> pspace_aligned' s \<and> pspace_distinct' s
                                                         \<and> pspace_bounded' s", rotated])
        apply (clarsimp simp: gen_obj_at_simps)
       apply (wpsimp wp: sts_st_tcb_at'_cases setThreadState_sched_pointers_valid_sched_pointers)
      apply (rule setThreadState_corres)
      apply clarsimp
     apply (wpsimp wp: thread_get_wp threadGet_wp)+
   apply (clarsimp simp: obj_at_def is_tcb_def)
   apply (rename_tac ko, case_tac ko; clarsimp)
  apply (clarsimp simp: in_ep_queue_at_def)
  done

crunch ifCondRefillUnblockCheck
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P p"
  (simp: crunch_simps wp: whileLoop_wp crunch_wps ignore: threadSet)

crunch removeAndRestartEPQueuedThread, removeAndRestartNTFNQueuedThread
  for pspace_bounded'[wp]: pspace_bounded'
  (simp: crunch_simps wp: whileLoop_wp ignore: updateSchedContext
   wp: crunch_wps)

crunch reply_unlink_tcb
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  (rule: in_correct_ready_q_lift ready_qs_distinct_lift)

lemma blocked_on_send_not_runnable:
  "st_tcb_at is_blocked_on_send t s \<Longrightarrow> st_tcb_at (Not \<circ> runnable) t s"
  by (fastforce simp: pred_tcb_at_def obj_at_def vs_all_heap_simps runnable_eq_active)

lemma blocked_on_send_recv_not_runnable:
  "st_tcb_at is_blocked_on_send_recv t s \<Longrightarrow> st_tcb_at (Not \<circ> runnable) t s"
  by (fastforce simp: pred_tcb_at_def obj_at_def vs_all_heap_simps runnable_eq_active)

lemma is_blocked_on_ntfn_not_runnable:
  "st_tcb_at is_blocked_on_ntfn t s \<Longrightarrow> st_tcb_at (Not \<circ> runnable) t s"
  by (fastforce simp: pred_tcb_at_def obj_at_def vs_all_heap_simps runnable_eq_active)

lemmas reply_unlink_tcb_typ_at_lifts[wp] = abs_typ_at_lifts[OF reply_unlink_tcb_typ_at]

lemma endpoint_IdleEPState_split:
  "(case epState ep of IdleEPState \<Rightarrow> f | _ \<Rightarrow> g) = (if epState ep = IdleEPState then f else g)"
  apply (cases ep; clarsimp)
  by (rename_tac state queue, case_tac state; clarsimp)

lemma set_endpoint_ep_queues_blocked[wp]:
  "\<lbrace>\<lambda>s. (\<forall>p\<in>set (ep_queue ep). st_tcb_at (\<lambda>st. ep_blocked st = Some ep_ptr) p s)
        \<and> ep_queues_blocked s\<rbrace>
   set_endpoint ep_ptr ep
   \<lbrace>\<lambda>_. ep_queues_blocked\<rbrace>"
  apply (wpsimp wp: set_simple_ko_wp)
  apply (fastforce simp: ep_queues_blocked_def eps_of_kh_def ep_at_pred_def st_tcb_at_def obj_at_def)
  done

crunch set_endpoint
  for ready_qs_distinct[wp]: ready_qs_distinct
  and ready_queues_runnable[wp]: ready_queues_runnable
  (wp: ready_qs_distinct_lift ready_queues_runnable_lift)

lemma in_ep_queue_at_unique:
  "\<lbrakk>in_ep_queue_at t ep_ptr s; ep_queues_blocked s\<rbrakk> \<Longrightarrow> \<forall>p. p \<noteq> ep_ptr \<longrightarrow> \<not> in_ep_queue_at t p s"
  apply (clarsimp simp: in_ep_queue_at_def ep_queued_def obj_at_def ep_queues_blocked_def
                        st_tcb_at_def)
  apply (frule_tac x=ep_ptr in spec)
  apply fastforce
  done

lemma tcb_ep_dequeue_not_ep_queued:
  "\<lbrace>in_ep_queue_at t ep_ptr and ep_queues_blocked\<rbrace>
   tcb_ep_dequeue t ep_ptr
   \<lbrace>\<lambda>_ s. \<not> ep_queued t s\<rbrace>"
  unfolding tcb_ep_dequeue_def
  apply (wpsimp wp: set_simple_ko_wp get_simple_ko_wp)
  apply (frule (1) in_ep_queue_at_unique)
  apply (clarsimp simp: in_ep_queue_at_def ep_queued_def eps_of_kh_def list.case_eq_if
                 split: if_splits)
  done

lemma threadGet_return_tcbSchedNexts_of:
  "monadic_rewrite False True (tcb_at' t)
     (threadGet tcbSchedNext t) (gets (\<lambda>s. tcbSchedNexts_of s t))"
  apply (rule monadic_rewrite_add_return_l)
  apply (rule monadic_rewrite_add_return_r)
  apply monadic_rewrite_symb_exec_l
    apply monadic_rewrite_symb_exec_r
     apply (fastforce intro: monadic_rewrite_guard_arg_cong)
    apply (wpsimp wp: threadGet_wp)+
  apply (clarsimp simp: obj_at'_def opt_map_red)
  done

lemma reply_unlink_tcb_ep_queues_blocked[wp]:
  "\<lbrace>ep_queues_blocked and not ep_queued t\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>_. ep_queues_blocked\<rbrace>"
  unfolding reply_unlink_tcb_def
  by (wpsimp wp: set_thread_state_ep_queues_blocked_not_queued gts_wp get_simple_ko_wp
           simp: ep_queued_def in_ep_queue_at_def)

lemma reply_unlink_tcb_ntfn_queues_blocked[wp]:
  "\<lbrace>ntfn_queues_blocked and not ntfn_queued t\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>_. ntfn_queues_blocked\<rbrace>"
  unfolding reply_unlink_tcb_def
  by (wpsimp wp: set_thread_state_ntfn_queues_blocked_not_queued gts_wp get_simple_ko_wp
           simp: ntfn_queued_def in_ntfn_queue_at_def)

crunch update_reply
  for ready_queues_runnable[wp]: ready_queues_runnable
  and ep_queues[wp]: "\<lambda>s. P (ep_queued t s)"
  (wp: ready_queues_runnable_lift ep_queued_lift)

lemma reply_unlink_tcb_ready_queues_runnable[wp]:
  "\<lbrace>ready_queues_runnable and not_queued t\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>_. ready_queues_runnable\<rbrace>"
  unfolding reply_unlink_tcb_def update_sk_obj_ref_def
  by (wpsimp wp: set_thread_state_ready_queues_runnable_not_queued gts_wp wp: get_simple_ko_wp)

lemma replyUnlink_valid_sched_pointers:
  "\<lbrace>\<lambda>s. valid_sched_pointers s \<and> \<not> is_sched_linked tcbPtr s\<rbrace>
   replyUnlink replyPtr tcbPtr
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  unfolding replyUnlink_def
  by (wpsimp wp: setThreadState_sched_pointers_valid_sched_pointers gts_wp')

crunch reply_unlink_tcb
  for ep_queued[wp]: "\<lambda>s. P (ep_queued t s)"
  and ntfn_queued[wp]: "\<lambda>s. P (ntfn_queued t s)"
  (wp: crunch_wps ep_queued_lift simp:  ntfn_queued_def in_ntfn_queue_at_def)

lemma set_endpoint_ntfn_queued[wp]:
  "set_endpoint ep_ptr ep \<lbrace>\<lambda>s. P (ntfn_queued t s)\<rbrace>"
  by (wpsimp wp: ntfn_queued_lift)

lemma tcb_ep_dequeue_ep_queues_blocked[wp]:
  "tcb_ep_dequeue t ep_ptr \<lbrace>ep_queues_blocked\<rbrace>"
  unfolding tcb_ep_dequeue_def
  apply (wpsimp wp: set_endpoint_ep_queues_blocked get_simple_ko_wp)
  apply (rename_tac ep p)
  apply (clarsimp simp: ep_queues_blocked_def eps_of_kh_def obj_at_def opt_map_def
                 split: option.splits list.splits)
  apply (prop_tac "set (filter ((\<noteq>) t) (ep_queue ep)) \<subseteq> set (ep_queue ep)")
   apply (rule filter_is_subset)
  apply (fastforce simp: removeAll_filter_not_eq)
  done

crunch tcb_ep_dequeue
  for ntfn_queued[wp]: "\<lambda>s. P (ntfn_queued t s)"
  and ntfn_queues_blocked[wp]: ntfn_queues_blocked
  (wp: ntfn_queues_blocked_lift crunch_wps ignore: set_simple_ko)

lemma is_blocked_on_send_isSend:
  "\<lbrakk>is_blocked_on_send st; thread_state_relation st st'\<rbrakk> \<Longrightarrow> isSend st'"
  by (cases st; cases st'; clarsimp simp: thread_state_relation_def isSend_def)

lemma is_blocked_on_receive_isReceive:
  "\<lbrakk>is_blocked_on_receive st; thread_state_relation st st'\<rbrakk> \<Longrightarrow> isReceive st'"
  by (cases st; cases st'; clarsimp simp: thread_state_relation_def isReceive_def)

lemma removeAndRestartEPQueuedThread_corres:
  "corres dc
     (in_ep_queue_at t epptr and not ntfn_queued t and not_queued t and not_in_release_q t
      and st_tcb_at is_blocked_on_send_recv t
      and reply_unlink_ts_pred t and valid_objs and valid_sched and current_time_bounded
      and ep_queues_blocked and ntfn_queues_blocked
      and pspace_aligned and pspace_distinct)
     (valid_objs' and valid_sched_pointers and sym_heap_sched_pointers)
     (remove_and_restart_ep_queued_thread t epptr)
     (removeAndRestartEPQueuedThread t epptr)"
  supply if_split[split del]
  apply add_pspace_adb'
  apply (rule corres_cross_add_guard[where Q'="tcb_at' t"])
   apply (fastforce intro!: tcb_at_cross)
  apply (clarsimp simp: remove_and_restart_ep_queued_thread_def removeAndRestartEPQueuedThread_def)
  apply (rule corres_symb_exec_r[OF _ gts_sp']; (solves wpsimp)?)
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (fastforce dest!: st_tcb_at_coerce_concrete
                           is_blocked_on_send_isSend is_blocked_on_receive_isReceive
                     simp: ep_queues_blocked_def in_ep_queue_at_def st_tcb_at'_def obj_at'_def)
  apply (clarsimp simp: maybeM_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF tcbEPDequeue_corres], simp, simp)
      apply (rule corres_split[OF getThreadState_corres])
        apply (rule corres_stateAssert_r)
        apply (rename_tac st st')
        apply (rule corres_split[where r'=dc])
           apply (rule corres_option_split)
             apply (case_tac st;
                    clarsimp simp: isReceive_def thread_state_relation_def is_blocked_on_receive_def)
            apply (rule corres_return_trivial)
           apply (rule replyUnlink_corres)
          apply (rule restartThreadIfNoFault_corres)
         apply (wpsimp wp: reply_unlink_tcb_valid_sched_action)
        apply (wpsimp wp: replyUnlink_valid_sched_pointers)
       apply (wpsimp wp: gts_wp)
      apply (wpsimp wp: gts_wp')
     apply ((wpsimp wp: tcb_ep_dequeue_not_ep_queued hoare_vcg_imp_lift' hoare_case_option_wp
                       hoare_vcg_all_lift
             | strengthen valid_objs_valid_tcbs)+)[1]
    apply (rule_tac Q'="\<lambda>_ s. valid_objs' s \<and> valid_sched_pointers s
                              \<and> pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_bounded' s
                              \<and> \<not> is_sched_linked t s
                              \<and> (\<forall>st. st_tcb_at' ((=) st) t s
                                      \<longrightarrow> valid_bound_reply'
                                            (if isReceive st then replyObject st else Nothing) s)"
                 in hoare_post_imp)
     apply (clarsimp simp: valid_bound_obj'_def split: if_splits option.splits)
    apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
   apply (wpsimp wp: hoare_drop_imps)
   apply (frule valid_sched_valid_ready_qs)
   apply (frule valid_sched_valid_release_q)
   apply (intro conjI impI allI; clarsimp?)
   subgoal
     by (fastforce simp: is_blocked_on_receive_def vs_all_heap_simps pred_tcb_at_def obj_at_def
                         reply_unlink_ts_pred_def
                  split: option.splits if_splits)
  apply clarsimp
  apply (frule (1) st_tcb_at_coerce_abstract)
  apply (clarsimp simp: isReceive_def pred_tcb_at'_def obj_at'_def pred_tcb_at_def obj_at_def)
  apply (rename_tac tcb tcb')
  apply (case_tac "tcb_state tcb"; clarsimp)
  apply (prop_tac "valid_tcb_state (tcb_state tcb) s")
   apply (rule st_tcb_at_valid_st2)
    apply (fastforce simp: pred_tcb_at_def obj_at_def)
   apply fastforce
  apply (clarsimp simp: valid_bound_obj'_def split: option.splits)
  apply (fastforce intro!: reply_at_cross simp: pred_tcb_at'_def obj_at'_def)
  done

lemma remove_and_restart_ep_queued_thread_valid_idle[wp]:
  "\<lbrace>valid_idle and K (t \<noteq> idle_thread_ptr)\<rbrace>
   remove_and_restart_ep_queued_thread t epptr
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  unfolding remove_and_restart_ep_queued_thread_def
  apply forward_inv_step
  apply (wpsimp wp: gts_wp)
  apply (fastforce simp: valid_idle_def)
  done

lemma remove_and_restart_ep_queued_thread_not_queued_other:
  "\<lbrace>\<lambda>s. not_queued t s \<and> scheduler_act_not t s \<and> t' \<noteq> t\<rbrace>
   remove_and_restart_ep_queued_thread t' epptr
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  unfolding remove_and_restart_ep_queued_thread_def
  apply forward_inv_step
  apply (wpsimp wp: gts_wp)
  done

crunch remove_and_restart_ep_queued_thread, remove_and_restart_ntfn_queued_thread,
       remove_and_restart_badged_thread
  for not_queued[wp]: "not_queued t"
  and tcb_at[wp]: "tcb_at t"
  (wp: crunch_wps simp: crunch_simps)

crunch removeAndRestartEPQueuedThread, removeAndRestartNTFNQueuedThread,
       removeAndRestartBadgedThread
  for valid_objs'[wp]: valid_objs'
  (wp: crunch_wps simp: crunch_simps)

lemma restartThreadIfNoFault_valid_sched_pointers[wp]:
  "\<lbrace>\<lambda>s. valid_sched_pointers s \<and> \<not> is_sched_linked t s\<rbrace>
   restartThreadIfNoFault t
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  unfolding restartThreadIfNoFault_def
  by (wpsimp wp: setThreadState_sched_pointers_valid_sched_pointers)

lemma removeAndRestartEPQueuedThread_valid_sched_pointers[wp]:
  "removeAndRestartEPQueuedThread t epptr \<lbrace>valid_sched_pointers\<rbrace>"
  unfolding removeAndRestartEPQueuedThread_def
  by (wpsimp wp: replyUnlink_valid_sched_pointers hoare_drop_imps)

lemma removeAndRestartNTFNQueuedThread_valid_sched_pointers[wp]:
  "removeAndRestartNTFNQueuedThread t epptr \<lbrace>valid_sched_pointers\<rbrace>"
  unfolding removeAndRestartNTFNQueuedThread_def
  by (wpsimp wp: setThreadState_sched_pointers_valid_sched_pointers hoare_drop_imps)

lemma removeAndRestartBadgedThread_valid_sched_pointers[wp]:
  "removeAndRestartBadgedThread t epptr badge \<lbrace>valid_sched_pointers\<rbrace>"
  unfolding removeAndRestartBadgedThread_def
  by (wpsimp wp: restartThreadIfNoFault_valid_sched_pointers gts_wp')

lemma set_endpoint_reply_unlink_ts_pred[wp]:
  "set_endpoint ep_ptr ep \<lbrace>reply_unlink_ts_pred p\<rbrace>"
  apply (wpsimp wp: set_simple_ko_wp)
  apply (fastforce simp: reply_unlink_ts_pred_def reply_at_ppred_def obj_at_def ep_at_pred_def)
  done

lemma set_endpoint_ntfn_queues_blocked[wp]:
  "set_endpoint ep_ptr ep \<lbrace>ntfn_queues_blocked\<rbrace>"
  by (wpsimp wp: ntfn_queues_blocked_lift)

lemma tcb_ep_dequeue_in_ep_queue_at_other:
  "\<lbrace>\<lambda>s. P (in_ep_queue_at t epptr s) \<and> t' \<noteq> t\<rbrace>
   tcb_ep_dequeue t' epptr'
   \<lbrace>\<lambda>_ s. P (in_ep_queue_at t epptr s)\<rbrace>"
  unfolding tcb_ep_dequeue_def
  apply (wpsimp wp: set_simple_ko_wp get_simple_ko_wp)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: removeAll_filter_not_eq in_ep_queue_at_def obj_at_def eps_of_kh_def
                        opt_map_def
                 split: list.splits)
  apply (rename_tac ep)
  apply (intro conjI impI allI)
   apply (fastforce dest: empty_filter_conv[THEN iffD1, OF sym])
  apply (intro iffI)
   apply (fastforce dest: in_filter_neq)
  apply (cut_tac xs="ep_queue ep" and P="(\<noteq>) t'" in filter_is_subset)
  apply fastforce
  done

lemma tcb_ep_dequeue_ep_queued_other:
  "\<lbrace>\<lambda>s. P (ep_queued t s) \<and> t' \<noteq> t\<rbrace>
   tcb_ep_dequeue t' epptr
   \<lbrace>\<lambda>_ s. P (ep_queued t s)\<rbrace>"
  unfolding ep_queued_def
  apply (insert bool_function_four_cases[where f=P])
  apply (elim disjE; clarsimp; (solves wpsimp)?)
   apply (rule hoare_allI)
   apply (wpsimp wp: hoare_allI tcb_ep_dequeue_in_ep_queue_at_other[where P=Not])
  apply (rule hoare_ex_pre_conj)
  apply (wpsimp wp: hoare_exI tcb_ep_dequeue_in_ep_queue_at_other[where P=id, simplified])
  done

lemma in_ep_queue_at_lift:
  "(\<And>P. f \<lbrace>\<lambda>s. P (ep_queues_of s)\<rbrace>) \<Longrightarrow> (\<And>P. f \<lbrace>\<lambda>s. P (in_ep_queue_at t ep_ptr s)\<rbrace>)"
  apply (clarsimp simp: in_ep_queue_at_def)
  by (rule hoare_lift_Pf2; wpsimp)

lemma in_ntfn_queue_at_lift:
  "(\<And>P. f \<lbrace>\<lambda>s. P (ntfn_queues_of s)\<rbrace>) \<Longrightarrow> (\<And>P. f \<lbrace>\<lambda>s. P (in_ntfn_queue_at t ep_ptr s)\<rbrace>)"
  apply (clarsimp simp: in_ntfn_queue_at_def)
  by (rule hoare_lift_Pf2; wpsimp)

crunch restart_thread_if_no_fault, reply_unlink_tcb
  for in_ep_queue_at[wp]: "\<lambda>s. P (in_ep_queue_at t epptr s)"
  and in_ntfn_queue_at[wp]: "\<lambda>s. P (in_ntfn_queue_at t epptr s)"
  and ntfns_of[wp]: "\<lambda>s. P (ntfns_of s)"
  (wp: in_ep_queue_at_lift in_ntfn_queue_at_lift)

lemma remove_and_restart_ep_queued_thread_in_ep_queue_at_other:
  "\<lbrace>\<lambda>s. in_ep_queue_at t epptr s \<and> t' \<noteq> t\<rbrace>
   remove_and_restart_ep_queued_thread t' epptr
   \<lbrace>\<lambda>_ s. in_ep_queue_at t epptr s\<rbrace>"
  unfolding remove_and_restart_ep_queued_thread_def
  by (wpsimp wp: tcb_ep_dequeue_in_ep_queue_at_other gts_wp hoare_vcg_all_lift hoare_drop_imps)

crunch tcb_ep_dequeue, tcb_ep_append
  for ntfns_of[wp]: "\<lambda>s. P (ntfns_of s)"
  (wp: crunch_wps ignore: set_simple_ko)

crunch remove_and_restart_ep_queued_thread, remove_and_restart_badged_thread
  for ntfn_queued[wp]: "\<lambda>s. P (ntfn_queued t s)"
  (wp: ntfn_queued_lift crunch_wps)

crunch if_cond_refill_unblock_check
  for ep_queues_blocked[wp]: ep_queues_blocked
  and ntfn_queues_blocked[wp]: ntfn_queues_blocked
  (wp: ep_queues_blocked_lift ntfn_queues_blocked_lift)

lemma remove_and_restart_ep_queued_thread_ep_queues_blocked:
  "\<lbrace>ep_queues_blocked and in_ep_queue_at t ep_ptr\<rbrace>
   remove_and_restart_ep_queued_thread t ep_ptr
   \<lbrace>\<lambda>_. ep_queues_blocked\<rbrace>"
  unfolding remove_and_restart_ep_queued_thread_def restart_thread_if_no_fault_def
  by (wpsimp wp: set_thread_state_ep_queues_blocked_not_queued tcb_ep_dequeue_not_ep_queued gts_wp
                 hoare_vcg_all_lift hoare_drop_imps)

lemma remove_and_restart_ep_queued_thread_ntfn_queues_blocked:
  "\<lbrace>ntfn_queues_blocked and not ntfn_queued t\<rbrace>
   remove_and_restart_ep_queued_thread t ep_ptr
   \<lbrace>\<lambda>_. ntfn_queues_blocked\<rbrace>"
  unfolding remove_and_restart_ep_queued_thread_def restart_thread_if_no_fault_def
  by (wpsimp wp: set_thread_state_ntfn_queues_blocked_not_queued tcb_ep_dequeue_not_ep_queued gts_wp
                 hoare_vcg_all_lift hoare_drop_imps)

lemma removeAndRestartEPQueuedThread_sym_heap_sched_pointers[wp]:
  "\<lbrace>sym_heap_sched_pointers and valid_sched_pointers\<rbrace>
   removeAndRestartEPQueuedThread t ep_ptr
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  unfolding removeAndRestartEPQueuedThread_def restartThreadIfNoFault_def
  by (wpsimp wp: setThreadState_sched_pointers_valid_sched_pointers
                 replyUnlink_valid_sched_pointers threadGet_wp hoare_drop_imps hoare_vcg_all_lift)

lemma removeAndRestartNTFNQueuedThread_sym_heap_sched_pointers[wp]:
  "\<lbrace>sym_heap_sched_pointers and valid_sched_pointers\<rbrace>
   removeAndRestartNTFNQueuedThread t ep_ptr
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  unfolding removeAndRestartNTFNQueuedThread_def
  by (wpsimp wp: setThreadState_sched_pointers_valid_sched_pointers hoare_drop_imps)

lemma removeAndRestartBadgedThread_sym_heap_sched_pointers[wp]:
  "\<lbrace>sym_heap_sched_pointers and valid_sched_pointers\<rbrace>
   removeAndRestartBadgedThread t ep_ptr badge
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  unfolding removeAndRestartBadgedThread_def restartThreadIfNoFault_def
  by (wpsimp wp: setThreadState_sched_pointers_valid_sched_pointers hoare_drop_imps gts_wp')

lemma tcbSchedPrev_update_tcbSchedNexts_of[wp]:
  "threadSet (tcbSchedPrev_update f) t' \<lbrace>\<lambda>s. P (tcbSchedNexts_of s t)\<rbrace>"
  by (wpsimp wp: threadSet_field_inv)

lemma tcbSchedNext_update_tcbSchedNexts_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedNexts_of s t) \<and> t' \<noteq> t\<rbrace>
   threadSet (tcbSchedNext_update f) t'
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s t)\<rbrace>"
  by (wpsimp wp: threadSet_wp)

lemma tcbQueuePrepend_tcbSchedNexts_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedNexts_of s t) \<and> t' \<noteq> t\<rbrace>
   tcbQueuePrepend q t'
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s t)\<rbrace>"
  unfolding tcbQueuePrepend_def
  by (wpsimp wp: tcbSchedNext_update_tcbSchedNexts_of_other)

lemma tcbQueueRemove_tcbSchedNexts_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedNexts_of s t') \<and> t \<noteq> t'
        \<and> (\<exists>ls. heap_ls (tcbSchedNexts_of s) (Some t) ls \<and> t' \<in> set ls)\<rbrace>
   tcbQueueRemove q t
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s t')\<rbrace>"
  supply heap_path_append[simp del] if_split[split del]
  apply (subst conj_assoc[symmetric])+
  apply (rule hoare_ex_pre_conj[simplified conj_commute], rename_tac ls)
  apply (clarsimp simp: tcbQueueRemove_def)
  apply (intro bind_wp[OF _ stateAssert_sp])
  apply (clarsimp simp: pred_conj_def)
  apply (subst conj_assoc[symmetric])+
  apply (rule hoare_ex_pre_conj[simplified conj_commute], rename_tac ts)
  apply (rule bind_wp[OF _ get_tcb_sp'])
  apply (rule hoare_if)
   \<comment> \<open>q is a singleton\<close>
   apply wpsimp
  apply (rule hoare_if)
   \<comment> \<open>t is the head of q\<close>
   apply (wpsimp wp: tcbSchedNext_update_tcbSchedNexts_of_other)
  \<comment> \<open>t is not the head of q\<close>
  apply (rule_tac S="\<exists>pfx. ts = pfx @ t # tl ls" in hoare_gen_asm_spec)
   apply (prop_tac "ls \<noteq> []", fastforce)
   apply (clarsimp simp: list_queue_relation_def)
   apply (frule_tac xs=ls and ys=ts in heap_ls_suffix)
     apply fastforce
    apply fastforce
   apply (force dest!: heap_path_head simp: suffix_def)
  apply (clarsimp, rename_tac pfx)
  apply (rule_tac P'1="\<lambda>s. \<exists>ptr. tcbSchedPrevs_of s t = Some ptr \<and> ptr \<in> set pfx"
               in hoare_pre_add[THEN iffD2])
   apply (clarsimp simp: list_queue_relation_def)
   apply (frule (1) heap_path_sym_heap_non_nil_lookup_prev)
    apply fastforce
   apply (fastforce intro: last_in_set simp: opt_map_red)
  apply (rule_tac S="t' \<in> set (tl ls)" in hoare_gen_asm_spec)
   apply (clarsimp simp: list_queue_relation_def)
   apply (frule_tac xs=ls in heap_path_head)
    apply fastforce
   apply (case_tac ls; clarsimp)
  apply (wpsimp wp: tcbSchedNext_update_tcbSchedNexts_of_other)
  apply (fastforce dest: heap_ls_distinct simp: list_queue_relation_def opt_map_def obj_at'_def)
  done

lemma tcbEPDequeue_tcbSchedNexts_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedNexts_of s t') \<and> t' \<noteq> t
        \<and> (\<exists>ls. heap_ls (tcbSchedNexts_of s) (Some t) ls \<and> t' \<in> set ls)\<rbrace>
   tcbEPDequeue t epptr
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s t')\<rbrace>"
  apply (clarsimp simp: tcbEPDequeue_def)
  apply (wpsimp wp: tcbQueueRemove_tcbSchedNexts_of_other getEndpoint_wp)
  done

lemma tcbNTFNDequeue_tcbSchedNexts_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedNexts_of s t') \<and> t' \<noteq> t
        \<and> ((\<exists>ls. heap_ls (tcbSchedNexts_of s) (Some t) ls \<and> t' \<in> set ls))\<rbrace>
   tcbNTFNDequeue t ntfnPtr
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s t')\<rbrace>"
  apply (clarsimp simp: tcbNTFNDequeue_def)
  apply (wpsimp wp: tcbQueueRemove_tcbSchedNexts_of_other getNotification_wp)
  done

lemma tcbSchedEnqueue_tcbSchedNexts_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedNexts_of s t) \<and> t' \<noteq> t\<rbrace>
   tcbSchedEnqueue t'
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s t)\<rbrace>"
  unfolding tcbSchedEnqueue_def
  by (wpsimp wp: tcbQueuePrepend_tcbSchedNexts_of_other threadSet_field_inv threadGet_wp)

lemma rescheduleRequired_tcbSchedNexts_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedNexts_of s t) \<and> sch_act_not t s\<rbrace>
   rescheduleRequired
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s t)\<rbrace>"
  unfolding rescheduleRequired_def
  by (wpsimp wp: tcbSchedEnqueue_tcbSchedNexts_of_other getSchedulable_wp)

lemma possibleSwitchTo_tcbSchedNexts_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedNexts_of s t) \<and> t' \<noteq> t \<and> sch_act_not t s\<rbrace>
   possibleSwitchTo t'
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s t)\<rbrace>"
  unfolding possibleSwitchTo_def
  by (wpsimp wp: tcbSchedEnqueue_tcbSchedNexts_of_other threadGet_wp
                 rescheduleRequired_tcbSchedNexts_of_other inReleaseQueue_wp)

lemma restartThreadIfNoFault_tcbSchedNexts_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedNexts_of s t) \<and> t' \<noteq> t \<and> sch_act_not t s\<rbrace>
   restartThreadIfNoFault t'
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s t)\<rbrace>"
  unfolding restartThreadIfNoFault_def ifCondRefillUnblockCheck_def
  by (wpsimp wp: possibleSwitchTo_tcbSchedNexts_of_other hoare_drop_imps)

lemma removeAndRestartEPQueuedThread_tcbSchedNexts_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedNexts_of s t') \<and> sch_act_not t' s \<and> t' \<noteq> t
        \<and> (\<exists>ls. heap_ls (tcbSchedNexts_of s) (Some t) ls \<and> t' \<in> set ls)\<rbrace>
   removeAndRestartEPQueuedThread t epptr
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s t')\<rbrace>"
  unfolding removeAndRestartEPQueuedThread_def
  apply (wpsimp wp: restartThreadIfNoFault_tcbSchedNexts_of_other
                    tcbEPDequeue_tcbSchedNexts_of_other hoare_drop_imps)
  apply fastforce
  done

lemma removeAndRestartNTFNQueuedThread_tcbSchedNexts_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedNexts_of s t') \<and> sch_act_not t' s \<and> t' \<noteq> t
        \<and> (\<exists>ls. heap_ls (tcbSchedNexts_of s) (Some t) ls \<and> t' \<in> set ls)\<rbrace>
   removeAndRestartNTFNQueuedThread t epptr
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s t')\<rbrace>"
  unfolding removeAndRestartNTFNQueuedThread_def
  apply (wpsimp wp: possibleSwitchTo_tcbSchedNexts_of_other
                    tcbNTFNDequeue_tcbSchedNexts_of_other hoare_drop_imps)
  apply fastforce
  done

lemma removeAndRestartBadgedThread_tcbSchedNexts_of_other:
  "\<lbrace>\<lambda>s. P (tcbSchedNexts_of s t') \<and> sch_act_not t' s \<and> t' \<noteq> t
        \<and> (\<exists>ls. heap_ls (tcbSchedNexts_of s) (Some t) ls \<and> t' \<in> set ls)\<rbrace>
   removeAndRestartBadgedThread t epptr badge
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s t')\<rbrace>"
  unfolding removeAndRestartBadgedThread_def
  apply (wpsimp wp: restartThreadIfNoFault_tcbSchedNexts_of_other
                    tcbEPDequeue_tcbSchedNexts_of_other gts_wp')
  apply fastforce
  done

lemma cancelAllIPC_corres:
  "corres dc
     (invs and valid_sched and ep_at ep_ptr and current_time_bounded) invs'
     (cancel_all_ipc ep_ptr) (cancelAllIPC ep_ptr)"
  apply add_sym_refs
  apply add_sch_act_wf
  apply (clarsimp simp: cancel_all_ipc_def cancelAllIPC_def)
  apply (rule corres_stateAssert_ignore, solves simp)+
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro: ksReadyQueues_asrt_cross)
  apply (rule_tac Q'="ep_at' ep_ptr" in corres_cross_add_guard)
   apply (fastforce intro!: ep_at_cross)
  apply (rule corres_split_forwards'[OF _ get_simple_ko_sp get_ep_sp'])
   apply (corres corres: getEndpoint_corres)
  apply (rename_tac ep ep')
  apply (subst endpoint_IdleEP_split)
  apply (subst endpoint_IdleEPState_split)
  apply (rule corres_if_strong')
    apply (clarsimp simp: ep_relation_def split: Structures_A.endpoint.splits)
   apply clarsimp
  apply (rule_tac F="ep_queue ep \<noteq> []" in corres_req)
   apply (fastforce dest!: valid_objs_ko_at invs_valid_objs
                     simp: valid_obj_def valid_ep_def split: Structures_A.endpoint.splits)
  apply (rule_tac Q'="\<lambda>s. list_queue_relation (ep_queue ep) (epQueue ep')
                                              (tcbSchedNexts_of s) (tcbSchedPrevs_of s)"
               in corres_cross_add_guard)
   apply (frule state_relation_ep_queues_relation)
   apply (fastforce simp: ep_queues_relation_def opt_map_def eps_of_kh_def obj_at_def obj_at'_def
                   split: option.splits)
  apply (rule_tac F="distinct (ep_queue ep)" in corres_req)
   apply (fastforce intro: heap_ls_distinct simp: list_queue_relation_def)
  apply (rule corres_symb_exec_l[OF _ _ return_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ return_sp]; (solves wpsimp)?)
  apply clarsimp
  apply (rule corres_stateAssert_ignore)
   apply clarsimp
   apply (rule list_queue_relation_tcb_queue_head_end_valid)
    apply fastforce
   apply (fastforce dest: in_ep_queue_sched_flag_set[rotated]
                    elim: sym_refs_ep_queues_blocked[OF invs_sym_refs]
                    simp: eps_of_kh_def opt_map_def obj_at_def
                   split: option.splits)
  \<comment> \<open>step over the mapM_x on the abstract side and the whileLoop on the concrete side, leaving
     rescheduleRequired\<close>
  apply (rule_tac Q="\<lambda>_ s. ep_at_pred (\<lambda>ep. ep = IdleEP) ep_ptr s
                           \<and> ep_queues_blocked s \<and> ntfn_queues_blocked s
                           \<and> valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_sched s
                           \<and> heap_refs_inv (tcb_scps_of s) (sc_tcbs_of s)
                           \<and> current_time_bounded s"
              and Q'="\<lambda>_. valid_tcbs' and valid_sched_pointers"
               in corres_split_forwards'[where r'=dc])
     apply (rule stronger_corres_guard_imp)
       apply (clarsimp simp: threadGet_def)
       apply (subst bind_dummy_ret_val)+
       apply (rule_tac P="\<lambda>ls s. ep_at_pred (\<lambda>ep. ep_queue ep = ls) ep_ptr s
                                 \<and> distinct ls
                                 \<and> (ls \<noteq> []
                                    \<longrightarrow> (\<forall>p \<in> set ls. in_ep_queue_at p ep_ptr s \<and> \<not> ntfn_queued p s
                                                      \<and> not_queued p s \<and> not_in_release_q p s
                                                      \<and> st_tcb_at is_blocked_on_send_recv p s
                                                      \<and> reply_unlink_ts_pred p s))
                                 \<and> valid_objs s \<and> valid_idle s
                                 \<and> ep_queues_blocked s \<and> ntfn_queues_blocked s
                                 \<and> pspace_aligned s \<and> pspace_distinct s
                                 \<and> heap_refs_inv (tcb_scps_of s) (sc_tcbs_of s)
                                 \<and> valid_sched s \<and> current_time_bounded s"
                   and P'="\<lambda>_. valid_objs' and valid_sched_pointers and sym_heap_sched_pointers
                               and pspace_aligned' and pspace_distinct' and pspace_bounded'
                               and ep_at' ep_ptr"
                    in corres_mapM_x_whileLoop[where nexts_of=tcbSchedNexts_of])
             apply (corres corres: removeAndRestartEPQueuedThread_corres)
            apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
                  apply (wpsimp wp: remove_and_restart_ep_queued_thread_dequeues_head)
                  apply (clarsimp simp: ep_at_pred_def, rename_tac obj)
                  apply (case_tac "ep_queue obj"; clarsimp)
                 apply wpsimp
                 apply (fastforce elim: distinct_tl)
                apply (wpsimp wp: remove_and_restart_ep_queued_thread_dequeues_head
                                  remove_and_restart_ep_queued_thread_other
                                  remove_and_restart_ep_queued_thread_reply_unlink_ts_pred_other
                                  remove_and_restart_ep_queued_thread_in_ep_queue_at_other
                                  hoare_vcg_const_imp_lift hoare_vcg_ball_lift hoare_vcg_all_lift)
                apply (fastforce dest!: list.set_sel(2) distinct_hd_not_in_tl
                                 intro: weak_valid_sched_action_scheduler_action_not
                                        blocked_on_send_recv_not_runnable)
               apply wpsimp
               apply (frule_tac t="hd ls" in not_idle_thread')
                 apply (fastforce dest: hd_in_set)
                apply fastforce
               apply (clarsimp simp: valid_idle_def)
              apply (wpsimp wp: remove_and_restart_ep_queued_thread_valid_sched
                                remove_and_restart_ep_queued_thread_ep_queues_blocked
                                remove_and_restart_ep_queued_thread_ntfn_queues_blocked)+
            apply (rule conjI)
             apply (clarsimp simp: obj_at_kh_kheap_simps)
            apply (erule not_idle_thread')
             apply fastforce
            apply fastforce
           apply wpsimp
          apply (wpsimp wp: hoare_vcg_const_imp_lift hoare_vcg_ball_lift
                            removeAndRestartEPQueuedThread_sym_heap_sched_pointers)
         apply wpsimp
         apply (rule monadic_rewrite_guard_imp)
          apply (rule threadGet_return_tcbSchedNexts_of[simplified threadGet_def])
         apply (force intro!: tcb_at_cross simp: ex_abs_def)
        apply wpsimp
        apply (force intro!: tcb_at_cross simp: ex_abs_def)
       apply (wpsimp wp: removeAndRestartEPQueuedThread_tcbSchedNexts_of_other)
       apply (clarsimp simp: ex_abs_def)
       apply (rename_tac s' s)
       apply (rule conjI)
        apply clarsimp
        apply (prop_tac "scheduler_action s = switch_thread t'")
         apply (drule state_relation_sched_act_relation)
         apply (clarsimp simp: sched_act_relation_def)
         apply (case_tac "scheduler_action s"; clarsimp)
        apply (fastforce dest!: valid_sched_weak_valid_sched_action
                                weak_valid_sched_action_scheduler_action_not
                         intro: blocked_on_send_recv_not_runnable simp: scheduler_act_not_def)
       apply (frule state_relation_ep_queues_relation)
       apply (clarsimp simp: ep_queues_relation_def)
       apply (fastforce simp: list_queue_relation_def)
      apply clarsimp
      apply (rename_tac s s')
      apply (frule invs_sym_refs)
      apply (frule sym_refs_ep_queues_blocked)
      apply (frule valid_sched_valid_ready_qs)
      apply (frule valid_sched_valid_release_q)
      apply (prop_tac "ep_queues_of s ep_ptr = Some (ep_queue ep)")
       apply (fastforce simp: opt_map_def eps_of_kh_def obj_at_def split: option.splits)
      apply (prop_tac "\<forall>p \<in> set (ep_queue ep). st_tcb_at is_blocked_on_send_recv p s")
       apply (clarsimp simp: ep_queues_blocked_def)
       apply (drule_tac x=ep_ptr in spec)
       apply (drule_tac x="ep_queue ep" in spec)
       apply (fastforce elim!: st_tcb_weakenE simp: ep_blocked_def
                        split: Structures_A.thread_state.splits)
      apply (intro conjI impI allI; fastforce?)
       apply (force simp: ep_at_pred_def obj_at_def)
      apply (clarsimp simp: in_ep_queue_at_def)
      apply (intro conjI impI allI)
         apply (force dest: ep_queues_ntfn_queues_disjoint
                      simp: in_ntfn_queue_at_def ntfn_queued_def)
        apply (clarsimp simp: not_queued_def)
        apply (force dest!: ep_queues_ready_queues_disjoint)
       apply (clarsimp simp: not_in_release_q_def)
       apply (fastforce dest!: ep_queues_release_queue_disjoint)
      apply (fastforce simp: reply_unlink_ts_pred_def simp flip: tcb_at_kh_simps
                      elim!: st_tcb_recv_reply_state_refs[OF _ invs_sym_refs, simplified op_equal])
     apply (fastforce simp: list_queue_relation_def)
    apply (rule hoare_vcg_conj_lift_pre_fix)
     apply (rule hoare_weaken_pre)
      apply (rule mapM_x_inv_wp2[
                    where I=valid_objs
                      and V="\<lambda>xs. ep_at_pred (\<lambda>ep. ep_queue ep = xs) ep_ptr"])
       apply (force simp: ep_at_pred_def valid_obj_def valid_ep_def
                   split: Structures_A.endpoint.splits)
      apply (wpsimp wp: remove_and_restart_ep_queued_thread_dequeues_head)
      apply (force simp: ep_at_pred_def valid_obj_def valid_ep_def
                  split: Structures_A.endpoint.splits)
     apply (fastforce simp: ep_at_pred_def obj_at_def)
    apply (rule_tac S="distinct queue" in hoare_gen_asm_spec, fastforce)
    apply (rule hoare_weaken_pre)
     apply (rule_tac Q="\<lambda>t s. in_ep_queue_at t ep_ptr s \<and> \<not> ntfn_queued t s
                              \<and> not_queued t s \<and> not_in_release_q t s \<and> scheduler_act_not t s
                              \<and> st_tcb_at is_blocked_on_send_recv t s \<and> t \<noteq> idle_thread s"
                  in ball_mapM_x_scheme)
       apply (wpsimp wp: remove_and_restart_ep_queued_thread_other remove_and_restart_ep_queued_thread_in_ep_queue_at_other)
      apply ((wpsimp wp: remove_and_restart_ep_queued_thread_other
                         remove_and_restart_ep_queued_thread_valid_sched
                         remove_and_restart_ep_queued_thread_ep_queues_blocked
                         remove_and_restart_ep_queued_thread_ntfn_queues_blocked
              | strengthen valid_objs_valid_tcbs)+)[1]
      apply (clarsimp simp: obj_at_kh_kheap_simps)
     apply fastforce
    apply (clarsimp simp: valid_ep_def cong: conj_cong)
    apply (rename_tac s)
    apply (frule invs_sym_refs)
    apply (frule sym_refs_ep_queues_blocked)
    apply (frule valid_sched_valid_ready_qs)
    apply (frule valid_sched_valid_release_q)
    apply (prop_tac "ep_queues_of s ep_ptr = Some (ep_queue ep)")
     apply (fastforce simp: opt_map_def eps_of_kh_def obj_at_def split: option.splits)
    apply (prop_tac "\<forall>p \<in> set (ep_queue ep). st_tcb_at is_blocked_on_send_recv p s")
     apply (clarsimp simp: ep_queues_blocked_def)
     apply (drule_tac x=ep_ptr in spec)
     apply (drule_tac x="ep_queue ep" in spec)
     apply (fastforce elim!: st_tcb_weakenE simp: ep_blocked_def
                      split: Structures_A.thread_state.splits)
    apply (intro conjI impI allI ballI; fastforce?)
         apply (force simp: in_ep_queue_at_def ep_at_pred_def obj_at_def)
        apply (clarsimp simp: in_ep_queue_at_def)
        apply (force dest: ep_queues_ntfn_queues_disjoint
                     simp: in_ntfn_queue_at_def ntfn_queued_def)
       apply (clarsimp simp: not_queued_def)
       apply (force dest!: ep_queues_ready_queues_disjoint)
      apply (clarsimp simp: not_in_release_q_def)
      apply (fastforce dest!: ep_queues_release_queue_disjoint)
     apply (fastforce intro: weak_valid_sched_action_scheduler_action_not
                             blocked_on_send_recv_not_runnable)
    apply (rule not_idle_thread', fastforce+)
   apply (rule_tac Q'="\<lambda>_. pspace_aligned' and pspace_distinct' and pspace_bounded'
                           and valid_objs' and valid_sched_pointers and sym_heap_sched_pointers"
                in hoare_post_imp)
    apply fastforce
   apply (wpsimp wp: whileLoop_valid_inv)
   apply fastforce
  apply add_pspace_adb'
  apply (rule corres_symb_exec_r_conj_ex_abs_forwards[OF _ get_ep_sp', rotated]; (solves wpsimp)?)
   apply wpsimp
   apply (force intro: ep_at_cross simp: ex_abs_def ep_at_pred_def obj_at_def is_ep_def)
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (frule state_relation_pspace_relation)
   apply (clarsimp simp: pspace_relation_heap_pspace_relation heap_pspace_relation_def
                         map_relation_def eps_of_kh_def opt_map_def obj_at'_def ep_at_pred_def
                         ep_relation_def
                  split: option.splits Structures_A.endpoint.splits)
  apply (corres corres: rescheduleRequired_corres)
   apply (frule valid_sched_valid_ready_qs)
   apply (fastforce dest: valid_sched_valid_release_q)
  apply fastforce
  done

lemma blocked_on_recv_ntfn_tcb_at_not_runnable:
  "blocked_on_recv_ntfn_tcb_at t s \<Longrightarrow> st_tcb_at (Not \<circ> runnable) t s"
  by (fastforce simp: pred_tcb_at_def obj_at_def vs_all_heap_simps runnable_eq_active)

lemma valid_tcbs_ko_at:
  "valid_tcbs s \<Longrightarrow> ko_at (TCB tcb) ptr s \<Longrightarrow> valid_tcb ptr tcb s"
  by (auto simp: valid_tcbs_def obj_at_def)

crunch tcb_ntfn_dequeue
  for ep_queued[wp]: "\<lambda>s. P (ep_queued t s)"
  and ep_queues_blocked[wp]: ep_queues_blocked
  (wp: ep_queues_blocked_lift ep_queued_lift crunch_wps ignore: set_simple_ko)

lemma set_notification_ntfn_queues_blocked[wp]:
  "\<lbrace>\<lambda>s. (\<forall>p\<in>set (ntfn_queue (ntfn_obj ntfn)). st_tcb_at (\<lambda>st. ntfn_blocked st = Some ntfn_ptr) p s)
        \<and> ntfn_queues_blocked s\<rbrace>
   set_notification ntfn_ptr ntfn
   \<lbrace>\<lambda>_. ntfn_queues_blocked\<rbrace>"
  apply (wpsimp wp: set_simple_ko_wp)
  apply (fastforce simp: ntfn_queues_blocked_def ntfn_at_pred_def st_tcb_at_def obj_at_def)
  done

lemma tcb_ntfn_dequeue_ntfn_queues_blocked[wp]:
  "tcb_ntfn_dequeue t ntfn_ptr \<lbrace>ntfn_queues_blocked\<rbrace>"
  unfolding tcb_ntfn_dequeue_def
  apply (wpsimp wp: get_simple_ko_wp)
  apply (clarsimp simp: ntfn_queues_blocked_def obj_at_def opt_map_def split: list.splits)
  apply (rename_tac ntfn p head tail)
  apply (cut_tac xs="ntfn_queue (ntfn_obj ntfn)" and P="(\<noteq>) t" in filter_is_subset)
  apply (fastforce simp: removeAll_filter_not_eq split: ntfn.splits)
  done

lemma in_ntfn_queue_at_unique:
  "\<lbrakk>in_ntfn_queue_at t ntfn_ptr s; ntfn_queues_blocked s\<rbrakk>
   \<Longrightarrow> \<forall>p. p \<noteq> ntfn_ptr \<longrightarrow> \<not> in_ntfn_queue_at t p s"
  apply (clarsimp simp: in_ntfn_queue_at_def obj_at_def ntfn_queues_blocked_def st_tcb_at_def)
  apply (frule_tac x=ntfn_ptr in spec)
  apply fastforce
  done

lemma tcb_ntfn_dequeue_not_ntfn_queued:
  "\<lbrace>in_ntfn_queue_at t ntfn_ptr and ntfn_queues_blocked\<rbrace>
   tcb_ntfn_dequeue t ntfn_ptr
   \<lbrace>\<lambda>_ s. \<not> ntfn_queued t s\<rbrace>"
  unfolding tcb_ntfn_dequeue_def
  apply (wpsimp wp: set_simple_ko_wp get_simple_ko_wp)
  apply (frule (1) in_ntfn_queue_at_unique)
  apply (force simp: in_ntfn_queue_at_def ntfn_queued_def list.case_eq_if split: if_splits)
  done

lemma is_blocked_on_ntfn_isBlockedOnNtfn:
  "\<lbrakk>is_blocked_on_ntfn st; thread_state_relation st st'\<rbrakk> \<Longrightarrow> isBlockedOnNtfn st'"
  by (cases st; cases st'; clarsimp simp: thread_state_relation_def isBlockedOnNtfn_def)

lemma removeAndRestartNTFNQueuedThread_corres:
  "corres dc
     (in_ntfn_queue_at t ntfnPtr and not ep_queued t and not_queued t and not_in_release_q t
      and tcb_at t and valid_objs and valid_sched and current_time_bounded
      and ep_queues_blocked and ntfn_queues_blocked
      and pspace_aligned and pspace_distinct)
     (valid_objs' and valid_sched_pointers and sym_heap_sched_pointers and pspace_bounded')
     (remove_and_restart_ntfn_queued_thread t ntfnPtr)
     (removeAndRestartNTFNQueuedThread t ntfnPtr)"
  apply add_pspace_adb'
  apply (rule corres_cross_add_guard[where Q'="tcb_at' t"])
   apply (fastforce intro!: tcb_at_cross)
  apply (clarsimp simp: remove_and_restart_ntfn_queued_thread_def removeAndRestartNTFNQueuedThread_def)
  apply (rule corres_symb_exec_r[OF _ gts_sp']; (solves wpsimp)?)
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (clarsimp simp: ntfn_queues_blocked_def in_ntfn_queue_at_def st_tcb_at'_def obj_at'_def)
   apply (rename_tac q tcb)
   apply (drule_tac x=ntfnPtr in spec)
   apply (drule_tac x=q in spec)
   apply clarsimp
   apply (drule_tac x=t in bspec, fastforce)
   apply (frule (3) st_tcb_at_coerce_concrete)
   apply (clarsimp simp: st_tcb_at_def obj_at_def st_tcb_at'_def obj_at'_def ntfn_blocked_def)
   apply (rule_tac st=st in is_blocked_on_ntfn_isBlockedOnNtfn)
    apply (fastforce split: Structures_A.thread_state.splits)
   apply (fastforce simp: st_tcb_at_def obj_at_def ntfn_queues_blocked_def in_ntfn_queue_at_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF tcbNTFNDequeue_corres], simp, simp)
      apply (rule corres_split[OF setThreadState_corres])
         apply clarsimp
        apply (rule corres_split_eqr[OF get_tcb_obj_ref_corres])
           apply (clarsimp simp: tcb_relation_def)
          apply (rule corres_split[OF ifCondRefillUnblockCheck_corres])
            apply (rule possibleSwitchTo_corres, simp)
           apply (wpsimp simp: if_cond_refill_unblock_check_def
                           wp: refill_unblock_check_active_scs_valid)
          apply wpsimp
         apply (wpsimp wp: get_tcb_obj_ref_wp)
        apply (wpsimp wp: threadGet_wp)
       apply (clarsimp cong: conj_cong imp_cong all_cong)
       apply (rule_tac Q'="\<lambda>_. pspace_aligned and pspace_distinct and current_time_bounded
                               and active_scs_valid and valid_objs
                               and in_correct_ready_q and ready_qs_distinct
                               and ready_or_release
                               and valid_sched_action and tcb_at t and st_tcb_at runnable t
                               and ep_queues_blocked and ntfn_queues_blocked
                               and ready_queues_runnable"
                    in hoare_strengthen_post[rotated])
        apply clarsimp
        apply (frule valid_objs_valid_tcbs)
        apply (frule (1) valid_tcbs_ko_at)
        apply (fastforce simp: is_sc_obj obj_at_def opt_map_red valid_tcb_def opt_pred_def
                        split: option.splits)
       apply (wp set_thread_state_valid_sched_action set_thread_state_ep_queues_blocked_not_queued
                 set_thread_state_ntfn_queues_blocked_not_queued
                 set_thread_state_ready_queues_runnable_not_queued)
      apply (simp add: option.case_eq_if)
       apply (rule_tac Q'="\<lambda>_. valid_objs' and tcb_at' t
                               and sym_heap_sched_pointers and valid_sched_pointers
                               and pspace_aligned' and pspace_distinct' and pspace_bounded'"
                    in hoare_strengthen_post[rotated])
       apply clarsimp
      apply (wp setThreadState_st_tcb setThreadState_sched_pointers_valid_sched_pointers)
     apply (wpsimp wp: set_thread_state_pred_map_tcb_sts_of tcb_ntfn_dequeue_not_ntfn_queued)
    apply (wp | strengthen valid_objs'_valid_tcbs')+
   apply clarsimp
   apply (frule valid_sched_valid_ready_qs)
   apply (fastforce dest: valid_sched_valid_release_q)
  apply clarsimp
  done

lemma refill_unblock_check_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action and active_scs_valid\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  apply (clarsimp simp: weak_valid_sched_action_def)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift'')
  done

crunch if_cond_refill_unblock_check
  for weak_valid_sched_action[wp]: weak_valid_sched_action
  and in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  (simp: crunch_simps)

crunch tcb_ntfn_dequeue, tcb_ntfn_append
  for eps_of[wp]: "\<lambda>s. P (eps_of s)"
  (wp: crunch_wps ignore: set_simple_ko)

crunch remove_and_restart_ntfn_queued_thread
  for ep_queued[wp]: "\<lambda>s. P (ep_queued t s)"
  (wp: ep_queued_lift)

lemma in_ntfn_queue_at_in_ntfn_queue_at_other:
  "\<lbrace>\<lambda>s. in_ntfn_queue_at t ntfn_ptr s \<and> t' \<noteq> t\<rbrace>
   tcb_ntfn_dequeue t' ntfn_ptr
   \<lbrace>\<lambda>_ s. in_ntfn_queue_at t ntfn_ptr s\<rbrace>"
  unfolding tcb_ntfn_dequeue_def
  apply (wpsimp wp: set_simple_ko_wp get_simple_ko_wp)
  apply (clarsimp simp: removeAll_filter_not_eq in_ntfn_queue_at_def obj_at_def opt_map_def
                 split: list.splits)
  apply (intro conjI impI allI)
   using empty_filter_conv apply fastforce
  apply (fastforce dest: in_filter_neq[where t=t and t'=t'])
  done

lemma remove_and_restart_ntfn_queued_thread_in_ntfn_queue_at_other:
  "\<lbrace>\<lambda>s. in_ntfn_queue_at t ntfn_ptr s \<and> t' \<noteq> t\<rbrace>
   remove_and_restart_ntfn_queued_thread t' ntfn_ptr
   \<lbrace>\<lambda>_. in_ntfn_queue_at t ntfn_ptr\<rbrace>"
  unfolding remove_and_restart_ntfn_queued_thread_def
  by (wpsimp wp: in_ntfn_queue_at_in_ntfn_queue_at_other)

lemma remove_and_restart_ntfn_queued_thread_ep_queues_blocked:
  "\<lbrace>ep_queues_blocked and not ep_queued t\<rbrace>
   remove_and_restart_ntfn_queued_thread t ep_ptr
   \<lbrace>\<lambda>_. ep_queues_blocked\<rbrace>"
  unfolding remove_and_restart_ntfn_queued_thread_def restart_thread_if_no_fault_def
  by (wpsimp wp: set_thread_state_ep_queues_blocked_not_queued)

lemma remove_and_restart_ntfn_queued_thread_ntfn_queues_blocked:
  "\<lbrace>ntfn_queues_blocked and in_ntfn_queue_at t ntfn_ptr\<rbrace>
   remove_and_restart_ntfn_queued_thread t ntfn_ptr
   \<lbrace>\<lambda>_. ntfn_queues_blocked\<rbrace>"
  unfolding remove_and_restart_ntfn_queued_thread_def restart_thread_if_no_fault_def
  by (wpsimp wp: set_thread_state_ntfn_queues_blocked_not_queued tcb_ntfn_dequeue_not_ntfn_queued)

lemma tcb_ntfn_dequeue_isActive[wp]:
  "tcb_ntfn_dequeue tcb_ptr ntfn_ptr \<lbrace>ntfn_at_pred (\<lambda>ntfn. P (isActive ntfn)) ntfn_ptr\<rbrace>"
  unfolding tcb_ntfn_dequeue_def
  apply (wpsimp wp: set_simple_ko_wp get_simple_ko_wp)
  apply (fastforce simp: isActive_def ntfn_at_pred_def obj_at_def split: ntfn.splits list.splits)
  done

lemma remove_and_restart_ntfn_queued_thread_isActive[wp]:
  "remove_and_restart_ntfn_queued_thread tcb_ptr ntfn_ptr \<lbrace>ntfn_at_pred (\<lambda>ntfn. P (isActive ntfn)) ntfn_ptr\<rbrace>"
  by (wpsimp simp: remove_and_restart_ntfn_queued_thread_def)

lemma cancelAllSignals_corres:
  "corres dc
     (invs and valid_sched and ntfn_at ntfn_ptr and current_time_bounded) invs'
     (cancel_all_signals ntfn_ptr) (cancelAllSignals ntfn_ptr)"
  apply add_sch_act_wf
  apply add_sym_refs
  apply (rule corres_cross_add_guard[where Q'="ntfn_at' ntfn_ptr"])
   apply (fastforce intro!: ntfn_at_cross)
  apply (simp add: cancel_all_signals_def cancelAllSignals_def)
  apply (rule corres_stateAssert_ignore, solves simp)+
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro: ksReadyQueues_asrt_cross)
  apply (rule corres_underlying_split[OF _ _ get_simple_ko_sp get_ntfn_sp'])
   apply (corres corres: getNotification_corres)
    apply fastforce
  apply (rename_tac ntfn ntfn')
  apply (case_tac "ntfn_obj ntfn", simp_all add: ntfn_relation_def)
  apply (rule_tac F="ntfn_queue (ntfn_obj ntfn) \<noteq> []" in corres_req)
   apply (fastforce dest!: valid_objs_ko_at invs_valid_objs simp: valid_obj_def valid_ntfn_def)
  apply (rename_tac queue)
  apply (rule_tac Q'="\<lambda>s. list_queue_relation
                            queue (ntfnQueue ntfn') (tcbSchedNexts_of s) (tcbSchedPrevs_of s)"
               in corres_cross_add_guard)
   apply (frule state_relation_ntfn_queues_relation)
   apply (fastforce simp: ntfn_queues_relation_def opt_map_def obj_at_def obj_at'_def
                   split: option.splits)
  apply (rule_tac F="distinct queue" in corres_req)
   apply (fastforce intro: heap_ls_distinct simp: list_queue_relation_def)
  apply (rule corres_stateAssert_ignore)
   apply (rule list_queue_relation_tcb_queue_head_end_valid)
    apply fastforce
   apply (fastforce dest: in_ntfn_queue_sched_flag_set[rotated]
                    elim: sym_refs_ntfn_queues_blocked[OF invs_sym_refs]
                    simp: eps_of_kh_def opt_map_def obj_at_def
                   split: option.splits)
  \<comment> \<open>step over the mapM_x on the abstract side and the whileLoop on the concrete side, leaving
     rescheduleRequired\<close>
  apply (rule_tac Q="\<lambda>_ s. ntfn_at_pred (\<lambda>ntfn. ntfn_obj ntfn = IdleNtfn) ntfn_ptr s
                           \<and> ep_queues_blocked s \<and> ntfn_queues_blocked s
                           \<and> valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_sched s
                           \<and> heap_refs_inv (tcb_scps_of s) (sc_tcbs_of s)
                           \<and> current_time_bounded s"
              and Q'="\<lambda>_. valid_tcbs' and valid_sched_pointers"
               in corres_split_forwards'[where r'=dc])
     apply (rule stronger_corres_guard_imp)
       apply (clarsimp simp: threadGet_def)
       apply (subst bind_dummy_ret_val)+
       apply (rule_tac P="\<lambda>ls s. ntfn_at_pred (\<lambda>ntfn. ntfn_queue (ntfn_obj ntfn) = ls) ntfn_ptr s
                                 \<and> distinct ls
                                 \<and> (ls \<noteq> []
                                    \<longrightarrow> (\<forall>p \<in> set ls. in_ntfn_queue_at p ntfn_ptr s
                                                      \<and> \<not> ep_queued p s
                                                      \<and> not_queued p s \<and> not_in_release_q p s
                                                      \<and> st_tcb_at is_blocked_on_ntfn p s))
                                 \<and> valid_objs s \<and> valid_idle s
                                 \<and> ep_queues_blocked s \<and> ntfn_queues_blocked s
                                 \<and> pspace_aligned s \<and> pspace_distinct s
                                 \<and> heap_refs_inv (tcb_scps_of s) (sc_tcbs_of s)
                                 \<and> valid_sched s \<and> current_time_bounded s"
                   and P'="\<lambda>_. valid_objs' and valid_sched_pointers and sym_heap_sched_pointers
                               and pspace_aligned' and pspace_distinct' and pspace_bounded'
                               and ntfn_at' ntfn_ptr"
                    in corres_mapM_x_whileLoop[where nexts_of=tcbSchedNexts_of])
             apply (rule corres_guard_imp)
               apply (rule removeAndRestartNTFNQueuedThread_corres)
              apply (fastforce dest: valid_sched_valid_release_q)
             apply fastforce
            apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
                  apply (wpsimp wp: remove_and_restart_ntfn_queued_thread_dequeues_head)
                  apply (clarsimp simp: ntfn_at_pred_def, rename_tac obj)
                  apply (case_tac "ntfn_queue (ntfn_obj obj)"; clarsimp)
                 apply wpsimp
                 apply (fastforce elim: distinct_tl)
                apply (wpsimp wp: remove_and_restart_ntfn_queued_thread_dequeues_head
                                  remove_and_restart_ntfn_queued_thread_other
                                  remove_and_restart_ntfn_queued_thread_in_ntfn_queue_at_other
                                  hoare_vcg_const_imp_lift hoare_vcg_ball_lift)
                apply (fastforce dest!: list.set_sel(2) distinct_hd_not_in_tl
                                 intro: weak_valid_sched_action_scheduler_action_not
                                        is_blocked_on_ntfn_not_runnable)
               apply wpsimp
               apply (frule_tac t="hd ls" in not_idle_thread')
                 apply (fastforce dest: hd_in_set)
                apply fastforce
               apply (clarsimp simp: valid_idle_def)
              apply (wpsimp wp: remove_and_restart_ntfn_queued_thread_valid_sched
                                remove_and_restart_ntfn_queued_thread_ep_queues_blocked
                                remove_and_restart_ntfn_queued_thread_ntfn_queues_blocked)+
            apply (rule conjI)
             apply (force simp: obj_at_kh_kheap_simps vs_all_heap_simps)
            apply (erule not_idle_thread')
             apply fastforce
            apply fastforce
           apply wpsimp
          apply (wpsimp wp: hoare_vcg_const_imp_lift hoare_vcg_ball_lift)
         apply wpsimp
         apply (rule monadic_rewrite_guard_imp)
          apply (rule threadGet_return_tcbSchedNexts_of[simplified threadGet_def])
         apply (force intro!: tcb_at_cross simp: ex_abs_def)
        apply wpsimp
        apply (force intro!: tcb_at_cross simp: ex_abs_def)
       apply (wpsimp wp: removeAndRestartNTFNQueuedThread_tcbSchedNexts_of_other)
       apply (clarsimp simp: ex_abs_def)
       apply (rename_tac s)
       apply (rule conjI)
        apply clarsimp
        apply (prop_tac "scheduler_action s = switch_thread t'")
         apply (drule state_relation_sched_act_relation)
         apply (clarsimp simp: sched_act_relation_def)
         apply (case_tac "scheduler_action s"; clarsimp)
        apply (fastforce dest!: valid_sched_weak_valid_sched_action
                                weak_valid_sched_action_scheduler_action_not
                         intro: is_blocked_on_ntfn_not_runnable simp: scheduler_act_not_def)
       apply (frule state_relation_ntfn_queues_relation)
       apply (clarsimp simp: ntfn_queues_relation_def)
       apply (drule_tac x=ntfn_ptr in spec)
       apply (fastforce simp: list_queue_relation_def)
      apply (clarsimp cong: conj_cong)
      apply (rename_tac s s')
      apply (frule invs_sym_refs)
      apply (frule sym_refs_ntfn_queues_blocked)
      apply (frule sym_refs_ep_queues_blocked)
      apply (frule valid_sched_valid_ready_qs)
      apply (frule valid_sched_valid_release_q)
      apply (prop_tac "ntfn_queues_of s ntfn_ptr = Some queue")
       apply (fastforce simp: opt_map_def obj_at_def split: option.splits)
      apply (prop_tac "\<forall>p \<in> set queue. st_tcb_at is_blocked_on_ntfn p s")
       apply (clarsimp simp: ntfn_queues_blocked_def)
       apply (drule_tac x=ntfn_ptr in spec)
       apply (drule_tac x=queue in spec)
       apply (fastforce elim!: st_tcb_weakenE simp: ntfn_blocked_def
                        split: Structures_A.thread_state.splits)
      apply (intro conjI impI allI ballI; fastforce?)
          apply (force simp: ntfn_at_pred_def obj_at_def)
         apply (force dest: ep_queues_ntfn_queues_disjoint simp: in_ntfn_queue_at_def ntfn_queued_def)
        apply (force dest: ep_queues_ntfn_queues_disjoint simp: in_ep_queue_at_def ep_queued_def)
       apply (clarsimp simp: not_queued_def)
       apply (force dest!: ntfn_queues_ready_queues_disjoint)
      apply (clarsimp simp: not_in_release_q_def)
      apply (fastforce dest!: ntfn_queues_release_queue_disjoint)
     apply (fastforce simp: list_queue_relation_def)
    apply (rule hoare_vcg_conj_lift_pre_fix)
     apply (rule hoare_weaken_pre)
      apply (rule mapM_x_inv_wp2[
                    where I="valid_objs and ntfn_at_pred (\<lambda>ntfn. \<not> isActive ntfn) ntfn_ptr"
                      and V="\<lambda>xs. ntfn_at_pred (\<lambda>ntfn. ntfn_queue (ntfn_obj ntfn) = xs) ntfn_ptr"])
       apply (clarsimp simp: ntfn_at_pred_def)
       apply (force simp: valid_obj_def valid_ntfn_def isActive_def split: ntfn.splits)
      apply (wpsimp wp: remove_and_restart_ntfn_queued_thread_dequeues_head)
      apply (force simp: ntfn_at_pred_def valid_obj_def valid_ntfn_def
                  split: Structures_A.ntfn.splits)
     apply (fastforce simp: ntfn_at_pred_def obj_at_def isActive_def)
    apply (rule hoare_weaken_pre)
     apply (rule_tac Q="\<lambda>t s. in_ntfn_queue_at t ntfn_ptr s \<and> \<not> ep_queued t s
                              \<and> not_queued t s \<and> not_in_release_q t s \<and> scheduler_act_not t s
                              \<and> st_tcb_at is_blocked_on_ntfn t s \<and> t \<noteq> idle_thread s"
                  in ball_mapM_x_scheme)
       apply (wpsimp wp: remove_and_restart_ntfn_queued_thread_other
                         remove_and_restart_ntfn_queued_thread_in_ntfn_queue_at_other)
      apply (wpsimp wp: remove_and_restart_ntfn_queued_thread_other
                        remove_and_restart_ntfn_queued_thread_valid_sched
                        remove_and_restart_ntfn_queued_thread_ep_queues_blocked
                        remove_and_restart_ntfn_queued_thread_ntfn_queues_blocked)
      apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps)
     apply fastforce
   apply clarsimp
   apply (rename_tac s)
   apply (frule invs_sym_refs)
   apply (frule sym_refs_ntfn_queues_blocked)
   apply (frule sym_refs_ep_queues_blocked)
   apply (frule valid_sched_valid_ready_qs)
   apply (frule valid_sched_valid_release_q)
   apply (prop_tac "ntfn_queues_of s ntfn_ptr = Some queue")
    apply (fastforce simp: opt_map_def obj_at_def split: option.splits)
   apply (prop_tac "\<forall>p \<in> set queue. st_tcb_at is_blocked_on_ntfn p s")
    apply (clarsimp simp: ntfn_queues_blocked_def)
    apply (drule_tac x=ntfn_ptr in spec)
    apply (drule_tac x=queue in spec)
    apply (fastforce elim!: st_tcb_weakenE simp: ntfn_blocked_def
                     split: Structures_A.thread_state.splits)
    apply (intro conjI impI allI ballI; fastforce?)
         apply (force dest: ep_queues_ntfn_queues_disjoint simp: in_ntfn_queue_at_def ntfn_queued_def)
        apply (force dest: ep_queues_ntfn_queues_disjoint simp: in_ep_queue_at_def ep_queued_def)
       apply (clarsimp simp: not_queued_def)
       apply (force dest!: ntfn_queues_ready_queues_disjoint)
      apply (clarsimp simp: not_in_release_q_def)
      apply (fastforce dest!: ntfn_queues_release_queue_disjoint)
     apply (fastforce intro: weak_valid_sched_action_scheduler_action_not
                             is_blocked_on_ntfn_not_runnable)
    apply (rule not_idle_thread', fastforce+)
   apply (rule_tac Q'="\<lambda>_. pspace_aligned' and pspace_distinct' and pspace_bounded'
                           and valid_objs' and valid_sched_pointers and sym_heap_sched_pointers"
                in hoare_post_imp)
    apply fastforce
   apply (wpsimp wp: whileLoop_valid_inv)
   apply fastforce
  apply add_pspace_adb'
  apply (rule corres_symb_exec_r_conj_ex_abs_forwards[OF _ get_ntfn_sp', rotated]; (solves wpsimp)?)
   apply wpsimp
   apply (force intro!: ntfn_at_cross simp: ex_abs_def ntfn_at_pred_def obj_at_def is_ntfn_def)
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (frule state_relation_pspace_relation)
   apply (clarsimp simp: pspace_relation_heap_pspace_relation heap_pspace_relation_def
                         map_relation_def opt_map_def obj_at'_def ntfn_at_pred_def ntfn_relation_def
                  split: option.splits Structures_A.ntfn.splits)
  apply (corres corres: rescheduleRequired_corres)
   apply (frule valid_sched_valid_ready_qs)
   apply (fastforce dest: valid_sched_valid_release_q)
  apply fastforce
  done

lemma replyUnlink_valid_irq_node'[wp]:
  "replyUnlink r t \<lbrace>\<lambda> s. valid_irq_node' (irq_node' s) s\<rbrace>"
  unfolding replyUnlink_def
  by (wpsimp wp: valid_irq_node_lift gts_wp')

lemma updateSchedContext_valid_pspace'[wp]:
  "\<lbrace>valid_pspace' and
    (\<lambda>s. \<forall>sc. (valid_sched_context' sc s \<longrightarrow> valid_sched_context' (f sc) s)
              \<and> (valid_sched_context_size' sc \<longrightarrow> valid_sched_context_size' (f sc)))\<rbrace>
   updateSchedContext scp f
   \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  unfolding updateSchedContext_def
  apply wpsimp
  by (fastforce simp: obj_at'_def  valid_obj'_def)

lemma refillPopHead_valid_pspace'[wp]:
  "refillPopHead scp \<lbrace>valid_pspace'\<rbrace>"
  unfolding refillPopHead_def updateSchedContext_def
  apply (wpsimp wp: whileLoop_valid_inv getRefillNext_wp)
  by (fastforce simp: obj_at'_def valid_obj'_def MIN_REFILLS_def refillSize_def refillNext_def
                      valid_sched_context'_def valid_sched_context_size'_def scBits_simps
               dest!: opt_predD
               elim!: opt_mapE)

lemma refillPopHead_not_live'[wp]:
  "refillPopHead scPtr \<lbrace>\<lambda>s. P (ko_wp_at' (Not \<circ> live') p s)\<rbrace>"
  unfolding refillPopHead_def
  apply (wpsimp wp: updateSchedContext_wp getRefillNext_wp)
  apply (clarsimp simp: ko_wp_at'_def obj_at'_def opt_map_red live'_def live_sc'_def gen_objBits_simps
                        ps_clear_upd)
  done

lemma updateRefillHd_ko_wp_at_not_live'[wp]:
  "updateRefillHd scPtr f \<lbrace>\<lambda>s. P (ko_wp_at' (Not \<circ> live') p s)\<rbrace>"
  unfolding updateRefillHd_def
  apply (wpsimp wp: updateSchedContext_wp)
  apply (clarsimp simp: ko_wp_at'_def obj_at'_def opt_map_red gen_objBits_simps ps_clear_upd live'_def)
  done

crunch ifCondRefillUnblockCheck
  for not_live'[wp]: "\<lambda>s. P (ko_wp_at' (Not \<circ> live') p' s)"
  (simp: crunch_simps wp: crunch_wps simp_del: comp_apply)

lemma updateRefillHd_refs_of'[wp]:
  "updateRefillHd sc_ptr f \<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>"
  unfolding updateRefillHd_def updateSchedContext_def
  apply (wpsimp wp: setObject_state_refs_of_eq)
  apply (fastforce elim!: rsubst[where P=P] simp: obj_at'_def state_refs_of'_def split: if_splits)
  done

lemma refillPopHead_refs_of'[wp]:
  "refillPopHead sc_ptr \<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>"
  unfolding refillPopHead_def updateSchedContext_def
  apply (wpsimp wp: getRefillNext_wp)
  apply (fastforce elim!: rsubst[where P=P] simp: obj_at'_def state_refs_of'_def split: if_splits)
  done

crunch ifCondRefillUnblockCheck
  for valid_pspace'[wp]: valid_pspace'
  and replies_of'[wp]: "\<lambda>s. P (replies_of' s)"
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and valid_machine_state'[wp]: valid_machine_state'
  and ksInterrupt[wp]: "\<lambda>s. P (ksInterruptState s)"
  and refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  and valid_replies'[wp]: valid_replies'
  and valid_mdb'[wp]: valid_mdb'
  and valid_bitmaps[wp]: valid_bitmaps
  (wp: crunch_wps simp: crunch_simps valid_pspace'_def ignore: threadSet)

lemma valid_mdb'_ksSchedulerAction_update[simp]:
  "valid_mdb' (ksSchedulerAction_update f s) = valid_mdb' s"
  by (clarsimp simp: valid_mdb'_def)

crunch possibleSwitchTo
  for valid_replies'[wp]: valid_replies'
  and pspace_canonical'[wp]: pspace_canonical'
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  and no_0_obj'[wp]: no_0_obj'
  and valid_mdb'[wp]: valid_mdb'
  and valid_pspace'[wp]: valid_pspace'
  and valid_bitmaps[wp]: valid_bitmaps
  (wp: crunch_wps simp: crunch_simps simp: valid_pspace'_def)

(* FIXME RT: move *)
lemma valid_pspace'_pspace_aligned'[elim!]:
  "valid_pspace' s \<Longrightarrow> pspace_aligned' s"
  by fastforce

lemma valid_pspace'_pspace_distinct'[elim!]:
  "valid_pspace' s \<Longrightarrow> pspace_distinct' s"
  by fastforce

lemma valid_pspace'_pspace_bounded'[elim!]:
  "valid_pspace' s \<Longrightarrow> pspace_bounded' s"
  by fastforce

crunch removeAndRestartEPQueuedThread, removeAndRestartNTFNQueuedThread,
       removeAndRestartBadgedThread
  for pspace_canonical'[wp]: pspace_canonical'
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  and no_0_obj'[wp]: no_0_obj'
  and valid_mdb'[wp]: valid_mdb'
  and valid_bitmaps[wp]: valid_bitmaps
  and if_unsafe_then_cap'[wp]: if_unsafe_then_cap'
  and valid_global_refs'[wp]: valid_global_refs'
  and valid_arch_state'[wp]: valid_arch_state'
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and valid_irq_handlers'[wp]: valid_irq_handlers'
  and valid_irq_states'[wp]: valid_irq_states'
  and valid_machine_state'[wp]: valid_machine_state'
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and ksDomScheduleStart[wp]: "\<lambda>s. P (ksDomScheduleStart s)"
  and sym_heap_reply_pointers[wp]: sym_heap_reply_pointers
  and irqs_masked'[wp]: irqs_masked'
  and valid_dom_schedule'[wp]: valid_dom_schedule'
  and untyped_ranges_zero'[wp]: untyped_ranges_zero'
  (wp: crunch_wps valid_mdb'_lift valid_dom_schedule'_lift threadSet_urz simp: crunch_simps
   ignore: threadSet)

lemma restartThreadIfNoFault_valid_replies':
  "\<lbrace>valid_replies' and st_tcb_at' (\<lambda>st. \<not> isBlockedOnReply st) t\<rbrace>
   restartThreadIfNoFault t
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  unfolding restartThreadIfNoFault_def
  apply (wpsimp wp: sts'_valid_replies' threadGet_wp hoare_drop_imps)
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def isBlockedOnReply_def split: thread_state.splits)
  done

lemma removeAndRestartEPQueuedThread_valid_replies':
  "\<lbrace>valid_replies' and pspace_aligned' and pspace_distinct'\<rbrace>
   removeAndRestartEPQueuedThread t epptr
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  apply (clarsimp simp: removeAndRestartEPQueuedThread_def)
  apply (rule bind_wp[OF _ gts_sp'])
  apply (rule bind_wp[OF _ assert_sp])
  \<comment> \<open>step over tcbEPDequeue\<close>
  apply forward_inv_step
  apply (rule bind_wp[OF _ gts_sp'])
  apply (rule bind_wp[OF _ stateAssert_sp])
  apply (wpsimp wp: restartThreadIfNoFault_valid_replies' replyUnlink_st_tcb_at'
                    hoare_vcg_all_lift hoare_vcg_imp_lift' gts_wp')
  by (elim disjE;
      fastforce dest!: valid_replies'_other_state
                 simp: st_tcb_at'_def obj_at'_def isSend_def isReceive_def isBlockedOnReply_def
                split: thread_state.splits)

lemma removeAndRestartNTFNQueuedThread_valid_replies':
  "\<lbrace>valid_replies' and pspace_aligned' and pspace_distinct'\<rbrace>
   removeAndRestartNTFNQueuedThread t ntfnPtr
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  apply (clarsimp simp: removeAndRestartNTFNQueuedThread_def)
  apply (rule bind_wp[OF _ gts_sp'])
  apply (wpsimp wp: sts'_valid_replies' hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (fastforce dest!: valid_replies'_other_state
                    simp: st_tcb_at'_def obj_at'_def isBlockedOnNtfn_def isBlockedOnReply_def
                   split: thread_state.splits)
  done

lemma removeAndRestartEPQueuedThread_invs'[wp]:
  "removeAndRestartEPQueuedThread t ep_ptr \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: invs'_def valid_pspace'_def)
  apply (wpsimp wp: removeAndRestartEPQueuedThread_valid_replies' valid_irq_node_lift)
  done

lemma replyUnlink_invs'[wp]:
  "\<lbrace>invs' and (\<lambda>s. replyTCBs_of s replyPtr = Some tcbPtr \<longrightarrow> \<not> is_reply_linked replyPtr s)
    and (\<lambda>s. \<not> is_sched_linked tcbPtr s)\<rbrace>
   replyUnlink replyPtr tcbPtr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_pspace'_def
  by (wpsimp wp: replyUnlink_valid_sched_pointers valid_dom_schedule'_lift)

lemma removeAndRestartNTFNQueuedThread_invs'[wp]:
  "removeAndRestartNTFNQueuedThread t ntfnPtr \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: invs'_def valid_pspace'_def)
  apply (wpsimp wp: removeAndRestartNTFNQueuedThread_valid_replies' valid_irq_node_lift)
  done

crunch cancelAllIPC, cancelAllSignals
  for invs'[wp]: invs'
  (wp: crunch_wps)

lemma removeAndRestartEPQueuedThread_st_tcb_at:
  "\<lbrace>st_tcb_at' P t and K (P Inactive \<and> P Restart)\<rbrace>
   removeAndRestartEPQueuedThread t' epptr
   \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  unfolding removeAndRestartEPQueuedThread_def restartThreadIfNoFault_def
  by (wpsimp wp: sts_st_tcb_at'_cases hoare_drop_imps replyUnlink_st_tcb_at')

lemma cancelAllIPC_st_tcb_at:
  "\<lbrace>st_tcb_at' P t and K (P Inactive \<and> P Restart)\<rbrace> cancelAllIPC epptr \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  apply (clarsimp simp: cancelAllIPC_def)
  apply (intro bind_wp[OF _ stateAssert_inv] bind_wp[OF _ get_ep_sp'])
  apply (subst endpoint_IdleEPState_split)
  apply (rule hoare_if; (solves wpsimp)?)
  apply wpsimp
     apply (rule hoare_drop_imps)
     apply (rule get_ep_inv')
    apply (rule_tac Q'="\<lambda>_ _. P Inactive \<and> P Restart" in hoare_post_add)
    apply (wpsimp wp: whileLoop_valid_inv removeAndRestartEPQueuedThread_st_tcb_at hoare_drop_imps)+
  done

lemmas cancelAllIPC_makes_simple[wp] =
       cancelAllIPC_st_tcb_at [where P=simple', simplified]

lemma removeAndRestartNTFNQueuedThread_st_tcb_at:
  "\<lbrace>st_tcb_at' P t and K (P Restart)\<rbrace> removeAndRestartNTFNQueuedThread t' epptr \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  unfolding removeAndRestartNTFNQueuedThread_def restartThreadIfNoFault_def
  by (wpsimp wp: sts_st_tcb_at'_cases hoare_drop_imps replyUnlink_st_tcb_at')

lemma cancelAllSignals_st_tcb_at:
  "\<lbrace>st_tcb_at' P t and K (P Restart)\<rbrace> cancelAllSignals epptr \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  apply (clarsimp simp: cancelAllSignals_def)
  apply (intro bind_wp[OF _ stateAssert_inv] bind_wp[OF _ get_ntfn_sp'])
  apply (rename_tac ntfn)
  apply (case_tac "ntfnState ntfn"; clarsimp; (solves wpsimp)?)
  apply wpsimp
     apply (rule hoare_drop_imps)
     apply (rule get_ntfn_inv')
    apply (rule_tac Q'="\<lambda>_ _. P Restart" in hoare_post_add)
    apply (wpsimp wp: whileLoop_valid_inv removeAndRestartNTFNQueuedThread_st_tcb_at hoare_drop_imps)+
  done

lemmas cancelAllSignals_makes_simple[wp] =
       cancelAllSignals_st_tcb_at [where P=simple', simplified]

lemma threadSet_unlive_other:
  "\<lbrace>ko_wp_at' (Not \<circ> live') p and K (p \<noteq> t)\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>rv. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  by (clarsimp simp: threadSet_def valid_def getObject_def
                     setObject_def in_monad loadObject_default_def
                     ko_wp_at'_def split_def in_magnitude_check
                     gen_objBits_simps updateObject_default_def
                     ps_clear_upd)

lemma tcbQueuePrepend_unlive_other:
  "\<lbrace>ko_wp_at' (Not \<circ> live') p and K (p \<noteq> t)\<rbrace>
   tcbQueuePrepend q t
   \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  supply if_split[split del]
  apply (simp add: tcbQueuePrepend_def)
  apply (wpsimp wp: threadGet_wp threadSet_unlive_other hoare_vcg_imp_lift')
  apply (clarsimp simp: tcbQueueEmpty_def list_queue_relation_def)
  apply (rename_tac ts)
  apply (prop_tac "ts \<noteq> []", fastforce)
  apply (frule (1) heap_path_head)
  apply (drule_tac x="hd ts" in bspec, fastforce)
  apply (force simp: live'_def ko_wp_at'_def obj_at'_def opt_pred_def opt_map_def
              split: option.splits thread_state.splits)
  done

lemma tcbSchedEnqueue_unlive_other:
  "\<lbrace>ko_wp_at' (Not \<circ> live') p and K (p \<noteq> t)\<rbrace>
   tcbSchedEnqueue t
   \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  unfolding tcbSchedEnqueue_def
  by (wpsimp wp: threadGet_wp threadSet_unlive_other tcbQueuePrepend_unlive_other)

lemma rescheduleRequired_unlive[wp]:
  "rescheduleRequired \<lbrace>ko_wp_at' (Not \<circ> live') p\<rbrace>"
  supply comp_apply[simp del]
  unfolding rescheduleRequired_def
  apply (wpsimp wp: getSchedulable_wp tcbSchedEnqueue_unlive_other)
  apply (fastforce simp: schedulable'_def opt_pred_def  obj_at'_def
                         live'_def ko_wp_at'_def opt_map_def o_def)
  done

crunch scheduleTCB
  for unlive[wp]: "ko_wp_at' (Not \<circ> live') p"
  (wp: crunch_wps isSchedulable_inv simp: crunch_simps)

lemma setThreadState_unlive_other:
  "\<lbrace>ko_wp_at' (Not \<circ> live') p and K (p \<noteq> t)\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  unfolding setThreadState_def
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: ko_wp_at'_def obj_at'_def)
  done

lemma setThreadState_Inactive_unlive:
  "setThreadState Inactive tptr \<lbrace>ko_wp_at' (Not o live') p\<rbrace>"
  apply (clarsimp simp: setThreadState_def)
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: live'_def ko_wp_at'_def obj_at'_def gen_objBits_simps ps_clear_upd
                        RISCV64.hyp_live'_def) (* FIXME: rt arch-split *)
  done

lemma possibleSwitchTo_unlive_other:
  "\<lbrace>ko_wp_at' (Not \<circ> live') p and K (p \<noteq> t) and valid_tcbs'\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  unfolding possibleSwitchTo_def inReleaseQueue_def
  by (wpsimp wp: tcbSchedEnqueue_unlive_other threadGet_wp rescheduleRequired_unlive)

lemma cancelAllIPC_unlive[wp]:
  "\<lbrace>\<top>\<rbrace> cancelAllIPC epPtr \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> live') epPtr\<rbrace>"
  apply (clarsimp simp: cancelAllIPC_def)
  apply (rule bind_wp[OF _ stateAssert_sp])+
  apply (subst endpoint_IdleEPState_split)
   apply wpsimp
       apply (rule_tac Q'="\<lambda>ep. ko_at' ep epPtr" in hoare_post_imp)
        apply (clarsimp simp: live'_def ko_wp_at'_def obj_at'_def)
       apply (wpsimp wp: getEndpoint_wp)+
  apply (clarsimp simp: live'_def ko_wp_at'_def obj_at'_def)
  done

lemma tcbNTFNDequeue_ntfnBoundTCB[wp]:
  "tcbNTFNDequeue tcbPtr ntfnPtr \<lbrace>obj_at' (\<lambda>ntfn. P (ntfnBoundTCB ntfn)) ntfnPtr\<rbrace>"
  apply (clarsimp simp: tcbNTFNDequeue_def)
  apply forward_inv_step+
  apply (wpsimp wp: updateNotification_wp hoare_drop_imps hoare_vcg_all_lift)
  apply (fastforce simp: obj_at'_def ps_clear_upd gen_objBits_simps)
  done

lemma tcbNTFNDequeue_ntfnSc[wp]:
  "tcbNTFNDequeue tcbPtr ntfnPtr \<lbrace>obj_at' (\<lambda>ntfn. P (ntfnSc ntfn)) ntfnPtr\<rbrace>"
  apply (clarsimp simp: tcbNTFNDequeue_def)
  apply forward_inv_step+
  apply (wpsimp wp: updateNotification_wp hoare_drop_imps hoare_vcg_all_lift)
  apply (fastforce simp: obj_at'_def ps_clear_upd gen_objBits_simps)
  done

crunch possibleSwitchTo, ifCondRefillUnblockCheck
  for obj_at'_ntfn[wp]: "\<lambda>s. P (obj_at' (Q :: notification \<Rightarrow> bool) p s)"
  (wp: crunch_wps simp: crunch_simps)

lemma removeAndRestartNTFNQueuedThread_ntfnBoundTCB[wp]:
  "removeAndRestartNTFNQueuedThread tcbPtr ntfnPtr \<lbrace>obj_at' (\<lambda>ntfn. P (ntfnBoundTCB ntfn)) ntfnPtr\<rbrace>"
  unfolding removeAndRestartNTFNQueuedThread_def
  by (wpsimp wp: gts_wp')

lemma removeAndRestartNTFNQueuedThread_ntfnSc[wp]:
  "removeAndRestartNTFNQueuedThread tcbPtr ntfnPtr \<lbrace>obj_at' (\<lambda>ntfn. P (ntfnSc ntfn)) ntfnPtr\<rbrace>"
  unfolding removeAndRestartNTFNQueuedThread_def
  by (wpsimp wp: gts_wp')

lemma cancelAllSignals_unlive:
  "\<lbrace>obj_at' (\<lambda>ntfn. ntfnBoundTCB ntfn = None) ntfnptr and obj_at' (\<lambda>ntfn. ntfnSc ntfn = None) ntfnptr\<rbrace>
   cancelAllSignals ntfnptr
   \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> live') ntfnptr\<rbrace>"
  (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (clarsimp simp: cancelAllSignals_def)
  apply (rule bind_wp[OF _ stateAssert_sp])+
  apply (rule bind_wp[OF _ get_ntfn_sp'])
  apply (rename_tac ntfn)
  apply (case_tac "ntfnState ntfn"; clarsimp)
    apply wpsimp
    apply (clarsimp simp: live'_def ko_wp_at'_def obj_at'_def live_ntfn'_def)
   apply wpsimp
   apply (clarsimp simp: live'_def ko_wp_at'_def obj_at'_def live_ntfn'_def)
  apply wpsimp
     apply (rule_tac Q'="\<lambda>ntfn. ko_at' ntfn ntfnptr and ?pre" in hoare_post_imp)
      apply (clarsimp simp: live'_def ko_wp_at'_def obj_at'_def live_ntfn'_def)
     apply (wpsimp wp: getNotification_wp)+
    apply (rule_tac Q'="\<lambda>_. ?pre" in hoare_post_imp)
     apply fastforce
    apply (wpsimp wp: whileLoop_valid_inv)+
  done

crunch possibleSwitchTo
  for ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps)

crunch cancelBadgedSends
  for pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and pspace_bounded'[wp]: pspace_bounded'
  (wp: crunch_wps)

lemma removeAndRestartBadgedThread_valid_replies':
  "\<lbrace>valid_replies' and valid_sched_pointers and sym_heap_sched_pointers
    and pspace_aligned' and pspace_distinct'\<rbrace>
   removeAndRestartBadgedThread t epptr badge
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  unfolding removeAndRestartBadgedThread_def
  apply (wpsimp wp: gts_wp' hoare_vcg_imp_lift' restartThreadIfNoFault_valid_replies')
  apply (fastforce simp: isBlockedOnReply_def isSend_def st_tcb_at'_def obj_at'_def
                  split: thread_state.splits)
  done

lemma removeAndRestartBadgedThread_invs'[wp]:
  "removeAndRestartBadgedThread t epptr badge \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: invs'_def valid_pspace'_def)
  apply (wpsimp wp: removeAndRestartBadgedThread_valid_replies' valid_irq_node_lift)
  done

crunch cancelBadgedSends
  for invs'[wp]: invs'
  (wp: crunch_wps)

lemma removeAndRestartBadgedThread_corres:
  "corres dc
     (in_ep_queue_at t ep_ptr and not ntfn_queued t and not_queued t and not_in_release_q t
      and st_tcb_at is_blocked_on_send t
      and valid_objs and valid_sched and current_time_bounded
      and ep_queues_blocked and ntfn_queues_blocked
      and pspace_aligned and pspace_distinct)
     (valid_objs' and valid_sched_pointers and sym_heap_sched_pointers and pspace_bounded')
     (remove_and_restart_badged_thread t ep_ptr badge)
     (removeAndRestartBadgedThread t ep_ptr badge)"
  supply if_split[split del]
  apply add_pspace_adb'
  apply (rule corres_cross_add_guard[where Q'="tcb_at' t"])
   apply (fastforce intro!: tcb_at_cross)
  apply (clarsimp simp: remove_and_restart_badged_thread_def removeAndRestartBadgedThread_def)
  apply (rule corres_split_forwards'[OF _ gts_sp gts_sp'])
   apply (corres corres: getThreadState_corres)
  apply (rename_tac st st')
  apply (rule corres_assert_gen_asm_cross_forwards)
   apply (force dest!: st_tcb_at_coerce_concrete is_blocked_on_send_isSend
                 simp: ep_queues_blocked_def in_ep_queue_at_def st_tcb_at'_def obj_at'_def)
  apply (clarsimp simp: when_def)
  apply (rule corres_if_strong')
    apply (clarsimp simp: thread_state_relation_def isSend_def; case_tac st; case_tac st'; clarsimp)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_split[OF tcbEPDequeue_corres], simp, simp)
       apply (rule restartThreadIfNoFault_corres)
      apply (wpsimp wp: tcb_ep_dequeue_not_ep_queued)
     apply wpsimp
    apply clarsimp
    apply (frule valid_sched_valid_ready_qs)
    apply (fastforce dest: valid_sched_valid_release_q)
   apply fastforce
  apply clarsimp
  done

lemma remove_and_restart_badged_thread_ep_queues_blocked:
  "\<lbrace>ep_queues_blocked and in_ep_queue_at t ep_ptr\<rbrace>
   remove_and_restart_badged_thread t ep_ptr badge
   \<lbrace>\<lambda>_. ep_queues_blocked\<rbrace>"
  unfolding remove_and_restart_badged_thread_def restart_thread_if_no_fault_def
  by (wpsimp wp: set_thread_state_ep_queues_blocked_not_queued tcb_ep_dequeue_not_ep_queued gts_wp)

lemma remove_and_restart_badged_thread_ntfn_queues_blocked:
  "\<lbrace>ntfn_queues_blocked and not ntfn_queued t\<rbrace>
   remove_and_restart_badged_thread t ep_ptr badge
   \<lbrace>\<lambda>_. ntfn_queues_blocked\<rbrace>"
  unfolding remove_and_restart_badged_thread_def restart_thread_if_no_fault_def
  by (wpsimp wp: set_thread_state_ntfn_queues_blocked_not_queued tcb_ep_dequeue_not_ep_queued gts_wp)

lemma remove_and_restart_badged_thread_other:
  "\<lbrace>\<lambda>s. Q (st_tcb_at P t s) \<and> t' \<noteq> t\<rbrace>
   remove_and_restart_badged_thread t' epptr badge
   \<lbrace>\<lambda>_ s. Q (st_tcb_at P t s)\<rbrace>"
  unfolding remove_and_restart_badged_thread_def
  by (wpsimp wp: restart_thread_if_no_fault_other reply_unlink_tcb_st_tcb_at_other gts_wp
                 hoare_vcg_all_lift hoare_vcg_imp_lift')

lemma remove_and_restart_badged_thread_in_ep_queue_at_other:
  "\<lbrace>\<lambda>s. in_ep_queue_at t epptr s \<and> t' \<noteq> t\<rbrace>
   remove_and_restart_badged_thread t' epptr badge
   \<lbrace>\<lambda>_ s. in_ep_queue_at t epptr s\<rbrace>"
  unfolding remove_and_restart_badged_thread_def
  by (wpsimp wp: tcb_ep_dequeue_in_ep_queue_at_other gts_wp)

lemma cancelBadgedSends_corres:
  "corres dc
     (invs and valid_sched and ep_at epptr and current_time_bounded) invs'
     (cancel_badged_sends epptr bdg) (cancelBadgedSends epptr bdg)"
  apply add_sym_refs
  apply add_sch_act_wf
  apply (rule_tac Q'="ep_at' epptr" in corres_cross_add_guard)
   apply (fastforce intro!: ep_at_cross)
  apply (clarsimp simp: cancel_badged_sends_def cancelBadgedSends_def)
  apply (rule corres_stateAssert_ignore, solves simp)+
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro: ksReadyQueues_asrt_cross)
  apply (rule corres_split_forwards'[OF _ get_simple_ko_sp get_ep_sp'])
   apply (corres corres: getEndpoint_corres)
  apply (rename_tac ep ep')
  apply (case_tac ep; simp add: ep_relation_def)
  apply (rename_tac queue)
  apply (rule_tac Q'="\<lambda>s. list_queue_relation
                            queue (epQueue ep') (tcbSchedNexts_of s) (tcbSchedPrevs_of s)"
               in corres_cross_add_guard)
   apply (frule state_relation_ep_queues_relation)
   apply (fastforce simp: ep_queues_relation_def opt_map_def eps_of_kh_def obj_at_def obj_at'_def
                   split: option.splits)
  apply (rule_tac F="distinct queue" in corres_req)
   apply (fastforce intro: heap_ls_distinct simp: list_queue_relation_def)
  apply (rule corres_stateAssert_ignore)
   apply (rule list_queue_relation_tcb_queue_head_end_valid)
    apply fastforce
   apply (fastforce dest: in_ep_queue_sched_flag_set[rotated]
                    elim: sym_refs_ep_queues_blocked[OF invs_sym_refs]
                    simp: eps_of_kh_def opt_map_def obj_at_def
                   split: option.splits)
  apply (rule_tac Q="\<lambda>_ s. ep_queues_blocked s \<and> ntfn_queues_blocked s
                           \<and> valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_sched s
                           \<and> heap_refs_inv (tcb_scps_of s) (sc_tcbs_of s)
                           \<and> current_time_bounded s "
              and Q'="\<lambda>_. valid_tcbs' and valid_sched_pointers"
               in corres_split_forwards'[where r'=dc])
     apply (rule stronger_corres_guard_imp)
       apply (clarsimp simp: threadGet_def)
       apply (subst bind_dummy_ret_val)+
       apply (rule_tac P="\<lambda>ls s. distinct ls
                                 \<and> (ls \<noteq> []
                                    \<longrightarrow> (\<forall>p \<in> set ls. in_ep_queue_at p epptr s \<and> \<not> ntfn_queued p s
                                                      \<and> not_queued p s \<and> not_in_release_q p s
                                                      \<and> st_tcb_at is_blocked_on_send p s))
                                 \<and> valid_objs s \<and> valid_idle s
                                 \<and> ep_queues_blocked s \<and> ntfn_queues_blocked s
                                 \<and> pspace_aligned s \<and> pspace_distinct s
                                 \<and> heap_refs_inv (tcb_scps_of s) (sc_tcbs_of s)
                                 \<and> valid_sched s \<and> current_time_bounded s"
                   and P'="\<lambda>_. valid_objs' and valid_sched_pointers and sym_heap_sched_pointers
                               and pspace_aligned' and pspace_distinct' and pspace_bounded'
                               and ep_at' epptr"
                    in corres_mapM_x_whileLoop[where nexts_of=tcbSchedNexts_of])
             apply (rule corres_guard_imp)
               apply (rule removeAndRestartBadgedThread_corres)
              apply (fastforce dest: valid_sched_valid_release_q)
             apply clarsimp
            apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
                 apply wpsimp
                 apply (fastforce elim: distinct_tl)
                apply (wpsimp wp: remove_and_restart_badged_thread_in_ep_queue_at_other
                                  remove_and_restart_badged_thread_other
                                  hoare_vcg_const_imp_lift hoare_vcg_ball_lift)
                apply (fastforce dest!: list.set_sel(2) distinct_hd_not_in_tl
                                 intro: weak_valid_sched_action_scheduler_action_not
                                        blocked_on_send_not_runnable)
               apply (wpsimp simp: remove_and_restart_badged_thread_def wp: gts_wp)
               apply (fastforce dest!: not_idle_thread' hd_in_set
                                 simp: st_tcb_at_def obj_at_def)
              apply (wpsimp wp: remove_and_restart_badged_thread_ep_queues_blocked)
             apply (wpsimp wp: remove_and_restart_badged_thread_ntfn_queues_blocked)
            apply (wpsimp wp: remove_and_restart_badged_thread_valid_sched)
            apply (intro conjI)
             apply (clarsimp simp: obj_at_kh_kheap_simps)
            apply (erule not_idle_thread')
             apply fastforce
            apply fastforce
           apply wpsimp
          apply (wpsimp wp: hoare_vcg_const_imp_lift hoare_vcg_ball_lift
                            removeAndRestartBadgedThread_sym_heap_sched_pointers)
         apply (rule monadic_rewrite_guard_imp)
          apply (rule threadGet_return_tcbSchedNexts_of[simplified threadGet_def])
         apply (force intro!: tcb_at_cross simp: ex_abs_def)
        apply wpsimp
        apply (force intro!: tcb_at_cross simp: ex_abs_def)
       apply (wpsimp wp: removeAndRestartBadgedThread_tcbSchedNexts_of_other)
       apply (clarsimp simp: ex_abs_def)
       apply (rename_tac s)
       apply (rule conjI)
        apply clarsimp
        apply (prop_tac "scheduler_action s = switch_thread t'")
         apply (drule state_relation_sched_act_relation)
         apply (clarsimp simp: sched_act_relation_def)
         apply (case_tac "scheduler_action s"; clarsimp)
        apply (fastforce dest!: valid_sched_weak_valid_sched_action
                                weak_valid_sched_action_scheduler_action_not
                         intro: blocked_on_send_not_runnable simp: scheduler_act_not_def)
       apply (frule state_relation_ep_queues_relation)
       apply (clarsimp simp: ep_queues_relation_def)
       apply (drule_tac x=epptr in spec)
       apply (fastforce simp: list_queue_relation_def)
      apply clarsimp
      apply (rename_tac s s')
      apply (frule invs_sym_refs)
      apply (frule sym_refs_ep_queues_blocked)
      apply (frule valid_sched_valid_ready_qs)
      apply (frule valid_sched_valid_release_q)
      apply (prop_tac "ep_queues_of s epptr = Some queue")
       apply (fastforce simp: opt_map_def eps_of_kh_def obj_at_def split: option.splits)
      apply (prop_tac "\<forall>p \<in> set queue. st_tcb_at is_blocked_on_send p s")
       apply (fastforce dest: in_send_ep_queue_st_tcb_at simp: obj_at_def elim: st_tcb_weakenE)
      apply (intro conjI impI allI; fastforce?)
      apply (clarsimp simp: in_ep_queue_at_def)
      apply (intro conjI impI allI)
        apply (force dest: ep_queues_ntfn_queues_disjoint
                     simp: in_ntfn_queue_at_def ntfn_queued_def)
       apply (clarsimp simp: not_queued_def)
       apply (force dest!: ep_queues_ready_queues_disjoint)
      apply (clarsimp simp: not_in_release_q_def)
      apply (fastforce dest!: ep_queues_release_queue_disjoint)
     apply (fastforce simp: list_queue_relation_def)
    apply (rule hoare_weaken_pre)
     apply (rule_tac Q="\<lambda>t s. in_ep_queue_at t epptr s \<and> \<not> ntfn_queued t s
                              \<and> not_queued t s \<and> not_in_release_q t s \<and> scheduler_act_not t s
                              \<and> st_tcb_at is_blocked_on_send t s \<and> t \<noteq> idle_thread s"
                  in ball_mapM_x_scheme)
       apply (wpsimp wp: remove_and_restart_badged_thread_other
                         remove_and_restart_badged_thread_in_ep_queue_at_other)
      apply (wpsimp wp: remove_and_restart_badged_thread_valid_sched
                        remove_and_restart_badged_thread_ep_queues_blocked
                        remove_and_restart_badged_thread_ntfn_queues_blocked)
      apply (clarsimp simp: obj_at_kh_kheap_simps)
     apply fastforce
    apply (clarsimp simp: valid_ep_def cong: conj_cong)
    apply (rename_tac s )
    apply (frule invs_sym_refs)
    apply (frule sym_refs_ep_queues_blocked)
    apply (frule valid_sched_valid_ready_qs)
    apply (frule valid_sched_valid_release_q)
    apply (prop_tac "ep_queues_of s epptr = Some queue")
     apply (fastforce simp: opt_map_def eps_of_kh_def obj_at_def split: option.splits)
    apply (prop_tac "\<forall>p \<in> set queue. st_tcb_at is_blocked_on_send p s")
     apply (fastforce dest: in_send_ep_queue_st_tcb_at simp: obj_at_def elim: st_tcb_weakenE)
    apply (intro conjI impI allI ballI; fastforce?)
         apply (force simp: in_ep_queue_at_def ep_at_pred_def obj_at_def)
        apply (clarsimp simp: in_ep_queue_at_def)
        apply (force dest: ep_queues_ntfn_queues_disjoint
                     simp: in_ntfn_queue_at_def ntfn_queued_def)
       apply (clarsimp simp: not_queued_def)
       apply (force dest!: ep_queues_ready_queues_disjoint)
      apply (clarsimp simp: not_in_release_q_def)
      apply (fastforce dest!: ep_queues_release_queue_disjoint)
     apply (fastforce intro: weak_valid_sched_action_scheduler_action_not
                             blocked_on_send_not_runnable)
    apply (rule not_idle_thread', fastforce+)
   apply (rule_tac Q'="\<lambda>_. pspace_aligned' and pspace_distinct' and pspace_bounded'
                           and valid_objs' and valid_sched_pointers and sym_heap_sched_pointers"
                in hoare_post_imp)
    apply fastforce
   apply (wpsimp wp: whileLoop_valid_inv removeAndRestartBadgedThread_sym_heap_sched_pointers)
   apply fastforce
  apply (corres corres: rescheduleRequired_corres)
   apply (frule valid_sched_valid_ready_qs)
   apply (fastforce dest: valid_sched_valid_release_q)
  apply fastforce
  done

crunch schedContextCancelYieldTo, tcbReleaseRemove, setThreadState, updateRestartPC
  for tcbQueued[wp]: "obj_at' (\<lambda>obj. P (tcbQueued obj)) t"
  (cong: if_cong)

lemma suspend_unqueued[wp]:
  "\<lbrace>\<top>\<rbrace> suspend t \<lbrace>\<lambda>_. obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  unfolding suspend_def comp_def
  by (wpsimp wp: tcbSchedDequeue_not_tcbQueued[simplified comp_def])

crunch schedContextCancelYieldTo, tcbQueueRemove, setThreadState
  for not_tcbInReleaseQueue[wp]: "obj_at' (\<lambda>tcb. P (tcbInReleaseQueue tcb)) t"
  (wp: crunch_wps cong: if_cong)

lemma tcbReleaseRemove_flag_not_set:
  "\<lbrace>\<top>\<rbrace> tcbReleaseRemove t \<lbrace>\<lambda>_. obj_at' (Not \<circ> tcbInReleaseQueue) t\<rbrace>"
  apply (simp add: tcbReleaseRemove_def)
  apply (wpsimp wp: inReleaseQueue_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma suspend_flag_not_set:
  "\<lbrace>\<top>\<rbrace> suspend t \<lbrace>\<lambda>_. obj_at' (Not \<circ> tcbInReleaseQueue) t\<rbrace>"
  unfolding suspend_def comp_def
  by (wpsimp wp: tcbReleaseRemove_flag_not_set[simplified comp_def])

lemma asUser_tcbQueued[wp]:
  "asUser t' f \<lbrace>\<lambda>s. Q (obj_at' (P \<circ> tcbQueued) t s)\<rbrace>"
  unfolding asUser_def threadGet_stateAssert_gets_asUser
  by (wpsimp wp: threadSet_obj_at'_no_state simp: asUser_fetch_def obj_at'_def)

lemmas asUser_st_tcb_at'[wp] = asUser_obj_at [folded st_tcb_at'_def]

end