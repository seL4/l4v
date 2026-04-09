(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory IpcCancel_R
imports
  Schedule_R
  Reply_R
  "Lib.SimpStrategy"
begin

arch_requalify_facts
  valid_global_refs_lift'

crunch updateEndpoint, updateNotification, tcbNTFNDequeue, tcbNTFNAppend, tcbEPDequeue, tcbEPAppend,
       removeAndRestartEPQueuedThread, removeAndRestartNTFNQueuedThread,
       cancelBadgedSends, cancelAllSignals, cancelAllIPC, cancelIPC, cancelSignal
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps)

global_interpretation updateEndpoint: typ_at_all_props' "updateEndpoint epPtr f"
  by typ_at_props'

global_interpretation updateNotification: typ_at_all_props' "updateNotification ntfnPtr f"
  by typ_at_props'

global_interpretation tcbNTFNDequeue: typ_at_all_props' "tcbNTFNDequeue tcbPtr ntfnPtr"
  by typ_at_props'

global_interpretation tcbNTFNAppend: typ_at_all_props' "tcbNTFNAppend tcbPtr ntfnPtr"
  by typ_at_props'

global_interpretation tcbEPDequeue: typ_at_all_props' "tcbEPDequeue tcbPtr epPtr"
  by typ_at_props'

global_interpretation tcbEPAppend: typ_at_all_props' "tcbEPAppend tcbPtr epPtr state"
  by typ_at_props'

global_interpretation tcbQueueRemove: typ_at_all_props' "tcbQueueRemove queue tcbPtr"
  by typ_at_props'

global_interpretation removeAndRestartEPQueuedThread:
  typ_at_all_props' "removeAndRestartEPQueuedThread t epptr"
  by typ_at_props'

global_interpretation removeAndRestartNTFNQueuedThread:
  typ_at_all_props' "removeAndRestartNTFNQueuedThread t ntfnPtr"
  by typ_at_props'

global_interpretation removeAndRestartBadgedThread:
  typ_at_all_props' "removeAndRestartBadgedThread t epptr badge"
  by typ_at_props'

global_interpretation cancelBadgedSends: typ_at_all_props' "cancelBadgedSends epptr badge"
  by typ_at_props'

global_interpretation cancelAllSignals: typ_at_all_props' "cancelAllSignals ntfnPtr"
  by typ_at_props'

global_interpretation cancelAllIPC: typ_at_all_props' "cancelAllIPC epptr"
  by typ_at_props'

global_interpretation cancelIPC: typ_at_all_props' "cancelIPC tptr"
  by typ_at_props'

global_interpretation cancelSignal: typ_at_all_props' "cancelSignal threadPtr ntfnPtr"
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch-split*)

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
  unfolding cancelSignal_def replyRemoveTCB_def cleanReply_def
  by (wpsimp wp: sts_st_tcb_at'_cases_strong getNotification_wp hoare_vcg_imp_lift')

lemma cancelSignal_simple[wp]:
  "\<lbrace>\<top>\<rbrace> cancelSignal t ntfn \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  by (wpsimp wp: cancelSignal_st_tcb_at'_cases)

lemma cancelSignal_pred_tcb_at':
  "\<lbrace>pred_tcb_at' proj P t' and K (t \<noteq> t')\<rbrace>
     cancelSignal t ntfnptr
   \<lbrace>\<lambda>rv. pred_tcb_at' proj P t'\<rbrace>"
  apply (simp add: cancelSignal_def)
  apply (wp sts_pred_tcb_neq' getNotification_wp | wpc | clarsimp)+
  done

crunch cancelIPC, cancelSignal
  (* FIXME RT: VER-1016 *)
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps)

crunch emptySlot
 for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
  (wp: setCTE_pred_tcb_at')

defs capHasProperty_def:
  "capHasProperty ptr P \<equiv> cte_wp_at' (\<lambda>c. P (cteCap c)) ptr"

end

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

context begin interpretation Arch .
crunch emptySlot
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
end

sublocale delete_one_conc_pre < delete_one: typ_at_all_props' "cteDeleteOne slot"
  by typ_at_props'

declare delete_remove1 [simp]
declare delete.simps [simp del]

lemma sch_act_wf_weak_sch_act_wf[elim!]:
  "sch_act_wf (ksSchedulerAction s) s \<Longrightarrow> weak_sch_act_wf (ksSchedulerAction s) s"
  by (clarsimp simp: weak_sch_act_wf_def)

lemma replyTCB_update_corres:
  "corres dc (reply_at rp) (reply_at' rp)
            (set_reply_obj_ref reply_tcb_update rp new)
            (updateReply rp (replyTCB_update (\<lambda>_. new)))"
  apply (simp add: update_sk_obj_ref_def updateReply_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF get_reply_corres])
      apply (rule set_reply_corres)
      apply (simp add: reply_relation_def)
  by (wpsimp simp: obj_at'_def replyPrev_same_def)+

lemma replyUnlinkTcb_corres:
  "corres dc
     (valid_tcbs and pspace_aligned and pspace_distinct
       and st_tcb_at (\<lambda>st. \<exists>ep pl. st = Structures_A.BlockedOnReceive ep (Some rp) pl
                           \<or> st = Structures_A.BlockedOnReply rp) t
       and reply_tcb_reply_at ((=) (Some t)) rp)
        valid_tcbs'
        (reply_unlink_tcb t rp) (replyUnlink rp t)" (is "corres _ _ ?conc_guard _ _")
  apply (rule_tac Q="?conc_guard
                     and st_tcb_at' (\<lambda>st. (\<exists>ep pl. st = BlockedOnReceive ep (receiver_can_grant pl) (Some rp))
                                          \<or> st = BlockedOnReply (Some rp)) t
                     and reply_at' rp"
               in corres_cross_over_guard)
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
         apply (rule corres_split[OF replyTCB_update_corres])
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

lemma updateEndpoint_wp:
  "\<lbrace>\<lambda>s. \<forall>ep :: endpoint. ko_at' ep epPtr s \<longrightarrow> P (set_obj' epPtr (f ep) s)\<rbrace>
   updateEndpoint epPtr f
   \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding updateEndpoint_def setEndpoint_def
  by (wpsimp wp: set_ep'.setObject_wp getEndpoint_wp)

lemma updateNotification_wp:
  "\<lbrace>\<lambda>s. \<forall>ntfn :: notification. ko_at' ntfn ntfnPtr s \<longrightarrow> P (set_obj' ntfnPtr (f ntfn) s)\<rbrace>
   updateNotification ntfnPtr f
   \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding updateNotification_def setNotification_def
  by (wpsimp wp: set_ntfn'.setObject_wp getNotification_wp)

lemma updateEndpoint_dom_eps_of'[wp]:
  "updateEndpoint a b \<lbrace>\<lambda>s. P (dom (eps_of' s))\<rbrace>"
  apply (wpsimp wp: updateEndpoint_wp)
  apply (fastforce elim!: rsubst[where P=P] simp: projectKO_opts_defs obj_at'_def opt_map_red)
  done

lemma set_endpoint_dom_eps_of[wp]:
  "set_endpoint ep_ptr ep \<lbrace>\<lambda>s. P (dom (eps_of s))\<rbrace>"
  apply (wpsimp wp: set_simple_ko_wp)
  apply (fastforce elim: rsubst[where P=P] simp: opt_map_red eps_of_kh_def ep_at_pred_def)
  done

lemma set_endpoint_det_wp[wp]:
  "det_wp (ep_at ep_ptr) (set_endpoint ep_ptr ep)"
  apply (wpsimp wp: get_object_wp simp: set_simple_ko_def)
  apply (clarsimp simp: gen_obj_at_simps is_ep_def)
  apply (rename_tac ko, case_tac ko; clarsimp)
  done

lemmas set_endpoint_no_fail[wp] = det_wp_no_fail[OF set_endpoint_det_wp]

method set_simple_ko_heaps_inv =
  wpsimp wp: set_simple_ko_wp,
  erule rsubst[where P=P],
  clarsimp simp: ep_at_pred_def ntfn_at_pred_def opt_map_def

lemma set_endpoint_scs_fields_of[wp]:
  "set_endpoint ep_ptr ep \<lbrace>\<lambda>s. P (scs_fields_of s)\<rbrace>"
  by set_simple_ko_heaps_inv

lemma set_notification_scs_fields_of[wp]:
  "set_notification ntfn_ptr ntfn \<lbrace>\<lambda>s. P (scs_fields_of s)\<rbrace>"
  by set_simple_ko_heaps_inv

lemma set_endpoint_cnodes_of[wp]:
  "set_endpoint ep_ptr ep \<lbrace>\<lambda>s. P (cnodes_of s)\<rbrace>"
  by set_simple_ko_heaps_inv

lemma set_endpoint_replies_of[wp]:
  "set_endpoint ep_ptr ep \<lbrace>\<lambda>s. P (replies_of s)\<rbrace>"
  by set_simple_ko_heaps_inv

lemma set_notification_cnodes_of[wp]:
  "set_notification ntfn_ptr ntfn \<lbrace>\<lambda>s. P (cnodes_of s)\<rbrace>"
  by set_simple_ko_heaps_inv

lemma set_notification_replies_of[wp]:
  "set_notification ntfn_ptr ntfn \<lbrace>\<lambda>s. P (replies_of s)\<rbrace>"
  by set_simple_ko_heaps_inv

context begin interpretation Arch .

lemma no_fail_setEndpoint[wp]:
  "no_fail (ep_at' ptr) (setEndpoint ptr new)"
  unfolding setEndpoint_def
  apply (wpsimp wp: no_fail_setObject_other)
  apply (clarsimp simp: objBits_simps)
  done

lemma no_fail_updateEndpoint[wp]:
  "no_fail (ep_at' ptr) (updateEndpoint ptr f)"
  by (wpsimp wp: getEndpoint_wp simp: updateEndpoint_def)

crunch updateEndpoint
  for ntfns_of'[wp]: "\<lambda>s. P (ntfns_of' s)"
  (wp: crunch_wps)

crunch updateNotification
  for eps_of'[wp]: "\<lambda>s. P (eps_of' s)"
  (wp: crunch_wps)

lemma set_endpoint_aobjs_of[wp]:
  "set_endpoint ep_ptr ep \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  by set_simple_ko_heaps_inv

lemma set_notification_aobjs_of[wp]:
  "set_notification ntfn_ptr ntfn \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  by set_simple_ko_heaps_inv

crunch updateEndpoint, updateNotification
  for dom_tcbs_of'[wp]: "\<lambda>s. P (dom (tcbs_of' s))"
  and tcbs_of'[wp]: "\<lambda>s. P (tcbs_of' s)"

lemma updateEndpoint_list_queue_relation[wp]:
  "updateEndpoint epPtr f \<lbrace>\<lambda>s. list_queue_relation ls q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)\<rbrace>"
  by (rule hoare_lift_Pf2[where f=tcbSchedNexts_of]; wpsimp)

lemma updateNotification_list_queue_relation[wp]:
  "updateNotification epPtr f \<lbrace>\<lambda>s. list_queue_relation ls q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)\<rbrace>"
  by (rule hoare_lift_Pf2[where f=tcbSchedNexts_of]; wpsimp)

lemma updateEndpoint_epQueues_of_other:
  "\<lbrace>\<lambda>s. P (epQueues_of s p) \<and> p \<noteq> epPtr\<rbrace>
   updateEndpoint epPtr F
   \<lbrace>\<lambda>_ s. P (epQueues_of s p)\<rbrace>"
  apply (wpsimp wp: updateEndpoint_wp)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: opt_map_def)
  done

lemmas corres_assert_gen_asm_cross_forwards =
  corres_assert_gen_asm_cross[where P=P' and P'=P' for P', where Q=Q' and Q'=Q' for Q', simplified]

lemma set_endpoint_cdt_list[wp]:
  "set_endpoint ptr ep \<lbrace>\<lambda>s. P (cdt_list s)\<rbrace>"
  by (wpsimp wp: set_simple_ko_wp)

lemma set_notification_cdt_list[wp]:
  "set_notification ptr ntfn \<lbrace>\<lambda>s. P (cdt_list s)\<rbrace>"
  by (wpsimp wp: set_simple_ko_wp)

lemma in_ep_queue_sched_flag_set:
  "\<lbrakk>ep_queues_blocked s; (s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s;
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
         ghost_relation_wrapper_def[simp del] (*FIXME arch-split RT: not necessary after arch-split*)
         heap_ghost_relation_wrapper_def[simp del] (*FIXME arch-split RT: not necessary after arch-split*)
         return_bind[simp del]
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_distinct_cross)
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
  apply (rcorres_conj_lift \<open>fastforce\<close>)+
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
  apply (rcorres_conj_lift \<open>fastforce\<close>)+
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
  by (rcorres_conj_lift \<open>fastforce\<close>)+

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
  "valid_obj' (KONotification (ntfnQueue_update (\<lambda>_. q) ntfn)) s
   = valid_obj' (KONotification ntfn) s"
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
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_distinct_cross)
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
       apply (clarsimp simp: obj_relation_cuts_def2 obj_at'_def reply_relation_def)
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
             apply (rule corres_split[OF replyUnlinkTcb_corres])
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
  apply (clarsimp simp: objBits_simps)
  done

lemma no_fail_updateNotification[wp]:
  "no_fail (ntfn_at' ptr) (updateNotification ptr f)"
  by (wpsimp wp: getNotification_wp simp: updateNotification_def)

lemma in_ntfn_queue_sched_flag_set:
  "\<lbrakk>ntfn_queues_blocked s; (s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s;
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
  apply (wpsimp wp: get_object_wp simp: set_simple_ko_def)
  apply (safe; clarsimp simp: obj_at_simps is_ntfn_def)
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
         heap_ghost_relation_wrapper_def[simp del] (*FIXME arch-split RT: not necessary after arch-split*)
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_distinct_cross)
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
  apply (rcorres_conj_lift \<open>fastforce\<close>)+
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
  apply (rcorres_conj_lift \<open>fastforce\<close>)+
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
  by (rcorres_conj_lift \<open>fastforce\<close>)+

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

context begin interpretation Arch . (*FIXME: arch-split*)

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
     apply (fastforce dest: invs_no_loops no_loops_direct_simp)
    apply fastforce
    done
qed
end

end

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

lemma gbep_ret':
  "\<lbrakk> st = BlockedOnReceive epPtr r d \<or> st = BlockedOnSend epPtr p1 p2 p3 p4 \<rbrakk>
      \<Longrightarrow> getBlockingObject st = return epPtr"
  by (auto simp add: getBlockingObject_def epBlocked_def assert_opt_def)

lemma replySC_None_not_head:
  "replySC reply = None \<longleftrightarrow> \<not> isHead (replyNext reply)"
  by (fastforce simp: isHead_def getHeadScPtr_def split: reply_next.split_asm option.split_asm)

lemma sr_inv_sc_with_reply_None_helper:
  "\<not> isHead (replyNext reply') \<Longrightarrow>
   sr_inv
     (valid_objs and pspace_aligned and pspace_distinct and valid_replies and
      st_tcb_at ((=) (Structures_A.thread_state.BlockedOnReply rp)) t and
      (\<lambda>s. sym_refs (state_refs_of s)) and (\<lambda>s. sc_with_reply rp s = None) and reply_at rp)
     (valid_objs' and
      (\<lambda>s'. sym_refs (list_refs_of_replies' s')) and sym_heap_sched_pointers and
      (\<lambda>s. sym_refs (state_refs_of' s)) and ko_at' reply' rp and
      ((\<lambda>s'. sc_with_reply' rp s' = None) and pspace_aligned' and pspace_distinct' and pspace_bounded'))
     (do y <-
         do y <-
            when (\<exists>y. replyNext reply' = Some y)
             (updateReply (theReplyNextPtr (replyNext reply'))
               (replyPrev_update Map.empty));
            when (\<exists>y. replyPrev reply' = Some y)
             (updateReply (the (replyPrev reply'))
               (replyNext_update Map.empty))
         od;
         cleanReply rp
      od)"
  apply (case_tac "replyNext reply'"; simp add: getHeadScPtr_def isHead_def split: reply_next.splits)
   (* replyNext reply' = None *)
   apply (case_tac "replyPrev reply'"; simp)
    (* replyNext reply' = None & replyPrev reply' = None *)
    apply (rule sr_inv_imp)
      apply (rule cleanReply_sr_inv[where P=\<top> and P'=\<top>])
     apply simp
    apply simp
   (* replyNext reply' = None & replyPrev reply' = Some prv_rp *)
   apply (rename_tac prv_rp)
   apply (rule sr_inv_bind)
     apply (rule sr_inv_imp)
       apply (rule cleanReply_sr_inv[where P=\<top> and P'="valid_objs' and reply_at' rp"])
      apply simp
     apply simp
    apply (rule updateReply_sr_inv)
     apply (fastforce simp: reply_relation_def opt_map_red obj_at'_def
                     dest!: sym_refs_replyNext_replyPrev_sym[where rp'=rp, THEN iffD2])
    apply clarsimp
    apply (frule_tac rp=prv_rp in sc_replies_relation_sc_with_reply_None)
        apply simp
       apply (clarsimp simp: obj_at'_def opt_map_red)
      apply (erule (7) sc_with_reply_replyPrev_None)
       apply (clarsimp simp: obj_at'_def opt_map_red)+
    apply (fastforce simp: projectKO_opt_sc obj_at'_def opt_map_red)
   apply (wpsimp wp: updateReply_valid_objs' simp: valid_reply'_def obj_at'_def)
  (* replyNext reply' = Some nxt_rp *)
  apply (rename_tac nxt_rp)
  apply (case_tac "replyPrev reply'"; simp)
   (* replyNext reply' = Some nxt_rp & replyPrev reply' = None *)
   apply (rule sr_inv_bind)
     apply (rule sr_inv_imp)
       apply (rule cleanReply_sr_inv[where P=\<top> and P'="valid_objs' and reply_at' rp"])
      apply simp
     apply simp
    apply (rule updateReply_sr_inv)
     apply (clarsimp simp: reply_relation_def)
    apply (clarsimp simp: projectKO_opt_sc obj_at'_def opt_map_red  sc_replies_relation_def)
    apply (rename_tac nreply')
    apply (rule heap_path_heap_upd_not_in, simp)
    apply (rename_tac scp replies)
    apply (drule_tac x=scp and y=replies in spec2, simp)
    apply (prop_tac "rp \<notin> set replies")
     apply (drule_tac sc=scp in valid_replies_sc_with_reply_None, simp)
     apply (clarsimp simp: sc_replies_sc_at_def obj_at_def is_reply sc_replies_of_scs_def
                           scs_of_kh_def map_project_def
                    elim!: opt_mapE)
    apply (erule (1) heap_ls_prev_not_in)
    apply (fastforce elim!: sym_refs_replyNext_replyPrev_sym[THEN iffD1] simp: opt_map_red)
   apply (wpsimp wp: updateReply_valid_objs' simp: valid_reply'_def obj_at'_def)
  (* replyNext reply' = Some nxt_rp & replyPrev reply' = Some prv_rp *)
  apply (rename_tac prv_rp)
  apply (rule_tac Q="valid_objs and pspace_aligned and pspace_distinct and valid_replies
                     and (\<lambda>s. sym_refs (state_refs_of s))
                     and (\<lambda>s. sc_with_reply rp s = None)
                     and (\<lambda>s. sc_with_reply prv_rp s = None)
                     and (\<lambda>s. sc_with_reply nxt_rp s = None)
                     and reply_at rp"
             and Q'="valid_objs' and reply_at' rp
                     and pspace_aligned' and pspace_distinct'
                     and reply_at' prv_rp and reply_at' nxt_rp
                     and (\<lambda>s'. sc_with_reply' rp s' = None)
                     and (\<lambda>s'. sc_with_reply' prv_rp s' = None)
                     and (\<lambda>s'. sc_with_reply' nxt_rp s' = None)
                     and (\<lambda>s'. sym_refs (state_refs_of' s'))
                     and (\<lambda>s'. replyPrevs_of s' nxt_rp = Some rp)
                     and (\<lambda>s'. replyNexts_of s' prv_rp = Some rp)"
         in sr_inv_stronger_imp)
    apply (rule sr_inv_bind)
      apply (rule sr_inv_imp)
        apply (rule cleanReply_sr_inv[where P=\<top> and P'="valid_objs' and reply_at' rp"])
       apply simp
      apply simp
     apply (rule sr_inv_bind)
       apply (rule sr_inv_imp)
         apply (rule updateReply_sr_inv_next[simplified])
        apply simp
       apply simp
      apply (rule sr_inv_imp)
        apply (rule updateReply_sr_inv_prev[simplified])
       apply simp+
     apply wpsimp
    apply (wpsimp wp: updateReply_valid_objs' simp: valid_reply'_def)
  apply clarsimp
   apply (rule  conjI)
    apply (fastforce simp: obj_at'_def  opt_map_red
                    elim!: state_relationE sc_with_reply_replyPrev_None sc_with_reply_replyNext_None)
   apply (fastforce simp: obj_at'_def  opt_map_red
                   elim!: state_relationE sc_with_reply_replyNext_None)
  apply (prop_tac"sc_with_reply prv_rp s = None \<and> sc_with_reply nxt_rp s = None")
   apply (rule conjI)
    apply (fastforce simp: obj_at'_def  opt_map_red
                    elim!: state_relationE sc_with_reply_replyPrev_None sc_with_reply_replyNext_None)
   apply (fastforce simp: obj_at'_def  opt_map_red
                   elim!: state_relationE sc_with_reply_replyNext_None)
  apply (erule state_relationE)
  apply (clarsimp simp: sc_replies_relation_sc_with_reply_cross_eq)
  apply (rule conjI)
   apply (clarsimp simp: obj_at'_def)
  apply (frule (1) reply_ko_at_valid_objs_valid_reply')
  apply (clarsimp simp: valid_reply'_def valid_bound_obj'_def)
  apply (fastforce simp: obj_at'_def  opt_map_red
                  elim!: sym_refs_replyNext_replyPrev_sym[THEN iffD1]
                         sym_refs_replyNext_replyPrev_sym[THEN iffD2])
  done

lemma no_fail_sc_wtih_reply_None_helper:
  "\<not> isHead (replyNext reply') \<Longrightarrow>
   no_fail
     (\<lambda>s'. (s, s') \<in> state_relation \<and>
           (valid_objs' and
            (\<lambda>s'. sym_refs (list_refs_of_replies' s')) and
            ko_at' reply' rp and
            ((\<lambda>s'. sc_with_reply' rp s' = None) and
             pspace_aligned' and pspace_distinct' and pspace_bounded'))
            s')
     (do y <-
         do y <-
            when (\<exists>y. replyNext reply' = Some y)
             (updateReply (theReplyNextPtr (replyNext reply'))
               (replyPrev_update Map.empty));
            when (\<exists>y. replyPrev reply' = Some y)
             (updateReply (the (replyPrev reply'))
               (replyNext_update Map.empty))
         od;
         cleanReply rp
      od)"
  apply (case_tac "replyNext reply'"; simp split del: if_split)
   apply wpsimp
   apply (frule (1) reply_ko_at_valid_objs_valid_reply')
   apply (clarsimp simp: obj_at'_def  valid_reply'_def)
  apply (rename_tac nextr; case_tac nextr; simp add: isHead_def)
  apply (case_tac "replyPrev reply'"; simp)
   apply (wpsimp;
          frule (1) reply_ko_at_valid_objs_valid_reply';
          clarsimp simp: obj_at'_def  valid_reply'_def)+
  done

lemma replyRemoveTCB_corres:
  "corres dc
     (valid_objs and pspace_aligned and pspace_distinct and valid_replies
      and st_tcb_at ((=) (Structures_A.thread_state.BlockedOnReply rp)) t
      and (\<lambda>s. sym_refs (state_refs_of s)))
     (valid_objs' and (\<lambda>s'. sym_refs (list_refs_of_replies' s')) and sym_heap_sched_pointers)
     (reply_remove_tcb t rp) (replyRemoveTCB t)"
  (is "corres _ ?abs_guard ?conc_guard _ _")
  apply add_sym_refs
  apply (rule_tac Q'="st_tcb_at' ((=) (thread_state.BlockedOnReply (Some rp))) t" in corres_cross_add_guard)
   apply (fastforce dest!: st_tcb_at_coerce_concrete elim!: pred_tcb'_weakenE)
  apply (rule_tac Q="reply_at rp" in corres_cross_add_abs_guard)
   apply (fastforce dest: st_tcb_at_valid_st2)
  apply (clarsimp simp: reply_remove_tcb_def replyRemoveTCB_def isReply_def)
  apply (rule corres_stateAssert_ignore, simp)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF getThreadState_corres])
      apply (rule corres_assert_gen_asm_l)
      apply (rule corres_assert_gen_asm2)
      apply (rule corres_assert_opt_assume)
       apply (case_tac state; simp)
       apply (drule sym[of rp], simp)
       apply (rule_tac P'="?conc_guard and (\<lambda>s'. sym_refs (state_refs_of' s')) and reply_at' rp"
                   and P="?abs_guard" in corres_symb_exec_r)
                 (* get sc_with_reply *)
          apply (rule corres_symb_exec_l)
             apply (rename_tac reply' sc_opt)
             apply (rule_tac P="?abs_guard and (\<lambda>s. sc_with_reply rp s = sc_opt) and reply_at rp"
                         and P'="?conc_guard and (\<lambda>s. sym_refs (state_refs_of' s)) and ko_at' reply' rp"
                    in corres_inst)
             apply (rule_tac Q'="(\<lambda>s'. sc_with_reply' rp s' = sc_opt) and pspace_aligned'
                                      and pspace_distinct' and pspace_bounded'"
                    in corres_cross_add_guard)
              apply (frule pspace_relation_pspace_bounded'[OF state_relation_pspace_relation])
              apply (fastforce simp: sc_replies_relation_sc_with_reply_cross_eq
                              dest!: state_relationD pspace_distinct_cross dest: pspace_aligned_cross)
             apply (case_tac sc_opt; simp split del: if_split add: bind_assoc)

              (** sc_with_reply rp s = None **)
              apply (rule_tac F="replySC reply' = None" in corres_req)
               apply (fastforce dest!: sc_with_reply_None_reply_sc_reply_at dest: replySCs_of_cross
                                 simp: obj_at'_def  opt_map_red)
              apply (clarsimp simp: replySC_None_not_head)
  subgoal for reply'
    apply (simp only: bind_assoc[symmetric])
    apply (rule corres_symb_exec_r_sr)
       apply (rule corres_guard_imp)
         apply (rule replyUnlinkTcb_corres[simplified dc_def])
        apply (clarsimp dest!: valid_objs_valid_tcbs)
        apply (frule (1) st_tcb_reply_state_refs)
        apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb is_reply reply_tcb_reply_at_def)
       apply simp
      apply (erule sr_inv_sc_with_reply_None_helper)
     apply (wpsimp wp: updateReply_valid_objs' simp: valid_reply'_def obj_at'_def)
     apply (fastforce elim!: reply_ko_at_valid_objs_valid_reply')
    apply (wpsimp wp: no_fail_sc_wtih_reply_None_helper)
    apply fastforce
    done

            (** sc_with_reply \<noteq> None : rp is in a reply stack **)
             apply (rename_tac scp)
             apply (rule_tac F="replyNext reply' \<noteq> None" in corres_req)
              apply clarsimp
              apply (prop_tac "sc_at scp s")
               apply (fastforce dest!: sc_with_reply_SomeD1
                                 simp: sc_replies_sc_at_def obj_at_def is_sc_obj_def
                                 elim: valid_sched_context_size_objsI)
              apply (prop_tac "sc_at' scp s'")
               apply (fastforce dest!: state_relationD sc_at_cross)
              apply (drule sc_with_reply'_SomeD, clarsimp)
              apply (case_tac "hd xs = rp")
               apply (drule heap_path_head, clarsimp)
               apply (drule (3) sym_refs_scReplies)
               apply (clarsimp simp: obj_at'_def sym_heap_def elim!: opt_mapE)

              apply (frule (1) heap_path_takeWhile_lookup_next)
              apply (frule heap_path_head, clarsimp)
              apply (prop_tac "takeWhile ((\<noteq>) rp) xs = hd xs # tl (takeWhile ((\<noteq>) rp) xs)")
               apply (case_tac xs; simp)
              apply (simp del: heap_path.simps)
              apply (drule_tac p1="hd xs" and ps1="tl (takeWhile ((\<noteq>) rp) xs)"
                     in sym_refs_reply_heap_path_doubly_linked_Nexts_rev[where p'=rp, THEN iffD1])
               apply clarsimp
              apply (case_tac "rev (tl (takeWhile ((\<noteq>) rp) xs))";
                     clarsimp simp: obj_at'_def elim!: opt_mapE)
             apply (clarsimp simp: liftM_def bind_assoc split del: if_split)
             apply (rename_tac next_reply)
             apply (rule_tac Q="\<lambda>x. ?abs_guard
                                and (\<lambda>s. \<exists>n. kheap s scp = Some (Structures_A.SchedContext x n))
                                and (\<lambda>s. sc_with_reply rp s = Some scp)
                                and  K (rp \<in> set (sc_replies x))"
                    in corres_symb_exec_l)
                apply (rename_tac sc)
                apply (rule_tac Q'="(\<lambda>s'. scReplies_of s' scp = hd_opt (sc_replies sc)) and sc_at' scp"
                       in corres_cross_add_guard)
                 apply (clarsimp; rule conjI)
                  apply (frule state_relation_sc_replies_relation)
                  apply (frule sc_replies_relation_scReplies_of[symmetric])
                    apply (fastforce dest!: sc_at_cross valid_objs_valid_sched_context_size
                                      simp: obj_at_def is_sc_obj_def obj_at'_def)
                   apply (fastforce dest!: sc_at_cross valid_objs_valid_sched_context_size
                                     simp: obj_at_def is_sc_obj_def state_relation_def obj_at'_def
                                            opt_map_def)
                  apply (clarsimp simp: sc_replies_of_scs_def map_project_def opt_map_def
                                        scs_of_kh_def)
                 apply (fastforce dest!: state_relation_pspace_relation sc_at_cross
                                         valid_objs_valid_sched_context_size
                                   simp: obj_at_def is_sc_obj)
                apply (rule corres_gen_asm')
                apply (rule corres_symb_exec_l)
                   apply (rename_tac replysc)
                   apply (rule_tac P="?abs_guard and (\<lambda>s. sc_with_reply rp s = Some scp)
                                      and obj_at (\<lambda>ko. \<exists>n. ko = Structures_A.SchedContext sc n) scp
                                      and reply_sc_reply_at ((=) replysc) rp"
                          in corres_inst)
                   apply (rename_tac replysc)
                   apply (rule_tac F="replySC reply' = replysc" in corres_req)
                    apply (fastforce dest!: replySCs_of_cross simp: obj_at'_def  opt_map_red)
                   apply (case_tac "hd (sc_replies sc) = rp"; simp split del: if_split)

                   (* hd (sc_replies sc) = rp & replysc = Some scp: rp is at the head of the queue *)
                   (* i.e. replyNext reply'  *)
                    apply (rule corres_guard_imp)
                      apply (rule corres_assert_gen_asm_l2)
                      apply (simp add: updateSchedContext_def getHeadScPtr_def isHead_def
                                       neq_conv[symmetric]
                                split: reply_next.splits)
                      apply (rule corres_split[OF setSchedContext_scReply_update_None_corres[simplified dc_def]])
                        apply (rule_tac Q =\<top> and
                                        P'="valid_objs' and sym_heap_sched_pointers and ko_at' reply' rp" and
                                        Q'="(\<lambda>s'. \<forall>prp. replyPrev reply' = Some prp
                                                        \<longrightarrow> replyNexts_of s' prp = Some rp)"
                            in corres_inst_add)
                        apply (rule corres_symb_exec_r_sr)
                           apply (rule corres_guard_imp)
                             apply (rule corres_split[OF cleanReply_sc_with_reply_None_corres])
                               apply (rule replyUnlinkTcb_corres[simplified dc_def])
                              apply wpsimp
                             apply wpsimp
                            apply simp
                           apply simp
                          apply (clarsimp cong: conj_cong)
                          apply (case_tac "replyPrev reply'"; simp)
                          apply (rename_tac prev_rp)
                          apply (rule sr_inv_imp)
                            apply (rule_tac P =\<top> and
                                            P'=" (\<lambda>s'. \<forall>prp. replyPrev reply' = Some prp
                                                             \<longrightarrow> replyNexts_of s' prev_rp = Some rp)"
                                         in updateReply_sr_inv)
                             apply (clarsimp simp: reply_relation_def  obj_at'_def obj_at_def
                                            elim!: opt_mapE)
                            apply clarsimp
                            apply (drule_tac rp=prev_rp in sc_replies_relation_replyNext_update, simp)
                            apply simp
                           apply simp
                          apply clarsimp
                         apply wpsimp
                        apply wpsimp
                        apply (frule (1) reply_ko_at_valid_objs_valid_reply')
                        apply (clarsimp simp: valid_reply'_def valid_bound_reply'_def)
                       apply (wpsimp wp: sc_replies_update_takeWhile_sc_with_reply
                                         sc_replies_update_takeWhile_valid_replies)
                      apply (wpsimp wp: scReply_update_empty_sc_with_reply')
                     apply clarsimp
                     apply (frule_tac reply_ptr=rp and sc_ptr= scp and list="tl (sc_replies sc)"
                            in sym_refs_reply_sc_reply_at)
                      apply (clarsimp simp: sc_replies_sc_at_def obj_at_def is_reply)
                      apply (metis list.sel(1) list.sel(3) list.set_cases)
                     apply (clarsimp simp: getHeadScPtr_def reply_sc_reply_at_def obj_at_def is_reply
                                    split: reply_next.splits)
                     apply (frule (1) st_tcb_reply_state_refs)
                     apply (clarsimp dest!: valid_objs_valid_tcbs
                                      simp: obj_at_def is_reply reply_tcb_reply_at_def)
                     apply (clarsimp simp: opt_map_red opt_map_def split: option.splits)
                     apply (rule context_conjI; clarsimp simp: vs_heap_simps obj_at_def)
                     apply (intro conjI)
                      apply (metis list.sel(1) list.set_cases)
                     apply (clarsimp simp: pred_tcb_at_def obj_at_def)
                    apply clarsimp
                    apply (rule conjI)
                     apply clarsimp
                     apply (intro conjI impI)
                       apply (clarsimp dest!: sc_ko_at_valid_objs_valid_sc'
                                        simp: valid_sched_context'_def refillSize_def
                                       split: if_splits)
                      apply (clarsimp dest!: sc_ko_at_valid_objs_valid_sc'
                                       simp: valid_sched_context_size'_def)
                     apply (clarsimp dest!: sc_ko_at_valid_objs_valid_sc'
                                      simp: valid_sched_context'_def valid_sched_context_size'_def)
                     apply (erule sym_refs_replyNext_replyPrev_sym[THEN iffD2])
                     apply (clarsimp simp: opt_map_red obj_at'_def)
                    apply (frule (3) sym_refs_scReplies)
                    apply (clarsimp simp: hd_opt_def  opt_map_red sym_heap_def
                                   split: list.split_asm)
                    apply (clarsimp simp: opt_map_red obj_at'_def  split: reply_next.splits)

                  (* rp is in the middle of the reply stack *)
                  (* hd (sc_replies sc) \<noteq> rp & rp \<in> set (sc_replies sc) *)
                   apply (rule corres_guard_imp)
                     apply (rule_tac Q="valid_objs' and ko_at' reply' rp
                                        and (\<lambda>s'. sym_refs (list_refs_of_replies' s')) and sc_at' scp
                                        and (\<lambda>s'. sym_refs (state_refs_of' s'))
                                        and (\<lambda>s'. sc_with_reply' rp s' = Some scp)
                                        and (\<lambda>s'. scReplies_of s' scp = hd_opt (sc_replies sc))
                                        and (\<lambda>s'. \<forall>prp. replyPrev reply' = Some prp
                                                        \<longrightarrow> replyNexts_of s' prp = Some rp)"
                            in corres_assert_gen_asm_l)
                     apply (simp split del: if_split)
                     apply (clarsimp simp: getHeadScPtr_def isHead_def neq_conv[symmetric]
                                    split: reply_next.splits)
                     apply (rename_tac nxt_rp)
                     apply (rule stronger_corres_guard_imp)
                       apply (rule corres_split
                                     [OF updateReply_replyPrev_takeWhile_middle_corres])
                           apply simp
                          apply simp
                         apply (rule_tac P ="?abs_guard and reply_sc_reply_at ((=) None) rp" and
                                         Q ="\<lambda>s. sc_with_reply rp s = None" and
                                         P'="valid_objs' and ko_at' reply' rp and sc_at' scp" and
                                         Q'="(\<lambda>s'. \<forall>prp. replyPrev reply' = Some prp
                                                         \<longrightarrow> replyNexts_of s' prp = Some rp)"
                               in corres_inst_add)
                         apply (rule corres_symb_exec_r_sr)
                            apply (rule corres_guard_imp)
                              apply (rule corres_split[OF cleanReply_sc_with_reply_None_corres])
                                apply (rule replyUnlinkTcb_corres[simplified dc_def])
                               apply wpsimp
                              apply wpsimp
                             apply clarsimp
                             apply (frule (1) st_tcb_reply_state_refs, frule valid_objs_valid_tcbs)
                             apply (fastforce simp: obj_at_def is_reply reply_tcb_reply_at_def pred_tcb_at_def)
                            apply simp
                           apply (clarsimp cong: conj_cong)
                           apply (case_tac "replyPrev reply'"; simp)
                           apply (rename_tac prev_rp)
                           apply (rule sr_inv_imp)
                             apply (rule_tac P =\<top> and
                                             P'=" (\<lambda>s'. \<forall>prp. replyPrev reply' = Some prp
                                                              \<longrightarrow> replyNexts_of s' prev_rp = Some rp)"
                                    in updateReply_sr_inv)
                              apply (clarsimp simp: reply_relation_def  obj_at'_def obj_at_def
                                             elim!: opt_mapE)
                             apply clarsimp
                             apply (drule_tac rp=prev_rp in sc_replies_relation_replyNext_update, simp)
                             apply simp
                            apply simp
                           apply clarsimp
                          apply wpsimp
                         apply wpsimp
                         apply (clarsimp dest!: reply_ko_at_valid_objs_valid_reply'
                                          simp: valid_reply'_def)
                        apply (wpsimp wp: sc_replies_update_takeWhile_sc_with_reply
                                          sc_replies_update_takeWhile_middle_sym_refs
                                          sc_replies_update_takeWhile_valid_replies)
                       apply (wpsimp wp: updateReply_valid_objs' updateReply_ko_at'_other)
                      apply (clarsimp cong: conj_cong)
                      apply simp
                     apply (clarsimp simp: valid_reply'_def)
                     apply (rule context_conjI)
                      apply (clarsimp simp: obj_at'_def  opt_map_red)
                     apply (clarsimp simp: obj_at_def del: opt_mapE)
                     apply (frule (1) valid_sched_context_objsI)
                     apply (clarsimp simp: valid_sched_context_def del: opt_mapE)
                     apply (frule (4) next_reply_in_sc_replies[OF state_relation_sc_replies_relation])
                        apply (fastforce dest!: state_relationD pspace_aligned_cross pspace_distinct_cross)
                       apply (fastforce dest!: state_relationD pspace_distinct_cross)
                      apply (fastforce dest!: state_relationD pspace_relation_pspace_bounded')
                     apply (clarsimp simp: obj_at'_def)
                     apply (clarsimp simp: vs_heap_simps)
                    apply clarsimp
                    apply (rule conjI)
                     apply (clarsimp simp: list_all_iff dest!: set_takeWhileD)
                    apply (drule (2) sc_replies_middle_reply_sc_None)
                       apply (clarsimp simp: vs_heap_simps obj_at_def elim!: opt_mapE)
                      apply (fastforce simp: obj_at_def is_sc_obj_def elim!: valid_sched_context_size_objsI)
                     apply (erule reply_sc_reply_at)
                    apply (clarsimp simp: reply_sc_reply_at_def obj_at_def)
                   apply (fastforce elim!: sym_refs_replyNext_replyPrev_sym[THEN iffD2]
                                     simp: opt_map_red obj_at'_def)
                  apply (wpsimp simp: get_sk_obj_ref_def wp: get_reply_exs_valid)
                   apply (fastforce dest!: Reply_or_Receive_reply_at[rotated] simp: obj_at_def is_reply)
                  apply simp
                 apply (wpsimp wp: get_sk_obj_ref_wp)
                 apply (clarsimp simp: obj_at_def reply_sc_reply_at_def)
                apply (wpsimp simp: get_sk_obj_ref_def get_simple_ko_def obj_at_def
                                wp: get_object_wp)
                apply (prop_tac "reply_at rp s")
                 apply (fastforce dest!: st_tcb_at_valid_st2 simp: valid_tcb_state_def)
                apply (fastforce simp: obj_at_def is_reply partial_inv_def a_type_def)
               apply (wpsimp wp: get_sched_context_exs_valid)
                apply (drule sc_with_reply_SomeD)
                apply (wpsimp simp: is_sc_obj_def
                       | clarsimp split: Structures_A.kernel_object.splits)+
              apply (fastforce dest!: sc_with_reply_SomeD1 simp: sc_replies_sc_at_def obj_at_def)
             apply (wpsimp wp: get_sched_context_no_fail)
             apply (fastforce dest!: sc_with_reply_SomeD elim!: valid_sched_context_size_objsI
                               simp: obj_at_def is_sc_obj_def)
            apply wpsimp
           apply wpsimp
           apply (fastforce dest!: st_tcb_at_valid_st2 simp: valid_tcb_state_def)
          apply wpsimp
         apply (wpsimp wp: get_reply_inv' wp_del: getReply_wp)
          apply (wpsimp simp: getReply_def)
         apply clarsimp
        apply wpsimp
       apply wpsimp
      apply clarsimp
     apply (wpsimp wp: gts_wp)
    apply wpsimp
   apply (clarsimp simp: st_tcb_at_tcb_at pred_tcb_at_def obj_at_def is_tcb)
  apply clarsimp
  apply (rule context_conjI; clarsimp)
   apply (fastforce intro: reply_at_cross)
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
  apply (rename_tac tcb reply)
  apply (case_tac "tcbState tcb"; simp)
  done

lemma setSchedContext_pop_head_corres:
  "\<lbrakk> replyNext reply' = Some (Head ptr)  \<rbrakk> \<Longrightarrow>
   corres dc
          ((\<lambda>s. (sc_replies_of s |> hd_opt) ptr = Some rp)
                and valid_objs and pspace_aligned and pspace_distinct)
          (ko_at' reply' rp)
          (update_sched_context ptr (sc_replies_update tl))
          (do sc' \<leftarrow> getSchedContext ptr;
              setSchedContext ptr (scReply_update (\<lambda>_. replyPrev reply') sc')
           od)"
  supply opt_mapE[elim!]
  apply (rule_tac Q'="sc_at' ptr" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD simp: obj_at_def is_sc_obj_def vs_heap_simps
                    elim!: sc_at_cross valid_objs_valid_sched_context_size)
  apply (rule_tac Q'="pspace_aligned' and pspace_distinct'" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: pspace_aligned_cross pspace_distinct_cross)
  apply (rule_tac Q'="\<lambda>s'. scReplies_of s' ptr = Some rp" in corres_cross_add_guard)
   apply (subst sc_replies_relation_scReplies_of[symmetric, OF state_relation_sc_replies_relation])
      apply simp
     apply clarsimp
     apply (fastforce simp: opt_map_red dest!: sc_at'_cross[OF state_relation_pspace_relation])
    apply (clarsimp simp: opt_map_red gen_obj_at_simps)+
  apply (rule corres_symb_exec_r)
     apply (rule_tac P'="ko_at' sc' ptr and ko_at' reply' rp
                         and pspace_aligned' and pspace_distinct' and  K (scReply sc' = Some rp)" in corres_inst)
     apply (rule corres_gen_asm2')
     apply (rule_tac Q="sc_obj_at (objBits sc' - minSchedContextBits) ptr" in corres_cross_add_abs_guard)
      apply (fastforce dest!: state_relationD ko_at_sc_cross)
     apply (rule corres_guard_imp)
       apply (rule_tac P="(\<lambda>s. (sc_replies_of s |> hd_opt) ptr = Some rp)
                          and sc_obj_at (objBits sc' - minSchedContextBits) ptr"
                  and n1="objBits sc' - minSchedContextBits"
                            in monadic_rewrite_corres_l[OF update_sched_context_rewrite])
       apply (rule corres_symb_exec_l)
          apply (rule corres_guard_imp)
            apply (rule_tac P="(\<lambda>s. kheap s ptr =
                                       Some (kernel_object.SchedContext sc (objBits sc' - minSchedContextBits)))
                               and K (rp = hd (sc_replies sc))"
                        and P'="ko_at' sc' ptr and ko_at' reply' rp
                               and pspace_distinct' and pspace_aligned'"  in corres_inst)
            apply (rule corres_gen_asm')
            apply (rule stronger_corres_guard_imp)
              apply (rule_tac sc=sc and sc'=sc' in setSchedContext_update_corres; simp?)
               apply (clarsimp simp: sc_relation_def refillSize_def)+
            apply (clarsimp simp: obj_at'_def)
            apply (prop_tac "heap_ls (replyPrevs_of s') (Some rp) (sc_replies sc)")
             apply (drule state_relation_sc_replies_relation)
             apply (drule (2) sc_replies_relation_prevs_list, simp)
            apply (case_tac "sc_replies sc"; clarsimp simp: opt_map_red)
           apply simp
          apply simp
         apply (wpsimp wp: get_sched_context_exs_valid simp: is_sc_obj_def obj_at_def)
          apply (rename_tac ko xs; case_tac ko; clarsimp)
         apply simp
        apply (wpsimp simp: obj_at_def is_sc_obj_def vs_heap_simps opt_pred_def)
       apply (wpsimp wp: get_sched_context_no_fail simp: obj_at_def is_sc_obj)
      apply (clarsimp simp: obj_at_def is_sc_obj_def)
     apply simp
    apply (wpsimp simp: obj_at'_def)+
  done

lemma sched_context_donate_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action and bound_sc_tcb_at ((=) None) tcb_ptr\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp update_sched_context_wp test_reschedule_wp
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

crunch rescheduleRequired, setQueue, tcbSchedEnqueue, tcbReleaseRemove, updateReply
  for scReplies_of[wp]: "\<lambda>s. P' (scReplies_of s)"
  (simp: crunch_simps wp: crunch_wps)

crunch updateReply, setSchedContext, updateSchedContext
  for tcbSCs_of[wp]: "\<lambda>s. P' (tcbSCs_of s)"
  and list_refs_of_replies'[wp]: "\<lambda>s. P (list_refs_of_replies' s)"
  and tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
  and tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_sched_pointers[wp]: valid_sched_pointers
  (simp: crunch_simps wp: crunch_wps)

lemma scReplies_of_scTCB_update[simp]:
  "\<lbrakk> ko_at' sc scp s\<rbrakk>
   \<Longrightarrow> P (\<lambda>a. if a = scp then scReply (scTCB_update (\<lambda>_. Some tp) sc) else scReplies_of s a)
       \<longleftrightarrow> P (scReplies_of s)"
  by (fastforce simp: obj_at'_def  opt_map_red elim!: rsubst[where P=P])

crunch schedContextDonate
  for replies_of': "\<lambda>s. P (replies_of' s)" (* this interfers with list_refs_of_replies' *)
  and scReplies_of[wp]: "\<lambda>s. P' (scReplies_of s)"
  (simp: crunch_simps wp: crunch_wps)

lemma updateReply_replyNext_update_None:
  "\<lbrace> \<top> \<rbrace>
   updateReply rp (replyNext_update Map.empty)
   \<lbrace>\<lambda>rv s. (replies_of' s |> replyNext) rp = None \<rbrace>"
  by (wpsimp wp: updateReply_wp_all)

lemma update_sched_context_sc_replies_update_tl:
  "\<lbrace>\<lambda>s. \<exists>x. (kheap s |> sc_of ||> sc_replies) scp = Some (x#list)\<rbrace>
   update_sched_context scp (sc_replies_update tl)
   \<lbrace>\<lambda>_. sc_replies_sc_at ((=) list) scp\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: obj_at_def sc_replies_sc_at_def opt_map_red)
  done

lemma setSchedContext_local_sym_refs:
  "\<lbrace>\<lambda>s. ko_at' r' rp s \<and> ko_at' sc scp s \<and> replyPrev r' \<noteq> Some rp
        \<and> (\<forall>p'. p' \<noteq> scp \<longrightarrow> scReplies_of s p' \<noteq> Some rp)\<rbrace>
   setSchedContext scp (scReply_update (\<lambda>_. replyPrev r') sc)
   \<lbrace>\<lambda>rv s. \<forall>p'. scReplies_of s p' \<noteq> Some rp\<rbrace>"
  apply (wpsimp wp: setObject_sc_wp simp: setSchedContext_def)
  apply (clarsimp simp: obj_at'_def  opt_map_red elim!: opt_mapE split: if_split_asm)
  apply (drule_tac x=p' in spec)
  apply (clarsimp simp: opt_map_red)
  done

crunch sched_context_donate, set_reply_obj_ref, update_sched_context
  for ep_queues_blocked[wp]: ep_queues_blocked
  and ntfn_queus_blocked[wp]: ntfn_queues_blocked
  (wp: ep_queues_blocked_lift ntfn_queues_blocked_lift)

lemma replyPop_corres:
  "\<lbrakk>st = Structures_A.thread_state.BlockedOnReply rp;
    st' = Structures_H.thread_state.BlockedOnReply (Some rp)\<rbrakk> \<Longrightarrow>
   corres dc
     (valid_objs and pspace_aligned and pspace_distinct
      and st_tcb_at ((=) st) t and weak_valid_sched_action
      and sc_at scp and reply_at rp and active_scs_valid and valid_ready_qs and valid_release_q
      and ready_or_release
      and valid_replies and (\<lambda>s. sym_refs (state_refs_of s))
      and bound_sc_tcb_at ((=) tcbsc) t
      and reply_tcb_reply_at ((=) (Some t)) rp
      and (\<lambda>s. sc_with_reply rp s = Some scp)
      and (\<lambda>s. (sc_replies_of s |> hd_opt) scp = Some rp))
     (valid_objs'
      and reply_at' rp and sc_at' scp and sym_heap_sched_pointers and valid_sched_pointers
      and (\<lambda>s'. sym_refs (list_refs_of_replies' s')))
     (do x <- reply_unlink_sc scp rp;
         y <- when (tcbsc = None) (sched_context_donate scp t);
         reply_unlink_tcb t rp
      od)
     (replyPop rp t)"
  (is "\<lbrakk> _ ; _ \<rbrakk> \<Longrightarrow> corres _ (?abs_guard and valid_replies and (\<lambda>s. sym_refs (state_refs_of s))
                              and bound_sc_tcb_at ((=) tcbsc) t and reply_tcb_reply_at ((=) (Some t)) rp
                              and (\<lambda>s. sc_with_reply rp s = _) and ?sc_replies)
                             (?conc_guard and (\<lambda>s'. sym_refs (list_refs_of_replies' s'))) _ _")
  supply if_split[split del] opt_mapE[elim!]
  apply add_sym_refs
  apply (rule_tac Q'="st_tcb_at' ((=) st') t" in corres_cross_add_guard)
   apply (fastforce dest!: st_tcb_at_coerce_concrete elim!: pred_tcb'_weakenE)
  apply (rule_tac Q'="\<lambda>s. tcbSCs_of s t = tcbsc" in corres_cross_add_guard)
   apply (fastforce dest!: bound_sc_tcb_at_cross elim!: obj_at'_weakenE)
  apply (rule_tac Q'="pspace_distinct'" in corres_cross_add_guard)
   apply (fastforce dest!: pspace_distinct_cross)
  apply (rule_tac Q'="pspace_aligned'" in corres_cross_add_guard)
   apply (fastforce dest!: pspace_aligned_cross)
  apply (rule_tac Q'="pspace_bounded'" in corres_cross_add_guard)
   apply (fastforce dest!: pspace_relation_pspace_bounded'[OF state_relation_pspace_relation])
  apply (rule_tac Q'="\<lambda>s. scReplies_of s scp = Some rp" in corres_cross_add_guard)
   apply (fastforce simp: opt_map_red obj_at'_def
                   dest!: sc_replies_relation_scReplies_of state_relation_sc_replies_relation)
  apply (simp add: reply_unlink_sc_def replyPop_def bind_assoc liftM_def)
  apply (rule_tac Q="\<lambda>sc. ?abs_guard and ep_queues_blocked and ntfn_queues_blocked
                           and reply_tcb_reply_at ((=) (Some t)) rp
                           and (\<lambda>s. \<exists>n. ko_at (Structures_A.SchedContext sc n) scp s)
                           and bound_sc_tcb_at ((=) tcbsc) t
                           and K (\<exists>ls. sc_replies sc = rp#ls \<and> distinct (rp#ls))"
         in corres_symb_exec_l)
     apply (rename_tac sc)
     apply (rule corres_gen_asm') (* sc_replies sc = rp # ls, distinct (rp#ls) *)
     apply (rule corres_stateAssert_add_assertion[rotated])
      apply (clarsimp simp: sym_refs_asrt_def)
     apply (rule corres_guard_imp)
       apply (rule corres_split[OF get_reply_corres])
         apply (rename_tac r r')
         apply (rule_tac P="?abs_guard and ep_queues_blocked and ntfn_queues_blocked
                            and reply_tcb_reply_at ((=) (Some t)) rp
                            and ko_at (Structures_A.Reply r) rp and bound_sc_tcb_at ((=) tcbsc) t
                            and (\<lambda>s. \<exists>n. ko_at (Structures_A.SchedContext sc n) scp s)"
                     and P'="?conc_guard and (\<lambda>s'. sym_refs (list_refs_of_replies' s'))
                            and pspace_aligned' and pspace_distinct' and pspace_bounded'
                            and (\<lambda>s. sym_refs (state_refs_of' s))
                            and st_tcb_at' ((=) st') t and (\<lambda>s. tcbSCs_of s t = tcbsc) and ko_at' r' rp
                            and (\<lambda>s. scReplies_of s scp = Some rp)
                            and K (replyTCB r' = Some t) and K (replyNext r' = Some (Head scp))"
                in corres_inst)
         apply (rule corres_gen_asm2') (* replyNext r' = Some (Head scp) *)
         apply (rule corres_gen_asm2') (* replyTCB r' = Some t *)
         apply (erule exE, rename_tac list)
         apply (rule_tac F="case list of [] \<Rightarrow> replyPrev r' = None | a#_ \<Rightarrow> replyPrev r' = Some a"
                in corres_req)
          apply (clarsimp simp: gen_obj_at_simps)
          apply (drule (1) sc_replies_relation_prevs_list'[OF state_relation_sc_replies_relation])
          apply (clarsimp simp: opt_map_red del: opt_mapE)
          apply (case_tac list; simp)
         apply (simp add: bind_assoc)
         apply (rule corres_symb_exec_l) (* assert reply_sc r = Some scp *)
            apply (rule corres_symb_exec_r) (* get threadState for t *)
               apply (rename_tac state)
               apply (rule_tac P="?abs_guard and ep_queues_blocked and ntfn_queues_blocked
                                  and reply_tcb_reply_at ((=) (Some t)) rp
                                  and ko_at (Structures_A.Reply r) rp
                                  and bound_sc_tcb_at ((=) tcbsc) t
                                  and (\<lambda>s. \<exists>n. ko_at (Structures_A.SchedContext sc n) scp s)"
                           and P'="?conc_guard and (\<lambda>s'. sym_refs (list_refs_of_replies' s'))
                                  and pspace_aligned' and pspace_distinct' and pspace_bounded'
                                  and (\<lambda>s. sym_refs (state_refs_of' s)) and st_tcb_at' ((=) st') t
                                  and (\<lambda>s. tcbSCs_of s t = tcbsc)
                                  and (\<lambda>s. scReplies_of s scp = Some rp)
                                  and ko_at' r' rp and sc_at' scp and K (state = st')"
                      in corres_inst)
               apply (rule corres_gen_asm2')
               apply (simp add: bind_assoc isReply_def isHead_def updateSchedContext_def)
               apply (subst bind_assoc[symmetric, where m="getSchedContext _"])
               apply (rule corres_guard_imp)
                 apply (rule corres_split[OF setSchedContext_pop_head_corres[where rp=rp]])
                    apply simp  (* scReplies at scp = replyPrev r', tl (sc_replies sc) *)
                   apply (rule corres_split[where r'=dc])
                      apply (case_tac list; simp)
                      apply (rename_tac a ls)
                      apply (rule_tac P="?abs_guard
                                         and ep_queues_blocked and ntfn_queues_blocked
                                         and reply_tcb_reply_at ((=) (Some t)) rp
                                         and sc_replies_sc_at ((=) (a#ls)) scp
                                         and ko_at (Structures_A.Reply r) rp
                                         and bound_sc_tcb_at ((=) tcbsc) t"
                                  and P'="?conc_guard and (\<lambda>s'. sym_refs (list_refs_of_replies' s'))
                                          and pspace_aligned' and pspace_distinct' and pspace_bounded'
                                          and st_tcb_at' ((=) st') t and (\<lambda>s. tcbSCs_of s t = tcbsc)
                                          and ko_at' r' rp and (\<lambda>s. \<forall>p'. scReplies_of s p' \<noteq> Some rp)
                                          and (\<lambda>s. \<forall>p'. replyPrevs_of s p' \<noteq> Some rp)"
                             in corres_inst)
                      apply (rule stronger_corres_guard_imp)
                        apply (rule updateReply_replyPrev_same_corres)
                        apply (clarsimp simp: reply_relation_def)
                       apply clarsimp
                       apply (clarsimp simp: sc_replies_sc_at_def obj_at_def is_sc_obj)
                       apply (erule (1) valid_objsE[where x=scp])
                       apply (clarsimp simp: valid_obj_def valid_sched_context_def dest!: sym[of _ "sc_replies _"])
                       apply (clarsimp simp: obj_at_def)
                      apply clarsimp
                      apply (erule valid_objsE'[where x=rp])
                       apply (fastforce simp: obj_at'_def)
                      apply (clarsimp simp: valid_obj'_def valid_reply'_def)
                     apply (rule corres_guard_imp)
                       apply (rule corres_split[OF updateReply_replyNext_not_head_corres])
                          apply (clarsimp simp: isHead_def)
                         apply (rule_tac P="?abs_guard and ep_queues_blocked and ntfn_queues_blocked
                                             and reply_tcb_reply_at ((=) (Some t)) rp
                                             and bound_sc_tcb_at ((=) tcbsc) t
                                             and sc_replies_sc_at (\<lambda>ls. rp \<notin> set ls) scp
                                             and reply_sc_reply_at ((=) None) rp "
                                     and P'="?conc_guard and st_tcb_at' ((=) st') t
                                             and pspace_aligned' and pspace_distinct'
                                             and pspace_bounded'
                                             and (\<lambda>s. (replies_of' s |> replyNext) rp = None)
                                             and (\<lambda>s. \<forall>p'. replyPrevs_of s p' \<noteq> Some rp)
                                             and (\<lambda>s. \<forall>p'. scReplies_of s p' \<noteq> Some rp)
                                             and (\<lambda>s. tcbSCs_of s t = tcbsc)"
                                in corres_inst)
                         apply (rule_tac Q'="\<lambda>rv. ?conc_guard and st_tcb_at' ((=) st') t
                                                  and pspace_aligned' and pspace_distinct'
                                                  and pspace_bounded'
                                                  and (\<lambda>s. (replies_of' s |> replyNext) rp = None)
                                                  and (\<lambda>s. \<forall>p'. replyPrevs_of s p' \<noteq> Some rp)
                                                  and (\<lambda>s. \<forall>p'. scReplies_of s p' \<noteq> Some rp)
                                                  and (\<lambda>s. tcbSCs_of s t = rv)"
                                in corres_symb_exec_r)
                            apply (rename_tac tcbsc')
                            apply (rule stronger_corres_guard_imp)
                              apply (rule_tac Q'="K (tcbsc' = tcbsc)" in corres_inst_add)
                              apply (rule corres_gen_asm2')
                              apply (rule corres_split[OF corres_when2])
                                  apply simp
                                 apply (rule schedContextDonate_corres) (* donate *)
                                apply (rule_tac P="?abs_guard
                                                   and ep_queues_blocked and ntfn_queues_blocked
                                                   and reply_tcb_reply_at ((=) (Some t)) rp"
                                            and P'="valid_objs'
                                                    and sym_heap_sched_pointers
                                                    and valid_sched_pointers
                                                    and st_tcb_at' ((=) st') t and reply_at' rp
                                                    and (\<lambda>s. (replies_of' s |> replyNext) rp = None)
                                                    and (\<lambda>s. \<forall>p'. replyPrevs_of s p' \<noteq> Some rp)
                                                    and (\<lambda>s. \<forall>p'. scReplies_of s p' \<noteq> Some rp)
                                                    and pspace_aligned' and pspace_distinct'
                                                    and pspace_bounded'"
                                             in corres_inst)
                                apply (rule corres_symb_exec_r_sr_strong) (* replyPrev at rp = None *)
                                   apply (rule corres_guard_imp)
                                     apply (rule replyUnlinkTcb_corres)
                                    apply (clarsimp simp: valid_objs_valid_tcbs elim!: pred_tcb_weakenE)
                                   apply simp
                                  apply (simp add: cleanReply_def)
                                  apply (rule updateReply_sr_inv)
                                   apply (clarsimp simp: reply_relation_def)
                                  apply (intro conjI impI allI)
                                  apply (erule sc_replies_relation_replyNext_None; clarsimp)
                                  apply (clarsimp simp: obj_at'_def opt_map_red)
                                 apply wpsimp
                                apply wpsimp
                               apply simp
                               apply wpsimp
                              apply (rule hoare_when_cases, simp)
                              apply (wpsimp wp: schedContextDonate_valid_objs'
                                                schedContextDonate_replies_of' schedContextDonate_reply_projs)
                             apply (clarsimp split: if_split)
                             apply (frule_tac t=t in valid_release_q_not_in_release_q_not_runnable)
                              apply (clarsimp simp: pred_tcb_at_def obj_at_def)
                              apply (case_tac "tcb_state tcb"; clarsimp)
                             apply (frule (3) bound_sc_tcb_at_cross)
                             apply (fastforce simp: vs_all_heap_simps obj_at_kh_kheap_simps
                                                    weak_valid_sched_action_no_sc_sched_act_not)
                            apply (clarsimp simp: pred_tcb_at'_def opt_map_red gen_obj_at_simps pred_tcb_at_def)
                            apply (drule (1) pspace_relation_absD[OF _ state_relation_pspace_relation, where x=t])
                            apply (rename_tac tcb' sc')
                            apply (clarsimp simp: tcb_relation_cut_def tcb_relation_def)
                           apply (wpsimp wp: threadGet_wp)
                           apply (clarsimp simp: obj_at'_def  opt_map_red)
                          apply wpsimp
                         apply wpsimp
                        apply wpsimp
                       apply (wpsimp wp: updateReply_valid_objs' updateReply_replyNext_update_None)
                      apply wpsimp
                      apply simp
                     apply simp
                    apply wpsimp
                   apply (elim conjE)
                   apply (wpsimp wp: updateReply_valid_objs' simp: valid_reply'_def)
                  apply (clarsimp cong: conj_cong imp_cong simp: pred_conj_def)
                  apply (wpsimp wp: update_sched_context_sc_replies_update_tl)
                  apply (rule_tac Q'="\<lambda>_. sc_replies_sc_at ((=) list) scp" in hoare_strengthen_post[rotated])
                   apply (clarsimp simp: sc_replies_sc_at_def obj_at_def)
                  apply (wpsimp wp: update_sched_context_sc_replies_update_tl)
                 apply (fold updateSchedContext_def)
                 apply (rule_tac Q'="\<lambda>_. valid_objs' and sym_heap_sched_pointers
                                        and valid_sched_pointers
                                        and ko_at' r' rp and sc_at' scp
                                        and (\<lambda>s. sym_refs (list_refs_of_replies' s))
                                        and st_tcb_at' ((=) (Structures_H.thread_state.BlockedOnReply (Some rp))) t
                                        and (\<lambda>s. \<forall>p'. scReplies_of s p' \<noteq> Some rp)
                                        and (\<lambda>s. \<forall>p'. replyPrevs_of s p' \<noteq> Some rp)
                                        and (\<lambda>s. tcbSCs_of s t = tcbsc)
                                        and pspace_aligned' and pspace_distinct' and pspace_bounded'"
                        in hoare_strengthen_post[rotated])
                  apply (clarsimp split: if_split simp: valid_reply'_def obj_at'_def)
                 apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp simp: valid_reply'_def)
                 apply (rule hoare_vcg_conj_lift)
                  apply (wpsimp wp: updateSchedContext_wp)
                 apply wpsimp
                 apply (rule hoare_vcg_conj_lift)
                  apply (wpsimp wp: setSchedContext_local_sym_refs simp: updateSchedContext_def)
                 apply wpsimp
                apply (clarsimp simp: sc_replies_sc_at_def obj_at_def is_sc_obj opt_map_red)
                apply (rule conjI, clarsimp simp: vs_all_heap_simps opt_map_red)
                apply (rename_tac n sc0)
                apply (clarsimp simp: reply_relation_def)
                apply (erule (1) valid_objsE[where x=scp])
                apply (clarsimp simp: valid_obj_def valid_sched_context_def obj_at_def)
                apply (case_tac "sc_replies sc0"; simp)
                apply (intro conjI impI allI; rename_tac ls; case_tac ls; clarsimp)
               apply (clarsimp simp: valid_obj'_def opt_map_red)
               apply (intro conjI impI)
                   apply (fastforce simp: obj_at'_def opt_map_red opt_pred_def
                                          valid_sched_context'_def valid_obj'_def valid_reply'_def
                                          refillSize_def
                                   split: if_splits)
                  apply (fold fun_upd_def)
                  apply (clarsimp simp: obj_at'_def  opt_map_red ps_clear_upd gen_objBits_simps
                                 split: if_split)
                 apply (fastforce dest!: sym_refs_replyNext_replyPrev_sym[where rp'=rp and rp=rp, THEN iffD2]
                                   simp: gen_obj_at_simps opt_map_red)
                apply (clarsimp del: opt_mapE)
                apply (drule (4) sym_refs_scReplies[simplified sym_heap_def, rule_format, THEN iffD1])
                apply (clarsimp simp: obj_at'_def  opt_map_red)
               apply (clarsimp del: opt_mapE)
               apply (drule (1) reply_sym_heap_Prev_Next[simplified sym_heap_def, rule_format, THEN iffD1])
               apply (clarsimp simp: obj_at'_def  opt_map_red)
              apply wpsimp
              apply (fastforce elim!: pred_tcb'_weakenE)
             apply wpsimp
            apply wpsimp
           apply (wpsimp simp: assert_def reply_relation_def split: if_split)
          apply wpsimp
         apply (wpsimp simp: reply_relation_def)
        apply wpsimp
        apply (wpsimp wp: get_simple_ko_wp)
       apply wpsimp
      apply simp
     apply (clarsimp del: opt_mapE)
     apply (rule conjI)
      apply (clarsimp simp: sym_refs_asrt_def pred_tcb_at'_def obj_at'_def)
      apply (drule sym_ref_Receive_or_Reply_replyTCB')
        apply (fastforce simp: obj_at'_def)
       apply (rule disjI2, rule sym, simp)
      apply clarsimp
     apply (drule (4) sym_refs_scReplies[simplified sym_heap_def, rule_format, THEN iffD1])
     apply (clarsimp simp: obj_at'_def  opt_map_red)
    apply (wpsimp wp: get_sched_context_exs_valid)
     apply (clarsimp simp: obj_at_def is_sc_obj)
    apply simp
   apply wpsimp
   apply (prop_tac "distinct (sc_replies sc)")
    apply (fastforce simp: valid_obj_def obj_at_def is_sc_obj valid_sched_context_def)
   apply (frule sym_refs_ep_queues_blocked)
   apply (clarsimp simp: gen_obj_at_simps opt_map_red vs_all_heap_simps)
  apply wpsimp
  apply (clarsimp simp: obj_at_def is_sc_obj)
  done

lemma get_tcb_obj_ref_exs_valid[wp]:
  "\<exists>tcb. kheap s tp = Some (Structures_A.TCB tcb)
   \<Longrightarrow> \<lbrace>(=) s\<rbrace> get_tcb_obj_ref f tp \<exists>\<lbrace>\<lambda>_. (=) s\<rbrace>"
  by (clarsimp simp: get_tcb_obj_ref_def thread_get_def gets_the_def get_tcb_def bind_def
                     gets_def get_def return_def exs_valid_def
              split: Structures_A.kernel_object.splits)

lemma replyRemove_corres:
  "\<lbrakk> st = Structures_A.thread_state.BlockedOnReply rp;
     st'= BlockedOnReply (Some rp)\<rbrakk> \<Longrightarrow>
   corres dc (valid_objs and pspace_aligned and pspace_distinct and valid_replies
              and weak_valid_sched_action and active_scs_valid and valid_release_q
              and valid_ready_qs and ready_or_release
              and st_tcb_at ((=) st) t and (\<lambda>s. sym_refs (state_refs_of s)))
             (valid_objs' and sym_heap_sched_pointers and valid_sched_pointers
              and (\<lambda>s'. sym_refs (list_refs_of_replies' s')) and K (rp' = rp))
             (reply_remove t rp) (replyRemove rp' t)"
  (is "\<lbrakk> _ ; _ \<rbrakk> \<Longrightarrow> corres _ ?abs_guard ?conc_guard _ _")
  apply (rule corres_gen_asm2', simp only:)
  apply add_sym_refs
  apply (rule_tac Q'="st_tcb_at' ((=) st') t" in corres_cross_add_guard)
   apply (fastforce dest!: st_tcb_at_coerce_concrete elim!: pred_tcb'_weakenE)
  apply (rule_tac Q="reply_at rp" in corres_cross_add_abs_guard)
   apply (fastforce dest: st_tcb_at_valid_st2)
  apply (clarsimp simp: reply_remove_def replyRemove_def)
  apply (rule corres_stateAssert_add_assertion[rotated], clarsimp)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF get_reply_corres])
      apply (rename_tac reply reply')
      apply (rule_tac P="?abs_guard and ko_at (Structures_A.Reply reply) rp"
                 and P'="?conc_guard and (\<lambda>s. sym_refs (state_refs_of' s)) and st_tcb_at' ((=) st') t
                         and ko_at' reply' rp"
             in corres_inst)
      apply (rule corres_guard_imp)
        apply (rule corres_assert_gen_asm_l)
        apply (prop_tac "reply_tcb reply = replyTCB reply'")
         apply (clarsimp simp: reply_relation_def)
        apply (clarsimp simp: assert_opt_def isReply_def split del: if_split)
        apply (rule_tac P="?abs_guard and ko_at (Structures_A.Reply reply) rp"
                   and P'="?conc_guard and (\<lambda>s. sym_refs (state_refs_of' s)) and st_tcb_at' ((=) st') t
                           and ko_at' reply' rp"
               in corres_inst)
        apply (rule_tac Q'="\<lambda>rv'. ?conc_guard and st_tcb_at' ((=) st') t and (\<lambda>s'. sym_refs (state_refs_of' s'))
                                  and ko_at' reply' rp and K (rv' = st')"
               in corres_symb_exec_r)
           apply (rename_tac rv')
           apply (rule corres_gen_asm2')
           apply (simp only:)
           apply (rule corres_guard_imp)
             apply (rule corres_assert_gen_asm2; simp split del: if_split)
             apply (rule corres_symb_exec_l)
                apply (rename_tac sc_opt)
                apply (rule_tac P="?abs_guard and (\<lambda>s. sc_with_reply rp s = sc_opt) and  ko_at (Structures_A.Reply reply) rp"
                           and P'="?conc_guard and (\<lambda>s. sym_refs (state_refs_of' s)) and ko_at' reply' rp"
                       in corres_inst)
                apply (rule_tac Q'="(\<lambda>s'. sc_with_reply' rp s' = sc_opt) and pspace_aligned'
                                    and pspace_distinct' and pspace_bounded'"
                       in corres_cross_add_guard)
                 apply (frule pspace_relation_pspace_bounded'[OF state_relation_pspace_relation])
                 apply (fastforce simp: sc_replies_relation_sc_with_reply_cross_eq
                                 dest!: state_relationD pspace_distinct_cross dest: pspace_aligned_cross)
                apply (case_tac sc_opt; simp split del: if_split add: bind_assoc)
                 (* sc_with_reply rp s = None *)
                 apply (rule_tac F="replySC reply' = None" in corres_req)
                  apply (fastforce dest!: sc_with_reply_None_reply_sc_reply_at replySCs_of_cross
                                   elim!: obj_at_weakenE
                                    simp: is_reply obj_at'_def  opt_map_red)
                 apply (clarsimp simp: replySC_None_not_head)
                 apply (simp only: bind_assoc[symmetric])
                 apply (rule corres_symb_exec_r_sr)
                    apply (rule corres_guard_imp)
                      apply (rule replyUnlinkTcb_corres[simplified dc_def])
                     apply (fastforce dest: valid_objs_valid_tcbs st_tcb_reply_state_refs
                                      simp: obj_at_def is_reply reply_tcb_reply_at_def elim!: pred_tcb_weakenE)
                    apply simp
                   apply (rule sr_inv_imp)
                     apply (erule sr_inv_sc_with_reply_None_helper)
                    apply (fastforce elim!: obj_at_weakenE simp: is_reply)
                   apply simp
                  apply (wpsimp wp: updateReply_valid_objs' simp: valid_reply'_def obj_at'_def)
                  apply (fastforce elim!: reply_ko_at_valid_objs_valid_reply')
                 apply (wpsimp wp: no_fail_sc_wtih_reply_None_helper, simp)
                (* sc_with_reply \<noteq> None : rp is in a reply stack *)
                apply (rename_tac scp)
                apply (rule_tac F="replyNext reply' \<noteq> None" in corres_req)
                 apply clarsimp
                 apply (prop_tac "sc_at scp s")
                  apply (fastforce dest!: sc_with_reply_SomeD1
                                    simp: sc_replies_sc_at_def obj_at_def is_sc_obj_def
                                    elim: valid_sched_context_size_objsI)
                 apply (prop_tac "sc_at' scp s'")
                  apply (fastforce dest!: state_relationD sc_at_cross)
                 apply (drule sc_with_reply'_SomeD, clarsimp)
                 apply (case_tac "hd xs = rp")
                  apply (drule heap_path_head, clarsimp)
                  apply (drule (3) sym_refs_scReplies)
                  apply (clarsimp simp: obj_at'_def sym_heap_def elim!: opt_mapE)
                 apply (frule (1) heap_path_takeWhile_lookup_next)
                 apply (frule heap_path_head, clarsimp)
                 apply (prop_tac "takeWhile ((\<noteq>) rp) xs = hd xs # tl (takeWhile ((\<noteq>) rp) xs)")
                  apply (case_tac xs; simp)
                 apply (simp del: heap_path.simps)
                 apply (drule_tac p1="hd xs" and ps1="tl (takeWhile ((\<noteq>) rp) xs)"
                        in sym_refs_reply_heap_path_doubly_linked_Nexts_rev[where p'=rp, THEN iffD1])
                  apply clarsimp
                 apply (case_tac "rev (tl (takeWhile ((\<noteq>) rp) xs))";
                        clarsimp simp: obj_at'_def elim!: opt_mapE)
                apply (clarsimp simp: liftM_def bind_assoc split del: if_split)
                apply (rename_tac next_reply)
                apply (rule_tac Q="\<lambda>sc. ?abs_guard
                                        and (\<lambda>s. \<exists>n. kheap s scp = Some (Structures_A.SchedContext sc n))
                                        and (\<lambda>s. sc_with_reply rp s = Some scp)
                                        and ko_at (Structures_A.Reply reply) rp
                                        and  K (rp \<in> set (sc_replies sc))"
                       in corres_symb_exec_l)
                   apply (rename_tac sc)
                   apply (rule_tac Q'="\<lambda>s. scReplies_of s scp = hd_opt (sc_replies sc) \<and> sc_at' scp s"
                          in corres_cross_add_guard)
                    apply (clarsimp; rule conjI)
                     apply (frule state_relation_sc_replies_relation)
                     apply (frule sc_replies_relation_scReplies_of[symmetric])
                       apply (fastforce dest!: sc_at_cross valid_objs_valid_sched_context_size
                                         simp: obj_at_def is_sc_obj_def obj_at'_def)
                      apply (fastforce dest!: sc_at_cross valid_objs_valid_sched_context_size
                                        simp: obj_at_def is_sc_obj_def state_relation_def obj_at'_def
                                               opt_map_def)
                     apply (clarsimp simp: sc_replies_of_scs_def map_project_def opt_map_def
                                           scs_of_kh_def)
                    apply (fastforce dest!: state_relation_pspace_relation sc_at_cross
                                            valid_objs_valid_sched_context_size
                                      simp: obj_at_def is_sc_obj)
                   apply (rule corres_gen_asm')
                   apply (rule corres_symb_exec_l)
                      apply (rename_tac tcbsc)
                      apply (rule_tac P="?abs_guard and (\<lambda>s. sc_with_reply rp s = Some scp)
                                         and obj_at (\<lambda>ko. \<exists>n. ko = Structures_A.SchedContext sc n) scp
                                         and bound_sc_tcb_at ((=) tcbsc) t
                                         and ko_at (Structures_A.Reply reply) rp
                                         and reply_sc_reply_at
                                                  (\<lambda>ko. (hd (sc_replies sc) = rp \<longrightarrow> Some scp = ko)
                                                      \<and> (hd (sc_replies sc) \<noteq> rp \<longrightarrow> None = ko)) rp"
                             in corres_inst)
                      apply (rule_tac F="(hd (sc_replies sc) = rp \<longrightarrow> replySC reply' = Some scp)
                                          \<and> (hd (sc_replies sc) \<noteq> rp \<longrightarrow> replySC reply' = None)"
                             in corres_req, clarsimp)
                       apply (drule (1) replySCs_of_cross)
                       apply (clarsimp simp: obj_at'_def opt_map_red  getHeadScPtr_def
                                      split: reply_next.splits)
                      apply (case_tac "hd (sc_replies sc) = rp"; simp add: bind_assoc split del: if_split)

                       (* hd (sc_replies sc) = rp & replysc = Some scp: rp is at the head of the queue *)
                       apply (simp add: isHead_def)
                       apply (rule corres_guard_imp)
                         (* replyPop *)
                         apply (rule replyPop_corres[simplified dc_def]; simp)
                        apply (clarsimp simp: obj_at_def is_sc_obj is_reply opt_map_red
                                              reply_tcb_reply_at_def vs_all_heap_simps)
                        apply (drule (1) valid_sched_context_size_objsI, simp)
                        apply (drule sc_with_reply_SomeD)
                        apply (metis list.sel(1) list.set_cases)
                       apply (clarsimp simp: obj_at'_def)

                      (* rp is in the middle of the reply stack *)
                      (* hd (sc_replies sc) \<noteq> rp & rp \<in> set (sc_replies sc) *)
                      apply (simp add: reply_unlink_sc_def bind_assoc liftM_def split del: if_split)
                      apply (rule_tac Q="\<lambda>rv. ?abs_guard and (\<lambda>s. sc_with_reply rp s = Some scp)
                                              and obj_at (\<lambda>ko. \<exists>n. ko = kernel_object.SchedContext sc n) scp
                                              and bound_sc_tcb_at ((=) tcbsc) t
                                              and ko_at (Structures_A.Reply reply) rp
                                              and reply_sc_reply_at ((=) None) rp and K (rv = sc)"
                             in corres_symb_exec_l)
                         apply (rule corres_gen_asm', simp split del: if_split)
                         apply (rule_tac Q="\<lambda>rv. ?abs_guard and (\<lambda>s. sc_with_reply rp s = Some scp)
                                                  and obj_at (\<lambda>ko. \<exists>n. ko = kernel_object.SchedContext sc n) scp
                                                  and bound_sc_tcb_at ((=) tcbsc) t
                                                  and ko_at (Structures_A.Reply reply) rp
                                                  and reply_sc_reply_at ((=) None) rp and K (rv = reply)"
                                in corres_symb_exec_l)
                            apply (rule corres_gen_asm')
                            apply (simp split del: if_split add: bind_assoc)
                            apply (rule corres_guard_imp)
                              apply (rule_tac Q="?conc_guard and ko_at' reply' rp and sc_at' scp
                                                 and (\<lambda>s'. sym_refs (state_refs_of' s'))
                                                 and (\<lambda>s'. sc_with_reply' rp s' = Some scp)
                                                 and (\<lambda>s'. scReplies_of s' scp = hd_opt (sc_replies sc))
                                                 and (\<lambda>s'. \<forall>prp. replyPrev reply' = Some prp
                                                                 \<longrightarrow> replyNexts_of s' prp = Some rp)"
                                     in corres_assert_gen_asm_l)
                              apply (clarsimp simp: getHeadScPtr_def isHead_def neq_conv[symmetric]
                                             split: reply_next.splits)
                              apply (rename_tac nxt_rp)
                              apply (rule stronger_corres_guard_imp)
                                apply (rule corres_split
                                              [OF updateReply_replyPrev_takeWhile_middle_corres])
                                    apply simp
                                   apply simp
                                  apply (rule_tac P ="?abs_guard and reply_sc_reply_at ((=) None) rp
                                                       and ko_at (Structures_A.Reply reply) rp
                                                       and bound_sc_tcb_at ((=) tcbsc) t" and
                                                  Q ="\<lambda>s. sc_with_reply rp s = None" and
                                                  P'="valid_objs' and ko_at' reply' rp and sc_at' scp" and
                                                  Q'="(\<lambda>s'. \<forall>prp. replyPrev reply' = Some prp
                                                                  \<longrightarrow> replyNexts_of s' prp = Some rp)"
                                        in corres_inst_add)
                                  apply (rule corres_symb_exec_r_sr)
                                     apply (rule corres_symb_exec_r_sr)
                                        apply (rule corres_guard_imp)
                                          apply (rule replyUnlinkTcb_corres[simplified dc_def])
                                         apply (fastforce dest: valid_objs_valid_tcbs st_tcb_reply_state_refs
                                                          simp: obj_at_def is_reply reply_tcb_reply_at_def elim!: pred_tcb_weakenE)
                                        apply simp
                                       apply (rule sr_inv_imp)
                                         apply (rule cleanReply_sr_inv)
                                        apply simp
                                       apply simp
                                      apply wpsimp
                                     apply wpsimp
                                     apply (clarsimp dest!: state_relationD simp: reply_sc_reply_at_def)
                                     apply (fastforce intro!: reply_at_cross elim!: obj_at_weakenE simp: is_reply)
                                    apply (clarsimp cong: conj_cong)
                                    apply (case_tac "replyPrev reply'"; simp)
                                    apply (rename_tac prev_rp)
                                    apply (rule sr_inv_imp)
                                      apply (rule_tac P =\<top> and
                                                      P'=" (\<lambda>s'. \<forall>prp. replyPrev reply' = Some prp
                                                                       \<longrightarrow> replyNexts_of s' prev_rp = Some rp)"
                                             in updateReply_sr_inv)
                                       apply (clarsimp simp: reply_relation_def  obj_at'_def obj_at_def
                                                      elim!: opt_mapE)
                                      apply clarsimp
                                      apply (drule_tac rp=prev_rp in sc_replies_relation_replyNext_update, simp)
                                      apply simp
                                     apply simp
                                    apply clarsimp
                                   apply wpsimp
                                  apply wpsimp
                                  apply (clarsimp dest!: reply_ko_at_valid_objs_valid_reply'
                                                   simp: valid_reply'_def)
                                 apply (wpsimp wp: sc_replies_update_takeWhile_sc_with_reply
                                                   sc_replies_update_takeWhile_middle_sym_refs
                                                   sc_replies_update_takeWhile_valid_replies)
                                apply (wpsimp wp: updateReply_valid_objs' updateReply_ko_at'_other)
                               apply (clarsimp cong: conj_cong)
                               apply simp
                              apply (clarsimp simp: valid_reply'_def)
                              apply (rule context_conjI)
                               apply (clarsimp simp: obj_at'_def  opt_map_red)
                              apply (clarsimp simp: obj_at_def del: opt_mapE)
                              apply (frule (1) valid_sched_context_objsI)
                              apply (clarsimp simp: valid_sched_context_def del: opt_mapE)
                              apply (frule (4) next_reply_in_sc_replies[OF state_relation_sc_replies_relation])
                                 apply (fastforce dest!: state_relationD pspace_aligned_cross pspace_distinct_cross)
                                apply (fastforce dest!: state_relationD pspace_distinct_cross)
                               apply (fastforce dest!: state_relationD pspace_relation_pspace_bounded')
                              apply (clarsimp simp: obj_at'_def)
                              apply (clarsimp simp: vs_heap_simps)
                             apply clarsimp
                             apply (rule conjI)
                              apply (clarsimp simp: list_all_iff dest!: set_takeWhileD)
                             apply (clarsimp simp: reply_relation_def)
                            apply (fastforce elim!: sym_refs_replyNext_replyPrev_sym[THEN iffD2]
                                              simp: opt_map_red obj_at'_def)
                           apply (wpsimp simp: get_sk_obj_ref_def wp: get_reply_exs_valid)
                            apply (fastforce dest!: Reply_or_Receive_reply_at[rotated]
                                              simp: obj_at_def is_reply)
                           apply simp
                          apply (wpsimp wp: get_simple_ko_wp)
                          apply (clarsimp simp: obj_at_def reply_sc_reply_at_def)
                         apply (wpsimp simp: get_sk_obj_ref_def get_simple_ko_def obj_at_def
                                         wp: get_object_wp)
                         apply (fastforce simp: obj_at_def is_reply partial_inv_def a_type_def)
                        apply (wpsimp wp: get_sched_context_exs_valid)
                         apply (drule sc_with_reply_SomeD)
                         apply clarsimp+
                       apply (wpsimp simp: obj_at_def)
                      apply (wpsimp wp: get_sched_context_no_fail)
                      apply (fastforce elim!: valid_sched_context_size_objsI simp: obj_at_def is_sc_obj_def)
                     apply (wpsimp simp: pred_tcb_at_def obj_at_def)
                    apply (wpsimp wp: gbsc_bound_tcb simp: obj_at_def)
                    apply (clarsimp simp: obj_at_def reply_sc_reply_at_def is_reply)
                    apply (case_tac "sc_replies sc"; simp)
                    apply (intro conjI impI)
                     apply (fastforce dest!: sym_refs_reply_sc_reply_at
                                       simp: sc_replies_sc_at_def obj_at_def reply_sc_reply_at_def)
                    apply (fastforce dest!: sc_replies_middle_reply_sc_None
                                      simp: vs_heap_simps obj_at_def is_sc_obj is_reply reply_sc_reply_at_def
                                     elim!: valid_sched_context_size_objsI opt_mapE)
                   apply (wpsimp simp: get_tcb_obj_ref_def thread_get_def st_tcb_def2)
                  apply (wpsimp wp: get_sched_context_exs_valid)
                   apply (fastforce dest!: sc_with_reply_SomeD1 simp: sc_replies_sc_at_def obj_at_def)
                  apply simp
                 apply wpsimp
                 apply (fastforce dest!: sc_with_reply_SomeD1 simp: sc_replies_sc_at_def obj_at_def)
                apply (wpsimp wp: get_sched_context_no_fail)
                apply (fastforce dest!: sc_with_reply_SomeD1 simp: sc_replies_sc_at_def is_sc_obj obj_at_def
                                 elim!: obj_at_weakenE valid_sched_context_size_objsI)
               apply wpsimp
              apply wpsimp
             apply wpsimp
            apply simp
           apply (fastforce dest!: st_tcb_at_valid_st2 simp: valid_tcb_state_def)
          apply clarsimp
          apply (wpsimp simp: op_equal)
         apply wpsimp
        apply wpsimp
       apply (fastforce dest: valid_objs_valid_tcbs st_tcb_reply_state_refs
                         simp: obj_at_def is_reply reply_tcb_reply_at_def)
      apply clarsimp
     apply (wpsimp wp: get_simple_ko_ko_at)
    apply wpsimp
   apply clarsimp
  apply (fastforce intro!: reply_at_cross)
  done

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
         apply (rule threadset_corres; (simp add: inQ_def)?)
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
      apply (wpsimp wp: threadSet_pred_tcb_no_state RISCV64.threadSet_invs_trivial)+ (*FIXME arch-split RT*)
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

context begin interpretation Arch . (*FIXME: arch-split*)

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
  apply (simp add: cancelSignal_def invs'_def valid_pspace'_def Let_def valid_dom_schedule'_def)
  apply (intro bind_wp[OF _ stateAssert_sp])
  apply (wp valid_irq_node_lift irqs_masked_lift hoare_vcg_all_lift hoare_vcg_imp_lift'
            setThreadState_sched_pointers_valid_sched_pointers sts'_valid_replies')
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

end

crunch cancelIPC
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and ksMachineState[wp]: "\<lambda>s. P (ksMachineState s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
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
          apply (wpsimp wp: gts_wp' hoare_vcg_all_lift hoare_drop_imps)+
  done

crunch blockedCancelIPC
  for sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_bitmaps[wp]: valid_bitmaps
  (wp: crunch_wps)

lemma valid_irq_node'_ksSchedulerAction[simp]:
  "valid_irq_node' w (ksSchedulerAction_update f s) = valid_irq_node' w s"
  by (simp add: valid_irq_node'_def)

crunch blockedCancelIPC
  for list_refs_of_replies'[wp]: "\<lambda>s. P (list_refs_of_replies' s)"
  (wp: crunch_wps)

lemma blockedCancelIPC_invs':
  "\<lbrace>invs' and st_tcb_at' ((=) st) tptr\<rbrace>
   blockedCancelIPC st tptr rptrOpt
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_dom_schedule'_def
  apply (wpsimp wp: blockedCancelIPC_valid_sched_pointers
                    valid_irq_node_lift valid_irq_handlers_lift' valid_irq_states_lift'
                    irqs_masked_lift
              simp: cteCaps_of_def)
  done

lemma threadSet_fault_invs':
  "threadSet (tcbFault_update upd) t \<lbrace>invs'\<rbrace>"
  apply (wpsimp wp: RISCV64.threadSet_invs_trivial) (*FIXME arch-split RT*)
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
    = weak_sch_act_wf_lift[OF _ setCTE.typ_at_lifts_all'(1)]

 (* prevents wp from splitting on the when; stronger technique than hoare_when_weak_wp
    FIXME: possible to replace with hoare_when_weak_wp?
 *)
definition
  "removeFromBitmap_conceal d p q t \<equiv> when (null [x\<leftarrow>q . x \<noteq> t]) (removeFromBitmap d p)"

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

lemma (in delete_one) suspend_corres:
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
            apply (clarsimp simp: update_restart_pc_def updateRestartPC_def)
            apply (rule asUser_corres')
            apply (simp add: RISCV64.nextInstructionRegister_def RISCV64.faultRegister_def
                             RISCV64_H.nextInstructionRegister_def RISCV64_H.faultRegister_def
                             RISCV64_H.Register_def)
            apply (rule corres_underlying_trivial)
            apply (wpsimp simp: RISCV64.setRegister_def RISCV64.getRegister_def)
           apply (rule corres_rel_imp)
            apply (rule corres_return_trivial)
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
         apply (wpsimp wp: gts_wp hoare_vcg_all_lift hoare_drop_imps
                | strengthen invs_implies valid_ready_qs_in_correct_ready_q
                             valid_ready_qs_ready_qs_distinct
                             valid_sched_valid_ready_qs valid_sched_valid_release_q invs'_implies
                             sym_refs_ep_queues_blocked sym_refs_ntfn_queues_blocked
                             valid_ready_qs_ready_queues_runnable valid_release_q_release_q_runnable)+
   apply (fastforce dest: valid_sched_valid_release_q)
  apply clarsimp
  done

lemma (in delete_one) prepareThreadDelete_corres:
  "corres dc \<top> \<top>
          (prepare_thread_delete t) (ArchRetypeDecls_H.RISCV64_H.prepareThreadDelete t)"
  by (simp add: RISCV64_A.prepare_thread_delete_def RISCV64_H.prepareThreadDelete_def)

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

lemma (in delete_one_conc) suspend_invs'[wp]:
  "suspend t \<lbrace>invs'\<rbrace>"
  apply (simp add: suspend_def updateRestartPC_def)
  apply (wpsimp wp: tcbReleaseRemove_invs' schedContextCancelYieldTo_invs' sts_invs_minor' gts_wp')
    apply (rule_tac Q'="\<lambda>_. invs' and st_tcb_at' simple' t" in hoare_post_imp)
     apply (fastforce elim: pred_tcb'_weakenE)
    apply wpsimp+
  done

lemma (in delete_one_conc_pre) suspend_st_tcb_at':
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

lemmas (in delete_one_conc_pre) suspend_makes_simple' =
       suspend_st_tcb_at' [where P=simple', simplified]

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

global_interpretation refillUnblockCheck: typ_at_all_props' "refillUnblockCheck scp"
  by typ_at_props'

global_interpretation ifCondRefillUnblockCheck: typ_at_all_props' "ifCondRefillUnblockCheck scp act ast"
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
     (valid_objs' and valid_sched_pointers
      and pspace_aligned' and pspace_distinct' and pspace_bounded'
      and (\<lambda>s. \<not> is_sched_linked t s))
     (restart_thread_if_no_fault t) (restartThreadIfNoFault t)"
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

global_interpretation possibleSwitchTo: typ_at_all_props' "possibleSwitchTo target"
  by typ_at_props'

crunch ifCondRefillUnblockCheck
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P p"
  (simp: crunch_simps wp: whileLoop_wp crunch_wps ignore: threadSet)

crunch removeAndRestartEPQueuedThread, removeAndRestartNTFNQueuedThread
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  and pspace_bounded'[wp]: pspace_bounded'
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

lemma set_reply_ready_queues_runnable[wp]:
  "set_reply reply_ptr reply \<lbrace>ready_queues_runnable\<rbrace>"
  by (wpsimp wp: ready_queues_runnable_lift)

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

lemma set_reply_obj_ref_ep_queued[wp]:
  "set_reply_obj_ref update ref new \<lbrace>\<lambda>s. P (ep_queued t s)\<rbrace>"
  by (wpsimp wp: ep_queued_lift)

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
  apply (rule corres_cross_add_guard[where Q'="tcb_at' t"])
   apply (fastforce intro!: tcb_at_cross)
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest: pspace_distinct_cross)
  apply (rule_tac Q'=pspace_bounded' in corres_cross_add_guard)
   apply (fastforce intro!: pspace_relation_pspace_bounded')
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
           apply (rule replyUnlinkTcb_corres)
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

lemma is_blocked_on_ntfn_isNtfn:
  "\<lbrakk>is_blocked_on_ntfn st; thread_state_relation st st'\<rbrakk> \<Longrightarrow> isNtfn st'"
  by (cases st; cases st'; clarsimp simp: thread_state_relation_def isNtfn_def)

lemma removeAndRestartNTFNQueuedThread_corres:
  "corres dc
     (in_ntfn_queue_at t ntfnPtr and not ep_queued t and not_queued t and not_in_release_q t
      and tcb_at t and valid_objs and valid_sched and current_time_bounded
      and ep_queues_blocked and ntfn_queues_blocked
      and pspace_aligned and pspace_distinct)
     (valid_objs' and valid_sched_pointers and sym_heap_sched_pointers and pspace_bounded')
     (remove_and_restart_ntfn_queued_thread t ntfnPtr)
     (removeAndRestartNTFNQueuedThread t ntfnPtr)"
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_distinct_cross)
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
   apply (rule_tac st=st in is_blocked_on_ntfn_isNtfn)
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
  and list_refs_of_replies'[wp]: "\<lambda>s. P (list_refs_of_replies' s)"
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

context Arch begin arch_global_naming

lemma tcbSchedEnqueue_valid_pspace'[wp]:
  "tcbSchedEnqueue tcbPtr \<lbrace>valid_pspace'\<rbrace>"
  unfolding valid_pspace'_def
  by wpsimp

end

arch_requalify_facts tcbSchedEnqueue_valid_pspace' (* FIXME arch-split: interface *)
lemmas [wp] = tcbSchedEnqueue_valid_pspace'

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
  and list_refs_of_replies'[wp]: "\<lambda>s. P (list_refs_of_replies' s)"
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
                    simp: st_tcb_at'_def obj_at'_def isNtfn_def isBlockedOnReply_def
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
  unfolding invs'_def valid_dom_schedule'_def valid_pspace'_def
  by (wpsimp wp: replyUnlink_valid_sched_pointers)

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
                     ko_wp_at'_def  split_def in_magnitude_check
                     gen_objBits_simps updateObject_default_def
                     ps_clear_upd RISCV64_H.fromPPtr_def)

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

context begin interpretation Arch . (*FIXME: arch-split*)

lemma possibleSwitchTo_unlive_other:
  "\<lbrace>ko_wp_at' (Not \<circ> live') p and K (p \<noteq> t) and valid_tcbs'\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  unfolding possibleSwitchTo_def inReleaseQueue_def
  by (wpsimp wp: tcbSchedEnqueue_unlive_other threadGet_wp rescheduleRequired_unlive)+

lemma setThreadState_Inactive_unlive:
  "setThreadState Inactive tptr \<lbrace>ko_wp_at' (Not o live') p\<rbrace>"
  apply (clarsimp simp: setThreadState_def)
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: live'_def ko_wp_at'_def obj_at'_def gen_objBits_simps ps_clear_upd
                        hyp_live'_def)
  done

lemma replyUnlink_unlive:
  "replyUnlink replyPtr tcbPtr \<lbrace>ko_wp_at' (Not o live') p\<rbrace>"
  supply fun_upd_apply[simp del]
  apply (clarsimp simp: replyUnlink_def updateReply_def)
  apply (wpsimp wp: setThreadState_Inactive_unlive set_reply'.set_wp gts_wp')
  apply (clarsimp simp: live'_def ko_wp_at'_def live_reply'_def obj_at'_def ps_clear_upd fun_upd_apply)
  done

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
  apply (fastforce simp: obj_at'_def ps_clear_upd objBits_simps)
  done

lemma tcbNTFNDequeue_ntfnSc[wp]:
  "tcbNTFNDequeue tcbPtr ntfnPtr \<lbrace>obj_at' (\<lambda>ntfn. P (ntfnSc ntfn)) ntfnPtr\<rbrace>"
  apply (clarsimp simp: tcbNTFNDequeue_def)
  apply forward_inv_step+
  apply (wpsimp wp: updateNotification_wp hoare_drop_imps hoare_vcg_all_lift)
  apply (fastforce simp: obj_at'_def ps_clear_upd objBits_simps)
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

declare if_cong[cong]

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
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest!: pspace_distinct_cross)
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

lemma suspend_unqueued:
  "\<lbrace>\<top>\<rbrace> suspend t \<lbrace>\<lambda>_. obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  unfolding suspend_def comp_def
  by (wpsimp wp: tcbSchedDequeue_not_tcbQueued[simplified comp_def])

crunch schedContextCancelYieldTo, tcbQueueRemove, setThreadState
  for not_tcbInReleaseQueue[wp]: "obj_at' (\<lambda>tcb. P (tcbInReleaseQueue tcb)) t"
  (wp: crunch_wps)

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

crunch prepareThreadDelete
  for unqueued: "obj_at' (Not \<circ> tcbQueued) t"
  and inactive: "st_tcb_at' ((=) Inactive) t'"
  (simp: obj_at'_not_comp_fold)

end
end
