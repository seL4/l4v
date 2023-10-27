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

context begin interpretation Arch . (*FIXME: arch_split*)

(* FIXME RT: remove *)
declare if_weak_cong [cong]

crunch aligned'[wp]: cancelAllIPC pspace_aligned'
  (wp: crunch_wps mapM_x_wp' simp: unless_def crunch_simps)
crunch distinct'[wp]: cancelAllIPC pspace_distinct'
  (wp: crunch_wps mapM_x_wp' simp: unless_def crunch_simps)

crunch aligned'[wp]: cancelAllSignals pspace_aligned'
  (wp: crunch_wps mapM_x_wp')
crunch distinct'[wp]: cancelAllSignals pspace_distinct'
  (wp: crunch_wps mapM_x_wp')

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

lemma cancelSignal_tcb_at':
  "cancelSignal tptr ntfnptr \<lbrace>\<lambda>s. P (tcb_at' tptr' s)\<rbrace>"
  unfolding cancelSignal_def Let_def
  apply (wpsimp wp: hoare_drop_imp)
  done

crunches cancelIPC, cancelSignal
  (* FIXME RT: VER-1016 *)
  for tcb_at'_better[wp]: "\<lambda>s. P (tcb_at' p s)"
  and it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps cancelSignal_tcb_at' simp: crunch_simps pred_tcb_at'_def)

crunch pred_tcb_at'[wp]: emptySlot "pred_tcb_at' proj P t"
  (wp: setCTE_pred_tcb_at')

lemma valid_inQ_queues_ksReadyQueuesL1Bitmap_upd[simp]:
  "valid_inQ_queues (ksReadyQueuesL1Bitmap_update f s) = valid_inQ_queues s"
  unfolding valid_inQ_queues_def
  by simp

lemma valid_inQ_queues_ksReadyQueuesL2Bitmap_upd[simp]:
  "valid_inQ_queues (ksReadyQueuesL2Bitmap_update f s) = valid_inQ_queues s"
  unfolding valid_inQ_queues_def
  by simp

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
  assumes delete_one_queues:
    "\<lbrace>Invariants_H.valid_queues and valid_objs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)\<rbrace>
     cteDeleteOne sl \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
    "\<lbrace>valid_inQ_queues and valid_objs'\<rbrace> cteDeleteOne sl \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
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
crunch typ_at'[wp]: emptySlot "\<lambda>s. P (typ_at' T p s)"
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
        (valid_tcbs' and valid_release_queue_iff)
        (reply_unlink_tcb t rp) (replyUnlink rp t)" (is "corres _ _ ?conc_guard _ _")
  apply (rule_tac Q="?conc_guard
         and st_tcb_at' (\<lambda>st. (\<exists>ep pl. st = BlockedOnReceive ep (receiver_can_grant pl) (Some rp))
                               \<or> st = BlockedOnReply (Some rp)) t"
         in corres_cross_over_guard)
   apply clarsimp
   apply (drule (1) st_tcb_at_coerce_concrete; clarsimp simp: state_relation_def)
   apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
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
  apply (prop_tac "reply_at' rp s")
   apply (fastforce simp: valid_tcbs'_def valid_tcb'_def valid_tcb_state'_def)
  apply (clarsimp simp: obj_at'_def)
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
  apply (clarsimp simp: replyUnlink_def getReply_def updateReply_def)
  apply (wpsimp wp: set_reply'.getObject_wp set_reply'.getObject_wp gts_wp'
              simp: valid_tcb_state'_def)
  done

lemma blocked_cancelIPC_corres:
  "\<lbrakk> st = Structures_A.BlockedOnReceive epPtr reply_opt p' \<or>
     st = Structures_A.BlockedOnSend epPtr p; thread_state_relation st st';
     st = Structures_A.BlockedOnSend epPtr p \<longrightarrow> reply_opt = None \<rbrakk> \<Longrightarrow>
   corres dc (valid_objs and pspace_aligned and pspace_distinct
              and st_tcb_at ((=) st) t and (\<lambda>s. sym_refs (state_refs_of s)))
             (valid_objs' and valid_release_queue_iff and st_tcb_at' ((=) st') t)
           (blocked_cancel_ipc st t reply_opt)
           (blockedCancelIPC st' t reply_opt)" (is "\<lbrakk> _ ; _ ; _ \<rbrakk> \<Longrightarrow> corres _ (?abs_guard and _) _ _ _")
  apply add_sym_refs
  apply (prop_tac "getBlockingObject st' = return epPtr")
   apply (case_tac st; clarsimp simp: getBlockingObject_def epBlocked_def)
  apply (simp add: blocked_cancel_ipc_def blockedCancelIPC_def gbep_ret)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getEndpoint_corres])
      apply (rule_tac F="ep \<noteq> IdleEP" in corres_gen_asm2)
      apply (rule corres_assert_assume[rotated])
       apply (clarsimp split: endpoint.splits)
       \<comment>\<open>drop sym_refs assumtions; add reply_tcb link\<close>
      apply (rule_tac P="?abs_guard and (\<lambda>s. bound reply_opt \<longrightarrow> reply_tcb_reply_at ((=) (Some t)) (the reply_opt) s)
                         and valid_ep rv
                         and (\<lambda>_. (st = Structures_A.BlockedOnSend epPtr p
                                      \<longrightarrow> (\<exists>list. rv = Structures_A.SendEP list))
                                \<and> (st = Structures_A.thread_state.BlockedOnReceive epPtr reply_opt p'
                                     \<longrightarrow> (\<exists>list. rv = Structures_A.RecvEP list)))"
                  and P'="valid_objs' and valid_release_queue_iff and st_tcb_at' ((=) st') t
                          and valid_ep' ep"
                   in corres_inst)
      \<comment>\<open>cross over replyTCB\<close>
      apply (rule_tac Q="\<lambda>s. bound reply_opt \<longrightarrow> obj_at' (\<lambda>r. replyTCB r = Some t) (the reply_opt) s" in corres_cross_add_guard)
       apply clarsimp
       apply (drule state_relationD)
       apply (frule_tac s'=s' in pspace_aligned_cross, simp)
       apply (frule_tac s'=s' in pspace_distinct_cross, simp, simp)
       apply (clarsimp simp: obj_at_def sk_obj_at_pred_def)
       apply (rename_tac rp list reply)
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
      apply (rule corres_gen_asm)
      apply (erule disjE; clarsimp simp: ep_relation_def get_ep_queue_def split del: if_split)
       \<comment>\<open>BlockedOnReceive\<close>
       apply (rename_tac list)
       apply (cases reply_opt;
              simp split del: if_split add: bind_assoc cong: if_cong)
         \<comment>\<open>reply_opt = None\<close>
        apply (rule corres_guard_imp)
          apply (rule corres_split[OF setEndpoint_corres])
             apply (simp add: ep_relation_def split: list.split)
            apply (rule setThreadState_corres)
            apply simp
           apply wpsimp+
         apply (frule (1) Receive_or_Send_ep_at[rotated], fastforce)
         apply (intro conjI;
                clarsimp simp: st_tcb_at_def obj_at_def is_ep is_tcb
                       intro!: valid_ep_remove1_RecvEP)
        apply clarsimp
        apply (frule Receive_or_Send_ep_at'[rotated], simp)
         apply (simp add: thread_state_relation_def)
        apply (fastforce simp: valid_ep'_def)
         \<comment>\<open>reply_opt bound\<close>
       apply (rule corres_guard_imp)
         apply (rule_tac R="\<lambda>_. ep_at epPtr and reply_tcb_reply_at ((=) (Some t)) a  and ?abs_guard"
                     and R'="\<lambda>_. ep_at' epPtr and obj_at' (\<lambda>r. replyTCB r = Some t) a
                                 and valid_objs' and valid_release_queue_iff
                                 and st_tcb_at' ((=) st') t"
                      in corres_split[OF setEndpoint_corres])
            apply (simp add: ep_relation_def split: list.split)
           apply (rule corres_guard_imp)
             apply (rule corres_split[OF replyUnlinkTcb_corres])
               apply (rule setThreadState_corres, simp)
              apply wpsimp
             apply (wpsimp wp: replyUnlink_valid_objs')
            apply (fastforce simp: pred_tcb_at_def obj_at_def is_tcb)
           apply (fastforce simp: obj_at'_def pred_tcb_at'_def)
          apply (wpsimp wp: set_simple_ko_wp)
         apply (wpsimp wp: set_ep'.set_wp)
        apply clarsimp
        apply (frule (1) Reply_or_Receive_reply_at[rotated], fastforce)
        apply (frule (1) Receive_or_Send_ep_at[rotated], fastforce)
        apply (clarsimp simp: st_tcb_at_tcb_at)
        apply (rule conjI, clarsimp simp: obj_at_def is_ep)
        apply (rule conjI, clarsimp simp: sk_obj_at_pred_def obj_at_def)
        apply (intro conjI)
           apply (fastforce elim!: valid_objs_ep_update intro!: valid_ep_remove1_RecvEP)
          apply (clarsimp elim!: pspace_aligned_obj_update dest!: invs_psp_aligned
                           simp: a_type_def is_ep)
         apply (clarsimp elim!: pspace_distinct_same_type dest!: invs_distinct
                          simp: a_type_def is_ep obj_at_def)
        apply (clarsimp simp: pred_tcb_at_def obj_at_def is_ep)
       apply (clarsimp split del: if_split)
       apply (frule (1) Receive_or_Send_ep_at'[rotated], blast)
       apply (clarsimp split del: if_split)
       apply (rule conjI, clarsimp simp: obj_at'_def ps_clear_upd objBits_simps)
       apply (rule conjI; clarsimp simp: pred_tcb_at'_def obj_at'_def ps_clear_upd)
       apply (intro conjI impI; clarsimp?)
         apply (erule valid_objs'_ep_update)
          apply (case_tac "remove1 t list";
                 clarsimp simp: valid_ep'_def obj_at'_def;
                 metis distinct.simps(2) distinct_remove1 list.set_intros(1) list.set_intros(2)
                       set_remove1)
         apply (clarsimp simp: obj_at'_def)
        apply ((clarsimp simp: obj_at'_def valid_ep'_def)+)[2]
        apply (erule valid_release_queue_ksPSpace_update)
         apply ((clarsimp simp: ko_wp_at'_def objBitsKO_def koTypeOf_def)+)[2]
       apply (erule valid_release_queue'_ksPSpace_update)
        apply ((clarsimp simp: ko_wp_at'_def objBitsKO_def koTypeOf_def)+)[2]
      \<comment>\<open>BlockedOnSend\<close>
      apply (rename_tac list)
      apply (rule corres_guard_imp)
        apply (rule corres_split[OF setEndpoint_corres])
           apply (simp add: ep_relation_def split: list.split)
          apply (rule setThreadState_corres)
          apply simp
         apply (simp add: valid_tcb_state_def pred_conj_def)
         apply wpsimp+
       apply (frule (1) Receive_or_Send_ep_at[rotated], fastforce)
       apply (intro conjI;
              clarsimp simp: st_tcb_at_def obj_at_def is_ep is_tcb
                     intro!: valid_ep_remove1_SendEP)
      apply (clarsimp split del: if_split)
      apply (frule (1) Receive_or_Send_ep_at'[rotated], blast)
      apply (fastforce simp: valid_ep'_def)
     apply (wpsimp wp: getEndpoint_wp hoare_vcg_conj_lift get_simple_ko_wp)+
   apply (frule (2) Receive_or_Send_ep_at, clarsimp)
   apply (rule conjI, clarsimp)
    apply (drule (1) st_tcb_recv_reply_state_refs)
    apply (clarsimp simp: sk_obj_at_pred_def obj_at_def)
   apply (rule conjI)
    apply (clarsimp simp: obj_at_def)
    apply (erule (1) valid_objsE[where x=epPtr])
    apply (clarsimp simp: valid_obj_def)
   apply (erule disjE; clarsimp simp: obj_at_def pred_tcb_at_def)
    apply (frule (2) sym_ref_BlockedOnReceive_RecvEP[OF _ _ sym], simp)
   apply (frule (2) sym_ref_BlockedOnSend_SendEP[OF _ _ sym], simp)
  apply clarsimp
  apply (rule context_conjI)
   apply (erule (1) Receive_or_Send_ep_at'[rotated])
   apply (fastforce simp: thread_state_relation_def)
  apply (clarsimp simp: obj_at'_def)
  apply (rule conjI)
   apply (erule (1) valid_objsE', clarsimp simp: valid_obj'_def)
  apply (erule disjE)
   apply (fastforce dest!: sym_ref_BlockedOnReceive_RecvEP' simp: ko_wp_at'_def)
  apply (fastforce dest!: sym_ref_BlockedOnSend_SendEP' simp: ko_wp_at'_def)
  done

lemma cancelSignal_corres:
  "corres dc
          (invs and valid_ready_qs and st_tcb_at ((=) (Structures_A.BlockedOnNotification ntfn)) t)
          (invs' and st_tcb_at' ((=) (BlockedOnNotification ntfn)) t)
          (cancel_signal t ntfn)
          (cancelSignal t ntfn)"
  apply add_sym_refs
  apply add_ready_qs_runnable
  apply (simp add: cancel_signal_def cancelSignal_def Let_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getNotification_corres])
      apply (rule_tac F="isWaitingNtfn (ntfnObj ntfnaa)" in corres_gen_asm2)
      apply (case_tac "ntfn_obj ntfna"; simp add: ntfn_relation_def isWaitingNtfn_def)
      apply (case_tac "ntfna", case_tac "ntfnaa")
      apply clarsimp
      apply wpfix
      apply (rename_tac list bound_tcb sc)
      apply (rule_tac R="remove1 t list = []" in corres_cases')
       apply (simp del: dc_simp)
       apply (rule corres_split[OF setNotification_corres])
          apply (simp add: ntfn_relation_def)
         apply (rule setThreadState_corres)
         apply simp
        apply (wp abs_typ_at_lifts)+
      apply (simp add: list_case_If del: dc_simp)
      apply (rule corres_split[OF setNotification_corres])
         apply (clarsimp simp add: ntfn_relation_def neq_Nil_conv)
        apply (rule setThreadState_corres)
        apply simp
       apply (wp abs_typ_at_lifts)+
     apply (wp get_simple_ko_wp getNotification_wp)+
   apply (clarsimp simp: conj_comms st_tcb_at_tcb_at)
   apply (clarsimp simp: st_tcb_at_def obj_at_def)
   apply (erule pspace_valid_objsE, fastforce)
   apply (clarsimp simp: valid_obj_def valid_tcb_def valid_tcb_state_def)
   apply (drule sym, simp add: obj_at_def)
   apply clarsimp
   apply (erule pspace_valid_objsE[where p=ntfn], fastforce)
   apply (fastforce simp: valid_obj_def valid_ntfn_def
                   split: option.splits Structures_A.ntfn.splits)
  apply (clarsimp simp: conj_comms pred_tcb_at' cong: conj_cong)
  apply (rule conjI)
   apply (simp add: pred_tcb_at'_def)
   apply (drule obj_at_ko_at')
   apply clarsimp
   apply (frule ko_at_valid_objs')
     apply fastforce
    apply simp
   apply (clarsimp simp: valid_obj'_def valid_tcb'_def valid_tcb_state'_def)
   apply (drule sym, simp)
  apply (intro conjI impI allI; fastforce?)
  apply (drule sym_refs_st_tcb_atD', fastforce)
  apply (fastforce simp: isWaitingNtfn_def ko_wp_at'_def obj_at'_def
                         ntfn_bound_refs'_def get_refs_def
                  split: Structures_H.notification.splits ntfn.splits option.splits)
  done

lemma cte_map_tcb_2:
  "cte_map (t, tcb_cnode_index 2) = t + 2*2^cte_level_bits"
  by (simp add: cte_map_def tcb_cnode_index_def to_bl_1 shiftl_t2n)

context begin interpretation Arch . (*FIXME: arch_split*)

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
     (valid_objs' and valid_release_queue_iff and
      (\<lambda>s'. sym_refs (list_refs_of_replies' s')) and
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
       apply (rule cleanReply_sr_inv[where P=\<top> and P'="valid_objs' and valid_release_queue_iff
                                                        and reply_at' rp"])
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
       apply (rule cleanReply_sr_inv[where P=\<top> and P'="valid_objs' and valid_release_queue_iff
                                                        and reply_at' rp"])
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
             and Q'="valid_objs' and valid_release_queue_iff and reply_at' rp
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
        apply (rule cleanReply_sr_inv[where P=\<top> and P'="valid_objs' and valid_release_queue_iff
                                                        and reply_at' rp"])
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
           (valid_objs' and valid_release_queue_iff and
            (\<lambda>s'. sym_refs (list_refs_of_replies' s')) and
            (\<lambda>s. sym_refs (state_refs_of' s)) and
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
  "corres dc (valid_objs and pspace_aligned and pspace_distinct and valid_replies
              and st_tcb_at ((=) (Structures_A.thread_state.BlockedOnReply rp)) t and (\<lambda>s. sym_refs (state_refs_of s)))
             (valid_objs' and valid_release_queue_iff and (\<lambda>s'. sym_refs (list_refs_of_replies' s')))
                (reply_remove_tcb t rp) (replyRemoveTCB t)"
  (is "corres _ ?abs_guard ?conc_guard _ _")
  apply add_sym_refs
  apply (rule_tac Q="st_tcb_at' ((=) (thread_state.BlockedOnReply (Some rp))) t" in corres_cross_add_guard)
   apply (fastforce dest!: st_tcb_at_coerce_concrete elim!: pred_tcb'_weakenE)
  apply (clarsimp simp: reply_remove_tcb_def replyRemoveTCB_def isReply_def)
  apply (rule corres_guard_imp)
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
             apply (rule_tac Q="(\<lambda>s'. sc_with_reply' rp s' = sc_opt) and pspace_aligned'
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
    apply (erule no_fail_sc_wtih_reply_None_helper)
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
                apply (rule_tac Q="(\<lambda>s'. scReplies_of s' scp = hd_opt (sc_replies sc)) and sc_at' scp"
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
                      apply (simp add: getHeadScPtr_def isHead_def neq_conv[symmetric] split: reply_next.splits)
                      apply (rule corres_split[OF setSchedContext_scReply_update_None_corres[simplified dc_def]])
                        apply (rule_tac Q =\<top> and
                                        P'="valid_objs' and valid_release_queue_iff and ko_at' reply' rp" and
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
                        apply (clarsimp dest!: reply_ko_at_valid_objs_valid_reply' simp: valid_reply'_def)
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
                                      simp: valid_sched_context'_def valid_sched_context_size'_def
                                            objBits_simps)
                     apply (erule sym_refs_replyNext_replyPrev_sym[THEN iffD2])
                     apply (clarsimp simp: opt_map_red obj_at'_def)
                    apply (frule (3) sym_refs_scReplies)
                    apply (clarsimp simp: hd_opt_def  opt_map_red sym_heap_def
                                   split: list.split_asm)
                    apply (clarsimp simp: opt_map_red obj_at'_def  split: reply_next.splits)

                  (* rp is in the middle of the reply stack *)
                  (* hd (sc_replies sc) \<noteq> rp & rp \<in> set (sc_replies sc) *)
                   apply (rule corres_guard_imp)
                     apply (rule_tac Q="valid_objs' and valid_release_queue_iff and ko_at' reply' rp
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
                                         P'="valid_objs' and valid_release_queue_iff
                                             and ko_at' reply' rp and sc_at' scp" and
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
   apply (prop_tac "reply_at' rp s")
    apply (fastforce dest: tcb_in_valid_state' simp: valid_tcb_state'_def)
  using fold_list_refs_of_replies' apply metis
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
  apply (rule_tac Q="sc_at' ptr" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD simp: obj_at_def is_sc_obj_def vs_heap_simps
                    elim!: sc_at_cross valid_objs_valid_sched_context_size)
  apply (rule_tac Q="pspace_aligned' and pspace_distinct'" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: pspace_aligned_cross pspace_distinct_cross)
  apply (rule_tac Q="\<lambda>s'. scReplies_of s' ptr = Some rp" in corres_cross_add_guard)
   apply (subst sc_replies_relation_scReplies_of[symmetric, OF state_relation_sc_replies_relation])
      apply simp
     apply clarsimp
     apply (fastforce simp: opt_map_red dest!: sc_at'_cross[OF state_relation_pspace_relation])
    apply (clarsimp simp: opt_map_red obj_at_simps)+
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
               apply (clarsimp simp: sc_relation_def refillSize_def objBits_simps)+
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

crunches sched_context_donate
  for sc_at[wp]: "sc_at scp"
  (simp: crunch_simps wp: crunch_wps)

crunches rescheduleRequired, setQueue, tcbSchedEnqueue, tcbReleaseRemove, updateReply
  for scReplies_of[wp]: "\<lambda>s. P' (scReplies_of s)"
  (simp: crunch_simps wp: crunch_wps)

crunches updateReply, setSchedContext, updateSchedContext
  for tcbSCs_of[wp]: "\<lambda>s. P' (tcbSCs_of s)"
  and list_refs_of_replies'[wp]: "\<lambda>s. P (list_refs_of_replies' s)"
  (simp: crunch_simps opt_map_Some_eta_fold wp: crunch_wps)

lemma scReplies_of_scTCB_update[simp]:
  "\<lbrakk> ko_at' sc scp s\<rbrakk>
   \<Longrightarrow> P (\<lambda>a. if a = scp then scReply (scTCB_update (\<lambda>_. Some tp) sc) else scReplies_of s a)
       \<longleftrightarrow> P (scReplies_of s)"
  by (fastforce simp: obj_at'_def  opt_map_red elim!: rsubst[where P=P])

crunches schedContextDonate
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

lemma replyPop_corres:
  "\<lbrakk>st = Structures_A.thread_state.BlockedOnReply rp;
    st' = Structures_H.thread_state.BlockedOnReply (Some rp)\<rbrakk> \<Longrightarrow>
   corres dc
     (valid_objs and pspace_aligned and pspace_distinct
      and st_tcb_at ((=) st) t and weak_valid_sched_action
      and sc_at scp and reply_at rp and active_scs_valid
      and valid_replies and (\<lambda>s. sym_refs (state_refs_of s))
      and bound_sc_tcb_at ((=) tcbsc) t
      and reply_tcb_reply_at ((=) (Some t)) rp
      and (\<lambda>s. sc_with_reply rp s = Some scp)
      and (\<lambda>s. (sc_replies_of s |> hd_opt) scp = Some rp))
     (valid_objs' and valid_release_queue_iff and valid_queues and valid_queues'
      and reply_at' rp and sc_at' scp
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
  apply (rule_tac Q="st_tcb_at' ((=) st') t" in corres_cross_add_guard)
   apply (fastforce dest!: st_tcb_at_coerce_concrete elim!: pred_tcb'_weakenE)
  apply (rule_tac Q="\<lambda>s. tcbSCs_of s t = tcbsc" in corres_cross_add_guard)
   apply (fastforce dest!: bound_sc_tcb_at_cross elim!: obj_at'_weakenE)
  apply (rule_tac Q="pspace_distinct'" in corres_cross_add_guard)
   apply (fastforce dest!: pspace_distinct_cross)
  apply (rule_tac Q="pspace_aligned'" in corres_cross_add_guard)
   apply (fastforce dest!: pspace_aligned_cross)
  apply (rule_tac Q="pspace_bounded'" in corres_cross_add_guard)
   apply (fastforce dest!: pspace_relation_pspace_bounded'[OF state_relation_pspace_relation])
  apply (rule_tac Q="\<lambda>s. scReplies_of s scp = Some rp" in corres_cross_add_guard)
   apply (fastforce simp: opt_map_red obj_at'_def
                   dest!: sc_replies_relation_scReplies_of state_relation_sc_replies_relation)
  apply (simp add: reply_unlink_sc_def replyPop_def bind_assoc liftM_def)
  apply (rule_tac Q="\<lambda>sc. ?abs_guard and reply_tcb_reply_at ((=) (Some t)) rp
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
         apply (rule_tac P="?abs_guard and reply_tcb_reply_at ((=) (Some t)) rp
                            and ko_at (Structures_A.Reply r) rp and bound_sc_tcb_at ((=) tcbsc) t
                            and (\<lambda>s. \<exists>n. ko_at (Structures_A.SchedContext sc n) scp s)"
                     and P'="?conc_guard and (\<lambda>s'. sym_refs (list_refs_of_replies' s'))
                            and pspace_aligned' and pspace_distinct' and pspace_bounded' and (\<lambda>s. sym_refs (state_refs_of' s))
                            and st_tcb_at' ((=) st') t and (\<lambda>s. tcbSCs_of s t = tcbsc) and ko_at' r' rp
                            and (\<lambda>s. scReplies_of s scp = Some rp)
                            and K (replyTCB r' = Some t) and K (replyNext r' = Some (Head scp))"
                in corres_inst)
         apply (rule corres_gen_asm2') (* replyNext r' = Some (Head scp) *)
         apply (rule corres_gen_asm2') (* replyTCB r' = Some t *)
         apply (erule exE, rename_tac list)
         apply (rule_tac F="case list of [] \<Rightarrow> replyPrev r' = None | a#_ \<Rightarrow> replyPrev r' = Some a"
                in corres_req)
          apply (clarsimp simp: obj_at_simps)
          apply (drule (1) sc_replies_relation_prevs_list'[OF state_relation_sc_replies_relation])
          apply (clarsimp simp: opt_map_red del: opt_mapE)
          apply (case_tac list; simp)
         apply (simp add: bind_assoc)
         apply (rule corres_symb_exec_l) (* assert reply_sc r = Some scp *)
            apply (rule corres_symb_exec_r) (* get threadState for t *)
               apply (rename_tac state)
               apply (rule_tac P="?abs_guard and reply_tcb_reply_at ((=) (Some t)) rp
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
               apply (simp add: bind_assoc isReply_def isHead_def)
               apply (subst bind_assoc[symmetric, where m="getSchedContext _"])
               apply (rule corres_guard_imp)
                 apply (rule corres_split[OF setSchedContext_pop_head_corres[where rp=rp]])
                    apply simp  (* scReplies at scp = replyPrev r', tl (sc_replies sc) *)
                   apply (rule corres_split[where r'=dc])
                      apply (case_tac list; simp)
                      apply (rename_tac a ls)
                      apply (rule_tac P="?abs_guard and reply_tcb_reply_at ((=) (Some t)) rp
                                         and sc_replies_sc_at ((=) (a#ls)) scp
                                         and ko_at (Structures_A.Reply r) rp
                                         and bound_sc_tcb_at ((=) tcbsc) t"
                                  and P'="?conc_guard and (\<lambda>s'. sym_refs (list_refs_of_replies' s'))
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
                         apply (rule_tac P="?abs_guard and reply_tcb_reply_at ((=) (Some t)) rp
                                             and bound_sc_tcb_at ((=) tcbsc) t
                                             and sc_replies_sc_at (\<lambda>ls. rp \<notin> set ls) scp
                                             and reply_sc_reply_at ((=) None) rp "
                                     and P'="?conc_guard and st_tcb_at' ((=) st') t
                                             and (\<lambda>s. (replies_of' s |> replyNext) rp = None)
                                             and (\<lambda>s. \<forall>p'. replyPrevs_of s p' \<noteq> Some rp)
                                             and (\<lambda>s. \<forall>p'. scReplies_of s p' \<noteq> Some rp)
                                             and (\<lambda>s. tcbSCs_of s t = tcbsc)"
                                in corres_inst)
                         apply (rule_tac Q'="\<lambda>rv. ?conc_guard and st_tcb_at' ((=) st') t
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
                                apply (rule_tac P="?abs_guard and reply_tcb_reply_at ((=) (Some t)) rp"
                                            and P'="valid_objs' and valid_release_queue_iff
                                                   and st_tcb_at' ((=) st') t and reply_at' rp
                                                   and (\<lambda>s. (replies_of' s |> replyNext) rp = None)
                                                   and (\<lambda>s. \<forall>p'. replyPrevs_of s p' \<noteq> Some rp)
                                                   and (\<lambda>s. \<forall>p'. scReplies_of s p' \<noteq> Some rp)"
                                       in corres_inst)
                                apply (rule corres_symb_exec_r_sr_strong) (* replyPrev at rp = None *)
                                   apply (rule corres_guard_imp)
                                     apply (rule replyUnlinkTcb_corres)
                                    apply (clarsimp simp: valid_objs_valid_tcbs elim!: pred_tcb_weakenE)
                                   apply simp
                                  apply (simp add: cleanReply_def)
                                  apply (rule_tac Q'="\<lambda>_ s. reply_at' rp s \<and> (replies_of' s |> replyNext) rp = None
                                                            \<and> (\<forall>p'. replyPrevs_of s p' \<noteq> Some rp)
                                                            \<and> (\<forall>p'. scReplies_of s p' \<noteq> Some rp)"
                                         in sr_inv_ul_bind[rotated])
                                    apply (rule updateReply_sr_inv)
                                     apply (clarsimp simp: reply_relation_def)
                                    apply (intro conjI impI allI)
                                    apply (erule sc_replies_relation_replyNext_None; clarsimp)
                                    apply (clarsimp simp: obj_at'_def opt_map_red)
                                   apply clarsimp
                                   apply (wpsimp wp: updateReply_wp_all)
                                   apply (clarsimp simp: obj_at'_def  objBits_simps ps_clear_upd opt_map_red)
                                   apply (rename_tac s s' reply' sc')
                                   apply (intro conjI allI; clarsimp split: if_split_asm simp:)
                                   apply (rename_tac scp' sc'')
                                   apply (drule_tac x=scp' in spec[where P="\<lambda>x. scReplies_of _ x \<noteq> Some rp"])
                                   apply (clarsimp simp: opt_map_red)
                                  apply (clarsimp simp: sr_inv_def updateReply_def)
                                  apply (clarsimp simp: setReply_def getReply_def getObject_def
                                                        setObject_def split_def objBits_simps'
                                                        updateObject_default_def in_monad fail_def
                                                        in_magnitude_check obj_at_simps return_def
                                                        loadObject_default_def RISCV64_H.fromPPtr_def
                                                 split: if_split_asm option.split_asm
                                                 dest!: readObject_misc_ko_at')
                                  apply (prop_tac "(ksPSpace s')(rp \<mapsto>
                                                          KOReply (replyNext_update Map.empty reply))
                                                   = ksPSpace s'")
                                   apply (rule ext)
                                   apply (clarsimp simp: opt_map_red split: if_split)
                                   apply (case_tac reply; simp)
                                  apply simp
                                 apply wpsimp
                                apply wpsimp
                               apply wpsimp
                              apply (rule hoare_when_cases, simp)
                              apply (wpsimp wp: schedContextDonate_valid_objs'
                                                schedContextDonate_replies_of' schedContextDonate_reply_projs)
                             apply (fastforce split: if_split)
                            apply (clarsimp simp: pred_tcb_at'_def opt_map_red obj_at_simps pred_tcb_at_def)
                            apply (drule (1) pspace_relation_absD[OF _ state_relation_pspace_relation, where x=t])
                            apply (rename_tac tcb' sc')
                            apply (clarsimp simp: other_obj_relation_def tcb_relation_def)
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
                  apply (rule_tac Q="\<lambda>_. sc_replies_sc_at ((=) list) scp" in hoare_strengthen_post[rotated])
                   apply (clarsimp simp: sc_replies_sc_at_def obj_at_def)
                  apply (wpsimp wp: update_sched_context_sc_replies_update_tl)
                 apply (fold updateSchedContext_def)
                 apply (rule_tac Q="\<lambda>_. valid_objs' and valid_release_queue_iff
                                        and valid_queues and valid_queues'
                                        and ko_at' r' rp and sc_at' scp
                                        and (\<lambda>s. sym_refs (list_refs_of_replies' s))
                                        and st_tcb_at' ((=) (Structures_H.thread_state.BlockedOnReply (Some rp))) t
                                        and (\<lambda>s. \<forall>p'. scReplies_of s p' \<noteq> Some rp)
                                        and (\<lambda>s. \<forall>p'. replyPrevs_of s p' \<noteq> Some rp)
                                        and (\<lambda>s. tcbSCs_of s t = tcbsc)"
                        in hoare_strengthen_post[rotated])
                  apply (clarsimp split: if_split simp: valid_reply'_def opt_map_Some_eta_fold obj_at'_def)
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
               apply (clarsimp simp: valid_obj'_def  opt_map_red opt_map_Some_eta_fold)
               apply (intro conjI impI)
                   apply (fastforce simp: obj_at'_def opt_map_red opt_pred_def
                                          valid_sched_context'_def valid_obj'_def valid_reply'_def
                                          refillSize_def
                                   split: if_splits)
                  apply (fold fun_upd_def)
                  apply (clarsimp simp: obj_at'_def  opt_map_red ps_clear_upd objBits_simps
                                 split: if_split)
                 apply (fastforce dest!: sym_refs_replyNext_replyPrev_sym[where rp'=rp and rp=rp, THEN iffD2]
                                   simp: obj_at_simps opt_map_red)
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
   apply (clarsimp simp: obj_at_simps opt_map_red vs_all_heap_simps)
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
              and weak_valid_sched_action and active_scs_valid
              and st_tcb_at ((=) st) t and (\<lambda>s. sym_refs (state_refs_of s)))
             (valid_objs' and valid_release_queue_iff and valid_queues and valid_queues'
              and (\<lambda>s'. sym_refs (list_refs_of_replies' s')) and K (rp' = rp))
             (reply_remove t rp) (replyRemove rp' t)"
  (is "\<lbrakk> _ ; _ \<rbrakk> \<Longrightarrow> corres _ ?abs_guard ?conc_guard _ _")
  apply (rule corres_gen_asm2', simp only:)
  apply add_sym_refs
  apply (rule_tac Q="st_tcb_at' ((=) st') t" in corres_cross_add_guard)
   apply (fastforce dest!: st_tcb_at_coerce_concrete elim!: pred_tcb'_weakenE)
  apply (clarsimp simp: reply_remove_def replyRemove_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (clarsimp simp: sym_refs_asrt_def)
  apply (rule corres_guard_imp)
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
                apply (rule_tac Q="(\<lambda>s'. sc_with_reply' rp s' = sc_opt) and pspace_aligned'
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
                   apply (rule_tac Q="\<lambda>s. scReplies_of s scp = hd_opt (sc_replies sc) \<and> sc_at' scp s"
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
                                                  P'="valid_objs' and valid_release_queue_iff
                                                      and ko_at' reply' rp and sc_at' scp" and
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
   apply (fastforce dest!: st_tcb_at_valid_st2 simp: valid_tcb_state_def)
  apply (fastforce dest: tcb_in_valid_state' simp: valid_tcb_state'_def)
  done

lemma cancel_ipc_corres:
  "corres dc (invs and valid_ready_qs and tcb_at t) invs'
      (cancel_ipc t) (cancelIPC t)"
  apply add_sym_refs
  apply add_ready_qs_runnable
  apply (rule_tac Q="tcb_at' t" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: tcb_at_cross)
  apply (simp add: cancel_ipc_def cancelIPC_def Let_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (clarsimp simp: sym_refs_asrt_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getThreadState_corres])
      apply (rule corres_split[OF ])
         apply (rule threadset_corres; simp?)
         apply (clarsimp simp: tcb_relation_def fault_rel_optionation_def)
        apply (rule_tac P="invs and valid_ready_qs and st_tcb_at ((=) state) t" and
                        P'="invs' and st_tcb_at' ((=) statea) t" in corres_inst)
        apply (case_tac state, simp_all add: isTS_defs list_case_If gbep_ret')[1]
           apply (rule corres_guard_imp)
             apply (rename_tac epPtr reply pl)
             apply (rule_tac st = "Structures_A.thread_state.BlockedOnReceive epPtr reply pl"
                    in blocked_cancelIPC_corres[simplified])
               apply simp
              apply (clarsimp simp: thread_state_relation_def)
             apply simp+
            apply (clarsimp simp: invs_implies)
           apply (clarsimp simp: invs'_implies)
          apply (rule corres_guard_imp)
            apply (rename_tac epPtr data)
            apply (rule_tac st = "Structures_A.thread_state.BlockedOnSend epPtr data"
                   in blocked_cancelIPC_corres[where reply_opt=None, simplified])
             apply simp
            apply (clarsimp simp: thread_state_relation_def)
           apply simp
           apply (clarsimp simp: invs_implies)
          apply (clarsimp simp: invs'_implies)
         apply (rule corres_guard_imp)
           apply (rule replyRemoveTCB_corres)
          apply simp
          apply (clarsimp simp: thread_state_relation_def)
          apply (clarsimp simp: invs_implies)
         apply (clarsimp simp: invs'_implies)
        apply (rule corres_guard_imp)
          apply (rule cancelSignal_corres)
         apply simp+
       apply (wpsimp wp: thread_set_invs_fault_None thread_set_valid_ready_qs thread_set_no_change_tcb_state)
      apply (wpsimp wp: threadSet_pred_tcb_no_state threadSet_invs_trivial)+
     apply (wp gts_sp[where P="\<top>", simplified])+
    apply (rule hoare_strengthen_post)
     apply (rule gts_sp'[where P="\<top>"])
    apply (clarsimp elim!: pred_tcb'_weakenE)
   apply fastforce
  apply (clarsimp simp: inQ_def obj_at'_def valid_release_queue'_def
                 dest!: invs_valid_release_queue')
  done

declare cart_singleton_empty [simp]
declare cart_singleton_empty2[simp]

lemma sch_act_simple_not_t[simp]: "sch_act_simple s \<Longrightarrow> sch_act_not t s"
  by (clarsimp simp: sch_act_simple_def)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma cancelSignal_invs':
  "\<lbrace>invs' and st_tcb_at' (\<lambda>st. st = BlockedOnNotification ntfn) t\<rbrace>
   cancelSignal t ntfn
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  proof -
    have NIQ: "\<And>s. \<lbrakk> valid_queues s;
                     \<forall>d p. \<forall>t\<in>set (ksReadyQueues s (d, p)). st_tcb_at' runnable' t s;
                     st_tcb_at' (Not \<circ> runnable') t s \<rbrakk>
                     \<Longrightarrow> \<forall>d p. t \<notin> set (ksReadyQueues s (d,p))"
      apply (clarsimp simp add: pred_tcb_at'_def Invariants_H.valid_queues_def
                                valid_queues_no_bitmap_def)
      apply (drule spec | drule(1) bspec | clarsimp simp: obj_at'_def inQ_def)+
      done
    have NTFNSN: "\<And>ntfn ntfn'.
                    \<lbrace>\<lambda>s. sch_act_not (ksCurThread s) s \<rbrace> setNotification ntfn ntfn'
                    \<lbrace>\<lambda>_ s. sch_act_not (ksCurThread s) s\<rbrace>"
      apply (rule hoare_weaken_pre)
       apply wps
       apply (wp, simp)
      done
    show ?thesis
      apply (simp add: cancelSignal_def invs'_def Let_def valid_dom_schedule'_def)
      apply (rule hoare_seq_ext[OF _ stateAssert_sp])
      apply (wp valid_irq_node_lift sts_sch_act' irqs_masked_lift
                hoare_vcg_all_lift [OF set_ntfn'.ksReadyQueues]
                setThreadState_ct_not_inQ NTFNSN set_ntfn'.get_wp
                hoare_vcg_all_lift set_ntfn'.ksReadyQueues hoare_vcg_imp_lift'
              | simp add: valid_tcb_state'_def list_case_If split del: if_split)+
      apply (clarsimp simp: pred_tcb_at' ready_qs_runnable_def)
      apply (frule (1) NIQ)
       apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
      apply (case_tac "ntfnObj ko", simp_all add: isWaitingNtfn_def)
      apply (rule conjI)
       apply (clarsimp simp: valid_ntfn'_def)
       apply normalise_obj_at'
       apply (frule ko_at_valid_objs')
         apply (simp add: valid_pspace_valid_objs')
        apply (clarsimp simp: projectKO_opt_ntfn split: kernel_object.splits)
       apply (simp add: valid_obj'_def valid_ntfn'_def)
       apply (rule conjI, clarsimp simp: pred_tcb_at'_def obj_at'_def)
       apply (rule conjI, erule_tac rfs'="list_refs_of_replies' s" in delta_sym_refs)
         subgoal
         by (auto simp: symreftype_inverse' list_refs_of_replies'_def
                        get_refs_def2 opt_map_def
                 split: option.splits)
        subgoal
        by (auto simp: symreftype_inverse' list_refs_of_replies'_def
                       get_refs_def2 opt_map_def
                split: option.splits)
        apply (frule obj_at_valid_objs', clarsimp)
        apply (clarsimp simp:  valid_obj'_def valid_ntfn'_def)
        apply (frule st_tcb_at_state_refs_ofD')
        apply (frule ko_at_state_refs_ofD')
        apply (fastforce simp: get_refs_def elim!: if_live_state_refsE split: option.splits)
       apply (frule obj_at_valid_objs', clarsimp)
       apply (clarsimp simp:  valid_obj'_def valid_ntfn'_def)
       apply (rule conjI, clarsimp split: option.splits)
       apply (frule st_tcb_at_state_refs_ofD')
       apply (frule ko_at_state_refs_ofD')
       apply (rule conjI)
        apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
       apply (rule conjI)
        apply (clarsimp split: if_split_asm)
        apply (fastforce simp: list_refs_of_replies'_def opt_map_def o_def split: option.splits)
       apply (fastforce simp: get_refs_def elim!: if_live_state_refsE split: option.splits)
       done
  qed

lemma ep_redux_simps3:
  "ep_q_refs_of' (case xs of [] \<Rightarrow> IdleEP | y # ys \<Rightarrow> RecvEP (y # ys))
        = (set xs \<times> {EPRecv})"
  "ep_q_refs_of' (case xs of [] \<Rightarrow> IdleEP | y # ys \<Rightarrow> SendEP (y # ys))
        = (set xs \<times> {EPSend})"
  by (fastforce split: list.splits simp: valid_ep_def valid_ntfn_def)+

end

crunches cancelIPC
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
  and ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ntfn_at'[wp]: "ntfn_at' t"
  (wp: crunch_wps simp: crunch_simps)

crunches blockedCancelIPC
  for valid_queues[wp]: valid_queues
  and replyNexts_replyPrevs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s)"
  (wp: crunch_wps)

crunches cancelSignal, replyRemoveTCB
  for sch_act_wf[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  (wp: crunch_wps sts_sch_act')

lemma blockedCancelIPC_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> sch_act_not tptr s\<rbrace>
   blockedCancelIPC st tptr rptrOpt
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding blockedCancelIPC_def getBlockingObject_def epBlocked_def
  apply (wpsimp wp: hoare_vcg_imp_lift' getEndpoint_wp haskell_assert_wp sts_sch_act')
  done

lemma nonempty_epQueue_remove1_valid_ep':
  "\<lbrakk>valid_ep' ep s; remove1 tptr (epQueue ep) = x # xs; ep \<noteq> IdleEP\<rbrakk>
   \<Longrightarrow> valid_ep' (epQueue_update (\<lambda>_. x # xs) ep) s"
  by (case_tac ep; clarsimp simp: valid_ep'_def;
      metis (full_types) distinct.simps(2) distinct_remove1 list.set_intros(1)
                         list.set_intros(2) notin_set_remove1)

lemma blockedCancelIPC_valid_pspace'[wp]:
  "\<lbrace>valid_pspace' and st_tcb_at' ((=) st) tptr\<rbrace>
   blockedCancelIPC st tptr rptrOpt
   \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  supply opt_mapE[elim!]
  unfolding valid_pspace'_def blockedCancelIPC_def getBlockingObject_def
  apply (wpsimp wp: valid_mdb'_lift hoare_vcg_imp_lift getEndpoint_wp
                    hoare_vcg_all_lift sts'_valid_replies' replyUnlink_st_tcb_at'
              simp: valid_tcb_state'_def epBlocked_def)
  apply (rule ccontr, normalise_obj_at')
  apply (match premises in epQueue: "_ (valid_ep' ep s)" for ep s \<Rightarrow>
         \<open>rule meta_mp[rotated, where P="valid_ep' ep s"]\<close>)
   apply (drule(1) ep_ko_at_valid_objs_valid_ep')
   apply (case_tac "remove1 tptr (epQueue ko)"; clarsimp)
    apply (clarsimp simp: valid_ep'_def)
   apply (fastforce dest: nonempty_epQueue_remove1_valid_ep'[rotated])
  apply (case_tac "rptrOpt"; clarsimp simp: pred_tcb_at'_eq_commute)
   apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  apply (rename_tac rptr reply)
  apply (drule_tac rptr=rptr in valid_replies'D[simplified pred_tcb_at'_eq_commute])
   apply clarsimp
  apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  done

lemma cancelIPC_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> sch_act_not tptr s\<rbrace>
   cancelIPC tptr
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding cancelIPC_def
  apply (wpsimp wp: gts_wp' hoare_vcg_imp_lift' threadSet_sch_act hoare_vcg_all_lift
                    replyRemoveTCB_sch_act_wf)
  done

crunches getBlockingObject
  for inv: P

lemma blockedCancelIPC_if_live'[wp]:
  "blockedCancelIPC st tptr epptr \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  unfolding blockedCancelIPC_def getBlockingObject_def
  apply (wpsimp wp: getEndpoint_wp haskell_assert_wp)
  apply (clarsimp simp: if_live_then_nonz_cap'_def endpoint.disc_eq_case endpoint_live')
  done

lemma blockedCancelIPC_valid_idle':
  "\<lbrace>valid_idle' and (\<lambda>s. tptr \<noteq> ksIdleThread s)\<rbrace>
   blockedCancelIPC st tptr epptr
   \<lbrace>\<lambda>_. valid_idle'\<rbrace>"
  unfolding blockedCancelIPC_def getBlockingObject_def
  apply (wpsimp wp: getEndpoint_wp)
  done

crunches blockedCancelIPC
  for ct_not_inQ[wp]: ct_not_inQ
  and cur_tcb'[wp]: "cur_tcb'"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and valid_queues'[wp]: valid_queues'
  and valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'
  and untyped_ranges_zero'[wp]: "untyped_ranges_zero'"
  (wp: crunch_wps)

lemma blockedCancelIPC_invs':
  "\<lbrace>invs' and st_tcb_at' ((=) st) tptr\<rbrace>
   blockedCancelIPC st tptr rptrOpt
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (rule hoare_strengthen_pre_via_assert_backward[
                where E="obj_at' ((\<noteq>) IdleEP) (the (epBlocked st))
                         and K (\<exists>x. epBlocked st = Some x)"])
   apply (simp add: blockedCancelIPC_def getBlockingObject_def)
   apply (wpsimp wp: getEndpoint_wp)
   apply (clarsimp simp: obj_at'_def)
  unfolding invs'_def decompose_list_refs_of_replies' valid_dom_schedule'_def
  apply (wpsimp wp: valid_irq_node_lift typ_at_lifts
                    valid_irq_handlers_lift' valid_irq_states_lift' irqs_masked_lift
              simp: cteCaps_of_def pred_tcb_at'_def)
  done

lemma threadSet_fault_invs':
  "threadSet (tcbFault_update upd) t \<lbrace>invs'\<rbrace>"
  apply (wpsimp wp: threadSet_invs_trivial)
  apply (clarsimp simp: inQ_def)
  apply (rule conjI)
   apply clarsimp
  apply (frule invs_valid_release_queue')
  apply (clarsimp simp: valid_release_queue'_def obj_at'_def)
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
            hoare_drop_imp[where R="%rv s. P' rv" for P'])
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
  "\<lbrakk> \<And>t. \<lbrace>\<lambda>s. sa s \<noteq> SwitchToThread t\<rbrace> f \<lbrace>\<lambda>rv s. sa s \<noteq> SwitchToThread t\<rbrace>;
     \<And>t. \<lbrace>st_tcb_at' runnable' t\<rbrace> f \<lbrace>\<lambda>rv. st_tcb_at' runnable' t\<rbrace>;
     \<And>t. \<lbrace>tcb_in_cur_domain' t\<rbrace> f \<lbrace>\<lambda>rv. tcb_in_cur_domain' t\<rbrace> \<rbrakk>
       \<Longrightarrow> \<lbrace>\<lambda>s. weak_sch_act_wf (sa s) s\<rbrace> f \<lbrace>\<lambda>rv s. weak_sch_act_wf (sa s) s\<rbrace>"
  apply (simp only: weak_sch_act_wf_def imp_conv_disj)
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift hoare_vcg_conj_lift)
  apply simp_all
  done

crunches cancelSignal, setBoundNotification
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

crunches unbindNotification, bindNotification, unbindMaybeNotification
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

lemma cancelSignal_tcb_obj_at':
  "(\<And>tcb st qd. P (tcb\<lparr>tcbState := st, tcbQueued := qd\<rparr>) \<longleftrightarrow> P tcb)
     \<Longrightarrow> cancelSignal t word \<lbrace>obj_at' P t'\<rbrace>"
  apply (simp add: cancelSignal_def)
  apply (wpsimp wp: setThreadState_not_st getNotification_wp)
  done

crunches replyRemoveTCB, cancelSignal, getBlockingObject, blockedCancelIPC
  for obj_at'_only_st_qd_ft: "\<lambda>s. P (obj_at' (Q :: tcb \<Rightarrow> bool) t s)"
  (simp: crunch_simps pred_tcb_at'_def wp: crunch_wps)

(* FIXME: Proved outside of `crunch` because without the `[where P=P]` constraint, the
   postcondition unifies with the precondition in a wonderfully exponential way. VER-1337 *)
lemma cancelIPC_obj_at'_only_st_qd_ft:
  "\<lbrace>\<lambda>s. P (obj_at' Q t' s) \<and>
        (\<forall>upd tcb. Q (tcbState_update upd tcb) = Q tcb) \<and>
        (\<forall>upd tcb. Q (tcbQueued_update upd tcb) = Q tcb) \<and>
        (\<forall>upd tcb. Q (tcbFault_update upd tcb) = Q tcb)\<rbrace>
   cancelIPC t
   \<lbrace>\<lambda>_ s. P (obj_at' Q t' s)\<rbrace>"
  unfolding cancelIPC_def Let_def
  apply (wpsimp wp: scheduleTCB_obj_at'_only_st_qd_ft[where P=P]
                    threadSet_obj_at'_only_st_qd_ft[where P=P]
                    setThreadState_obj_at'_only_st_qd_ft[where P=P]
                    replyUnlink_obj_at'_only_st_qd_ft[where P=P]
                    getBlockingObject_obj_at'_only_st_qd_ft[where P=P]
                    replyRemoveTCB_obj_at'_only_st_qd_ft[where P=P]
                    blockedCancelIPC_obj_at'_only_st_qd_ft[where P=P]
                    cancelSignal_obj_at'_only_st_qd_ft[where P=P]
                    hoare_drop_imp)
  done

lemma cancelIPC_tcbDomain_obj_at':
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace> cancelIPC t \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  apply (wpsimp wp: cancelIPC_obj_at'_only_st_qd_ft)
  done

lemma (in delete_one_conc_pre) cancelIPC_tcb_in_cur_domain':
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> cancelIPC t \<lbrace>\<lambda>_. tcb_in_cur_domain' t'\<rbrace>"
  apply (simp add: tcb_in_cur_domain'_def)
  apply (rule hoare_pre)
   apply wps
   apply (wp cancelIPC_tcbDomain_obj_at' | simp)+
  done

text \<open>The suspend operation, significant as called from delete\<close>

lemma setBoundNotification_tcb_in_cur_domain'[wp]:
  "setBoundNotification st t \<lbrace>tcb_in_cur_domain' t'\<rbrace>"
  apply (simp add: tcb_in_cur_domain'_def)
  apply (rule hoare_pre)
   apply wps
  apply (wp setBoundNotification_not_ntfn | simp)+
  done

lemma sbn_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   setBoundNotification ntfn t
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp weak_sch_act_wf_lift)

lemma set_ep_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
     setEndpoint epptr ep
   \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (wp weak_sch_act_wf_lift)
  done

lemma setObject_ntfn_sa_unchanged[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
    setObject ptr (ntfn::Structures_H.notification)
   \<lbrace>\<lambda>rv s.  P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp | simp add: updateObject_default_def)+
  done

lemma setNotification_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
    setNotification ntfnptr ntfn
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (wp hoare_vcg_all_lift hoare_convert_imp hoare_vcg_conj_lift
         | simp add: weak_sch_act_wf_def st_tcb_at'_def tcb_in_cur_domain'_def)+
   apply wps
   apply (wpsimp simp: o_def)+
  done

lemmas ipccancel_weak_sch_act_wfs
    = weak_sch_act_wf_lift[OF _ setCTE_pred_tcb_at']

lemma tcbSchedDequeue_corres':
  "corres dc (tcb_at t and pspace_aligned and pspace_distinct)
             (tcb_at' t and valid_inQ_queues)
             (tcb_sched_action (tcb_sched_dequeue) t) (tcbSchedDequeue t)"
  apply (simp only: tcbSchedDequeue_def tcb_sched_action_def)
  apply (rule corres_symb_exec_r[OF _ _ threadGet_inv, where Q'="\<lambda>rv. tcb_at' t and valid_inQ_queues and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"])
    defer
    apply (wp threadGet_obj_at', simp, simp)
   apply (wp, simp)
  apply (case_tac queued)
   defer
   apply (simp add: unless_def when_def)
   apply (rule corres_no_failI)
    apply (wp)
   apply (clarsimp simp: in_monad thread_get_def get_tcb_def set_tcb_queue_def tcb_at_def
                         state_relation_def gets_the_def gets_def get_def return_def bind_def
                         assert_opt_def get_tcb_queue_def modify_def put_def)
   apply (prop_tac "t \<notin> set (ready_queues a (tcb_domain tcb) (tcb_priority tcb))")
    apply (force simp: tcb_sched_dequeue_def valid_inQ_queues_def
           ready_queues_relation_def obj_at'_def inQ_def project_inject)
   apply (simp add: ready_queues_relation_def cdt_relation_def)
  apply (simp add: unless_def when_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="(=)", OF threadGet_corres])
       apply (clarsimp simp: tcb_relation_def)
      apply (simp split del: if_split)
      apply (rule corres_split_eqr[OF threadGet_corres])
         apply (clarsimp simp: tcb_relation_def)
        apply (rule corres_split_eqr[OF getQueue_corres])
          apply (simp split del: if_split)
          apply (subst bind_return_unit, rule corres_split[where r'=dc])
             apply (simp add: tcb_sched_dequeue_def)
             apply (prove_prop \<open>(\<lambda>x. x \<noteq> t) = (\<noteq>) t\<close>, simp)
             apply (rule setQueue_corres)
            apply (rule corres_split_noop_rhs)
              apply (clarsimp, rule removeFromBitmap_corres_noop)
             apply (simp add: dc_def[symmetric])
             apply (rule threadSet_corres_noop, simp_all add: tcb_relation_def)[1]
            apply (wp | simp)+
  done

lemma setQueue_valid_inQ_queues:
  "\<lbrace>valid_inQ_queues and (\<lambda>s. \<forall>t \<in> set ts. obj_at' (inQ d p) t s)\<rbrace>
   setQueue d p ts
   \<lbrace>\<lambda>_. valid_inQ_queues\<rbrace>"
  apply (simp add: setQueue_def valid_inQ_queues_def)
  apply wp
  apply clarsimp
  done

lemma threadSet_valid_inQ_queues:
  "\<lbrace>valid_inQ_queues and (\<lambda>s. \<forall>d p. (\<exists>tcb. (inQ d p tcb) \<and> \<not>(inQ d p (f tcb)))
                        \<longrightarrow> obj_at' (\<lambda>tcb. (inQ d p tcb) \<and> \<not>(inQ d p (f tcb))) t s
                        \<longrightarrow> t \<notin> set (ksReadyQueues s (d, p)))\<rbrace>
     threadSet f t
   \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
  apply (simp add: threadSet_def)
  apply wp
   apply (simp add: valid_inQ_queues_def pred_tcb_at'_def)
   apply (wp hoare_Ball_helper
             hoare_vcg_all_lift
             setObject_tcb_strongest)[1]
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: valid_inQ_queues_def pred_tcb_at'_def)
  apply (clarsimp simp: obj_at'_def)
  apply (fastforce)
  done

(* reorder the threadSet before the setQueue, useful for lemmas that don't refer to bitmap *)
lemma setQueue_after_addToBitmap:
  "(setQueue d p q >>= (\<lambda>rv. (when P (addToBitmap d p)) >>= (\<lambda>rv. threadSet f t))) =
   (when P (addToBitmap d p) >>= (\<lambda>rv. (threadSet f t) >>= (\<lambda>rv. setQueue d p q)))"
  apply (case_tac P, simp_all)
   prefer 2
   apply (simp add: setQueue_after)
  apply (simp add: setQueue_def when_def)
  apply (subst oblivious_modify_swap)
  apply (simp add: threadSet_def getObject_def setObject_def readObject_def
                   loadObject_default_def bitmap_fun_defs gets_the_def omonad_defs
                   split_def projectKO_def alignCheck_assert read_magnitudeCheck_assert
                   magnitudeCheck_assert updateObject_default_def obind_def)
  apply (intro oblivious_bind, simp_all split: option.splits)
  apply (clarsimp simp: bind_assoc)
  done

lemma tcbSchedEnqueue_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_. valid_inQ_queues\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def setQueue_after_addToBitmap)
  apply (rule hoare_pre)
   apply (rule_tac B="\<lambda>rv. valid_inQ_queues and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"
                in hoare_seq_ext)
    apply (rename_tac queued)
    apply (case_tac queued, simp_all add: unless_def)[1]
     apply (wp setQueue_valid_inQ_queues threadSet_valid_inQ_queues threadGet_wp
               hoare_vcg_const_Ball_lift
            | simp add: inQ_def bitmap_fun_defs
            | fastforce simp: valid_inQ_queues_def inQ_def obj_at'_def)+
  done

 (* prevents wp from splitting on the when; stronger technique than hoare_when_weak_wp
    FIXME: possible to replace with hoare_when_weak_wp?
 *)
definition
  "removeFromBitmap_conceal d p q t \<equiv> when (null [x\<leftarrow>q . x \<noteq> t]) (removeFromBitmap d p)"

crunches rescheduleRequired, scheduleTCB
  for valid_inQ_queues[wp]: valid_inQ_queues
  (wp: crunch_wps)

lemma sts_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
  by (wpsimp simp: setThreadState_def inQ_def wp: threadSet_valid_inQ_queues)

lemma updateObject_ep_inv:
  "\<lbrace>P\<rbrace> updateObject (obj::endpoint) ko p q n \<lbrace>\<lambda>rv. P\<rbrace>"
  by simp (rule updateObject_default_inv)

lemma sbn_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_valid_inQ_queues [THEN hoare_strengthen_post])
   apply (clarsimp simp: sch_act_simple_def Invariants_H.valid_queues_def inQ_def)+
  done

crunch valid_inQ_queues[wp]: cancelSignal valid_inQ_queues
  (simp: updateObject_default_inv crunch_simps wp: crunch_wps)

crunches tcbSchedEnqueue
  for inQ[wp]: "\<lambda>s. obj_at' (inQ d p) t s"
  (wp: crunch_wps simp: crunch_simps)

lemma rescheduleRequired_inQ[wp]:
  "rescheduleRequired \<lbrace>\<lambda>s. obj_at' (inQ d p) t s\<rbrace>"
  apply (clarsimp simp: rescheduleRequired_def)
  apply (wpsimp wp: isSchedulable_wp)
  apply (clarsimp simp: obj_at'_def inQ_def)
  done

crunches scheduleTCB
  for inQ[wp]: "\<lambda>s. obj_at' (inQ d p) t s"
  (wp: crunch_wps simp: crunch_simps)

lemma setThreadState_inQ[wp]:
  "setThreadState ts tptr \<lbrace>\<lambda>s. obj_at' (inQ d p) t s\<rbrace>"
  apply (clarsimp simp: setThreadState_def)
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: obj_at'_def inQ_def objBitsKO_def)
  done

lemma replyUnlink_valid_inQ_queues[wp]:
  "replyUnlink replyPtr tcbPtr \<lbrace>valid_inQ_queues\<rbrace>"
  apply (clarsimp simp: replyUnlink_def updateReply_def)
  apply (wpsimp wp: set_reply'.set_wp gts_wp')
  apply (fastforce simp: valid_inQ_queues_def obj_at'_def)
  done

lemma replyRemoveTCB_valid_inQ_queues[wp]:
  "replyRemoveTCB tptr \<lbrace>valid_inQ_queues\<rbrace>"
  unfolding replyRemoveTCB_def updateReply_def
  apply clarsimp
  apply (rule hoare_seq_ext_skip, (solves \<open>wpsimp\<close>)?)+
  apply wpsimp
  done

lemma cancelIPC_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> cancelIPC t \<lbrace>\<lambda>_. valid_inQ_queues\<rbrace>"
  unfolding cancelIPC_def Let_def blockedCancelIPC_def getBlockingObject_def
  apply (wpsimp wp: hoare_drop_imps threadSet_valid_inQ_queues)
  apply (clarsimp simp: valid_inQ_queues_def inQ_def)
  done

lemma valid_queues_inQ_queues:
  "Invariants_H.valid_queues s \<Longrightarrow> valid_inQ_queues s"
  by (force simp: Invariants_H.valid_queues_def valid_inQ_queues_def obj_at'_def
                  valid_queues_no_bitmap_def)

lemma asUser_tcbQueued_inv[wp]:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbQueued tcb)) t'\<rbrace> asUser t m \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbQueued tcb)) t'\<rbrace>"
  apply (simp add: asUser_def tcb_in_cur_domain'_def threadGet_def)
  apply (wp threadSet_obj_at'_strongish getObject_tcb_wp | wpc | simp | clarsimp simp: obj_at'_def)+
  done

lemma asUser_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> asUser t f \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
  unfolding valid_inQ_queues_def Ball_def
  apply (wpsimp wp: hoare_vcg_all_lift)
    defer
   apply assumption
  apply (simp add: inQ_def[abs_def] obj_at'_conj)
  apply (rule hoare_convert_imp)
   apply (wp asUser_ksQ)
  apply wp
  done

lemma (in delete_one) suspend_corres:
  "corres dc (einvs and tcb_at t) (invs' and tcb_at' t)
             (SchedContext_A.suspend t) (ThreadDecls_H.suspend t)"
  apply (simp add: SchedContext_A.suspend_def Thread_H.suspend_def)
  apply add_sym_refs
  apply (rule corres_stateAssert_add_assertion)
   prefer 2
   apply (clarsimp simp: sym_refs_asrt_def)
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
          apply (rule corres_split[OF setThreadState_corres], simp)
            apply (rule corres_split[OF tcbSchedDequeue_corres'])
              apply (rule corres_split[OF tcbReleaseRemove_corres], simp)
                apply (rule schedContextCancelYieldTo_corres)
               apply wpsimp+
          apply (wpsimp simp: update_restart_pc_def updateRestartPC_def)
          apply (rule hoare_post_imp[where Q = "\<lambda>rv s. invs s \<and> tcb_at t s"], fastforce)
          apply wp
         apply wpsimp
        apply (rule hoare_post_imp[where Q = "\<lambda>rv s. invs' s \<and> tcb_at' t s"])
         apply (fastforce simp: invs'_def dest!: valid_queues_inQ_queues)
        apply wp
         apply (clarsimp simp: updateRestartPC_def)
         apply wpsimp
        apply wpsimp
       apply (wpsimp wp: gts_wp)
      apply (wpsimp wp: gts_wp')
     apply (rule hoare_post_imp[where Q = "\<lambda>rv s. invs s \<and> tcb_at t s"], fastforce)
     apply wpsimp
    apply (rule hoare_post_imp[where Q = "\<lambda>rv s. invs' s \<and> tcb_at' t s"], fastforce)
    apply (wpsimp wp: hoare_drop_imps)+
  done

lemma (in delete_one) prepareThreadDelete_corres:
  "corres dc \<top> \<top>
          (prepare_thread_delete t) (ArchRetypeDecls_H.RISCV64_H.prepareThreadDelete t)"
  by (simp add: RISCV64_A.prepare_thread_delete_def RISCV64_H.prepareThreadDelete_def)

lemma rescheduleRequired_oa_queued:
  "\<lbrace> (\<lambda>s. P (obj_at' (\<lambda>tcb. Q (tcbQueued tcb) (tcbDomain tcb) (tcbPriority tcb)) t' s)) and sch_act_simple\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_ s. P (obj_at' (\<lambda>tcb. Q (tcbQueued tcb) (tcbDomain tcb) (tcbPriority tcb)) t' s)\<rbrace>"
  (is "\<lbrace>?OAQ t' p and sch_act_simple\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: rescheduleRequired_def sch_act_simple_def)
  apply (rule_tac B="\<lambda>rv s. (rv = ResumeCurrentThread \<or> rv = ChooseNewThread)
                       \<and> ?OAQ t' p s" in hoare_seq_ext)
   including no_pre
   apply (wp | clarsimp)+
   apply (case_tac x)
     apply (wp | clarsimp)+
  done


(* FIXME: rename uses of setThreadState_oa_queued; the "_queued" suffix doesn't make sense
   any more. VER-1332 *)
lemmas setThreadState_oa_queued = setThreadState_oa

lemma setBoundNotification_oa_queued:
  "\<lbrace>\<lambda>s. P' (obj_at' (\<lambda>tcb. P (tcbQueued tcb) (tcbDomain tcb) (tcbPriority tcb)) t' s) \<rbrace>
    setBoundNotification ntfn t
   \<lbrace>\<lambda>_ s. P' (obj_at' (\<lambda>tcb. P (tcbQueued tcb) (tcbDomain tcb) (tcbPriority tcb)) t' s) \<rbrace>"
  (is "\<lbrace>\<lambda>s. P' (?Q P s)\<rbrace> _ \<lbrace>\<lambda>_ s. P' (?Q P s)\<rbrace>")
  proof (rule P_bool_lift [where P=P'])
    show pos:
      "\<And>R. \<lbrace> ?Q R \<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>_. ?Q R \<rbrace>"
      apply (simp add: setBoundNotification_def)
      apply (wp threadSet_obj_at'_strongish)
      apply (clarsimp)
      done
    show "\<lbrace>\<lambda>s. \<not> ?Q P s\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>_ s. \<not> ?Q P s\<rbrace>"
      by (simp add: not_obj_at' comp_def, wp hoare_convert_imp pos)
  qed

lemma tcbSchedDequeue_ksQ_distinct[wp]:
  "\<lbrace>\<lambda>s. distinct (ksReadyQueues s p)\<rbrace>
    tcbSchedDequeue t
   \<lbrace>\<lambda>_ s. distinct (ksReadyQueues s p)\<rbrace>"
  apply (simp add: tcbSchedDequeue_def  removeFromBitmap_conceal_def[symmetric])
  apply wp
        apply (rule hoare_pre_post, assumption)
        apply (clarsimp simp: bitmap_fun_defs removeFromBitmap_conceal_def, wp, clarsimp)
       apply wp+
     apply (rule_tac Q="\<lambda>_ s. distinct (ksReadyQueues s p)" in hoare_post_imp)
      apply (clarsimp | wp)+
  done

lemma tcbSchedDequeue_t_notksQ:
  "\<lbrace>\<lambda>s. t \<in> set (ksReadyQueues s (d, p)) \<longrightarrow>
           obj_at' (\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t s\<rbrace>
    tcbSchedDequeue t
   \<lbrace>\<lambda>_ s. t \<notin> set (ksReadyQueues s (d, p))\<rbrace>"
  apply (rule_tac Q="(\<lambda>s. t \<notin> set (ksReadyQueues s (d, p)))
                            or obj_at'(\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t"
               in hoare_pre_imp, clarsimp)
  apply (rule hoare_pre_disj)
   apply (wp tcbSchedDequeue_notksQ)[1]
  apply (simp add: tcbSchedDequeue_def  removeFromBitmap_conceal_def[symmetric])
  apply wp
        apply (rule hoare_pre_post, assumption)
        apply (clarsimp simp: bitmap_fun_defs removeFromBitmap_conceal_def, wp, clarsimp)
       apply (wp threadGet_wp)+
  apply (auto simp: obj_at'_real_def ko_wp_at'_def)
  done

lemma asUser_sch_act_simple[wp]:
  "\<lbrace>sch_act_simple\<rbrace> asUser s t \<lbrace>\<lambda>_. sch_act_simple\<rbrace>"
  unfolding sch_act_simple_def
  apply (rule asUser_nosch)
  done

crunches updateRestartPC
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P tcbPtr"
  and invs'[wp]: invs'

lemma (in delete_one_conc) suspend_invs'[wp]:
  "suspend t \<lbrace>invs'\<rbrace>"
  apply (simp add: suspend_def updateRestartPC_def)
  apply (wpsimp wp: tcbReleaseRemove_invs' schedContextCancelYieldTo_invs' sts_invs_minor' gts_wp')
    apply (rule_tac Q="\<lambda>_. invs' and st_tcb_at' simple' t" in hoare_post_imp)
     apply (fastforce elim: pred_tcb'_weakenE)
    apply wpsimp+
  done

lemma (in delete_one_conc) suspend_objs':
  "\<lbrace>invs' and tcb_at' t\<rbrace>
   suspend t \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (rule_tac Q="\<lambda>_. invs'" in hoare_strengthen_post)
   apply (wp suspend_invs')
   apply fastforce+
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

crunches cancelSignal, cleanReply
  for valid_queues[wp]: valid_queues
  (simp: crunch_simps wp: crunch_wps)

lemma tcbFault_update_valid_queues:
  "\<lbrakk>ko_at' tcb t s; valid_queues s\<rbrakk>
   \<Longrightarrow> valid_queues (s\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbFault_update Map.empty tcb))\<rparr>)"
   by (fastforce simp: valid_queues_def valid_queues_no_bitmap_def valid_bitmapQ_def bitmapQ_def
                       bitmapQ_no_L2_orphans_def bitmapQ_no_L1_orphans_def obj_at'_def
                        inQ_def objBitsKO_def)

lemma cancelIPC_queues[wp]:
  "cancelIPC t \<lbrace>valid_queues\<rbrace>"
  apply (simp add: cancelIPC_def Let_def)
  apply (wpsimp wp: threadSet_wp tcbFault_update_valid_queues hoare_drop_imps gts_wp')
  apply (fastforce intro: tcbFault_update_valid_queues)
  done

lemma rescheduleRequired_sch_act_simple_not_queued:
  "\<lbrace>\<lambda>s. t' \<notin> set (ksReadyQueues s (d, p)) \<and> sch_act_simple s\<rbrace>
   rescheduleRequired
   \<lbrace>\<lambda>_ s. t' \<notin> set (ksReadyQueues s (d, p))\<rbrace>"
  apply (clarsimp simp: rescheduleRequired_def getSchedulerAction_def sch_act_simple_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp?)
    apply wpsimp
   apply wpsimp
  apply (fastforce simp: pred_conj_def valid_def)
  done

lemma scheduleTCB_sch_act_simple_not_queued:
  "\<lbrace>\<lambda>s. t' \<notin> set (ksReadyQueues s (d, p)) \<and> sch_act_simple s\<rbrace>
   scheduleTCB tcbPtr
   \<lbrace>\<lambda>_ s. t' \<notin> set (ksReadyQueues s (d, p))\<rbrace>"
  apply (wpsimp simp: scheduleTCB_def wp: rescheduleRequired_sch_act_simple_not_queued isSchedulable_wp)
  done

lemma sts_ksQ_oaQ:
  "\<lbrace>Invariants_H.valid_queues\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. t \<in> set (ksReadyQueues s (d, p)) \<longrightarrow>
           obj_at' (\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t s\<rbrace>"
  (is "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_. ?POST\<rbrace>")
  proof -
    have RR: "\<lbrace>sch_act_simple and ?POST\<rbrace> rescheduleRequired \<lbrace>\<lambda>_. ?POST\<rbrace>"
      apply (simp add: rescheduleRequired_def)
      apply (wp)
        apply (clarsimp)
       apply (rule_tac
                Q="(\<lambda>s. action = ResumeCurrentThread \<or> action = ChooseNewThread) and ?POST"
                                                               in hoare_pre_imp, assumption)
       apply (case_tac action)
         apply (clarsimp)+
      apply (wp)
      apply (clarsimp simp: sch_act_simple_def)
      done
    show ?thesis
      apply (simp add: setThreadState_def scheduleTCB_def getSchedulerAction_def)
      apply (wpsimp wp: RR isSchedulable_wp)
       apply (rule_tac Q="\<lambda>_. ?POST" in hoare_post_imp)
        apply (clarsimp simp add: sch_act_simple_def)
       apply (wp hoare_convert_imp)
      apply (clarsimp simp: Invariants_H.valid_queues_def valid_queues_no_bitmap_def)
      apply (fastforce dest: bspec elim!: obj_at'_weakenE simp: inQ_def)
      done
  qed

crunches schedContextCancelYieldTo
  for not_queued[wp]: "\<lambda>s. t' \<notin> set (ksReadyQueues s (d, p))"
  (wp: crunch_wps simp: crunch_simps)

lemma (in delete_one_conc_pre) suspend_nonq:
  "\<lbrace>Invariants_H.valid_queues and K (t = t')\<rbrace>
   suspend t
   \<lbrace>\<lambda>_ s. \<forall>d p. t' \<notin> set (ksReadyQueues s (d, p))\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: suspend_def unless_def)
  unfolding updateRestartPC_def
  apply (wpsimp wp: hoare_allI tcbSchedDequeue_t_notksQ sts_ksQ_oaQ hoare_vcg_imp_lift
                    hoare_disjI2[where R="\<lambda>_. valid_queues"])
  done

lemma suspend_makes_inactive:
  "\<lbrace>K (t = t')\<rbrace> suspend t \<lbrace>\<lambda>rv. st_tcb_at' ((=) Inactive) t'\<rbrace>"
  apply (cases "t = t'", simp_all)
  apply (simp add: suspend_def unless_def)
  apply (wp threadSet_pred_tcb_no_state setThreadState_st_tcb | simp)+
  done

lemma tcbSchedEnqueue_sch_act_not_ct[wp]:
  "\<lbrace>\<lambda>s. sch_act_not (ksCurThread s) s\<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_ s. sch_act_not (ksCurThread s) s\<rbrace>"
  by (rule hoare_weaken_pre, wps tcbSchedEnqueue_ct', wp, simp)

lemma sts_sch_act_not_ct[wp]:
  "\<lbrace>\<lambda>s. sch_act_not (ksCurThread s) s\<rbrace>
   setThreadState st t \<lbrace>\<lambda>_ s. sch_act_not (ksCurThread s) s\<rbrace>"
  by (rule hoare_weaken_pre, wps tcbSchedEnqueue_ct', wp, simp)

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

crunches setThreadState
  for valid_refills'[wp]: "valid_refills' scp"

crunches ifCondRefillUnblockCheck
  for valid_objs'[wp]: valid_objs'
  and valid_tcbs'[wp]: valid_tcbs'
  (wp: hoare_vcg_if_lift2 crunch_wps simp: crunch_simps)

lemma restart_thread_if_no_fault_corres:
  "corres dc (valid_sched_action and tcb_at t and pspace_aligned and pspace_distinct
              and valid_objs and active_scs_valid and current_time_bounded)
             (valid_queues and valid_queues' and valid_release_queue_iff and valid_objs')
             (restart_thread_if_no_fault t)
             (restartThreadIfNoFault t)"
    (is "corres _ _ ?conc_guard _ _")
  apply (rule corres_cross_over_guard[where Q="?conc_guard and tcb_at' t"])
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
          apply (rule_tac Q="\<lambda>scopt s. case_option True (\<lambda>p. sc_at p s) scopt \<and>
                                       tcb_at t s \<and> valid_sched_action s \<and>
                                       pspace_aligned s \<and> pspace_distinct s \<and> valid_objs s \<and>
                                       active_scs_valid s \<and> current_time_bounded s"
                 in hoare_strengthen_post[rotated])
           apply (fastforce split: option.splits
                             simp: obj_at_def is_sc_obj opt_map_red opt_pred_def)
          apply (wpsimp wp: thread_get_wp' simp: get_tcb_obj_ref_def)
         apply (clarsimp simp: bool.case_eq_if option.case_eq_if)
         apply (wpsimp wp: threadGet_wp)
        apply (rule_tac Q="\<lambda>_ s. tcb_at t s \<and>
                                 valid_sched_action s \<and>
                                 pspace_aligned s \<and> pspace_distinct s \<and> valid_objs s \<and>
                                 active_scs_valid s \<and> current_time_bounded s"
               in hoare_strengthen_post[rotated])
         apply (fastforce dest: valid_objs_ko_at
                          simp: valid_bound_obj_def valid_obj_def valid_tcb_def)
        apply (wpsimp wp: sts_typ_ats set_thread_state_valid_sched_action)
       apply (rule hoare_strengthen_post[where Q="\<lambda>_ s. tcb_at' t s \<and> valid_objs' s
                                                      \<and> valid_release_queue_iff s
                                                      \<and> valid_queues s \<and> valid_queues' s", rotated])
        apply (clarsimp simp: obj_at_simps)
       apply (wpsimp wp: sts_st_tcb_at'_cases)
      apply (rule setThreadState_corres)
      apply clarsimp
     apply (wpsimp wp: thread_get_wp threadGet_wp)+
   apply (clarsimp simp: obj_at_def is_tcb_def)
   apply (rename_tac ko, case_tac ko; clarsimp)
  apply (clarsimp simp: obj_at'_def  valid_tcb_state'_def)
  done

crunches possibleSwitchTo
  for sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"

global_interpretation possibleSwitchTo: typ_at_all_props' "possibleSwitchTo target"
  by typ_at_props'

crunches ifCondRefillUnblockCheck
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P p"
  and weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  and cur_tcb'[wp]: cur_tcb'
  (simp: crunch_simps wp: whileLoop_wp)

lemma cancelAllIPC_loop_body_st_tcb_at'_other:
  "\<lbrace>\<lambda>s. st_tcb_at' P t' s \<and> tcb_at' t' s \<and> t' \<noteq> t\<rbrace>
   cancelAllIPC_loop_body t
   \<lbrace>\<lambda>_. st_tcb_at' P t'\<rbrace>"
  apply (clarsimp simp: cancelAllIPC_loop_body_def restartThreadIfNoFault_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip, wpsimp wp: replyUnlink_st_tcb_at')
  apply (wpsimp wp: threadGet_wp)
     apply (rule hoare_strengthen_post[where Q="\<lambda>_. st_tcb_at' P t'", rotated])
      apply (clarsimp simp: obj_at'_def)
     apply (wpsimp wp: sts_st_tcb_at'_cases threadGet_wp)+
  apply (clarsimp simp: obj_at'_def)
  done

lemma cancelAllIPC_loop_body_weak_sch_act_wf:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<and> tcb_at' t s \<and> st_tcb_at' (not runnable') t s\<rbrace>
   cancelAllIPC_loop_body t
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: cancelAllIPC_loop_body_def restartThreadIfNoFault_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip, wpsimp wp: replyUnlink_st_tcb_at')
  apply (wpsimp wp: sts_st_tcb_at'_cases hoare_drop_imps)
  apply (clarsimp simp: weak_sch_act_wf_def pred_neg_def st_tcb_at'_def obj_at'_def)
  done

crunches cancelAllIPC_loop_body
  for valid_queues'[wp]: valid_queues'
  and valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'
  and valid_objs'[wp]: valid_objs'
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (simp: valid_tcb_state'_def crunch_simps wp: whileLoop_wp ignore: updateSchedContext)

global_interpretation cancelAllIPC_loop_body: typ_at_all_props' "cancelAllIPC_loop_body t"
  by typ_at_props'

lemma cancelAllIPC_loop_body_valid_queues:
  "\<lbrace>\<lambda>s. valid_queues s \<and> valid_tcbs' s\<rbrace>
   cancelAllIPC_loop_body t
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  unfolding cancelAllIPC_loop_body_def restartThreadIfNoFault_def
  apply (wpsimp wp: sts_valid_queues sts_st_tcb_at'_cases hoare_drop_imps)
  done

lemma cancelAllIPC_corres_helper:
  "distinct list \<Longrightarrow>
   corres dc
          ((\<lambda>s. \<forall>t \<in> set list. blocked_on_send_recv_tcb_at t s \<and> t \<noteq> idle_thread s
                               \<and> reply_unlink_ts_pred t s)
            and (valid_sched and valid_objs and pspace_aligned and pspace_distinct
                 and current_time_bounded and (\<lambda>s. heap_refs_inv (tcb_scps_of s) (sc_tcbs_of s))))
          ((\<lambda>s. \<forall>t \<in> set list. tcb_at' t s)
            and (valid_queues and valid_queues' and valid_objs' and valid_release_queue_iff))
     (mapM_x cancel_all_ipc_loop_body list)
     (mapM_x cancelAllIPC_loop_body list)"
  unfolding cancel_all_ipc_loop_body_def cancelAllIPC_loop_body_def
  apply (rule_tac S="{t. (fst t = snd t) \<and> fst t \<in> set list}" in corres_mapM_x_scheme)
          apply clarsimp
          apply (rename_tac t)
          apply (rule corres_guard_imp)
            apply (rule corres_split[OF getThreadState_corres], rename_tac st st')
              apply (rule_tac P="\<lambda>s. blocked_on_send_recv_tcb_at t s \<and> t \<noteq> idle_thread s
                                     \<and> reply_unlink_ts_pred t s \<and> valid_sched s \<and> valid_objs s
                                     \<and> pspace_aligned s \<and> pspace_distinct s
                                     \<and> st_tcb_at ((=) st) t s \<and> current_time_bounded s"
                          and P'="\<lambda>s. valid_queues s \<and> valid_queues' s \<and> valid_objs' s
                                      \<and> valid_release_queue_iff s"
                           in corres_inst)
              apply (case_tac "\<exists>ep r_opt pl.
                                st = Structures_A.thread_state.BlockedOnReceive ep r_opt pl")
               apply (clarsimp simp: when_def split: option.splits)
               apply (intro conjI impI allI; clarsimp simp: isReceive_def)
                apply (corresKsimp corres: restart_thread_if_no_fault_corres)
                apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb valid_sched_def)
               apply (rule corres_guard_imp)
                 apply (rule corres_split[OF replyUnlinkTcb_corres])
                    apply (rule corres_guard_imp)
                      apply (rule restart_thread_if_no_fault_corres)
                     apply simp
                    apply simp
                  apply (wpsimp wp: reply_unlink_tcb_valid_sched_action)
                 apply wpsimp
                apply (fastforce simp: vs_all_heap_simps pred_tcb_at_def obj_at_def
                                       reply_unlink_ts_pred_def)
               apply clarsimp
              apply (prop_tac "\<not> isReceive st'")
               apply (case_tac st; clarsimp simp: isReceive_def)
              apply (case_tac st;
                     clarsimp simp: isReceive_def;
                     (corresKsimp corres: restart_thread_if_no_fault_corres,
                      fastforce simp: obj_at_def))
             apply (wpsimp wp: gts_wp)
            apply (wpsimp wp: gts_wp')
           apply (clarsimp simp: vs_all_heap_simps obj_at_def is_tcb_def)
          apply clarsimp
         apply (fold cancel_all_ipc_loop_body_def)
         apply (intro hoare_vcg_conj_lift_pre_fix;
                (solves \<open>wpsimp wp: gts_wp simp: cancel_all_ipc_loop_body_def\<close>)?)
          apply (wpsimp wp: restart_thread_if_no_fault_tcb_sts_of_other
                            reply_unlink_tcb_tcb_sts_of_other gts_wp
                      simp: cancel_all_ipc_loop_body_def)
         apply (wpsimp wp: cancel_all_ipc_loop_body_reply_unlink_ts_pred_other)
        apply (wpsimp simp: restartThreadIfNoFault_def)
       apply (wpsimp wp: cancel_all_ipc_loop_body_valid_sched gts_wp
                   simp: cancel_all_ipc_loop_body_def)
      apply (fold cancelAllIPC_loop_body_def)
      apply (wpsimp wp: cancelAllIPC_loop_body_weak_sch_act_wf cancelAllIPC_loop_body_valid_queues)
     apply fastforce+
  done

lemmas reply_unlink_tcb_typ_at_lifts[wp] = abs_typ_at_lifts[OF reply_unlink_tcb_typ_at]

lemma in_send_ep_queue_TCBBlockedSend:
  "\<lbrakk>kheap s epptr = Some (Endpoint (Structures_A.SendEP queue)); t \<in> set queue; invs s\<rbrakk>
   \<Longrightarrow> (epptr, TCBBlockedSend) \<in> state_refs_of s t"
  apply (prop_tac "valid_ep (Structures_A.SendEP queue) s")
   apply (fastforce simp: valid_objs_def valid_obj_def dest!: invs_valid_objs)
  apply (clarsimp simp: state_refs_of_def valid_ep_def split: option.splits)
  apply (intro conjI impI allI; (fastforce simp: obj_at_def)?)
  apply (prop_tac "(t, EPSend) \<in> state_refs_of s epptr", clarsimp simp: state_refs_of_def)
  apply (clarsimp simp: sym_refs_def dest!: invs_sym_refs)
  apply (fastforce simp: state_refs_of_def)
  done

lemma cancelAllIPC_corres:
  "corres dc (invs and valid_sched and ep_at ep_ptr and current_time_bounded)
             (invs' and ep_at' ep_ptr)
             (cancel_all_ipc ep_ptr) (cancelAllIPC ep_ptr)"
proof -
  have P:
    "\<And>list. distinct list \<Longrightarrow>
         corres dc
          ((\<lambda>s. \<forall>t \<in> set list. blocked_on_send_recv_tcb_at t s \<and> t \<noteq> idle_thread s
                               \<and> reply_unlink_ts_pred t s)
            and (valid_sched and valid_objs and pspace_aligned and pspace_distinct and ep_at ep_ptr
                 and current_time_bounded and (\<lambda>s. heap_refs_inv (tcb_scps_of s) (sc_tcbs_of s))))
          ((\<lambda>s. \<forall>t \<in> set list. tcb_at' t s)
            and (valid_queues and valid_queues' and valid_objs' and valid_release_queue_iff
                 and ep_at' ep_ptr))
     (do set_endpoint ep_ptr Structures_A.IdleEP;
         mapM_x cancel_all_ipc_loop_body list;
         reschedule_required
      od)
     (do setEndpoint ep_ptr IdleEP;
         mapM_x cancelAllIPC_loop_body list;
         rescheduleRequired
     od)" (is "\<And>list. _ \<Longrightarrow> corres _ (?abs_guard list) (?conc_guard list) _ _")
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF setEndpoint_corres])
         apply (simp add: ep_relation_def)
        apply clarsimp
        apply (rule corres_split)
           apply (erule cancelAllIPC_corres_helper)
          apply (rule rescheduleRequired_corres)
         apply (rule_tac Q="?abs_guard list" in hoare_weaken_pre)
          apply (rule hoare_strengthen_post)
           apply (rule ball_mapM_x_scheme)
             apply (intro hoare_vcg_conj_lift_pre_fix;
                    (solves \<open>wpsimp wp: gts_wp simp: cancel_all_ipc_loop_body_def\<close>)?)
              apply (wpsimp wp: restart_thread_if_no_fault_tcb_sts_of_other
                                reply_unlink_tcb_tcb_sts_of_other gts_wp
                          simp: cancel_all_ipc_loop_body_def)
             apply (wpsimp wp: cancel_all_ipc_loop_body_reply_unlink_ts_pred_other)
            apply (wpsimp wp: cancel_all_ipc_loop_body_valid_sched gts_wp
                        simp: cancel_all_ipc_loop_body_def)
           apply simp
          apply fastforce
         apply simp
        apply (rule_tac Q="?conc_guard list" in hoare_weaken_pre)
         apply (rule hoare_strengthen_post)
          apply (rule ball_mapM_x_scheme)
            apply (wpsimp wp: cancelAllIPC_loop_body_st_tcb_at'_other)
           apply (wpsimp wp: cancelAllIPC_loop_body_weak_sch_act_wf
                             cancelAllIPC_loop_body_valid_queues
                             cancelAllIPC_loop_body_st_tcb_at'_other)
          apply (simp add: valid_objs'_valid_tcbs')+
       apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_const_Ball_lift hoare_vcg_imp_lift'
                   simp: reply_unlink_ts_pred_def)+
     apply (clarsimp simp: valid_ep_def)
    apply (clarsimp simp: valid_ep'_def)
    done

  show ?thesis
    apply (clarsimp simp: cancel_all_ipc_def[folded cancel_all_ipc_loop_body_def]
                          cancelAllIPC_def[folded restartThreadIfNoFault_def
                                           , folded cancelAllIPC_loop_body_def])
    apply (subst forM_x_def fun_app_def)+
    apply add_sym_refs
    apply (rule corres_stateAssert_add_assertion[rotated])
     apply (clarsimp simp: pred_conj_def sym_refs_asrt_def)
    apply add_sch_act_wf
    apply (rule corres_stateAssert_add_assertion[rotated])
     apply (clarsimp simp: sch_act_wf_asrt_def)
    apply (rule corres_underlying_split[OF _ _ get_simple_ko_sp get_ep_sp'])
     apply (rule corres_guard_imp [OF getEndpoint_corres];
            simp add: ep_relation_def get_ep_queue_def)
    apply (rename_tac ep ep')
    apply (case_tac "ep = Structures_A.IdleEP \<or> ep' = Structures_H.IdleEP")
     apply (case_tac ep; case_tac ep'; simp add: ep_relation_def get_ep_queue_def)
    apply (simp add: endpoint.case_eq_if Structures_A.endpoint.case_eq_if del: K_bind_def)
    apply (simp add: get_ep_queue_def Structures_A.endpoint.case_eq_if)
    apply (rule_tac F="epQueue ep' = ep_queue ep \<and> distinct (ep_queue ep)" in corres_req)
     apply (rule conjI; clarsimp)
      apply (case_tac ep; clarsimp simp: ep_relation_def)
     apply (drule (1) valid_objs_ko_at[OF invs_valid_objs])
     apply (case_tac ep; clarsimp simp: valid_obj_def valid_ep_def)
    apply simp
    apply (rule corres_guard_imp)
      apply (rule P[simplified])
      apply simp
     apply (clarsimp; rule conjI; (fastforce simp: invs_def)?)
     apply clarsimp
     apply (prop_tac "t \<noteq> idle_thread s")
      apply (case_tac ep;
             fastforce simp: obj_at_def invs_def valid_state_def valid_pspace_def
                      dest!: not_idle_tcb_in_SendEp not_idle_tcb_in_RecvEp)
     apply (prop_tac "st_tcb_at is_blocked_on_send_recv t s")
      apply (case_tac ep; erule_tac t=t in ep_queued_st_tcb_at; (fastforce simp: invs_def)?)
     apply (clarsimp simp: pred_tcb_at_disj tcb_at_kh_simps[symmetric] reply_unlink_ts_pred_def
                           conj_disj_distribR is_blocked_on_receive_def is_blocked_on_send_def)
     apply (fastforce simp: pred_tcb_at_def obj_at_def
                     elim!: st_tcb_recv_reply_state_refs[OF _ invs_sym_refs, simplified op_equal])
    apply (clarsimp simp: invs'_def valid_pspace'_def valid_objs'_valid_tcbs')
    apply (fastforce dest!: ep_ko_at_valid_objs_valid_ep' simp: valid_ep'_def split: endpoint.split_asm)
    done
qed

lemma ntfn_cancel_corres_helper:
  "corres dc
          ((\<lambda>s. \<forall>t \<in> set list. tcb_at t s \<and> t \<noteq> idle_thread s
                               \<and> blocked_on_recv_ntfn_tcb_at t s)
           and valid_sched
           and valid_objs
           and pspace_aligned
           and pspace_distinct and (\<lambda>s. heap_refs_inv (tcb_scps_of s) (sc_tcbs_of s))
           and cur_tcb and current_time_bounded
           and K (distinct list))
          ((\<lambda>s. \<forall>t \<in> set list. tcb_at' t s)
           and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
           and Invariants_H.valid_queues
           and valid_queues'
           and valid_objs'
           and valid_release_queue_iff)
          (mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.Restart;
                          sc_opt <- get_tcb_obj_ref tcb_sched_context t;
                          y <- if_sporadic_cur_sc_assert_refill_unblock_check sc_opt;
                          possible_switch_to t
                       od) list)
          (mapM_x (\<lambda>t. do y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                          scOpt <- threadGet tcbSchedContext t;
                          y <- ifCondRefillUnblockCheck scOpt (Some False) (Some True);
                          possibleSwitchTo t
                       od) list)"
  (is "corres _ _ ?conc_guard _ _")
  apply (rule corres_gen_asm')
  apply (rule corres_cross_over_guard[where Q="?conc_guard and cur_tcb'"])
   apply (fastforce simp: cur_tcb_cross)
  apply (subst pred_conj_assoc[symmetric])+
  apply (rule_tac S="{t. (fst t = snd t) \<and> fst t \<in> set list}" in corres_mapM_x_scheme;
         ((subst pred_conj_assoc)+)?)
          apply clarsimp
          apply (rule corres_guard_imp)
            apply (rename_tac tp)
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
             apply (rule_tac Q="\<lambda>_. pspace_aligned and pspace_distinct and current_time_bounded
                                    and active_scs_valid and valid_objs
                                    and valid_sched_action and tcb_at tp"
                    in hoare_strengthen_post[rotated])
              apply clarsimp
              apply (frule (1) valid_objs_ko_at)
              apply (fastforce simp: is_sc_obj obj_at_def opt_map_red valid_objs_def valid_obj_def
                                     valid_tcb_def in_omonad valid_bound_obj_def
                              split: option.splits)
             apply (wp set_thread_state_valid_sched_action)
            apply (simp add: option.case_eq_if bool.case_eq_if)
            apply (rule_tac Q="\<lambda>_. valid_queues and valid_queues' and valid_release_queue_iff
                                   and valid_objs' and tcb_at' tp"
                   in hoare_strengthen_post[rotated])
             apply (clarsimp simp: valid_objs'_valid_tcbs' obj_at'_def)
            apply (wp setThreadState_st_tcb)
           apply force
          apply (clarsimp simp: valid_tcb_state'_def)
         apply (wpsimp wp: set_thread_state_pred_map_tcb_sts_of)
        apply (wpsimp wp: typ_at_lifts)
       apply (clarsimp simp: pred_conj_def)
       apply (rename_tac tp)
       apply (wpsimp wp: get_tcb_obj_ref_wp possible_switch_to_valid_sched_weak hoare_vcg_imp_lift')
        apply (rule_tac Q="\<lambda>_ s. tcb_at tp s \<longrightarrow>
                                   (bound (tcb_scps_of s tp) \<longrightarrow>  not_in_release_q tp s)
                                   \<and> current_time_bounded s
                                   \<and> heap_refs_inv (tcb_scps_of s) (sc_tcbs_of s)
                                   \<and> (pred_map (\<lambda>a. \<exists>y. a = Some y) (tcb_scps_of s) tp
                                       \<and> not_in_release_q tp s
                                           \<longrightarrow> pred_map runnable (tcb_sts_of s) tp
                                               \<and> released_sc_tcb_at tp s
                                               \<and> active_scs_valid s
                                               \<and> tp \<noteq> idle_thread s)
                                   \<and> pspace_distinct s \<and>  cur_tcb s \<and> valid_objs s
                                   \<and>  pspace_aligned s
                                   \<and> valid_sched_except_blocked s
                                   \<and> valid_blocked_except tp s"
                in hoare_strengthen_post[rotated])
         apply (clarsimp simp: obj_at_def is_tcb vs_all_heap_simps opt_map_red)
         apply (rename_tac scp t tcb' sc n)
         apply (clarsimp simp: heap_refs_inv_def2)
         apply (frule_tac x=tp and y=scp in spec2)
         apply (drule_tac x=t and y=scp in spec2)
         apply (clarsimp simp: pred_map_eq vs_all_heap_simps opt_map_red)
        apply (wpsimp wp: set_thread_state_pred_map_tcb_sts_of possible_switch_to_valid_sched_weak
                          set_thread_state_break_valid_sched[simplified pred_conj_def]
                          hoare_vcg_imp_lift')
       apply clarsimp
       apply (rule conjI, clarsimp simp: tcb_at_kh_simps[symmetric])
        apply (drule valid_release_q_not_in_release_q_not_runnable[OF valid_sched_valid_release_q])
         apply (erule pred_tcb_weakenE)
         apply (clarsimp simp: is_blocked_thread_state_defs)
         apply (case_tac "itcb_state tcb"; simp)
        apply clarsimp
       apply clarsimp
       apply (rule conjI)
        apply (frule valid_sched_released_ipc_queues)
        apply (fastforce simp: released_ipc_queues_defs vs_all_heap_simps)
       apply (erule valid_sched_active_scs_valid)
      apply (wpsimp wp: hoare_vcg_const_Ball_lift typ_at_lifts sts_st_tcb')
     apply (auto simp: valid_tcb_state'_def)
  done

lemma refill_unblock_check_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action and active_scs_valid\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  apply (clarsimp simp: weak_valid_sched_action_def)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift'')
  done

crunches if_cond_refill_unblock_check
  for weak_valid_sched_action[wp]: weak_valid_sched_action
  (simp: crunch_simps)

lemma cancelAllSignals_corres:
  "corres dc (invs and valid_sched and ntfn_at ntfn and current_time_bounded)
             (invs' and ntfn_at' ntfn)
             (cancel_all_signals ntfn) (cancelAllSignals ntfn)"
  apply add_sch_act_wf
  apply (simp add: cancel_all_signals_def cancelAllSignals_def)
  apply add_sym_refs
  apply (intro corres_stateAssert_add_assertion)
    apply (rule corres_underlying_split [OF _ _ get_simple_ko_sp get_ntfn_sp'])
     apply (rule corres_guard_imp [OF getNotification_corres])
      apply simp+
    apply (case_tac "ntfn_obj ntfna", simp_all add: ntfn_relation_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF setNotification_corres])
         apply (simp add: ntfn_relation_def)
        apply (rule corres_split [OF ntfn_cancel_corres_helper])
          apply (rule rescheduleRequired_corres)
         apply (simp add: dc_def)
         apply (rename_tac list)
         apply (rule_tac R="\<lambda>_ s. (\<forall>x\<in>set list. released_if_bound_sc_tcb_at x s)
                                  \<and> current_time_bounded s"
                in hoare_post_add)
         apply (rule mapM_x_wp')
         apply wpsimp
            apply (wpsimp wp: hoare_vcg_ball_lift hoare_vcg_imp_lift)
           apply (wpsimp wp: get_tcb_obj_ref_wp)
          apply (wpsimp wp: set_thread_state_weak_valid_sched_action
                            set_thread_state_pred_map_tcb_sts_of hoare_vcg_imp_lift
                      simp: disj_imp)
           apply (rule hoare_pre_cont)
          apply (wpsimp wp: set_thread_state_weak_valid_sched_action
                            set_thread_state_pred_map_tcb_sts_of hoare_vcg_imp_lift)
         apply clarsimp
         apply (rule conjI; clarsimp)
          apply fastforce
         apply (fastforce simp: vs_all_heap_simps)
        apply (rename_tac list)
        apply (rule_tac R="\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s"
               in hoare_post_add)
        apply (rule mapM_x_wp')
        apply (rule hoare_name_pre_state)
        apply (wpsimp wp: hoare_vcg_const_Ball_lift
                          sts_st_tcb' setThreadState_not_st
                    simp: valid_tcb_state'_def)
       apply (wpsimp wp: hoare_vcg_const_Ball_lift)+
     apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
     apply (erule (1) obj_at_valid_objsE)
     apply (frule valid_sched_active_scs_valid)
     apply (clarsimp simp: valid_obj_def valid_ntfn_def not_idle_tcb_in_waitingntfn
                           valid_sched_weak_valid_sched_action
                    dest!: valid_objs_valid_tcbs)
     apply (clarsimp simp: ball_conj_distrib[symmetric])
     apply (rename_tac q s t)
     apply (rule context_conjI)
      apply (drule_tac x=ntfn and y=t and tp=TCBSignal in sym_refsE;
             clarsimp simp: in_state_refs_of_iff refs_of_rev vs_all_heap_simps)
     apply (clarsimp simp: valid_sched_released_ipc_queues released_ipc_queues_blocked_on_recv_ntfn_E1)
    apply clarsimp
    apply (frule invs'_valid_tcbs')
    apply (fastforce simp: invs'_def valid_ntfn'_def
                           valid_obj'_def sym_refs_asrt_def sch_act_wf_asrt_def
           | drule ko_at_valid_objs')+
  done

lemma ep'_Idle_case_helper:
  "(case ep of IdleEP \<Rightarrow> a | _ \<Rightarrow> b) = (if (ep = IdleEP) then a else b)"
  by (cases ep, simp_all)

lemma rescheduleRequired_notresume:
  "\<lbrace>\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread\<rbrace>
    rescheduleRequired \<lbrace>\<lambda>_ s. ksSchedulerAction s = ChooseNewThread\<rbrace>"
  proof -
    have ssa: "\<lbrace>\<top>\<rbrace> setSchedulerAction ChooseNewThread
               \<lbrace>\<lambda>_ s. ksSchedulerAction s = ChooseNewThread\<rbrace>"
      by (simp add: setSchedulerAction_def | wp)+
    show ?thesis
      by (simp add: rescheduleRequired_def, wp ssa)
  qed

lemma setThreadState_ResumeCurrentThread_imp_notct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
proof -
  have nrct:
    "\<lbrace>\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread\<rbrace>
     rescheduleRequired
     \<lbrace>\<lambda>_ s. ksSchedulerAction s \<noteq> ResumeCurrentThread\<rbrace>"
    by (rule hoare_strengthen_post [OF rescheduleRequired_notresume], simp)
  show ?thesis
  apply (simp add: setThreadState_def scheduleTCB_def)
  apply (wpsimp wp: hoare_vcg_imp_lift [OF nrct] isSchedulable_wp hoare_vcg_if_lift2)
   apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp)
    apply clarsimp
   apply (rule hoare_convert_imp [OF threadSet.ksSchedulerAction threadSet.ct])
  apply assumption
  done
qed

lemma replyUnlink_valid_irq_node'[wp]:
  "replyUnlink r t \<lbrace>\<lambda> s. valid_irq_node' (irq_node' s) s\<rbrace>"
  unfolding replyUnlink_def
  by (wpsimp wp: valid_irq_node_lift gts_wp')

lemma replyUnlink_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s p) t\<rbrace>
   replyUnlink r t
   \<lbrace>\<lambda>_ s. P (ksReadyQueues s p) t\<rbrace>"
  unfolding replyUnlink_def
  by (wpsimp wp: gts_wp' sts_ksQ)

lemma weak_sch_act_wf_D1:
  "weak_sch_act_wf sa s \<Longrightarrow> (\<forall>t. sa = SwitchToThread t \<longrightarrow> st_tcb_at' runnable' t s)"
  by (simp add: weak_sch_act_wf_def)

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
                      valid_sched_context'_def valid_sched_context_size'_def scBits_simps objBits_simps
               dest!: opt_predD
               elim!: opt_mapE)

lemma refillUnblockCheck_ko_wp_at_not_live[wp]:
  "refillUnblockCheck scp \<lbrace>\<lambda>s. P (ko_wp_at' (Not \<circ> live') p' s)\<rbrace>"
  unfolding refillUnblockCheck_def refillHeadOverlappingLoop_def mergeRefills_def
  apply (wpsimp wp: whileLoop_valid_inv updateSchedContext_wp hoare_drop_imps getRefillNext_wp
              simp: updateRefillHd_def refillPopHead_def)
        apply (clarsimp simp: ko_wp_at'_def obj_at'_def runReaderT_def opt_map_red
                   split del: if_split
                       elim!: rsubst[where P=P])
        apply (frule refillHeadOverlapping_implies_count_greater_than_one)
         apply (fastforce simp: obj_at'_def)
        apply (rule iffI; clarsimp simp: opt_map_red split: if_splits)
            apply (fastforce simp: objBits_simps' live_sc'_def)+
         apply (clarsimp simp: ps_clear_upd)+
       apply (wpsimp wp: updateSchedContext_wp simp: updateRefillHd_def)
      apply (wpsimp wp: hoare_drop_imps refillReady_wp isRoundRobin_wp simp: setReprogramTimer_def)+
  apply (clarsimp simp: ko_wp_at'_def obj_at'_def opt_map_red
             split del: if_split
                 elim!: rsubst[where P=P])
  apply (intro iffI; clarsimp simp: opt_map_red)
   apply (fold fun_upd_def)
   apply (fastforce simp: objBits_simps')
  apply (clarsimp simp: opt_map_red ps_clear_upd split: if_splits)
  done

lemma updateRefillHd_refs_of'[wp]:
  "updateRefillHd sc_ptr f \<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>"
  unfolding updateRefillHd_def updateSchedContext_def
  apply (wpsimp wp: setObject_state_refs_of_eq)
  apply (fastforce elim!: rsubst[where P=P] simp: obj_at'_def state_refs_of'_def split: if_splits)
  done

lemma refillPopHead_refs_of'[wp]:
  "refillPopHead sc_ptr \<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>"
  unfolding refillPopHead_def updateSchedContext_def
  apply wpsimp
  apply (fastforce elim!: rsubst[where P=P] simp: obj_at'_def state_refs_of'_def split: if_splits)
  done

crunches ifCondRefillUnblockCheck
  for ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' t"
  and valid_pspace'[wp]: valid_pspace'
  and list_refs_of_replies'[wp]: "\<lambda>s. P (list_refs_of_replies' s)"
  and if_live_then_nonz_cap'[wp]: if_live_then_nonz_cap'
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and valid_machine_state'[wp]: valid_machine_state'
  and ksInterrupt[wp]: "\<lambda>s. P (ksInterruptState s)"
  and unlive[wp]: "ko_wp_at' (Not \<circ> live') p"
  and refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  (wp: crunch_wps updateSchedContext_wp simp: crunch_simps valid_pspace'_def ignore: threadSet)

lemma cancel_all_invs'_helper:
  "\<lbrace>invs' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)
    and (\<lambda>s. (\<forall>x \<in> set q.
                tcb_at' x s \<and> ex_nonz_cap_to' x s \<and> sch_act_not x s \<and>
                st_tcb_at' (\<lambda>st. (\<exists>obj grant reply. st = BlockedOnReceive obj grant reply) \<or>
                           (\<exists>obj badge grant grantreply iscall.
                            st = BlockedOnSend obj badge grant grantreply iscall)) x s)
         \<and> distinct q)\<rbrace>
   mapM_x (\<lambda>t. do st <- getThreadState t;
                  y <- case if isReceive st then replyObject st else None of None \<Rightarrow> return () | Some x \<Rightarrow> replyUnlink x t;
                  fault <- threadGet tcbFault t;
                  if fault = None then do y <- setThreadState Structures_H.thread_state.Restart t;
                                          scOpt <- threadGet tcbSchedContext t;
                                          y \<leftarrow> ifCondRefillUnblockCheck scOpt (Some False) (Some True);
                                          possibleSwitchTo t
                                       od
                  else setThreadState Structures_H.thread_state.Inactive t
               od) q
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  supply if_split[split del] comp_apply[simp del]
  unfolding valid_dom_schedule'_def invs'_def
  apply (rule mapM_x_inv_wp2)
   apply clarsimp
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
                    hoare_vcg_const_Ball_lift sts_st_tcb' setThreadState_not_st
                    possibleSwitchTo_sch_act_not_other)
       apply (strengthen weak_sch_act_wf_D1)
       apply (wpsimp wp: valid_irq_node_lift hoare_vcg_const_Ball_lift
                         sts_valid_queues sts_st_tcb' setThreadState_not_st sts_sch_act'
                  split: if_splits)+
     apply (wp hoare_drop_imp)
    apply (wpsimp wp: hoare_vcg_const_Ball_lift hoare_vcg_all_lift gts_wp' hoare_vcg_imp_lift
                      replyUnlink_valid_objs' replyUnlink_st_tcb_at'
                simp: valid_tcb_state'_def)+
  apply (rule conjI)
   apply (fastforce simp: global'_no_ex_cap pred_tcb_at'_def obj_at'_def)
  apply clarsimp
  apply (apply_conjunct \<open>intro impI\<close>,
         (frule (1) valid_replies'_other_state; clarsimp))+
  apply (fastforce simp: global'_no_ex_cap)
  done

lemma not_in_epQueue:
  assumes ko_at:  "ko_at' r ep_ptr s" and
          srefs:  "sym_refs (state_refs_of' s)" and
          nidle:  "r \<noteq> IdleEP" and
          st_act: "st_tcb_at' simple' t s"
  shows   "t \<notin> set (epQueue r)"
proof
  assume t_epQ: "t \<in> set (epQueue r)"

  with ko_at nidle
  have "(t, EPRecv) \<in> state_refs_of' s ep_ptr
        \<or> (t, EPSend) \<in> state_refs_of' s ep_ptr"
    by - (drule ko_at_state_refs_ofD', case_tac r, (clarsimp)+)

  with ko_at srefs
  have "(ep_ptr, TCBBlockedRecv) \<in> state_refs_of' s t
         \<or> (ep_ptr, TCBBlockedSend) \<in> state_refs_of' s t"
    apply -
    apply (frule(1) sym_refs_ko_atD')
    apply (drule ko_at_state_refs_ofD')
    apply (case_tac r)
      apply (clarsimp simp: st_tcb_at_refs_of_rev'
             | drule(1) bspec | drule st_tcb_at_state_refs_ofD')+
    done

  with ko_at have "st_tcb_at' (Not \<circ> simple') t s"
    apply -
    apply (erule disjE)
     apply (drule state_refs_of'_elemD)
     apply (simp add: st_tcb_at_refs_of_rev')
     apply (erule pred_tcb'_weakenE)
     apply (clarsimp simp: isBlockedOnReply_def)
    apply (drule state_refs_of'_elemD)
    apply (simp add: st_tcb_at_refs_of_rev')
    apply (erule pred_tcb'_weakenE)
    apply (clarsimp simp: isBlockedOnReply_def)
    done

  with st_act show False
    by (rule pred_tcb'_neq_contra) simp
qed

lemma ct_not_in_epQueue:
  assumes "ko_at' r ep_ptr s" and
          "sym_refs (state_refs_of' s)" and
          "r \<noteq> IdleEP" and
          "ct_in_state' simple' s"
  shows   "ksCurThread s \<notin> set (epQueue r)"
  using assms unfolding ct_in_state'_def
  by (rule not_in_epQueue)

lemma not_in_ntfnQueue:
  assumes ko_at:  "ko_at' r ntfn_ptr s" and
          srefs:  "sym_refs (state_refs_of' s)" and
          nidle:  "ntfnObj r \<noteq> IdleNtfn \<and> (\<forall>b m. ntfnObj r \<noteq> ActiveNtfn b)" and
          st_act: "st_tcb_at' simple' t s"
  shows   "t \<notin> set (ntfnQueue (ntfnObj r))"
proof
  assume t_epQ: "t \<in> set (ntfnQueue (ntfnObj r))"

  with ko_at nidle
  have "(t, NTFNSignal) \<in> state_refs_of' s ntfn_ptr"
    by - (drule ko_at_state_refs_ofD', case_tac "ntfnObj r", (clarsimp)+)
  with ko_at srefs
  have "(ntfn_ptr, TCBSignal) \<in> state_refs_of' s t"
    apply -
    apply (frule(1) sym_refs_ko_atD')
    apply (drule ko_at_state_refs_ofD')
    apply (case_tac "ntfnObj r")
      apply (clarsimp simp: st_tcb_at_refs_of_rev' ntfn_bound_refs'_def
             | drule st_tcb_at_state_refs_ofD')+
      apply (drule_tac x="(t, NTFNSignal)" in bspec, clarsimp)
      apply (clarsimp simp: st_tcb_at_refs_of_rev' sym_refs_def dest!: st_tcb_at_state_refs_ofD')
     apply (fastforce simp: st_tcb_at_refs_of_rev' sym_refs_def dest!: st_tcb_at_state_refs_ofD')
    by (metis sym_refs_simp symreftype.simps(7))

  with ko_at have "st_tcb_at' (Not \<circ> simple') t s"
    apply -
    apply (drule state_refs_of'_elemD)
    apply (simp add: st_tcb_at_refs_of_rev')
    apply (erule pred_tcb'_weakenE)
    apply (clarsimp simp: isBlockedOnReply_def)
    done

  with st_act show False
    by (rule pred_tcb'_neq_contra) simp
qed

lemma ct_not_in_ntfnQueue:
  assumes ko_at:  "ko_at' r ntfn_ptr s" and
          srefs:  "sym_refs (state_refs_of' s)" and
          nidle:  "ntfnObj r \<noteq> IdleNtfn \<and> (\<forall>b m. ntfnObj r \<noteq> ActiveNtfn b)" and
          st_act: "ct_in_state' simple' s"
  shows   "ksCurThread s \<notin> set (ntfnQueue (ntfnObj r))"
  using assms unfolding ct_in_state'_def
  by (rule not_in_ntfnQueue)

lemma sch_act_wf_weak[elim!]:
  "sch_act_wf sa s \<Longrightarrow> weak_sch_act_wf sa s"
  by (case_tac sa, (simp add: weak_sch_act_wf_def)+)

lemma cancelAllIPC_invs'[wp]:
  "cancelAllIPC ep_ptr \<lbrace>invs'\<rbrace>"
  supply valid_dom_schedule'_def[simp]
  unfolding cancelAllIPC_def cancelAllIPC_loop_body_def restartThreadIfNoFault_def
  apply (simp add: ep'_Idle_case_helper cong del: if_cong)
  apply (intro hoare_seq_ext[OF _ stateAssert_sp])
  apply (wpsimp wp: rescheduleRequired_invs' cancel_all_invs'_helper
                    hoare_vcg_const_Ball_lift
                    valid_global_refs_lift' valid_arch_state_lift'
                    valid_irq_node_lift ssa_invs' sts_sch_act' getEndpoint_wp
                    irqs_masked_lift)
    apply (clarsimp simp: invs'_def valid_ep'_def)
    apply (wpsimp wp: hoare_vcg_const_Ball_lift)
   apply (wpsimp wp: getEndpoint_wp)
  apply (clarsimp simp: invs'_def valid_ep'_def)
  apply (frule obj_at_valid_objs', fastforce)
  apply (clarsimp simp:  valid_obj'_def)
  apply (rule conjI)
   apply (metis fold_list_refs_of_replies')
  apply (clarsimp simp: sym_refs_asrt_def sch_act_wf_asrt_def)
  apply (rule conjI)
   apply (drule(1) sym_refs_ko_atD')
   apply (clarsimp simp: valid_ep'_def st_tcb_at_refs_of_rev' split: endpoint.splits)
     apply (intro conjI)
      apply ((drule(1) bspec | drule st_tcb_at_state_refs_ofD'
              | clarsimp elim!: if_live_state_refsE split: if_splits)+)[1]
     apply (fastforce simp: st_tcb_at'_def obj_at'_def)
    apply (fastforce elim!: pred_tcb'_weakenE)
   apply (intro conjI)
     apply ((drule(1) bspec | drule st_tcb_at_state_refs_ofD'
             | clarsimp elim!: if_live_state_refsE split: if_splits)+)[1]
    apply (fastforce simp: st_tcb_at'_def obj_at'_def)
   apply (fastforce elim!: pred_tcb'_weakenE)
  apply (clarsimp simp: valid_ep'_def split: endpoint.splits)
  done

lemma ex_nonz_cap_to'_tcb_in_WaitingNtfn'_q:
  "\<lbrakk>ko_at' ntfn ntfnPtr s; ntfnObj ntfn = Structures_H.ntfn.WaitingNtfn q; valid_objs' s;
    sym_refs (state_refs_of' s); if_live_then_nonz_cap' s; t \<in> set q\<rbrakk>
   \<Longrightarrow> ex_nonz_cap_to' t s"
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x = ntfnPtr in allE)
  apply (drule_tac x = "(t, NTFNSignal)" in bspec)
   apply (clarsimp simp: state_refs_of'_def obj_at'_def refs_of'_def)
  apply (fastforce intro: if_live_state_refsE)
  done

lemma cancelAllSignals_invs'_helper:
  "\<lbrace>invs' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)
    and (\<lambda>s. (\<forall>x \<in> set q. st_tcb_at' (\<lambda>st. \<exists>ref. st = BlockedOnNotification ref) x s
                          \<and> ex_nonz_cap_to' x s))
    and K (distinct q)\<rbrace>
    mapM_x (\<lambda>t. do y <- setThreadState Structures_H.thread_state.Restart t;
                        scOpt <- threadGet tcbSchedContext t;
                        y \<leftarrow> ifCondRefillUnblockCheck scOpt (Some False) (Some True);
                        possibleSwitchTo t
                od) q
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding valid_dom_schedule'_def invs'_def
  apply (rule hoare_gen_asm)
  apply (rule mapM_x_inv_wp2)
   apply clarsimp
  apply (wpsimp wp: sts_st_tcb_at'_cases valid_irq_node_lift irqs_masked_lift
                    hoare_vcg_const_Ball_lift hoare_vcg_all_lift hoare_vcg_imp_lift'
              simp: cteCaps_of_def o_def)
  apply (fastforce simp: valid_tcb_state'_def global'_no_ex_cap
                         pred_tcb_at'_def obj_at'_def distinct_imply_not_in_tail)
  done

lemma ntfn_queued_st_tcb_at':
  "\<And>P. \<lbrakk>ko_at' ntfn ptr s; (t, rt) \<in> ntfn_q_refs_of' (ntfnObj ntfn);
         valid_objs' s; sym_refs (state_refs_of' s);
         \<And>ref. P (BlockedOnNotification ref) \<rbrakk>
   \<Longrightarrow> st_tcb_at' P t s"
  apply (case_tac "ntfnObj ntfn", simp_all)
  apply (frule(1) sym_refs_ko_atD')
  apply (clarsimp)
  apply (erule_tac y="(t,NTFNSignal)" in my_BallE)
   apply (clarsimp simp: refs_of_rev' pred_tcb_at'_def obj_at'_def ko_wp_at'_def)+
  done

lemma cancelAllSignals_invs'[wp]:
  "cancelAllSignals ntfnPtr \<lbrace>invs'\<rbrace>"
  apply (simp add: cancelAllSignals_def)
  apply (intro hoare_seq_ext[OF _ stateAssert_sp])
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp'])
  apply (case_tac "ntfnObj ntfn"; simp)
    apply wpsimp
   apply wpsimp
  apply (wpsimp wp: rescheduleRequired_invs' sts_st_tcb_at'_cases
                    cancelAllSignals_invs'_helper hoare_vcg_const_Ball_lift
                    hoare_drop_imps hoare_vcg_all_lift
              simp: valid_dom_schedule'_def)
   apply (clarsimp simp: invs'_def valid_dom_schedule'_def)
   apply (wpsimp wp: hoare_vcg_const_Ball_lift)
  apply (clarsimp simp: invs'_def valid_pspace'_def valid_ntfn'_def
                        valid_dom_schedule'_def)
  apply (prop_tac "valid_ntfn' ntfn s")
   apply (frule (2) ntfn_ko_at_valid_objs_valid_ntfn')
  apply (clarsimp simp: valid_ntfn'_def)
  apply (intro conjI impI)
    apply (clarsimp simp: list_refs_of_replies'_def opt_map_def o_def split: option.splits)
    apply (fastforce intro: if_live_then_nonz_capE'
                      simp: ko_wp_at'_def obj_at'_def  live_ntfn'_def)
   apply (fastforce elim!: ex_nonz_cap_to'_tcb_in_WaitingNtfn'_q ntfn_queued_st_tcb_at'
                    simp: sym_refs_asrt_def sch_act_wf_asrt_def)+
  done

lemma setQueue_valid_ep'[wp]:
  "setQueue domain prio q \<lbrace>valid_ep' ep\<rbrace>"
  apply (clarsimp simp: setQueue_def)
  apply wpsimp
  apply (clarsimp simp: valid_ep'_def split: endpoint.splits)
  done

lemma tcbSchedEnqueue_valid_ep'[wp]:
  "tcbSchedEnqueue thread \<lbrace>valid_ep' ep\<rbrace>"
  apply (clarsimp simp: tcbSchedEnqueue_def unless_def when_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply clarsimp
  apply (rule hoare_seq_ext_skip, wpsimp wp: hoare_if)+
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: valid_ep'_def obj_at'_def  objBitsKO_def split: endpoint.splits)
  done

lemma cancelAllIPC_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace> cancelAllIPC ep \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  unfolding cancelAllIPC_def
  apply (wpsimp wp: mapM_x_wp_inv getEndpoint_wp)
  by (fastforce simp: valid_ep'_def)

lemma cancelAllSignals_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace> cancelAllSignals ntfn \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  unfolding cancelAllSignals_def
  apply (wpsimp wp: mapM_x_wp_inv getNotification_wp)
  by (fastforce simp: valid_obj'_def valid_ntfn'_def
                dest: ko_at_valid_objs')

lemma cancelAllIPC_st_tcb_at:
  "\<lbrace>st_tcb_at' P t and K (P Inactive \<and> P Restart)\<rbrace>
   cancelAllIPC epptr
   \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  unfolding cancelAllIPC_def cancelAllIPC_loop_body_def restartThreadIfNoFault_def
  apply (rule hoare_gen_asm)
  apply simp
  apply (intro hoare_seq_ext[OF _ stateAssert_sp])
  apply (intro hoare_seq_ext[OF _ get_ep_sp'])
  apply (clarsimp simp: endpoint.case_eq_if)
  apply (rule conjI)
   apply wpsimp
  apply (wpsimp wp: mapM_x_wp' sts_st_tcb_at'_cases threadGet_wp hoare_vcg_imp_lift
              simp: obj_at_ko_at'_eq[where P=\<top>, simplified])
     apply (rule_tac Q="\<lambda>_. tcb_at' x and st_tcb_at' P t" in hoare_strengthen_post)
      apply (wpsimp wp: replyUnlink_st_tcb_at')
     apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
    apply (wpsimp wp: gts_wp')
    apply (fastforce simp: obj_at_ko_at'_eq[where P=\<top>, simplified])
   apply wpsimp
  by clarsimp

lemmas cancelAllIPC_makes_simple[wp] =
       cancelAllIPC_st_tcb_at [where P=simple', simplified]

lemma cancelAllSignals_st_tcb_at:
  "\<lbrace>st_tcb_at' P t and K (P Restart)\<rbrace>
   cancelAllSignals epptr
   \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  unfolding cancelAllSignals_def
  apply (rule hoare_gen_asm)
  apply (wpsimp wp: mapM_x_wp' sts_st_tcb_at'_cases getNotification_wp)
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
                     objBits_simps' updateObject_default_def
                     ps_clear_upd RISCV64_H.fromPPtr_def)

lemma rescheduleRequired_unlive[wp]:
  "\<lbrace>\<lambda>s. ko_wp_at' (Not \<circ> live') p s \<and> sch_act_not p s\<rbrace>
   rescheduleRequired
   \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  unfolding rescheduleRequired_def
  apply (wpsimp wp: setObject_ko_wp_at getObject_tcb_wp isSchedulable_wp
              simp: objBits_simps' bitmap_fun_defs tcbSchedEnqueue_def unless_def
                    threadSet_def setQueue_def threadGet_getObject)+
  by (fastforce simp: o_def dest!: obj_at_ko_at'[where P=\<top>])

lemma tcbSchedEnqueue_unlive_other:
  "\<lbrace>ko_wp_at' (Not \<circ> live') p and K (p \<noteq> t)\<rbrace>
   tcbSchedEnqueue t
   \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def)
  apply (wpsimp wp: threadGet_wp threadSet_unlive_other)
  apply (fastforce simp: obj_at'_def  ko_wp_at'_def)
  done

crunches scheduleTCB
  for unlive[wp]: "ko_wp_at' (Not \<circ> live') p"
  (wp: crunch_wps isSchedulable_inv simp: crunch_simps)

lemma setThreadState_unlive_other:
  "\<lbrace>ko_wp_at' (Not \<circ> live') p and sch_act_not p and K (p \<noteq> t)\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>rv. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  unfolding setThreadState_def
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: ko_wp_at'_def obj_at'_def)
  done

context begin interpretation Arch . (*FIXME: arch_split*)

lemma possibleSwitchTo_unlive_other:
  "\<lbrace>ko_wp_at' (Not \<circ> live') p and sch_act_not p and K (p \<noteq> t)\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  apply (simp add: possibleSwitchTo_def inReleaseQueue_def)
  apply (wpsimp wp: tcbSchedEnqueue_unlive_other threadGet_wp rescheduleRequired_unlive)+
  apply (auto simp: obj_at'_def ko_wp_at'_def)
  done

lemma setThreadState_Inactive_unlive:
  "\<lbrace>ko_wp_at' (Not \<circ> live') p and sch_act_not p\<rbrace>
   setThreadState Inactive tptr
   \<lbrace>\<lambda>_. ko_wp_at' (Not o live') p\<rbrace>"
  apply (clarsimp simp: setThreadState_def)
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: ko_wp_at'_def obj_at'_def is_aligned_def ps_clear_def objBitsKO_def)
  done

lemma replyUnlink_unlive:
  "\<lbrace>ko_wp_at' (Not \<circ> live') p and sch_act_not p\<rbrace>
   replyUnlink replyPtr tcbPtr
   \<lbrace>\<lambda>_. ko_wp_at' (Not o live') p\<rbrace>"
  apply (clarsimp simp: replyUnlink_def updateReply_def)
  apply (wpsimp wp: setThreadState_Inactive_unlive set_reply'.set_wp gts_wp')
  apply (fastforce simp: ko_wp_at'_def obj_at'_def is_aligned_def ps_clear_def
                         objBitsKO_def live_reply'_def)
  done

lemma cancelAllIPC_unlive:
  "\<lbrace>valid_objs' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and ep_at' ep\<rbrace>
   cancelAllIPC ep
   \<lbrace>\<lambda>rv. ko_wp_at' (Not \<circ> live') ep\<rbrace>"
  unfolding cancelAllIPC_def cancelAllIPC_loop_body_def restartThreadIfNoFault_def
  apply (simp add: ep'_Idle_case_helper)
  apply wpsimp
       apply (rule_tac Q="\<lambda>_ s. ko_wp_at' (Not \<circ> live') ep s \<and> sch_act_not ep s \<and> ep_at' ep s"
                    in hoare_post_imp, fastforce)
       apply (rule mapM_x_wp_inv)
       apply (wpsimp wp: possibleSwitchTo_unlive_other setThreadState_unlive_other
                         possibleSwitchTo_sch_act_not_other replyUnlink_unlive hoare_drop_imps)
       apply (clarsimp simp: ko_wp_at'_def st_tcb_at'_def obj_at'_def isReceive_def)
      apply (wpsimp wp: set_ep'.set_wp getEndpoint_wp)+
  by (fastforce simp: ko_wp_at'_def st_tcb_at'_def obj_at'_def isReceive_def objBits_simps)

lemma cancelAllSignals_unlive_helper:
  "\<lbrace>\<lambda>s. (\<forall>x\<in>set xs. tcb_at' x s) \<and> ko_wp_at' (Not \<circ> live') p s
         \<and> sch_act_not p s \<and> p \<notin> set xs\<rbrace>
   mapM_x (\<lambda>t. do
                 y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                 scOpt <- threadGet tcbSchedContext t;
                 y <- ifCondRefillUnblockCheck scOpt (Some False) (Some True);
                 possibleSwitchTo t
               od) xs
   \<lbrace>\<lambda>rv s. (\<forall>x\<in>set xs. tcb_at' x s) \<and> ko_wp_at' (Not \<circ> live') p s
           \<and>sch_act_not p s\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp')
   apply (rule hoare_pre)
    apply (wpsimp wp: hoare_vcg_const_Ball_lift setThreadState_unlive_other
                      possibleSwitchTo_unlive_other possibleSwitchTo_sch_act_not_other)
   apply clarsimp
  apply clarsimp
  done

lemma cancelAllSignals_unlive:
  "\<lbrace>\<lambda>s. valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s
      \<and> obj_at' (\<lambda>ko. ntfnBoundTCB ko = None) ntfnptr s
      \<and> obj_at' (\<lambda>ko. ntfnSc ko = None) ntfnptr s\<rbrace>
   cancelAllSignals ntfnptr
   \<lbrace>\<lambda>rv. ko_wp_at' (Not \<circ> live') ntfnptr\<rbrace>"
  apply (simp add: cancelAllSignals_def)
  apply (repeat_unless \<open>rule hoare_seq_ext[OF _ get_ntfn_sp']\<close>
                       \<open>rule hoare_seq_ext_skip, wpsimp\<close>)
  apply (case_tac "ntfnObj ntfn"; simp)
    apply wp
    apply (fastforce simp: obj_at'_real_def live_ntfn'_def ko_wp_at'_def)
   apply wp
   apply (fastforce simp: obj_at'_real_def live_ntfn'_def ko_wp_at'_def)
  apply (wp rescheduleRequired_unlive)
    apply (rule cancelAllSignals_unlive_helper[THEN hoare_strengthen_post])
    apply fastforce
   apply (wpsimp wp: hoare_vcg_const_Ball_lift set_ntfn'.ko_wp_at
               simp: objBits_simps')
  apply (clarsimp, frule (1) ko_at_valid_objs'_pre,
         clarsimp simp: valid_obj'_def valid_ntfn'_def)
  apply (intro conjI[rotated]; clarsimp)
    apply (fastforce simp: obj_at'_def)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  apply (clarsimp simp: live_ntfn'_def ko_wp_at'_def obj_at'_def)
  done

declare if_cong[cong]

lemma insert_eqD:
  "A = insert a B \<Longrightarrow> a \<in> A"
  by blast

crunches setSchedulerAction
  for tcb_in_cur_domain'[wp]: "tcb_in_cur_domain' p"
  (simp: tcb_in_cur_domain'_def wp_del: ssa_wp)

crunches possibleSwitchTo
  for tcb_in_cur_domain'[wp]: "tcb_in_cur_domain' p"
  and ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps)

lemma cancelBadgedSends_filterM_helper':
  notes if_cong[cong del]
  shows
  "\<forall>ys.
   \<lbrace>\<lambda>s. invs' s \<and> sch_act_wf (ksSchedulerAction s) s
           \<and> ex_nonz_cap_to' epptr s \<and> ep_at' epptr s
           \<and> sym_refs ((state_refs_of' s) (epptr := set (xs @ ys) \<times> {EPSend}))
           \<and> (\<forall>y \<in> set (xs @ ys). state_refs_of' s y = {(epptr, TCBBlockedSend)}
                                                        \<union> tcb_non_st_state_refs_of' s y)
           \<and> distinct (xs @ ys)\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> getThreadState t;
                      if blockingIPCBadge st = badge
                      then
                        do restartThreadIfNoFault t;
                           return False
                        od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv s. invs' s \<and> sch_act_wf (ksSchedulerAction s) s
           \<and> ex_nonz_cap_to' epptr s \<and> ep_at' epptr s
           \<and> sym_refs ((state_refs_of' s) (epptr := (set rv \<union> set ys) \<times> {EPSend}))
           \<and> (\<forall>y \<in> set ys. state_refs_of' s y = {(epptr, TCBBlockedSend)}
                                                 \<union> tcb_non_st_state_refs_of' s y)
           \<and> distinct rv \<and> distinct (xs @ ys) \<and> set rv \<subseteq> set xs \<and> (\<forall>x \<in> set xs. tcb_at' x s)\<rbrace>"
  supply valid_dom_schedule'_def[simp]
  unfolding restartThreadIfNoFault_def
  apply (simp only: invs'_def)
  apply (rule_tac xs=xs in rev_induct)
   apply clarsimp
   apply wp
   apply clarsimp
  apply (clarsimp simp: filterM_append bind_assoc simp del: set_append distinct_append)
  apply (drule spec, erule hoare_seq_ext[rotated])
  apply (rule hoare_seq_ext [OF _ gts_inv'])
  apply (simp add: opt_map_Some_eta_fold split del: if_split)
  apply (rule hoare_pre)
   apply (wpsimp wp: setThreadState_state_refs_of' valid_irq_node_lift hoare_vcg_const_Ball_lift
                     valid_irq_handlers_lift'' irqs_masked_lift sts_st_tcb'
                     hoare_vcg_all_lift sts_sch_act'
                     threadGet_inv[THEN hoare_drop_imp] hoare_vcg_imp_lift'
               simp: cteCaps_of_def o_def)
  apply (clarsimp simp: opt_map_Some_eta_fold)
  apply (frule insert_eqD, frule state_refs_of'_elemD)
  apply (clarsimp simp: valid_tcb_state'_def st_tcb_at_refs_of_rev')
  apply (frule pred_tcb_at')
  apply (rule conjI[rotated], blast)
  apply (clarsimp cong: conj_cong)
  apply (thin_tac "sym_refs _") \<comment> \<open>this removes the list_refs_of_reply' sym_refs premise\<close>
  apply (intro conjI)
          apply (find_goal \<open>match conclusion in "sym_refs _" \<Rightarrow> \<open>-\<close>\<close>)
          apply (erule delta_sym_refs)
           apply (fastforce split: if_split_asm)
          subgoal (* this takes approximately 15s *)
          by (auto simp: state_refs_of'_def symreftype_inverse'
                         tcb_bound_refs'_def obj_at'_def get_refs_def2 tcb_st_refs_of'_def
                  split: option.splits if_splits thread_state.splits)
         by (fastforce simp: valid_pspace'_def valid_tcb'_def pred_tcb_at'_def obj_at'_def subsetD
                      elim!: valid_objs_valid_tcbE' st_tcb_ex_cap'')+

lemmas cancelBadgedSends_filterM_helper
    = spec [where x=Nil, OF cancelBadgedSends_filterM_helper', simplified]

lemma cancelBadgedSends_invs'[wp]:
  notes if_cong[cong del]
  shows
  "cancelBadgedSends epptr badge \<lbrace>invs'\<rbrace>"
  apply (simp add: cancelBadgedSends_def)
  apply (intro hoare_seq_ext[OF _ stateAssert_sp])
  apply (rule hoare_seq_ext [OF _ get_ep_sp'], rename_tac ep)
  apply (case_tac ep, simp_all)
    apply ((wp | simp)+)[2]
  apply (subst bind_assoc [where g="\<lambda>_. rescheduleRequired",
                           symmetric])+
  apply (rule hoare_seq_ext
                [OF rescheduleRequired_invs'])
  apply (simp add: list_case_return invs'_def valid_dom_schedule'_def cong: list.case_cong)
  apply (rule hoare_pre, wp valid_irq_node_lift irqs_masked_lift)
    apply (rule hoare_strengthen_post,
           rule cancelBadgedSends_filterM_helper[where epptr=epptr])
    apply (clarsimp simp: ep_redux_simps3 fun_upd_def[symmetric] o_def)
    apply (clarsimp simp add: valid_ep'_def invs'_def valid_dom_schedule'_def comp_def
                       split: list.split)
    apply blast
   apply (simp add: list_case_return invs'_def valid_dom_schedule'_def)
   apply (wp valid_irq_node_lift irqs_masked_lift | wp (once) sch_act_sane_lift)+
  apply (clarsimp simp: valid_ep'_def fun_upd_def[symmetric]
                        obj_at'_weakenE[OF _ TrueI])
  apply (frule obj_at_valid_objs', clarsimp)
  apply (clarsimp simp: valid_obj'_def valid_ep'_def )
  apply (frule if_live_then_nonz_capD', simp add: obj_at'_real_def)
   apply clarsimp
  apply (clarsimp simp: sym_refs_asrt_def)
  apply (frule(1) sym_refs_ko_atD')
  apply (clarsimp simp add: fun_upd_idem st_tcb_at_refs_of_rev' o_def sch_act_wf_asrt_def)
  apply (drule (1) bspec, drule st_tcb_at_state_refs_ofD', clarsimp)
  apply (auto simp: tcb_bound_refs'_def get_refs_def
             split: option.splits)
  done

lemma restart_thread_if_no_fault_valid_sched_blocked_on_send:
  "\<lbrace>\<lambda>s. valid_sched s \<and> tcb_at t s \<and> heap_refs_inv (tcb_scps_of s) (sc_tcbs_of s)
        \<and> current_time_bounded s
        \<and> (epptr, TCBBlockedSend) \<in> state_refs_of s t \<and> t \<noteq> idle_thread s\<rbrace>
   restart_thread_if_no_fault t
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp wp: restart_thread_if_no_fault_valid_sched gts_wp)
  apply (frule valid_sched_released_ipc_queues)
  apply (frule TCBBlockedSend_in_state_refs_of)
  apply (prop_tac "blocked_on_send_tcb_at t s")
   apply (fastforce simp: is_blocked_thread_state_defs vs_all_heap_simps obj_at_def pred_tcb_at_def)
  apply (drule (1) released_ipc_queues_blocked_on_send_E1)
  apply (intro conjI)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def vs_all_heap_simps)
   apply (metis runnable.simps)
  apply (clarsimp simp: is_timeout_fault_opt_def vs_all_heap_simps obj_at_def pred_tcb_at_def)
  done

lemma in_send_ep_queue_TCBBlockedSend':
  "\<lbrakk>ko_at' (Structures_H.SendEP queue) epptr s; x \<in> set queue;
    sym_refs (state_refs_of' s); valid_objs' s\<rbrakk>
   \<Longrightarrow> ko_wp_at' (\<lambda>ko. (epptr, TCBBlockedSend) \<in> refs_of' ko) x s"
  apply (prop_tac "valid_ep' (Structures_H.SendEP queue) s")
   apply (fastforce simp: valid_objs'_def valid_obj'_def obj_at'_def
                   split: kernel_object.splits)
  apply (clarsimp simp: valid_ep'_def)
  apply (prop_tac "(x, EPSend) \<in> state_refs_of' s epptr")
   apply (clarsimp simp: state_refs_of'_def obj_at'_def)
  apply (clarsimp simp: sym_refs_def)
  apply (fastforce simp: ko_wp_at'_def obj_at'_def  state_refs_of'_def)
  done

lemma cancelBadgedSends_corres:
  "corres dc (invs and valid_sched and ep_at epptr and current_time_bounded)
             (invs' and ep_at' epptr)
         (cancel_badged_sends epptr bdg) (cancelBadgedSends epptr bdg)"
  apply add_sym_refs
  apply add_sch_act_wf
  apply (clarsimp simp: cancel_badged_sends_def cancelBadgedSends_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (clarsimp simp: sym_refs_asrt_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (clarsimp simp: sch_act_wf_asrt_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getEndpoint_corres _ get_simple_ko_sp get_ep_sp',
                                        where Q="invs and valid_sched and current_time_bounded"
                                          and Q'="invs' and (\<lambda>s. sym_refs (state_refs_of' s))
                                                  and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)"])
    apply simp_all
  apply (case_tac ep; simp add: ep_relation_def)
  apply (rename_tac queue)
  apply (simp add: filterM_mapM list_case_return cong: list.case_cong)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor[OF setEndpoint_corres])
       apply (clarsimp simp: ep_relation_def)
      apply (rule_tac F="distinct queue" in corres_gen_asm)
      apply (rule corres_split_eqr)
         apply (rule_tac P="\<lambda>s. valid_sched s \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_objs s
                                \<and> heap_refs_inv (tcb_scps_of s) (sc_tcbs_of s) \<and> current_time_bounded s"
                     and Q="\<lambda>t s. tcb_at t s \<and> (epptr, TCBBlockedSend) \<in> state_refs_of s t
                                  \<and> t \<noteq> idle_thread s"
                     and P'="\<lambda>s. valid_objs' s \<and> weak_sch_act_wf (ksSchedulerAction s) s \<and> valid_queues s
                                 \<and> valid_queues' s \<and> valid_tcbs' s \<and> valid_release_queue_iff s"
                     and Q'="\<lambda>t s. tcb_at' t s \<and> st_tcb_at' (not runnable') t s"
                     and S="{t. (fst t = snd t) \<and> fst t \<in> set queue}"
                     and r="(=)"
                     and r'="(=)"
                  in corres_mapM_scheme; (solves fastforce)?)
             apply (clarsimp simp: liftM_def[symmetric])
             apply (rule corres_guard_imp)
               apply (rule corres_split[OF getThreadState_corres])
                 apply (rule_tac F="\<exists>pl. st = Structures_A.BlockedOnSend epptr pl"
                              in corres_gen_asm)
                 apply (rule corres_if2[where Q=\<top> and Q'=\<top>])
                   apply (clarsimp simp: blocking_ipc_badge_def blockingIPCBadge_def
                                  split: thread_state.splits)
                  apply (clarsimp simp: o_def dc_def[symmetric] liftM_def)
                  apply (rule corres_guard_imp)
                    apply (rule corres_split[OF restart_thread_if_no_fault_corres])
                      unfolding restartThreadIfNoFault_def
                      apply (rule corres_return_eq_same, simp)
                     apply (rule hoare_TrueI[where P=\<top>])
                    apply (rule hoare_TrueI[where P=\<top>])
                   apply simp+
                apply (wpsimp wp: gts_wp)
               apply (wpsimp wp: gts_wp')
              apply (clarsimp simp: st_tcb_def2 st_tcb_at_refs_of_rev valid_sched_def
                              dest!: state_refs_of_elemD)
             apply (clarsimp simp: st_tcb_def2 st_tcb_at_refs_of_rev)
            apply (wpsimp wp: gts_wp)
           apply (wpsimp wp: sts_st_tcb_at'_cases threadGet_wp gts_wp' hoare_vcg_imp_lift
                       simp: obj_at_ko_at'_eq[where P=\<top>, simplified])
           apply (clarsimp simp: obj_at'_def pred_neg_def)
          apply (wpsimp wp: restart_thread_if_no_fault_valid_sched_blocked_on_send[where epptr=epptr]
                            gts_wp)
         apply (wpsimp wp: sts_weak_sch_act_wf sts_st_tcb_at'_cases hoare_vcg_imp_lift
                           setThreadState_valid_queues' threadGet_wp gts_wp'
                     simp: obj_at_ko_at'_eq[where P=\<top>, simplified])
         apply (fastforce simp: valid_tcb_state'_def obj_at'_def  st_tcb_at'_def
                                pred_neg_def weak_sch_act_wf_def)
        apply (rule corres_split[OF ])
           apply (rule setEndpoint_corres)
           apply (simp split: list.split add: ep_relation_def)
          apply (rule rescheduleRequired_corres)
         apply (wp weak_sch_act_wf_lift_linear)+
       apply (rule_tac Q="\<lambda>_ s. valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s
                                \<and> ep_at epptr s \<and> valid_sched s
                                \<and> heap_refs_inv (tcb_scps_of s) (sc_tcbs_of s)
                                \<and> current_time_bounded s"
                    in hoare_strengthen_post)
        apply (rule_tac Q="\<lambda>t s. tcb_at t s \<and> (epptr, TCBBlockedSend) \<in> state_refs_of s t
                                 \<and> t \<noteq> idle_thread s"
                     in ball_mapM_scheme)
          apply (wpsimp wp: restart_thread_if_no_fault_tcb_sts_of_other gts_wp)
         apply (wpsimp wp: restart_thread_if_no_fault_valid_sched_blocked_on_send[where epptr=epptr]
                           gts_wp)
        apply simp
       apply fastforce
      apply (rule_tac Q="(\<lambda>s. \<forall>t\<in>set queue. tcb_at' t s \<and> st_tcb_at' (not runnable') t s)
                         and (\<lambda>s. valid_tcbs' s \<and> weak_sch_act_wf (ksSchedulerAction s) s
                                  \<and> valid_queues s \<and> valid_queues' s \<and> valid_release_queue_iff s
                                  \<and> ep_at' epptr s)"
                   in hoare_weaken_pre[rotated], clarsimp)
       apply simp
      apply (rule hoare_strengthen_post)
       apply (rule_tac Q="\<lambda>t s. tcb_at' t s \<and> st_tcb_at' (not runnable') t s"
                    in ball_mapM_scheme)
         apply (wpsimp wp: sts_st_tcb_at'_cases threadGet_wp gts_wp' hoare_vcg_imp_lift
                     simp: obj_at_ko_at'_eq[where P=\<top>, simplified])
         apply (clarsimp simp: obj_at'_def pred_neg_def)
        apply (wpsimp wp: sts_st_tcb_at'_cases threadGet_wp gts_wp' hoare_vcg_imp_lift
                    simp: obj_at_ko_at'_eq[where P=\<top>, simplified])
        apply (fastforce simp: valid_tcb_state'_def obj_at'_def  st_tcb_at'_def
                               pred_neg_def weak_sch_act_wf_def)
       apply simp
      apply simp
     apply (wpsimp wp: hoare_vcg_ball_lift)
    apply (wpsimp wp: hoare_vcg_ball_lift)
   apply (clarsimp simp: obj_at_def is_ep_def cong: conj_cong)
   apply (prop_tac "valid_ep (Structures_A.SendEP queue) s")
    apply (fastforce simp: valid_objs_def valid_obj_def
                     dest: invs_valid_objs)
   apply (intro conjI impI allI ballI; (fastforce simp: valid_ep_def obj_at_def is_tcb_def)?)
    apply (fastforce intro: in_send_ep_queue_TCBBlockedSend)
   apply (rule not_idle_tcb_in_SendEp; fastforce)
  apply (clarsimp cong: conj_cong)
  apply (prop_tac "valid_ep' (Structures_H.SendEP queue) s")
   apply (fastforce simp: valid_objs'_def valid_obj'_def obj_at'_def
                    dest: invs_valid_objs')
  apply (intro conjI impI ballI; (fastforce simp: valid_ep'_def obj_at'_def)?)
  apply (frule (2) in_send_ep_queue_TCBBlockedSend')
   apply fastforce
  apply (fastforce simp: st_tcb_at_refs_of_rev' st_tcb_at'_def obj_at'_def pred_neg_def)
  done

crunches schedContextCancelYieldTo, tcbReleaseRemove
  for tcbQueued[wp]: "obj_at' (\<lambda>obj. \<not> tcbQueued obj) t"
  (wp: crunch_wps simp: crunch_simps setReleaseQueue_def setReprogramTimer_def getReleaseQueue_def)

lemma suspend_unqueued:
  "\<lbrace>\<top>\<rbrace> suspend t \<lbrace>\<lambda>rv. obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  apply (simp add: suspend_def unless_def tcbSchedDequeue_def)
  apply (wp hoare_vcg_if_lift hoare_vcg_conj_lift hoare_vcg_imp_lift)
          apply (wpsimp simp: threadGet_getObject comp_def wp: getObject_tcb_wp)+
      apply (rule hoare_strengthen_post, rule hoare_post_taut)
      apply (fastforce simp: obj_at'_def)
     apply (rule hoare_post_taut)
    apply wpsimp+
  done

crunch unqueued: prepareThreadDelete "obj_at' (Not \<circ> tcbQueued) t"
crunch inactive: prepareThreadDelete "st_tcb_at' ((=) Inactive) t'"
crunch nonq: prepareThreadDelete " \<lambda>s. \<forall>d p. t' \<notin> set (ksReadyQueues s (d, p))"

end
end
