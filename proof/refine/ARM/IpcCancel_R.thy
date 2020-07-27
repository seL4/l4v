(*
 * Copyright 2014, General Dynamics C4 Systems
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

crunch aligned'[wp]: cancelAllIPC pspace_aligned'
  (wp: crunch_wps mapM_x_wp' simp: unless_def crunch_simps)
crunch distinct'[wp]: cancelAllIPC pspace_distinct'
  (wp: crunch_wps mapM_x_wp' simp: unless_def crunch_simps)

crunch aligned'[wp]: cancelAllSignals pspace_aligned'
  (wp: crunch_wps mapM_x_wp')
crunch distinct'[wp]: cancelAllSignals pspace_distinct'
  (wp: crunch_wps mapM_x_wp')

lemma cancelSignal_simple[wp]:
  "\<lbrace>\<top>\<rbrace> cancelSignal t ntfn \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  apply (simp add: cancelSignal_def Let_def)
  apply (wp setThreadState_st_tcb | simp)+
  done

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
  (wp: crunch_wps cancelSignal_tcb_at' simp: crunch_simps pred_tcb_at'_def)

crunch pred_tcb_at'[wp]: emptySlot "pred_tcb_at' proj P t"
  (wp: setCTE_pred_tcb_at')

(* valid_queues is too strong *)
definition valid_inQ_queues :: "KernelStateData_H.kernel_state \<Rightarrow> bool" where
  "valid_inQ_queues \<equiv>
     \<lambda>s. \<forall>d p. (\<forall>t\<in>set (ksReadyQueues s (d, p)). obj_at' (inQ d p) t s) \<and> distinct (ksReadyQueues s (d, p))"

defs capHasProperty_def:
  "capHasProperty ptr P \<equiv> cte_wp_at' (\<lambda>c. P (cteCap c)) ptr"
end

lemma cancelIPC_simple[wp]:
  "\<lbrace>\<top>\<rbrace> cancelIPC t \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  unfolding cancelIPC_def
  apply (wpsimp wp: setThreadState_st_tcb replyRemoveTCB_st_tcb_at'_Inactive cancelSignal_simple
                    replyUnlink_st_tcb_at'_wp set_reply'.set_wp gts_wp' threadSet_wp
              simp: Let_def tcb_obj_at'_pred_tcb'_set_obj'_iff)
  apply (clarsimp simp: st_tcb_at'_def o_def obj_at'_def isBlockedOnReply_def)
  done

(* Assume various facts about cteDeleteOne, proved in Finalise_R *)
locale delete_one_conc_pre =
  assumes delete_one_st_tcb_at:
    "\<And>P. (\<And>st. simple' st \<longrightarrow> P st) \<Longrightarrow>
     \<lbrace>st_tcb_at' P t\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  assumes delete_one_typ_at:
    "\<And>P. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  assumes delete_one_aligned:
    "\<lbrace>pspace_aligned'\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  assumes delete_one_distinct:
    "\<lbrace>pspace_distinct'\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  assumes delete_one_it:
    "\<And>P. \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> cteDeleteOne cap \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
  assumes delete_one_queues:
    "\<lbrace>Invariants_H.valid_queues and valid_objs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)\<rbrace>
     cteDeleteOne sl \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  assumes delete_one_inQ_queues:
    "\<lbrace>valid_inQ_queues\<rbrace> cteDeleteOne sl \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
  (* FIXME RT: not true any more: assumes delete_one_sch_act_simple:
    "\<lbrace>sch_act_simple\<rbrace> cteDeleteOne sl \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"  *)
  (* FIXME RT: not true any more: assumes delete_one_sch_act_not:
    "\<And>t. \<lbrace>sch_act_not t\<rbrace> cteDeleteOne sl \<lbrace>\<lambda>rv. sch_act_not t\<rbrace>" *)
  assumes delete_one_reply_st_tcb_at: (* FIXME RT: pre can probably be weakened *)
    "\<And>P t. \<lbrace>\<lambda>s. st_tcb_at' P t s \<and> (\<exists>t' r. cte_wp_at' (\<lambda>cte. cteCap cte = ReplyCap t' r) slot s)\<rbrace>
      cteDeleteOne slot
     \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
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
  supply getNotification_inv[wp del] set_ntfn'.get_inv[wp del]
  apply (wpsimp wp: setThreadState_st_tcb_at'_cases
                    hoare_drop_imp[where R="\<lambda>rv _. delete t (f rv) = []" for f]
                    hoare_drop_imp[where R="\<lambda>rv _. \<exists>a b. delete t (f rv) = a # b" for f])
  done

(* FIXME RT: move to... Bits_R? Proved by MikiT in #874 *)
lemma sym_ref_Receive_or_Reply_replyTCB:
  "\<lbrakk> sym_refs (state_refs_of' s); ko_at' tcb tp s;
     tcbState tcb = BlockedOnReceive ep pl (Some rp)
     \<or> tcbState tcb = BlockedOnReply (Some rp) \<rbrakk> \<Longrightarrow>
    \<exists>reply. ksPSpace s rp = Some (KOReply reply) \<and> replyTCB reply = Some tp"
  apply (drule (1) sym_refs_obj_atD'[rotated, where p=tp])
  apply (clarsimp simp: state_refs_of'_def projectKOs obj_at'_def)
  apply (clarsimp simp: ko_wp_at'_def)
  apply (erule disjE; clarsimp)
  apply (rename_tac koa; case_tac koa;
         simp add: get_refs_def2 ep_q_refs_of'_def ntfn_q_refs_of'_def
                   tcb_st_refs_of'_def tcb_bound_refs'_def
            split: endpoint.split_asm ntfn.split_asm thread_state.split_asm if_split_asm)+
  done

lemma cancelIPC_simple'_not_awaiting_reply:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of' s)\<rbrace>
   cancelIPC t
   \<lbrace>\<lambda>_. st_tcb_at' ((=) Running or (=) Inactive or (=) Restart or (=) IdleThreadState) t\<rbrace>"
  unfolding cancelIPC_def Let_def getBlockingObject_def
  apply (wpsimp wp: sts_st_tcb_at'_cases hoare_vcg_all_lift hoare_vcg_imp_lift
                    hoare_pre_cont[where a="getEndpoint x" and P="\<lambda>rv _. P rv" for x P]
                    hoare_disjI2[where f="getEndpoint x" and Q="\<lambda>_. tcb_at' y" for x y]
                    replyUnlink_st_tcb_at'_sym_ref replyRemoveTCB_st_tcb_at'_sym_ref
                    cancelSignal_st_tcb_at' threadSet_pred_tcb_at_state[where p=t] gts_wp')
  apply (rule conjI; clarsimp)
   apply normalise_obj_at'
   apply (rename_tac rptr tcb reply)
   apply (erule notE)
   apply (frule(1) sym_ref_Receive_or_Reply_replyTCB, fast)
   apply (clarsimp simp: obj_at'_def projectKO_eq project_inject)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

context begin interpretation Arch .
crunch typ_at'[wp]: emptySlot "\<lambda>s. P (typ_at' T p s)"
end

context delete_one_conc_pre
begin

lemmas delete_one_typ_ats[wp] = typ_at_lifts [OF delete_one_typ_at]

end

declare if_weak_cong [cong]
declare delete_remove1 [simp]
declare delete.simps [simp del]

lemma invs_weak_sch_act_wf[elim!]:
  "invs' s \<Longrightarrow> weak_sch_act_wf (ksSchedulerAction s) s"
  apply (drule invs_sch_act_wf')
  apply (clarsimp simp: weak_sch_act_wf_def)
  done

(* FIXME RT: move to TcbAcc_R and replace gts_wf' with this *)
lemma gts_wf''[wp]:
  "\<lbrace>valid_objs'\<rbrace> getThreadState t \<lbrace>valid_tcb_state'\<rbrace>"
  apply (simp add: getThreadState_def threadGet_def liftM_def)
  apply (wp getObject_tcb_wp)
  apply clarsimp
  apply (drule obj_at_ko_at', clarsimp)
  apply (frule ko_at_valid_objs', fastforce, simp add: projectKOs)
  apply (fastforce simp: valid_obj'_def valid_tcb'_def)
  done

lemma replyUnlink_valid_objs':
  "\<lbrace>valid_objs' and reply_at' rptr\<rbrace>
    replyUnlink rptr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (clarsimp simp: replyUnlink_def setReplyTCB_def getReplyTCB_def liftM_def)
  apply (wpsimp wp: set_reply_valid_objs' hoare_vcg_all_lift
              simp: valid_tcb_state'_def)
  apply (frule (1) ko_at_valid_objs'[where 'a=reply, simplified])
   apply (clarsimp simp: projectKO_opt_reply split: kernel_object.splits)
  apply (clarsimp simp: valid_obj'_def valid_reply'_def obj_at'_def)
  done

lemma setReplyTCB_corres:
  "corres dc (reply_at rp) (reply_at' rp)
            (set_reply_obj_ref reply_tcb_update rp new)
            (setReplyTCB new rp)"
  apply (simp add: update_sk_obj_ref_def setReplyTCB_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ get_reply_corres])
      apply (rule set_reply_corres)
      apply (simp add: reply_relation_def)
  by (wpsimp simp: obj_at'_def replyNext_same_def)+

lemma reply_unlink_tcb_corres:
  "\<lbrakk>st = Structures_A.BlockedOnReceive ep (Some rp) pl
    \<or> st = Structures_A.BlockedOnReply rp\<rbrakk> \<Longrightarrow>
   corres dc
     (valid_objs and pspace_aligned and pspace_distinct
       and st_tcb_at ((=) st) t and reply_tcb_reply_at ((=) (Some t)) rp)
          (valid_objs' and valid_release_queue_iff)
        (reply_unlink_tcb t rp) (replyUnlink rp)" (is "_ \<Longrightarrow> corres _ _ ?conc_guard _ _")
  apply (rule_tac Q="?conc_guard
              and st_tcb_at' (\<lambda>st. st = BlockedOnReceive ep (receiver_can_grant pl) (Some rp)
                                 \<or> st = BlockedOnReply (Some rp)) t" in corres_cross_over_guard)
   apply clarsimp
   apply (drule (1) st_tcb_at_coerce_concrete; clarsimp simp: state_relation_def)
   apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  apply (simp add: reply_unlink_tcb_def replyUnlink_def getReplyTCB_def liftM_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ get_reply_corres])
      apply (rule corres_assert_gen_asm_l)
      apply (rename_tac reply'; prop_tac "replyTCB reply' = Some t")
       apply (clarsimp simp: reply_relation_def)
      apply simp
      apply (rule corres_split[OF _ gts_corres])
        apply (rule corres_assert_assume_l)
        apply (rule corres_split [OF _ setReplyTCB_corres])
          apply (rule sts_corres)
          apply (clarsimp simp: thread_state_relation_def)
         apply wpsimp
        apply (wpsimp simp: setReplyTCB_def)
       apply (wpsimp wp: hoare_vcg_disj_lift gts_wp get_simple_ko_wp)+
   apply (clarsimp simp: sk_obj_at_pred_def obj_at_def is_reply pred_tcb_at_def is_tcb)
  apply (prop_tac "reply_at' rp s")
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
   apply (erule (1) valid_objsE')
   apply (fastforce simp: valid_obj'_def projectKOs valid_tcb'_def valid_tcb_state'_def obj_at'_def)
  apply (clarsimp simp: obj_at'_def projectKOs pred_tcb_at'_def invs'_def valid_state'_def valid_pspace'_def)
  apply (erule (1) valid_objsE'[where x=rp])
  apply (clarsimp simp: valid_obj'_def valid_reply'_def)
  done

lemma blocked_cancel_ipc_corres:
  "\<lbrakk> st = Structures_A.BlockedOnReceive epPtr p' pl \<or>
     st = Structures_A.BlockedOnSend epPtr p; thread_state_relation st st' \<rbrakk> \<Longrightarrow>
   corres dc (invs and st_tcb_at ((=) st) t) (invs' and st_tcb_at' ((=) st') t)
           (blocked_cancel_ipc st t reply_opt)
           (do ep \<leftarrow> getEndpoint epPtr;
               y \<leftarrow> assert (\<not> (case ep of IdleEP \<Rightarrow> True | _ \<Rightarrow> False));
               ep' \<leftarrow>
               if remove1 t (epQueue ep) = [] then return IdleEP
               else
                 return $ epQueue_update (%_. (remove1 t (epQueue ep))) ep;
               y \<leftarrow> setEndpoint epPtr ep';
               setThreadState Structures_H.thread_state.Inactive t
            od)"
  sorry (* FIXME RT: needs statement update
  apply (simp add: blocked_cancel_ipc_def gbep_ret)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_ep_corres])
      apply (rule_tac F="ep \<noteq> IdleEP" in corres_gen_asm2)
      apply (rule corres_assert_assume[rotated])
       apply (clarsimp split: endpoint.splits)
      apply (rule_tac P="invs and st_tcb_at ((=) st) t" and
                      P'="invs' and st_tcb_at' ((=) st') t" in corres_inst)
      apply (case_tac rv)
        apply (simp add: ep_relation_def)
       apply (simp add: get_ep_queue_def ep_relation_def split del: if_split)
       apply (rename_tac list)
       apply (case_tac "remove1 t list")
        apply simp
        apply (rule corres_guard_imp)
          apply (rule corres_split [OF _ set_ep_corres])
             apply (rule sts_corres)
             apply simp
            apply (simp add: ep_relation_def)
           apply (simp add: valid_tcb_state_def pred_conj_def)
           apply (wp weak_sch_act_wf_lift)+
         apply (clarsimp simp: st_tcb_at_tcb_at)
         apply (clarsimp simp: st_tcb_at_def obj_at_def)
         apply (erule pspace_valid_objsE)
          apply fastforce
         apply (auto simp: valid_tcb_state_def valid_tcb_def
                           valid_obj_def obj_at_def)[1]
        apply (clarsimp simp: pred_tcb_at')
        apply (clarsimp simp: pred_tcb_at'_def)
        apply (drule obj_at_ko_at')
        apply clarify
        apply (drule ko_at_valid_objs')
          apply fastforce
         apply (simp add: projectKOs)
        apply (auto simp add: valid_obj'_def valid_tcb'_def
                              valid_tcb_state'_def)[1]
       apply clarsimp
       apply (rule corres_guard_imp)
         apply (rule corres_split [OF _ set_ep_corres])
            apply (rule sts_corres)
            apply simp
           apply (simp add: ep_relation_def)
          apply (wp)+
        apply (clarsimp simp: st_tcb_at_tcb_at)
        apply (clarsimp simp: st_tcb_at_def obj_at_def)
        apply (erule pspace_valid_objsE)
         apply fastforce
        apply (auto simp: valid_tcb_state_def valid_tcb_def
                          valid_obj_def obj_at_def)[1]
       apply (clarsimp simp: pred_tcb_at')
       apply (clarsimp simp: pred_tcb_at'_def)
       apply (drule obj_at_ko_at')
       apply clarify
       apply (drule ko_at_valid_objs')
         apply fastforce
        apply (simp add: projectKOs)
       apply (auto simp add: valid_obj'_def valid_tcb'_def
                             valid_tcb_state'_def)[1]
      apply (simp add: get_ep_queue_def ep_relation_def split del: if_split)
      apply (rename_tac list)
      apply (case_tac "remove1 t list")
       apply simp
       apply (rule corres_guard_imp)
         apply (rule corres_split [OF _ set_ep_corres])
            apply (rule sts_corres)
            apply simp
           apply (simp add: ep_relation_def)
          apply (simp add: valid_tcb_state_def pred_conj_def)
          apply (wp weak_sch_act_wf_lift)+
        apply (clarsimp simp: st_tcb_at_tcb_at)
        apply (clarsimp simp: st_tcb_at_def obj_at_def)
        apply (erule pspace_valid_objsE)
         apply fastforce
        apply (auto simp: valid_tcb_state_def valid_tcb_def
                          valid_obj_def obj_at_def)[1]
       apply (clarsimp simp: pred_tcb_at')
       apply (clarsimp simp: pred_tcb_at'_def)
       apply (drule obj_at_ko_at')
       apply clarify
       apply (drule ko_at_valid_objs')
         apply fastforce
        apply (simp add: projectKOs)
       apply (auto simp add: valid_obj'_def valid_tcb'_def
                             valid_tcb_state'_def)[1]
      apply clarsimp
      apply (rule corres_guard_imp)
        apply (rule corres_split [OF _ set_ep_corres])
           apply (rule sts_corres)
           apply simp
          apply (simp add: ep_relation_def)
         apply (wp)+
       apply (clarsimp simp: st_tcb_at_tcb_at)
       apply (clarsimp simp: st_tcb_at_def obj_at_def)
       apply (erule pspace_valid_objsE)
        apply fastforce
       apply (auto simp: valid_tcb_state_def valid_tcb_def
                         valid_obj_def obj_at_def)[1]
      apply (clarsimp simp: pred_tcb_at')
      apply (clarsimp simp: pred_tcb_at'_def)
      apply (drule obj_at_ko_at')
      apply clarify
      apply (drule ko_at_valid_objs')
        apply fastforce
       apply (simp add: projectKOs)
      apply (auto simp add: valid_obj'_def valid_tcb'_def
                            valid_tcb_state'_def)[1]
     apply (wp getEndpoint_wp)+
   apply (clarsimp simp: st_tcb_at_def obj_at_def)
   apply (erule pspace_valid_objsE)
    apply fastforce
   apply (auto simp: valid_tcb_state_def valid_tcb_def
                     valid_obj_def obj_at_def)[1]
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: pred_tcb_at'_def)
   apply (drule obj_at_ko_at')
   apply clarify
   apply (drule ko_at_valid_objs')
     apply fastforce
    apply (simp add: projectKOs)
   apply (auto simp add: valid_obj'_def valid_tcb'_def
                         valid_tcb_state'_def)[1]
  apply (fastforce simp: ko_wp_at'_def obj_at'_def projectKOs dest: sym_refs_st_tcb_atD')
  done *)

lemma cancel_signal_corres:
  "corres dc
          (invs and st_tcb_at ((=) (Structures_A.BlockedOnNotification ntfn)) t)
          (invs' and st_tcb_at' ((=) (BlockedOnNotification ntfn)) t)
          (cancel_signal t ntfn)
          (cancelSignal t ntfn)"
  apply (simp add: cancel_signal_def cancelSignal_def Let_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_ntfn_corres])
      apply (rule_tac F="isWaitingNtfn (ntfnObj ntfnaa)" in corres_gen_asm2)
      apply (case_tac "ntfn_obj ntfna"; simp add: ntfn_relation_def isWaitingNtfn_def)
      apply (case_tac "ntfna", case_tac "ntfnaa")
      apply clarsimp
      apply wpfix
      apply (rename_tac list bound_tcb sc)
      apply (rule_tac R="remove1 t list = []" in corres_cases')
       apply (simp del: dc_simp)
       apply (rule corres_split [OF _ set_ntfn_corres])
          apply (rule sts_corres)
          apply simp
         apply (simp add: ntfn_relation_def)
        apply (wp abs_typ_at_lifts)+
      apply (simp add: list_case_If del: dc_simp)
      apply (rule corres_split [OF _ set_ntfn_corres])
         apply (rule sts_corres)
         apply simp
        apply (clarsimp simp add: ntfn_relation_def neq_Nil_conv)
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
    apply (simp add: projectKOs)
   apply (clarsimp simp: valid_obj'_def valid_tcb'_def valid_tcb_state'_def)
   apply (drule sym, simp)
  apply clarsimp
  apply (rule context_conjI)
   apply (drule sym_refs_st_tcb_atD', fastforce)
   apply (fastforce simp: isWaitingNtfn_def ko_wp_at'_def obj_at'_def projectKOs
                        ntfn_bound_refs'_def get_refs_def
                 split: Structures_H.notification.splits ntfn.splits option.splits)
  apply (frule ko_at_valid_objs', fastforce)
   apply (clarsimp simp: projectKO_opt_ntfn split: kernel_object.splits)
  apply (fastforce simp: valid_obj'_def valid_ntfn'_def isWaitingNtfn_def
                  split: option.splits ntfn.splits)
  done

lemma cte_map_tcb_2:
  "cte_map (t, tcb_cnode_index 2) = t + 2*2^cte_level_bits"
  by (simp add: cte_map_def tcb_cnode_index_def to_bl_1)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma reply_mdbNext_is_descendantD:
  assumes sr: "(s, s') \<in> state_relation"
  and   invs: "invs' s'"
  and    tcb: "tcb_at t s"
  and    cte: "ctes_of s' (t + 0x20) = Some cte"
  and   desc: "descendants_of (t, tcb_cnode_index 2) (cdt s) = {sl}"
  shows       "mdbNext (cteMDBNode cte) = cte_map sl"
proof -
  from tcb have "cte_at (t, tcb_cnode_index 2) s"
    by (simp add: tcb_at_cte_at dom_tcb_cap_cases)
  hence "descendants_of' (t + 2*2^cte_level_bits) (ctes_of s') = {cte_map sl}"
    using sr desc
    by (fastforce simp: state_relation_def cdt_relation_def cte_map_def tcb_cnode_index_def)
  thus ?thesis
    using cte invs
    apply (clarsimp simp: descendants_of'_def)
    apply (frule singleton_eqD, drule CollectD)
    apply (erule subtree.cases)
     apply (clarsimp simp: mdb_next_rel_def mdb_next_def cte_level_bits_def)
    apply (subgoal_tac "c' = cte_map sl")
     apply (fastforce dest: invs_no_loops no_loops_direct_simp)
    apply fastforce
    done
qed
end

locale delete_one_conc = delete_one_conc_pre +
  assumes delete_one_invs:
    "\<And>p. \<lbrace>invs'\<rbrace> cteDeleteOne p \<lbrace>\<lambda>rv. invs'\<rbrace>"

locale delete_one = delete_one_conc + delete_one_abs +
  assumes delete_one_corres:
    "corres dc (einvs and cte_wp_at can_fast_finalise ptr)
               (invs' and cte_at' (cte_map ptr))
          (cap_delete_one ptr) (cteDeleteOne (cte_map ptr))"

lemma (in delete_one) cancel_ipc_corres:
  "corres dc (einvs and tcb_at t) (invs' and tcb_at' t)
      (cancel_ipc t) (cancelIPC t)"
  apply (simp add: cancel_ipc_def cancelIPC_def Let_def)
  apply (rule corres_guard_imp)
  sorry (*
    apply (rule corres_split [OF _ gts_corres])
      apply (rule_tac P="einvs and st_tcb_at ((=) state) t" and
                      P'="invs' and st_tcb_at' ((=) statea) t" in corres_inst)
      apply (case_tac state, simp_all add: isTS_defs list_case_If)[1]
         apply (rule corres_guard_imp)
           apply (rule blocked_cancel_ipc_corres)
            apply fastforce
           apply fastforce
          apply simp
         apply simp
        apply (clarsimp simp add: isTS_defs list_case_If)
        apply (rule corres_guard_imp)
          apply (rule blocked_cancel_ipc_corres)
           apply fastforce
          apply fastforce
         apply simp
        apply simp
       apply (rule corres_guard_imp)
         apply (rule reply_cancel_ipc_corres)
        apply (clarsimp elim!: st_tcb_weakenE)
       apply (clarsimp elim!: pred_tcb'_weakenE)
      apply (rule corres_guard_imp [OF cancel_signal_corres], simp+)
     apply (wp gts_sp[where P="\<top>",simplified])+
    apply (rule hoare_strengthen_post)
     apply (rule gts_sp'[where P="\<top>"])
    apply (clarsimp elim!: pred_tcb'_weakenE)
   apply simp
  apply simp
  done *)

lemma setNotification_utr[wp]:
  "\<lbrace>untyped_ranges_zero'\<rbrace> setNotification ntfn nobj \<lbrace>\<lambda>rv. untyped_ranges_zero'\<rbrace>"
  apply (simp add: cteCaps_of_def)
  apply (rule hoare_pre, wp untyped_ranges_zero_lift)
  apply (simp add: o_def)
  done

lemma setEndpoint_utr[wp]:
  "\<lbrace>untyped_ranges_zero'\<rbrace> setEndpoint p ep \<lbrace>\<lambda>rv. untyped_ranges_zero'\<rbrace>"
  apply (simp add: cteCaps_of_def)
  apply (rule hoare_pre, wp untyped_ranges_zero_lift)
  apply (simp add: o_def)
  done

declare cart_singleton_empty [simp]
declare cart_singleton_empty2[simp]

lemma sch_act_simple_not_t[simp]: "sch_act_simple s \<Longrightarrow> sch_act_not t s"
  by (clarsimp simp: sch_act_simple_def)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma cancelSignal_invs':
  "\<lbrace>invs' and st_tcb_at' (\<lambda>st. st = BlockedOnNotification ntfn) t and sch_act_not t\<rbrace>
    cancelSignal t ntfn \<lbrace>\<lambda>rv. invs'\<rbrace>"
  proof -
    have NIQ: "\<And>s. \<lbrakk> Invariants_H.valid_queues s; st_tcb_at' (Not \<circ> runnable') t s \<rbrakk>
                                         \<Longrightarrow> \<forall>x. t \<notin> set (ksReadyQueues s x)"
      apply (clarsimp simp add: pred_tcb_at'_def Invariants_H.valid_queues_def
                                valid_queues_no_bitmap_def)
      apply (drule spec | drule(1) bspec | clarsimp simp: obj_at'_def inQ_def)+
      done
    have NTFNSN: "\<And>ntfn ntfn'.
                    \<lbrace>\<lambda>s. sch_act_not (ksCurThread s) s \<rbrace> setNotification ntfn ntfn'
                    \<lbrace>\<lambda>_ s. sch_act_not (ksCurThread s) s\<rbrace>"
      apply (rule hoare_weaken_pre)
       apply (wps)
       apply (wp, simp)
      done
    show ?thesis
      apply (simp add: cancelSignal_def invs'_def valid_state'_def Let_def)
      apply (wp valid_irq_node_lift sts_sch_act' irqs_masked_lift
                hoare_vcg_all_lift [OF set_ntfn'.ksReadyQueues] sts_valid_queues
                setThreadState_ct_not_inQ NTFNSN
                hoare_vcg_all_lift set_ntfn'.ksReadyQueues
              | simp add: valid_tcb_state'_def list_case_If split del: if_split)+
       prefer 2
       apply assumption
      apply (rule hoare_strengthen_post)
       apply (rule get_ntfn_sp')
      apply (clarsimp simp: pred_tcb_at')
      apply (frule NIQ)
       apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
      apply (rule conjI)
       apply (clarsimp simp: valid_ntfn'_def)
       apply (case_tac "ntfnObj r", simp_all add: isWaitingNtfn_def)
       apply (frule ko_at_valid_objs')
         apply (simp add: valid_pspace_valid_objs')
        apply (clarsimp simp: projectKO_opt_ntfn split: kernel_object.splits)
       apply (simp add: valid_obj'_def valid_ntfn'_def)
       apply (frule st_tcb_at_state_refs_ofD')
       apply (frule ko_at_state_refs_ofD')
       apply (rule conjI, erule delta_sym_refs)
         apply (fastforce simp: ntfn_bound_refs'_def get_refs_def2
                         split: if_split_asm)
        apply (clarsimp split: if_split_asm)
          subgoal
          by (auto simp: symreftype_inverse' ntfn_bound_refs'_def tcb_bound_refs'_def
                         ntfn_q_refs_of'_def obj_at'_def projectKOs
                  split: ntfn.splits option.splits)
         subgoal
         by (auto simp: symreftype_inverse' ntfn_bound_refs'_def tcb_bound_refs'_def
                        get_refs_def2
                 split: option.splits)
        subgoal
        by (fastforce simp: symreftype_inverse' ntfn_bound_refs'_def
                            tcb_bound_refs'_def ntfn_q_refs_of'_def remove1_empty
                     split: ntfn.splits)
       apply (rule conjI, erule_tac rfs'="list_refs_of_replies' s" in delta_sym_refs)
         subgoal
         by (auto simp: symreftype_inverse' list_refs_of_replies'_def
                        get_refs_def2 opt_map_def
                 split: option.splits)
        subgoal
        by (auto simp: symreftype_inverse' list_refs_of_replies'_def
                       get_refs_def2 opt_map_def
                split: option.splits)
       apply (rule conjI)
        apply (fastforce simp: get_refs_def elim!: if_live_state_refsE split: option.splits)
       apply (fastforce simp: sym_refs_def dest!: idle'_only_sc_refs)
      apply (case_tac "ntfnObj r", simp_all)
      apply (frule obj_at_valid_objs', clarsimp)
      apply (clarsimp simp: projectKOs valid_obj'_def valid_ntfn'_def)
      apply (rule conjI, clarsimp split: option.splits)
      apply (frule st_tcb_at_state_refs_ofD')
      apply (frule ko_at_state_refs_ofD')
      apply (rule conjI, erule delta_sym_refs)
        apply (fastforce simp: ntfn_bound_refs'_def get_refs_def2
                        split: if_split_asm option.splits)
       apply (clarsimp split: if_split_asm)
        subgoal
        by (auto simp: symreftype_inverse' ntfn_bound_refs'_def tcb_bound_refs'_def
                       get_refs_def2 set_eq_subset
                split: option.splits)
       subgoal
       by (auto simp: symreftype_inverse' ntfn_bound_refs'_def tcb_bound_refs'_def
                      get_refs_def2 set_eq_subset
               split: option.splits)
      apply (rule conjI, erule_tac rfs'="list_refs_of_replies' s" in delta_sym_refs)
        subgoal
        by (auto simp: symreftype_inverse' list_refs_of_replies'_def
                       get_refs_def2 opt_map_def
                split: option.splits)
       subgoal
       by (auto simp: symreftype_inverse' list_refs_of_replies'_def
                      get_refs_def2 opt_map_def
               split: option.splits)
      apply (rule conjI)
       apply (fastforce simp: get_refs_def elim!: if_live_state_refsE split: option.splits)
      apply (rule conjI)
       apply (case_tac "ntfnBoundTCB r")
        apply (clarsimp elim!: if_live_state_refsE)+
      apply (clarsimp dest!: idle'_only_sc_refs)
      done
  qed

lemma ep_redux_simps3:
  "ep_q_refs_of' (case xs of [] \<Rightarrow> IdleEP | y # ys \<Rightarrow> RecvEP (y # ys))
        = (set xs \<times> {EPRecv})"
  "ep_q_refs_of' (case xs of [] \<Rightarrow> IdleEP | y # ys \<Rightarrow> SendEP (y # ys))
        = (set xs \<times> {EPSend})"
  by (fastforce split: list.splits simp: valid_ep_def valid_ntfn_def)+

lemma setEndpoint_pde_mappings'[wp]:
  "\<lbrace>valid_pde_mappings'\<rbrace> setEndpoint ptr val \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  by (wp valid_pde_mappings_lift')

end

lemma (in delete_one_conc) cancelIPC_invs[wp]:
  shows "\<lbrace>tcb_at' t and invs'\<rbrace> cancelIPC t \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  have P: "\<And>xs v f. (case xs of [] \<Rightarrow> return v | y # ys \<Rightarrow> return (f (y # ys)))
                         = return (case xs of [] \<Rightarrow> v | y # ys \<Rightarrow> f xs)"
    by (clarsimp split: list.split)
  have NIQ: "\<And>s. \<lbrakk> Invariants_H.valid_queues s; st_tcb_at' (Not \<circ> runnable') t s \<rbrakk>
                                       \<Longrightarrow> \<forall>x. t \<notin> set (ksReadyQueues s x)"
    apply (clarsimp simp add: pred_tcb_at'_def Invariants_H.valid_queues_def valid_queues_no_bitmap_def)
    apply (drule spec | drule(1) bspec | clarsimp simp: obj_at'_def inQ_def)+
    done
  have Q:
    "\<And>epptr. \<lbrace>st_tcb_at' (\<lambda>st. \<exists>a pl. (st = BlockedOnReceive epptr a pl)
                            \<or> (\<exists>a b c d. st = BlockedOnSend epptr a b c d)) t
                  and invs'\<rbrace>
      do ep \<leftarrow> getEndpoint epptr;
         y \<leftarrow> assert (\<not> (case ep of IdleEP \<Rightarrow> True | _ \<Rightarrow> False));
         ep' \<leftarrow> case remove1 t (epQueue ep)
                of [] \<Rightarrow> return Structures_H.endpoint.IdleEP
                | x # xs \<Rightarrow> return (epQueue_update (%_. x # xs) ep);
         y \<leftarrow> setEndpoint epptr ep';
         setThreadState Inactive t
      od \<lbrace>\<lambda>rv. invs'\<rbrace>"
    apply (simp add: invs'_def valid_state'_def)
    apply (subst P)
    apply (wp valid_irq_node_lift valid_global_refs_lift' valid_arch_state_lift'
              irqs_masked_lift sts_sch_act'
              sts_valid_queues setThreadState_ct_not_inQ
              hoare_vcg_all_lift
              | simp add: valid_tcb_state'_def split del: if_split
              | wpc)+
     prefer 2
  sorry (*
     apply assumption
    apply (rule hoare_strengthen_post [OF get_ep_sp'])
    apply (clarsimp simp: pred_tcb_at' fun_upd_def[symmetric] conj_comms  o_def
               split del: if_split cong: if_cong)
    apply (rule conjI, clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def projectKOs)
    apply (frule obj_at_valid_objs', clarsimp)
    apply (clarsimp simp: projectKOs valid_obj'_def)
    apply (rule conjI)
     apply (clarsimp simp: obj_at'_def valid_ep'_def projectKOs
                    dest!: pred_tcb_at')
    apply (frule NIQ)
     apply (erule pred_tcb'_weakenE, fastforce)
    apply (clarsimp, rule conjI)
     apply (auto simp: pred_tcb_at'_def obj_at'_def)[1]
    apply (rule conjI)
     apply (clarsimp split: Structures_H.endpoint.split_asm list.split
                      simp: valid_ep'_def)
      apply (rename_tac list x xs)
      apply (frule distinct_remove1[where x=t])
      apply (cut_tac xs=list in set_remove1_subset[where x=t])
      apply auto[1]
     apply (rename_tac list x xs)
     apply (frule distinct_remove1[where x=t])
     apply (cut_tac xs=list in set_remove1_subset[where x=t])
     apply auto[1]
    apply (frule(1) sym_refs_ko_atD')
    apply (rule conjI)
     apply (clarsimp elim!: if_live_state_refsE split: Structures_H.endpoint.split_asm)
    apply (drule st_tcb_at_state_refs_ofD')
    apply (clarsimp simp: ep_redux_simps3 valid_ep'_def
                   split: Structures_H.endpoint.split_asm
                    cong: list.case_cong)
     apply (frule_tac x=t in distinct_remove1)
     apply (frule_tac x=t in set_remove1_eq)
     by (auto elim!: delta_sym_refs
               simp: symreftype_inverse' tcb_st_refs_of'_def tcb_bound_refs'_def
              split: thread_state.splits if_split_asm) *)
  (* FIXME RT: can probably be removed
  have R:
    "\<lbrace>invs' and tcb_at' t\<rbrace>
     do y \<leftarrow> threadSet (\<lambda>tcb. tcb \<lparr> tcbFault := None \<rparr>) t;
        slot \<leftarrow> getThreadReplySlot t;
        callerCap \<leftarrow> liftM (mdbNext \<circ> cteMDBNode) (getCTE slot);
        when (callerCap \<noteq> nullPointer) (do
            y \<leftarrow> stateAssert (capHasProperty callerCap (\<lambda>cap. isReplyCap cap
                                                           \<and> \<not> capReplyMaster cap))
                [];
            cteDeleteOne callerCap
        od)
     od
     \<lbrace>\<lambda>rv. invs'\<rbrace>"
    unfolding getThreadReplySlot_def
    by (wp valid_irq_node_lift delete_one_invs hoare_drop_imps
           threadSet_invs_trivial irqs_masked_lift
      | simp add: o_def if_apply_def2
      | fastforce simp: inQ_def)+ *)
  show ?thesis
    apply (simp add:   cancelIPC_def crunch_simps
               cong:   if_cong list.case_cong)
  sorry (*
    apply (rule hoare_seq_ext [OF _ gts_sp'])
    apply (case_tac state,
           simp_all add: isTS_defs)
           apply (safe intro!: hoare_weaken_pre[OF Q]
                               hoare_weaken_pre[OF R]
                               hoare_weaken_pre[OF return_wp]
                               hoare_weaken_pre[OF cancelSignal_invs']
                       elim!: pred_tcb'_weakenE)
          apply (auto simp: pred_tcb_at'_def obj_at'_def
                      dest: invs_sch_act_wf')
  done *)
qed

crunches setReply, setSchedContext
  for sch_act_simple[wp]: sch_act_simple
  (simp: crunch_simps sch_act_simple_def wp: crunch_wps)

lemma replyUnlink_sch_act_simple[wp]:
  "replyUnlink t' \<lbrace>sch_act_simple\<rbrace>"
  apply (simp add: replyUnlink_def setReplyTCB_def getReplyTCB_def)
  by (wpsimp wp: hoare_drop_imps)

lemma replyRemoveTCB_sch_act_simple[wp]:
  "replyRemoveTCB t' \<lbrace>sch_act_simple\<rbrace>"
  supply if_split[split del]
  apply (simp add: replyRemoveTCB_def cleanReply_def)
  by (wpsimp wp: hoare_drop_imps hoare_vcg_if_lift hoare_vcg_all_lift)

crunch inv[wp]: getBlockingObject P

lemma (in delete_one_conc_pre) cancelIPC_sch_act_simple[wp]:
  "cancelIPC t \<lbrace>sch_act_simple\<rbrace>"
  apply (simp add: cancelIPC_def cancelSignal_def Let_def
             cong: if_cong Structures_H.thread_state.case_cong)
  by (wpsimp wp: hoare_drop_imps | rule sch_act_simple_lift)+

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
  "\<lbrace>st_tcb_at' P t\<rbrace>
     cancelIPC t'
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (simp add: cancelIPC_def Let_def
             cong: if_cong Structures_H.thread_state.case_cong)
  sorry (*
  apply (rule hoare_seq_ext [OF _ gts_sp'])
  apply (case_tac x, simp_all add: isTS_defs list_case_If)
         apply (wp sts_st_tcb_at'_cases delete_one_st_tcb_at
                   threadSet_pred_tcb_no_state
                   cancelSignal_st_tcb_at hoare_drop_imps
                | clarsimp simp: o_def if_fun_split)+
  done *)

lemma weak_sch_act_wf_lift_linear:
  "\<lbrakk> \<And>t. \<lbrace>\<lambda>s. sa s \<noteq> SwitchToThread t\<rbrace> f \<lbrace>\<lambda>rv s. sa s \<noteq> SwitchToThread t\<rbrace>;
     \<And>t. \<lbrace>st_tcb_at' runnable' t\<rbrace> f \<lbrace>\<lambda>rv. st_tcb_at' runnable' t\<rbrace>;
     \<And>t. \<lbrace>tcb_in_cur_domain' t\<rbrace> f \<lbrace>\<lambda>rv. tcb_in_cur_domain' t\<rbrace> \<rbrakk>
       \<Longrightarrow> \<lbrace>\<lambda>s. weak_sch_act_wf (sa s) s\<rbrace> f \<lbrace>\<lambda>rv s. weak_sch_act_wf (sa s) s\<rbrace>"
  apply (simp only: weak_sch_act_wf_def imp_conv_disj)
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift hoare_vcg_conj_lift)
  apply simp_all
  done

lemma sts_sch_act_not[wp]:
  "\<lbrace>sch_act_not t\<rbrace> setThreadState st t' \<lbrace>\<lambda>rv. sch_act_not t\<rbrace>"
  unfolding setThreadState_def rescheduleRequired_def scheduleTCB_def
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp isSchedulable_inv)
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

lemma cancelAllIPC_tcb_at_runnable':
  "\<lbrace>st_tcb_at' runnable' t\<rbrace> cancelAllIPC epptr \<lbrace>\<lambda>_. st_tcb_at' runnable' t\<rbrace>"
  unfolding cancelAllIPC_def
  apply (wpsimp wp: mapM_x_wp' hoare_vcg_if_lift setThreadState_st_tcb_at'_test_unaffected
                    threadGet_wp
              simp: o_def
         split_del: if_split)
  oops (*
  by (wpsimp wp: mapM_x_wp' sts_st_tcb' hoare_drop_imp) *)

lemma cancelAllSignals_tcb_at_runnable':
  "\<lbrace>st_tcb_at' runnable' t\<rbrace> cancelAllSignals ntfnptr \<lbrace>\<lambda>_. st_tcb_at' runnable' t\<rbrace>"
  unfolding cancelAllSignals_def
  sorry (*
  by (wpsimp wp: mapM_x_wp' sts_st_tcb' hoare_drop_imp) *)

crunches unbindNotification, bindNotification, unbindMaybeNotification
  for st_tcb_at'[wp]: "st_tcb_at' P p"
  (wp: threadSet_pred_tcb_no_state ignore: threadSet)

lemma (in delete_one_conc_pre) finaliseCap_tcb_at_runnable':
  "\<lbrace>st_tcb_at' runnable' t\<rbrace> finaliseCap cap final True \<lbrace>\<lambda>_. st_tcb_at' runnable' t\<rbrace>"
  apply (clarsimp simp add: finaliseCap_def Let_def)
  oops (*
  apply (rule conjI | clarsimp | wp cancelAllIPC_tcb_at_runnable' getObject_ntfn_inv
                                    cancelAllSignals_tcb_at_runnable'
       | wpc)+
  done *)

crunch pred_tcb_at'[wp]: isFinalCapability "pred_tcb_at' proj st t"
  (simp: crunch_simps)

lemma (in delete_one_conc_pre) cteDeleteOne_tcb_at_runnable':
  "\<lbrace>st_tcb_at' runnable' t\<rbrace> cteDeleteOne callerCap \<lbrace>\<lambda>_. st_tcb_at' runnable' t\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def)
  oops (*
  apply (wp finaliseCap_tcb_at_runnable' | clarsimp | wp (once) hoare_drop_imps)+
  done
*)

lemma (in delete_one_conc_pre) cancelIPC_tcb_at_runnable':
  "\<lbrace>st_tcb_at' runnable' t'\<rbrace> cancelIPC t \<lbrace>\<lambda>_. st_tcb_at' runnable' t'\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (clarsimp simp: cancelIPC_def Let_def)
  oops (*
  apply (case_tac "t'=t")
   apply (rule_tac B="\<lambda>st. st_tcb_at' runnable' t and K (runnable' st)"
            in hoare_seq_ext)
    apply(case_tac x; simp)
   apply (wpsimp wp: sts_pred_tcb_neq')+
           apply (rule_tac Q="\<lambda>rv. ?PRE" in hoare_post_imp, fastforce)
           apply (wp cteDeleteOne_tcb_at_runnable'
                    threadSet_pred_tcb_no_state
                    cancelSignal_tcb_at_runnable'
                    sts_pred_tcb_neq' hoare_drop_imps
                  | wpc | simp add: o_def if_fun_split)+
  done *)

crunch ksCurDomain[wp]: cancelSignal "\<lambda>s. P (ksCurDomain s)"
  (wp: crunch_wps)

lemma (in delete_one_conc_pre) cancelIPC_ksCurDomain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> cancelIPC t \<lbrace>\<lambda>_ s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: cancelIPC_def Let_def)
  apply (wp hoare_vcg_conj_lift delete_one_ksCurDomain
       | wpc
       | rule hoare_drop_imps
       | simp add: o_def if_fun_split)+
  sorry

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

(* FIXME RT: setBoundNotification should be simple_ko' *)
lemma setBoundNotification_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> setBoundNotification st t \<lbrace>\<lambda>_. tcb_in_cur_domain' t'\<rbrace>"
  apply (simp add: tcb_in_cur_domain'_def)
  apply (rule hoare_pre)
  apply wps
  apply (wp setBoundNotification_not_ntfn | simp)+
  done

lemma cancelSignal_tcb_obj_at':
  "(\<And>tcb st qd. P (tcb\<lparr>tcbState := st, tcbQueued := qd\<rparr>) \<longleftrightarrow> P tcb)
     \<Longrightarrow> cancelSignal t word \<lbrace>obj_at' P t'\<rbrace>"
  apply (simp add: cancelSignal_def)
  apply (wpsimp wp: setThreadState_not_st getNotification_wp)
  done

lemma (in delete_one_conc_pre) cancelIPC_tcbDomain_obj_at':
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace> cancelIPC t \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  apply (simp add: cancelIPC_def Let_def)
  apply (wp hoare_vcg_conj_lift
            setThreadState_not_st delete_one_tcbDomain_obj_at' cancelSignal_tcb_obj_at'
       | wpc
       | rule hoare_drop_imps
       | simp add: o_def if_fun_split)+
  sorry

lemma (in delete_one_conc_pre) cancelIPC_tcb_in_cur_domain':
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> cancelIPC t \<lbrace>\<lambda>_. tcb_in_cur_domain' t'\<rbrace>"
  apply (simp add: tcb_in_cur_domain'_def)
  apply (rule hoare_pre)
   apply wps
   apply (wp cancelIPC_tcbDomain_obj_at' | simp)+
  done

(* FIXME RT: not true any more
lemma (in delete_one_conc_pre) cancelIPC_sch_act_not:
  "\<lbrace>sch_act_not t'\<rbrace> cancelIPC t \<lbrace>\<lambda>_. sch_act_not t'\<rbrace>"
  apply (simp add: cancelIPC_def Let_def)
  apply (wp hoare_vcg_conj_lift
            delete_one_sch_act_not
       | wpc
       | simp add: o_def if_apply_def2
              split del: if_split
       | rule hoare_drop_imps)+
  oops *)

lemma (in delete_one_conc_pre) cancelIPC_weak_sch_act_wf:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
      cancelIPC t
   \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  oops (*
  apply (rule weak_sch_act_wf_lift_linear)
  apply (wp cancelIPC_sch_act_not cancelIPC_tcb_in_cur_domain' cancelIPC_tcb_at_runnable')+
  done *)

text \<open>The suspend operation, significant as called from delete\<close>

lemma rescheduleRequired_weak_sch_act_wf:
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: rescheduleRequired_def setSchedulerAction_def)
  apply (wp hoare_post_taut | simp add: weak_sch_act_wf_def)+
  done

lemma sts_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s
        \<and> (ksSchedulerAction s = SwitchToThread t \<longrightarrow> runnable' st)\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding setThreadState_def scheduleTCB_def
  apply (wpsimp wp: rescheduleRequired_weak_sch_act_wf hoare_vcg_if_lift2 hoare_vcg_imp_lift
                    hoare_vcg_all_lift threadSet_pred_tcb_at_state threadSet_tcbDomain_triv
                    isSchedulable_inv
                    hoare_pre_cont[where a="isSchedulable x" and P="\<lambda>rv _. rv" for x]
                    hoare_pre_cont[where a="isSchedulable x" and P="\<lambda>rv _. \<not>rv" for x]
              simp: weak_sch_act_wf_def)
  done

lemma sbn_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  by (simp add: setBoundNotification_def, wp threadSet.ksSchedulerAction)


lemma sbn_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   setBoundNotification ntfn t
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp weak_sch_act_wf_lift sbn_st_tcb')


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

lemma setObject_oa_unchanged[wp]:
  "\<lbrace>\<lambda>s. obj_at' (\<lambda>tcb::tcb. P tcb) t s\<rbrace>
    setObject ptr (ntfn::Structures_H.notification)
   \<lbrace>\<lambda>rv s.  obj_at' P t s\<rbrace>"
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_type
                            updateObject_default_def
                            in_monad)
  done

lemma setNotification_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
    setNotification ntfnptr ntfn
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (wp hoare_vcg_all_lift hoare_convert_imp hoare_vcg_conj_lift
         | simp add: weak_sch_act_wf_def st_tcb_at'_def tcb_in_cur_domain'_def)+
   apply (wps )
   apply (wp  | simp add: o_def)+
  done

lemmas ipccancel_weak_sch_act_wfs
    = weak_sch_act_wf_lift[OF _ setCTE_pred_tcb_at']

lemma tcbSchedDequeue_corres':
  "corres dc (tcb_at t) (tcb_at' t and valid_inQ_queues) (tcb_sched_action (tcb_sched_dequeue) t) (tcbSchedDequeue t)"
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
           ready_queues_relation_def obj_at'_def inQ_def projectKO_eq project_inject)
   apply (simp add: ready_queues_relation_def cdt_relation_def)
  apply (simp add: unless_def when_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="(=)", OF _ threadget_corres])
       apply (simp split del: if_split)
       apply (rule corres_split_eqr[OF _ threadget_corres])
          apply (rule corres_split_eqr[OF _ getQueue_corres])
            apply (simp split del: if_split)
            apply (subst bind_return_unit, rule corres_split[where r'=dc])
               apply (rule corres_split_noop_rhs)
                 apply (simp add: dc_def[symmetric])
                 apply (rule threadSet_corres_noop, simp_all add: tcb_relation_def)[1]
                apply (clarsimp, rule removeFromBitmap_corres_noop)
               apply wp
              apply (simp add: tcb_sched_dequeue_def)
              apply (prove_prop \<open>(\<lambda>x. x \<noteq> t) = (\<noteq>) t\<close>, simp)
              apply (rule setQueue_corres)
             apply (wp | simp add: tcb_relation_def)+
  done

lemma setQueue_valid_inQ_queues:
  "\<lbrace>valid_inQ_queues
      and (\<lambda>s. \<forall>t \<in> set ts. obj_at' (inQ d p) t s)
      and K (distinct ts)\<rbrace>
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
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (fastforce)
  done

lemma valid_inQ_queues_ksReadyQueuesL1Bitmap_upd[simp]:
  "valid_inQ_queues (s\<lparr>ksReadyQueuesL1Bitmap := f\<rparr>) = valid_inQ_queues s"
  unfolding valid_inQ_queues_def
  by simp

lemma valid_inQ_queues_ksReadyQueuesL2Bitmap_upd[simp]:
  "valid_inQ_queues (s\<lparr>ksReadyQueuesL2Bitmap := f\<rparr>) = valid_inQ_queues s"
  unfolding valid_inQ_queues_def
  by simp

(* reorder the threadSet before the setQueue, useful for lemmas that don't refer to bitmap *)
lemma setQueue_after_addToBitmap:
  "(setQueue d p q >>= (\<lambda>rv. (when P (addToBitmap d p)) >>= (\<lambda>rv. threadSet f t))) =
   (when P (addToBitmap d p) >>= (\<lambda>rv. (threadSet f t) >>= (\<lambda>rv. setQueue d p q)))"
  apply (case_tac P, simp_all)
   prefer 2
   apply (simp add: setQueue_after)
  apply (simp add: setQueue_def when_def)
  apply (subst oblivious_modify_swap)
  apply (simp add: threadSet_def getObject_def setObject_def
                   loadObject_default_def bitmap_fun_defs
                   split_def projectKO_def2 alignCheck_assert
                   magnitudeCheck_assert updateObject_default_def)
  apply (intro oblivious_bind, simp_all)
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

lemma valid_inQ_queues_ksSchedulerAction_update[simp]:
  "valid_inQ_queues (ksSchedulerAction_update f s) = valid_inQ_queues s"
  by (simp add: valid_inQ_queues_def)

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

lemma setEndpoint_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> setEndpoint ptr ep \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
  apply (unfold setEndpoint_def)
  apply (rule setObject_ep_pre)
  apply (simp add: valid_inQ_queues_def)
  apply (wp hoare_Ball_helper hoare_vcg_all_lift setObject_queues_unchanged[OF updateObject_ep_inv])
  apply simp
  done

lemma set_ntfn_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> setNotification ptr ntfn \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
  apply (unfold setNotification_def)
  apply (rule setObject_ntfn_pre)
  apply (simp add: valid_inQ_queues_def)
  apply (wp hoare_Ball_helper hoare_vcg_all_lift)
    apply (clarsimp simp: updateObject_default_def in_monad)
    apply (wp updateObject_default_inv | simp)+
    done

crunch valid_inQ_queues[wp]: cancelSignal valid_inQ_queues
  (simp: updateObject_default_inv crunch_simps wp: crunch_wps)

lemma (in delete_one_conc_pre) cancelIPC_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> cancelIPC t \<lbrace>\<lambda>_. valid_inQ_queues\<rbrace>"
  apply (simp add: cancelIPC_def Let_def)
  apply (wp hoare_drop_imps delete_one_inQ_queues threadSet_valid_inQ_queues | wpc | simp add:if_apply_def2 Fun.comp_def)+
   apply (clarsimp simp: valid_inQ_queues_def inQ_def)+
   sorry

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
  "\<lbrace> valid_inQ_queues \<rbrace> asUser t f \<lbrace>\<lambda>rv. valid_inQ_queues \<rbrace>"
  unfolding valid_inQ_queues_def Ball_def
  apply (wpsimp wp: hoare_vcg_all_lift)
    defer
    apply (wp asUser_ksQ)
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
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor [OF _ cancel_ipc_corres])
  sorry (*
      apply (rule corres_split [OF _ gts_corres])
        apply (rule corres_split_nor)
           apply (rule corres_split_nor [OF _ sts_corres])
              apply (rule tcbSchedDequeue_corres')
             apply wpsimp
            apply wp
           apply wpsimp
          apply (rule corres_if)
            apply (case_tac state; simp)
           apply (simp add: update_restart_pc_def updateRestartPC_def)
           apply (rule corres_as_user')
           apply (simp add: ARM.nextInstructionRegister_def ARM.faultRegister_def
                            ARM_H.nextInstructionRegister_def ARM_H.faultRegister_def)
           apply (simp add: ARM_H.Register_def)
           apply (subst unit_dc_is_eq)
           apply (rule corres_underlying_trivial)
           apply (wpsimp simp: ARM.setRegister_def ARM.getRegister_def)
          apply (rule corres_return_trivial)
          apply (wpsimp simp: update_restart_pc_def updateRestartPC_def)+
       apply (rule hoare_post_imp[where Q = "\<lambda>rv s. tcb_at t s \<and> is_etcb_at t s"])
        apply simp
       apply wp
      apply (rule hoare_post_imp[where Q = "\<lambda>rv s. tcb_at' t s \<and> valid_inQ_queues s"])
       apply (wpsimp simp: valid_queues_inQ_queues)
      apply wp+
   apply (force simp: valid_sched_def tcb_at_is_etcb_at)
  apply (clarsimp simp add: invs'_def valid_state'_def valid_queues_inQ_queues)
  done *)

lemma (in delete_one) prepareThreadDelete_corres:
  "corres dc (tcb_at t) (tcb_at' t)
        (prepare_thread_delete t) (ArchRetypeDecls_H.ARM_H.prepareThreadDelete t)"
  by (simp add: ArchVSpace_A.ARM_A.prepare_thread_delete_def ArchRetype_H.ARM_H.prepareThreadDelete_def)

lemma no_refs_simple_strg':
  "st_tcb_at' simple' t s' \<and> P {} \<longrightarrow> st_tcb_at' (\<lambda>st. P (tcb_st_refs_of' st)) t s'"
  oops (* FIXME RT: not true any more; adjust simple'?
  by (fastforce elim!: pred_tcb'_weakenE)+ *)

crunch it[wp]: cancelSignal "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma (in delete_one_conc_pre) cancelIPC_it[wp]:
  "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>
   cancelIPC t
   \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  apply (simp add: cancelIPC_def Let_def)
  apply (wp hoare_drop_imps delete_one_it | wpc | simp add:if_apply_def2 Fun.comp_def)+
  sorry

lemma tcbSchedDequeue_notksQ:
  "\<lbrace>\<lambda>s. t' \<notin> set(ksReadyQueues s p)\<rbrace>
    tcbSchedDequeue t
   \<lbrace>\<lambda>_ s. t' \<notin> set(ksReadyQueues s p)\<rbrace>"
  apply (simp add: tcbSchedDequeue_def  removeFromBitmap_conceal_def[symmetric])
  apply wp
        apply (rule hoare_pre_post, assumption)
        apply (clarsimp simp: bitmap_fun_defs removeFromBitmap_conceal_def, wp, clarsimp)
       apply wp+
     apply clarsimp
     apply (rule_tac Q="\<lambda>_ s. t' \<notin> set(ksReadyQueues s p)" in hoare_post_imp)
      apply (wp | clarsimp)+
  done

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

lemma sts_valid_queues_partial:
  "\<lbrace>Invariants_H.valid_queues and sch_act_simple\<rbrace>
    setThreadState st t
   \<lbrace>\<lambda>_ s. \<forall>t' d p.
            (t' \<in> set(ksReadyQueues s (d, p)) \<longrightarrow>
             (obj_at' (\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t' s
              \<and> (t' \<noteq> t \<longrightarrow> st_tcb_at' runnable' t' s)))
            \<and> distinct (ksReadyQueues s (d, p))
            \<and> (maxDomain < d \<longrightarrow> ksReadyQueues s (d, p) = []) \<and>
              (maxPriority < p \<longrightarrow> ksReadyQueues s (d, p) = [])\<rbrace>"
  (is "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_ s. \<forall>t' d p. ?OA t' d p s \<and> ?DISTINCT d p s \<rbrace>")
  apply (rule_tac Q="\<lambda>_ s. (\<forall>t' d p. ?OA t' d p s) \<and> (\<forall>d p. ?DISTINCT d p s)"
           in hoare_post_imp)
   apply (clarsimp)
  apply (rule hoare_conjI)
   apply (rule_tac Q="\<lambda>s. \<forall>t' d p.
             ((t'\<in>set(ksReadyQueues s (d, p))
               \<or> \<not> (sch_act_simple s))
                  \<longrightarrow> (obj_at'(\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t' s
                       \<and> st_tcb_at' runnable' t' s))" in hoare_pre_imp)
    apply (fastforce simp: Invariants_H.valid_queues_def valid_queues_no_bitmap_def
                           pred_tcb_at'_def obj_at'_def inQ_def)
   apply (rule hoare_vcg_all_lift)+
    apply (rule hoare_convert_imp)
     including no_pre
     apply (wp sts_ksQ setThreadState_oa_queued hoare_impI sts_pred_tcb_neq'
            | clarsimp)+
  apply (rule_tac Q="\<lambda>s. \<forall>d p. ?DISTINCT d p s \<and> sch_act_simple s" in hoare_pre_imp)
   apply (clarsimp simp: Invariants_H.valid_queues_def valid_queues_no_bitmap_def)
  apply (wp hoare_vcg_all_lift sts_ksQ)
  apply (clarsimp)
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

lemma sts_invs_minor'_no_valid_queues:
  "\<lbrace>st_tcb_at' (\<lambda>st'. tcb_st_refs_of' st' = tcb_st_refs_of' st
                   \<and> (st \<noteq> Inactive \<and> \<not> idle' st \<longrightarrow>
                      st' \<noteq> Inactive \<and> \<not> idle' st')) t
      and (\<lambda>s. t = ksIdleThread s \<longrightarrow> idle' st)
      and (\<lambda>s. runnable' st \<and> obj_at' tcbQueued t s \<longrightarrow> st_tcb_at' runnable' t s)
      and sch_act_simple
      and invs'\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. (\<forall>t' d p.
            (t' \<in> set(ksReadyQueues s (d, p)) \<longrightarrow>
             (obj_at' (\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t' s
              \<and> (t' \<noteq> t \<longrightarrow> st_tcb_at' runnable' t' s)))
            \<and> distinct (ksReadyQueues s (d, p))
            \<and> (maxDomain < d \<or> maxPriority < p \<longrightarrow> ksReadyQueues s (d, p) = [])) \<and>
         valid_bitmapQ s \<and>
         bitmapQ_no_L2_orphans s \<and>
         bitmapQ_no_L1_orphans s \<and>
         valid_pspace' s \<and>
         sch_act_wf (ksSchedulerAction s) s \<and>
         sym_refs (list_refs_of_replies' s) \<and>
         sym_refs (state_refs_of' s) \<and>
         if_live_then_nonz_cap' s \<and>
         if_unsafe_then_cap' s \<and>
         valid_idle' s \<and>
         valid_global_refs' s \<and>
         valid_arch_state' s \<and>
         valid_irq_node' (irq_node' s) s \<and>
         valid_irq_handlers' s \<and>
         valid_irq_states' s \<and>
         valid_machine_state' s \<and>
         irqs_masked' s \<and>
         valid_queues' s \<and>
         valid_release_queue s \<and>
         valid_release_queue' s \<and>
         ct_not_inQ s \<and>
         ct_idle_or_in_cur_domain' s \<and>
         valid_pde_mappings' s \<and>
         pspace_domain_valid s \<and>
         ksCurDomain s \<le> maxDomain \<and>
         valid_dom_schedule' s \<and>
         untyped_ranges_zero' s \<and>
         cur_tcb' s \<and>
         tcb_at' t s\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_queues_def)
  apply (wp sts_valid_queues_partial sts_ksQ
            setThreadState_oa_queued sts_st_tcb_at'_cases
            irqs_masked_lift
            valid_irq_node_lift
            setThreadState_ct_not_inQ
            sts_valid_bitmapQ_sch_act_simple
            sts_valid_bitmapQ_no_L2_orphans_sch_act_simple
            sts_valid_bitmapQ_no_L1_orphans_sch_act_simple
            hoare_vcg_conj_lift hoare_vcg_imp_lift hoare_vcg_all_lift)+
  apply (clarsimp)
  apply (intro conjI)
        apply (clarsimp simp: valid_queues_def)
       apply (clarsimp simp: inQ_def comp_def)
      apply (clarsimp simp: st_tcb_at'_def)
      apply (simp add: valid_queues_no_bitmap_def)
      apply (drule obj_at_valid_objs')
       apply (clarsimp simp: valid_pspace'_def)
      apply (clarsimp simp: valid_obj'_def valid_tcb'_def projectKOs)
      apply (blast intro: valid_tcb_state'_same_tcb_st_refs_of')
     apply (clarsimp simp: comp_def)
    apply (clarsimp dest!: st_tcb_at_state_refs_ofD'
                    elim!: rsubst[where P=sym_refs]
                   intro!: ext)
    using tcb_bound_refs'_helper apply blast
   apply (fastforce simp: valid_queues_def inQ_def pred_tcb_at' pred_tcb_at'_def
                   elim!: st_tcb_ex_cap'' obj_at'_weakenE)+
  done

crunch ct_idle_or_in_cur_domain'[wp]: tcbSchedDequeue ct_idle_or_in_cur_domain'

lemma tcbSchedDequeue_invs'_no_valid_queues:
   "\<lbrace>\<lambda>s. (\<forall>t' d p.
            (t' \<in> set(ksReadyQueues s (d, p)) \<longrightarrow>
             (obj_at' (\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t' s
              \<and> (t' \<noteq> t \<longrightarrow> st_tcb_at' runnable' t' s)))
            \<and> distinct (ksReadyQueues s (d, p)) \<and> (maxDomain < d \<or> maxPriority < p \<longrightarrow> ksReadyQueues s (d, p) = [])) \<and>
         valid_bitmapQ s \<and>
         bitmapQ_no_L2_orphans s \<and>
         bitmapQ_no_L1_orphans s \<and>
         valid_pspace' s \<and>
         sch_act_wf (ksSchedulerAction s) s \<and>
         sym_refs (list_refs_of_replies' s) \<and>
         sym_refs (state_refs_of' s) \<and>
         if_live_then_nonz_cap' s \<and>
         if_unsafe_then_cap' s \<and>
         valid_idle' s \<and>
         valid_global_refs' s \<and>
         valid_arch_state' s \<and>
         valid_irq_node' (irq_node' s) s \<and>
         valid_irq_handlers' s \<and>
         valid_irq_states' s \<and>
         valid_machine_state' s \<and>
         irqs_masked' s \<and>
         valid_queues' s \<and>
         valid_release_queue s \<and>
         valid_release_queue' s \<and>
         ct_not_inQ s \<and>
         ct_idle_or_in_cur_domain' s \<and>
         valid_pde_mappings' s \<and>
         pspace_domain_valid s \<and>
         ksCurDomain s \<le> maxDomain \<and>
         valid_dom_schedule' s \<and>
         untyped_ranges_zero' s \<and>
         cur_tcb' s \<and>
         tcb_at' t s\<rbrace>
    tcbSchedDequeue t
   \<lbrace>\<lambda>_. invs' \<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
  apply (wp tcbSchedDequeue_valid_queues_weak valid_irq_handlers_lift
            valid_irq_node_lift valid_irq_handlers_lift'
            tcbSchedDequeue_irq_states irqs_masked_lift cur_tcb_lift
            untyped_ranges_zero_lift
         | clarsimp simp add: cteCaps_of_def valid_queues_def o_def)+
  apply (rule conjI)
   apply (fastforce simp: obj_at'_def inQ_def st_tcb_at'_def valid_queues_no_bitmap_except_def)
  apply (rule conjI, clarsimp simp: correct_queue_def)
  apply (fastforce simp: valid_pspace'_def intro: obj_at'_conjI
                   elim: valid_objs'_maxDomain valid_objs'_maxPriority)
  done

lemmas sts_tcbSchedDequeue_invs' =
  sts_invs_minor'_no_valid_queues
  tcbSchedDequeue_invs'_no_valid_queues

lemma asUser_sch_act_simple[wp]:
  "\<lbrace>sch_act_simple\<rbrace> asUser s t \<lbrace>\<lambda>_. sch_act_simple\<rbrace>"
  unfolding sch_act_simple_def
  apply (rule asUser_nosch)
  done

lemma schedContextCancelYieldTo_valid_objs'[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>valid_objs'\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def)
  apply (rule hoare_seq_ext[OF _ threadGet_sp])
  apply (rule hoare_when_cases; (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_seq_ext[OF _ get_sc_sp'])
  apply (rule_tac B="\<lambda>_. valid_objs'" in hoare_seq_ext[rotated])
   apply (wpsimp wp: set_sc_valid_objs')
   apply (fastforce dest!: obj_at_valid_objs'
                     simp: projectKOs valid_obj'_def valid_sched_context'_def
                           valid_sched_context_size'_def scBits_simps objBits_simps')
  apply (wpsimp wp: threadSet_valid_objs')
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def)
  done

lemma schedContextCancelYieldTo_valid_mdb'[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>valid_mdb'\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def threadSet_def )
  apply (wpsimp wp: getObject_tcb_wp hoare_drop_imps hoare_vcg_ex_lift threadGet_wp)
  apply (fastforce simp: obj_at'_def projectKOs tcb_cte_cases_def)
  done

lemma schedContextCancelYieldTo_sym_refs[wp]:
  defines "sc' sc \<equiv> KOSchedContext (scYieldFrom_update Map.empty sc)"
  and "tcb' tcb \<equiv> KOTCB (tcbYieldTo_update Map.empty tcb)"
  and "state' tptr tcb sc (s :: global.kernel_state)
         \<equiv> s\<lparr>ksPSpace := \<lambda>a. if a = tptr
                             then Some (KOTCB (tcbYieldTo_update Map.empty tcb))
                             else if a = the (tcbYieldTo tcb)
                                  then Some (KOSchedContext (scYieldFrom_update Map.empty sc))
                                  else ksPSpace s a\<rparr>"
  shows "schedContextCancelYieldTo tptr \<lbrace>\<lambda>s. sym_refs (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def setSchedContext_def)
  apply (wpsimp wp: setObject_sc_wp threadSet_wp threadGet_wp)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (rename_tac tcb)
  apply (rule_tac x=tcb in exI)
  apply clarsimp
  apply (rename_tac scPtr sc)
  apply (rule delta_sym_refs, assumption)
   apply (rename_tac x y tp)
   apply (clarsimp simp: obj_at'_def  tcb_bound_refs'_def refs_of'_def state_refs_of'_def
                  split: if_split_asm option.splits)
   apply (rename_tac obj')
   apply (prop_tac "ps_clear x (objBitsKO obj') s")
    apply (rule ps_clear_domE)
     apply simp
    subgoal by (auto simp: dom_def)
   apply (fastforce simp: ps_clear_def)

  \<comment> \<open>we introduce some facts which greatly simplify the proof\<close>
  apply (prop_tac "is_aligned tptr (objBitsKO (tcb' tcb))")
   apply (fastforce simp: ps_clear_def objBitsKO_def tcb'_def split: if_splits)

  apply (prop_tac "is_aligned scPtr (objBitsKO (sc' sc))")
   apply (fastforce simp: ps_clear_def objBitsKO_def sc'_def split: if_splits)

  apply (prop_tac "ps_clear scPtr (objBitsKO (sc' sc))
                            (state' tptr tcb sc s)")
   apply (fastforce simp: ps_clear_def objBitsKO_def sc'_def tcb'_def state'_def split: if_splits )[1]

  apply (prop_tac "ps_clear tptr (objBitsKO (KOTCB (tcbYieldTo_update Map.empty tcb)))
                            (state' tptr tcb sc s)")
   apply (fastforce simp: ps_clear_def objBitsKO_def state'_def split: if_splits )[1]

  apply (clarsimp simp: state_refs_of'_def sc'_def tcb'_def state'_def split: if_splits)
    apply (fastforce simp: get_refs_def2)
   apply (case_tac "y = scPtr \<or> y = tptr")
    apply (fastforce simp: tcb_bound_refs'_def tcb_st_refs_of'_def get_refs_def2
                    split: if_split_asm thread_state.splits)
   apply (clarsimp simp: tcb_bound_refs'_def get_refs_def2)
   apply (prop_tac "(scPtr, TCBYieldTo) \<in> state_refs_of' s tptr")
    apply (clarsimp simp: state_refs_of'_def)
   apply (fastforce simp: sym_refs_def get_refs_def split: option.splits)

  apply (thin_tac "ps_clear _ _ _")+
  apply (thin_tac "is_aligned _ _")+ \<comment> \<open>to speed up the following\<close>
  by (fastforce simp: get_refs_def2 ps_clear_def is_aligned_def
               split: if_split_asm option.splits)

lemma schedContextCancelYieldTo_sch_act_wf[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def)
  apply (wpsimp wp: threadSet_sch_act threadGet_wp)
  apply (fastforce simp: obj_at'_def projectKOs)
  done

lemma schedContextCancelYieldTo_if_live_then_nonz_cap'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> sym_refs (state_refs_of' s)\<rbrace>
   schedContextCancelYieldTo tptr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def)
  apply (rule hoare_seq_ext[OF _ threadGet_sp])
  apply (rule hoare_when_cases; (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_seq_ext[OF _ get_sc_sp'])
  apply (rule_tac B="\<lambda>_ s. if_live_then_nonz_cap' s"
               in hoare_seq_ext[rotated])
   apply (wpsimp wp: setSchedContext_iflive')
   apply (erule if_live_then_nonz_capE')
   apply (clarsimp simp: live'_def ko_wp_at'_def obj_at'_def projectKOs live_sc'_def)
  apply (wpsimp wp: threadSet_iflive' setSchedContext_iflive' threadGet_wp)
  apply (fastforce simp: obj_at'_def projectKOs)
  done

lemma schedContextCancelYieldTo_if_unsafe_then_cap'[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>if_unsafe_then_cap'\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def)
  apply (wpsimp wp: threadSet_ifunsafe' threadGet_wp)
  apply (fastforce simp: obj_at'_def projectKOs)
  done

lemma schedContextCancelYieldTo_valid_idle'[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>valid_idle'\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def)
  apply (wpsimp wp: threadSet_idle' setObject_sc_idle' updateObject_default_inv
                    threadGet_wp hoare_vcg_imp_lift' hoare_vcg_all_lift)
  apply (fastforce simp: valid_idle'_def obj_at'_def projectKOs idle_tcb'_def)
  done

lemma schedContextCancelYieldTo_valid_release_queue[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>valid_release_queue\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def)
  apply (wpsimp wp: threadSet_valid_release_queue threadGet_wp)
  apply (fastforce simp: obj_at'_def projectKOs)
  done

lemma schedContextCancelYieldTo_ct_not_inQ[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>ct_not_inQ\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def)
  apply (wpsimp wp: threadSet_not_inQ threadGet_wp)
  apply (fastforce simp: obj_at'_def projectKOs)
  done

lemma schedContextCancelYieldTo_valid_pde_mappings'[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>valid_pde_mappings'\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def setSchedContext_def)
  apply (wpsimp wp: threadGet_wp)
  apply (fastforce simp: valid_pde_mappings'_def obj_at'_def projectKOs ps_clear_upd')
  done

lemma schedContextCancelYieldTo_cur_tcb'[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>cur_tcb'\<rbrace>"
  apply (wpsimp simp: schedContextCancelYieldTo_def
                  wp: threadSet_cur threadGet_wp)
  apply (fastforce simp: obj_at'_def projectKOs)
  done

lemma schedContextCancelYieldTo_tcb_at'[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>tcb_at' ptr\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def)
  apply (wpsimp wp: threadGet_wp)
  apply (fastforce simp: obj_at'_def projectKOs)
  done

lemma schedContextCancelYeldTo_valid_release_queue'[wp]:
  "schedContextCancelYieldTo t \<lbrace>valid_release_queue'\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def)
  apply (rule hoare_seq_ext[OF _ threadGet_sp])
  apply (rule hoare_when_cases; (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_seq_ext[OF _ get_sc_sp'])
  apply (rule_tac B="\<lambda>_. valid_release_queue'" in hoare_seq_ext[rotated])
   apply wpsimp
  apply (wpsimp wp: threadSet_valid_release_queue' setObject_tcb_wp)
  apply (clarsimp simp: valid_release_queue'_def obj_at'_def)
  done

crunches schedContextCancelYieldTo
  for pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and no_0_obj'[wp]: no_0_obj'
  and ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and valid_queues[wp]: valid_queues
  and list_refs_of_replies[wp]: "\<lambda>s. sym_refs (list_refs_of_replies' s)"
  and if_unsafe_then_cap'[wp]: if_unsafe_then_cap'
  and valid_global_refs'[wp]: valid_global_refs'
  and valid_arch_state'[wp]: valid_arch_state'
  and irq_node[wp]: "\<lambda>s. P (irq_node' s)"
  and typ_at[wp]: "\<lambda>s. P (typ_at' T p s)"
  and interrupt_state[wp]: "\<lambda>s. P (ksInterruptState s)"
  and valid_irq_state'[wp]: valid_irq_states'
  and valid_machine_state'[wp]: valid_machine_state'
  and valid_queues[wp]: valid_queues
  and valid_queues'[wp]: valid_queues'
  and ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps simp: crunch_simps tcb_cte_cases_def)

lemma schedContextCancelYieldTo_invs':
  "\<lbrace>invs' and sch_act_simple and tcb_at' t and (\<lambda>s. t \<noteq> ksIdleThread s)\<rbrace>
   schedContextCancelYieldTo t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def setSchedContext_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift cur_tcb_lift
                    untyped_ranges_zero_lift
              simp: cteCaps_of_def o_def)
  apply (simp add: inQ_def)
  done

crunches tcbReleaseRemove
  for pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and no_0_obj'[wp]: no_0_obj'
  and ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and list_refs_of_replies[wp]: "\<lambda>s. sym_refs (list_refs_of_replies' s)"
  and state_refs_of'[wp]: "\<lambda>s. sym_refs (state_refs_of' s)"
  and valid_global_refs'[wp]: valid_global_refs'
  and valid_arch_state'[wp]: valid_arch_state'
  and irq_node[wp]: "\<lambda>s. P (irq_node' s)"
  and typ_at[wp]: "\<lambda>s. P (typ_at' T p s)"
  and interrupt_state[wp]: "\<lambda>s. P (ksInterruptState s)"
  and valid_irq_state'[wp]: valid_irq_states'
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  and ksMachineState[wp]: "\<lambda>s. P (ksMachineState s)"
  and valid_pde_mappings'[wp]: valid_pde_mappings'
  (wp: crunch_wps simp: crunch_simps tcb_cte_cases_def)

crunches setReleaseQueue, setReprogramTimer
  for if_unsafe_then_cap'[wp]: if_unsafe_then_cap'
  and valid_machine_state'[wp]: valid_machine_state'
  (wp: crunch_wps simp: crunch_simps valid_machine_state'_def)

lemma tcbReleaseRemove_if_unsafe_then_cap'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>if_unsafe_then_cap'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def)
  apply (wpsimp wp: threadSet_ifunsafe')
  done

lemma tcbReleaseRemove_valid_machine_state'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_machine_state'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

lemma setReleaseQueue_ct_idle_or_in_cur_domain'[wp]:
  "setReleaseQueue rlq \<lbrace>ct_idle_or_in_cur_domain'\<rbrace>"
  apply (wpsimp simp: setReleaseQueue_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma setReprogramTimer_ct_idle_or_in_cur_domain'[wp]:
  "setReprogramTimer reprogramTimer \<lbrace>ct_idle_or_in_cur_domain'\<rbrace>"
  apply (clarsimp simp: setReprogramTimer_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_disj_lift)
  done

lemma tcbReleaseRemove_ct_idle_or_in_cur_domain'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>ct_idle_or_in_cur_domain'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def)
  apply (wpsimp wp: threadSet_ct_idle_or_in_cur_domain' hoare_vcg_imp_lift' hoare_vcg_disj_lift)
  done

crunches setReprogramTimer
  for valid_queues[wp]: valid_queues
  and ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"

lemma tcbReleaseRemove_valid_queues_no_bitmap:
  "\<lbrace>valid_queues\<rbrace>
   tcbReleaseRemove tcbPtr
   \<lbrace>\<lambda>_. valid_queues_no_bitmap\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: threadSet_valid_queues_no_bitmap_new)
  apply (clarsimp simp: valid_queues_no_bitmap_def valid_queues_def)
  apply (fastforce simp: obj_at'_def inQ_def)
  done

crunches setReleaseQueue, setReprogramTimer
  for valid_bitmapQ[wp]: valid_bitmapQ
  and bitmapQ_no_L2_orphans[wp]: bitmapQ_no_L2_orphans
  and bitmapQ_no_L1_orphans[wp]: bitmapQ_no_L1_orphans
  (simp: crunch_simps valid_bitmapQ_def bitmapQ_def bitmapQ_no_L2_orphans_def
         bitmapQ_no_L1_orphans_def)

lemma tcbReleaseRemove_valid_bitmapQ:
  "\<lbrace>valid_bitmapQ and sch_act_simple\<rbrace>
   tcbReleaseRemove tcbPtr
   \<lbrace>\<lambda>_. valid_bitmapQ\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def)
  apply (wpsimp wp: threadSet_valid_bitmapQ)
  done

lemma tcbReleaseRemove_bitmapQ_no_L2_orphans[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>bitmapQ_no_L2_orphans\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def)
  apply (wpsimp wp: threadSet_valid_bitmapQ_no_L2_orphans)
  done

lemma tcbReleaseRemove_bitmapQ_no_L1_orphans[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>bitmapQ_no_L1_orphans\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def)
  apply (wpsimp wp: threadSet_valid_bitmapQ_no_L1_orphans)
  done

lemma tcbReleaseRemove_valid_queues:
  "\<lbrace>valid_queues and sch_act_simple\<rbrace>
   tcbReleaseRemove tcbPtr
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (clarsimp simp: valid_queues_def)
  apply (wpsimp wp: tcbReleaseRemove_valid_queues_no_bitmap tcbReleaseRemove_valid_bitmapQ
              simp: valid_queues_def)
  done

crunches setReleaseQueue, setReprogramTimer
  for valid_queues'[wp]: valid_queues'
  (simp: valid_queues'_def)

lemma tcbReleaseRemove_valid_queues'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_queues'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: threadSet_valid_queues')
  apply (clarsimp simp: valid_queues'_def inQ_def)
  done

crunches setReprogramTimer
  for valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'

lemma tcbReleaseRemove_valid_release_queue[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_release_queue\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: threadSet_valid_release_queue)
  apply (clarsimp simp: valid_release_queue_def)
  done

lemma tcbReleaseRemove_valid_release_queue'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_release_queue'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: threadSet_valid_release_queue')
  apply (clarsimp simp: valid_release_queue'_def obj_at'_def)
  done

crunches setReprogramTimer
  for valid_objs'[wp]: valid_objs'
  and sch_act_wf[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  and if_live_then_nonz_cap'[wp]: if_live_then_nonz_cap'
  and valid_idle'[wp]: valid_idle'
  and valid_mdb'[wp]: valid_mdb'
  and ct_not_inQ[wp]: ct_not_inQ
  (simp: valid_mdb'_def)

lemma tcbReleaseRemove_valid_objs'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_objs'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: threadSet_valid_objs')
  apply (clarsimp simp: valid_tcb'_def valid_cap'_def tcb_cte_cases_def)
  done

lemma tcbReleaseRemove_valid_mdb'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_mdb'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule_tac B="\<lambda>_. valid_mdb'" in hoare_seq_ext[rotated])
   apply wpsimp
   apply (clarsimp simp: valid_mdb'_def)
  apply (wpsimp wp: setObject_tcb_mdb' getObject_tcb_wp simp: threadSet_def)
  apply (fastforce simp: obj_at'_def projectKOs tcb_cte_cases_def)
  done

lemma tcbReleaseRemove_sch_act_wf[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (wpsimp wp: threadSet_sch_act)
  done

lemma tcbReleaseRemove_if_live_then_nonz_cap'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> sym_refs (state_refs_of' s)\<rbrace>
   tcbReleaseRemove tptr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: threadSet_iflive' setSchedContext_iflive' threadGet_wp)
  apply (fastforce simp: obj_at'_def projectKOs)
  done

lemma tcbReleaseRemove_valid_idle'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_idle'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (wpsimp wp: threadSet_idle')
  done

lemma tcbReleaseRemove_ct_not_inQ[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>ct_not_inQ\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: threadSet_not_inQ)
  apply (clarsimp simp: ct_not_inQ_def)
  done

lemma tcbReleaseRemove_tcb_at'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>tcb_at' t\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def
                        setReprogramTimer_def)
  apply (wpsimp wp: threadSet_tcb')
  done

lemma tcbReleaseRemove_invs':
  "\<lbrace>invs' and sch_act_simple\<rbrace>
   tcbReleaseRemove tcbPtr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift cur_tcb_lift
                    untyped_ranges_zero_lift tcbReleaseRemove_valid_queues
              simp: cteCaps_of_def o_def)
  done

lemma cancelIPC_simple_except_awaiting_reply:
  "\<lbrace>\<lambda>s. invs' s \<and> tcb_at' t s\<rbrace> cancelIPC t
   \<lbrace>\<lambda>rv. st_tcb_at' ((=) Running or (=) Inactive or (=) Restart or (=) IdleThreadState) t\<rbrace>"
sorry

crunches tcbReleaseRemove, tcbSchedDequeue
  for sch_act_simple[wp]: sch_act_simple
  and ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps simp: crunch_simps sch_act_simple_def)

lemma (in delete_one_conc) suspend_invs'[wp]:
  "\<lbrace>invs' and sch_act_simple and tcb_at' t and (\<lambda>s. t \<noteq> ksIdleThread s)\<rbrace>
   ThreadDecls_H.suspend t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: suspend_def updateRestartPC_def getThreadState_def)
  apply (rule_tac B="\<lambda>_ s. invs' s
                           \<and> sch_act_simple s
                           \<and> tcb_at' t s
                           \<and> t \<noteq> ksIdleThread s
                           \<and> st_tcb_at' ((=) Running or (=) Inactive or (=) Restart
                                          or (=) IdleThreadState) t s"
               in hoare_seq_ext[rotated])
   apply (wpsimp wp: cancelIPC_simple_except_awaiting_reply)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip)
  apply clarsimp
   apply (wpsimp simp: updateRestartPC_def)
  apply (wpsimp wp: sts_tcbSchedDequeue_invs' tcbReleaseRemove_invs'
                    schedContextCancelYieldTo_invs')
  apply (fastforce simp: tcb_st_refs_of'_def st_tcb_at'_def obj_at'_def projectKOs)
  done

crunches ThreadDecls_H.suspend
  (* FIXME RT: VER-1016 *)
  for tcb_at'_better[wp]: "\<lambda>s. P (tcb_at' t s)"
  and sch_act_simple[wp]: "sch_act_simple"
  (rule: sch_act_simple_lift
     wp: crunch_wps
   simp: crunch_simps if_fun_split st_tcb_at'_def)

lemma (in delete_one_conc) suspend_objs':
  "\<lbrace>invs' and sch_act_simple and tcb_at' t and (\<lambda>s. t \<noteq> ksIdleThread s)\<rbrace>
   suspend t \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (rule_tac Q="\<lambda>_. invs'" in hoare_strengthen_post)
   apply (wp suspend_invs')
  apply fastforce
  done

lemma schedContextCancelYieldTo_st_tcb_at'[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>st_tcb_at' P t\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_when_cases; (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_seq_ext_skip, wpsimp)+
  apply (wpsimp simp: threadSet_def wp: setObject_tcb_wp getObject_tcb_wp)
  apply (fastforce simp: obj_at'_def st_tcb_at'_def projectKOs is_aligned_def objBitsKO_def
                         ps_clear_def)
  done

lemma (in delete_one_conc_pre) suspend_st_tcb_at':
  assumes x[simp]: "\<And>st. simple' st \<longrightarrow> P st" shows
  "\<lbrace>st_tcb_at' P t\<rbrace>
     suspend thread
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  unfolding suspend_def updateRestartPC_def
  apply (wp sts_st_tcb_at'_cases threadSet_pred_tcb_no_state
            cancelIPC_st_tcb_at hoare_drop_imps asUser_pred_tcb_at' x
         | simp)+
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

lemmas (in delete_one_conc_pre) suspend_makes_simple' =
       suspend_st_tcb_at' [where P=simple', simplified]

lemma valid_queues_not_runnable'_not_ksQ:
  assumes "Invariants_H.valid_queues s" and "st_tcb_at' (Not \<circ> runnable') t s"
  shows   "\<forall>d p. t \<notin> set (ksReadyQueues s (d, p))"
  using assms
  apply -
  apply (clarsimp simp: Invariants_H.valid_queues_def valid_queues_no_bitmap_def pred_tcb_at'_def)
  apply (erule_tac x=d in allE)
  apply (erule_tac x=p in allE)
  apply (clarsimp)
  apply (drule(1) bspec)
  apply (clarsimp simp: obj_at'_def)
  done

declare valid_queues_not_runnable'_not_ksQ[OF ByAssum, simp]

lemma cancelSignal_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues and st_tcb_at' (Not \<circ> runnable') t\<rbrace>
   cancelSignal t ae
   \<lbrace>\<lambda>_. Invariants_H.valid_queues \<rbrace>"
  apply (simp add: cancelSignal_def)
  apply (wpsimp wp: sts_valid_queues getNotification_wp)
  done

lemma (in delete_one_conc_pre) cancelIPC_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues and valid_objs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)\<rbrace>
   cancelIPC t \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: cancelIPC_def Let_def
             cong: Structures_H.thread_state.case_cong list.case_cong)
  sorry (*
  apply (rule hoare_seq_ext [OF _ gts_sp'])
  apply (rule hoare_pre)
   apply (wpc
           | wp hoare_vcg_conj_lift delete_one_queues threadSet_valid_queues
                threadSet_valid_objs' sts_valid_queues setEndpoint_ksQ
                hoare_vcg_all_lift threadSet_sch_act threadSet_weak_sch_act_wf
           | simp add: o_def if_apply_def2 inQ_def
           | rule hoare_drop_imps
           | clarsimp simp: valid_tcb'_def tcb_cte_cases_def
                     elim!: pred_tcb'_weakenE)+
  apply (fastforce dest: valid_queues_not_runnable'_not_ksQ elim: pred_tcb'_weakenE)
  done *)

(* FIXME: move to Schedule_R *)
lemma tcbSchedDequeue_nonq[wp]:
  "\<lbrace>Invariants_H.valid_queues and tcb_at' t and K (t = t')\<rbrace>
    tcbSchedDequeue t \<lbrace>\<lambda>_ s. \<forall>d p. t' \<notin> set (ksReadyQueues s (d, p))\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: tcbSchedDequeue_def)
  apply (wp threadGet_wp|simp)+
  apply (fastforce simp: Invariants_H.valid_queues_def valid_queues_no_bitmap_def obj_at'_def projectKOs inQ_def)
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

crunches schedContextCancelYieldTo, tcbReleaseRemove
  for not_queued[wp]: "\<lambda>s. t' \<notin> set (ksReadyQueues s (d, p))"
  (wp: crunch_wps simp: crunch_simps)

lemma (in delete_one_conc_pre) suspend_nonq:
  "\<lbrace>Invariants_H.valid_queues and valid_objs' and tcb_at' t
                 and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
                 and (\<lambda>s. t \<noteq> ksIdleThread s) and K (t = t')\<rbrace>
     suspend t
   \<lbrace>\<lambda>rv s. \<forall>d p. t' \<notin> set (ksReadyQueues s (d, p))\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: suspend_def unless_def)
  unfolding updateRestartPC_def
  apply (wpsimp wp: hoare_allI tcbSchedDequeue_t_notksQ sts_ksQ_oaQ hoare_vcg_imp_lift
                    hoare_disjI2[where Q="\<lambda>_. valid_queues"])
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

lemma ep_cancel_corres_helper:
  "corres dc ((\<lambda>s. \<forall>t \<in> set list. tcb_at t s)
                    and valid_objs
                    and pspace_aligned
                    and pspace_distinct)
             ((\<lambda>s. \<forall>t \<in> set list. tcb_at' t s)
                    and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
                    and Invariants_H.valid_queues
                    and valid_queues'
                    and valid_objs'
                    and valid_release_queue_iff)
          (mapM_x (\<lambda>t. do
                        y \<leftarrow> set_thread_state t Structures_A.Restart;
                        tcb_sched_action tcb_sched_enqueue t
                     od) list)
          (mapM_x (\<lambda>t. do
                        y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                        tcbSchedEnqueue t
                     od) list)"
  apply (rule_tac S="{t. (fst t = snd t) \<and> fst t \<in> set list}"
                     in corres_mapM_x)
      apply clarsimp
      apply (rule corres_guard_imp)
        apply (subst bind_return_unit, rule corres_split[OF tcbSchedEnqueue_corres])
          apply simp
          apply (rule corres_guard_imp[OF sts_corres])
            apply simp
           apply (simp add: valid_tcb_state_def)
          apply simp
         apply (wp sts_valid_queues)+
       apply force
      apply (clarsimp simp: valid_tcb_state'_def)
     apply ((wp hoare_vcg_const_Ball_lift | simp)+)[1]
    apply (rule hoare_pre)
    apply (wp hoare_vcg_const_Ball_lift
              weak_sch_act_wf_lift_linear sts_st_tcb' setThreadState_not_st
              sts_valid_queues tcbSchedEnqueue_not_st
         | simp)+
    apply (auto elim: obj_at'_weakenE simp: valid_tcb_state'_def)
  done

lemma ep_cancel_corres:
  "corres dc (invs and valid_sched and ep_at ep) (invs' and ep_at' ep)
             (cancel_all_ipc ep) (cancelAllIPC ep)"
proof -
  have P:
    "\<And>list.
     corres dc (\<lambda>s. (\<forall>t \<in> set list. tcb_at t s) \<and> valid_pspace s \<and> ep_at ep s
                        \<and> weak_valid_sched_action s)
               (\<lambda>s. (\<forall>t \<in> set list. tcb_at' t s) \<and> valid_pspace' s
                         \<and> ep_at' ep s \<and> weak_sch_act_wf (ksSchedulerAction s) s
                         \<and> Invariants_H.valid_queues s \<and> valid_queues' s \<and> valid_objs' s)
               (do x \<leftarrow> set_endpoint ep Structures_A.IdleEP;
                   x \<leftarrow> mapM_x (\<lambda>t. do
                        y \<leftarrow> set_thread_state t Structures_A.Restart;
                        tcb_sched_action tcb_sched_enqueue t
                     od) list;
                   reschedule_required
               od)
               (do x \<leftarrow> setEndpoint ep IdleEP;
                   x \<leftarrow> mapM_x (\<lambda>t. do
                        y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                        tcbSchedEnqueue t
                     od) list;
                   rescheduleRequired
                od)"
    apply (rule corres_split')
       apply (rule corres_guard_imp [OF set_ep_corres])
         apply (simp add: ep_relation_def)+
      apply (rule corres_split [OF rescheduleRequired_corres])
        apply (rule ep_cancel_corres_helper)
       apply (rule mapM_x_wp')
  sorry (*
       apply (wp weak_sch_act_wf_lift_linear set_thread_state_runnable_weak_valid_sched_action | simp)+
      apply (rule_tac R="\<lambda>_ s. \<forall>x\<in>set list. tcb_at' x s \<and> valid_objs' s"
                   in hoare_post_add)
      apply (rule mapM_x_wp')
      apply (rule hoare_name_pre_state)
      apply ((wp hoare_vcg_const_Ball_lift mapM_x_wp'
                sts_valid_queues setThreadState_not_st sts_st_tcb' tcbSchedEnqueue_not_st
           | clarsimp
           | fastforce elim: obj_at'_weakenE simp: valid_tcb_state'_def)+)[2]
      apply (rule hoare_name_pre_state)
      apply (wp hoare_vcg_const_Ball_lift set_ep_valid_objs'
          | (clarsimp simp: valid_ep'_def)
          | (drule (1) bspec, clarsimp simp: valid_pspace'_def valid_tcb'_def valid_ep'_def elim!: valid_objs_valid_tcbE'))+
      done *)

  show ?thesis
    apply (simp add: cancel_all_ipc_def cancelAllIPC_def)
    apply (rule corres_split' [OF _ _ get_simple_ko_sp get_ep_sp'])
     apply (rule corres_guard_imp [OF get_ep_corres], simp+)
    apply (case_tac epa, simp_all add: ep_relation_def
                                       get_ep_queue_def)
     apply (rule corres_guard_imp [OF P]
             | clarsimp simp: valid_obj_def valid_ep_def
                              valid_obj'_def valid_ep'_def
                              invs_valid_pspace projectKOs
                              valid_sched_def valid_sched_action_def
             | erule obj_at_valid_objsE
             | drule ko_at_valid_objs'
             | rule conjI | clarsimp simp: invs'_def valid_state'_def)+
    sorry
qed

crunches inReleaseQueue
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (sa s) s"
  and tcb_in_cur_domain'[wp]: "tcb_in_cur_domain' t"
  and cur_tcb'[wp]: cur_tcb'

crunches possibleSwitchTo
  for valid_pspace'[wp]: valid_pspace'
  and valid_queue[wp]: Invariants_H.valid_queues
  and cap_to'[wp]: "ex_nonz_cap_to' p"
  and ifunsafe'[wp]: "if_unsafe_then_cap'"
  and global_refs'[wp]: valid_global_refs'
  and valid_machine_state'[wp]: valid_machine_state'
  and cur[wp]: cur_tcb'
  and valid_queues'[wp]: valid_queues'
  and valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'
  and refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  and replies_of'[wp]: "\<lambda>s. P (replies_of' s)"
  and idle'[wp]: "valid_idle'"
  and valid_arch'[wp]: valid_arch_state'
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and irq_states' [wp]: valid_irq_states'
  and pde_mappings' [wp]: valid_pde_mappings'
  and pspace_domain_valid[wp]: "pspace_domain_valid"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and tcb'[wp]: "tcb_at' addr"
  and valid_objs'[wp]: valid_objs'
  (wp: crunch_wps cur_tcb_lift simp: crunch_simps)

lemma possibleSwitchTo_sch_act[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> st_tcb_at' runnable' t s\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (wpsimp simp: possibleSwitchTo_def curDomain_def inReleaseQueue_def wp: threadGet_wp)
  by (fastforce simp: obj_at'_def tcb_in_cur_domain'_def)

lemma possibleSwitchTo_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' t
      and (\<lambda>s. \<forall>t. ksSchedulerAction s = SwitchToThread t
                   \<longrightarrow> st_tcb_at' runnable' t s)\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  by (wpsimp simp: possibleSwitchTo_def inReleaseQueue_def wp: hoare_vcg_if_lift2 hoare_drop_imps)

lemma possibleSwitchTo_ct_idle_or_in_cur_domain'[wp]:
  "possibleSwitchTo t \<lbrace>ct_idle_or_in_cur_domain'\<rbrace>"
  apply (wpsimp simp: possibleSwitchTo_def curDomain_def inReleaseQueue_def
                  wp: threadGet_wp rescheduleRequired_valid_release_queue'_sch_act_simple)
  apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_tcb)
  apply (fastforce simp: ct_idle_or_in_cur_domain'_def)
  done

lemma possibleSwitchTo_utr[wp]:
  "possibleSwitchTo t \<lbrace>untyped_ranges_zero'\<rbrace>"
  by (wpsimp simp: cteCaps_of_def o_def wp: untyped_ranges_zero_lift)

lemma possibleSwitchTo_all_invs_but_ct_not_inQ':
  "\<lbrace>\<lambda>s. all_invs_but_ct_not_inQ' s \<and> st_tcb_at' runnable' t s
        \<and> valid_objs' s \<and> weak_sch_act_wf (ksSchedulerAction s) s
        \<and> sch_act_simple s \<and> ex_nonz_cap_to' t s\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>_. all_invs_but_ct_not_inQ'\<rbrace>"
  apply wp
   apply (rule hoare_use_eq_irq_node', wp)
   apply (wpsimp wp: typ_at_lift_valid_irq_node' valid_irq_handlers_lift'
                     cteCaps_of_ctes_of_lift irqs_masked_lift)
  apply clarsimp
  by (metis fold_list_refs_of_replies')

lemma possibleSwitchTo_weak_sch_act[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<and> st_tcb_at' runnable' t s\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding possibleSwitchTo_def curDomain_def inReleaseQueue_def
  apply (wpsimp wp: threadGet_wp rescheduleRequired_weak_sch_act_wf
                    hoare_vcg_if_lift_strong)
  by (auto simp: obj_at'_def weak_sch_act_wf_def tcb_in_cur_domain'_def
                 projectKO_eq ps_clear_domE)

lemma ntfn_cancel_corres_helper:
  "corres dc ((\<lambda>s. \<forall>t \<in> set list. tcb_at t s \<and> t \<noteq> idle_thread s
                                      \<and> blocked_on_recv_ntfn_tcb_at t s)
              and valid_sched
              and valid_objs
              and pspace_aligned
              and pspace_distinct
              and cur_tcb
              and K (distinct list))
             ((\<lambda>s. \<forall>t \<in> set list. tcb_at' t s)
              and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
              and Invariants_H.valid_queues
              and valid_queues'
              and valid_objs'
              and valid_release_queue_iff)
          (mapM_x (\<lambda>t. do
                        y \<leftarrow> set_thread_state t Structures_A.Restart;
                        possible_switch_to t
                     od) list)
          (mapM_x (\<lambda>t. do
                        y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                        possibleSwitchTo t
                     od) list)"
  (is "corres _ _ ?conc_guard _ _")
  apply (rule corres_gen_asm')
  apply (rule corres_cross_over_guard[where Q="?conc_guard and cur_tcb'"])
   apply (fastforce simp: cur_tcb_cross)
  apply (subst pred_conj_assoc[symmetric])+
  apply (rule_tac S="{t. (fst t = snd t) \<and> fst t \<in> set list}" in corres_mapM_x_scheme
         ; ((subst pred_conj_assoc)+)?)
        apply clarsimp
        apply (rule corres_guard_imp)
          apply (rule corres_split[OF possibleSwitchTo_corres])
            apply (rule sts_corres)
            apply simp
           apply (wp sts_valid_queues set_thread_state_weak_valid_sched_action
                     setThreadState_st_tcb)+
         apply force
        apply (clarsimp simp: valid_tcb_state'_def)
       apply (wpsimp wp: set_thread_state_pred_map_tcb_sts_of)
      apply (wpsimp wp: typ_at_lifts)
     apply (clarsimp simp: pred_conj_def)
     apply (wpsimp wp: set_thread_state_possible_switch_to_valid_sched
                       hoare_vcg_const_Ball_lift set_thread_state_pred_map_tcb_sts_of)
     apply (frule valid_sched_released_ipc_queues)
     apply (fastforce simp: released_ipc_queues_defs)
    apply (wpsimp wp: hoare_vcg_const_Ball_lift typ_at_lifts sts_st_tcb'
                      sts_valid_queues)
    apply (auto simp: valid_tcb_state'_def)
  done

lemma ntfn_cancel_corres:
  "corres dc (invs and valid_sched and ntfn_at ntfn) (invs' and ntfn_at' ntfn)
             (cancel_all_signals ntfn) (cancelAllSignals ntfn)"
  apply (simp add: cancel_all_signals_def cancelAllSignals_def)
  apply (rule corres_split' [OF _ _ get_simple_ko_sp get_ntfn_sp'])
   apply (rule corres_guard_imp [OF get_ntfn_corres])
    apply simp+
  apply (case_tac "ntfn_obj ntfna", simp_all add: ntfn_relation_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ set_ntfn_corres])
       apply (rule corres_split [OF rescheduleRequired_corres])
         apply (rule ntfn_cancel_corres_helper)
        apply (clarsimp simp: dc_def)
        apply (rename_tac list)
        apply (rule_tac R="\<lambda>_ s. (\<forall>x\<in>set list. released_if_bound_sc_tcb_at x s)"
               in hoare_post_add)
        apply (rule mapM_x_wp')
        apply (wpsimp wp: weak_sch_act_wf_lift_linear
                          set_thread_state_weak_valid_sched_action
                          hoare_vcg_imp_lift set_thread_state_pred_map_tcb_sts_of)
        apply (fastforce simp: vs_all_heap_simps)
       apply (rename_tac list)
        apply (rule_tac R="\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s"
               in hoare_post_add)
       apply (rule mapM_x_wp')
       apply (rule hoare_name_pre_state)
       apply (wpsimp wp: hoare_vcg_const_Ball_lift
                         sts_st_tcb' sts_valid_queues setThreadState_not_st
                   simp: valid_tcb_state'_def)
      apply (simp add: ntfn_relation_def)
     apply (wpsimp wp: hoare_vcg_const_Ball_lift)+
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (erule (1) obj_at_valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def not_idle_tcb_in_waitingntfn
                         valid_sched_weak_valid_sched_action)
   apply (clarsimp simp: ball_conj_distrib[symmetric])
   apply (rename_tac q s t)
   apply (rule context_conjI)
    apply (drule_tac x=ntfn and y=t and tp=TCBSignal in sym_refsE
           ; clarsimp simp: in_state_refs_of_iff refs_of_rev vs_all_heap_simps)
   apply (clarsimp simp: valid_sched_released_ipc_queues released_ipc_queues_blocked_on_recv_ntfn_E1)
  apply (clarsimp simp: invs'_def valid_state'_def invs_weak_sch_act_wf valid_ntfn'_def
                        valid_obj'_def projectKOs
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
  apply (simp add: setThreadState_def)
  apply (wpsimp wp: hoare_vcg_imp_lift [OF nrct])
   apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp)
    apply (clarsimp)
  sorry (*
   apply (rule hoare_convert_imp [OF threadSet.ksSchedulerAction threadSet.ct])
  apply assumption
  done *)
qed

lemma cancel_all_invs'_helper:
  "\<lbrace>all_invs_but_sym_refs_ct_not_inQ' and (\<lambda>s. \<forall>x \<in> set q. tcb_at' x s)
       and (\<lambda>s. sym_refs (\<lambda>x. if x \<in> set q then {r \<in> state_refs_of' s x. snd r = TCBBound}
                              else state_refs_of' s x)
              \<and>  (\<forall>x \<in> set q. ex_nonz_cap_to' x s))\<rbrace>
   mapM_x (\<lambda>t. do st <- getThreadState t;
                  y <- case if isReceive st then replyObject st else None of None \<Rightarrow> return () | Some x \<Rightarrow> replyUnlink x;
                  fault <- threadGet tcbFault t;
                  if fault = None then do y <- setThreadState Structures_H.thread_state.Restart t;
                                          possibleSwitchTo t
                                       od
                  else setThreadState Structures_H.thread_state.Inactive t
               od) q
   \<lbrace>\<lambda>rv. all_invs_but_ct_not_inQ'\<rbrace>"
  apply (rule mapM_x_inv_wp2)
   apply clarsimp
  apply (rule hoare_pre)
   apply (wp valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
             hoare_vcg_const_Ball_lift untyped_ranges_zero_lift
             sts_valid_queues sts_st_tcb' setThreadState_not_st
        | simp add: cteCaps_of_def o_def)+
(*   apply (unfold fun_upd_apply Invariants_H.tcb_st_refs_of'_simps)
  apply clarsimp
  apply (intro conjI)
  apply (clarsimp simp: valid_tcb_state'_def global'_no_ex_cap
                 elim!: rsubst[where P=sym_refs]
                 dest!: set_mono_suffix
                intro!: ext
       | (drule (1) bspec, clarsimp simp: valid_pspace'_def valid_tcb'_def elim!: valid_objs_valid_tcbE'))+ *)
  sorry

lemma ep_q_refs_max:
  "\<lbrakk> ko_at' r p s; sym_refs (state_refs_of' s); r \<noteq> IdleEP \<rbrakk>
      \<Longrightarrow> (state_refs_of' s p \<subseteq> (set (epQueue r) \<times> {EPSend, EPRecv}))
       \<and> (\<forall>x\<in>set (epQueue r). \<exists>ntfnptr. state_refs_of' s x \<subseteq>
                                  {(p, TCBBlockedSend), (p, TCBBlockedRecv), (ntfnptr, TCBBound)})"
  apply (frule(1) sym_refs_ko_atD')
  apply (drule ko_at_state_refs_ofD')
  apply (case_tac r)
  sorry (*
    apply (clarsimp simp: st_tcb_at_refs_of_rev' tcb_bound_refs'_def
             | rule conjI | drule(1) bspec | drule st_tcb_at_state_refs_ofD'
             | case_tac ntfnptr)+
  done *)

lemma rescheduleRequired_invs'[wp]:
  "\<lbrace>invs'\<rbrace> rescheduleRequired \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp ssa_invs' | simp | wpc)+
  apply (clarsimp simp: invs'_def valid_state'_def)
  sorry

lemma invs_rct_ct_activatable':
  "\<lbrakk> invs' s; ksSchedulerAction s = ResumeCurrentThread \<rbrakk>
   \<Longrightarrow> st_tcb_at' activatable' (ksCurThread s) s"
  by (simp add: invs'_def valid_state'_def ct_in_state'_def)

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
       apply (clarsimp)
      sorry (*
      apply (drule state_refs_of'_elemD)
      apply (simp add: st_tcb_at_refs_of_rev')
      apply (erule pred_tcb'_weakenE)
      apply (clarsimp)
      done *)

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
      apply (clarsimp simp: st_tcb_at_refs_of_rev' dest!: st_tcb_at_state_refs_ofD')
      sorry

    with ko_at have "st_tcb_at' (Not \<circ> simple') t s"
      apply -
      apply (drule state_refs_of'_elemD)
      apply (simp add: st_tcb_at_refs_of_rev')
      apply (erule pred_tcb'_weakenE)
      apply (clarsimp)
      sorry

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

lemma rescheduleRequired_all_invs_but_ct_not_inQ:
  "\<lbrace>all_invs_but_ct_not_inQ'\<rbrace> rescheduleRequired \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre)
   apply (wp rescheduleRequired_ct_not_inQ
             valid_irq_node_lift valid_irq_handlers_lift''
             irqs_masked_lift cur_tcb_lift
             untyped_ranges_zero_lift
             | simp add: cteCaps_of_def o_def)+
  apply (auto simp: sch_act_wf_weak)
  sorry

lemma cancelAllIPC_invs'[wp]:
  "\<lbrace>invs'\<rbrace> cancelAllIPC ep_ptr \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: cancelAllIPC_def ep'_Idle_case_helper cong del: if_cong)
  apply (wpsimp wp: rescheduleRequired_all_invs_but_ct_not_inQ
                    cancel_all_invs'_helper hoare_vcg_const_Ball_lift
                    valid_global_refs_lift' valid_arch_state_lift'
                    valid_irq_node_lift ssa_invs' sts_sch_act'
                    irqs_masked_lift
              simp: sch_act_wf.simps forM_x_def)
   prefer 2
   apply assumption
  apply (rule hoare_strengthen_post [OF get_ep_sp'])
  apply (clarsimp simp: invs'_def valid_state'_def valid_ep'_def)
  apply (frule obj_at_valid_objs', fastforce)
  apply (clarsimp simp: projectKOs valid_obj'_def)
  apply (rule conjI)
   apply (metis fold_list_refs_of_replies')
  apply (rule conjI)
   apply (case_tac r; clarsimp simp: valid_ep'_def)
  apply (rule conjI[rotated])
   apply (drule(1) sym_refs_ko_atD')
   apply (case_tac r; clarsimp simp: st_tcb_at_refs_of_rev')
    apply (clarsimp elim!: if_live_state_refsE split: if_splits
           | drule(1) bspec | drule st_tcb_at_state_refs_ofD')+
  apply (drule(2) ep_q_refs_max)
  apply (erule delta_sym_refs)
   apply (clarsimp dest!: symreftype_inverse' split: if_split_asm | drule(1) bspec subsetD)+
  done

lemma cancelAllSignals_invs'[wp]:
  "\<lbrace>invs'\<rbrace> cancelAllSignals ntfn \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: cancelAllSignals_def)
  apply (rule hoare_seq_ext [OF _ get_ntfn_sp'])
  apply (case_tac "ntfnObj ntfna", simp_all)
    apply (wp, simp)
   apply (wp, simp)
  apply (rule hoare_pre)
   apply (wp rescheduleRequired_all_invs_but_ct_not_inQ
             cancel_all_invs'_helper hoare_vcg_const_Ball_lift
             valid_irq_node_lift ssa_invs' irqs_masked_lift
          | simp only: sch_act_wf.simps)+
  apply (clarsimp simp: invs'_def valid_state'_def valid_ntfn'_def)
  sorry (*
  apply (frule obj_at_valid_objs', clarsimp)
  apply (clarsimp simp: projectKOs valid_obj'_def valid_ntfn'_def)
  apply (drule(1) sym_refs_ko_atD')
  apply (rule conjI, clarsimp elim!: if_live_state_refsE)
  apply (rule conjI[rotated])
   apply (clarsimp elim!: if_live_state_refsE)
   apply (drule_tac x="(x, NTFNSignal)" in bspec)
    apply (clarsimp simp: st_tcb_at_refs_of_rev')+
   apply (drule st_tcb_at_state_refs_ofD')
   apply clarsimp
  apply (erule delta_sym_refs)
   apply (clarsimp split: if_split_asm)
  apply (clarsimp split: if_split_asm)
   apply (fastforce simp: symreftype_inverse' ntfn_bound_refs'_def)
  apply (drule_tac x="(x, NTFNSignal)" in bspec)
   apply (clarsimp simp: st_tcb_at_refs_of_rev')+
  apply (drule st_tcb_at_state_refs_ofD')
  apply (fastforce simp: symreftype_inverse' ntfn_bound_refs'_def tcb_bound_refs'_def)
  done *)

lemma cancelAllIPC_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace> cancelAllIPC ep \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: cancelAllIPC_def ep'_Idle_case_helper  cong del: if_cong)
  apply (rule hoare_seq_ext [OF _ get_ep_sp'])
  apply (rule hoare_pre)
   apply (wp set_ep_valid_objs' setSchedulerAction_valid_objs')
    apply (rule_tac Q="\<lambda>rv s. valid_objs' s \<and> (\<forall>x\<in>set (epQueue ep). tcb_at' x s)"
                    in hoare_post_imp)
     apply simp
    apply (simp add: Ball_def)
    apply (wp mapM_x_wp' sts_valid_objs'
              hoare_vcg_all_lift hoare_vcg_const_imp_lift)+
     apply simp
     sorry (*
    apply (simp add: valid_tcb_state'_def)
   apply (wp set_ep_valid_objs' hoare_vcg_all_lift hoare_vcg_const_imp_lift)
  apply (clarsimp)
  apply (frule(1) ko_at_valid_objs')
   apply (simp add: projectKOs)
  apply (clarsimp simp: valid_obj'_def valid_ep'_def)
  apply (case_tac epa, simp_all)
  done *)

lemma cancelAllSignals_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace> cancelAllSignals ntfn \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: cancelAllSignals_def)
  apply (rule hoare_seq_ext [OF _ get_ntfn_sp'])
  apply (case_tac "ntfnObj ntfna", simp_all)
    apply (wp, simp)
   apply (wp, simp)
  apply (rename_tac list)
  apply (rule_tac Q="\<lambda>rv s. valid_objs' s \<and> (\<forall>x\<in>set list. tcb_at' x s)"
                  in hoare_post_imp)
   apply (simp add: valid_ntfn'_def)
  apply (simp add: Ball_def)
  apply (wp setSchedulerAction_valid_objs' mapM_x_wp'
            sts_valid_objs' hoare_vcg_all_lift hoare_vcg_const_imp_lift
       | simp)+
  sorry (*
   apply (simp add: valid_tcb_state'_def)
  apply (wp set_ntfn_valid_objs' hoare_vcg_all_lift hoare_vcg_const_imp_lift)
  apply clarsimp
  apply (frule(1) ko_at_valid_objs')
   apply (simp add: projectKOs)
  apply (clarsimp simp: valid_obj'_def valid_ntfn'_def)
  done *)

lemma cancelAllIPC_st_tcb_at:
  "\<lbrace>st_tcb_at' P t and K (P Inactive \<and> P Restart)\<rbrace>
   cancelAllIPC epptr
   \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  unfolding cancelAllIPC_def
  apply (rule hoare_gen_asm)
  apply (wpsimp wp: mapM_x_wp' sts_st_tcb_at'_cases hoare_vcg_imp_lift threadGet_obj_at'_field
                    hoare_vcg_disj_lift replyUnlink_st_tcb_at'_wp hoare_vcg_all_lift
                    getEndpoint_wp replyUnlink_tcb_obj_at'_no_change
              simp: obj_at'_ignoring_obj[where P="tcb_at' a b" for a b]
                    obj_at'_ignoring_obj[where P="st_tcb_at' a b c" for a b c]
                    obj_at'_ignoring_obj[where P="a \<noteq> b" for a b]
           (* This gnarly obj_at'-unfolding clarsimp should only be applied to non-wp goals. *)
         | match conclusion in "\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>" \<Rightarrow> \<open>-\<close>
             \<bar> "_" \<Rightarrow> \<open>clarsimp simp: pred_tcb_at'_def obj_at'_def\<close>)+
  done

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

lemma threadSet_not_tcb[wp]:
  "\<lbrace>ko_wp_at' (\<lambda>x. P x \<and> (projectKO_opt x = (None :: tcb option))) p\<rbrace>
     threadSet f t
   \<lbrace>\<lambda>rv. ko_wp_at' (\<lambda>x. P x \<and> (projectKO_opt x = (None :: tcb option))) p\<rbrace>"
  by (clarsimp simp: threadSet_def valid_def getObject_def
                     setObject_def in_monad loadObject_default_def
                     ko_wp_at'_def projectKOs split_def in_magnitude_check
                     objBits_simps' updateObject_default_def
                     ps_clear_upd' projectKO_opt_tcb)

lemma setThreadState_not_tcb[wp]:
  "setThreadState st t \<lbrace>ko_wp_at' (\<lambda>x. P x \<and> (projectKO_opt x = (None :: tcb option))) p\<rbrace>"
  unfolding setThreadState_def scheduleTCB_def rescheduleRequired_def tcbSchedEnqueue_def
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp isSchedulable_inv)
  done

lemma tcbSchedEnqueue_unlive:
  "\<lbrace>ko_wp_at' (\<lambda>x. \<not> live' x \<and> (projectKO_opt x = (None :: tcb option))) p
    and tcb_at' t\<rbrace>
    tcbSchedEnqueue t
   \<lbrace>\<lambda>_. ko_wp_at' (\<lambda>x. \<not> live' x \<and> (projectKO_opt x = (None :: tcb option))) p\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wp | simp add: setQueue_def bitmap_fun_defs)+
  done

lemma cancelAll_unlive_helper:
  "\<lbrace>\<lambda>s. (\<forall>x\<in>set xs. tcb_at' x s) \<and>
     ko_wp_at' (\<lambda>x. \<not> live' x \<and> (projectKO_opt x = (None :: tcb option))) p s\<rbrace>
     mapM_x (\<lambda>t. do
                   y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                   tcbSchedEnqueue t
                 od) xs
   \<lbrace>\<lambda>rv. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp')
   apply (rule hoare_pre)
    apply (wp tcbSchedEnqueue_unlive hoare_vcg_const_Ball_lift)
   apply clarsimp
  apply (clarsimp elim!: ko_wp_at'_weakenE)
  done

context begin interpretation Arch . (*FIXME: arch_split*)

lemma rescheduleRequired_unlive:
  "\<lbrace>\<lambda>s. ko_wp_at' (Not \<circ> live') p s \<and> ksSchedulerAction s \<noteq> SwitchToThread p\<rbrace>
      rescheduleRequired
   \<lbrace>\<lambda>rv. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp | simp | wpc)+
   apply (simp add: tcbSchedEnqueue_def unless_def
                    threadSet_def setQueue_def threadGet_def)
   apply (wp setObject_ko_wp_at getObject_tcb_wp
            | simp add: objBits_simps' bitmap_fun_defs split del: if_split)+
  sorry (*
  apply (clarsimp simp: o_def)
  apply (drule obj_at_ko_at')
  apply clarsimp
  done *)

lemma cancelAllIPC_unlive:
  "\<lbrace>valid_objs' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)\<rbrace>
      cancelAllIPC ep \<lbrace>\<lambda>rv. ko_wp_at' (Not \<circ> live') ep\<rbrace>"
  apply (simp add: cancelAllIPC_def ep'_Idle_case_helper)
  apply (rule hoare_seq_ext [OF _ get_ep_sp'])
  apply (rule hoare_pre)
   apply (wp cancelAll_unlive_helper setObject_ko_wp_at
             hoare_vcg_const_Ball_lift rescheduleRequired_unlive
             mapM_x_wp'
        | simp add: objBits_simps')+
  sorry (*
  apply (clarsimp simp: projectKO_opt_tcb)
  apply (frule(1) obj_at_valid_objs')
  apply (intro conjI impI)
  apply (clarsimp simp: valid_obj'_def valid_ep'_def projectKOs
                        obj_at'_def pred_tcb_at'_def ko_wp_at'_def
                 split: endpoint.split_asm)+
  done *)

lemma cancelAllSignals_unlive:
  "\<lbrace>\<lambda>s. valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s
      \<and> obj_at' (\<lambda>ko. ntfnBoundTCB ko = None) ntfnptr s\<rbrace>
      cancelAllSignals ntfnptr \<lbrace>\<lambda>rv. ko_wp_at' (Not \<circ> live') ntfnptr\<rbrace>"
  apply (simp add: cancelAllSignals_def)
  apply (rule hoare_seq_ext [OF _ get_ntfn_sp'])
  apply (case_tac "ntfnObj ntfn", simp_all add: setNotification_def)
    apply wp
  sorry (*
    apply (fastforce simp: obj_at'_real_def projectKOs
                     dest: obj_at_conj'
                     elim: ko_wp_at'_weakenE)
   apply wp
   apply (fastforce simp: obj_at'_real_def projectKOs
                    dest: obj_at_conj'
                    elim: ko_wp_at'_weakenE)
  apply (wp rescheduleRequired_unlive)
   apply (wp cancelAll_unlive_helper)
   apply ((wp mapM_x_wp' setObject_ko_wp_at hoare_vcg_const_Ball_lift)+,
          simp_all add: objBits_simps', simp_all)
   apply (fold setNotification_def, wp)
  apply (intro conjI[rotated])
     apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
    apply (clarsimp simp: projectKOs projectKO_opt_tcb)
   apply (fastforce simp: ko_wp_at'_def valid_obj'_def valid_ntfn'_def
                         obj_at'_def projectKOs)+
  done *)

crunch ep_at'[wp]: tcbSchedEnqueue "ep_at' epptr"
  (simp: unless_def)

declare if_cong[cong]

lemma insert_eqD:
  "A = insert a B \<Longrightarrow> a \<in> A"
  by blast

lemma cancelBadgedSends_filterM_helper':
  notes if_cong[cong del]
  shows
  "\<forall>ys.
   \<lbrace>\<lambda>s. all_invs_but_sym_refs_ct_not_inQ' s
           \<and> ex_nonz_cap_to' epptr s \<and> ep_at' epptr s
           \<and> sym_refs ((state_refs_of' s) (epptr := set (xs @ ys) \<times> {EPSend}))
           \<and> (\<forall>y \<in> set (xs @ ys). state_refs_of' s y = {(epptr, TCBBlockedSend)}
                                       \<union> {r \<in> state_refs_of' s y. snd r = TCBBound})
           \<and> distinct (xs @ ys)\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> getThreadState t;
                      if blockingIPCBadge st = badge then
                        do y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                           y \<leftarrow> tcbSchedEnqueue t;
                           return False
                        od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv s. all_invs_but_sym_refs_ct_not_inQ' s
           \<and> ex_nonz_cap_to' epptr s \<and> ep_at' epptr s
           \<and> sym_refs ((state_refs_of' s) (epptr := (set rv \<union> set ys) \<times> {EPSend}))
           \<and> (\<forall>y \<in> set ys. state_refs_of' s y = {(epptr, TCBBlockedSend)}
                                   \<union> {r \<in> state_refs_of' s y. snd r = TCBBound})
           \<and> distinct rv \<and> distinct (xs @ ys) \<and> set rv \<subseteq> set xs \<and> (\<forall>x \<in> set xs. tcb_at' x s)\<rbrace>"
  apply (rule_tac xs=xs in rev_induct)
   apply clarsimp
   apply wp
   apply clarsimp
  apply (clarsimp simp: filterM_append bind_assoc simp del: set_append distinct_append)
  apply (drule spec, erule hoare_seq_ext[rotated])
  apply (rule hoare_seq_ext [OF _ gts_inv'])
  apply (rule hoare_pre)
   apply (wp valid_irq_node_lift hoare_vcg_const_Ball_lift sts_sch_act'
             sch_act_wf_lift valid_irq_handlers_lift'' cur_tcb_lift irqs_masked_lift
             sts_st_tcb' sts_valid_queues setThreadState_not_st
             tcbSchedEnqueue_not_st
             untyped_ranges_zero_lift
        | clarsimp simp: cteCaps_of_def o_def)+
  apply (frule insert_eqD, frule state_refs_of'_elemD)
  apply (clarsimp simp: valid_tcb_state'_def st_tcb_at_refs_of_rev')
  apply (frule pred_tcb_at')
  apply (rule conjI[rotated], blast)
  apply clarsimp
  apply (intro conjI)
      apply (clarsimp simp: valid_pspace'_def valid_tcb'_def elim!: valid_objs_valid_tcbE' dest!: st_tcb_ex_cap'')
     apply (fastforce dest!: st_tcb_ex_cap'')
    apply (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def)
  sorry (*
   apply (erule delta_sym_refs)
    apply (fastforce elim!: obj_atE'
                      simp: state_refs_of'_def projectKOs tcb_bound_refs'_def
                            subsetD symreftype_inverse'
                     split: if_split_asm)+
  done *)

lemmas cancelBadgedSends_filterM_helper
    = spec [where x=Nil, OF cancelBadgedSends_filterM_helper', simplified]

lemma cancelBadgedSends_invs[wp]:
  notes if_cong[cong del]
  shows
  "\<lbrace>invs'\<rbrace> cancelBadgedSends epptr badge \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: cancelBadgedSends_def)
  apply (rule hoare_seq_ext [OF _ get_ep_sp'])
  apply (case_tac ep, simp_all)
    apply ((wp | simp)+)[2]
  apply (subst bind_assoc [where g="\<lambda>_. rescheduleRequired",
                           symmetric])+
  apply (rule hoare_seq_ext
                [OF rescheduleRequired_all_invs_but_ct_not_inQ])
  apply (simp add: list_case_return cong: list.case_cong)
  apply (rule hoare_pre, wp valid_irq_node_lift irqs_masked_lift)
  sorry (*
    apply simp
    apply (rule hoare_strengthen_post,
           rule cancelBadgedSends_filterM_helper[where epptr=epptr])
    apply (clarsimp simp: ep_redux_simps3 fun_upd_def[symmetric])
    apply (clarsimp simp add: valid_ep'_def split: list.split)
    apply blast
   apply (wp valid_irq_node_lift irqs_masked_lift | wp (once) sch_act_sane_lift)+
  apply (clarsimp simp: invs'_def valid_state'_def
                        valid_ep'_def fun_upd_def[symmetric]
                        obj_at'_weakenE[OF _ TrueI])
  apply (frule obj_at_valid_objs', clarsimp)
  apply (clarsimp simp: valid_obj'_def valid_ep'_def projectKOs)
  apply (frule if_live_then_nonz_capD', simp add: obj_at'_real_def)
   apply (clarsimp simp: projectKOs)
  apply (frule(1) sym_refs_ko_atD')
  apply (clarsimp simp add: fun_upd_idem
                            st_tcb_at_refs_of_rev')
  apply (drule (1) bspec, drule st_tcb_at_state_refs_ofD', clarsimp)
  apply (fastforce simp: set_eq_subset tcb_bound_refs'_def)
  done *)

lemma cancel_badged_sends_corres:
  "corres dc (invs and valid_sched and ep_at epptr) (invs' and ep_at' epptr)
         (cancel_badged_sends epptr bdg) (cancelBadgedSends epptr bdg)"
  apply (simp add: cancel_badged_sends_def cancelBadgedSends_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_ep_corres get_simple_ko_sp get_ep_sp',
                                 where Q="invs and valid_sched" and Q'=invs'])
    apply simp_all
  apply (case_tac ep, simp_all add: ep_relation_def)
  apply (simp add: filterM_mapM list_case_return cong: list.case_cong)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor [OF _ set_ep_corres])
       apply (rule corres_split_eqr[OF _ _ _ hoare_post_add[where R="\<lambda>_. valid_objs'"]])
          apply (rule corres_split [OF rescheduleRequired_corres])
            apply (rule set_ep_corres)
            apply (simp split: list.split add: ep_relation_def)
           apply (wp weak_sch_act_wf_lift_linear)+
         apply (rule_tac S="(=)"
                     and Q="\<lambda>xs s. (\<forall>x \<in> set xs. (epptr, TCBBlockedSend) \<in> state_refs_of s x) \<and> distinct xs \<and> valid_etcbs s"
                    and Q'="\<lambda>xs s. (\<forall>x \<in> set xs. tcb_at' x s) \<and> weak_sch_act_wf (ksSchedulerAction s) s \<and> Invariants_H.valid_queues s \<and> valid_queues' s \<and> valid_objs' s"
                     in corres_mapM_list_all2[where r'="(=)"],
                simp_all add: list_all2_refl)[1]
           apply (clarsimp simp: liftM_def[symmetric] o_def)
           apply (rule corres_guard_imp)
             apply (rule corres_split [OF _ gts_corres])
               apply (rule_tac F="\<exists>pl. st = Structures_A.BlockedOnSend epptr pl"
                            in corres_gen_asm)
               apply (clarsimp simp: o_def dc_def[symmetric] liftM_def)
  sorry (*
               apply (rule corres_split [OF _ sts_corres])
                  apply (rule corres_split[OF _ tcbSchedEnqueue_corres])
                    apply (rule corres_trivial)
                    apply simp
                   apply wp+
                 apply simp
                apply (wp sts_valid_queues gts_st_tcb_at)+
            apply (clarsimp simp: valid_tcb_state_def tcb_at_def st_tcb_def2
                                  st_tcb_at_refs_of_rev
                           dest!: state_refs_of_elemD elim!: tcb_at_is_etcb_at[rotated])
           apply (simp add: is_tcb_def)
          apply (wp hoare_vcg_const_Ball_lift gts_wp | clarsimp)+
            apply (wp gts_st_tcb_at hoare_vcg_const_Ball_lift hoare_vcg_imp_lift
                      weak_sch_act_wf_lift_linear mapM_wp'
                      sts_st_tcb' sts_valid_queues setThreadState_valid_objs'
                      set_thread_state_runnable_weak_valid_sched_action
                      | clarsimp simp: valid_tcb_state'_def)+
      apply (simp add: ep_relation_def)
     apply (wp hoare_vcg_const_Ball_lift weak_sch_act_wf_lift_linear set_ep_valid_objs'
                | simp)+
   apply (clarsimp simp: conj_comms)
   apply (frule sym_refs_ko_atD, clarsimp+)
   apply (rule obj_at_valid_objsE, assumption+, clarsimp+)
   apply (clarsimp simp: valid_obj_def valid_ep_def valid_sched_def valid_sched_action_def)
   apply (rule conjI, erule obj_at_weakenE, clarsimp simp: is_ep)
   apply (clarsimp simp: st_tcb_at_refs_of_rev)
   apply (drule(1) bspec, drule st_tcb_at_state_refs_ofD, clarsimp)
   apply (simp add: set_eq_subset)
  apply (clarsimp simp: obj_at'_weakenE[OF _ TrueI])
  apply (drule ko_at_valid_objs', clarsimp)
   apply (simp add: projectKOs)
  apply (clarsimp simp: valid_obj'_def valid_ep'_def invs_weak_sch_act_wf
                        invs'_def valid_state'_def)
  done *)

crunches schedContextCancelYieldTo, tcbReleaseRemove
  for tcbQueued[wp]: "obj_at' (\<lambda>obj. \<not> tcbQueued obj) t"
  (wp: crunch_wps simp: crunch_simps setReleaseQueue_def setReprogramTimer_def getReleaseQueue_def)

lemma suspend_unqueued:
  "\<lbrace>\<top>\<rbrace> suspend t \<lbrace>\<lambda>rv. obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  apply (simp add: suspend_def unless_def tcbSchedDequeue_def)
  apply (wp hoare_vcg_if_lift hoare_vcg_conj_lift hoare_vcg_imp_lift)
          apply (wpsimp simp: threadGet_def comp_def wp: getObject_tcb_wp)+
      apply (rule hoare_strengthen_post, rule hoare_post_taut)
      apply (fastforce simp: obj_at'_def projectKOs)
     apply (rule hoare_post_taut)
    apply wpsimp+
  done

crunch unqueued: prepareThreadDelete "obj_at' (Not \<circ> tcbQueued) t"
crunch inactive: prepareThreadDelete "st_tcb_at' ((=) Inactive) t'"
crunch nonq: prepareThreadDelete " \<lambda>s. \<forall>d p. t' \<notin> set (ksReadyQueues s (d, p))"

end
end
