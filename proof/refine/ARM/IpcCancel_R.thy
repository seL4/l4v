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
  and it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps cancelSignal_tcb_at' simp: crunch_simps pred_tcb_at'_def)

crunch pred_tcb_at'[wp]: emptySlot "pred_tcb_at' proj P t"
  (wp: setCTE_pred_tcb_at')

defs capHasProperty_def:
  "capHasProperty ptr P \<equiv> cte_wp_at' (\<lambda>c. P (cteCap c)) ptr"
end

lemma cancelIPC_simple[wp]:
  "\<lbrace>\<top>\<rbrace> cancelIPC t \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  unfolding cancelIPC_def blockedCancelIPC_def
  apply (wpsimp wp: setThreadState_st_tcb gts_wp' threadSet_wp
              simp: Let_def tcb_obj_at'_pred_tcb'_set_obj'_iff)
  apply (clarsimp simp: st_tcb_at'_def o_def obj_at'_def isBlockedOnReply_def)
  done

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
  assumes delete_one_inQ_queues:
    "\<lbrace>valid_inQ_queues and valid_objs'\<rbrace> cteDeleteOne sl \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
  (* FIXME RT: not true any more: assumes delete_one_sch_act_simple:
    "\<lbrace>sch_act_simple\<rbrace> cteDeleteOne sl \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"  *)
  (* FIXME RT: not true any more: assumes delete_one_sch_act_not:
    "\<And>t. \<lbrace>sch_act_not t\<rbrace> cteDeleteOne sl \<lbrace>\<lambda>rv. sch_act_not t\<rbrace>" *)
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

lemma cancelIPC_simple':
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of' s)\<rbrace>
   cancelIPC t
   \<lbrace>\<lambda>_. st_tcb_at' simple' t\<rbrace>"
  unfolding cancelIPC_def Let_def getBlockingObject_def blockedCancelIPC_def
  apply (wpsimp wp: sts_st_tcb_at'_cases hoare_vcg_all_lift hoare_vcg_imp_lift
                    hoare_pre_cont[where a="getEndpoint x" and P="\<lambda>rv _. P rv" for x P]
                    hoare_disjI2[where f="getEndpoint x" and Q="\<lambda>_. tcb_at' y" for x y]
                    replyUnlink_st_tcb_at'_sym_ref replyRemoveTCB_st_tcb_at'_sym_ref
                    cancelSignal_st_tcb_at' threadSet_pred_tcb_at_state[where p=t] gts_wp')
  apply (rule conjI; clarsimp)
   apply normalise_obj_at'
   apply (rename_tac rptr tcb reply)
   apply (erule notE)
   apply (frule(1) sym_ref_Receive_or_Reply_replyTCB', fast)
   apply (clarsimp simp: obj_at'_def projectKO_eq project_inject)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

context begin interpretation Arch .
crunch typ_at'[wp]: emptySlot "\<lambda>s. P (typ_at' T p s)"
end

sublocale delete_one_conc_pre < delete_one: typ_at_all_props' "cteDeleteOne slot"
  by typ_at_props'

declare if_weak_cong [cong]
declare delete_remove1 [simp]
declare delete.simps [simp del]

lemma sch_act_wf_weak_sch_act_wf[elim!]:
  "sch_act_wf (ksSchedulerAction s) s \<Longrightarrow> weak_sch_act_wf (ksSchedulerAction s) s"
  by (clarsimp simp: weak_sch_act_wf_def)

lemma invs_weak_sch_act_wf[elim!]:
  "invs' s \<Longrightarrow> weak_sch_act_wf (ksSchedulerAction s) s"
  apply (drule invs_sch_act_wf')
  by clarsimp

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

lemma replyTCB_update_corres:
  "corres dc (reply_at rp) (reply_at' rp)
            (set_reply_obj_ref reply_tcb_update rp new)
            (updateReply rp (replyTCB_update (\<lambda>_. new)))"
  apply (simp add: update_sk_obj_ref_def updateReply_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ get_reply_corres])
      apply (rule set_reply_corres)
      apply (simp add: reply_relation_def)
  by (wpsimp simp: obj_at'_def replyPrev_same_def)+

lemma setReply_valid_tcb'[wp]:
  "setReply rp new  \<lbrace>valid_tcb' tcb\<rbrace>"
  apply (clarsimp simp: setReply_def)
  apply (rule setObject_valid_tcb')
  done

lemma setReply_valid_tcbs'[wp]:
  "setReply rp new  \<lbrace>valid_tcbs'\<rbrace>"
  unfolding valid_tcbs'_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
    apply (wpsimp simp: setReply_def )+
    apply (wpsimp wp: set_reply'.setObject_wp)+
  done

lemma reply_unlink_tcb_corres:
  "\<lbrakk>st = Structures_A.BlockedOnReceive ep (Some rp) pl
    \<or> st = Structures_A.BlockedOnReply rp\<rbrakk> \<Longrightarrow>
   corres dc
     (valid_tcbs and pspace_aligned and pspace_distinct
       and st_tcb_at ((=) st) t and reply_tcb_reply_at ((=) (Some t)) rp)
          (valid_tcbs' and valid_release_queue_iff)
        (reply_unlink_tcb t rp) (replyUnlink rp t)" (is "_ \<Longrightarrow> corres _ _ ?conc_guard _ _")
  apply (rule_tac Q="?conc_guard
              and st_tcb_at' (\<lambda>st. st = BlockedOnReceive ep (receiver_can_grant pl) (Some rp)
                                 \<or> st = BlockedOnReply (Some rp)) t" in corres_cross_over_guard)
   apply clarsimp
   apply (drule (1) st_tcb_at_coerce_concrete; clarsimp simp: state_relation_def)
   apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  apply (simp add: reply_unlink_tcb_def replyUnlink_def liftM_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ get_reply_corres])
      apply (rule corres_assert_gen_asm_l)
      apply (rename_tac reply'; prop_tac "replyTCB reply' = Some t")
       apply (clarsimp simp: reply_relation_def)
      apply simp
      apply (rule corres_split[OF _ gts_corres])
        apply (rule corres_assert_gen_asm_l)
        apply (rule corres_stateAssert_implied[where P'=\<top>, simplified])
         apply (rule corres_split[OF _ replyTCB_update_corres])
           apply (rule sts_corres)
           apply (clarsimp simp: thread_state_relation_def)
          apply wpsimp

         apply (wpsimp simp: updateReply_def)
        apply (fastforce simp: replyUnlink_assertion_def thread_state_relation_def)
       apply (wpsimp wp: hoare_vcg_disj_lift gts_wp get_simple_ko_wp)+
   apply (clarsimp simp: sk_obj_at_pred_def obj_at_def is_reply pred_tcb_at_def is_tcb)
  apply (clarsimp simp: obj_at'_def st_tcb_at'_def projectKOs)
  apply (prop_tac "reply_at' rp s")
   apply (fastforce simp: valid_tcbs'_def valid_tcb'_def valid_tcb_state'_def)
  apply (clarsimp simp: obj_at'_def projectKOs)
  done

lemma setNotification_valid_tcb'[wp]:
  "setNotification ntfn val \<lbrace>valid_tcb' tcb\<rbrace>"
  apply (clarsimp simp: setNotification_def)
  apply (rule setObject_valid_tcb')
  done

lemma setNotification_valid_tcbs'[wp]:
  "setNotification ntfn val \<lbrace>valid_tcbs'\<rbrace>"
  unfolding valid_tcbs'_def
  by (wpsimp wp: set_ntfn'.setObject_wp hoare_vcg_all_lift hoare_vcg_imp_lift'
           simp: setNotification_def)+

lemma setEndpoint_valid_tcb'[wp]:
  "setEndpoint epPtr val \<lbrace>valid_tcb' tcb\<rbrace>"
  apply (clarsimp simp: setEndpoint_def)
  apply (rule setObject_valid_tcb')
  done

lemma setEndpoint_valid_tcbs'[wp]:
  "setEndpoint ePtr val \<lbrace>valid_tcbs'\<rbrace>"
  unfolding valid_tcbs'_def
  by (wpsimp wp: set_ep'.setObject_wp hoare_vcg_all_lift hoare_vcg_imp_lift'
           simp: setEndpoint_def)+

lemma replyUnlink_valid_tcbs'[wp]:
  "replyUnlink replyPtr tcbPtr \<lbrace>valid_tcbs'\<rbrace>"
  apply (clarsimp simp: replyUnlink_def getReply_def
                        updateReply_def)
  apply (wpsimp wp: set_reply'.getObject_wp set_reply'.getObject_wp gts_wp'
              simp: valid_tcb_state'_def )
  done

lemma blocked_cancel_ipc_corres:
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
    apply (rule corres_split [OF _ get_ep_corres])
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
       apply (clarsimp simp: obj_relation_cuts_def2 obj_at'_def reply_relation_def projectKOs)
       apply (rename_tac ko)
       apply (case_tac ko; simp)
       apply (rename_tac reply')
       apply (frule_tac x=rp in pspace_alignedD', simp)
       apply (drule_tac x=rp in pspace_distinctD', simp)
       apply (clarsimp simp: reply_relation_def)
       \<comment>\<open>main corres proof\<close>
      apply (rule corres_gen_asm)
      apply (erule disjE; clarsimp simp: ep_relation_def get_ep_queue_def split del: if_split)
       \<comment>\<open>BlockedOnReceive\<close>
       apply (rename_tac list)
       apply (cases reply_opt;
              simp split del: if_split add: if_return_closure bind_assoc cong: if_cong)
         \<comment>\<open>reply_opt = None\<close>
        apply (rule corres_guard_imp)
          apply (rule corres_split [OF _ set_ep_corres])
             apply (rule sts_corres)
             apply simp
            apply (simp add: ep_relation_def split: list.split)
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
                      in corres_split [OF _ set_ep_corres])
            apply (rule corres_guard_imp)
              apply (rule corres_split [OF _ reply_unlink_tcb_corres])
                 apply (rule sts_corres)
                 apply simp
                apply fastforce
               apply wpsimp
              apply (wpsimp wp: replyUnlink_valid_objs')
             apply (fastforce simp: pred_tcb_at_def obj_at_def is_tcb)
            apply (fastforce simp: obj_at'_def pred_tcb_at'_def)
           apply (simp add: ep_relation_def split: list.split)
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
       apply (rule conjI, clarsimp simp: obj_at'_def projectKOs ps_clear_upd' objBits_simps)
       apply (rule conjI; clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs ps_clear_upd')
       apply (intro conjI impI; clarsimp?)
         apply (erule valid_objs'_ep_update)
          apply (case_tac "remove1 t list"
                 ; clarsimp simp: valid_ep'_def obj_at'_def projectKOs
                 ; metis distinct.simps(2) distinct_remove1 list.set_intros(1) list.set_intros(2)
                         set_remove1)
         apply (clarsimp simp: obj_at'_def projectKOs)
        apply ((clarsimp simp: obj_at'_def projectKOs valid_ep'_def)+)[2]
        apply (erule valid_release_queue_ksPSpace_update)
         apply ((clarsimp simp: ko_wp_at'_def objBitsKO_def koTypeOf_def)+)[2]
       apply (erule valid_release_queue'_ksPSpace_update)
        apply ((clarsimp simp: ko_wp_at'_def objBitsKO_def koTypeOf_def)+)[2]
      \<comment>\<open>BlockedOnSend\<close>
      apply (rename_tac list)
      apply (rule corres_guard_imp)
        apply (rule corres_split [OF _ set_ep_corres])
           apply (rule sts_corres)
           apply simp
          apply (simp add: ep_relation_def split: list.split)
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
   apply (frule (2) Receive_or_Send_ep_at)
   apply (clarsimp simp: obj_at_def is_ep pred_tcb_at_def)
   apply (rule conjI, clarsimp)
    apply (drule (1) BlockedOnReceive_reply_tcb_reply_at[rotated])
     apply (fastforce simp: pred_tcb_at_def obj_at_def)
    apply (clarsimp simp: sk_obj_at_pred_def obj_at_def)
   apply (rule conjI)
    apply (erule (1) valid_objsE[where x=epPtr], clarsimp simp: valid_obj_def)
   apply (erule disjE)
    apply (fastforce dest!: sym_ref_BlockedOnReceive_RecvEP)
   apply (fastforce dest!: sym_ref_BlockedOnSend_SendEP)
  apply clarsimp
  apply (rule context_conjI)
   apply (erule (1) Receive_or_Send_ep_at'[rotated])
   apply (fastforce simp: thread_state_relation_def)
  apply (clarsimp simp: obj_at'_def projectKOs )
  apply (rule conjI)
   apply (erule (1) valid_objsE', clarsimp simp: valid_obj'_def)
  apply (erule disjE)
   apply (fastforce dest!: sym_ref_BlockedOnReceive_RecvEP' simp: ko_wp_at'_def)
  apply (fastforce dest!: sym_ref_BlockedOnSend_SendEP' simp: ko_wp_at'_def)
  done

lemma cancel_signal_corres:
  "corres dc
          (invs and valid_ready_qs and st_tcb_at ((=) (Structures_A.BlockedOnNotification ntfn)) t)
          (invs' and st_tcb_at' ((=) (BlockedOnNotification ntfn)) t)
          (cancel_signal t ntfn)
          (cancelSignal t ntfn)"
  apply add_sym_refs
  apply add_ready_qs_runnable
  apply (simp add: cancel_signal_def cancelSignal_def Let_def)
  apply (rule corres_stateAssert_add_assertion[where P'=\<top>, simplified, rotated])
   apply (clarsimp simp: ready_qs_runnable_def)
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
  apply (intro conjI impI allI; fastforce?)
  apply (drule sym_refs_st_tcb_atD', fastforce)
  apply (fastforce simp: isWaitingNtfn_def ko_wp_at'_def obj_at'_def projectKOs
                         ntfn_bound_refs'_def get_refs_def
                  split: Structures_H.notification.splits ntfn.splits option.splits)
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
    "\<And>p. \<lbrace>invs' and sch_act_simple\<rbrace> cteDeleteOne p \<lbrace>\<lambda>rv. invs'\<rbrace>"

locale delete_one = delete_one_conc + delete_one_abs +
  assumes delete_one_corres:
    "corres dc (einvs and cte_wp_at can_fast_finalise ptr)
               (invs' and cte_at' (cte_map ptr))
          (cap_delete_one ptr) (cteDeleteOne (cte_map ptr))"

(* reply_remove_tcb_corres *)

lemma gbep_ret':
  "\<lbrakk> st = BlockedOnReceive epPtr r d \<or> st = BlockedOnSend epPtr p1 p2 p3 p4 \<rbrakk>
      \<Longrightarrow> getBlockingObject st = return epPtr"
  by (auto simp add: getBlockingObject_def epBlocked_def assert_opt_def)

(* FIXME RT: update the one in ArchFinalise_AI; don't want invs *)
lemma sc_with_reply_None_no_reply_sc:
  "\<lbrakk>kheap s rp = Some (kernel_object.Reply reply); valid_objs s; sym_refs (state_refs_of s);
    valid_replies s; sc_with_reply rp s = None\<rbrakk>
       \<Longrightarrow> reply_sc reply = None"
  apply (rule ccontr, clarsimp simp: obj_at_def)
  apply (drule (3) reply_sc_refs)
  apply (drule_tac sc=y in valid_replies_sc_with_reply_None)
   apply (clarsimp simp: sc_at_ppred_def obj_at_def)+
  done

(* FIXME RT: update the one in Invariant_AI; we don't need valid_objs *)
lemma reply_sc_refs':
  "\<lbrakk>reply_sc reply = Some t; sym_refs (state_refs_of s);
    kheap s rptr = Some (Structures_A.Reply reply)\<rbrakk>
  \<Longrightarrow> \<exists>sc n. kheap s t = Some (Structures_A.SchedContext sc n) \<and>
     (rptr \<in> set (sc_replies sc))"
  apply (drule sym_refs_ko_atD[rotated])
   apply (simp add: obj_at_def)
  apply (clarsimp simp: get_refs_def2 obj_at_def valid_obj_def valid_reply_def refs_of_rev
                        valid_bound_obj_def is_sc_obj_def state_refs_of_def image_iff)
  done

(* FIXME RT: replace the one in ArchFinalise_AI *)
lemma sc_with_reply_None_reply_sc_reply_at:
  "\<lbrakk> sc_with_reply rp s = None; reply_at rp s;
      sym_refs (state_refs_of s); valid_replies s\<rbrakk>
       \<Longrightarrow> reply_sc_reply_at ((=) None) rp s"
  apply (rule ccontr, clarsimp simp: obj_at_def reply_sc_reply_at_def is_reply)
  apply (drule not_sym, clarsimp)
  apply (drule (2) reply_sc_refs')
  apply (drule_tac sc=y in valid_replies_sc_with_reply_None, simp)
   apply (clarsimp simp: sc_at_ppred_def obj_at_def)+
  done

(* replyClean *)

crunches cleanReply
 for valid_tcbs'[wp]: valid_tcbs'

lemma no_fail_setReply [wp]:
  "no_fail (reply_at' p) (setReply p reply)"
  unfolding setReply_def
  by (wpsimp simp: objBits_simps)

lemma no_fail_updateReply [wp]:
  "no_fail (reply_at' rp) (updateReply rp f)"
  unfolding updateReply_def by wpsimp

lemma no_fail_cleanReply [wp]:
  "no_fail (reply_at' rp) (cleanReply rp)"
  unfolding cleanReply_def
  apply (rule no_fail_pre, rule no_fail_bind)
     apply (wpsimp wp: updateReply_wp_all)+
  apply (clarsimp simp: obj_at'_def ps_clear_upd' objBits_simps' projectKOs)
  done

lemma replySc_None_not_head:
  "replySc reply = None \<longleftrightarrow> \<not> isHead (replyNext reply)"
  by (fastforce simp: isHead_def getHeadScPtr_def split: reply_next.split_asm option.split_asm)

(* reply_at_cross with property *)
(* RT FIXME: use this to define reply_at_cross; do the same for other objects *)
lemma reply_at_prop_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  assumes P: "\<And>r r'. reply_relation r r' \<Longrightarrow> P r \<Longrightarrow> P' r'"
  assumes t: "obj_at (\<lambda>ko. \<exists>r. ko = Structures_A.Reply r \<and> P r) ptr s"
  shows "obj_at' (\<lambda>r'::reply. P' r') ptr s'"
  using assms
  apply (clarsimp simp: obj_at_def is_reply)
  apply (drule (1) pspace_relation_absD, clarsimp)
  apply (case_tac z; simp)
  by (fastforce dest!: aligned_distinct_obj_at'I[where 'a=reply] elim: obj_at'_weakenE)

lemma reply_sc_reply_at_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  assumes t: "reply_sc_reply_at ((=) sc_opt) rp s"
  shows "obj_at' (\<lambda>ko::reply. replySc ko = sc_opt) rp s'"
  using assms
  unfolding reply_sc_reply_at_def
  apply -
  apply (erule reply_at_prop_cross[OF _ ps _ t[simplified reply_sc_reply_at_def]])
  by (clarsimp simp: reply_relation_def)

(* sr_inv lemmas for reply_remove_tcb_corres *)

lemma pspace_relation_reply_at:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "ksPSpace s' p = Some (KOReply reply')"
  shows "reply_at p s" using assms
  apply -
  apply (erule(1) pspace_dom_relatedE)
  apply (erule(1) obj_relation_cutsE)
  apply (clarsimp simp: other_obj_relation_def is_reply obj_at_def
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        ARM_A.arch_kernel_obj.split_asm)+
  done

lemma next_is_not_head[simp]:
  "isNext x \<Longrightarrow> \<not> isHead x"
  by (clarsimp simp: isNext_def isHead_def split: option.splits reply_next.splits)

context begin interpretation Arch .

lemma updateReply_sr_inv:
  "\<lbrakk>\<forall>s s' r r'. (P and ko_at (kernel_object.Reply r) rp) s \<longrightarrow>
                (P' and ko_at' r' rp) s' \<longrightarrow>
                 reply_relation r r' \<longrightarrow> reply_relation r (f r');
    \<forall>s s' reply'. pspace_relation (kheap s) (ksPSpace s') \<longrightarrow>
                (P' and ko_at' reply' rp) s' \<longrightarrow>
                (P and reply_at rp) s \<longrightarrow>
                 sc_replies_relation s s' \<longrightarrow>
                 sc_replies_relation s(s'\<lparr>ksPSpace := (ksPSpace s')(rp \<mapsto> KOReply (f reply'))\<rparr>)\<rbrakk>
   \<Longrightarrow> sr_inv P P' (updateReply rp f)"
  unfolding sr_inv_def updateReply_def setReply_def getReply_def
  apply (clarsimp simp: setReply_def getReply_def getObject_def setObject_def projectKOs
                        updateObject_default_def loadObject_default_def split_def
                        in_monad return_def fail_def objBits_simps' in_magnitude_check
                 split: if_split_asm option.split_asm)
  apply (rename_tac reply')
  apply (prop_tac "ko_at' reply' rp s'")
   apply (clarsimp simp: obj_at'_def objBits_simps' projectKOs)
  apply (frule (1) pspace_relation_reply_at[OF state_relation_pspace_relation])
  apply (clarsimp simp: obj_at_def is_reply)
  apply (rename_tac reply)
  apply (clarsimp simp: state_relation_def)
  apply (rule conjI)
   apply (frule (1) pspace_relation_absD)
   apply clarsimp
   apply (erule (2) pspace_relation_reply_update_conc_only)
   apply (clarsimp simp: objBits_simps')
  apply (clarsimp simp: caps_of_state_after_update cte_wp_at_after_update
                        swp_def fun_upd_def obj_at_def map_to_ctes_upd_other
              simp del: fun_upd_def)
  done

lemma updateReply_sr_inv_prev:
  "sr_inv ((\<lambda>s. sc_with_reply rp s = None) and valid_replies)
           (reply_at' rp) (updateReply rp (replyPrev_update (\<lambda>_. Nothing)))"
  apply (rule updateReply_sr_inv)
   apply (clarsimp simp: reply_relation_def)
  apply clarsimp
  by (erule (4) sc_replies_relation_sc_with_reply_None
                   [where rp=rp and
                           f="(replyPrev_update (\<lambda>_. Nothing))", simplified])

lemma updateReply_sr_inv_next:
  "sr_inv (P and (\<lambda>s. sc_with_reply rp s = None) and valid_replies
           and (\<lambda>s. sym_refs (state_refs_of s)))
           P' (updateReply rp (replyNext_update (\<lambda>_. Nothing)))"
  unfolding updateReply_def sr_inv_def
  apply (clarsimp simp: setReply_def getReply_def getObject_def setObject_def projectKOs
                        updateObject_default_def loadObject_default_def split_def
                        in_monad return_def fail_def objBits_simps' in_magnitude_check
                 split: if_split_asm option.split_asm)
  apply (rename_tac reply')
  apply (frule (1) pspace_relation_reply_at[OF state_relation_pspace_relation])
  apply (clarsimp simp: obj_at_def is_reply obj_at'_def projectKOs)
  apply (rename_tac reply)
  apply (frule sc_with_reply_None_reply_sc_reply_at)
     apply (clarsimp simp: obj_at_def is_reply)
    apply simp+
  apply (clarsimp simp: reply_sc_reply_at_def obj_at_def state_relation_def)
  apply (rule conjI)
   apply (frule (1) pspace_relation_absD)
   apply clarsimp
   apply (erule (2) pspace_relation_reply_update_conc_only)
   apply (clarsimp simp: reply_relation_def)
  apply (rule conjI)
   apply (clarsimp simp: sc_replies_relation_def)
   apply (drule_tac x=p and y=replies in spec2)
   apply (clarsimp simp: vs_heap_simps projectKO_opt_reply projectKO_opt_sc)
   apply (rule conjI; clarsimp)
   apply (rename_tac sc n)
   apply (drule_tac sc=p in valid_replies_sc_with_reply_None, simp)
   apply (clarsimp simp: sc_replies_sc_at_def obj_at_def)
   apply (erule (1) heap_path_heap_upd_not_in[where r=rp])
  apply (clarsimp simp: caps_of_state_after_update cte_wp_at_after_update
                        swp_def fun_upd_def obj_at_def map_to_ctes_upd_other
              simp del: fun_upd_def)
  done

end

lemma cleanReply_sr_inv:
  "sr_inv (P and (\<lambda>s. sc_with_reply rp s = None) and valid_replies
           and (\<lambda>s. sym_refs (state_refs_of s)))
           P' (cleanReply rp)"
  unfolding cleanReply_def
  apply (rule sr_inv_bind[rotated])
    apply (rule updateReply_sr_inv)
     apply (clarsimp simp: reply_relation_def)
    apply clarsimp
    apply (erule (4) sc_replies_relation_sc_with_reply_None[where rp=rp and f="(replyPrev_update (\<lambda>_. Nothing))", simplified])
   apply wpsimp
  apply (clarsimp intro!: updateReply_sr_inv_next[simplified])
  done

(* reply_remove_tcb related corres rules *)

context begin interpretation Arch .

(* setting scheduling contexts with sc_replies update *)
lemma setSchedContext_sc_replies_relation_corres:
  assumes R': "sc_relation sc n sc' \<longrightarrow> sc_relation (f sc) n (f' sc')"
  and     h : "\<forall> hp. sc_replies_relation_obj (f sc) (f' sc') hp"
  and     s : "objBits sc' = objBits (f' sc')"
  shows
  "corres dc (\<lambda>s. kheap s ptr = Some (kernel_object.SchedContext sc n))
             (ko_at' sc' ptr)
         (set_object ptr  (kernel_object.SchedContext (f sc) n))
         (setSchedContext ptr (f' sc'))"
  proof -
  have x: "updateObject (f' sc') = updateObject_default (f' sc')" by clarsimp
  have z: "\<And>s. sc_at' ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO (f' sc'))) = map_to_ctes (ksPSpace s)"
    by (clarsimp simp: obj_at_simps)
  have P: "\<And>(v::'a::pspace_storable). (1 :: word32) < 2 ^ (objBits v)"
    by (clarsimp simp: obj_at_simps objBits_defs pteBits_def pdeBits_def scBits_pos_power2
                split: kernel_object.splits arch_kernel_object.splits)
  show ?thesis
    apply (insert P R' h s)
    apply (clarsimp simp: setSchedContext_def)
    apply (rule corres_no_failI)
     apply (rule no_fail_pre)
      apply wp
      apply (rule x)
     apply (clarsimp elim!: obj_at'_weakenE simp: sc_relation_def objBits_simps scBits_simps)
    apply (clarsimp simp: obj_at_def is_sc_obj_def obj_at'_def projectKO_eq projectKO_opts_defs)
    apply (unfold update_sched_context_def set_object_def setObject_def)
    apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                          put_def return_def modify_def get_object_def x
                          projectKOs obj_at_def a_type_def
                          updateObject_default_def in_magnitude_check[OF _ P]
                   split: Structures_A.kernel_object.splits)
    apply (rename_tac s s')
    apply (prop_tac "obj_at (same_caps (kernel_object.SchedContext sc n)) ptr s")
     apply (clarsimp simp: obj_at_def)
    apply (clarsimp simp: state_relation_def
                          z[simplified obj_at'_def is_sc_obj_def projectKO_eq projectKO_opts_defs, simplified])
    apply (clarsimp simp: caps_of_state_after_update cte_wp_at_after_update
                              swp_def fun_upd_def obj_at_def)
    apply (subst conj_assoc[symmetric])
    apply (rule conjI[rotated])
     apply (clarsimp simp: ghost_relation_def)
     apply (erule_tac x=ptr in allE)+
     apply (clarsimp simp: obj_at_def a_type_def
                     split: Structures_A.kernel_object.splits if_split_asm)
    apply (fold fun_upd_def)
    apply (simp only: pspace_relation_def simp_thms
                      pspace_dom_update[where x="kernel_object.SchedContext _ _"
                                          and v="kernel_object.SchedContext _ _",
                                        simplified a_type_def, simplified])
    apply (simp only: dom_fun_upd2 simp_thms)
    apply (elim conjE)
    apply (frule bspec, erule domI)
    apply (rule conjI)
     apply (rule ballI, drule(1) bspec)
     apply (drule domD)
     apply (clarsimp simp: project_inject split: if_split_asm kernel_object.split_asm)
     apply (rename_tac bb aa ba)
     apply (drule_tac x="(aa, ba)" in bspec, simp)
     apply clarsimp
     apply (frule_tac ko'="kernel_object.SchedContext sc n" and x'=ptr
              in obj_relation_cut_same_type)
        apply simp+
     apply (clarsimp simp: a_type_def split: Structures_A.kernel_object.split_asm if_split_asm)
      (* sc_replies_relation *)
    apply (drule_tac x="replyPrevs_of s'" in spec)
    apply (clarsimp simp: sc_replies_relation_def)
    apply (rule conjI; clarsimp)
     apply (clarsimp simp: sc_replies_relation_def vs_heap_simps projectKO_opt_reply
                    split: if_split_asm)
     apply (drule_tac x=ptr and y="sc_replies (f sc)" in spec2)
     apply (prop_tac "ptr \<notin> dom (replyPrevs_of s')")
      apply (clarsimp simp: vs_heap_simps projectKO_opt_reply)
     apply simp
    apply (clarsimp simp: sc_replies_relation_def vs_heap_simps projectKO_opt_reply
                   split: if_split_asm)
    apply (rename_tac sc0 n0)
    apply (drule_tac x=p and y="sc_replies sc0" in spec2, clarsimp)
    apply (prop_tac "ptr \<notin> dom (replyPrevs_of s')")
     apply (clarsimp simp: vs_heap_simps projectKO_opt_reply)
    by simp
qed

lemma update_sc_replies_update_Head_corres:
  "\<lbrakk> replyNext reply' = Some (Head scp)  \<rbrakk> \<Longrightarrow>
   corres dc ((\<lambda>s. (sc_replies_of s |> hd_opt) ptr = Some rp) and valid_objs and pspace_aligned and pspace_distinct)
             \<top>
          (update_sched_context ptr (sc_replies_update (takeWhile ((\<noteq>) rp))))
         (do sc' \<leftarrow> getSchedContext ptr;
            setSchedContext ptr (scReply_update Map.empty sc')
          od)"
  apply (rule_tac Q="sc_at' ptr" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD simp: obj_at_def is_sc_obj_def vs_heap_simps
                    elim!: sc_at_cross valid_objs_valid_sched_context_size)
  apply (rule corres_symb_exec_r)
     apply (rule_tac P'="ko_at' sc' ptr" in corres_inst)
     apply (rule_tac Q="sc_obj_at (objBits sc' - minSchedContextBits) ptr" in corres_cross_add_abs_guard)
      apply (fastforce dest!: state_relationD ko_at'_cross)
     apply (rule corres_guard_imp)
       apply (rule_tac P="(\<lambda>s. (sc_replies_of s |> hd_opt) ptr = Some rp)
                          and sc_obj_at (objBits sc' - minSchedContextBits) ptr"
                  and n1="objBits sc' - minSchedContextBits"
                            in monadic_rewrite_corres[OF _ update_sched_context_rewrite])
       apply (rule corres_symb_exec_l)
          apply (rule corres_guard_imp)
            apply (rule_tac P="(\<lambda>s. kheap s ptr = Some (kernel_object.SchedContext sc (objBits sc'
                                                                                       - minSchedContextBits)))
                               and K (rp = hd (sc_replies sc))"
                        and P'="ko_at' sc' ptr"  in corres_inst)
            apply (rule corres_gen_asm')
            apply (rule_tac n="objBits sc' - minSchedContextBits"
                   in setSchedContext_sc_replies_relation_corres)
              apply (clarsimp simp: sc_relation_def)
             apply clarsimp
            apply (clarsimp simp: objBits_simps)
           apply simp
          apply simp
         apply (wpsimp wp: get_sched_context_exs_valid simp: is_sc_obj_def obj_at_def)
          apply (rename_tac ko xs; case_tac ko; clarsimp)
         apply simp
        apply (wpsimp simp: obj_at_def is_sc_obj_def vs_heap_simps)
       apply (wpsimp wp: get_sched_context_no_fail)
      apply (clarsimp simp: obj_at_def is_sc_obj_def)
     apply simp
    apply wpsimp+
  done

lemma updateReply_reply_sc_update_None_corres:
  "corres dc (reply_at rp and pspace_aligned and pspace_distinct) \<top>
    (set_reply_obj_ref reply_sc_update rp None)
    (updateReply rp (replyNext_update Map.empty))"
  apply (rule_tac Q="reply_at' rp" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD reply_at_cross)
  apply (clarsimp simp: update_sk_obj_ref_def updateReply_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ get_reply_corres])
      apply (rule set_reply_corres)
      apply (clarsimp simp: reply_relation_def)
     apply wpsimp+
  by (clarsimp simp: obj_at'_def replyPrev_same_def)

lemma updateReply_reply_sc_update_Some_corres:
  "corres dc (reply_at rp and pspace_aligned and pspace_distinct) \<top>
    (set_reply_obj_ref reply_sc_update rp (Some nr))
    (updateReply rp (replyNext_update (\<lambda>_. Some (Head nr))))"
  apply (rule_tac Q="reply_at' rp" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD reply_at_cross)
  apply (clarsimp simp: update_sk_obj_ref_def updateReply_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ get_reply_corres])
      apply (rule set_reply_corres)
      apply (clarsimp simp: reply_relation_def)
     apply wpsimp+
  by (clarsimp simp: obj_at'_def replyPrev_same_def)

lemma replyPrevNext_update_commute:
  "replyPrev_update Map.empty (replyNext_update Map.empty reply)
   = replyNext_update Map.empty (replyPrev_update Map.empty reply)"
  by (cases reply; clarsimp)

lemma updateReply_Prev_Next_rewrite:
  "monadic_rewrite False True (reply_at' rp)
    (do y <- updateReply rp (replyPrev_update Map.empty);
         updateReply rp (replyNext_update Map.empty)
     od)
    (do y <- updateReply rp (replyNext_update Map.empty);
         updateReply rp (replyPrev_update Map.empty)
     od)"
  apply (clarsimp simp: monadic_rewrite_def)
  apply (rule monad_state_eqI)
    apply (find_goal \<open>match conclusion in "_ = _" \<Rightarrow> -\<close>)
    apply (insert no_fail_updateReply, drule_tac x=rp and y="replyPrev_update Map.empty" in meta_spec2)
    apply (insert no_fail_updateReply, drule_tac x=rp and y="replyNext_update Map.empty" in meta_spec2)
    apply (rule; clarsimp simp: in_monad no_fail_def snd_bind split_def)
     apply (drule (1) use_valid[OF _ updateReply_reply_at'], fastforce)+
   apply (all \<open>clarsimp simp: updateReply_def getReply_def setReply_def getObject_def setObject_def
                              obj_at'_def projectKOs updateObject_default_def loadObject_default_def
                              split_def in_monad in_magnitude_check' objBits_simps'\<close>)
   apply (fastforce simp add: fun_upd_def replyPrevNext_update_commute)+
  done

(* FIXME RT: Move *)
lemma neq_conv :"((\<noteq>) x) = (\<lambda>c. c \<noteq> x)"
  by (rule ext) auto

lemma reply_sc_update_no_change:
  "set_reply_obj_ref reply_sc_update rp None \<lbrace>\<lambda>s. sc_with_reply rp s = None\<rbrace>"
  apply (wpsimp wp: update_sk_obj_ref_wp)
  apply (drule sc_with_reply_NoneD)
  apply (simp add: sc_with_reply_def sc_replies_sc_at_def obj_at_def)
  apply (rule the_pred_option_None)
  by (metis Structures_A.kernel_object.simps(45) option.simps(1))

lemma cleanReply_reply_sc_update_corres: (* for detaching the head of sc_replies *)
  "corres dc (reply_at rp and pspace_aligned and pspace_distinct
    and valid_replies and (\<lambda>s. sc_with_reply rp s = None))
    \<top>
     (set_reply_obj_ref reply_sc_update rp None)
     (cleanReply rp)"
  apply (rule_tac Q="reply_at' rp" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD reply_at_cross)
  apply (simp add: cleanReply_def bind_assoc)
  apply (rule corres_guard_imp)
    apply (rule monadic_rewrite_corres'[OF _ updateReply_Prev_Next_rewrite])
    apply (rule corres_bind_return)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF _ updateReply_reply_sc_update_None_corres])
        apply (rule_tac P="reply_at rp and valid_replies and (\<lambda>s. sc_with_reply rp s = None)"
                 and P'="reply_at' rp" in corres_noop_sr)
          apply (rule sr_inv_imp)
            apply (rule updateReply_sr_inv_prev[simplified])
           apply (clarsimp simp: reply_relation_def)
          apply simp
         apply (wpsimp wp: reply_sc_update_no_change)+
     apply simp+
  done

lemma update_sc_replies_update_middle_updateReply_prev_corres:
  assumes
    "rp \<in> set (sc_replies sc)"
    "st = Structures_A.thread_state.BlockedOnReply rp"
    "st' = Structures_H.thread_state.BlockedOnReply (Some rp)" "hd (sc_replies sc) \<noteq> rp"
  shows
  "corres dc
      (valid_objs and pspace_aligned and pspace_distinct and valid_replies
        and st_tcb_at ((=) st) t and (\<lambda>s. sym_refs (state_refs_of s))
        and (\<lambda>s. sc_with_reply rp s = Some scp)
        and obj_at (\<lambda>ko. \<exists>n. ko = kernel_object.SchedContext sc n) scp
        and reply_sc_reply_at ((=) None) rp)
      (valid_objs' and (\<lambda>s'. replyNexts_of s' rp = Some nrp)
        and (\<lambda>s. sym_refs (list_refs_of_replies' s)))
      (update_sched_context scp (sc_replies_update (takeWhile ((\<noteq>) rp))))
      (updateReply nrp (replyPrev_update Map.empty))"
proof -
  have z: "\<And>s x. reply_at' nrp s
                 \<Longrightarrow> map_to_ctes ((ksPSpace s) (nrp \<mapsto> KOReply (replyPrev_update Map.empty x)))
                     = map_to_ctes (ksPSpace s)"
    by (clarsimp simp: obj_at_simps)
  show ?thesis using assms
    supply opt_mapE[rule del]
    apply (rule_tac Q="reply_at' rp and reply_at' nrp and sc_at' scp
                      and st_tcb_at' ((=) st') t and (\<lambda>s. sym_refs (state_refs_of' s))
                      and (\<lambda>s'. sc_with_reply' rp s' = Some scp)" in corres_cross_add_guard)
     apply clarsimp
     apply (prop_tac "reply_at' rp s'")
      apply (fastforce dest!: state_relationD reply_sc_reply_at_cross simp: obj_at'_def)
     apply (rule conjI, simp)
     apply (rule conjI)
      apply (fastforce dest!: valid_objs'_replyNexts_of_reply_at')
     apply (rule conjI)
      apply (clarsimp dest!: state_relationD)
      apply (erule sc_at_cross; clarsimp simp add: obj_at_def is_sc_obj; simp?)
      apply (erule valid_objs_valid_sched_context_size, fastforce)
     apply (rule conjI)
      apply (fastforce dest!: st_tcb_at_coerce_concrete simp: thread_state_relation_def op_equal)
     apply (rule conjI)
      apply (fastforce dest!: state_refs_of_cross_eq)
     apply (fastforce dest: state_relationD simp: sc_replies_relation_sc_with_reply_cross_eq)
    apply (clarsimp simp: corres_underlying_def)
    apply (rename_tac s s')
    apply (rule conjI)
     defer
     apply (erule no_failD[OF no_fail_updateReply])
    apply (clarsimp simp: update_sched_context_def updateReply_def getReply_def
                          setReply_def getObject_def setObject_def in_monad split_def
                          get_object_def set_object_def bind_assoc loadObject_default_def
                          obj_at'_def projectKOs reply_sc_reply_at_def obj_at_def exec_gets
                          updateObject_default_def in_magnitude_check objBits_simps' a_type_def)
    apply (clarsimp simp: exec_get put_def)
    apply (rename_tac reply' sc' nextr)
    apply (prop_tac "reply_at' nrp s'")
     apply (clarsimp simp: obj_at'_def projectKOs objBits_simps')
    apply (prop_tac "reply_at nrp s")
     apply (drule (1) valid_sched_context_objsI)
     apply (clarsimp simp: valid_sched_context_def)
     apply (frule_tac nrp=nrp in next_reply_in_sc_replies[where rp=rp, OF state_relation_sc_replies_relation])
           apply (simp add: obj_at'_def projectKOs objBits_simps' opt_map_left_Some)+
     apply (clarsimp simp: vs_heap_simps)
    apply (drule_tac x=nextr in z)
    apply (clarsimp simp: state_relation_def obj_at_def is_reply obj_at'_def projectKOs)
    apply (rule conjI)
      (* pspace_relation *)
     apply (simp only: pspace_relation_def simp_thms
                       pspace_dom_update[where x="kernel_object.SchedContext _ _"
                                           and v="kernel_object.SchedContext _ _",
                                         simplified a_type_def, simplified])
     apply (simp only: dom_fun_upd2 simp_thms)
     apply (elim conjE)
     apply (frule bspec, erule domI)
     apply (frule_tac x=nrp in bspec, erule domI)
     apply (rule ballI, drule(1) bspec)
     apply (drule domD)
     apply (prop_tac "scp \<noteq> nrp", clarsimp)
     apply (clarsimp simp: project_inject split: if_split_asm kernel_object.split_asm)
     apply (rule conjI; clarsimp)
      apply (clarsimp simp: sc_relation_def)
     apply (rename_tac bb aa ba)
     apply (drule_tac x="(aa, ba)" in bspec, simp)
     apply (clarsimp simp: obj_at_def is_reply)
     apply (frule_tac ko'="kernel_object.Reply reply" and x'=nrp in obj_relation_cut_same_type)
        apply simp+
     apply (clarsimp simp: reply_relation_def)
    apply (rule conjI)
      (* sc_replies_relation *)
     apply (clarsimp simp: projectKO_opt_sc opt_map_left_Some)
     apply (frule (2) sc_replies_relation_scReply)
     apply (clarsimp simp: sc_replies_relation_def sc_replies_of_scs_def map_project_def scs_of_kh_def)
     apply (drule_tac x=p in spec)
     apply (intro conjI impI allI)
      (* p =  scp *)
      apply (clarsimp simp: opt_map_left_Some sc_of_def)
      apply (prop_tac "replyPrevs_of s' nrp = Some rp")
       apply (simp add: sym_refs_replyNext_replyPrev_sym[symmetric])
       apply (clarsimp simp: opt_map_left_Some)
      apply (prop_tac "scReply sc' \<noteq> Some rp")
       apply (drule heap_path_head; clarsimp)
      apply (frule (4) heap_ls_next_takeWhile_append_sym[OF _ _ _ _ reply_sym_heap_Prev_Next])
      apply simp
      apply (rule heap_path_heap_upd_not_in[rotated])
    using set_takeWhileD apply (metis (full_types))
      apply (erule heap_path_takeWhile_lookup_next)
      apply (prop_tac "nrp \<in> set (takeWhile ((\<noteq>) rp) (sc_replies sc))")
       apply clarsimp
    using set_takeWhileD apply metis
      (* p \<noteq> scp *)
     apply (rule heap_path_heap_upd_not_in)
      apply clarsimp
     apply (clarsimp simp: sc_of_def opt_map_Some)
     apply (rename_tac p sc2 ko)
     apply (case_tac ko; simp)
     apply (clarsimp simp: opt_map_left_Some sc_of_def)
     apply (prop_tac "replyPrevs_of s' nrp = Some rp")
      apply (simp add: sym_refs_replyNext_replyPrev_sym[symmetric])
      apply (clarsimp simp: opt_map_left_Some)
     apply (frule (2) heap_ls_next_in_list)
     apply (simp add: sc_with_reply_def the_pred_option_def
               split: if_split_asm)
     apply blast
    apply (rule conjI)
     apply (clarsimp simp add: ghost_relation_def)
     apply (erule_tac x=scp in allE)+
     apply (clarsimp simp: obj_at_def a_type_def
                    split: Structures_A.kernel_object.splits if_split_asm)
    apply (clarsimp simp: caps_of_state_after_update cte_wp_at_after_update
                          swp_def fun_upd_def obj_at_simps)
    done
qed

end

(* end : related corres rules *)

(* FIXME RT: the original in Invariants_AI; do we want valid_objs or valid_tcbs? *)
lemma st_tcb_at_valid_st2:
  "\<lbrakk> st_tcb_at ((=) st) t s; valid_tcbs s \<rbrakk> \<Longrightarrow> valid_tcb_state st s"
  by (clarsimp simp: valid_tcbs_def get_tcb_def pred_tcb_at_def obj_at_def valid_tcb_def)

(* FIXME RT: original in DetSchedInvs_AI; maybe combine and clean up *)
lemma BlockedOnReply_reply_tcb_reply_at:
  " st_tcb_at ((=) (Structures_A.BlockedOnReply rptr)) tptr s
   \<Longrightarrow> sym_refs (state_refs_of s)
   \<Longrightarrow> reply_tcb_reply_at ((=) (Some tptr)) rptr s"
  apply (clarsimp simp: pred_tcb_at_def)
  apply (drule (1) sym_refs_obj_atD[where p=tptr])
  apply (clarsimp simp: state_refs_of_def obj_at_def tcb_st_refs_of_def
                 split: Structures_A.thread_state.splits)
  apply (rename_tac ko; case_tac ko; clarsimp simp: get_refs_def2 reply_tcb_reply_at_def obj_at_def)
  done

(* FIXME RT: move to StateRelation.thy? Replace the non-projection one? *)
lemma sc_replies_relation_scReply_cross:
  "\<lbrakk> sc_replies_relation s s'; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned s; pspace_distinct s; valid_objs s;
   \<exists>n. kheap s ptr = Some (kernel_object.SchedContext sc n)\<rbrakk>
    \<Longrightarrow> scReplies_of s' ptr = hd_opt (sc_replies sc)"
  apply (prop_tac "sc_at' ptr s'")
   apply (fastforce intro!: sc_at_cross valid_sched_context_size_objsI simp: obj_at_def is_sc_obj_def)
  apply (clarsimp simp: sc_replies_relation_def obj_at'_def projectKOs)
  apply (drule_tac x=ptr and y="sc_replies sc" in spec2)
  apply (prop_tac "sc_replies_of s ptr = Some (sc_replies sc)")
   apply (clarsimp simp: vs_heap_simps)
  apply (clarsimp simp: sc_of_def opt_map_def)
  apply (case_tac "sc_replies sc"; clarsimp simp: projectKO_opt_sc)
  done

(* wp rules *)

lemma scReply_update_empty_sc_with_reply':
  "\<lbrace>(\<lambda>s. sc_with_reply' rp s = Some scp) and ko_at' sc' scp
    and (\<lambda>s. sym_refs (state_refs_of' s)) and reply_at' rp
    and (\<lambda>s. sym_refs (list_refs_of_replies' s))
    and K (scReply sc' = Some rp)
    and pspace_aligned' and pspace_distinct'\<rbrace>
   setSchedContext scp (scReply_update Map.empty sc')
   \<lbrace>\<lambda>rv s. sc_with_reply' rp s = None\<rbrace>"
  supply heap_path.simps[simp del]
  apply (wpsimp wp: set_sc'.setObject_wp simp: setSchedContext_def)
  apply (simp (no_asm) add: sc_with_reply'_def)
  apply (simp add: the_pred_option_def split: if_split_asm)
  apply (rule notI)
  apply (clarsimp simp add: Ex1_def)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (clarsimp simp: projectKO_opt_reply)
  apply (prop_tac "(replyPrevs_of s)(scp := None) = replyPrevs_of s")
   apply (rule ext)
   apply (clarsimp simp: opt_map_None opt_map_left_None set_reply'.not_sc)
  apply (clarsimp simp: sc_with_reply'_def the_pred_option_def)
  apply (split if_split_asm; simp)
  apply (drule the1_equality)
   apply blast
  by simp

(* another version of sc_replies_update_takeWhile_not_fst_replies_with_sc? *)
lemma sc_replies_update_takeWhile_sc_with_reply:
  "\<lbrace>(\<lambda>s. sc_with_reply rp s = Some scp) and valid_replies\<rbrace>
    update_sched_context scp
              (sc_replies_update (takeWhile ((\<noteq>) rp)))
             \<lbrace>\<lambda>rv s.
                 sc_with_reply rp s = None\<rbrace>"
   apply (wpsimp wp: set_object_wp hoare_vcg_all_lift get_object_wp
               simp: update_sched_context_def)
  apply (clarsimp dest!: sc_with_reply_SomeD1)
  apply (prop_tac "\<exists>replies. sc_replies_sc_at (\<lambda>rs. rs = replies) scp s \<and> rp \<in> set replies")
   apply (fastforce simp: sc_replies_sc_at_def obj_at_def)
  apply (thin_tac "sc_replies_sc_at _ _ _")
  apply (clarsimp simp: obj_at_def sc_replies_sc_at_def)
  apply (clarsimp simp: sc_with_reply_def)
  apply (prop_tac "\<not> rp \<in> set (takeWhile ((\<noteq>) rp) (sc_replies x))")
   apply (metis (mono_tags, lifting) takeWhile_taken_P)
  apply clarsimp
  apply (clarsimp simp add: the_pred_option_def Ex1_def)
  by (fastforce dest!: valid_replies_sc_replies_unique simp: obj_at_def sc_replies_sc_at_def)+

lemma sc_with_reply'_lift:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (replyPrevs_of s) (scReplies_of s)\<rbrace> f \<lbrace>\<lambda>rv s. P (replyPrevs_of s) (scReplies_of s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. sc_with_reply' rp s = scopt\<rbrace>"
  supply if_split[split del]
  unfolding valid_def sc_with_reply'_def
  apply (simp add: sc_with_reply'_def the_pred_option_def)
  apply (intro allI impI ballI)
  apply (rename_tac x; case_tac x; simp)
  apply (auto dest!: use_valid[OF _ x])
  done

(* maybe a more usable version of sc_replies_update_take_While_valid_replies *)
lemma sc_replies_update_takeWhile_valid_replies':
  "\<lbrace> valid_replies and (\<lambda>s. sc_with_reply rp s = Some scp)\<rbrace>
   update_sched_context scp (sc_replies_update (takeWhile ((\<noteq>) rp)))
   \<lbrace>\<lambda>rv. valid_replies\<rbrace>"
  apply (clarsimp simp: valid_def dest!: sc_with_reply_SomeD1)
  apply (prop_tac "\<exists>replies. sc_replies_sc_at (\<lambda>rs. rs = replies) scp s \<and> rp \<in> set replies")
   apply (fastforce simp: sc_replies_sc_at_def obj_at_def)
  apply (thin_tac "sc_replies_sc_at _ _ _")
  apply (elim exE conjE)
  apply (rule_tac s=s and replies1=replies and r'1=rp and sc_ptr1=scp
            in use_valid[OF _ sc_replies_update_take_While_valid_replies, simplified])
   apply (clarsimp simp: sc_replies_sc_at_def obj_at_def neq_conv[symmetric] return_def
                          update_sched_context_def in_bind get_object_def exec_gets)
   apply (metis (no_types, lifting) sched_context.fold_congs(10))
  apply (fastforce simp: sc_replies_sc_at_def obj_at_def)
  done

lemma update_sched_context_not_tcb_at[wp]:
  "update_sched_context ref f \<lbrace>\<lambda>s. \<not> ko_at (TCB tcb) t s\<rbrace>"
  apply (clarsimp simp: update_sched_context_def)
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (clarsimp simp: obj_at_def sk_obj_at_pred_def pred_neg_def split: if_splits)
  done

lemma update_sched_context_valid_tcb[wp]:
  "update_sched_context scp f \<lbrace>valid_tcb ptr tcb\<rbrace>"
  apply (clarsimp simp: update_sched_context_def)
  apply (wpsimp wp: set_object_typ_ats get_object_wp)
  done

lemma update_sched_context_valid_tcbs[wp]:
  "update_sched_context ref f \<lbrace>valid_tcbs\<rbrace>"
  unfolding valid_tcbs_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
  done

lemma sc_replies_update_takeWhile_middle_sym_refs:
  "\<lbrakk>hd (sc_replies sc) \<noteq> rp; rp \<in> set (sc_replies sc) \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. P (state_refs_of s) \<and> obj_at (\<lambda>ko. \<exists>n. ko = kernel_object.SchedContext sc n) scp s\<rbrace>
   update_sched_context scp (sc_replies_update (takeWhile ((\<noteq>) rp)))
   \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp wp: update_sched_context_state_refs_of)
  apply (clarsimp simp: sc_replies_sc_at_def obj_at_def)
  apply (prop_tac "takeWhile ((\<noteq>) rp) (sc_replies sc) \<noteq> []")
   apply (prop_tac "sc_replies sc \<noteq> []")
    apply (simp add: set_list_mem_nonempty)
   apply (case_tac "sc_replies sc"; simp)
  using hd_opt_append(1) takeWhile_dropWhile_id
  by (metis (mono_tags) append.right_neutral)

lemma updateReply_ko_at'_other:
  "\<lbrace>K (p \<noteq> rp) and ko_at' ko p\<rbrace> updateReply rp f \<lbrace>\<lambda>_. ko_at' ko p\<rbrace>"
  apply (wpsimp wp: updateReply_wp_all)
  by (clarsimp simp: obj_at'_def projectKOs ps_clear_upd')

crunches updateReply
for sc_at'[wp]: "\<lambda>s'. P (sc_at' scp s')"

lemma update_replyPrev_replyNexts_inv[wp]:
  "updateReply rp (replyPrev_update prev) \<lbrace>\<lambda>s. P (replyNexts_of s)\<rbrace>"
  unfolding updateReply_def supply fun_upd_apply[simp del]
  apply wpsimp
  by (metis ko_at'_replies_of' map_upd_triv opt_map_upd_Some)

lemma sr_inv_sc_with_reply_None_helper:
  "\<not> isHead (replyNext reply') \<Longrightarrow>
   sr_inv
     (valid_objs and pspace_aligned and pspace_distinct and valid_replies and
      st_tcb_at ((=) (Structures_A.thread_state.BlockedOnReply rp)) t and
      (\<lambda>s. sym_refs (state_refs_of s)) and (\<lambda>s. sc_with_reply rp s = None) and reply_at rp)
     (valid_objs' and valid_release_queue_iff and
      (\<lambda>s'. sym_refs (list_refs_of_replies' s')) and
      (\<lambda>s. sym_refs (state_refs_of' s)) and ko_at' reply' rp and
      ((\<lambda>s'. sc_with_reply' rp s' = None) and pspace_aligned' and pspace_distinct'))
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
  apply (case_tac "replyNext reply'"; simp add: getHeadScPtr_def isHead_def split: reply_next.splits )
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
     apply (fastforce simp: reply_relation_def opt_map_left_Some obj_at'_def projectKOs
                     dest!: sym_refs_replyNext_replyPrev_sym[where rp'=rp, THEN iffD2])
    apply clarsimp
    apply (frule_tac rp=prv_rp in sc_replies_relation_sc_with_reply_None)
        apply simp
       apply simp
      apply (erule (8) sc_with_reply_replyPrev_None)
       apply (clarsimp simp: obj_at'_def projectKOs opt_map_left_Some)+
    apply (fastforce simp: projectKO_opt_sc obj_at'_def opt_map_left_Some projectKOs)
   apply (wpsimp wp: updateReply_valid_objs'_preserved simp: valid_reply'_def obj_at'_def)
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
    apply (clarsimp simp: projectKO_opt_sc obj_at'_def opt_map_left_Some projectKOs sc_replies_relation_def)
    apply (rename_tac nreply')
    apply (rule heap_path_heap_upd_not_in, simp)
    apply (rename_tac scp replies)
    apply (drule_tac x=scp and y=replies in spec2, simp)
    apply (prop_tac "rp \<notin> set replies")
     apply (drule_tac sc=scp in valid_replies_sc_with_reply_None, simp)
     apply (clarsimp simp: sc_replies_sc_at_def obj_at_def is_reply sc_replies_of_scs_def
                           scs_of_kh_def map_project_def sc_of_def)
     apply (rename_tac ko; case_tac ko; simp)
    apply (erule (1) heap_ls_prev_not_in)
    apply (fastforce elim!: sym_refs_replyNext_replyPrev_sym[THEN iffD1] simp: opt_map_left_Some)
   apply (wpsimp wp: updateReply_valid_objs'_preserved simp: valid_reply'_def obj_at'_def)
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
    apply (wpsimp wp: updateReply_valid_objs'_preserved simp: valid_reply'_def obj_at'_def)
   apply clarsimp
   apply (rule conjI)
    apply (fastforce simp: obj_at'_def projectKOs opt_map_left_Some
                    elim!: state_relationE sc_with_reply_replyPrev_None sc_with_reply_replyNext_None)
   apply (fastforce simp: obj_at'_def projectKOs opt_map_left_Some
                   elim!: state_relationE sc_with_reply_replyNext_None)
  apply (prop_tac"sc_with_reply prv_rp s = None \<and> sc_with_reply nxt_rp s = None")
   apply (rule conjI)
    apply (fastforce simp: obj_at'_def projectKOs opt_map_left_Some
                    elim!: state_relationE sc_with_reply_replyPrev_None sc_with_reply_replyNext_None)
   apply (fastforce simp: obj_at'_def projectKOs opt_map_left_Some
                   elim!: state_relationE sc_with_reply_replyNext_None)
  apply (erule state_relationE)
  apply (clarsimp simp: sc_replies_relation_sc_with_reply_cross_eq)
  apply (rule conjI)
   apply (clarsimp simp: obj_at'_def projectKOs)
  apply (frule (1) reply_ko_at_valid_objs_valid_reply')
  apply (clarsimp simp: valid_reply'_def valid_bound_obj'_def)
  apply (fastforce simp: obj_at'_def projectKOs opt_map_left_Some
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
             pspace_aligned' and
             pspace_distinct'))
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
   apply (clarsimp simp: obj_at'_def projectKOs valid_reply'_def)
  apply (rename_tac nextr; case_tac nextr; simp add: isHead_def)
  apply (case_tac "replyPrev reply'"; simp)
   apply (wpsimp;
          frule (1) reply_ko_at_valid_objs_valid_reply';
          clarsimp simp: obj_at'_def projectKOs valid_reply'_def)+
  done

lemma reply_remove_tcb_corres:
  "\<lbrakk> st = Structures_A.thread_state.BlockedOnReply rp;
     thread_state_relation st st' \<rbrakk> \<Longrightarrow>
   corres dc (valid_objs and pspace_aligned and pspace_distinct and valid_replies
              and st_tcb_at ((=) st) t and (\<lambda>s. sym_refs (state_refs_of s)))
             (valid_objs' and valid_release_queue_iff and (\<lambda>s'. sym_refs (list_refs_of_replies' s')))
                (reply_remove_tcb t rp) (replyRemoveTCB t)"
  (is "\<lbrakk> _ ; _ \<rbrakk> \<Longrightarrow> corres _ ?abs_guard ?conc_guard _ _")
  apply add_sym_refs
  apply (rule_tac Q="st_tcb_at' ((=) st') t" in corres_cross_add_guard)
   apply (fastforce dest!: st_tcb_at_coerce_concrete elim!: pred_tcb'_weakenE)
  apply (clarsimp simp: reply_remove_tcb_def replyRemoveTCB_def isReply_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ gts_corres])
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
             apply (rule_tac Q="(\<lambda>s'. sc_with_reply' rp s' = sc_opt) and pspace_aligned' and pspace_distinct'"
                    in corres_cross_add_guard)
              apply (fastforce simp: sc_replies_relation_sc_with_reply_cross_eq
                              dest!: state_relationD pspace_distinct_cross dest: pspace_aligned_cross)
             apply (case_tac sc_opt; simp split del: if_split add: bind_assoc)

              (** sc_with_reply rp s = None **)
              apply (rule_tac F="replySc reply' = None" in corres_req)
               apply (fastforce dest!: state_relationD sc_with_reply_None_reply_sc_reply_at reply_sc_reply_at_cross
                                 simp: obj_at'_def)
              apply (clarsimp simp: replySc_None_not_head)
  subgoal for reply'
    apply (simp only: bind_assoc[symmetric])
    apply (rule corres_symb_exec_r_sr)
       apply (rule corres_guard_imp)
         apply (rule reply_unlink_tcb_corres[simplified dc_def])
         apply (rule disjI2, simp)
        apply (clarsimp dest!: valid_objs_valid_tcbs elim!: BlockedOnReply_reply_tcb_reply_at)
       apply simp
      apply (erule sr_inv_sc_with_reply_None_helper)
     apply (wpsimp wp: updateReply_valid_objs'_preserved simp: valid_reply'_def obj_at'_def)
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
              apply (case_tac "takeWhile ((\<noteq>)rp) xs", clarsimp del: opt_mapE)
               apply (drule (2) sym_refs_replySc_scReplies_of[THEN iffD2, rotated])
                apply (clarsimp simp: obj_at'_def)
               apply (clarsimp simp: obj_at'_def projectKOs)
              apply (simp only:)
              apply (drule sym_refs_reply_heap_path_doubly_linked_Nexts_rev[where p'=rp, THEN iffD1])
               apply fastforce
              apply (case_tac "rev list"; clarsimp simp: obj_at'_def projectKOs)
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
                  apply (fastforce dest!: state_relationD sc_replies_relation_scReply_cross)
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
                   apply (rule_tac F="replySc reply' = replysc" in corres_req)
                    apply (fastforce dest!: state_relationD reply_sc_reply_at_cross simp: obj_at'_def)
                   apply (case_tac "hd (sc_replies sc) = rp"; simp split del: if_split)

             (* hd (sc_replies sc) = rp & replysc = Some scp: rp is at the head of the queue *)
             (* i.e. replyNext reply'  *)
                    apply (rule corres_guard_imp)
                      apply (rule corres_assert_gen_asm_l2)
                      apply (simp add: getHeadScPtr_def isHead_def neq_conv[symmetric] split: reply_next.splits)
                      apply (rule corres_split[OF _ update_sc_replies_update_Head_corres[simplified dc_def]])
                         apply (rule_tac Q =\<top> and
                                         P'="valid_objs' and valid_release_queue_iff and ko_at' reply' rp" and
                                         Q'="(\<lambda>s'. \<forall>prp. replyPrev reply' = Some prp
                                                         \<longrightarrow> replyNexts_of s' prp = Some rp)"
                             in corres_inst_add)
                         apply (rule corres_symb_exec_r_sr)
                            apply (rule corres_guard_imp)
                              apply (rule corres_split[OF _ cleanReply_reply_sc_update_corres])
                                apply (rule reply_unlink_tcb_corres[simplified dc_def])
                                apply (rule disjI2, simp)
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
                              apply (clarsimp simp: reply_relation_def projectKOs obj_at'_def obj_at_def)
                             apply clarsimp
                             apply (drule_tac rp=prev_rp in sc_replies_relation_replyNext_update, simp)
                             apply simp
                            apply simp
                           apply clarsimp
                          apply wpsimp
                         apply wpsimp
                         apply (clarsimp dest!: reply_ko_at_valid_objs_valid_reply' simp: valid_reply'_def)
                        apply simp
                       apply (wpsimp wp: sc_replies_update_takeWhile_sc_with_reply
                                         sc_replies_update_takeWhile_valid_replies')
                      apply (wpsimp wp: scReply_update_empty_sc_with_reply')
                     apply clarsimp
                     apply (frule_tac reply_ptr=rp and sc_ptr= scp and list="tl (sc_replies sc)"
                            in sym_refs_reply_sc_reply_at)
                      apply (clarsimp simp: sc_replies_sc_at_def obj_at_def is_reply)
                      apply (metis list.sel(1) list.sel(3) list.set_cases)
                     apply (clarsimp simp: getHeadScPtr_def reply_sc_reply_at_def obj_at_def is_reply
                                    split: reply_next.splits)
                     apply (frule valid_objs_valid_tcbs, simp)
                     apply (frule (1) BlockedOnReply_reply_tcb_reply_at, simp)
                     apply (clarsimp simp: opt_map_left_Some opt_map_def split: option.splits)
                     apply (rule context_conjI; clarsimp simp: vs_heap_simps obj_at_def)
                     apply (metis list.sel(1) list.set_cases)
                    apply clarsimp
                    apply (rule conjI)
                     apply (clarsimp dest!: sc_ko_at_valid_objs_valid_sc'
                                      simp: valid_sched_context'_def valid_sched_context_size'_def
                                            objBits_simps)
                     apply (erule sym_refs_replyNext_replyPrev_sym[THEN iffD2])
                     apply (clarsimp simp: opt_map_left_Some obj_at'_def projectKOs)
                    apply (frule (1) sym_refs_replySc_scReplies_of[rotated, THEN iffD2])
                      apply (fastforce simp: obj_at'_def)
                     apply (metis hd_opt_simps(2) list.sel(1) list.set_cases)
                    apply (clarsimp simp: opt_map_left_Some obj_at'_def projectKOs split: reply_next.splits)

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
                                     [OF _ update_sc_replies_update_middle_updateReply_prev_corres[where t=t]])
                             apply (rule_tac P ="?abs_guard and reply_sc_reply_at ((=) None) rp" and
                                             Q ="\<lambda>s. sc_with_reply rp s = None" and
                                             P'="valid_objs' and valid_release_queue_iff
                                                 and ko_at' reply' rp and sc_at' scp" and
                                             Q'="(\<lambda>s'. \<forall>prp. replyPrev reply' = Some prp
                                                             \<longrightarrow> replyNexts_of s' prp = Some rp)"
                                   in corres_inst_add)
                             apply (rule corres_symb_exec_r_sr)
                                apply (rule corres_guard_imp)
                                  apply (rule corres_split[OF _ cleanReply_reply_sc_update_corres])
                                    apply (rule reply_unlink_tcb_corres[simplified dc_def])
                                    apply (rule disjI2, simp)
                                   apply wpsimp
                                  apply wpsimp
                                 apply (fastforce dest: valid_objs_valid_tcbs reply_tcb_reply_at
                                                        BlockedOnReply_reply_tcb_reply_at)
                                apply simp
                               apply (clarsimp cong: conj_cong)
                               apply (case_tac "replyPrev reply'"; simp)
                               apply (rename_tac prev_rp)
                               apply (rule sr_inv_imp)
                                 apply (rule_tac P =\<top> and
                                                 P'=" (\<lambda>s'. \<forall>prp. replyPrev reply' = Some prp
                                                                  \<longrightarrow> replyNexts_of s' prev_rp = Some rp)"
                                        in updateReply_sr_inv)
                                  apply (clarsimp simp: reply_relation_def projectKOs obj_at'_def obj_at_def)
                                 apply clarsimp
                                 apply (drule_tac rp=prev_rp in sc_replies_relation_replyNext_update, simp)
                                 apply simp
                                apply simp
                               apply clarsimp
                              apply wpsimp
                             apply wpsimp
                             apply (clarsimp dest!: reply_ko_at_valid_objs_valid_reply'
                                              simp: valid_reply'_def)
                            apply simp
                           apply simp
                          apply simp
                         apply simp
                        apply (wpsimp wp: sc_replies_update_takeWhile_sc_with_reply
                                          sc_replies_update_takeWhile_middle_sym_refs
                                          sc_replies_update_takeWhile_valid_replies')
                       apply (wpsimp wp: updateReply_valid_objs'_preserved updateReply_ko_at'_other)
                      apply (clarsimp cong: conj_cong)
                      apply simp
                     apply (clarsimp simp: valid_reply'_def)
                     apply (rule context_conjI)
                      apply (clarsimp simp: obj_at'_def projectKOs opt_map_left_Some)
                     apply (clarsimp simp: obj_at_def del: opt_mapE)
                     apply (frule (1) valid_sched_context_objsI)
                     apply (clarsimp simp: valid_sched_context_def del: opt_mapE)
                     apply (frule (4) next_reply_in_sc_replies[OF state_relation_sc_replies_relation])
                       apply (clarsimp simp: obj_at'_def)
                      apply simp
                     apply (clarsimp simp: vs_heap_simps)
                    apply clarsimp
                    apply (rule conjI)
                     apply (clarsimp simp: list_all_iff dest!: set_takeWhileD)
                    apply (drule (2) sc_replies_middle_reply_sc_None)
                       apply (clarsimp simp: vs_heap_simps obj_at_def)
                      apply (fastforce simp: obj_at_def is_sc_obj_def elim!: valid_sched_context_size_objsI)
                     apply (erule reply_sc_reply_at)
                    apply (clarsimp simp: reply_sc_reply_at_def obj_at_def)
                   apply (fastforce elim!: sym_refs_replyNext_replyPrev_sym[THEN iffD2]
                                     simp: opt_map_left_Some obj_at'_def projectKOs)
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
                apply clarsimp+
              apply wpsimp
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
  apply (clarsimp, rule conjI)
   using fold_list_refs_of_replies' apply metis
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def projectKOs)
  apply (rename_tac tcb reply)
  apply (case_tac "tcbState tcb"; simp)
  done

lemma cancel_ipc_corres:
  "corres dc (invs and valid_ready_qs and tcb_at t) invs'
      (cancel_ipc t) (cancelIPC t)"
  apply add_sym_refs
  apply add_ready_qs_runnable
  apply (rule_tac Q="tcb_at' t" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: tcb_at_cross)
  apply (simp add: cancel_ipc_def cancelIPC_def Let_def)
  apply (rule corres_stateAssert_add_assertion[where P'=\<top>, simplified, rotated])
   apply (clarsimp simp: sym_refs_asrt_def)
  apply (rule corres_stateAssert_add_assertion[where P'=\<top>, simplified, rotated])
   apply (clarsimp simp: ready_qs_runnable_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ gts_corres])
      apply (rule corres_split[OF _ threadset_corres])
                   apply (rule_tac P="invs and valid_ready_qs and st_tcb_at ((=) state) t" and
                                   P'="invs' and st_tcb_at' ((=) statea) t" in corres_inst)
                   apply (case_tac state, simp_all add: isTS_defs list_case_If gbep_ret')[1]
                      apply (rule corres_guard_imp)
                        apply (rename_tac epPtr reply pl)
                        apply (rule_tac st = "Structures_A.thread_state.BlockedOnReceive epPtr reply pl"
                               in blocked_cancel_ipc_corres[simplified])
                          apply simp
                         apply (clarsimp simp: thread_state_relation_def)
                         apply simp+
                       apply (clarsimp simp: invs_implies)
                      apply (clarsimp simp: invs'_implies)
                     apply (rule corres_guard_imp)
                       apply (rename_tac epPtr data)
                       apply (rule_tac st = "Structures_A.thread_state.BlockedOnSend epPtr data"
                              in blocked_cancel_ipc_corres[where reply_opt=None, simplified])
                        apply simp
                       apply (clarsimp simp: thread_state_relation_def)
                       apply simp
                      apply (clarsimp simp: invs_implies)
                     apply (clarsimp simp: invs'_implies)
                    apply (rule corres_guard_imp)
                      apply (rule reply_remove_tcb_corres)
                       apply simp
                      apply (clarsimp simp: thread_state_relation_def)
                      apply simp
                     apply (clarsimp simp: invs_implies)
                    apply (clarsimp simp: invs'_implies)
                   apply (rule corres_guard_imp)
                     apply (rule cancel_signal_corres)
                    apply simp+
                  apply (clarsimp simp: tcb_relation_def fault_rel_optionation_def)
                 apply simp+
       apply (wpsimp wp: thread_set_invs_fault_None thread_set_valid_ready_qs thread_set_no_change_tcb_state)
      apply (wpsimp wp: threadSet_pred_tcb_no_state threadSet_invs_trivial)
     apply (wp gts_sp[where P="\<top>", simplified])+
    apply (rule hoare_strengthen_post)
     apply (rule gts_sp'[where P="\<top>"])
    apply (clarsimp elim!: pred_tcb'_weakenE)
   apply simp
  apply (clarsimp simp: inQ_def obj_at'_def projectKOs valid_release_queue'_def
                 dest!: invs_valid_release_queue')
  done

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
       apply (wps)
       apply (wp, simp)
      done
    show ?thesis
      apply (simp add: cancelSignal_def invs'_def valid_state'_def Let_def)
      apply (rule hoare_seq_ext[OF _ stateAssert_sp])
      apply (wp valid_irq_node_lift sts_sch_act' irqs_masked_lift
                hoare_vcg_all_lift [OF set_ntfn'.ksReadyQueues]
                setThreadState_ct_not_inQ NTFNSN
                hoare_vcg_all_lift set_ntfn'.ksReadyQueues
              | simp add: valid_tcb_state'_def list_case_If split del: if_split)+
       prefer 2
       apply assumption
      apply (rule hoare_strengthen_post)
       apply (rule get_ntfn_sp')
      apply (clarsimp simp: pred_tcb_at' ready_qs_runnable_def)
      apply (frule (1) NIQ)
       apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
      apply (rule conjI)
       apply (clarsimp simp: valid_ntfn'_def)
       apply (case_tac "ntfnObj r", simp_all add: isWaitingNtfn_def)
       apply (frule ko_at_valid_objs')
         apply (simp add: valid_pspace_valid_objs')
        apply (clarsimp simp: projectKO_opt_ntfn split: kernel_object.splits)
       apply (simp add: valid_obj'_def valid_ntfn'_def)
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
        apply (case_tac "ntfnObj r", simp_all)
        apply (frule obj_at_valid_objs', clarsimp)
        apply (clarsimp simp: projectKOs valid_obj'_def valid_ntfn'_def)
        apply (frule st_tcb_at_state_refs_ofD')
        apply (frule ko_at_state_refs_ofD')
        apply (fastforce simp: get_refs_def elim!: if_live_state_refsE split: option.splits)
       apply (clarsimp simp: valid_idle'_def)
       apply (clarsimp simp: idle_tcb'_def obj_at'_def projectKOs st_tcb_at'_def)
      apply (case_tac "ntfnObj r", simp_all)
      apply (frule obj_at_valid_objs', clarsimp)
      apply (clarsimp simp: projectKOs valid_obj'_def valid_ntfn'_def)
      apply (rule conjI, clarsimp split: option.splits)
      apply (frule st_tcb_at_state_refs_ofD')
      apply (frule ko_at_state_refs_ofD')
      apply (rule conjI)
       apply (clarsimp split: if_split_asm)
       apply (fastforce simp: list_refs_of_replies'_def opt_map_def o_def split: option.splits)
      apply (rule conjI)
       apply (fastforce simp: get_refs_def elim!: if_live_state_refsE split: option.splits)
      apply (rule conjI)
       apply (fastforce simp: get_refs_def elim!: if_live_state_refsE split: option.splits)
      apply (case_tac "ntfnBoundTCB r")
       apply (clarsimp elim!: if_live_state_refsE)+
       apply (clarsimp dest!: idle'_only_sc_refs)
      apply (clarsimp simp: valid_idle'_def)
      apply (clarsimp simp: idle_tcb'_def obj_at'_def projectKOs st_tcb_at'_def)
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

crunches cancelIPC
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and ksMachineState[wp]: "\<lambda>s. P (ksMachineState s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and sch_act_simple[wp]: "sch_act_simple"
  and valid_pde_mappings'[wp]: "valid_pde_mappings'"
  and ifunsafe'[wp]: "if_unsafe_then_cap'"
  and global_refs'[wp]: "valid_global_refs'"
  and valid_arch'[wp]: "valid_arch_state'"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and vms'[wp]: "valid_machine_state'"
  and ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
  and pspace_domain_valid[wp]: pspace_domain_valid
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
  "\<lbrakk>ep \<noteq> IdleEP; remove1 tptr (epQueue ep) = x # xs; valid_ep' ep s\<rbrakk>
   \<Longrightarrow> valid_ep' (epQueue_update (\<lambda>_. x # xs) ep) s"
  apply (case_tac ep
         ; clarsimp simp: valid_ep'_def
         ; metis (full_types) distinct.simps(2) distinct_remove1 list.set_intros(1)
                              list.set_intros(2) notin_set_remove1)
  done

lemma blockedCancelIPC_valid_pspace'[wp]:
  "blockedCancelIPC st tptr rptrOpt \<lbrace>valid_pspace'\<rbrace>"
  unfolding valid_pspace'_def blockedCancelIPC_def getBlockingObject_def
  apply (wpsimp wp: valid_mdb'_lift hoare_vcg_imp_lift haskell_assert_wp getEndpoint_wp
              simp: valid_tcb_state'_def epBlocked_def)
  apply (case_tac "remove1 tptr (epQueue ko)"; clarsimp; normalise_obj_at')
   apply (clarsimp simp: valid_ep'_def)
  apply (drule(1) ep_ko_at_valid_objs_valid_ep')
  apply (rename_tac ko a list)
  apply (prop_tac "ko \<noteq> IdleEP \<longrightarrow> valid_ep' (epQueue_update (\<lambda>_. a # list) ko) s")
   apply (clarsimp simp: nonempty_epQueue_remove1_valid_ep')
  apply fastforce
  done

lemma cancelIPC_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> sch_act_not tptr s\<rbrace>
   cancelIPC tptr
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding cancelIPC_def
  apply (wpsimp wp: gts_wp' hoare_vcg_imp_lift' threadSet_sch_act hoare_vcg_all_lift
                    replyRemoveTCB_sch_act_wf)
  done

(* FIXME RT: move to ...? *)
crunches getBlockingObject
  for inv: P

(* FIXME RT: move to...? *)
lemma endpoint_live:
  "\<lbrakk>ko_at' ep ptr s; ep \<noteq> IdleEP\<rbrakk> \<Longrightarrow> ko_wp_at' live' ptr s"
  apply (clarsimp simp: ko_wp_at'_def obj_at'_def projectKOs)
  done

lemma blockedCancelIPC_if_live'[wp]:
  "blockedCancelIPC st tptr epptr \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  unfolding blockedCancelIPC_def getBlockingObject_def
  apply (wpsimp wp: getEndpoint_wp haskell_assert_wp)
  apply (clarsimp simp: if_live_then_nonz_cap'_def endpoint.disc_eq_case endpoint_live)
  done

lemma blockedCancelIPC_valid_idle':
  "\<lbrace>valid_idle' and valid_pspace' and (\<lambda>s. tptr \<noteq> ksIdleThread s)\<rbrace>
   blockedCancelIPC st tptr epptr
   \<lbrace>\<lambda>_. valid_idle'\<rbrace>"
  unfolding blockedCancelIPC_def getBlockingObject_def
  apply (wpsimp wp: getEndpoint_wp)
  apply (case_tac "remove1 tptr (epQueue ko)"; clarsimp; normalise_obj_at')
   apply (clarsimp simp: valid_ep'_def)
  apply (drule(1) ep_ko_at_valid_objs_valid_ep'[OF _ valid_pspace_valid_objs'])
  apply (rename_tac ko a list)
  apply (prop_tac "ko \<noteq> IdleEP \<longrightarrow> valid_ep' (epQueue_update (\<lambda>_. a # list) ko) s")
   apply (clarsimp simp: nonempty_epQueue_remove1_valid_ep')
  apply fastforce
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
  unfolding invs'_def valid_state'_def decompose_list_refs_of_replies'
  apply (wpsimp wp: valid_irq_node_lift typ_at_lifts blockedCancelIPC_valid_idle'
                    valid_irq_handlers_lift' valid_irq_states_lift' irqs_masked_lift
              simp: cteCaps_of_def pred_tcb_at'_def)
  apply (rule conjI)
   apply normalise_obj_at'
   apply (rename_tac tcb ep)
   apply (case_tac "tcbState tcb"; clarsimp simp: epBlocked_def obj_at'_def projectKOs)
  apply (rule ccontr)
  apply (clarsimp simp: valid_idle'_def idle_tcb'_def)
  apply normalise_obj_at'
  apply (rename_tac tcb ep sc)
  apply (case_tac "tcbState tcb"; clarsimp simp: epBlocked_def obj_at'_def projectKOs)
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
  apply (rule conjI)
   apply normalise_obj_at'
   apply (rename_tac tcb)
   apply (case_tac "tcbState tcb"; clarsimp)
  apply (frule invs_sch_act_wf')
  apply (case_tac "ksSchedulerAction s"; clarsimp simp: pred_tcb_at'_def)
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

lemma blockedCancelIPC_st_tcb_at:
  "\<lbrace>\<lambda>s. (t = t' \<longrightarrow> P Inactive) \<and> (t \<noteq> t' \<longrightarrow> st_tcb_at' P t s)\<rbrace>
   blockedCancelIPC st t' rptr
   \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  unfolding blockedCancelIPC_def Let_def getBlockingObject_def
  apply (wpsimp wp: setThreadState_st_tcb_at'_cases replyUnlink_st_tcb_at' hoare_vcg_imp_lift'
                    getEndpoint_wp)
  apply fastforce
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
  oops
(*by (wpsimp wp: mapM_x_wp' sts_st_tcb' hoare_drop_imp) *)

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

crunches cancelIPC
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  (wp: crunch_wps simp: crunch_simps pred_tcb_at'_def)

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

lemma sbn_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  by (simp add: setBoundNotification_def, wp threadSet.ksSchedulerAction)


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
  apply (fastforce simp: obj_at'_def projectKOs inQ_def objBitsKO_def )
  done

lemma replyUnlink_valid_inQ_queues[wp]:
  "replyUnlink replyPtr tcbPtr \<lbrace>valid_inQ_queues\<rbrace>"
  apply (clarsimp simp: replyUnlink_def updateReply_def)
  apply (wpsimp wp: set_reply'.set_wp gts_wp')
  apply (fastforce simp: valid_inQ_queues_def obj_at'_def projectKOs)
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

lemma get_tcb_yield_to_corres:
  "corres (=) (pspace_aligned and pspace_distinct and tcb_at t) \<top>
          (get_tcb_obj_ref tcb_yield_to t) (threadGet tcbYieldTo t)"
  apply (rule_tac Q="tcb_at' t" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: tcb_at_cross)
  apply (simp add: get_tcb_obj_ref_def getBoundNotification_def)
  apply (rule corres_guard_imp)
    apply (rule threadget_corres)
    apply (simp add: tcb_relation_def)+
  done

lemma tcb_yield_to_update_corres:
  "corres dc (pspace_aligned and pspace_distinct and tcb_at t) \<top>
          (set_tcb_obj_ref tcb_yield_to_update t yt) (threadSet (tcbYieldTo_update (\<lambda>_. yt)) t)"
  apply (rule_tac Q="tcb_at' t" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: tcb_at_cross)
  apply (simp add: set_tcb_obj_ref_def)
  apply (subst thread_set_def[simplified, symmetric])
  apply (rule corres_guard_imp)
    apply (rule threadset_corres, simp_all add: tcb_relation_def)
  done

lemma sc_relation_tcb_yield_to_update:
  "sc_relation sc n sc'
   \<Longrightarrow> sc_relation (sc_yield_from_update Map.empty (sc)) n (scYieldFrom_update Map.empty sc')"
  by (clarsimp simp: sc_relation_def)

lemma sched_context_cancel_yield_to_corres:
  "corres dc
          (pspace_aligned and pspace_distinct and valid_objs and tcb_at t)
          \<top>
          (sched_context_cancel_yield_to t)
          (schedContextCancelYieldTo t)" (is "corres _ ?abs_guard _ _ _")
  apply (rule_tac Q="tcb_at' t" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: tcb_at_cross)
  apply (clarsimp simp: sched_context_cancel_yield_to_def schedContextCancelYieldTo_def maybeM_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ get_tcb_yield_to_corres gyt_sp threadGet_sp
                             , where Q="?abs_guard"])
    defer
    apply (simp add: obj_at_def is_tcb_def)
   apply simp
  apply (case_tac scPtrOpt; clarsimp?)
  apply (rule corres_guard_imp)
    apply (subst bind_assoc[symmetric])
    apply (rule corres_split[OF _ update_sc_no_reply_stack_update_corres])
         apply (rule tcb_yield_to_update_corres)
         apply (simp add: sc_relation_tcb_yield_to_update)
        apply simp
       apply (clarsimp simp: objBits_simps')
      apply simp
     apply wpsimp
    apply wpsimp
   apply (clarsimp simp: valid_objs_def obj_at_def is_tcb_def)
   apply (fastforce simp: valid_obj_def valid_tcb_def valid_bound_obj_def pred_tcb_at_def obj_at_def
                   dest!: bspec
                   split: option.splits)
  apply clarsimp
  done

lemma reprogram_timer_corres:
   "corres dc \<top> \<top>
      (modify (reprogram_timer_update (\<lambda>_. True)))
      (setReprogramTimer True)"
  unfolding setReprogramTimer_def
  by (rule corres_modify) (simp add: state_relation_def swp_def)

lemma release_queue_corres:
  "corres (=) \<top> \<top> (gets release_queue) getReleaseQueue"
  by (simp add: getReleaseQueue_def state_relation_def release_queue_relation_def)

crunches ThreadDecls_H.suspend
  (* FIXME RT: VER-1016 *)
  for tcb_at'_better[wp]: "\<lambda>s. P (tcb_at' t s)"
  (rule: sch_act_simple_lift
     wp: crunch_wps
   simp: crunch_simps if_fun_split st_tcb_at'_def)

lemma tcb_release_remove_corres:
  "corres dc (pspace_aligned and pspace_distinct and tcb_at t) \<top>
             (tcb_release_remove t) (tcbReleaseRemove t)"
  unfolding tcb_release_remove_def tcbReleaseRemove_def tcb_sched_dequeue_def setReleaseQueue_def
  apply clarsimp
  apply (rule stronger_corres_guard_imp)
    apply (rule_tac r'="(=)" in corres_split)
       apply (rule corres_split)
          apply (rule corres_add_noop_lhs2)
          apply (rule corres_split)
             apply (rule threadSet_corres_noop; clarsimp simp: tcb_relation_def)
            apply (rule corres_modify)
            apply (auto simp: release_queue_relation_def state_relation_def swp_def)[1]
           apply wp
          apply wp
         apply (rule corres_rel_imp)
          apply (rule corres_when)
           apply clarsimp
          apply (rule reprogram_timer_corres)
         apply metis
        apply clarsimp
        apply wp
       apply (rule hoare_when_wp)
       apply clarsimp
       apply wp
      apply (rule release_queue_corres)
     apply wp
    apply clarsimp
    apply wpsimp
   apply simp
  apply (fastforce simp: state_relation_def tcb_at_cross)
  done

lemma (in delete_one) suspend_corres:
  "corres dc (einvs and tcb_at t) (invs' and tcb_at' t)
             (SchedContext_A.suspend t) (ThreadDecls_H.suspend t)"
  apply (simp add: SchedContext_A.suspend_def Thread_H.suspend_def)
  apply add_sym_refs
  apply (rule corres_stateAssert_add_assertion[where P'=\<top>, simplified])
   prefer 2
   apply (clarsimp simp: sym_refs_asrt_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor[OF _ cancel_ipc_corres])
      apply (rule corres_split[OF _ gts_corres], rename_tac state state')
        apply (simp only: when_def)
        apply (rule corres_split[OF _ corres_if])
             apply (rule corres_split[OF _ sts_corres])
                apply (rule corres_split[OF _ tcbSchedDequeue_corres'])
                  apply (rule corres_split[OF _ tcb_release_remove_corres])
                    apply (rule sched_context_cancel_yield_to_corres)
                   apply wpsimp+
            apply (case_tac state; clarsimp?)
           apply (clarsimp simp: update_restart_pc_def updateRestartPC_def)
           apply (rule corres_as_user')
           apply (simp add: ARM.nextInstructionRegister_def ARM.faultRegister_def
                            ARM_H.nextInstructionRegister_def ARM_H.faultRegister_def
                            ARM_H.Register_def)
           apply (rule corres_underlying_trivial)
           apply (wpsimp simp: ARM.setRegister_def ARM.getRegister_def)
          apply (rule corres_rel_imp)
           apply (rule corres_return_trivial)
          apply simp
         apply (wpsimp simp: update_restart_pc_def updateRestartPC_def)
          apply (rule hoare_post_imp[where Q = "\<lambda>rv s. invs s \<and> tcb_at t s"], fastforce)
          apply wp
         apply wpsimp
        apply (rule hoare_post_imp[where Q = "\<lambda>rv s. invs' s \<and> tcb_at' t s"])
         apply (fastforce simp: invs'_def valid_state'_def dest!: valid_queues_inQ_queues)
        apply wp
         apply (clarsimp simp: updateRestartPC_def)
         apply wpsimp
        apply wpsimp
       apply (wpsimp wp: gts_wp)
      apply (wpsimp wp: gts_wp')
     apply (rule hoare_post_imp[where Q = "\<lambda>rv s. invs s \<and> tcb_at t s"], fastforce)
     apply wpsimp
    apply (rule hoare_post_imp[where Q = "\<lambda>rv s. invs' s \<and> tcb_at' t s"], fastforce)
    apply wpsimp
   apply clarsimp+
  done

lemma (in delete_one) prepareThreadDelete_corres:
  "corres dc (tcb_at t) (tcb_at' t)
        (prepare_thread_delete t) (ArchRetypeDecls_H.ARM_H.prepareThreadDelete t)"
  by (simp add: ArchVSpace_A.ARM_A.prepare_thread_delete_def ArchRetype_H.ARM_H.prepareThreadDelete_def)

lemma no_refs_simple_strg':
  "st_tcb_at' simple' t s' \<and> P {} \<longrightarrow> st_tcb_at' (\<lambda>st. P (tcb_st_refs_of' st)) t s'"
  oops (* FIXME RT: not true any more; adjust simple'?
  by (fastforce elim!: pred_tcb'_weakenE)+ *)

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

crunch ct_idle_or_in_cur_domain'[wp]: tcbSchedDequeue ct_idle_or_in_cur_domain'

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

lemma schedContextCancelYieldTo_sch_act_wf[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def)
  apply (wpsimp wp: threadSet_sch_act threadGet_wp)
  apply (fastforce simp: obj_at'_def projectKOs)
  done

lemma schedContextCancelYieldTo_if_live_then_nonz_cap'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s\<rbrace>
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
  and list_refs_of_replies[wp]: "\<lambda>s. sym_refs (list_refs_of_replies' s)"
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
  "\<lbrace>invs' and sch_act_simple and tcb_at' t\<rbrace>
   schedContextCancelYieldTo t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def setSchedContext_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift cur_tcb_lift
                    untyped_ranges_zero_lift
              simp: cteCaps_of_def o_def)
  apply (fastforce simp: inQ_def valid_queues_def valid_queues_no_bitmap_def)
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

lemma tcbReleaseRemove_ct_idle_or_in_cur_domain'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>ct_idle_or_in_cur_domain'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def)
  apply (wpsimp wp: threadSet_ct_idle_or_in_cur_domain' hoare_vcg_imp_lift' hoare_vcg_disj_lift)
  done

crunches setReprogramTimer
  for valid_queues[wp]: valid_queues

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

crunches tcbReleaseRemove
  for valid_bitmapQ[wp]: valid_bitmapQ
  and bitmapQ_no_L2_orphans[wp]: bitmapQ_no_L2_orphans
  and bitmapQ_no_L1_orphans[wp]: bitmapQ_no_L1_orphans

lemma tcbReleaseRemove_valid_queues:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_queues\<rbrace>"
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
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s\<rbrace>
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

lemma tcbReleaseRemove_invs':
  "tcbReleaseRemove tcbPtr \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift cur_tcb_lift
                    untyped_ranges_zero_lift tcbReleaseRemove_valid_queues
              simp: cteCaps_of_def o_def)
  done

crunches tcbReleaseRemove, tcbSchedDequeue
  for sch_act_simple[wp]: sch_act_simple
  and ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps simp: crunch_simps sch_act_simple_def)

lemma (in delete_one_conc) suspend_invs'[wp]:
  "\<lbrace>invs' and sch_act_simple and tcb_at' t and (\<lambda>s. t \<noteq> ksIdleThread s)\<rbrace>
   ThreadDecls_H.suspend t
   \<lbrace>\<lambda>rv. invs'\<rbrace>" (is "valid ?pre _ _")
  apply (simp add: suspend_def updateRestartPC_def getThreadState_def)
  apply (rule hoare_seq_ext[OF _ stateAssert_sp])
  apply (rule_tac B="\<lambda>_. ?pre and st_tcb_at' simple' t"
               in hoare_seq_ext[rotated])
   apply (wpsimp wp: cancelIPC_simple')
   apply (clarsimp simp: sym_refs_asrt_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip)
   apply clarsimp
   apply (wpsimp simp: updateRestartPC_def)
  apply (rule_tac B="\<lambda>_. ?pre and st_tcb_at' ((=) Inactive) t"
               in hoare_seq_ext[rotated])
   apply (wpsimp wp: sts_invs_minor' sts_st_tcb_at'_cases)
   apply (fastforce simp: valid_tcb_state'_def)
  apply (wpsimp wp: tcbReleaseRemove_invs' schedContextCancelYieldTo_invs')
  done

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

crunches cancelSignal, replyUnlink, cleanReply
  for valid_queues[wp]: valid_queues
  (simp: crunch_simps wp: crunch_wps)

lemma tcbFault_update_valid_queues:
  "\<lbrakk>ko_at' tcb t s; valid_queues s\<rbrakk>
   \<Longrightarrow> valid_queues (s\<lparr>ksPSpace := ksPSpace s(t \<mapsto> KOTCB (tcbFault_update Map.empty tcb))\<rparr>)"
   by (fastforce simp: valid_queues_def valid_queues_no_bitmap_def valid_bitmapQ_def bitmapQ_def
                       bitmapQ_no_L2_orphans_def bitmapQ_no_L1_orphans_def obj_at'_def
                       projectKOs inQ_def objBitsKO_def)

lemma cancelIPC_queues[wp]:
  "cancelIPC t \<lbrace>valid_queues\<rbrace>"
  apply (simp add: cancelIPC_def Let_def)
  apply (wpsimp wp: threadSet_wp tcbFault_update_valid_queues hoare_drop_imps gts_wp')
  apply (fastforce intro: tcbFault_update_valid_queues)
  done

(* FIXME: move to Schedule_R *)
lemma tcbSchedDequeue_nonq[wp]:
  "\<lbrace>Invariants_H.valid_queues and tcb_at' t and K (t = t')\<rbrace>
   tcbSchedDequeue t
   \<lbrace>\<lambda>_ s. t' \<notin> set (ksReadyQueues s (d, p))\<rbrace>"
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
  "\<lbrace>Invariants_H.valid_queues and (\<lambda>s. t \<noteq> ksIdleThread s) and K (t = t')\<rbrace>
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

(* FIXME RT: use in Haskell in cancelAllIPC and cancelBadgedSends? *)
definition
  "restartThreadIfNoFault t
    \<equiv> do fault \<leftarrow> threadGet tcbFault t;
          if isNothing fault
          then do setThreadState Restart t;
                  possibleSwitchTo t
               od
          else setThreadState Inactive t
       od"

lemma restart_thread_if_no_fault_corres:
  "corres dc (valid_sched_action and tcb_at t and pspace_aligned and pspace_distinct and valid_tcbs)
             (valid_queues and valid_queues' and valid_release_queue_iff and valid_tcbs')
             (restart_thread_if_no_fault t)
             (restartThreadIfNoFault t)"
    (is "corres _ _ ?conc_guard _ _")
  apply (rule corres_cross_over_guard[where Q="?conc_guard and tcb_at' t"])
   apply (fastforce intro: tcb_at_cross)
  apply (clarsimp simp: restart_thread_if_no_fault_def restartThreadIfNoFault_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split
                  [OF _ threadget_corres[where r=fault_rel_optionation] thread_get_wp threadGet_wp])
     apply (rule corres_if)
       apply (clarsimp simp: fault_rel_optionation_def)
      apply (rule corres_split[OF _ sts_corres])
         apply clarsimp
         apply (rule possible_switch_to_corres)
        apply clarsimp
       apply (wpsimp wp: set_thread_state_valid_sched_action)
      apply (wpsimp wp: sts_st_tcb_at'_cases)
     apply (rule sts_corres)
     apply clarsimp
    apply (clarsimp simp: tcb_relation_def)
   apply (clarsimp simp: obj_at_def is_tcb_def invs_def valid_state_def)
   apply (fastforce split: Structures_A.kernel_object.splits)
  apply (fastforce simp: obj_at'_def projectKOs valid_tcb_state'_def)
  done

(* FIXME RT: move to AInvs *)
lemma restart_thread_if_no_fault_tcb_sts_of_other:
  "\<lbrace>\<lambda>s. Q (pred_map P (tcb_sts_of s) t') \<and> t \<noteq> t'\<rbrace>
   restart_thread_if_no_fault t
   \<lbrace>\<lambda>_ s. Q (pred_map P (tcb_sts_of s) t')\<rbrace>"
  apply (clarsimp simp: restart_thread_if_no_fault_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: possible_switch_to_pred_tcb_at[unfolded obj_at_kh_kheap_simps]
                    set_thread_state_pred_map_tcb_sts_of thread_get_inv)
  done

(* FIXME RT: move to AInvs *)
lemma reply_unlink_tcb_tcb_sts_of_other:
  "\<lbrace>\<lambda>s. Q (pred_map P (tcb_sts_of s) t') \<and> t \<noteq> t'\<rbrace>
   reply_unlink_tcb t r
   \<lbrace>\<lambda>_ s. Q (pred_map P (tcb_sts_of s) t')\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (rule hoare_seq_ext_skip, wpsimp)+
  apply (wpsimp wp: set_thread_state_pred_map_tcb_sts_of)
  done

crunches inReleaseQueue
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (sa s) s"
  and tcb_in_cur_domain'[wp]: "tcb_in_cur_domain' t"
  and cur_tcb'[wp]: cur_tcb'
  and if_live_then_nonz_cap'[wp]: if_live_then_nonz_cap'

crunches possibleSwitchTo
  for valid_pspace'[wp]: valid_pspace'
  and valid_queues[wp]: valid_queues
  and valid_tcbs'[wp]: valid_tcbs'
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
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and irq_states' [wp]: valid_irq_states'
  and pde_mappings' [wp]: valid_pde_mappings'
  and pspace_domain_valid[wp]: "pspace_domain_valid"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and valid_objs'[wp]: valid_objs'
  and ksArchState[wp]: "\<lambda>s. P (ksArchState s)"
  and ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and valid_irq_handlers'[wp]: valid_irq_handlers'
  (wp: crunch_wps cur_tcb_lift valid_irq_handlers_lift'' simp: crunch_simps)

global_interpretation possibleSwitchTo: typ_at_all_props' "possibleSwitchTo target"
  by typ_at_props'

lemma possibleSwitchTo_sch_act[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> st_tcb_at' runnable' t s\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (wpsimp simp: possibleSwitchTo_def wp: inReleaseQueue_wp threadGet_wp)
  by (fastforce simp: obj_at'_def tcb_in_cur_domain'_def)

lemma possibleSwitchTo_weak_sch_act[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<and> st_tcb_at' runnable' t s\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding possibleSwitchTo_def
  apply (wpsimp wp: inReleaseQueue_wp threadGet_wp rescheduleRequired_weak_sch_act_wf)
  by (auto simp: obj_at'_def weak_sch_act_wf_def tcb_in_cur_domain'_def
                 projectKO_eq ps_clear_domE)

lemma possibleSwitchTo_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' t
      and (\<lambda>s. \<forall>t. ksSchedulerAction s = SwitchToThread t
                   \<longrightarrow> st_tcb_at' runnable' t s)\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  by (wpsimp simp: possibleSwitchTo_def inReleaseQueue_def
               wp: hoare_vcg_if_lift2 hoare_drop_imps)

lemma possibleSwitchTo_ct_idle_or_in_cur_domain'[wp]:
  "possibleSwitchTo t \<lbrace>ct_idle_or_in_cur_domain'\<rbrace>"
  apply (wpsimp simp: possibleSwitchTo_def
                  wp: threadGet_wp inReleaseQueue_wp)
  apply (fastforce simp: obj_at'_def ct_idle_or_in_cur_domain'_def)
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
  apply (intro conjI; fastforce?)
  by (metis fold_list_refs_of_replies')

lemma possibleSwitchTo_sch_act_not_other:
  "\<lbrace>\<lambda>s. sch_act_not t' s \<and> t' \<noteq> t\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>_. sch_act_not t'\<rbrace>"
  apply (clarsimp simp: possibleSwitchTo_def)
  apply (wpsimp wp: threadGet_wp inReleaseQueue_wp)
  apply (clarsimp simp: obj_at'_def)
  done

(* FIXME RT: move to AInvs *)
lemma restart_thread_if_no_fault_reply_tcb_reply_at[wp]:
  "restart_thread_if_no_fault t \<lbrace>reply_tcb_reply_at ((=) (Some t')) r_opt\<rbrace>"
  apply (clarsimp simp: sk_obj_at_pred_def)
  apply (wpsimp wp: restart_thread_if_no_fault_obj_at_impossible')
  done

(* FIXME RT: move to AInvs *)
lemma reply_unlink_tcb_reply_tcb_reply_at_other:
  "\<lbrace>\<lambda>s. reply_tcb_reply_at ((=) (Some t')) r' s \<and> t' \<noteq> t\<rbrace>
   reply_unlink_tcb t r
   \<lbrace>\<lambda>_ s. reply_tcb_reply_at ((=) (Some t')) r' s\<rbrace>"
  apply (wpsimp wp: update_sk_obj_ref_wps get_simple_ko_wp gts_wp
              simp: reply_unlink_tcb_def)
  apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def pred_tcb_at_def)
  done

definition
  "reply_unlink_ts_pred t s
    \<equiv> \<forall>ep r_opt pl.
       pred_map ((=) (Structures_A.thread_state.BlockedOnReceive ep (Some r_opt) pl)) (tcb_sts_of s) t
       \<longrightarrow> reply_tcb_reply_at ((=) (Some t)) r_opt s"

(* FIXME RT: move to AInvs or even use in abstract spec? *)
definition
  "cancel_all_ipc_loop_body t
    \<equiv> do st \<leftarrow> get_thread_state t;
          reply_opt \<leftarrow> case st of Structures_A.thread_state.BlockedOnReceive x r_opt xa
                                   \<Rightarrow> return r_opt
                               | _ \<Rightarrow> return None;
          when (reply_opt \<noteq> None) $ reply_unlink_tcb t (the reply_opt);
          restart_thread_if_no_fault t
       od"

(* FIXME RT: move to AInvs *)
lemma cancel_all_ipc_loop_body_reply_unlink_ts_pred_other:
  "\<lbrace>\<lambda>s. reply_unlink_ts_pred t s \<and> t' \<noteq> t\<rbrace>
   cancel_all_ipc_loop_body t'
   \<lbrace>\<lambda>_. reply_unlink_ts_pred t\<rbrace>"
  unfolding reply_unlink_ts_pred_def cancel_all_ipc_loop_body_def
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: restart_thread_if_no_fault_tcb_sts_of_other reply_unlink_tcb_tcb_sts_of_other
                    reply_unlink_tcb_reply_tcb_reply_at_other hoare_vcg_all_lift
                    hoare_vcg_imp_lift')
  done

(* FIXME RT: use in Haskell? *)
definition
  "cancelAllIPC_loop_body t
    \<equiv> do st \<leftarrow> getThreadState t;
          replyOpt \<leftarrow> return (if isReceive st then replyObject st else Nothing);
          case replyOpt of None \<Rightarrow> return () | Some reply \<Rightarrow> replyUnlink reply t;
          restartThreadIfNoFault t
       od"

lemma cancelAllIPC_loop_body_st_tcb_at'_other:
  "\<lbrace>\<lambda>s. st_tcb_at' P t' s \<and> tcb_at' t' s \<and> t' \<noteq> t\<rbrace>
   cancelAllIPC_loop_body t
   \<lbrace>\<lambda>_. st_tcb_at' P t'\<rbrace>"
  apply (clarsimp simp: cancelAllIPC_loop_body_def restartThreadIfNoFault_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip, wpsimp wp: replyUnlink_st_tcb_at')
  apply (wpsimp wp: sts_st_tcb_at'_cases threadGet_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma cancelAllIPC_loop_body_weak_sch_act_wf:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<and> tcb_at' t s \<and> st_tcb_at' (not runnable') t s\<rbrace>
   cancelAllIPC_loop_body t
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: cancelAllIPC_loop_body_def restartThreadIfNoFault_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip, wpsimp wp: replyUnlink_st_tcb_at')
   apply (clarsimp simp: weak_sch_act_wf_def pred_neg_def st_tcb_at'_def obj_at'_def)
  apply (wpsimp wp: sts_st_tcb_at'_cases hoare_drop_imps)
  apply (clarsimp simp: weak_sch_act_wf_def pred_neg_def st_tcb_at'_def obj_at'_def)
  done

crunches cancelAllIPC_loop_body
  for valid_queues'[wp]: valid_queues'
  and valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'
  and valid_tcbs'[wp]: valid_tcbs'
  and tcb_at'[wp]: "\<lambda>s. tcb_at' threadPtr s"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (simp: valid_tcb_state'_def)

global_interpretation cancelAllIPC_loop_body: typ_at_all_props' "cancelAllIPC_loop_body t"
  by typ_at_props'

lemma cancelAllIPC_loop_body_valid_queues:
  "\<lbrace>\<lambda>s. valid_queues s \<and> valid_tcbs' s\<rbrace>
   cancelAllIPC_loop_body t
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (clarsimp simp: cancelAllIPC_loop_body_def restartThreadIfNoFault_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip, wpsimp)
   apply (clarsimp simp: weak_sch_act_wf_def pred_neg_def st_tcb_at'_def obj_at'_def)
  apply (wpsimp wp: sts_valid_queues sts_st_tcb_at'_cases hoare_drop_imps)
  apply (clarsimp simp: obj_at'_def projectKOs valid_tcb_state'_def pred_neg_def st_tcb_at'_def)
  done

lemma cancel_all_ipc_corres_helper:
  "distinct list \<Longrightarrow>
   corres dc
          ((\<lambda>s. \<forall>t \<in> set list. blocked_on_send_recv_tcb_at t s \<and> t \<noteq> idle_thread s
                               \<and> reply_unlink_ts_pred t s)
            and (valid_sched and valid_tcbs and pspace_aligned and pspace_distinct))
          ((\<lambda>s. \<forall>t \<in> set list. tcb_at' t s)
            and (valid_queues and valid_queues' and valid_tcbs' and valid_release_queue_iff))
     (mapM_x cancel_all_ipc_loop_body list)
     (mapM_x cancelAllIPC_loop_body list)"
  unfolding cancel_all_ipc_loop_body_def cancelAllIPC_loop_body_def
  apply (rule_tac S="{t. (fst t = snd t) \<and> fst t \<in> set list}" in corres_mapM_x_scheme)
          apply clarsimp
          apply (rule corres_guard_imp)
            apply (rule corres_split[OF _ gts_corres], rename_tac st st')
              apply (rule_tac P="\<lambda>s. blocked_on_send_recv_tcb_at y s \<and> y \<noteq> idle_thread s
                                     \<and> reply_unlink_ts_pred y s \<and> valid_sched s \<and> valid_tcbs s
                                     \<and> pspace_aligned s \<and> pspace_distinct s
                                     \<and> st_tcb_at ((=) st) y s"
                          and P'="\<lambda>s. valid_queues s \<and> valid_queues' s \<and> valid_tcbs' s
                                      \<and> valid_release_queue_iff s"
                           in corres_inst)
              apply (case_tac "\<exists>ep r_opt pl.
                                st = Structures_A.thread_state.BlockedOnReceive ep r_opt pl")
               apply (clarsimp simp: when_def split: option.splits)
               apply (intro conjI impI allI; clarsimp simp: isReceive_def)
                apply (corressimp corres: restart_thread_if_no_fault_corres)
                apply (fastforce simp: obj_at_def)
               apply (rule corres_guard_imp)
                 apply (rule corres_split[OF _ reply_unlink_tcb_corres])
                    apply (rule corres_guard_imp)
                      apply (rule restart_thread_if_no_fault_corres)
                     apply simp
                    apply simp
                   apply fastforce
                  apply (wpsimp wp: reply_unlink_tcb_valid_sched_action)
                 apply wpsimp
                apply (fastforce simp: vs_all_heap_simps pred_tcb_at_def obj_at_def
                                       reply_unlink_ts_pred_def)
               apply clarsimp
              apply (prop_tac "\<not> isReceive st'")
               apply (case_tac st; clarsimp simp: isReceive_def)
              apply (case_tac st
                     ; clarsimp simp: isReceive_def
                     ; (corressimp corres: restart_thread_if_no_fault_corres
                        , fastforce simp: obj_at_def))
             apply (wpsimp wp: gts_wp)
            apply (wpsimp wp: gts_wp')
           apply (clarsimp simp: vs_all_heap_simps obj_at_def is_tcb_def)
          apply clarsimp
         apply (fold cancel_all_ipc_loop_body_def)
         apply (intro hoare_vcg_conj_lift_left_fix
                ; (solves \<open>wpsimp wp: gts_wp simp: cancel_all_ipc_loop_body_def\<close>)?)
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

lemma in_recv_ep_queue_TCBBlockedRecv:
  "\<lbrakk>kheap s epptr = Some (Endpoint (Structures_A.RecvEP queue)); t \<in> set queue; invs s\<rbrakk>
   \<Longrightarrow> (epptr, TCBBlockedRecv) \<in> state_refs_of s t"
  apply (prop_tac "valid_ep (Structures_A.RecvEP queue) s")
   apply (fastforce simp: valid_objs_def valid_obj_def dest!: invs_valid_objs)
  apply (clarsimp simp: state_refs_of_def valid_ep_def split: option.splits)
  apply (intro conjI impI allI; (fastforce simp: obj_at_def)?)
  apply (prop_tac "(t, EPRecv) \<in> state_refs_of s epptr", clarsimp simp: state_refs_of_def)
  apply (clarsimp simp: sym_refs_def dest!: invs_sym_refs)
  apply (fastforce simp: state_refs_of_def)
  done

lemma in_send_ep_queue_thread_state:
  "\<lbrakk>ko_at' (Structures_H.SendEP queue) epPtr s; t \<in> set queue;
    sym_refs (state_refs_of' s); valid_objs' s\<rbrakk>
   \<Longrightarrow> st_tcb_at' isBlockedOnSend t s"
  apply (prop_tac "valid_ep' (SendEP queue) s")
   apply (fastforce simp: valid_objs'_def valid_obj'_def obj_at'_def projectKOs)
  apply (clarsimp simp: valid_ep'_def)
  apply (prop_tac "(t, EPSend) \<in> state_refs_of' s epPtr")
   apply (clarsimp simp: state_refs_of'_def obj_at'_def projectKOs)
  apply (clarsimp simp: sym_refs_def obj_at'_def)
  apply (fastforce simp: state_refs_of'_def tcb_bound_refs'_def st_tcb_at'_def get_refs_def2
                         isBlockedOnSend_def obj_at'_def projectKOs
                  split: if_splits thread_state.splits)
  done

lemma in_recv_ep_queue_thread_state:
  "\<lbrakk>ko_at' (Structures_H.RecvEP queue) epPtr s; t \<in> set queue;
    sym_refs (state_refs_of' s); valid_objs' s\<rbrakk>
   \<Longrightarrow> st_tcb_at' isBlockedOnReceive t s"
  apply (prop_tac "valid_ep' (RecvEP queue) s")
   apply (fastforce simp: valid_objs'_def valid_obj'_def obj_at'_def projectKOs)
  apply (clarsimp simp: valid_ep'_def)
  apply (prop_tac "(t, EPRecv) \<in> state_refs_of' s epPtr")
   apply (clarsimp simp: state_refs_of'_def obj_at'_def projectKOs)
  apply (clarsimp simp: sym_refs_def obj_at'_def)
  apply (fastforce simp: state_refs_of'_def tcb_bound_refs'_def st_tcb_at'_def get_refs_def2
                         isBlockedOnReceive_def obj_at'_def projectKOs
                  split: if_splits thread_state.splits)
  done

lemma IdleEP_versus_SendEP_and_RecvEP:
  "\<lbrakk>ep = Structures_A.IdleEP \<Longrightarrow> P;
    \<And>q. ep = Structures_A.SendEP q \<or> ep = Structures_A.RecvEP q \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  using Structures_A.endpoint.exhaust by auto

lemma not_IdleEP_case_split:
  "ep \<noteq> Structures_A.IdleEP
   \<Longrightarrow> (case ep of Structures_A.IdleEP \<Rightarrow> f
                 | _ \<Rightarrow> g)
       = g"
  by (cases ep; clarsimp?)

lemma not_IdleEP_case_split':
  "ep \<noteq> Structures_H.IdleEP
   \<Longrightarrow> (case ep of Structures_H.IdleEP \<Rightarrow> f
                 | _ \<Rightarrow> g)
       = g"
  by (cases ep; clarsimp?)

lemma get_ep_queue_Send_or_Recv:
  "ep = Structures_A.SendEP q \<or> ep = Structures_A.RecvEP q
   \<Longrightarrow> get_ep_queue ep = return q"
  by (fastforce simp: get_ep_queue_def split: Structures_A.endpoint.splits)

lemma cancel_all_ipc_corres:
  "corres dc (invs and valid_sched and ep_at ep_ptr) (invs' and ep_at' ep_ptr)
             (cancel_all_ipc ep_ptr) (cancelAllIPC ep_ptr)"
proof -
  have P:
    "\<And>list. distinct list \<Longrightarrow>
         corres dc
          ((\<lambda>s. \<forall>t \<in> set list. blocked_on_send_recv_tcb_at t s \<and> t \<noteq> idle_thread s
                               \<and> reply_unlink_ts_pred t s)
            and (valid_sched and valid_tcbs and pspace_aligned and pspace_distinct and ep_at ep_ptr))
          ((\<lambda>s. \<forall>t \<in> set list. tcb_at' t s)
            and (valid_queues and valid_queues' and valid_tcbs' and valid_release_queue_iff
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
      apply (rule corres_split[OF _ set_ep_corres])
         apply clarsimp
         apply (rule corres_split[OF rescheduleRequired_corres])
           apply (erule cancel_all_ipc_corres_helper)
          apply (rule_tac Q="?abs_guard list" in hoare_weaken_pre)
           apply (rule hoare_strengthen_post)
            apply (rule ball_mapM_x_scheme)
              apply (intro hoare_vcg_conj_lift_left_fix
                     ; (solves \<open>wpsimp wp: gts_wp simp: cancel_all_ipc_loop_body_def\<close>)?)
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
           apply simp+
        apply (simp add: ep_relation_def)
       apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_const_Ball_lift hoare_vcg_imp_lift'
                   simp: reply_unlink_ts_pred_def)+
    done

  show ?thesis
    apply (clarsimp simp: cancel_all_ipc_def[folded cancel_all_ipc_loop_body_def]
                          cancelAllIPC_def[folded restartThreadIfNoFault_def
                                           , folded cancelAllIPC_loop_body_def])
    apply (subst forM_x_def fun_app_def)+
    apply add_sym_refs
    apply (rule corres_stateAssert_add_assertion[where P'=\<top>, simplified, rotated])
     apply (clarsimp simp: pred_conj_def sym_refs_asrt_def)
    apply (rule corres_split'[OF _ _ get_simple_ko_sp get_ep_sp'])
     apply (rule corres_guard_imp [OF get_ep_corres]
            ; simp add: ep_relation_def get_ep_queue_def)
    apply (rename_tac ep ep')
    apply (case_tac "ep = Structures_A.IdleEP \<or> ep' = Structures_H.IdleEP")
     apply (case_tac ep; case_tac ep'; simp add: ep_relation_def get_ep_queue_def)
    apply (simp add: not_IdleEP_case_split not_IdleEP_case_split' del: K_bind_def)
    apply (rule_tac ep=ep in IdleEP_versus_SendEP_and_RecvEP; fastforce?)
    apply (rule corres_symb_exec_l)
       apply (rule_tac F="q = queue \<and> distinct queue \<and> epQueue ep' = queue"
                    in corres_gen_asm)
       apply (simp only: )
       apply (rule corres_guard_imp)
         apply (rule P)
         apply simp
        apply simp
       apply simp
       apply (intro conjI impI allI; fastforce?)
       apply (elim disjE)
        apply (clarsimp simp: ep_relation_def)
        apply (prop_tac "valid_ep' (Structures_H.SendEP queue) s")
         apply (fastforce intro: ep_ko_at_valid_objs_valid_ep')
        apply (clarsimp simp: valid_ep'_def)+
       apply (clarsimp simp: ep_relation_def)
       apply (prop_tac "valid_ep' (Structures_H.RecvEP (epQueue ep')) s")
        apply (fastforce intro: ep_ko_at_valid_objs_valid_ep')
       apply (clarsimp simp: valid_ep'_def
                      split: endpoint.splits)
       apply (simp add: get_ep_queue_def)
       apply (case_tac ep; wpsimp?)
      apply (clarsimp simp: get_ep_queue_Send_or_Recv)
      apply wpsimp
      apply (elim disjE)
       apply (prop_tac "valid_ep (Structures_A.SendEP q) s")
        apply (fastforce intro: valid_objs_ko_at
                          dest: invs_valid_objs
                          simp: obj_at_def valid_obj_def)
       apply (intro conjI impI allI ballI; fastforce?)
          apply (fastforce dest!: in_send_ep_queue_TCBBlockedSend
                            simp: is_blocked_on_send_recv_def vs_all_heap_simps obj_at_def
                                  state_refs_of_def tcb_st_refs_of_def refs_of_def get_refs_def2
                           split: option.splits Structures_A.thread_state.splits
                                  Structures_A.kernel_object.splits)
         apply (rule not_idle_tcb_in_SendEp; (fastforce simp: obj_at_def)?)
        apply (fastforce dest!: in_send_ep_queue_TCBBlockedSend
                          simp: vs_all_heap_simps state_refs_of_def tcb_st_refs_of_def
                                get_refs_def2 obj_at_def reply_unlink_ts_pred_def
                         split: Structures_A.thread_state.splits)
       apply (simp add: valid_ep_def)
      apply (clarsimp simp: ep_relation_def)
     apply (prop_tac "valid_ep (Structures_A.RecvEP q) s")
      apply (fastforce intro: valid_objs_ko_at
                        dest: invs_valid_objs
                        simp: obj_at_def valid_obj_def)
     apply (intro conjI impI allI ballI; fastforce?)
         apply (fastforce dest!: in_recv_ep_queue_TCBBlockedRecv
                           simp: is_blocked_on_send_recv_def vs_all_heap_simps obj_at_def
                                 state_refs_of_def tcb_st_refs_of_def refs_of_def get_refs_def2
                          split: option.splits Structures_A.thread_state.splits
                                 Structures_A.kernel_object.splits)
        apply (rule not_idle_tcb_in_RecvEp; (fastforce simp: obj_at_def)?)
       apply (clarsimp simp: vs_all_heap_simps reply_unlink_ts_pred_def)
       apply (subst identity_eq)
       apply (fastforce intro!: BlockedOnReceive_reply_tcb_reply_at
                          simp: pred_tcb_at_def obj_at_def)
      apply (clarsimp simp: valid_ep_def)
     apply (clarsimp simp: ep_relation_def)
    apply (wpsimp simp: get_ep_queue_def)
    done
qed

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
          apply (rule corres_split[OF possible_switch_to_corres])
            apply (rule sts_corres)
            apply simp
           apply (wp set_thread_state_valid_sched_action
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
    apply (wpsimp wp: hoare_vcg_const_Ball_lift typ_at_lifts sts_st_tcb')
    apply (auto simp: valid_tcb_state'_def)
  done

lemma ntfn_cancel_corres:
  "corres dc (invs and valid_sched and ntfn_at ntfn) (invs' and ntfn_at' ntfn)
             (cancel_all_signals ntfn) (cancelAllSignals ntfn)"
  apply (simp add: cancel_all_signals_def cancelAllSignals_def)
  apply add_sym_refs
  apply (rule corres_stateAssert_add_assertion[where P'=\<top>, simplified])
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
                         sts_st_tcb' setThreadState_not_st
                   simp: valid_tcb_state'_def)
      apply (simp add: ntfn_relation_def)
     apply (wpsimp wp: hoare_vcg_const_Ball_lift)+
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (erule (1) obj_at_valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def not_idle_tcb_in_waitingntfn
                         valid_sched_weak_valid_sched_action
                  dest!: valid_objs_valid_tcbs)
   apply (clarsimp simp: ball_conj_distrib[symmetric])
   apply (rename_tac q s t)
   apply (rule context_conjI)
    apply (drule_tac x=ntfn and y=t and tp=TCBSignal in sym_refsE
           ; clarsimp simp: in_state_refs_of_iff refs_of_rev vs_all_heap_simps)
   apply (clarsimp simp: valid_sched_released_ipc_queues released_ipc_queues_blocked_on_recv_ntfn_E1)
  apply clarsimp
  apply (frule invs'_valid_tcbs')
  apply (clarsimp simp: invs'_def valid_state'_def invs_weak_sch_act_wf valid_ntfn'_def
                        valid_obj'_def projectKOs sym_refs_asrt_def
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

lemma replyUnlink_sch_act[wp]:
  "replyUnlink r t \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp only: replyUnlink_def liftM_def)
  apply (wpsimp wp: sts_sch_act' gts_wp')
  apply (fastforce simp: replyUnlink_assertion_def st_tcb_at'_def obj_at'_def)
  done

lemma replyUnlink_list_refs_of_replies'[wp]:
  "replyUnlink r t \<lbrace>\<lambda>s. P (list_refs_of_replies' s)\<rbrace>"
  unfolding replyUnlink_def updateReply_def
  apply (wpsimp simp: updateObject_default_def setObject_def split_def wp: gts_wp')
  apply (erule arg_cong[where f=P, THEN iffD1, rotated])
  apply (rule ext)
  apply (clarsimp simp: opt_map_def sym_refs_def fun_upd_def list_refs_of_reply'_def
                        map_set_def projectKO_opt_reply obj_at'_real_def ko_wp_at'_def
                 split: option.split)
  done

lemma replyUnlink_valid_pspace'[wp]:
  "\<lbrace>\<lambda>s. valid_pspace' s\<rbrace>
   replyUnlink r t
   \<lbrace>\<lambda>_ s. valid_pspace' s\<rbrace>"
  unfolding replyUnlink_def updateReply_def
  apply (wpsimp wp: gts_wp' simp: valid_tcb_state'_def)
  apply (frule valid_pspace_valid_objs')
  apply (frule(1) reply_ko_at_valid_objs_valid_reply')
  apply (drule(1) ko_at'_inj)
  apply (clarsimp simp: valid_reply'_def)
  done

lemma replyUnlink_if_live_then_nonz_cap'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s\<rbrace>
   replyUnlink r t
   \<lbrace>\<lambda>_ s. if_live_then_nonz_cap' s\<rbrace>"
  unfolding replyUnlink_def updateReply_def
  apply (wpsimp wp: gts_wp')
  apply (erule if_live_then_nonz_capE')
  apply normalise_obj_at'
  apply (clarsimp simp: live_reply'_def)
  done

lemma replyUnlink_valid_idle'[wp]:
  "\<lbrace>\<lambda>s. valid_idle' s \<and> valid_pspace' s \<and> t \<noteq> ksIdleThread s\<rbrace>
   replyUnlink r t
   \<lbrace>\<lambda>_ s. valid_idle' s\<rbrace>"
  unfolding replyUnlink_def updateReply_def
  apply (wpsimp wp: gts_wp' simp: valid_reply'_def)
  apply (frule valid_pspace_valid_objs')
  apply (frule(1) reply_ko_at_valid_objs_valid_reply')
  apply (drule(1) ko_at'_inj)
  apply (clarsimp simp: valid_reply'_def)
  done

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

lemma cancel_all_invs'_helper:
  "\<lbrace>all_invs_but_ct_not_inQ'
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
                                          possibleSwitchTo t
                                       od
                  else setThreadState Structures_H.thread_state.Inactive t
               od) q
   \<lbrace>\<lambda>rv. all_invs_but_ct_not_inQ'\<rbrace>"
  supply if_split[split del] comp_apply[simp del]
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
  apply (fastforce simp: sch_act_wf_weak_sch_act_wf valid_pspace_valid_objs' valid_objs'_valid_tcbs'
                         global'_no_ex_cap)
  done

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
      apply (metis (full_types, hide_lams) sym_refs_simp symreftype.simps(3))
      done

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

lemma rescheduleRequired_all_invs_but_ct_not_inQ:
  "\<lbrace>all_invs_but_ct_not_inQ'\<rbrace> rescheduleRequired \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: invs'_def valid_state'_def)
  apply (wpsimp wp: rescheduleRequired_ct_not_inQ valid_irq_node_lift valid_irq_handlers_lift''
                    irqs_masked_lift cur_tcb_lift untyped_ranges_zero_lift
              simp: cteCaps_of_def o_def)
  apply fastforce
  done

lemma cancelAllIPC_invs'[wp]:
  "\<lbrace>invs'\<rbrace> cancelAllIPC ep_ptr \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: cancelAllIPC_def ep'_Idle_case_helper cong del: if_cong)
  apply (rule hoare_seq_ext[OF _ stateAssert_sp])
  apply (wpsimp wp: rescheduleRequired_all_invs_but_ct_not_inQ
                    cancel_all_invs'_helper hoare_vcg_const_Ball_lift
                    valid_global_refs_lift' valid_arch_state_lift'
                    valid_irq_node_lift ssa_invs' sts_sch_act' getEndpoint_wp
                    irqs_masked_lift)
  apply (clarsimp simp: invs'_def valid_state'_def valid_ep'_def)
  apply (frule obj_at_valid_objs', fastforce)
  apply (clarsimp simp: projectKOs valid_obj'_def)
  apply (rule conjI)
   apply (metis fold_list_refs_of_replies')
  apply (clarsimp simp: sym_refs_asrt_def)
  apply (rule conjI)
   apply (drule(1) sym_refs_ko_atD')
   apply (clarsimp simp: valid_ep'_def st_tcb_at_refs_of_rev' split: endpoint.splits)
    apply (intro conjI)
      apply ((drule(1) bspec | drule st_tcb_at_state_refs_ofD'
              | clarsimp elim!: if_live_state_refsE split: if_splits)+)[1]
     apply (fastforce simp: runnable'_def st_tcb_at'_def obj_at'_def)
    apply (fastforce elim!: pred_tcb'_weakenE)
   apply (intro conjI)
     apply ((drule(1) bspec | drule st_tcb_at_state_refs_ofD'
             | clarsimp elim!: if_live_state_refsE split: if_splits)+)[1]
    apply (fastforce simp: runnable'_def st_tcb_at'_def obj_at'_def)
   apply (fastforce elim!: pred_tcb'_weakenE)
  apply (clarsimp simp: valid_ep'_def split: endpoint.splits)
  done

lemma ex_nonz_cap_to'_tcb_in_WaitingNtfn'_q:
  "\<lbrakk>ko_at' ntfn ntfnPtr s; ntfnObj ntfn = Structures_H.ntfn.WaitingNtfn q; valid_objs' s;
    sym_refs (state_refs_of' s); if_live_then_nonz_cap' s\<rbrakk>
   \<Longrightarrow> \<forall>t\<in>set q. ex_nonz_cap_to' t s"
  apply (clarsimp simp: valid_obj'_def valid_ntfn'_def)
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x = ntfnPtr in allE)
  apply (drule_tac x = "(t, NTFNSignal)" in bspec)
   apply (clarsimp simp: state_refs_of'_def obj_at'_def refs_of'_def projectKOs)
  apply (fastforce intro: if_live_state_refsE)
  done

lemma cancelAllSignals_invs'_helper:
  "\<lbrace>all_invs_but_ct_not_inQ'
    and (\<lambda>s. \<forall>x \<in> set q. tcb_at' x s)
    and (\<lambda>s. (\<forall>x \<in> set q. ex_nonz_cap_to' x s))\<rbrace>
    mapM_x (\<lambda>t. do y <- setThreadState Structures_H.thread_state.Restart t;
                        possibleSwitchTo t
                od) q
   \<lbrace>\<lambda>rv. all_invs_but_ct_not_inQ'\<rbrace>"
  apply (rule mapM_x_inv_wp2)
   apply clarsimp
  apply (wpsimp wp: sts_st_tcb_at'_cases valid_irq_node_lift irqs_masked_lift
                    hoare_vcg_const_Ball_lift hoare_vcg_all_lift hoare_vcg_imp_lift'
              simp: cteCaps_of_def o_def)
  apply (intro conjI)
           apply (clarsimp simp: valid_tcb_state'_def global'_no_ex_cap
                          dest!: set_mono_suffix
                  | (drule (1) bspec, clarsimp simp: valid_pspace'_def))+
  done

lemma cancelAllSignals_invs'[wp]:
  "cancelAllSignals ntfnPtr \<lbrace>invs'\<rbrace>"
  apply (simp add: cancelAllSignals_def)
  apply (rule hoare_seq_ext[OF _ stateAssert_sp])
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp'])
  apply (case_tac "ntfnObj ntfn"; simp)
    apply wpsimp
   apply wpsimp
  apply (wpsimp wp: rescheduleRequired_all_invs_but_ct_not_inQ sts_st_tcb_at'_cases
                    cancelAllSignals_invs'_helper hoare_vcg_const_Ball_lift
                    hoare_drop_imps hoare_vcg_all_lift)
  apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def valid_ntfn'_def)
  apply (prop_tac "valid_ntfn' ntfn s")
   apply (frule (2) ntfn_ko_at_valid_objs_valid_ntfn')
  apply (clarsimp simp: valid_ntfn'_def)
  apply (intro conjI impI)
    apply (clarsimp simp: list_refs_of_replies'_def opt_map_def o_def split: option.splits)
   apply (fastforce intro: if_live_then_nonz_capE'
                     simp: ko_wp_at'_def live'_def obj_at'_def projectKOs live_ntfn'_def)
  apply (fastforce dest: ex_nonz_cap_to'_tcb_in_WaitingNtfn'_q simp: sym_refs_asrt_def)
  done

lemma setQueue_valid_ep'[wp]:
  "setQueue domain prio q \<lbrace>valid_ep' ep\<rbrace>"
  apply (clarsimp simp: setQueue_def)
  apply wpsimp
  apply (clarsimp simp: valid_ep'_def split: endpoint.splits)
  done

lemma addToBitmap_valid_ep'[wp]:
  "addToBitmap tdom prio \<lbrace>valid_ep' ep\<rbrace>"
  apply (clarsimp simp: addToBitmap_def modifyReadyQueuesL2Bitmap_def getReadyQueuesL2Bitmap_def
                        modifyReadyQueuesL1Bitmap_def getReadyQueuesL1Bitmap_def)
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
  apply (fastforce simp: valid_ep'_def obj_at'_def projectKOs objBitsKO_def split: endpoint.splits)
  done

lemma rescheduleRequired_valid_ep'[wp]:
  "rescheduleRequired \<lbrace>valid_ep' ep\<rbrace>"
  apply (clarsimp simp: rescheduleRequired_def)
  apply (rule hoare_seq_ext_skip, (solves \<open>wpsimp wp: isSchedulable_inv\<close>))+
  apply (wpsimp simp: valid_ep'_def split: endpoint.splits)
  done

lemma possibleSwitchTo_valid_ep'[wp]:
  "possibleSwitchTo target \<lbrace>valid_ep' ep\<rbrace>"
  apply (clarsimp simp: possibleSwitchTo_def)
  apply (wpsimp wp: threadGet_inv hoare_drop_imps hoare_vcg_if_lift2 inReleaseQueue_inv)
  apply (clarsimp simp: valid_ep'_def split: endpoint.splits)
  done

lemma setThreadState_valid_ep'[wp]:
  "setThreadState state tptr \<lbrace>valid_ep' ep\<rbrace>"
  apply (clarsimp simp: setThreadState_def scheduleTCB_def)
  apply (wpsimp wp: threadSet_wp isSchedulable_inv)
  apply (fastforce simp: valid_ep'_def obj_at'_def projectKOs objBitsKO_def split: endpoint.splits)
  done

lemma replyUnlink_valid_ep'[wp]:
  "replyUnlink replyPtr tcbPtr \<lbrace>valid_ep' ep\<rbrace>"
  apply (clarsimp simp: replyUnlink_def updateReply_def)
  apply (wpsimp wp: set_reply'.set_wp gts_wp')
  apply (fastforce simp: valid_ep'_def obj_at'_def projectKOs objBitsKO_def split: endpoint.splits)
  done

lemma cancelAllIPC_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace> cancelAllIPC ep \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: cancelAllIPC_def ep'_Idle_case_helper cong del: if_cong)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ get_ep_sp'])
  apply (rule hoare_if; (solves \<open>wpsimp\<close>)?)
  apply (rule_tac B="\<lambda>_ s. valid_objs' s \<and> valid_ep' epa s" in hoare_seq_ext[rotated])
   apply (wpsimp wp: set_ep_valid_objs')
    apply (wpsimp wp: set_ep'.set_wp)
   apply (clarsimp simp: pred_conj_def simp del: fun_upd_apply)
   apply (frule (1) ep_ko_at_valid_objs_valid_ep')
   apply (fastforce simp: valid_ep'_def obj_at'_def projectKOs objBitsKO_def split: endpoint.splits)
  apply (rule hoare_seq_ext)
   apply wpsimp
  apply (rule_tac Q="\<lambda>_ s. valid_objs' s \<and> valid_ep' ep s" in hoare_strengthen_post; clarsimp)
  apply (rule mapM_x_wp')
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip, wpsimp wp: replyUnlink_valid_objs')
  apply (wpsimp wp: threadGet_wp hoare_drop_imps replyUnlink_valid_objs')
  apply (fastforce simp: valid_ep'_def valid_tcb_state'_def obj_at'_def projectKOs
                  split: endpoint.splits)
  done

lemma cancelAllSignals_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace> cancelAllSignals ntfn \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: cancelAllSignals_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext [OF _ get_ntfn_sp'])
  apply (case_tac "ntfnObj ntfna", simp_all)
    apply (wp, simp)
   apply (wp, simp)
  apply (rename_tac list)
  apply (rule_tac Q="\<lambda>rv s. valid_objs' s \<and> (\<forall>x\<in>set list. tcb_at' x s)"
                  in hoare_post_imp)
   apply simp
  apply (wpsimp wp: setSchedulerAction_valid_objs' mapM_x_wp' sts_valid_objs'
                    hoare_vcg_ball_lift typ_at_lifts)
   apply (simp add: valid_tcb_state'_def)
  apply (wp hoare_vcg_ball_lift)
  apply (auto simp: projectKOs valid_obj'_def valid_ntfn'_def
              dest: ko_at_valid_objs')
  done

lemma cancelAllIPC_st_tcb_at:
  "\<lbrace>st_tcb_at' P t and K (P Inactive \<and> P Restart)\<rbrace>
   cancelAllIPC epptr
   \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  unfolding cancelAllIPC_def
  apply (rule hoare_gen_asm)
  apply (wpsimp wp: mapM_x_wp' sts_st_tcb_at'_cases hoare_vcg_imp_lift threadGet_obj_at'_field
                    hoare_vcg_disj_lift replyUnlink_st_tcb_at' hoare_vcg_all_lift
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

lemma threadSet_unlive_other:
  "\<lbrace>ko_wp_at' (Not \<circ> live') p and K (p \<noteq> t)\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>rv. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  by (clarsimp simp: threadSet_def valid_def getObject_def
                     setObject_def in_monad loadObject_default_def
                     ko_wp_at'_def projectKOs split_def in_magnitude_check
                     objBits_simps' updateObject_default_def
                     ps_clear_upd' ARM_H.fromPPtr_def)

lemma rescheduleRequired_unlive[wp]:
  "\<lbrace>\<lambda>s. ko_wp_at' (Not \<circ> live') p s \<and> sch_act_not p s\<rbrace>
   rescheduleRequired
   \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp | simp | wpc)+
   apply (simp add: tcbSchedEnqueue_def unless_def
                    threadSet_def setQueue_def threadGet_def)
   apply (wpsimp wp: setObject_ko_wp_at getObject_tcb_wp isSchedulable_wp
               simp: objBits_simps' bitmap_fun_defs)+
  apply (clarsimp simp: o_def)
  apply (drule obj_at_ko_at')
  apply clarsimp
  done

lemma tcbSchedEnqueue_unlive_other:
  "\<lbrace>ko_wp_at' (Not \<circ> live') p and K (p \<noteq> t)\<rbrace>
   tcbSchedEnqueue t
   \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def)
  apply (wpsimp wp: threadGet_wp threadSet_unlive_other)
  apply (fastforce simp: obj_at'_def projectKOs ko_wp_at'_def)
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
  apply (fastforce simp: ko_wp_at'_def obj_at'_def projectKOs is_aligned_def ps_clear_def objBitsKO_def)
  done

lemma replyUnlink_unlive:
  "\<lbrace>ko_wp_at' (Not \<circ> live') p and sch_act_not p\<rbrace>
   replyUnlink replyPtr tcbPtr
   \<lbrace>\<lambda>_. ko_wp_at' (Not o live') p\<rbrace>"
  apply (clarsimp simp: replyUnlink_def updateReply_def)
  apply (wpsimp wp: setThreadState_Inactive_unlive set_reply'.set_wp gts_wp')
  apply (fastforce simp: ko_wp_at'_def obj_at'_def projectKOs is_aligned_def ps_clear_def
                         objBitsKO_def live'_def live_reply'_def)
  done

lemma cancelAllIPC_unlive:
  "\<lbrace>valid_objs' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)\<rbrace>
   cancelAllIPC ep
   \<lbrace>\<lambda>rv. ko_wp_at' (Not \<circ> live') ep\<rbrace>"
  apply (simp add: cancelAllIPC_def ep'_Idle_case_helper)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ get_ep_sp'], rename_tac endpoint)
  apply (rule hoare_if)
   apply (wpsimp simp: ko_wp_at'_def live'_def obj_at'_def projectKOs)

  apply (rule_tac B="\<lambda>_ s. valid_objs' s
                           \<and> sch_act_wf (ksSchedulerAction s) s
                           \<and> ko_wp_at' (Not \<circ> live') ep s
                           \<and> ep_at' ep s
                           \<and> valid_ep' endpoint s"
               in hoare_seq_ext[rotated])
   apply (wpsimp wp: set_ep_valid_objs' set_ep'.sch_act_wf)
    apply (wpsimp wp: set_ep'.set_wp)
   apply (clarsimp simp del: fun_upd_apply)
   apply (frule (1) ep_ko_at_valid_objs_valid_ep')
   apply (clarsimp simp: valid_ep'_def ko_wp_at'_def obj_at'_def projectKOs objBitsKO_def
                         ps_clear_def)
   apply (fastforce simp: valid_ep'_def obj_at'_def projectKOs objBitsKO_def split: endpoint.splits)

  apply clarsimp
  apply (rule_tac Q="\<lambda>s. valid_objs' s
                         \<and> sch_act_not ep s
                         \<and> ko_wp_at' (Not \<circ> live') ep s
                         \<and> ep_at' ep s
                         \<and> valid_ep' endpoint s"
               in hoare_weaken_pre[rotated])
   apply (clarsimp simp: st_tcb_at'_def obj_at'_def projectKOs)
  apply (rule hoare_seq_ext)
   apply (wpsimp wp: rescheduleRequired_unlive)
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp')
   apply (rule hoare_seq_ext_skip, wpsimp)
   apply (rule hoare_seq_ext_skip, wpsimp wp: replyUnlink_valid_objs' replyUnlink_unlive)
   apply (wpsimp wp: possibleSwitchTo_unlive_other setThreadState_unlive_other hoare_drop_imps
                     possibleSwitchTo_sch_act_not_other)
   apply (clarsimp simp: valid_tcb_state'_def obj_at'_def projectKOs)
   apply (fastforce simp: valid_ep'_def obj_at'_def projectKOs split: endpoint.splits)
  apply clarsimp
  done

lemma cancelAllSignals_unlive_helper:
  "\<lbrace>\<lambda>s. (\<forall>x\<in>set xs. tcb_at' x s) \<and> ko_wp_at' (Not \<circ> live') p s
         \<and> sch_act_not p s \<and> p \<notin> set xs\<rbrace>
   mapM_x (\<lambda>t. do
                 y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
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
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext [OF _ get_ntfn_sp'])
  apply (case_tac "ntfnObj ntfn"; simp)
    apply wp
    apply (fastforce simp: obj_at'_real_def projectKOs live_ntfn'_def ko_wp_at'_def)
   apply wp
   apply (fastforce simp: obj_at'_real_def projectKOs live_ntfn'_def ko_wp_at'_def)
  apply (wp rescheduleRequired_unlive)
    apply (rule cancelAllSignals_unlive_helper[THEN hoare_strengthen_post])
    apply fastforce
   apply (wpsimp wp: hoare_vcg_const_Ball_lift set_ntfn'.ko_wp_at
               simp: objBits_simps')
  apply (clarsimp, frule (1) ko_at_valid_objs'_pre,
         clarsimp simp: valid_obj'_def valid_ntfn'_def)
  apply (intro conjI[rotated]; clarsimp)
    apply (fastforce simp: obj_at'_def projectKOs)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
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
   \<lbrace>\<lambda>s. all_invs_but_ct_not_inQ' s
           \<and> ex_nonz_cap_to' epptr s \<and> ep_at' epptr s
           \<and> sym_refs ((state_refs_of' s) (epptr := set (xs @ ys) \<times> {EPSend}))
           \<and> (\<forall>y \<in> set (xs @ ys). state_refs_of' s y = {(epptr, TCBBlockedSend)}
                                                        \<union> tcb_non_st_state_refs_of' s y)
           \<and> distinct (xs @ ys)\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> getThreadState t;
                      if blockingIPCBadge st = badge
                      then
                        do fault \<leftarrow> threadGet tcbFault t;
                           y \<leftarrow> if fault = None
                                then
                                  do y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                                     possibleSwitchTo t
                                  od
                                else setThreadState Structures_H.thread_state.Inactive t;
                           return False
                        od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv s. all_invs_but_ct_not_inQ' s
           \<and> ex_nonz_cap_to' epptr s \<and> ep_at' epptr s
           \<and> sym_refs ((state_refs_of' s) (epptr := (set rv \<union> set ys) \<times> {EPSend}))
           \<and> (\<forall>y \<in> set ys. state_refs_of' s y = {(epptr, TCBBlockedSend)}
                                                 \<union> tcb_non_st_state_refs_of' s y)
           \<and> distinct rv \<and> distinct (xs @ ys) \<and> set rv \<subseteq> set xs \<and> (\<forall>x \<in> set xs. tcb_at' x s)\<rbrace>"
  apply (rule_tac xs=xs in rev_induct)
   apply clarsimp
   apply wp
   apply clarsimp
  apply (clarsimp simp: filterM_append bind_assoc simp del: set_append distinct_append)
  apply (drule spec, erule hoare_seq_ext[rotated])
  apply (rule hoare_seq_ext [OF _ gts_inv'])
  apply (rule hoare_pre)
   apply (wpsimp wp: valid_irq_node_lift hoare_vcg_const_Ball_lift
                     valid_irq_handlers_lift'' irqs_masked_lift sts_st_tcb'
                     hoare_vcg_all_lift sts_sch_act'
                     threadGet_inv[THEN hoare_drop_imp] hoare_vcg_imp_lift'
               simp: cteCaps_of_def o_def)
  apply clarsimp
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
          by (auto simp: state_refs_of'_def symreftype_inverse' projectKOs
                         tcb_bound_refs'_def obj_at'_def get_refs_def2 tcb_st_refs_of'_def
                  split: option.splits if_splits thread_state.splits)
         by (fastforce simp: valid_pspace'_def valid_tcb'_def valid_idle'_def
                             pred_tcb_at'_def obj_at'_def idle_tcb'_def subsetD
                      elim!: valid_objs_valid_tcbE' st_tcb_ex_cap'')+

lemmas cancelBadgedSends_filterM_helper
    = spec [where x=Nil, OF cancelBadgedSends_filterM_helper', simplified]

lemma cancelBadgedSends_invs[wp]:
  notes if_cong[cong del]
  shows
  "\<lbrace>invs'\<rbrace> cancelBadgedSends epptr badge \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: cancelBadgedSends_def)
  apply (rule hoare_seq_ext[OF _ stateAssert_sp])
  apply (rule hoare_seq_ext [OF _ get_ep_sp'], rename_tac ep)
  apply (case_tac ep, simp_all)
    apply ((wp | simp)+)[2]
  apply (subst bind_assoc [where g="\<lambda>_. rescheduleRequired",
                           symmetric])+
  apply (rule hoare_seq_ext
                [OF rescheduleRequired_all_invs_but_ct_not_inQ])
  apply (simp add: list_case_return cong: list.case_cong)
  apply (rule hoare_pre, wp valid_irq_node_lift irqs_masked_lift)
    apply (rule hoare_strengthen_post,
           rule cancelBadgedSends_filterM_helper[where epptr=epptr])
    apply (clarsimp simp: ep_redux_simps3 fun_upd_def[symmetric] o_def)
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
  apply (clarsimp simp: sym_refs_asrt_def)
  apply (frule(1) sym_refs_ko_atD')
  apply (clarsimp simp add: fun_upd_idem st_tcb_at_refs_of_rev' o_def)
  apply (drule (1) bspec, drule st_tcb_at_state_refs_ofD', clarsimp)
  apply (auto simp: tcb_bound_refs'_def get_refs_def
             split: option.splits)
  done

lemma restart_thread_if_no_fault_valid_sched_blocked_on_send:
  "\<lbrace>\<lambda>s. valid_sched s \<and> tcb_at t s
        \<and> (epptr, TCBBlockedSend) \<in> state_refs_of s t \<and> t \<noteq> idle_thread s\<rbrace>
   restart_thread_if_no_fault t
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp wp: restart_thread_if_no_fault_valid_sched_not_runnable gts_wp)
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
   apply (fastforce simp: valid_objs'_def valid_obj'_def obj_at'_def projectKOs
                   split: kernel_object.splits)
  apply (clarsimp simp: valid_ep'_def)
  apply (prop_tac "(x, EPSend) \<in> state_refs_of' s epptr")
   apply (clarsimp simp: state_refs_of'_def obj_at'_def projectKOs)
  apply (clarsimp simp: sym_refs_def)
  apply (fastforce simp: ko_wp_at'_def obj_at'_def projectKOs state_refs_of'_def)
  done

lemma cancel_badged_sends_corres:
  "corres dc (invs and valid_sched and ep_at epptr)
             (invs' and ep_at' epptr)
         (cancel_badged_sends epptr bdg) (cancelBadgedSends epptr bdg)"
  apply add_sym_refs
  apply (clarsimp simp: cancel_badged_sends_def cancelBadgedSends_def)
  apply (rule corres_stateAssert_add_assertion[where P'=\<top>, simplified])
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF _ get_ep_corres get_simple_ko_sp get_ep_sp'
                              , where Q="invs and valid_sched"
                                  and Q'="invs' and (\<lambda>s. sym_refs (state_refs_of' s))"])
     apply simp_all
   apply (case_tac ep; simp add: ep_relation_def)
   apply (rename_tac queue)
   apply (simp add: filterM_mapM list_case_return cong: list.case_cong)
   apply (rule corres_guard_imp)
     apply (rule corres_split_nor[OF _ set_ep_corres])
        apply (rule_tac F="distinct queue" in corres_gen_asm)
        apply (rule corres_split_eqr)
           apply (rule corres_split[OF rescheduleRequired_corres])
             apply (rule set_ep_corres)
             apply (simp split: list.split add: ep_relation_def)
            apply (wp weak_sch_act_wf_lift_linear)+
          apply (rule_tac P="\<lambda>s. valid_sched s \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_tcbs s"
                      and Q="\<lambda>t s. tcb_at t s \<and> (epptr, TCBBlockedSend) \<in> state_refs_of s t
                                   \<and> t \<noteq> idle_thread s"
                      and P'="\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<and> valid_queues s
                                  \<and> valid_queues' s \<and> valid_tcbs' s \<and> valid_release_queue_iff s"
                      and Q'="\<lambda>t s. tcb_at' t s \<and> st_tcb_at' (not runnable') t s"
                      and S="{t. (fst t = snd t) \<and> fst t \<in> set queue}"
                      and r="(=)"
                      and r'="(=)"
                   in corres_mapM_scheme
                 ; (solves fastforce)?)
              apply (clarsimp simp: liftM_def[symmetric])
              apply (rule corres_guard_imp)
                apply (rule corres_split [OF _ gts_corres])
                  apply (rule_tac F="\<exists>pl. st = Structures_A.BlockedOnSend epptr pl"
                               in corres_gen_asm)
                  apply (rule corres_if2[where Q=\<top> and Q'=\<top>])
                    apply (clarsimp simp: blocking_ipc_badge_def blockingIPCBadge_def
                                   split: thread_state.splits)
                   apply (clarsimp simp: o_def dc_def[symmetric] liftM_def)
                   apply (rule corres_guard_imp)
                     apply (subst bind_assoc[symmetric])
                     apply (rule corres_guard_imp)
                       apply (fold restartThreadIfNoFault_def[simplified K_bind_def isNothing_def])
                       apply (rule corres_split[OF _ restart_thread_if_no_fault_corres])
                         apply (rule corres_return_eq_same, simp)
                        apply (rule hoare_TrueI[where P=\<top>])
                       apply (rule hoare_TrueI[where P=\<top>])
                      apply simp+
                 apply (wpsimp wp: gts_wp)
                apply (wpsimp wp: gts_wp')
               apply (fastforce simp: st_tcb_def2 st_tcb_at_refs_of_rev
                               dest!: state_refs_of_elemD )
              apply (clarsimp simp: st_tcb_def2 st_tcb_at_refs_of_rev)

             apply (wpsimp wp: gts_wp)
            apply (wpsimp wp: sts_st_tcb_at'_cases threadGet_wp gts_wp')
            apply (clarsimp simp: obj_at'_def)
           apply (wpsimp wp: restart_thread_if_no_fault_valid_sched_blocked_on_send[where epptr=epptr]
                             gts_wp)

          apply (wpsimp wp: sts_weak_sch_act_wf sts_st_tcb_at'_cases
                            setThreadState_valid_queues' threadGet_wp gts_wp')
          apply (fastforce simp: valid_tcb_state'_def obj_at'_def projectKOs st_tcb_at'_def
                                 pred_neg_def weak_sch_act_wf_def)

         apply (rule_tac Q="\<lambda>_ s. valid_tcbs s \<and> pspace_aligned s \<and> pspace_distinct s
                                  \<and> ep_at epptr s \<and> valid_sched s"
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
           apply (wpsimp wp: sts_st_tcb_at'_cases threadGet_wp gts_wp')
           apply (clarsimp simp: obj_at'_def)
          apply (wpsimp wp: sts_st_tcb_at'_cases threadGet_wp gts_wp')
          apply (fastforce simp: valid_tcb_state'_def obj_at'_def projectKOs st_tcb_at'_def
                                 pred_neg_def weak_sch_act_wf_def)
         apply simp
        apply simp

       apply (clarsimp simp: ep_relation_def)
      apply (wpsimp wp: hoare_vcg_ball_lift)
     apply (wpsimp wp: hoare_vcg_ball_lift)

    apply (clarsimp simp: obj_at_def is_ep_def cong: conj_cong)
    apply (prop_tac "valid_ep (Structures_A.SendEP queue) s")
     apply (fastforce simp: valid_objs_def valid_obj_def
                      dest: invs_valid_objs)
    apply (intro conjI impI allI ballI
           ; (fastforce simp: valid_ep_def obj_at_def is_tcb_def)?)
     apply (fastforce intro: in_send_ep_queue_TCBBlockedSend)
    apply (rule not_idle_tcb_in_SendEp; fastforce)

   apply (clarsimp cong: conj_cong)
   apply (prop_tac "valid_ep' (Structures_H.SendEP queue) s")
    apply (fastforce simp: valid_objs'_def valid_obj'_def obj_at'_def projectKOs
                     dest: invs_valid_objs')
   apply (intro conjI impI ballI
          ; (fastforce simp: valid_ep'_def obj_at'_def projectKOs)?)
   apply (frule (2) in_send_ep_queue_TCBBlockedSend')
    apply fastforce
   apply (clarsimp simp: st_tcb_at_refs_of_rev' st_tcb_at'_def obj_at'_def pred_neg_def)
  apply (clarsimp simp: sym_refs_asrt_def)
  done

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
