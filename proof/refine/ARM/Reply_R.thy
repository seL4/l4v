(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Reply_R
imports TcbAcc_R
begin

defs replyUnlink_assertion_def:
  "replyUnlink_assertion
    \<equiv> \<lambda>replyPtr state s. state = BlockedOnReply (Some replyPtr)
                          \<or> (\<exists>ep d. state = BlockedOnReceive ep d (Some replyPtr))"


crunches updateReply
  for pred_tcb_at'[wp]: "\<lambda>s. P (pred_tcb_at' proj test t s)"
  and tcb_at'[wp]: "\<lambda>s. P (tcb_at' t s)"
  and ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and valid_queues[wp]: "valid_queues"
  and reply_at'[wp]: "\<lambda>s. P (reply_at' rp s)"

lemma replyTCB_update_reply_projs[wp]:
  "\<lbrace>\<lambda>s. P (replyNexts_of s) (replyPrevs_of s)
          ((replyTCBs_of s)(rptr := tptrOpt)) (replySCs_of s)\<rbrace>
   updateReply rptr (replyTCB_update (\<lambda>_. tptrOpt))
   \<lbrace>\<lambda>_ s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)\<rbrace>"
  unfolding updateReply_def
  apply wpsimp
  apply (erule rsubst4[where P=P])
     apply (clarsimp simp: ext opt_map_def obj_at'_def projectKO_eq)+
  done

lemma replyUnlink_st_tcb_at':
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> (t' = t \<longrightarrow> P (P' Inactive)) \<and> (t' \<noteq> t \<longrightarrow> P (st_tcb_at' P' t' s))\<rbrace>
    replyUnlink r t
   \<lbrace>\<lambda>rv s. P (st_tcb_at' P' t' s)\<rbrace>"
  unfolding replyUnlink_def
  by (wpsimp wp: sts_st_tcb_at'_cases_strong gts_wp' hoare_vcg_imp_lift
           cong: conj_cong split: if_split_asm)

lemma replyUnlink_st_tcb_at'_sym_ref:
  "\<lbrace>\<lambda>s. reply_at' rptr s \<longrightarrow>
          obj_at' (\<lambda>reply. replyTCB reply = Some tptr) rptr s \<and> test Inactive\<rbrace>
   replyUnlink rptr tptr
   \<lbrace>\<lambda>_. st_tcb_at' test tptr\<rbrace>"
  apply (wpsimp simp: replyUnlink_def
                  wp: sts_st_tcb_at'_cases gts_wp')
  apply (fastforce simp: obj_at'_def projectKOs)
  done

crunches cleanReply
  for st_tcb_at'[wp]: "st_tcb_at' P t"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  and weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (rule: weak_sch_act_wf_lift)

global_interpretation updateReply: typ_at_all_props' "updateReply r f"
  by typ_at_props'

global_interpretation cleanReply: typ_at_all_props' "cleanReply p"
  by typ_at_props'

lemma replyRemoveTCB_st_tcb_at'_Inactive':
  "\<lbrace>\<top>\<rbrace>
   replyRemoveTCB tptr
   \<lbrace>\<lambda>_. st_tcb_at' ((=) Inactive) tptr\<rbrace>"
  unfolding replyRemoveTCB_def
  apply (wpsimp wp: replyUnlink_st_tcb_at' hoare_vcg_if_lift split_del: if_split)
  done

lemma replyRemoveTCB_st_tcb_at'[wp]:
  "P Inactive \<Longrightarrow> \<lbrace>\<top>\<rbrace> replyRemoveTCB t \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (rule replyRemoveTCB_st_tcb_at'_Inactive')
  apply (clarsimp elim!: pred_tcb'_weakenE)
  done

lemma replyRemoveTCB_st_tcb_at'_cases:
  "\<lbrace>\<lambda>s. (t = t' \<longrightarrow> Q (P Inactive)) \<and> (t \<noteq> t' \<longrightarrow> Q (st_tcb_at' P t s))\<rbrace>
   replyRemoveTCB t'
   \<lbrace>\<lambda>_ s. Q (st_tcb_at' P t s)\<rbrace>"
  unfolding replyRemoveTCB_def cleanReply_def
  by (wpsimp wp: replyUnlink_st_tcb_at' gts_wp' hoare_vcg_imp_lift')

lemma replyUnlink_tcb_obj_at'_no_change:
  "\<lbrace>(\<lambda>s. P (obj_at' Q tptr s)) and
    K (\<forall>tcb st. (Q (tcbState_update (\<lambda>_. Inactive) tcb) = Q tcb) \<and>
                (Q (tcbState_update (\<lambda>_. replyObject_update Map.empty st) tcb) = Q tcb) \<and>
                (Q (tcbQueued_update (\<lambda>_. True) tcb) = Q tcb))\<rbrace>
   replyUnlink rptr tptr'
   \<lbrace>\<lambda>_ s. P (obj_at' Q tptr s)\<rbrace>"
  unfolding replyUnlink_def scheduleTCB_def rescheduleRequired_def
            updateReply_def
  apply (rule hoare_gen_asm)
  apply (wpsimp wp: setThreadState_tcb_obj_at'_no_change gts_wp')
  done

lemma replyRemoveTCB_st_tcb_at'_sym_ref:
  "\<lbrace>(\<lambda>s. tcb_at' tptr s \<longrightarrow>
          (\<forall>rptr. st_tcb_at' (\<lambda>st. replyObject st = Some rptr) tptr s \<and> reply_at' rptr s \<longrightarrow>
                    obj_at' (\<lambda>reply. replyTCB reply = Some tptr) rptr s))
      and (K (test Inactive))\<rbrace>
   replyRemoveTCB tptr
   \<lbrace>\<lambda>_. st_tcb_at' test tptr\<rbrace>"
  unfolding replyRemoveTCB_def cleanReply_def updateReply_def
  apply (rule hoare_gen_asm)
  supply set_reply'.get_wp[wp del] set_reply'.get_wp_state_only[wp] set_reply'.get_wp_rv_only[wp]
  apply (wpsimp wp: hoare_vcg_if_lift hoare_vcg_all_lift replyUnlink_st_tcb_at'_sym_ref
                    set_reply'.set_no_update[where upd="\<lambda>r. (replyNext_update Map.empty
                                                              (replyPrev_update Map.empty r))"]
                    set_reply'.set_no_update[where upd="\<lambda>r. (replyNext_update Map.empty r)"]
                    set_reply'.set_no_update[where upd="\<lambda>r. (replyPrev_update Map.empty r)"]
                    hoare_vcg_imp_lift set_reply'.get_ko_at' haskell_assert_inv
              simp: disj_imp)
       apply (rule_tac Q="\<lambda>_. obj_at' (\<lambda>r. replyTCB r = Some tptr) rptr" in hoare_post_imp,
              clarsimp)
       apply wp
      apply (rule_tac Q="\<lambda>_. obj_at' (\<lambda>r. replyTCB r = Some tptr) rptr" in hoare_post_imp,
             clarsimp)
      apply (wpsimp wp: gts_wp')+
  apply (clarsimp simp: obj_at'_def pred_tcb_at'_def)
  done

lemma replyUnlink_reply_projs[wp]:
  "\<lbrace>\<lambda>s. P (replyNexts_of s) (replyPrevs_of s)
          ((replyTCBs_of s)(rptr := None)) (replySCs_of s)\<rbrace>
   replyUnlink rptr tptr
   \<lbrace>\<lambda>_ s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)\<rbrace>"
  unfolding replyUnlink_def
  apply (wpsimp wp: gts_wp')
  apply (erule rsubst4[where P=P])
     apply (clarsimp simp: ext)+
  done

lemma setReply_valid_pde_mappings'[wp]:
  "setReply p r \<lbrace>valid_pde_mappings'\<rbrace>"
  unfolding valid_pde_mappings'_def setReply_def
  apply (wpsimp wp: hoare_vcg_all_lift)
  done

lemma replyUnlink_valid_pspace'[wp]:
  "replyUnlink rptr tptr \<lbrace>valid_pspace'\<rbrace>"
  unfolding replyUnlink_def replyUnlink_assertion_def
            updateReply_def
  apply (wpsimp wp: sts'_valid_pspace'_inv hoare_vcg_imp_lift'
              simp: valid_tcb_state'_def valid_pspace'_def)
  apply normalise_obj_at'
  apply (frule(1) reply_ko_at_valid_objs_valid_reply')
  apply (clarsimp simp: valid_reply'_def)
  done

lemma replyUnlink_idle'[wp]:
  "\<lbrace>valid_idle' and valid_pspace' and (\<lambda>s. tptr \<noteq> ksIdleThread s)\<rbrace>
   replyUnlink rptr tptr
   \<lbrace>\<lambda>_. valid_idle'\<rbrace>"
  unfolding replyUnlink_def replyUnlink_assertion_def updateReply_def
  apply (wpsimp wp: hoare_vcg_imp_lift'
              simp: pred_tcb_at'_def)
  apply normalise_obj_at'
  apply (frule(1) reply_ko_at_valid_objs_valid_reply'[OF _ valid_pspace_valid_objs'])
  apply (clarsimp simp: valid_reply'_def)
  done

crunches replyUnlink
  for valid_queues[wp]: valid_queues
  (wp: crunch_wps)

lemma updateReply_replyNexts_replyPrevs_inv:
  "\<forall>ko. replyNext_of (f ko) = replyNext_of ko \<Longrightarrow>
   \<forall>ko. replyPrev (f ko) = replyPrev ko \<Longrightarrow>
  updateReply rptr f \<lbrace>\<lambda>s. P (replyNexts_of s) (replyPrevs_of s)\<rbrace>"
  unfolding updateReply_def
  apply wpsimp
  apply (erule rsubst2[where P=P])
   apply (clarsimp simp: ext opt_map_def list_refs_of_reply'_def obj_at'_def projectKO_eq
                         map_set_def projectKO_opt_reply ARM_H.fromPPtr_def
                  split: option.splits)+
  done

lemma decompose_list_refs_of_replies':
  "list_refs_of_replies' s
   = (\<lambda>r. get_refs ReplyPrev (replyPrevs_of s r) \<union> get_refs ReplyNext (replyNexts_of s r))"
  apply (fastforce simp: opt_map_def map_set_def list_refs_of_reply'_def
                  split: option.splits)
  done

lemma updateReply_list_refs_of_replies'_inv:
  "\<forall>ko. replyNext_of (f ko) = replyNext_of ko \<Longrightarrow>
   \<forall>ko. replyPrev (f ko) = replyPrev ko \<Longrightarrow>
   updateReply rptr f \<lbrace>\<lambda>s. P (list_refs_of_replies' s)\<rbrace>"
  by (wpsimp simp: decompose_list_refs_of_replies' wp: updateReply_replyNexts_replyPrevs_inv)

lemma cleanReply_reply_projs[wp]:
  "\<lbrace>\<lambda>s. P ((replyNexts_of s)(rptr := None)) ((replyPrevs_of s)(rptr := None))
          (replyTCBs_of s) ((replySCs_of s)(rptr := None))\<rbrace>
   cleanReply rptr
   \<lbrace>\<lambda>_ s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)\<rbrace>"
  unfolding cleanReply_def updateReply_def
  apply (wpsimp wp: set_reply'.set_wp)
  apply (erule rsubst4[where P=P])
     apply (clarsimp simp: ext opt_map_def obj_at'_def projectKO_eq
                    split: option.splits)+
  done

lemma updateReply_valid_objs':
  "\<lbrace>valid_objs' and (\<lambda>s. \<forall>r. valid_reply' r s \<longrightarrow> valid_reply' (upd r) s)\<rbrace>
   updateReply rptr upd
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding updateReply_def
  apply wpsimp
  apply (frule(1) reply_ko_at_valid_objs_valid_reply')
  apply clarsimp
  done

lemma cleanReply_valid_objs'[wp]:
  "cleanReply rptr \<lbrace>valid_objs'\<rbrace>"
  unfolding cleanReply_def
  apply (wpsimp wp: updateReply_valid_objs'
              simp: valid_reply'_def)
  done

crunches cleanReply, updateReply
  for valid_idle'[wp]: valid_idle'
  and ct_not_inQ[wp]: ct_not_inQ
  and sch_act_wf[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  and valid_inQ_queues[wp]: valid_inQ_queues
  and sch_act_not[wp]: "sch_act_not t"
  and aligned'[wp]: pspace_aligned'
  and distinct'[wp]: pspace_distinct'
  and no_0_obj'[wp]: "no_0_obj'"
  and cap_to': "ex_nonz_cap_to' t"

crunches replyUnlink
  for list_refs_of_replies'[wp]: "\<lambda>s. P (list_refs_of_replies' s)"
  and replyNexts_replyPrevs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s)"
  and ct_not_inQ[wp]: ct_not_inQ
  and ex_nonz_cap_to'[wp]: "(\<lambda>s. ex_nonz_cap_to' t s)"
  and valid_irq_handlers'[wp]: valid_irq_handlers'
  and valid_irq_states'[wp]: valid_irq_states'
  and irqs_masked'[wp]: irqs_masked'
  and ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
  and pspace_domain_valid[wp]: pspace_domain_valid
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and ksArchState[wp]: "\<lambda>s. P (ksArchState s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and sch_act_not[wp]: "sch_act_not t"
  (wp: crunch_wps updateReply_list_refs_of_replies'_inv updateReply_replyNexts_replyPrevs_inv)

crunches replyRemoveTCB
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and aligned'[wp]: pspace_aligned'
  and distinct'[wp]: pspace_distinct'
  and ct_not_inQ[wp]: ct_not_inQ
  and ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
  and cur_tcb'[wp]: "cur_tcb'"
  and no_0_obj'[wp]: "no_0_obj'"
  and it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  and ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and ksMachineState[wp]: "\<lambda>s. P (ksMachineState s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and sch_act_simple[wp]: "sch_act_simple"
  and valid_pde_mappings'[wp]: "valid_pde_mappings'"
  and untyped_ranges_zero'[wp]: "untyped_ranges_zero'"
  and ifunsafe'[wp]: "if_unsafe_then_cap'"
  and global_refs'[wp]: "valid_global_refs'"
  and valid_arch'[wp]: "valid_arch_state'"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n T p s)"
  and vms'[wp]: "valid_machine_state'"
  and valid_queues'[wp]: valid_queues'
  and valid_queues[wp]: valid_queues
  and valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'
  and cap_to': "ex_nonz_cap_to' t"
  and pspace_domain_valid[wp]: pspace_domain_valid
  (wp: crunch_wps hoare_vcg_if_lift
   simp: pred_tcb_at'_def if_distribR if_bool_eq_conj)

global_interpretation replyUnlink: typ_at_all_props' "replyUnlink replyPtr tcbPtr"
  by typ_at_props'

(* FIXME RT: move to...? *)
lemma valid_mdb'_lift:
  "(\<And>P. f \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>) \<Longrightarrow> f \<lbrace>valid_mdb'\<rbrace>"
  unfolding valid_mdb'_def
  apply simp
  done

lemma replyUnlink_valid_objs'[wp]:
  "replyUnlink rptr tptr \<lbrace>valid_objs'\<rbrace>"
  unfolding replyUnlink_def
  apply (wpsimp wp: updateReply_valid_objs'[where upd="replyTCB_update (\<lambda>_. tptrOpt)"
                                                      for tptrOpt] gts_wp'
              simp: valid_tcb_state'_def)
  apply (clarsimp simp: valid_reply'_def)
  done

lemma replyRemoveTCB_valid_pspace'[wp]:
  "replyRemoveTCB tptr \<lbrace>valid_pspace'\<rbrace>"
  unfolding replyRemoveTCB_def valid_pspace'_def cleanReply_def
  supply set_reply'.set_wp[wp del] if_split[split del]
  apply (wpsimp wp: valid_mdb'_lift updateReply_valid_objs' hoare_vcg_if_lift
                    hoare_vcg_imp_lift gts_wp' haskell_assert_inv
              simp: valid_reply'_def)
  apply (clarsimp simp: valid_reply'_def if_bool_eq_conj if_distribR)
  apply (case_tac "replyPrev ko = None"; clarsimp)
   apply (drule(1) sc_ko_at_valid_objs_valid_sc'
          , clarsimp simp: valid_sched_context'_def valid_sched_context_size'_def sc_size_bounds_def
                           valid_reply'_def objBits_simps)+
  done

lemma updateReply_iflive'_strong:
  "\<lbrace>if_live_then_nonz_cap' and
    (\<lambda>s. \<forall>ko. ko_at' ko rptr s \<and> \<not> live_reply' ko \<and> live_reply' (f ko) \<longrightarrow> ex_nonz_cap_to' rptr s)\<rbrace>
   updateReply rptr f
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding if_live_then_nonz_cap'_def
  apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)
    apply (wpsimp wp: updateReply_wp_all)
   apply wpsimp
  apply clarsimp
  apply (drule_tac x=x in spec)
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def ps_clear_def projectKO_reply)
  apply (case_tac "x=rptr"; clarsimp)
  done

lemma updateReply_iflive':
  "\<lbrace>if_live_then_nonz_cap' and K (\<forall>r. live_reply' (upd r) \<longrightarrow> live_reply' r)\<rbrace>
   updateReply rptr upd
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  by (wpsimp wp: updateReply_iflive'_strong)

lemma updateReply_valid_pspace'_strong:
  "\<lbrace>valid_pspace' and (\<lambda>s. \<forall>r. valid_reply' r s \<longrightarrow> valid_reply' (upd r) s)\<rbrace>
   updateReply rptr upd
   \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  unfolding updateReply_def
  apply (wpsimp wp: set_reply'.valid_pspace')
  apply (frule(1) reply_ko_at_valid_objs_valid_reply'[OF _ valid_pspace_valid_objs'])
  apply (clarsimp simp: valid_obj'_def)
  done

lemma updateReply_valid_pspace':
  "\<lbrace>valid_pspace' and K (\<forall>r s. valid_reply' r s \<longrightarrow> valid_reply' (upd r) s)\<rbrace>
   updateReply rptr upd
   \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wpsimp wp: updateReply_valid_pspace'_strong)
  done

lemma replyUnlink_iflive'[wp]:
  "replyUnlink rptr tptr \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  unfolding replyUnlink_def
  apply (wpsimp wp: updateReply_iflive' gts_wp' simp: live_reply'_def)
  done

lemma cleanReply_iflive'[wp]:
  "cleanReply rptr \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  unfolding cleanReply_def
  apply (wpsimp wp: updateReply_iflive' simp: live_reply'_def)
  done

lemma replyRemoveTCB_iflive'[wp]:
  "replyRemoveTCB tptr \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  unfolding replyRemoveTCB_def
  apply (wpsimp wp: hoare_vcg_all_lift updateReply_iflive' hoare_vcg_if_lift hoare_vcg_imp_lift'
                    gts_wp'
         split_del: if_split)
  apply (clarsimp simp: live_reply'_def)
  apply (intro impI conjI allI
         ; clarsimp simp: live_reply'_def pred_tcb_at'_def)
   apply normalise_obj_at'
   apply (rename_tac s sc reply tcb_reply_ptr prev_ptr next_ptr tcb)
   apply (prop_tac "live_sc' sc")
    apply (clarsimp simp: live_sc'_def)
   apply (prop_tac "ko_wp_at' live' (theHeadScPtr (Some next_ptr)) s")
    apply (clarsimp simp: ko_wp_at'_def obj_at'_def projectKO_eq project_inject)
   apply (clarsimp simp: if_live_then_nonz_cap'_def)
  apply normalise_obj_at'
  apply (rename_tac s sc reply tcb_reply_ptr next_ptr tcb)
  apply (prop_tac "live_sc' sc")
   apply (clarsimp simp: live_sc'_def)
  apply (prop_tac "ko_wp_at' live' (theHeadScPtr (Some next_ptr)) s")
   apply (clarsimp simp: ko_wp_at'_def obj_at'_def projectKO_eq project_inject)
  apply (clarsimp simp: if_live_then_nonz_cap'_def)
  done

lemma cleanReply_valid_pspace'[wp]:
  "cleanReply rptr \<lbrace>valid_pspace'\<rbrace>"
  unfolding cleanReply_def
  apply (wpsimp wp: updateReply_valid_pspace' simp: live_reply'_def)
  apply (clarsimp simp: valid_reply'_def)
  done

lemma updateReply_replyNext_Nothing[wp]:
  "\<lbrace>\<lambda>s. P ((replyNexts_of s)(rptr := Nothing)) (replyPrevs_of s)\<rbrace>
   updateReply rptr (replyNext_update (\<lambda>_. Nothing))
   \<lbrace>\<lambda>_ s. P (replyNexts_of s) (replyPrevs_of s)\<rbrace>"
  unfolding updateReply_def
  apply wpsimp
  apply (erule rsubst2[where P=P])
   apply (clarsimp simp: ext get_refs_def opt_map_def list_refs_of_reply'_def obj_at'_def
                         projectKO_eq
                  split: option.split)+
  done

lemma updateReply_replyPrev_Nothing[wp]:
  "\<lbrace>\<lambda>s. P (replyNexts_of s) ((replyPrevs_of s)(rptr := Nothing))\<rbrace>
   updateReply rptr (replyPrev_update (\<lambda>_. Nothing))
   \<lbrace>\<lambda>_ s. P (replyNexts_of s) (replyPrevs_of s)\<rbrace>"
  unfolding updateReply_def
  apply wpsimp
  apply (erule rsubst2[where P=P])
   apply (clarsimp simp: ext get_refs_def opt_map_def list_refs_of_reply'_def obj_at'_def
                         projectKO_eq
                  split: option.split)+
  done

lemma cleanReply_list_refs_of_replies':
  "\<lbrace>\<lambda>s. P ((list_refs_of_replies' s)(rptr := {}))\<rbrace>
   cleanReply rptr
   \<lbrace>\<lambda>_ s. P (list_refs_of_replies' s)\<rbrace>"
  unfolding cleanReply_def decompose_list_refs_of_replies'
  apply wpsimp
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (clarsimp simp: list_refs_of_reply'_def fun_upd_def)
  done

lemma isHead_to_head:
  "isHead x = (\<exists>scPtr. x = Some (Head scPtr))"
  "(\<forall>scPtr. y \<noteq> Head scPtr) = (\<exists>rPtr. y = Next rPtr)"
  apply (clarsimp simp: isHead_def split: option.split reply_next.split)
  apply (case_tac y; clarsimp)
  done

(* sym_heap *)

lemma sym_refs_replyNext_replyPrev_sym:
  "sym_refs (list_refs_of_replies' s') \<Longrightarrow>
    replyNexts_of s' rp = Some rp' \<longleftrightarrow> replyPrevs_of s' rp' = Some rp"
  apply (rule iffI; clarsimp simp: projectKO_opts_defs split: kernel_object.split_asm)
   apply (drule_tac tp=ReplyNext and y=rp' and x=rp in sym_refsD[rotated])
    apply (clarsimp simp: map_set_def opt_map_left_Some list_refs_of_reply'_def projectKO_opt_reply)
   apply (clarsimp simp: opt_map_left_Some map_set_def get_refs_def2 list_refs_of_reply'_def
                  split: option.split_asm)
  apply (drule_tac tp=ReplyPrev and y=rp and x=rp' in sym_refsD[rotated])
   apply (clarsimp simp: map_set_def opt_map_left_Some list_refs_of_reply'_def projectKO_opt_reply)
  by (clarsimp simp: opt_map_left_Some map_set_def get_refs_def2 list_refs_of_reply'_def
              split: option.split_asm)

lemma reply_sym_heap_Next_Prev:
  "sym_refs (list_refs_of_replies' s') \<Longrightarrow> sym_heap (replyNexts_of s') (replyPrevs_of s')"
  using sym_refs_replyNext_replyPrev_sym by clarsimp

lemmas reply_sym_heap_Prev_Next
  = sym_heap_symmetric[THEN iffD1, OF reply_sym_heap_Next_Prev]

lemmas sym_refs_replyNext_None
  = sym_heap_None[OF reply_sym_heap_Next_Prev]

lemmas sym_refs_replyPrev_None
  = sym_heap_None[OF reply_sym_heap_Prev_Next]

lemmas sym_refs_reply_heap_path_doubly_linked_Prevs_rev
  = sym_heap_path_reverse[OF reply_sym_heap_Next_Prev]

lemmas sym_refs_reply_heap_path_doubly_linked_Nexts_rev
  = sym_heap_path_reverse[OF reply_sym_heap_Prev_Next]

lemmas sym_refs_replyNext_heap_ls_Cons
  = sym_heap_ls_rev_Cons[OF reply_sym_heap_Next_Prev]

lemmas sym_refs_replyPrev_heap_ls_Cons
  = sym_heap_ls_rev_Cons[OF reply_sym_heap_Prev_Next]

lemmas sym_refs_replyNext_heap_ls
  = sym_heap_ls_rev[OF reply_sym_heap_Next_Prev]

lemmas sym_refs_replyPrev_heap_ls
  = sym_heap_ls_rev[OF reply_sym_heap_Prev_Next]

(* end: sym_heap *)

lemma ks_reply_at'_repliesD:
  "\<lbrakk>replies_of' s rptr = Some reply; sym_refs (list_refs_of_replies' s)\<rbrakk>
   \<Longrightarrow> replyNexts_of s rptr = replyNext_of reply
       \<and> (case replyNext_of reply of
            Some next \<Rightarrow> replyPrevs_of s next = Some rptr
          | None \<Rightarrow> \<forall>rptr'. replyPrevs_of s rptr' \<noteq> Some rptr)
       \<and> replyPrevs_of s rptr = replyPrev reply
       \<and> (case replyPrev reply of
            Some prev \<Rightarrow> replyNexts_of s prev = Some rptr
          | None \<Rightarrow> \<forall>rptr'. replyNexts_of s rptr' \<noteq> Some rptr)"
  apply (prop_tac "replyNexts_of s rptr = replyNext_of reply
                   \<and> replyPrevs_of s rptr = replyPrev reply ")
   apply (clarsimp simp: opt_map_def)
  apply (case_tac "replyNext_of reply"
         ; case_tac "replyPrev reply"
         ; clarsimp simp: sym_refs_replyNext_None sym_refs_replyPrev_None
                          sym_refs_replyNext_replyPrev_sym)
  done

\<comment>\<open> Used to "hide" @{term "sym_refs o list_refs_of_replies'"} from simplification. \<close>
definition protected_sym_refs :: "kernel_state \<Rightarrow> bool" where
  "protected_sym_refs s \<equiv> sym_refs (list_refs_of_replies' s)"

lemma replyRemoveTCB_sym_refs_list_refs_of_replies':
  "replyRemoveTCB tptr \<lbrace>\<lambda>s. sym_refs (list_refs_of_replies' s)\<rbrace>"
  unfolding replyRemoveTCB_def decompose_list_refs_of_replies'
  supply if_cong[cong]
  apply (wpsimp wp: cleanReply_list_refs_of_replies' hoare_vcg_if_lift hoare_vcg_imp_lift' gts_wp'
                    haskell_assert_wp
              simp: pred_tcb_at'_def
         split_del: if_split)
  unfolding decompose_list_refs_of_replies'[symmetric] protected_sym_refs_def[symmetric]
  \<comment>\<open> opt_mapE will sometimes destroy the @{term "(|>)"} inside @{term replyNexts_of}
      and @{term replyPrevs_of}, but we're using those as our local normal form. \<close>
  supply opt_mapE[rule del]
  apply (intro conjI impI allI)
       \<comment>\<open> Our 6 cases correspond to various cases of @{term replyNext} and @{term replyPrev}.
           We use @{thm ks_reply_at'_repliesD} to turn those cases into facts about
           @{term replyNexts_of} and @{term replyPrevs_of}. \<close>
       apply (all \<open>clarsimp simp: isHead_to_head
                   , normalise_obj_at'\<close>)
       apply (all \<open>drule(1) ks_reply_at'_repliesD[OF ko_at'_replies_of',
                                                  folded protected_sym_refs_def]
                   , clarsimp simp: projectKO_reply isHead_to_head\<close>)
       \<comment>\<open> Now, for each case we can blow open @{term sym_refs}, which will give us enough new
           @{term "(replyNexts_of, replyPrevs_of)"} facts that we can throw it all at metis. \<close>
       apply (clarsimp simp: sym_refs_def split_paired_Ball in_get_refs
              , intro conjI impI allI
              ; metis sym_refs_replyNext_replyPrev_sym[folded protected_sym_refs_def] option.sel
                      option.inject)+
  done

(* FIXME RT: move to...? *)
lemma objBits_sc_only_depends_on_scRefills:
  fixes sc :: sched_context
    and upd :: "sched_context \<Rightarrow> sched_context"
  assumes [simp]: "scRefills (upd sc) = scRefills sc"
  shows "objBits (upd sc) = objBits sc"
  apply (clarsimp simp: objBits_def objBitsKO_def)
  done

lemma replyRemoveTCB_valid_idle':
  "\<lbrace>valid_idle' and valid_pspace'\<rbrace>
   replyRemoveTCB tptr
   \<lbrace>\<lambda>_. valid_idle'\<rbrace>"
  unfolding replyRemoveTCB_def
  apply (wpsimp wp: cleanReply_valid_pspace' updateReply_valid_pspace' hoare_vcg_if_lift
                    hoare_vcg_imp_lift' gts_wp' setObject_sc_idle' haskell_assert_wp
         split_del: if_split)
  apply (clarsimp simp: valid_reply'_def pred_tcb_at'_def)
  apply (intro conjI impI allI
         ; simp?
         , normalise_obj_at'?
         , (solves \<open>clarsimp simp: valid_idle'_def idle_tcb'_def obj_at'_def isReply_def\<close>)?)
     apply (frule(1) sc_ko_at_valid_objs_valid_sc'[OF _ valid_pspace_valid_objs']
            , clarsimp simp: valid_sched_context'_def valid_sched_context_size'_def
                             objBits_sc_only_depends_on_scRefills)+
  done

lemma replyUnlink_sch_act[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> sch_act_not t s\<rbrace>
   replyUnlink r t
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: replyUnlink_def liftM_def)
  by (wpsimp wp: sts_sch_act' hoare_drop_imp)

lemma replyUnlink_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<and> sch_act_not t s\<rbrace>
   replyUnlink r t
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding replyUnlink_def updateReply_def
  by (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_all_lift gts_wp'
           simp: weak_sch_act_wf_def)

lemma replyRemoveTCB_sch_act_wf:
  "replyRemoveTCB tptr \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding replyRemoveTCB_def
  apply (wpsimp wp: gts_wp' haskell_assert_wp hoare_vcg_if_lift hoare_vcg_imp_lift'
              simp: pred_tcb_at'_def
         split_del: if_split)
  apply normalise_obj_at'
  apply (rename_tac tcb)
  apply (case_tac "tcbState tcb"
         ; clarsimp simp: isReply_def pred_tcb_at'_def)
  apply (intro conjI impI allI
         ; clarsimp simp: pred_tcb_at'_def obj_at'_def projectKO_eq project_inject)
  done

lemma replyRemoveTCB_invs':
  "replyRemoveTCB tptr \<lbrace>invs'\<rbrace>"
  unfolding invs'_def valid_state'_def
  apply (wpsimp wp: replyRemoveTCB_sym_refs_list_refs_of_replies' replyRemoveTCB_valid_idle'
                    valid_irq_node_lift valid_irq_handlers_lift' valid_irq_states_lift'
                    irqs_masked_lift replyRemoveTCB_sch_act_wf
              simp: cteCaps_of_def)
  done

(* FIXME RT: move this to lib *)
lemma partial_inv_inj_Some:
  "inj f \<Longrightarrow> partial_inv f (f r) = Some r"
  by (fastforce simp: proj_inj)

(* FIXME RT: move to non det lemma bucket *)
lemma put_id_return:
  "put s s = return () s"
  by (clarsimp simp: put_def return_def)

lemma set_reply_obj_ref_noop:
  "monadic_rewrite False True (reply_at rptr)
   (return ())
   (set_reply_obj_ref (K id) rptr x)"
  by (clarsimp simp: set_simple_ko_def monadic_rewrite_def exec_gets
                     update_sk_obj_ref_def gets_the_def
                     get_simple_ko_def partial_inv_inj_Some get_object_def bind_assoc obj_at_def
                     is_reply_def2 set_object_def exec_get put_id_return)

lemma updateReply_replyPrev_same_corres:
  assumes
    rr: "\<And>r1 r2. reply_relation r1 r2 \<Longrightarrow>
           reply_relation (g (\<lambda>y. new) r1) (f r2)"
  shows
  "corres dc (reply_at rp) (reply_at' rp and obj_at' (\<lambda>ko. replyPrev_same (f ko) ko) rp)
     (set_reply_obj_ref g rp new)
     (updateReply rp f)"
  apply (simp add: update_sk_obj_ref_def updateReply_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated[OF _ get_reply_corres])
      apply (rule set_reply_corres)
      apply (simp add: rr)
     apply wpsimp+
  by (clarsimp simp: obj_at'_def)

lemma updateReply_replyPrev_corres:
  "corres dc (reply_at rp and (\<lambda>s. rp \<notin> fst ` replies_with_sc s)) (reply_at' rp)
     (set_reply_obj_ref (\<lambda>_. id) rp r1)
     (updateReply rp (replyPrev_update (\<lambda>_. new)))"
  apply (simp add: update_sk_obj_ref_def updateReply_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated[OF _ get_reply_corres])
      apply (rule setReply_not_queued_corres)
      apply (simp add: reply_relation_def)
  by wpsimp+

lemma replyPrev_same_replyNext[simp]:
  "replyPrev_same (replyNext_update (\<lambda>_. Some (Head scptr)) ko) ko"
  by (clarsimp simp: replyPrev_same_def)

crunches update_sk_obj_ref
  for reply_at[wp]: "reply_at rp"
  (wp: crunch_wps)

crunches updateReply
  for sc_obj_at'[wp]: "\<lambda>s. Q (obj_at' (P :: sched_context \<Rightarrow> bool) scp s)"
  and reply_at'[wp]: "reply_at' rptr"

lemma updateReply_replyNexts_replyPrevs:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko rptr s \<longrightarrow>
       P (\<lambda>a. if a = rptr then replyNext_of (f ko) else replyNexts_of s a)
         (\<lambda>a. if a = rptr then replyPrev (f ko) else replyPrevs_of s a)\<rbrace>
   updateReply rptr f
   \<lbrace>\<lambda>_ s. P (replyNexts_of s) (replyPrevs_of s)\<rbrace>"
  unfolding updateReply_def
  by wpsimp

lemma replyNext_update_corres_Head:
  "corres dc (reply_at rptr) (reply_at' rptr)
   (set_reply_obj_ref reply_sc_update rptr (Some scptr))
   (updateReply rptr (\<lambda>reply. replyNext_update (\<lambda>_. Some (Head scptr)) reply))"
  unfolding update_sk_obj_ref_def updateReply_def
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated [OF set_reply_corres get_reply_corres])
      apply (clarsimp simp: reply_relation_def)
     apply wpsimp+
  apply (clarsimp simp: obj_at'_def replyPrev_same_def)
  done

lemma replyNext_update_corres_Next:
  "corres dc (reply_at rptr) (reply_at' rptr)
   (set_reply_obj_ref reply_sc_update rptr None)
   (updateReply rptr (\<lambda>reply. replyNext_update (\<lambda>_. Some (Next scptr)) reply))"
    unfolding update_sk_obj_ref_def updateReply_def
  apply clarsimp
  apply (rule corres_guard_imp)
  apply (rule corres_split_deprecated [OF set_reply_corres get_reply_corres])
  apply (clarsimp simp: reply_relation_def)
  apply wpsimp+
  apply (clarsimp simp: obj_at'_def replyPrev_same_def)
  done

(* FIXME RT: move to Lemma bucket *)
lemma case_list_when:
  "(case l of
      [] \<Rightarrow> return ()
      | r # x \<Rightarrow> f r x)
   = (when (l \<noteq> []) $ f (hd l) (tl l))"
  by (clarsimp simp: list_case_If2)

lemma update_sc_reply_stack_update_ko_at'_corres:
  "corres dc
     (sc_at ptr)
     (ko_at' sc' ptr and (\<lambda>s. heap_ls (replyPrevs_of s) reply_ptr replies))
     (update_sched_context ptr (sc_replies_update (\<lambda>_. replies)))
     (setSchedContext ptr (scReply_update (\<lambda>_. reply_ptr) sc'))"
  apply (rule_tac Q="sc_at' ptr" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD sc_at_cross simp: obj_at'_def)
  apply (rule_tac Q="sc_obj_at (objBits sc' - minSchedContextBits) ptr" in corres_cross_add_abs_guard)
   apply (fastforce dest!: state_relationD ko_at'_cross)
  apply (rule corres_guard_imp)
    apply (rule_tac P="sc_obj_at (objBits sc' - minSchedContextBits) ptr"
               and n1="objBits sc' - minSchedContextBits"
                         in monadic_rewrite_corres[OF _ update_sched_context_rewrite])
    apply (rule corres_symb_exec_l)
       apply (rule corres_guard_imp)
         apply (rule setSchedContext_update_corres
                       [where f'="scReply_update (\<lambda>_. reply_ptr)"
                        and f="sc_replies_update (\<lambda>_. replies)"])
          apply (clarsimp simp: sc_relation_def)
         apply (clarsimp simp: objBits_def objBitsKO_def)
        apply simp+
      apply (wpsimp wp: get_sched_context_exs_valid simp: is_sc_obj_def obj_at_def)
       apply (rename_tac ko; case_tac ko; simp)
      apply simp
     apply (wpsimp simp: obj_at_def is_sc_obj_def)+
    apply (wpsimp wp: get_sched_context_no_fail)
   apply (clarsimp simp: obj_at_def is_sc_obj_def)
  apply simp
  done

lemma bindReplySc_corres:
  "corres dc (reply_at rptr and sc_at scptr and (\<lambda>s. rptr \<notin> fst ` replies_with_sc s)
                and pspace_aligned and pspace_distinct and valid_objs)
             (reply_at' rptr and sc_at' scptr)
   (bind_sc_reply scptr rptr)
   (bindScReply scptr rptr)"
  unfolding bind_sc_reply_def bindScReply_def case_list_when
  apply (clarsimp simp: liftM_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated [OF _ get_sc_corres, where R'="\<lambda>sc. reply_at' rptr and ko_at' sc scptr"])
    (* This command is the lynch-pin. This does all useful state-relation lifting
         and prepares the rest of the argument*)
      apply (rule_tac Q'="reply_at' rptr and ko_at' sc scptr
               and K (scReply sc = hd_opt (sc_replies x))
               and (\<lambda>s. scReply sc \<noteq> None \<longrightarrow> reply_at' (the (scReply sc)) s)
               and K (rptr \<notin> set (sc_replies x))
               and (\<lambda>s. heap_ls (replyPrevs_of s) (scReply sc) (sc_replies x))"
             and Q="reply_at rptr and sc_at scptr
               and (\<lambda>s. rptr \<notin> fst ` replies_with_sc s)
               and pspace_aligned and pspace_distinct and valid_objs
               and (\<lambda>s. \<exists>n. ko_at (Structures_A.SchedContext x n) scptr s)"
             in stronger_corres_guard_imp)
        apply (rule corres_guard_imp)
          apply (rule corres_split_deprecated [where r'=dc])
             apply (rule corres_add_noop_lhs)
             apply (rule monadic_rewrite_corres
                          [OF _ monadic_rewrite_bind_head,
                           OF _ set_reply_obj_ref_noop[where rptr=rptr and x=None]])
             apply (simp add: bind_assoc)
             apply (rule corres_split_deprecated[OF _ updateReply_replyPrev_corres])
                  apply (rule corres_split_deprecated[OF _ update_sc_reply_stack_update_ko_at'_corres])
                    apply (rule updateReply_replyPrev_same_corres)
                    apply (clarsimp simp: reply_relation_def)
                   apply (wpsimp wp: updateReply_replyNexts_replyPrevs)+
            apply (rule_tac F="(sc_replies x \<noteq> []) = (\<exists>y. scReply sc = Some y)" in corres_gen_asm2)
            apply (erule corres_when2)
            apply (rule_tac F="scReply sc = Some (hd (sc_replies x))" in corres_gen_asm2)
            apply simp
            apply (rule replyNext_update_corres_Next)
           apply (wpsimp wp: hoare_vcg_all_lift)
          apply wpsimp
           apply (rule_tac Q="\<lambda>_. reply_at' rptr and ko_at' sc scptr
                    and (\<lambda>s. heap_ls (replyPrevs_of s) (Some y) (sc_replies x))
                    and K (rptr \<notin> set (sc_replies x))"
                  in hoare_strengthen_post[rotated])
            apply clarsimp
            apply (erule (1) heap_path_heap_upd_not_in[simplified fun_upd_def])
           apply wpsimp
           apply (frule Some_to_the, simp)
          apply (wpsimp wp: updateReply_replyNexts_replyPrevs)
         apply simp
         apply (clarsimp simp: obj_at_def)
         apply (frule (1) valid_sched_context_objsI)
         apply (clarsimp simp: valid_sched_context_def list_all_def obj_at_def)
        apply clarsimp
        apply (case_tac "sc_replies x"; simp)
        apply (intro allI impI conjI)
        apply (subgoal_tac "replyPrevs_of s a = replyPrev ko")
         apply (erule rsubst2[where P="\<lambda>a b. heap_ls a b c" for c])
          apply (rule ext, simp)
         apply simp
        apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKO_reply opt_map_def)
       apply assumption
      apply (clarsimp simp: obj_at_def  is_sc_obj)
      apply (frule state_relation_sc_replies_relation)
      apply (subgoal_tac "scReply sc = hd_opt (sc_replies sca)")
       apply (intro conjI)
          apply clarsimp
         apply clarsimp
         apply (erule (1) reply_at_cross[rotated])
          apply (frule (1) valid_sched_context_objsI)
          apply (clarsimp simp: valid_sched_context_def list_all_def obj_at_def)
         apply fastforce
        apply (clarsimp simp: replies_with_sc_def image_def)
        apply (drule_tac x=scptr in spec)
        apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
       apply (erule (1) sc_replies_relation_prevs_list)
       apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKO_sc)
      apply (erule (1) sc_replies_relation_scReply[symmetric])
      apply (clarsimp simp: obj_at'_real_def  ko_wp_at'_def projectKO_sc)
     apply wpsimp+
  done

lemma setObject_reply_pde_mappings'[wp]:
  "setObject ptr (val :: reply) \<lbrace>valid_pde_mappings'\<rbrace>"
  by (wp valid_pde_mappings_lift')

crunches bindScReply
  for pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and if_unsafe_then_cap'[wp]: if_unsafe_then_cap'
  and valid_global_refs'[wp]: valid_global_refs'
  and valid_arch_state'[wp]: valid_arch_state'
  and valid_irq_node'[wp]: "\<lambda>s. valid_irq_node' (irq_node' s) s"
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and valid_irq_handlers'[wp]: valid_irq_handlers'
  and valid_irq_states'[wp]: valid_irq_states'
  and valid_machine_state'[wp]: valid_machine_state'
  and irqs_masked'[wp]: irqs_masked'
  and valid_release_queue'[wp]: valid_release_queue'
  and ct_not_inQ[wp]: ct_not_inQ
  and ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
  and valid_pde_mappings'[wp]: valid_pde_mappings'
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and valid_dom_schedule'[wp]: valid_dom_schedule'
  and cur_tcb'[wp]: cur_tcb'
  and no_0_obj'[wp]: no_0_obj'
  and valid_mdb'[wp]: valid_mdb'
  and tcb_at'[wp]: "tcb_at' t"
  and cte_wp_at'[wp]: "cte_wp_at' P p"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps hoare_vcg_all_lift valid_irq_node_lift simp: crunch_simps valid_mdb'_def)

crunches rescheduleRequired, scheduleTCB
  for valid_tcb_state'[wp]: "valid_tcb_state' ts"
  (wp: crunch_wps)

crunches setThreadState
  for sc_ko_at'[wp]: "\<lambda>s. P (ko_at' (sc :: sched_context) p s)"
  (wp: crunch_wps simp: crunch_simps)

lemma updateReply_obj_at':
  "\<lbrace>\<lambda>s. reply_at' rptr s \<longrightarrow>
          P (obj_at' (\<lambda>ko. if rptr = p then Q (f ko) else Q ko) p s)\<rbrace>
   updateReply rptr f
   \<lbrace>\<lambda>rv s. P (obj_at' Q p s)\<rbrace>"
  apply (simp only: obj_at'_real_def updateReply_def)
  apply (wp set_reply'.ko_wp_at)
  apply (auto simp: ko_wp_at'_def obj_at'_def projectKO_eq projectKO_reply split: if_splits)
  done

lemma no_tcb_not_in_replies_with_sc:
  "\<lbrakk>valid_replies s; sym_refs (state_refs_of s);
    reply_tcb_reply_at (\<lambda>tptr. tptr = None) reply_ptr s\<rbrakk>
   \<Longrightarrow> reply_ptr \<notin> fst ` replies_with_sc s"
  apply (intro notI)
  unfolding valid_replies_defs
  apply (erule conjE)
  apply (drule (1) set_mp)
  apply clarsimp
  apply (rename_tac scptr tptr)
  apply (frule_tac thread = tptr in st_tcb_reply_state_refs[rotated])
   apply (clarsimp simp: pred_tcb_at_def obj_at_def, rule refl)
  apply (clarsimp simp: sk_obj_at_pred_def obj_at_def)
  done

lemma updateReply_list_refs_of_replies':
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko rptr s \<longrightarrow> P ((list_refs_of_replies' s)(rptr := list_refs_of_reply' (f ko)))\<rbrace>
   updateReply rptr f
   \<lbrace>\<lambda>rv s. P (list_refs_of_replies' s)\<rbrace>"
  unfolding updateReply_def by wp

lemma updateReply_obj_at'_inv:
  "\<forall>x. P (f x) = P x \<Longrightarrow>
   updateReply rPtr f \<lbrace>\<lambda>s. Q (obj_at' (P :: reply \<Rightarrow> bool) rp s)\<rbrace>"
  apply (wpsimp wp: updateReply_wp_all)
  apply (subgoal_tac "obj_at' P rp s = (obj_at' P rp (s\<lparr>ksPSpace := ksPSpace s(rPtr \<mapsto> KOReply (f ko))\<rparr>))")
   apply simp
  by (force simp: obj_at'_real_def ko_wp_at'_def objBitsKO_def ps_clear_def
                  projectKO_reply)

lemma updateReply_iflive'_weak:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' replyPtr\<rbrace>
   updateReply replyPtr f
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  by (wpsimp wp: updateReply_iflive'_strong)

lemma updateReply_replyTCB_invs':
  "\<lbrace>invs' and ex_nonz_cap_to' rptr and case_option \<top> (\<lambda>t. tcb_at' t) p\<rbrace>
   updateReply rptr (replyTCB_update (\<lambda>_. p))
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  by (wpsimp wp: updateReply_iflive'_weak updateReply_valid_objs' updateReply_list_refs_of_replies'_inv
           simp: invs'_def valid_state'_def valid_pspace'_def valid_reply'_def
          split: option.split_asm)

lemma bindScReply_valid_objs'[wp]:
  "\<lbrace>valid_objs' and reply_at' replyPtr\<rbrace>
   bindScReply scp replyPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding bindScReply_def
  supply set_sc_valid_objs'[wp del] set_sc'.valid_objs'[wp]
  apply (wpsimp wp: updateReply_valid_objs')
       apply (rule_tac Q="\<lambda>_. valid_objs' and sc_at' scp" in hoare_strengthen_post)
        apply wpsimp
       apply (simp add: valid_reply'_def valid_bound_obj'_def)
      apply (wpsimp wp: updateReply_valid_objs')
     apply wpsimp
      apply (rule_tac Q="\<lambda>_. valid_objs' and reply_at' y and reply_at' replyPtr
                         and ko_at' sc scp" in hoare_strengthen_post)
       apply (wpsimp wp: updateReply_valid_objs')
      apply clarsimp
      apply (prop_tac "sc_at' scp s")
       apply (clarsimp simp: obj_at'_def)
      apply (clarsimp simp: valid_reply'_def valid_obj'_def objBits_simps'
                            valid_sched_context'_def valid_sched_context_size'_def
                     dest!: sc_ko_at_valid_objs_valid_sc')+
     apply wpsimp+
  apply safe
       apply ((clarsimp simp: valid_reply'_def valid_obj'_def objBits_simps'
                              valid_sched_context'_def valid_sched_context_size'_def
                       dest!: sc_ko_at_valid_objs_valid_sc')+)[5]
  apply (clarsimp simp: obj_at'_def)
  done

lemma sym_refs_replySCs_of_scReplies_of:
  "\<lbrakk>sym_refs (state_refs_of' s'); pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> replySCs_of s' rp = Some scp \<longleftrightarrow> scReplies_of s' scp = Some rp"
  apply (rule iffI)
   apply (drule_tac tp=SCReply and x=rp and y=scp in sym_refsE;
          force simp: get_refs_def2 state_refs_of'_def projectKOs opt_map_left_Some refs_of_rev'
                dest: pspace_alignedD' pspace_distinctD' split: if_split_asm option.split_asm)+
  by (drule_tac tp=ReplySchedContext and x=scp and y=rp in sym_refsE;
      force simp: get_refs_def2 state_refs_of'_def projectKOs opt_map_left_Some refs_of_rev'
               dest: pspace_alignedD' pspace_distinctD' split: if_split_asm option.split_asm)+

crunches bindScReply
  for valid_queues[wp]: valid_queues
  and valid_queues'[wp]: valid_queues'
  and valid_release_queue[wp]: valid_release_queue

lemma bindScReply_sch_act_wf[wp]:
  "bindScReply scPtr replyPtr \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding bindScReply_def
  by (wpsimp wp: sts_sch_act' hoare_vcg_all_lift hoare_vcg_if_lift hoare_drop_imps)

lemma bindScReply_sym_refs_list_refs_of_replies':
  "\<lbrace>\<lambda>s. sym_refs (list_refs_of_replies' s) \<and>
        obj_at' (\<lambda>ko. replyPrev ko = None \<and> replyNext ko = None) replyPtr s \<and>
        (\<forall>oldReplyPtr. obj_at' (\<lambda>ko. scReply ko = Some oldReplyPtr) scPtr s \<longrightarrow>
         obj_at' (\<lambda>ko. replyNext ko = Some (Head scPtr)) oldReplyPtr s)\<rbrace>
   bindScReply scPtr replyPtr
   \<lbrace>\<lambda>_ s. sym_refs (list_refs_of_replies' s)\<rbrace>"
  supply if_split [split del]
  unfolding bindScReply_def
  apply (wpsimp wp: hoare_vcg_if_lift2 updateReply_list_refs_of_replies' updateReply_obj_at'
                    hoare_vcg_all_lift hoare_vcg_imp_lift' set_reply'.obj_at')
  by (auto simp: list_refs_of_replies'_def list_refs_of_reply'_def
                 opt_map_Some_def obj_at'_def projectKO_eq get_refs_def
           elim: delta_sym_refs split: if_splits)

lemma bindScReply_if_live_then_nonz_cap':
  "\<lbrace>if_live_then_nonz_cap'
    and ex_nonz_cap_to' scPtr and ex_nonz_cap_to' replyPtr
    and (\<lambda>s. \<forall>rp. obj_at' (\<lambda>ko. scReply ko = Some rp) scPtr s \<longrightarrow> obj_at' (\<lambda>ko. replyNext ko = Some (Head scPtr)) rp s )\<rbrace>
   bindScReply scPtr replyPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding bindScReply_def
  apply (simp (no_asm_use) split del: if_split
         | wp hoare_vcg_all_lift hoare_vcg_disj_lift hoare_vcg_imp_lift'
              hoare_vcg_if_lift set_reply'.obj_at' updateReply_iflive'_weak
         | rule threadGet_wp)+
  apply clarsimp
  apply (erule if_live_then_nonz_capE')
   apply (clarsimp simp: ko_wp_at'_def obj_at'_def projectKO_eq live_reply'_def projectKO_reply)
  done

lemma bindScReply_ex_nonz_cap_to'[wp]:
  "bindScReply scPtr replyPtr \<lbrace>ex_nonz_cap_to' ptr\<rbrace>"
  unfolding bindScReply_def
        apply (simp (no_asm_use) split del: if_split
               | wp hoare_vcg_all_lift hoare_vcg_disj_lift hoare_vcg_imp_lift'
                    hoare_vcg_if_lift set_reply'.obj_at' updateReply_obj_at'
               | rule threadGet_wp)+
  by clarsimp

lemma bindScReply_obj_at'_scTCB[wp]:
  "bindScReply scPtr replyPtr
   \<lbrace>\<lambda>s. P (obj_at' (\<lambda>ko. P' (scTCB ko)) scPtr s)\<rbrace>"
  unfolding bindScReply_def
  apply (wpsimp wp: hoare_drop_imp set_sc'.obj_at')
  by (auto simp: obj_at'_real_def ko_wp_at'_def)

lemma setReply_valid_tcb'[wp]:
  "setReply rp new  \<lbrace>valid_tcb' tcb\<rbrace>"
  apply (clarsimp simp: setReply_def)
  by (rule setObject_valid_tcb')

lemma setReply_valid_tcbs'[wp]:
  "setReply rp new  \<lbrace>valid_tcbs'\<rbrace>"
  unfolding valid_tcbs'_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' set_reply'.setObject_wp
           simp: setReply_def)

crunches updateReply
  for valid_tcbs'[wp]: valid_tcbs'

lemma updateReply_None_sym_refs_list_refs_of_replies'[wp]:
  "\<lbrace>\<lambda>s. sym_refs (list_refs_of_replies' s) \<and>
        replySCs_of s rptr \<noteq> None\<rbrace>
   updateReply rptr (replyNext_update (\<lambda>_. Nothing))
   \<lbrace>\<lambda>_ s. sym_refs (list_refs_of_replies' s)\<rbrace>"
  apply (wpsimp wp: updateReply_list_refs_of_replies')
  apply (erule delta_sym_refs)
   apply (auto simp: list_refs_of_reply'_def map_set_def
                     opt_map_def obj_at'_def projectKOs
              split: option.splits if_splits)
  done

lemma updateReply_replyNext_Nothing_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> replySCs_of s rptr \<noteq> None\<rbrace>
   updateReply rptr (replyNext_update (\<lambda>_. Nothing))
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp only: invs'_def valid_state'_def valid_pspace'_def)
  apply (wpsimp wp: updateReply_valid_objs' updateReply_iflive')
  apply (clarsimp simp: obj_at'_def projectKOs valid_reply'_def live_reply'_def
                  dest: pspace_alignedD' pspace_distinctD')
  done

end
