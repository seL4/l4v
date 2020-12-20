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
  "\<lbrace>\<lambda>s. (t = t' \<longrightarrow> P Inactive) \<and> (t \<noteq> t' \<longrightarrow> st_tcb_at' P t s)\<rbrace>
   replyRemoveTCB t'
   \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  unfolding replyRemoveTCB_def cleanReply_def
  apply (wpsimp wp: replyUnlink_st_tcb_at' hoare_vcg_imp_lift' gts_wp' haskell_assert_inv)
  apply (case_tac "t = t'"; clarsimp simp: pred_tcb_at'_def)
  done

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

lemma updateReply_list_refs_of_replies'_inv:
  "\<forall>ko. replyNext_of (f ko) = replyNext_of ko \<Longrightarrow>
   \<forall>ko. replyPrev (f ko) = replyPrev ko \<Longrightarrow>
   updateReply rptr f \<lbrace>\<lambda>s. P (list_refs_of_replies' s)\<rbrace>"
  unfolding updateReply_def
  apply wpsimp
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (clarsimp simp: list_refs_of_reply'_def obj_at'_def projectKO_eq
                        list_refs_of_replies'_def opt_map_def
                 split: option.splits)
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

lemma updateReply_valid_objs'_preserved_strong:
  "\<lbrace>valid_objs' and (\<lambda>s. \<forall>r. valid_reply' r s \<longrightarrow> valid_reply' (upd r) s)\<rbrace>
   updateReply rptr upd
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding updateReply_def
  apply wpsimp
  apply (frule(1) reply_ko_at_valid_objs_valid_reply')
  apply clarsimp
  done

lemma updateReply_valid_objs'_preserved:
  "\<lbrace>valid_objs' and K (\<forall>r s. valid_reply' r s \<longrightarrow> valid_reply' (upd r) s)\<rbrace>
   updateReply rptr upd
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wpsimp wp: updateReply_valid_objs'_preserved_strong)
  done

lemma cleanReply_valid_objs'[wp]:
  "cleanReply rptr \<lbrace>valid_objs'\<rbrace>"
  unfolding cleanReply_def
  apply (wpsimp wp: updateReply_valid_objs'_preserved
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
  apply (wpsimp wp: updateReply_valid_objs'_preserved[where upd="replyTCB_update (\<lambda>_. tptrOpt)"
                                                      for tptrOpt] gts_wp'
              simp: valid_tcb_state'_def)
  apply (clarsimp simp: valid_reply'_def)
  done

lemma replyRemoveTCB_valid_pspace'[wp]:
  "replyRemoveTCB tptr \<lbrace>valid_pspace'\<rbrace>"
  unfolding replyRemoveTCB_def valid_pspace'_def cleanReply_def
  supply set_reply'.set_wp[wp del] if_split[split del]
  apply (wpsimp wp: valid_mdb'_lift updateReply_valid_objs'_preserved hoare_vcg_if_lift
                    hoare_vcg_imp_lift gts_wp' haskell_assert_inv)
  apply (clarsimp simp: valid_reply'_def if_bool_eq_conj if_distribR)
  apply (case_tac "replyPrev ko = None"; clarsimp)
   apply (drule(1) sc_ko_at_valid_objs_valid_sc'
          , clarsimp simp: valid_sched_context'_def valid_sched_context_size'_def sc_size_bounds_def
                           valid_reply'_def objBits_simps)+
  done

lemma updateReply_iflive':
  "\<lbrace>if_live_then_nonz_cap' and K (\<forall>r. live_reply' (upd r) \<longrightarrow> live_reply' r)\<rbrace>
   updateReply rptr upd
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (rule hoare_gen_asm)
  unfolding if_live_then_nonz_cap'_def
  apply (wpsimp wp: updateReply_cap_to' hoare_vcg_all_lift hoare_vcg_imp_lift'
                    updateReply_wp_all)
  apply (rename_tac ptr ko)
  apply (case_tac "ptr = rptr")
   apply clarsimp
   apply (subst (asm) same_size_ko_wp_at'_set_ko'_iff)
    apply (clarsimp simp: ko_wp_at'_def obj_at'_def projectKO_eq project_inject objBits_simps)
   apply clarsimp
   apply (erule allE, erule mp)
   apply (erule allE, frule mp, assumption)
   apply (clarsimp simp: ko_wp_at'_def obj_at'_def projectKO_eq project_inject)
  apply (subst (asm) ko_wp_at'_set_ko'_distinct, assumption)
   apply (clarsimp simp: ko_wp_at'_def obj_at'_def projectKO_eq project_inject)
  apply fast
  done

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

lemma updateReply_iflive'_strong:
  "\<lbrace>if_live_then_nonz_cap' and
    (\<lambda>s. \<forall>ko. ko_at' ko rptr s \<and> \<not> live_reply' ko \<and> live_reply' (f ko)\<longrightarrow> ex_nonz_cap_to' rptr s)\<rbrace>
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

lemma decompose_list_refs_of_replies':
  "list_refs_of_replies' s
   = (\<lambda>r. get_refs ReplyPrev (replyPrevs_of s r) \<union> get_refs ReplyNext (replyNexts_of s r))"
  apply (fastforce simp: opt_map_def map_set_def list_refs_of_reply'_def
                  split: option.splits)
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

context begin interpretation Arch .

lemma pspace_relation_reply_update_conc_only:
  "\<lbrakk> pspace_relation ps ps'; ps x = Some (Structures_A.Reply reply); ps' x = Some (KOReply reply');
     reply_relation reply new\<rbrakk>
   \<Longrightarrow> pspace_relation ps (ps'(x \<mapsto> (KOReply new)))"
  apply (simp add: pspace_relation_def pspace_dom_update dom_fun_upd2
              del: dom_fun_upd)
  apply (erule conjE)
  apply (rule ballI, drule(1) bspec)
  apply (clarsimp simp: split_def)
  apply (drule bspec, simp)
  apply (clarsimp simp: obj_relation_cuts_def2 cte_relation_def
                        pte_relation_def pde_relation_def
                 split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm if_split_asm)
  done

end

lemma replyPrevs_of_replyNext_update:
  "ko_at' reply' rp s' \<Longrightarrow>
      replyPrevs_of (s'\<lparr>ksPSpace := ksPSpace s'(rp \<mapsto>
                            KOReply (reply' \<lparr> replyNext := v \<rparr>))\<rparr>) = replyPrevs_of s'"
  apply (clarsimp simp: obj_at'_def projectKOs isNext_def
                 split: option.split_asm reply_next.split_asm)
  by (fastforce simp: projectKO_opt_reply opt_map_def)

lemma scs_of'_reply_update:
  "reply_at' rp s' \<Longrightarrow>
      scs_of' (s'\<lparr>ksPSpace := ksPSpace s'(rp \<mapsto> KOReply reply)\<rparr>) = scs_of' s'"
  apply (clarsimp simp: obj_at'_def projectKOs isNext_def
                 split: option.split_asm reply_next.split_asm)
  by (fastforce simp: projectKO_opt_sc opt_map_def)

lemma sc_replies_relation_replyNext_update:
  "\<lbrakk>sc_replies_relation s s'; ko_at' reply' rp s'\<rbrakk>
     \<Longrightarrow> sc_replies_relation s (s'\<lparr>ksPSpace := (ksPSpace s')(rp \<mapsto>
                                           KOReply (reply' \<lparr> replyNext := v \<rparr>))\<rparr>)"
  by (clarsimp simp: scs_of'_reply_update[simplified] obj_at'_def
                     replyPrevs_of_replyNext_update[simplified])

(* an example of an sr_inv lemma; to be used in reply_remove_tcb_corres *)
lemma replyNext_Next_update_sr_inv:
   "\<lbrakk>\<not>isHead v; isNext (replyNext r')\<rbrakk> \<Longrightarrow>
    sr_inv P (P' and ko_at' r' rp)
       (setReply rp (r' \<lparr> replyNext := v \<rparr>))"
  unfolding sr_inv_def
  apply (clarsimp simp: cleanReply_def in_monad setReply_def setObject_def
                        exec_get split_def getReply_def projectKOs objBits_simps
                        updateObject_default_def ARM_H.fromPPtr_def obj_at'_def
                        in_magnitude_check replySizeBits_def
                 split: option.split_asm)
  apply (clarsimp simp: state_relation_def map_to_ctes_upd_other)
  apply (frule reply_at'_cross[where ptr=rp])
   apply (clarsimp simp: obj_at'_def objBits_simps projectKOs replySizeBits_def)
  apply (rule conjI; clarsimp simp: obj_at_def is_reply)
   apply (frule (1) pspace_relation_absD)
   apply (erule (2) pspace_relation_reply_update_conc_only)
   apply (clarsimp simp: reply_relation_def getHeadScPtr_def isNext_def isHead_def
                  split: reply_next.splits option.splits)
  apply (rule sc_replies_relation_replyNext_update[simplified])
   apply simp
  by (clarsimp simp: obj_at'_def objBits_simps projectKOs replySizeBits_def)


end