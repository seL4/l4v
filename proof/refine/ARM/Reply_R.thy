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

(* an example of an sr_inv lemma *)
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
  apply (erule sc_replies_relation_replyNext_update[simplified])
  by (clarsimp simp: obj_at'_def objBits_simps projectKOs replySizeBits_def)

(* for reply_remove_tcb_corres *)

(** sym_refs and prev/next; scReply and replySc *)

lemma sym_refs_replySc_scReplies_of:
  "\<lbrakk>reply_at' rp s'; sym_refs (state_refs_of' s'); sc_at' scp s'\<rbrakk>
   \<Longrightarrow> (replies_of' s' |> replySc) rp = Some scp \<longleftrightarrow> scReplies_of s' scp = Some rp"
  apply (rule iffI)
   apply (drule_tac tp=SCReply and x=rp and y=scp in sym_refsE;
          clarsimp simp: get_refs_def2 state_refs_of'_def obj_at'_def projectKOs opt_map_left_Some)
  by (drule_tac tp=ReplySchedContext and x=scp and y=rp in sym_refsE;
      clarsimp simp: get_refs_def2 state_refs_of'_def obj_at'_def projectKOs opt_map_left_Some)

lemma sym_refs_replySCs_of_None:
  "\<lbrakk>sym_refs (state_refs_of' s'); reply_at' rp s'; replySCs_of s' rp = None\<rbrakk>
  \<Longrightarrow> \<forall>scp. sc_at' scp s' \<longrightarrow> scReplies_of s' scp \<noteq> Some rp"
  apply (clarsimp simp: obj_at'_def projectKOs)
   apply (drule_tac tp=SCReply and y=rp and x=scp in sym_refsD[rotated])
    apply (clarsimp simp: state_refs_of'_def)
   by (clarsimp simp: state_refs_of'_def get_refs_def2 opt_map_left_Some)

lemma sym_refs_next_Head_no_prevs:
  "\<lbrakk>sym_refs (list_refs_of_replies' s'); replySCs_of s' rp \<noteq> None\<rbrakk>
  \<Longrightarrow> \<forall>p. replyPrevs_of s' p \<noteq> Some rp"
  by (clarsimp elim!: sym_refs_replyNext_None simp: projectKOs opt_map_left_Some)

lemma valid_objs'_replyPrevs_of_reply_at':
  "\<lbrakk> valid_objs' s'; reply_at' rp s'; replyPrevs_of s' rp = Some rp'\<rbrakk> \<Longrightarrow> reply_at' rp' s'"
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (erule (1) valid_objsE')
  by (clarsimp simp: valid_obj'_def valid_reply'_def valid_bound_obj'_def obj_at'_def projectKOs)

lemma valid_objs'_replyNexts_of_reply_at':
  "\<lbrakk> valid_objs' s'; reply_at' rp s'; replyNexts_of s' rp = Some rp'\<rbrakk> \<Longrightarrow> reply_at' rp' s'"
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (erule (1) valid_objsE')
  by (clarsimp simp: valid_obj'_def valid_reply'_def valid_bound_obj'_def obj_at'_def projectKOs)

(** sc_with_reply and sc_replies_relations : crossing information **)

lemma sc_replies_relation_prevs_list':
  "\<lbrakk> sc_replies_relation s s';
     kheap s scp = Some (kernel_object.SchedContext sc n)\<rbrakk>
    \<Longrightarrow> heap_ls (replyPrevs_of s') (scReplies_of s' scp) (sc_replies sc)"
  apply (clarsimp simp: sc_replies_relation_def sc_replies_of_scs_def scs_of_kh_def map_project_def)
  apply (clarsimp simp: opt_map_left_Some sc_of_def)
  done

(* FIXME RT: move to TcbAcc_R? also, drop alignment conditions from TcbAcc_R.pspace_relation_tcb_at *)
lemma pspace_relation_sc_at:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "ksPSpace s' scp = Some (KOSchedContext sc')"
  shows "sc_at scp s" using assms
  apply -
  apply (erule(1) pspace_dom_relatedE)
  apply (erule(1) obj_relation_cutsE)
  apply (clarsimp simp: other_obj_relation_def is_sc_obj obj_at_def
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        ARM_A.arch_kernel_obj.split_asm)+
  done

lemma sc_replies_relation_sc_with_reply_cross_eq_pred:
  "\<lbrakk> sc_replies_relation s s'; pspace_relation (kheap s) (ksPSpace s')\<rbrakk>
    \<Longrightarrow> (\<exists>sc n.
          kheap s scp = Some (kernel_object.SchedContext sc n) \<and>
          rp \<in> set (sc_replies sc)) =
      (\<exists>xs. heap_ls (replyPrevs_of s') (scReplies_of s' scp) xs
             \<and> heap_path (replyPrevs_of s') (scReplies_of s' scp) (takeWhile ((\<noteq>) rp) xs) (Some rp))"
  apply (rule iffI; clarsimp)
   apply (fastforce dest: sc_replies_relation_prevs_list' heap_path_takeWhile_lookup_next)
  apply (case_tac "scReplies_of s' scp", simp)
  apply (clarsimp simp: opt_map_Some projectKO_sc)
  apply (rename_tac p sc')
  apply (drule (1) pspace_relation_sc_at)
  apply (clarsimp simp: obj_at_def is_sc_obj)
  apply (drule (1) sc_replies_relation_prevs_list', clarsimp simp: opt_map_left_Some)
  apply (drule (1) heap_ls_unique, clarsimp)
  apply (case_tac "rp \<in> set (sc_replies sc)"; simp)
  apply (prop_tac "\<forall>xs. rp \<notin> set xs \<longrightarrow> takeWhile ((\<noteq>) rp) xs = xs")
   using takeWhile_eq_all_conv apply blast
  apply clarsimp
  using heap_path_end_unique by blast

(* crossing equality for sc_with_reply *)
lemma sc_replies_relation_sc_with_reply_cross_eq:
  "\<lbrakk> sc_replies_relation s s'; pspace_relation (kheap s) (ksPSpace s')\<rbrakk>
    \<Longrightarrow> sc_with_reply rp s = sc_with_reply' rp s'"
  unfolding sc_with_reply_def sc_with_reply'_def
  using sc_replies_relation_sc_with_reply_cross_eq_pred
  by simp

lemma sc_replies_relation_sc_with_reply_None:
  "\<lbrakk>sc_replies_relation s s'; reply_at rp s; ko_at' (reply'::reply) rp s';
    sc_with_reply rp s = None; valid_replies s\<rbrakk>
     \<Longrightarrow> sc_replies_relation s (s'\<lparr>ksPSpace := (ksPSpace s')(rp \<mapsto> KOReply (f reply'))\<rparr>)"
  apply (clarsimp simp: sc_replies_relation_def)
  apply (rename_tac scp replies)
  apply (drule_tac x=scp and y=replies in spec2)
  apply simp
  apply (drule_tac sc=scp in valid_replies_sc_with_reply_None, simp)
  apply (clarsimp simp: projectKOs obj_at'_def projectKO_opt_sc)
  apply (rule conjI; rule impI)
   apply (clarsimp simp: obj_at_def is_reply vs_heap_simps)
  apply (erule heap_path_heap_upd_not_in)
  by (clarsimp simp: sc_replies_sc_at_def obj_at_def vs_heap_simps)

lemma replyNexts_Some_replySCs_None:
  "replyNexts_of s rp = Some nrp \<Longrightarrow> replySCs_of s rp = None"
  by (clarsimp simp: opt_map_def projectKOs obj_at'_def split: option.splits reply_next.splits)

lemma replySCs_Some_replyNexts_None:
  "replySCs_of s rp = Some nrp \<Longrightarrow> replyNexts_of s rp = None"
  by (clarsimp simp: opt_map_def projectKOs obj_at'_def split: option.splits reply_next.splits)

lemma sc_replies_relation_sc_with_reply_heap_path:
  "\<lbrakk>sc_replies_relation s s'; sc_with_reply rp s = Some scp\<rbrakk>
  \<Longrightarrow> heap_ls  (replyPrevs_of s') (scReplies_of s' scp) (the (sc_replies_of s scp))
    \<and> heap_path (replyPrevs_of s') (scReplies_of s' scp) (takeWhile ((\<noteq>) rp) (the (sc_replies_of s scp))) (Some rp)"
  apply (clarsimp simp: sc_replies_relation_def dest!: sc_with_reply_SomeD)
  apply (drule_tac x=scp and y="sc_replies sc" in spec2)
  apply (clarsimp simp: vs_heap_simps)
  apply (frule (1) heap_path_takeWhile_lookup_next)
  by (metis (mono_tags) option.sel sc_replies.Some)

lemma next_reply_in_sc_replies:
  "\<lbrakk>sc_replies_relation s s'; sc_with_reply rp s = Some scp; sym_refs (list_refs_of_replies' s');
    sym_refs (state_refs_of' s'); replyNexts_of s' rp = Some nrp; reply_at' rp s'; sc_at' scp s'\<rbrakk>
  \<Longrightarrow>\<exists>xs ys. sc_replies_of s scp = Some (xs @ nrp # rp # ys)"
  supply opt_mapE[rule del]
  apply (frule (1) sc_replies_relation_sc_with_reply_heap_path)
  apply (prop_tac "replyPrevs_of s' nrp = Some rp")
   apply (simp add: sym_refs_replyNext_replyPrev_sym[symmetric])
  apply (drule sc_with_reply_SomeD, clarsimp)
  apply (prop_tac "the (sc_replies_of s scp) = sc_replies sc")
  using heap_ls_unique sc_replies_relation_prevs_list' apply blast
  apply simp
  apply (frule (3) heap_ls_prev_cases[OF _ _ _ reply_sym_heap_Prev_Next])
  apply (drule (1) sym_refs_replySCs_of_None)
   apply (erule replyNexts_Some_replySCs_None)
  apply (clarsimp simp: vs_heap_simps)
  apply (drule (2) heap_ls_next_takeWhile_append)
  by (force dest!: in_list_decompose_takeWhile)

lemma prev_reply_in_sc_replies:
  "\<lbrakk>sc_replies_relation s s'; sc_with_reply rp s = Some scp; sym_refs (list_refs_of_replies' s');
    sym_refs (state_refs_of' s'); replyPrevs_of s' rp = Some nrp; reply_at' nrp s'; sc_at' scp s'\<rbrakk>
  \<Longrightarrow>\<exists>xs ys. sc_replies_of s scp = Some (xs @ rp # nrp # ys)"
  supply opt_mapE[rule del]
  apply (frule (1) sc_replies_relation_sc_with_reply_heap_path)
  apply (prop_tac "replyNexts_of s' nrp = Some rp")
   apply (simp add: sym_refs_replyNext_replyPrev_sym[symmetric])
  apply (drule sc_with_reply_SomeD, clarsimp)
  apply (prop_tac "the (sc_replies_of s scp) = sc_replies sc")
  using heap_ls_unique sc_replies_relation_prevs_list' apply blast
  apply simp
  apply (frule (2) heap_ls_next_in_list)
  apply (frule (1) sym_refs_replySCs_of_None[where rp=nrp])
   apply (erule replyNexts_Some_replySCs_None)
  apply (drule_tac x=scp in spec)
  apply (clarsimp simp: vs_heap_simps)
  apply (frule (2) heap_ls_next_takeWhile_append[where p=rp])
  apply (frule in_list_decompose_takeWhile[where x=nrp])
  apply (frule in_list_decompose_takeWhile[where x=rp])
  apply auto
  done

lemma sc_replies_middle_reply_sc_None:
  "\<lbrakk>sym_refs (state_refs_of s); valid_replies s; sc_with_reply rp s = Some scp;
    (sc_replies_of s |> hd_opt) scp \<noteq> Some rp; sc_at scp s; reply_at rp s\<rbrakk> \<Longrightarrow>
   reply_sc_reply_at ((=) None) rp s"
  apply (clarsimp simp: obj_at_def is_sc_obj_def is_reply)
  apply (rename_tac ko n reply; case_tac ko; clarsimp)
  apply (rename_tac sc n)
  apply (drule sc_with_reply_SomeD1)
  apply (clarsimp simp: vs_heap_simps opt_map_Some)
  apply (case_tac "sc_replies sc"; simp)
   apply (clarsimp simp: sc_replies_sc_at_def obj_at_def)
  apply (rule ccontr)
  apply (clarsimp simp: reply_sc_reply_at_def obj_at_def)
  apply (case_tac "reply_sc reply"; simp)
  apply (drule sym_refs_sc_replies_sc_at)
   apply (fastforce simp: reply_sc_reply_at_def obj_at_def)
  apply (rename_tac p)
  apply clarsimp
  apply (prop_tac "sc_replies_sc_at ((\<lambda>rs. rp \<in> set rs)) p s")
   apply (clarsimp simp: sc_replies_sc_at_def obj_at_def)
   apply (metis list.set_intros(1))
  apply (drule valid_replies_sc_replies_unique)
   apply fastforce
  apply (prop_tac "scp=p")
   apply blast
  using sc_replies_sc_atE by fastforce

lemma sc_with_reply_replyNext_Some:
  " \<lbrakk>sc_replies_relation s s';
     valid_objs' s'; pspace_relation (kheap s) (ksPSpace s');
     valid_replies s; pspace_distinct s; pspace_aligned s;
     sym_refs (state_refs_of' s');
     sym_refs (list_refs_of_replies' s'); sc_at scp s;
     replyNexts_of s' rp = Some nxt_rp; reply_at rp s;
     sc_with_reply rp s = Some scp\<rbrakk>
    \<Longrightarrow> sc_with_reply nxt_rp s = Some scp"
  supply opt_mapE[rule del]
  apply (subgoal_tac "sc_with_reply' nxt_rp s' = Some scp")
   apply (fastforce simp: sc_replies_relation_sc_with_reply_cross_eq)
  apply (prop_tac "sc_with_reply' rp s' = Some scp \<and> reply_at' rp s' \<and> pspace_aligned' s' \<and> pspace_distinct' s'")
   apply (fastforce simp: sc_replies_relation_sc_with_reply_cross_eq
                   elim!: reply_at_cross pspace_distinct_cross pspace_aligned_cross)
  apply (clarsimp simp: obj_at_def is_sc_obj is_reply)
  apply (drule (1) sc_replies_relation_sc_with_reply_heap_path[rotated])
  apply (prop_tac "the (sc_replies_of s scp) = sc_replies sc")
   apply (clarsimp simp: sc_replies_of_scs_def sc_of_def scs_of_kh_def opt_map_def map_project_def)
  apply clarsimp
  apply (prop_tac "replyPrevs_of s' nxt_rp = Some rp")
   apply (erule (1) sym_refs_replyNext_replyPrev_sym[THEN iffD1])
  apply (prop_tac "heap_path (replyPrevs_of s') (scReplies_of s' scp)
                                         (takeWhile ((\<noteq>) nxt_rp) (sc_replies sc)) (Some nxt_rp)")
   apply (subst heap_path_extend[symmetric])
   apply (clarsimp simp del: heap_path_append)
   apply (subgoal_tac "nxt_rp \<in> set (sc_replies sc)")
    apply (frule (2) heap_ls_next_takeWhile_append[where p=nxt_rp])
    apply simp
   apply (prop_tac "rp \<in> set (sc_replies sc)")
    apply (case_tac "takeWhile ((\<noteq>) rp) (sc_replies sc) = (sc_replies sc)")
     apply simp
     apply (meson heap_path_end_unique option.simps(2))
    apply simp
   apply (frule (3) heap_ls_prev_cases[OF _ _ _ reply_sym_heap_Prev_Next])
   apply (erule disjE; simp)
   apply (frule replyNexts_Some_replySCs_None)
   apply (prop_tac "sc_at' scp s' \<and> (\<exists>ko. ko_at' ko rp s')")
    apply (rule conjI)
     apply (fastforce simp: obj_at'_def projectKOs opt_map_Some elim!: pspace_alignedD' pspace_distinctD')
    apply (clarsimp simp: obj_at'_def projectKOs)
    apply (rename_tac reply')
    apply (rule_tac x=reply' in exI)
    apply (clarsimp simp: projectKO_opt_reply)
   apply clarsimp
   apply (drule (2) sym_refs_replySc_scReplies_of[where rp=rp, rotated, symmetric])
   apply (clarsimp simp: projectKOs obj_at'_def opt_map_None opt_map_left_Some)
  apply (simp add: sc_with_reply'_def)
  apply (rule the_pred_option_Some)
   apply (rule_tac a=scp in ex1I, fastforce)
   apply (clarsimp simp: the_pred_option_def)
   apply (split if_split_asm; simp)
   defer
   apply fastforce
  apply (simp add: Ex1_def)
  apply clarsimp
proof -
  fix n :: nat and reply :: Structures_A.reply and sc :: Structures_A.sched_context and x :: "32 word" and xs :: "32 word list" and xa :: "32 word" and xsa :: "32 word list"
  assume a1: "scp = (THE x. \<exists>xs. heap_ls (replyPrevs_of s') (scReplies_of s' x) xs \<and> heap_path (replyPrevs_of s') (scReplies_of s' x) (takeWhile ((\<noteq>) rp) xs) (Some rp))"
  assume a2: "replyPrevs_of s' nxt_rp = Some rp"
  assume a3: "heap_ls (replyPrevs_of s') (scReplies_of s' x) xs"
  assume a4: "heap_ls (replyPrevs_of s') (scReplies_of s' (THE x. \<exists>xs. heap_ls (replyPrevs_of s') (scReplies_of s' x) xs \<and> heap_path (replyPrevs_of s') (scReplies_of s' x) (takeWhile ((\<noteq>) rp) xs) (Some rp))) (sc_replies sc)"
  assume a5: "heap_path (replyPrevs_of s') (scReplies_of s' x) (takeWhile ((\<noteq>) nxt_rp) xs) (Some nxt_rp)"
  assume a6: "heap_path (replyPrevs_of s') (scReplies_of s' (THE x. \<exists>xs. heap_ls (replyPrevs_of s') (scReplies_of s' x) xs \<and> heap_path (replyPrevs_of s') (scReplies_of s' x) (takeWhile ((\<noteq>) rp) xs) (Some rp))) (takeWhile ((\<noteq>) rp) (sc_replies sc)) (Some rp)"
  assume a7: "\<forall>y. (\<exists>xs. heap_ls (replyPrevs_of s') (scReplies_of s' y) xs \<and> heap_path (replyPrevs_of s') (scReplies_of s' y) (takeWhile ((\<noteq>) rp) xs) (Some rp)) \<longrightarrow> y = xa"
  then have "xa = scp"
    using a6 a4 a1 by blast
  then show "x = (THE w. \<exists>ws. heap_ls (replyPrevs_of s') (scReplies_of s' w) ws \<and> heap_path (replyPrevs_of s') (scReplies_of s' w) (takeWhile ((\<noteq>) rp) ws) (Some rp))"
    using a7 a5 a3 a2 a1 heap_path_extend_takeWhile by fastforce
qed

lemma sc_with_reply_replyPrev_None:
  "\<lbrakk>sc_with_reply rp s = None; sc_replies_relation s s'; valid_objs' s';
    pspace_relation (kheap s) (ksPSpace s'); valid_replies s;
    pspace_distinct s; pspace_aligned s;
    sym_refs (state_refs_of' s'); sym_refs (list_refs_of_replies' s');
    replyPrevs_of s' rp = Some prv_rp; reply_at rp s\<rbrakk>
  \<Longrightarrow> sc_with_reply prv_rp s = None"
  supply opt_mapE[rule del]
  apply (subgoal_tac "sc_with_reply' prv_rp s' = None")
   apply (fastforce simp: sc_replies_relation_sc_with_reply_cross_eq)
  apply (prop_tac "sc_with_reply' rp s' = None \<and> reply_at' rp s' \<and> pspace_aligned' s' \<and> pspace_distinct' s'")
   apply (fastforce simp: sc_replies_relation_sc_with_reply_cross_eq
                   elim!: reply_at_cross pspace_distinct_cross pspace_aligned_cross)
  apply clarsimp
  apply (drule sc_with_reply'_NoneD)
  apply (clarsimp simp: sc_with_reply'_def)
  apply (rule the_pred_option_None)
  apply (rule notI)
  apply (erule FalseI)
  apply (simp add: Ex1_def)
  apply clarsimp
  apply (rename_tac scp replies)
  apply (prop_tac "heap_path (replyPrevs_of s') (scReplies_of s' scp)
                                         (takeWhile ((\<noteq>) rp) replies) (Some rp)")
   apply (subst heap_path_extend[symmetric])
   apply (clarsimp simp del: heap_path_append)
   apply (subgoal_tac "rp \<in> set replies")
    apply (frule (2) heap_ls_next_takeWhile_append[where p=rp])
    apply simp
   apply (prop_tac "prv_rp \<in> set replies")
    apply (case_tac "takeWhile ((\<noteq>) prv_rp) replies = replies")
     apply simp
     apply (meson heap_path_end_unique option.simps(2))
    apply simp
   apply (frule (3) heap_ls_prev_cases[OF _ _ _ reply_sym_heap_Prev_Next])
   apply (erule disjE; simp)
   apply (prop_tac "replyNexts_of s' prv_rp = Some rp")
    apply (erule (1) sym_refs_replyNext_replyPrev_sym[THEN iffD2])
   apply (drule replyNexts_Some_replySCs_None)
   apply (prop_tac "sc_at' scp s' \<and> (\<exists>ko. ko_at' ko prv_rp s')")
    apply (rule conjI)
     apply (fastforce simp: obj_at'_def projectKOs opt_map_Some elim!: pspace_alignedD' pspace_distinctD')
    apply (drule (2) valid_objs'_replyPrevs_of_reply_at')
    apply (drule obj_at_ko_at'[where p=prv_rp], simp)
   apply clarsimp
   apply (drule (1) sym_refs_replySc_scReplies_of[where rp=prv_rp, rotated, symmetric])
    apply (clarsimp simp: obj_at'_def)
   apply simp
  apply (clarsimp simp: set_list_mem_nonempty projectKOs obj_at'_def opt_map_None opt_map_left_Some)
  apply (rule_tac x=scp in exI)
  apply (rule conjI)
   apply (rule_tac x=replies in exI)
   apply clarsimp
  apply clarsimp
  apply (frule_tac xs=xs in heap_path_extend_takeWhile[where p=rp and np=prv_rp], simp)
   apply (clarsimp simp: opt_map_left_Some)
  apply fastforce
  done

lemma sc_with_reply_replyNext_None:
  "\<lbrakk>sc_with_reply rp s = None; sc_replies_relation s s'; valid_objs' s';
    pspace_relation (kheap s) (ksPSpace s'); valid_replies s; valid_objs s;
    pspace_distinct s; pspace_aligned s; sym_refs (state_refs_of s);
    sym_refs (state_refs_of' s'); sym_refs (list_refs_of_replies' s');
    replyNexts_of s' rp = Some nxt_rp; reply_at rp s\<rbrakk>
   \<Longrightarrow> sc_with_reply nxt_rp s = None"
  supply opt_mapE[rule del]
  apply (rule ccontr)
  apply (drule not_Some_eq[THEN iffD2])
  apply (drule not_None_eq[THEN iffD1])
  apply (drule not_ex[THEN iffD2])
  apply (erule FalseI)
  apply clarsimp
  apply (rename_tac scp)
  apply (rule_tac x=scp in exI)
  apply (frule (1) sym_refs_replyNext_replyPrev_sym[THEN iffD1])
  apply (frule (4) prev_reply_in_sc_replies)
    apply (erule (3) reply_at_cross)
   apply (rule sc_at_cross; simp?)
   apply (drule sc_with_reply_SomeD)
   apply (fastforce simp: obj_at_def is_sc_obj_def
                   elim!: valid_sched_context_size_objsI)
  apply (clarsimp simp: vs_heap_simps)
  apply (rename_tac sc n)
  apply (clarsimp simp: sc_with_reply_def' the_pred_option_def
                 split: if_split_asm)
  apply (prop_tac "sc_replies_sc_at (\<lambda>rs. rp \<in> set rs)
                     (THE x. sc_replies_sc_at (\<lambda>rs. nxt_rp \<in> set rs) x s) s")
   apply (clarsimp simp: sc_replies_sc_at_def obj_at_def)
  apply (simp add: conj_commute)
  apply (rule context_conjI; clarsimp simp: the_equality)
  using valid_replies_sc_replies_unique by blast

(** end : sc_with_reply' **)

end