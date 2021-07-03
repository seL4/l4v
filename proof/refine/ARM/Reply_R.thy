(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Reply_R
imports Schedule_R
begin

defs replyUnlink_assertion_def:
  "replyUnlink_assertion
    \<equiv> \<lambda>replyPtr state s. state = BlockedOnReply (Some replyPtr)
                          \<or> (\<exists>ep d. state = BlockedOnReceive ep d (Some replyPtr))"

lemma valid_reply'_updates[simp]:
  "\<And>f. valid_reply' reply (ksReprogramTimer_update f s) = valid_reply' reply s"
  "\<And>f. valid_reply' reply (ksReleaseQueue_update f s) = valid_reply' reply s"
  by (auto simp: valid_reply'_def valid_bound_obj'_def split: option.splits)

crunches updateReply
  for pred_tcb_at'[wp]: "\<lambda>s. P (pred_tcb_at' proj test t s)"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  and ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and valid_queues[wp]: "valid_queues"
  and sc_obj_at'[wp]: "\<lambda>s. Q (obj_at' (P :: sched_context \<Rightarrow> bool) scp s)"

global_interpretation updateReply: typ_at_all_props' "updateReply p f"
  by typ_at_props'

lemma updateReply_replyNext_reply_projs[wp]:
  "\<lbrace>\<lambda>s. P ((replyNexts_of s)(rptr := getReplyNextPtr next)) (replyPrevs_of s)
          (replyTCBs_of s) ((replySCs_of s)(rptr := getHeadScPtr next))\<rbrace>
   updateReply rptr (replyNext_update (\<lambda>_. next))
   \<lbrace>\<lambda>_ s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)\<rbrace>"
  unfolding updateReply_def
  apply wpsimp
  apply (erule rsubst4[where P=P])
     apply (clarsimp simp: ext opt_map_def obj_at'_def projectKO_eq)+
  done

lemma updateReply_replyPrev_reply_projs[wp]:
  "\<lbrace>\<lambda>s. P (replyNexts_of s) ((replyPrevs_of s)(rptr := prev))
          (replyTCBs_of s) (replySCs_of s)\<rbrace>
   updateReply rptr (replyPrev_update (\<lambda>_. prev))
   \<lbrace>\<lambda>_ s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)\<rbrace>"
  unfolding updateReply_def
  apply wpsimp
  apply (erule rsubst4[where P=P])
     apply (clarsimp simp: ext opt_map_def obj_at'_def projectKO_eq)+
  done

lemma updateReply_replyTCB_reply_projs[wp]:
  "\<lbrace>\<lambda>s. P (replyNexts_of s) (replyPrevs_of s)
          ((replyTCBs_of s)(rptr := tptrOpt)) (replySCs_of s)\<rbrace>
   updateReply rptr (replyTCB_update (\<lambda>_. tptrOpt))
   \<lbrace>\<lambda>_ s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)\<rbrace>"
  unfolding updateReply_def
  apply wpsimp
  apply (erule rsubst4[where P=P])
     apply (clarsimp simp: ext opt_map_def obj_at'_def projectKO_eq)+
  done

lemma updateReply_reply_projs:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko rptr s \<longrightarrow>
       P (\<lambda>a. if a = rptr then replyNext_of (f ko) else replyNexts_of s a)
         (\<lambda>a. if a = rptr then replyPrev (f ko) else replyPrevs_of s a)
         (\<lambda>a. if a = rptr then replyTCB (f ko) else replyTCBs_of s a)
         (\<lambda>a. if a = rptr then replySC (f ko) else replySCs_of s a)\<rbrace>
   updateReply rptr f
   \<lbrace>\<lambda>_ s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)\<rbrace>"
  unfolding updateReply_def
  by wpsimp

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

crunches cleanReply
  for st_tcb_at'[wp]: "st_tcb_at' P t"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  and weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (rule: weak_sch_act_wf_lift)

global_interpretation cleanReply: typ_at_all_props' "cleanReply p"
  by typ_at_props'

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

lemma replyPop_st_tcb_at'_Inactive:
  "\<lbrace>\<top>\<rbrace> replyPop replyPtr tcbPtr \<lbrace>\<lambda>_. st_tcb_at' ((=) Inactive) tcbPtr\<rbrace>"
  apply (clarsimp simp: replyPop_def)
  by (wpsimp wp: replyUnlink_st_tcb_at' hoare_vcg_if_lift)

lemma replyPop_st_tcb_at'[wp]:
  "P Inactive \<Longrightarrow> \<lbrace>\<top>\<rbrace> replyPop r t \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (rule replyPop_st_tcb_at'_Inactive)
  apply (clarsimp elim!: pred_tcb'_weakenE)
  done

lemma replyRemove_st_tcb_at'_Inactive:
  "\<lbrace>\<top>\<rbrace> replyRemove replyPtr tcbPtr \<lbrace>\<lambda>_. st_tcb_at' ((=) Inactive) tcbPtr\<rbrace>"
  apply (clarsimp simp: replyRemove_def)
  by (wpsimp wp: replyUnlink_st_tcb_at' hoare_vcg_if_lift)

lemma replyRemove_st_tcb_at'[wp]:
  "P Inactive \<Longrightarrow> \<lbrace>\<top>\<rbrace> replyRemove r t \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (rule replyRemove_st_tcb_at'_Inactive)
  apply (clarsimp elim!: pred_tcb'_weakenE)
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
  and valid_mdb'[wp]: "valid_mdb'"

crunches replyUnlink
  for list_refs_of_replies'[wp]: "\<lambda>s. P (list_refs_of_replies' s)"
  and valid_queues[wp]: valid_queues
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
  and aligned'[wp]: pspace_aligned'
  and distinct'[wp]: pspace_distinct'
  and no_0_obj'[wp]: "no_0_obj'"
  and valid_mdb'[wp]: "valid_mdb'"
  (wp: crunch_wps updateReply_list_refs_of_replies'_inv simp: crunch_simps)

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

lemma updateReply_valid_objs':
  "\<lbrace>valid_objs' and (\<lambda>s. \<forall>r. valid_reply' r s \<longrightarrow> valid_reply' (upd r) s)\<rbrace>
   updateReply rptr upd
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding updateReply_def
  apply wpsimp
  apply (frule(1) reply_ko_at_valid_objs_valid_reply')
  apply clarsimp
  done


lemma replyUnlink_idle'[wp]:
  "\<lbrace>valid_idle' and (\<lambda>s. tptr \<noteq> ksIdleThread s)\<rbrace>
   replyUnlink rptr tptr
   \<lbrace>\<lambda>_. valid_idle'\<rbrace>"
  unfolding replyUnlink_def replyUnlink_assertion_def updateReply_def
  apply (wpsimp wp: hoare_vcg_imp_lift'
              simp: pred_tcb_at'_def)
  done

lemma replyUnlink_valid_objs'[wp]:
  "replyUnlink rptr tptr \<lbrace>valid_objs'\<rbrace>"
  unfolding replyUnlink_def
  apply (wpsimp wp: updateReply_valid_objs'[where upd="replyTCB_update (\<lambda>_. tptrOpt)" for tptrOpt]
                    gts_wp'
              simp: valid_tcb_state'_def)
  apply (clarsimp simp: valid_reply'_def)
  done

lemma setReply_valid_replies':
  "\<lbrace>\<lambda>s. valid_replies' s
        \<and> (replyNext_of reply \<noteq> None \<or> replyPrev reply \<noteq> None \<longrightarrow>
             (\<exists>tptr. replyTCB reply = Some tptr
                     \<and> st_tcb_at'
                       ((=) (Structures_H.thread_state.BlockedOnReply (Some rptr)))
                       tptr s))\<rbrace>
   setReply rptr reply
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  unfolding valid_replies'_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift hoare_vcg_ex_lift)
  apply auto
  done

lemma updateReply_valid_replies':
  "\<lbrace>\<lambda>s. valid_replies' s
        \<and> (\<forall>reply. ko_at' reply rptr s \<longrightarrow>
            (replyNext_of (f reply) \<noteq> None \<or> replyPrev (f reply) \<noteq> None \<longrightarrow>
              (\<exists>tptr. replyTCB (f reply) = Some tptr
                      \<and> st_tcb_at'
                        ((=) (Structures_H.thread_state.BlockedOnReply (Some rptr)))
                        tptr s)))\<rbrace>
   updateReply rptr f
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  unfolding updateReply_def
  by (wpsimp wp: setReply_valid_replies')

lemma updateReply_valid_replies'_not_linked:
  "\<lbrace>\<lambda>s. valid_replies' s
        \<and> (\<forall>reply. ko_at' reply rptr s \<longrightarrow>
                     replyNext_of (f reply) = None \<and> replyPrev (f reply) = None)\<rbrace>
   updateReply rptr f
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  apply (wpsimp wp: updateReply_valid_replies')
  by auto

lemma updateReply_valid_replies'_bound:
  "\<lbrace>\<lambda>s. valid_replies' s
        \<and> (\<forall>reply. ko_at' reply rptr s \<longrightarrow>
                     (\<exists>tptr. replyTCB (f reply) = Some tptr
                             \<and> st_tcb_at' ((=) (BlockedOnReply (Some rptr))) tptr s))\<rbrace>
   updateReply rptr f
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  by (wpsimp wp: updateReply_valid_replies')

lemma updateReply_valid_replies'_except:
  "\<lbrace>valid_replies'\<rbrace>
   updateReply rptr f
   \<lbrace>\<lambda>_. valid_replies'_except {rptr}\<rbrace>"
  unfolding valid_replies'_def valid_replies'_except_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_ex_lift updateReply_reply_projs)
  apply (auto simp: opt_map_def)
  done

lemma replyUnlink_valid_replies'[wp]:
  "\<lbrace>\<lambda>s. replyTCBs_of s rptr = Some tptr
        \<longrightarrow> valid_replies' s \<and> \<not> is_reply_linked rptr s\<rbrace>
   replyUnlink rptr tptr
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  unfolding replyUnlink_def
  apply (wpsimp wp: updateReply_valid_replies'_not_linked sts'_valid_replies'
                    hoare_vcg_all_lift hoare_vcg_imp_lift' gts_wp')
  apply normalise_obj_at'
  apply (clarsimp simp: valid_reply'_def pred_tcb_at'_def obj_at'_def projectKOs
                        replyUnlink_assertion_def)
  by (auto simp: opt_map_def split: option.splits)

lemma replyUnlink_valid_pspace'[wp]:
  "\<lbrace>\<lambda>s. valid_pspace' s \<and>
        (replyTCBs_of s rptr = Some tptr \<longrightarrow> \<not> is_reply_linked rptr s)\<rbrace>
   replyUnlink rptr tptr
   \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  by (wpsimp simp: valid_pspace'_def)

lemma replyUnlink_valid_idle'[wp]:
  "\<lbrace>valid_idle' and (\<lambda>s. tptr \<noteq> ksIdleThread s)\<rbrace>
   replyUnlink rptr tptr
   \<lbrace>\<lambda>_. valid_idle'\<rbrace>"
  unfolding replyUnlink_def replyUnlink_assertion_def updateReply_def
  by (wpsimp wp: hoare_vcg_imp_lift')

lemma decompose_list_refs_of_replies':
  "list_refs_of_replies' s
   = (\<lambda>r. get_refs ReplyPrev (replyPrevs_of s r) \<union> get_refs ReplyNext (replyNexts_of s r))"
  apply (fastforce simp: opt_map_def map_set_def list_refs_of_reply'_def
                  split: option.splits)
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

lemma cleanReply_valid_objs'[wp]:
  "cleanReply rptr \<lbrace>valid_objs'\<rbrace>"
  unfolding cleanReply_def
  apply (wpsimp wp: updateReply_valid_objs'
              simp: valid_reply'_def)
  done

lemma cleanReply_valid_replies'[wp]:
  "cleanReply rptr \<lbrace>valid_replies'\<rbrace>"
  unfolding valid_replies'_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift hoare_vcg_ex_lift)
  apply (auto simp: opt_map_def)
  done

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
  and valid_mdb'[wp]: valid_mdb'
  (wp: crunch_wps hoare_vcg_if_lift valid_mdb'_lift
   simp: pred_tcb_at'_def if_distribR if_bool_eq_conj)

global_interpretation replyUnlink: typ_at_all_props' "replyUnlink replyPtr tcbPtr"
  by typ_at_props'

lemma replyRemoveTCB_valid_objs'[wp]:
  "replyRemoveTCB tptr \<lbrace>valid_objs'\<rbrace>"
  unfolding replyRemoveTCB_def
  supply set_reply'.set_wp[wp del] if_split[split del]
  apply (wpsimp wp: updateReply_valid_objs' hoare_vcg_if_lift hoare_vcg_imp_lift gts_wp'
              simp: valid_reply'_def)
  apply (clarsimp simp: valid_reply'_def if_bool_eq_conj if_distribR)
  apply (case_tac "replyPrev ko = None"; clarsimp)
   apply (drule(1) sc_ko_at_valid_objs_valid_sc',
          clarsimp simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps)+
  done

lemma updateReply_prev_None_valid_replies'[wp]:
  "updateReply p (replyPrev_update (\<lambda>_. None)) \<lbrace>valid_replies'\<rbrace>"
  unfolding valid_replies'_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift hoare_vcg_ex_lift)
  by auto

lemma updateReply_next_None_valid_replies'[wp]:
  "updateReply p (replyNext_update (\<lambda>_. None)) \<lbrace>valid_replies'\<rbrace>"
  unfolding valid_replies'_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift hoare_vcg_ex_lift)
  by auto

lemma replyRemoveTCB_valid_replies'[wp]:
  "\<lbrace>valid_replies' and pspace_distinct' and pspace_aligned'\<rbrace>
   replyRemoveTCB tptr
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  unfolding replyRemoveTCB_def
  by (wpsimp wp: hoare_vcg_if_lift hoare_vcg_imp_lift gts_wp')

lemma replyRemoveTCB_valid_pspace'[wp]:
  "replyRemoveTCB tptr \<lbrace>valid_pspace'\<rbrace>"
  unfolding valid_pspace'_def
  by wpsimp

lemma updateReply_iflive'_strong:
  "\<lbrace>(\<lambda>s. reply_at' rptr s \<longrightarrow> if_live_then_nonz_cap' s) and
   (\<lambda>s. \<forall>ko. ko_at' ko rptr s \<and> \<not> live_reply' ko \<and> live_reply' (f ko) \<longrightarrow> ex_nonz_cap_to' rptr s)\<rbrace>
   updateReply rptr f
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding if_live_then_nonz_cap'_def
  apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)
    apply (wpsimp wp: updateReply_wp_all)
   apply wpsimp
  apply clarsimp
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def ps_clear_def projectKO_reply)
  apply (case_tac "x=rptr"; clarsimp)
  done

lemma updateReply_iflive':
  "\<lbrace>if_live_then_nonz_cap' and K (\<forall>r. live_reply' (upd r) \<longrightarrow> live_reply' r)\<rbrace>
   updateReply rptr upd
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  by (wpsimp wp: updateReply_iflive'_strong)

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
  unfolding cleanReply_def valid_pspace'_def
  apply (wpsimp wp: updateReply_valid_objs' simp: valid_reply'_def)
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
  "replyRemoveTCB tptr \<lbrace>valid_idle'\<rbrace>"
  unfolding replyRemoveTCB_def
  apply (wpsimp wp: hoare_vcg_if_lift hoare_vcg_imp_lift' gts_wp' setObject_sc_idle')
  apply (clarsimp simp: valid_reply'_def pred_tcb_at'_def)
  apply (intro conjI impI allI
         ; simp?
         , normalise_obj_at'?
         , (solves \<open>clarsimp simp: valid_idle'_def idle_tcb'_def obj_at'_def isReply_def\<close>)?)
  done

lemma replyUnlink_sch_act[wp]:
  "replyUnlink r t \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp only: replyUnlink_def liftM_def)
  apply (wpsimp wp: sts_sch_act' gts_wp')
  apply (fastforce simp: replyUnlink_assertion_def st_tcb_at'_def obj_at'_def)
  done

lemma replyUnlink_weak_sch_act_wf[wp]:
  "replyUnlink r t \<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp only: replyUnlink_def liftM_def)
  apply (wpsimp wp: sts_sch_act' gts_wp')
  by (fastforce simp: replyUnlink_assertion_def st_tcb_at'_def obj_at'_def
                      weak_sch_act_wf_def)

lemma replyRemoveTCB_sch_act_wf:
  "replyRemoveTCB tptr \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding replyRemoveTCB_def
  by (wpsimp wp: gts_wp' haskell_assert_wp hoare_vcg_if_lift hoare_vcg_imp_lift'
           simp: pred_tcb_at'_def
      split_del: if_split)

lemma replyRemoveTCB_invs':
  "replyRemoveTCB tptr \<lbrace>invs'\<rbrace>"
  unfolding invs'_def valid_state'_def valid_dom_schedule'_def
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

lemma updateReply_replyNext_not_head_corres:
  "\<not> isHead next_opt \<Longrightarrow>
   corres dc (reply_at rptr) (reply_at' rptr)
   (set_reply_obj_ref reply_sc_update rptr None)
   (updateReply rptr (\<lambda>reply. replyNext_update (\<lambda>_. next_opt) reply))"
    unfolding update_sk_obj_ref_def updateReply_def
  apply clarsimp
  apply (rule corres_guard_imp)
  apply (rule corres_split_deprecated [OF set_reply_corres get_reply_corres])
  apply (clarsimp simp: reply_relation_def isHead_def
                 split: option.splits reply_next.splits)
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

lemma bindScReply_corres:
  "corres dc (reply_at rptr and sc_at scptr and (\<lambda>s. rptr \<notin> fst ` replies_with_sc s)
                and pspace_aligned and pspace_distinct and valid_objs
                and valid_replies and (\<lambda>s. sym_refs (state_refs_of s)))
             (reply_at' rptr and sc_at' scptr)
   (bind_sc_reply scptr rptr)
   (bindScReply scptr rptr)"
  unfolding bind_sc_reply_def bindScReply_def case_list_when sym_refs_asrt_def
  apply (clarsimp simp: liftM_def)
  apply add_sym_refs
  apply (rule corres_stateAssert_implied[where P'=\<top>, simplified])
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
                and valid_replies and (\<lambda>s. sym_refs (state_refs_of s))
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
                 apply (wpsimp wp: updateReply_reply_projs)+
             apply (rule_tac F="(sc_replies x \<noteq> []) = (\<exists>y. scReply sc = Some y)" in corres_gen_asm2)
             apply (erule corres_when2)
             apply (rule_tac F="scReply sc = Some (hd (sc_replies x))" in corres_gen_asm2)
             apply simp
             apply (rule_tac P'="\<lambda>s. valid_replies s \<and> sym_refs (state_refs_of s)
                                     \<and> pspace_aligned s \<and> pspace_distinct s"
                    in corres_stateAssert_implied)
              apply (rule updateReply_replyNext_not_head_corres)
              apply (simp add: isHead_def)
             apply (erule valid_replies_sc_cross; clarsimp)
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
           apply (wpsimp wp: updateReply_reply_projs)+
          apply (clarsimp simp: obj_at_def)
          apply (frule (1) valid_sched_context_objsI)
          apply (clarsimp simp: valid_sched_context_def list_all_def obj_at_def)
         apply clarsimp
         apply (case_tac "sc_replies x"; simp)
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
       apply (force dest!: sc_replies_relation_scReplies_of
                     simp: obj_at'_def projectKOs opt_map_red vs_heap_simps is_sc_obj
                           obj_at_def)
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
  (wp: crunch_wps hoare_vcg_all_lift valid_irq_node_lift
   simp: crunch_simps valid_mdb'_def valid_dom_schedule'_def)

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
  "\<lbrace>\<lambda>s. reply_at' replyPtr s \<longrightarrow> if_live_then_nonz_cap' s \<and> ex_nonz_cap_to' replyPtr s\<rbrace>
   updateReply replyPtr f
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  by (wpsimp wp: updateReply_iflive'_strong, clarsimp simp: obj_at'_def)

lemma updateReply_replyTCB_invs':
  "\<lbrace>invs' and ex_nonz_cap_to' rptr and case_option \<top> (\<lambda>t. tcb_at' t) p and
    (\<lambda>s. is_reply_linked rptr s
         \<longrightarrow> (\<exists>tptr. p = Some tptr \<and> st_tcb_at' ((=) (BlockedOnReply (Some rptr))) tptr s))\<rbrace>
   updateReply rptr (replyTCB_update (\<lambda>_. p))
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wpsimp wp: updateReply_iflive'_weak updateReply_valid_objs'
                    updateReply_list_refs_of_replies'_inv updateReply_valid_replies'
           simp: invs'_def valid_state'_def valid_pspace'_def valid_reply'_def
          split: option.split_asm)
   by (auto simp: obj_at'_def projectKOs opt_map_def)

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
  done

lemma bindScReply_valid_replies'[wp]:
  "\<lbrace>\<lambda>s. valid_replies' s \<and> pspace_distinct' s \<and> pspace_aligned' s
        \<and> (\<exists>tptr. replyTCBs_of s replyPtr = Some tptr
                  \<and> st_tcb_at' ((=) (BlockedOnReply (Some replyPtr)))
                               tptr s)\<rbrace>
   bindScReply scPtr replyPtr
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  apply (solves wp | simp (no_asm_use) add: bindScReply_def split del: if_split cong: conj_cong |
         wp hoare_when_wp haskell_assert_wp hoare_vcg_if_lift2 hoare_vcg_all_lift
            hoare_vcg_disj_lift hoare_vcg_imp_lift' hoare_vcg_ex_lift
            updateReply_valid_replies'_bound updateReply_obj_at')+
  apply (clarsimp simp: sym_refs_asrt_def)
  apply (intro conjI impI allI; clarsimp?)
      apply (drule valid_replies'_sc_asrtD)
       apply (clarsimp, rule_tac x=scPtr in exI)
       apply (erule (2) sym_refs_scReplies[THEN sym_heapD1])
       apply (clarsimp simp: obj_at'_def projectKOs opt_map_def)
      apply ((erule impCE)?; fastforce simp: obj_at'_def projectKOs)+
  done

crunches bindScReply
  for valid_queues[wp]: valid_queues
  and valid_queues'[wp]: valid_queues'
  and valid_release_queue[wp]: valid_release_queue
  (simp: crunch_simps)

lemma bindScReply_sch_act_wf[wp]:
  "bindScReply scPtr replyPtr \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding bindScReply_def
  by (wpsimp wp: sts_sch_act' hoare_vcg_all_lift hoare_vcg_if_lift hoare_drop_imps)

lemma bindsym_heap_scReplies_list_refs_of_replies':
  "\<lbrace>\<lambda>s. sym_refs (list_refs_of_replies' s)
      \<and> \<not> is_reply_linked replyPtr s \<and> replySCs_of s replyPtr = None
      \<and> (\<forall>oldReplyPtr. (scReplies_of s) scPtr = Some oldReplyPtr
                          \<longrightarrow> replySCs_of s oldReplyPtr = Some scPtr)\<rbrace>
   bindScReply scPtr replyPtr
   \<lbrace>\<lambda>_ s. sym_refs (list_refs_of_replies' s)\<rbrace>"
  supply if_split [split del]
  unfolding bindScReply_def
  apply (wpsimp wp: updateReply_list_refs_of_replies' updateReply_obj_at'
                    hoare_vcg_all_lift hoare_vcg_imp_lift')
  by (auto simp: list_refs_of_replies'_def list_refs_of_reply'_def
                 opt_map_Some_def obj_at'_def projectKO_eq
           elim: delta_sym_refs split: if_splits)

lemma bindScReply_if_live_then_nonz_cap':
  "\<lbrace>if_live_then_nonz_cap'
    and ex_nonz_cap_to' scPtr and ex_nonz_cap_to' replyPtr
    and (\<lambda>s. \<forall>rp. (scReplies_of s) scPtr = Some rp
                    \<longrightarrow> replySCs_of s rp = Some scPtr)\<rbrace>
   bindScReply scPtr replyPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding bindScReply_def
  apply (simp (no_asm_use) split del: if_split
         | wp hoare_vcg_all_lift hoare_vcg_imp_lift'
              hoare_vcg_if_lift updateReply_iflive'_weak
         | rule threadGet_wp)+
  apply clarsimp
  apply (erule if_live_then_nonz_capE')
   apply (clarsimp simp: ko_wp_at'_def obj_at'_def live_reply'_def opt_map_def projectKOs)
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
   updateReply rptr (replyNext_update (\<lambda>_. None))
   \<lbrace>\<lambda>_ s. sym_refs (list_refs_of_replies' s)\<rbrace>"
  apply (wpsimp wp: updateReply_list_refs_of_replies')
  apply (erule delta_sym_refs)
   apply (auto simp: list_refs_of_reply'_def map_set_def
                     opt_map_def obj_at'_def projectKOs
              split: option.splits if_splits)
  done

lemma updateReply_replyNext_None_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> replySCs_of s rptr \<noteq> None\<rbrace>
   updateReply rptr (replyNext_update (\<lambda>_. None))
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp only: invs'_def valid_state'_def valid_pspace'_def)
  apply (wpsimp wp: updateReply_valid_objs' updateReply_iflive')
  apply (clarsimp simp: obj_at'_def projectKOs valid_reply'_def live_reply'_def
                  dest: pspace_alignedD' pspace_distinctD')
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

(* sym_refs and prev/next; scReply and replySC *)

lemma sym_refs_replySCs_of_None:
  "\<lbrakk>sym_refs (state_refs_of' s'); pspace_aligned' s'; pspace_distinct' s';
   replySCs_of s' rp = None\<rbrakk>
  \<Longrightarrow> \<forall>scp. scs_of' s' scp \<noteq> None \<longrightarrow> scReplies_of s' scp \<noteq> Some rp"
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (drule_tac tp=SCReply and y=rp and x=scp in sym_refsD[rotated])
   apply (force simp: state_refs_of'_def dest: pspace_alignedD' pspace_distinctD')
  by (clarsimp simp: state_refs_of'_def refs_of_rev' opt_map_red
              split: option.split_asm if_split_asm)

(* cleanReply *)
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
  apply (clarsimp simp: obj_at'_def ps_clear_upd objBits_simps' projectKOs)
  done

(* sc_with_reply/sc_with_reply' *)

lemma valid_objs'_replyPrevs_of_reply_at':
  "\<lbrakk> valid_objs' s'; replyPrevs_of s' rp = Some rp'\<rbrakk> \<Longrightarrow> reply_at' rp' s'"
  apply clarsimp
  apply (erule (1) valid_objsE')
  by (clarsimp simp: valid_obj'_def valid_reply'_def valid_bound_obj'_def obj_at'_def projectKOs)

lemma valid_objs'_replyNexts_of_reply_at':
  "\<lbrakk> valid_objs' s'; replyNexts_of s' rp = Some rp'\<rbrakk> \<Longrightarrow> reply_at' rp' s'"
  apply clarsimp
  apply (erule (1) valid_objsE')
  by (clarsimp simp: valid_obj'_def valid_reply'_def valid_bound_obj'_def obj_at'_def projectKOs)

(** sc_with_reply and sc_replies_relations : crossing information **)

(* modified version of sc_replies_relation_prevs_list in StateRelation.thy;
   updates only the abstract sc_relies; useful for the following few lemmas *)
lemma sc_replies_relation_prevs_list':
  "\<lbrakk> sc_replies_relation s s';
     kheap s scp = Some (kernel_object.SchedContext sc n)\<rbrakk>
    \<Longrightarrow> heap_ls (replyPrevs_of s') (scReplies_of s' scp) (sc_replies sc)"
  apply (clarsimp simp: sc_replies_relation_def sc_replies_of_scs_def scs_of_kh_def map_project_def)
  apply (clarsimp simp: sc_of_def opt_map_red)
  done

lemma sc_replies_relation_sc_with_reply_cross_eq_pred:
  "\<lbrakk> sc_replies_relation s s'; pspace_relation (kheap s) (ksPSpace s')\<rbrakk> \<Longrightarrow>
   (\<exists>sc n. kheap s scp = Some (kernel_object.SchedContext sc n) \<and> rp \<in> set (sc_replies sc))
    = (\<exists>xs. heap_ls (replyPrevs_of s') (scReplies_of s' scp) xs \<and> rp \<in> set xs)"
  apply (rule iffI; clarsimp)
   apply (rule_tac x="the (sc_replies_of2 s scp)" in exI)
  apply (clarsimp simp: sc_replies_relation_def sc_replies_of_scs_def scs_of_kh_def map_project_def)
  apply (drule_tac x=scp and y="sc_replies sc" in spec2)
  apply (clarsimp simp: sc_of_def opt_map_def projectKO_opt_sc split: option.splits)
  apply (case_tac "scReplies_of s' scp", simp)
  apply (rename_tac p)
  apply (drule pspace_relation_sc_at[where scp=scp])
   apply (clarsimp simp: projectKOs opt_map_red)
  apply (clarsimp simp: obj_at_simps is_sc_obj opt_map_red)
  apply (drule (1) sc_replies_relation_prevs_list', simp add: opt_map_red)
  apply (drule (1) heap_ls_unique, simp)
  done

(* crossing equality for sc_with_reply *)
lemma sc_replies_relation_sc_with_reply_cross_eq:
  "\<lbrakk> sc_replies_relation s s'; pspace_relation (kheap s) (ksPSpace s') \<rbrakk>
   \<Longrightarrow> sc_with_reply rp s = sc_with_reply' rp s'"
  unfolding sc_with_reply_def sc_with_reply'_def
  using sc_replies_relation_sc_with_reply_cross_eq_pred
  by simp

lemma sc_replies_relation_sc_with_reply_heap_path:
  "\<lbrakk>sc_replies_relation s s'; sc_with_reply rp s = Some scp\<rbrakk>
  \<Longrightarrow> heap_ls  (replyPrevs_of s') (scReplies_of s' scp) (the (sc_replies_of s scp))
    \<and> rp \<in> set (the (sc_replies_of s scp))"
  apply (clarsimp simp: sc_replies_relation_def dest!: sc_with_reply_SomeD)
  apply (drule_tac x=scp and y="sc_replies sc" in spec2)
  apply (clarsimp simp: vs_heap_simps)
  apply (frule (1) heap_path_takeWhile_lookup_next)
  by (metis (mono_tags) option.sel sc_replies.Some)

lemma next_reply_in_sc_replies:
  "\<lbrakk>sc_replies_relation s s'; sc_with_reply rp s = Some scp; sym_refs (list_refs_of_replies' s');
    sym_refs (state_refs_of' s'); replyNexts_of s' rp = Some nrp;
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
  \<Longrightarrow> \<exists>xs ys. sc_replies_of s scp = Some (xs @ nrp # rp # ys)"
  supply opt_mapE[rule del]
  apply (frule (1) sc_replies_relation_sc_with_reply_heap_path)
  apply (prop_tac "replyPrevs_of s' nrp = Some rp")
   apply (simp add: sym_refs_replyNext_replyPrev_sym[symmetric])
  apply (drule sc_with_reply_SomeD, clarsimp)
  apply (prop_tac "the (sc_replies_of s scp) = sc_replies sc")
  using heap_ls_unique sc_replies_relation_prevs_list' apply blast
  apply simp
  apply (frule (3) heap_ls_prev_cases[OF _ _ _ reply_sym_heap_Prev_Next])
  apply (drule (2) sym_refs_replySCs_of_None)
   apply (rule replyNexts_Some_replySCs_None[where rp=rp], simp)
  apply (clarsimp simp: vs_heap_simps)
  apply (drule (1) heap_ls_next_takeWhile_append[rotated -1])
  apply (meson omonadE(1))
  by (force dest!: in_list_decompose_takeWhile)

lemma prev_reply_in_sc_replies:
  "\<lbrakk>sc_replies_relation s s'; sc_with_reply rp s = Some scp; sym_refs (list_refs_of_replies' s');
    sym_refs (state_refs_of' s'); replyPrevs_of s' rp = Some nrp;
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
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
  apply (frule (2) sym_refs_replySCs_of_None[where rp=nrp])
   apply (rule replyNexts_Some_replySCs_None, simp)
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
  " \<lbrakk>sc_replies_relation s s'; valid_objs s;
     valid_objs' s'; pspace_relation (kheap s) (ksPSpace s');
     valid_replies s; pspace_distinct s; pspace_aligned s;
     sym_refs (state_refs_of' s');
     sym_refs (list_refs_of_replies' s');
     replyNexts_of s' rp = Some nxt_rp;
     sc_with_reply rp s = Some scp\<rbrakk>
    \<Longrightarrow> sc_with_reply nxt_rp s = Some scp"
  supply opt_mapE[rule del]
  apply (subgoal_tac "sc_with_reply' nxt_rp s' = Some scp")
   apply (fastforce simp: sc_replies_relation_sc_with_reply_cross_eq)
  apply (frule (1) sc_with_reply_Some_sc_at)
  apply (frule (1) sc_with_reply_Some_reply_at)
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
  apply (prop_tac "\<exists>xs. heap_ls (replyPrevs_of s') (scReplies_of s' scp) xs \<and> nxt_rp \<in> set xs")
   apply (rule_tac x="sc_replies sc" in exI)
   apply (frule (2) heap_ls_prev_cases)
    apply (erule reply_sym_heap_Prev_Next)
   apply (erule disjE)
    apply (frule (2) sym_refs_scReplies, clarsimp simp: sym_heap_def)
    apply (frule replySCs_Some_replyNexts_None[OF option.discI])
    apply (drule (1) sym_refs_replyNext_None, clarsimp)
   apply clarsimp
  apply (clarsimp simp: sc_with_reply'_def the_pred_option_def the_equality split: if_split_asm)
  apply (rule conjI)
   apply blast
  by (meson heap_ls_next_in_list)

lemma sc_with_reply_replyPrev_None:
  "\<lbrakk>sc_with_reply rp s = None; sc_replies_relation s s'; valid_objs' s';
    pspace_relation (kheap s) (ksPSpace s');
    pspace_distinct s; pspace_aligned s;
    sym_refs (state_refs_of' s'); sym_refs (list_refs_of_replies' s');
    replyPrevs_of s' rp = Some prv_rp\<rbrakk>
  \<Longrightarrow> sc_with_reply prv_rp s = None"
  supply opt_mapE[rule del]
  apply (subgoal_tac "sc_with_reply' prv_rp s' = None")
   apply (fastforce simp: sc_replies_relation_sc_with_reply_cross_eq)
  apply (prop_tac "reply_at rp s")
   apply (clarsimp simp: projectKOs elim!: opt_mapE)
   apply (erule (1) pspace_dom_relatedE)
   apply (erule (1) obj_relation_cutsE)
         apply ((clarsimp simp: other_obj_relation_def is_reply obj_at_def
                         split: Structures_A.kernel_object.split_asm if_split_asm
                                ARM_A.arch_kernel_obj.split_asm)+)[7]
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
  apply (frule (2) heap_ls_prev_cases)
   apply (erule reply_sym_heap_Prev_Next)
  apply (erule disjE)
   apply (frule (2) sym_refs_scReplies, clarsimp simp: sym_heap_def)
   apply (frule replySCs_Some_replyNexts_None[OF option.discI])
   apply (drule (1) sym_refs_replyNext_None, clarsimp)
  by (meson heap_ls_prev_not_in)

lemma sc_with_reply_replyNext_None:
  "\<lbrakk>sc_with_reply rp s = None; sc_replies_relation s s'; valid_objs' s';
    pspace_relation (kheap s) (ksPSpace s'); valid_replies s;
    pspace_distinct s; pspace_aligned s;
    sym_refs (state_refs_of' s'); sym_refs (list_refs_of_replies' s');
    replyNexts_of s' rp = Some nxt_rp\<rbrakk>
   \<Longrightarrow> sc_with_reply nxt_rp s = None"
  supply opt_mapE[rule del]
  apply (prop_tac "reply_at rp s")
   apply (clarsimp simp: projectKOs elim!: opt_mapE)
   apply (erule (1) pspace_dom_relatedE)
   apply (erule (1) obj_relation_cutsE)
         apply ((clarsimp simp: other_obj_relation_def is_reply obj_at_def
                         split: Structures_A.kernel_object.split_asm if_split_asm
                                ARM_A.arch_kernel_obj.split_asm)+)[7]
  apply (prop_tac "pspace_aligned' s' \<and> pspace_distinct' s'")
   apply (fastforce elim!: pspace_distinct_cross pspace_aligned_cross)
  apply (rule ccontr)
  apply (drule not_Some_eq[THEN iffD2])
  apply (drule not_None_eq[THEN iffD1])
  apply (drule not_ex[THEN iffD2])
  apply (erule FalseI)
  apply clarsimp
  apply (rename_tac scp)
  apply (rule_tac x=scp in exI)
  apply (frule (1) sym_refs_replyNext_replyPrev_sym[THEN iffD1])
  apply (frule (6) prev_reply_in_sc_replies)
  apply (drule sc_with_reply_SomeD)
  apply (clarsimp simp: vs_heap_simps)
  apply (rename_tac sc n)
  apply (clarsimp simp: sc_with_reply_def' the_pred_option_def
                 split: if_split_asm)
  apply (simp add: conj_commute)
  apply (rule context_conjI)
   apply (drule valid_replies_sc_replies_unique[where r=rp])
    apply (fastforce simp: sc_replies_sc_at_def obj_at_def)
   apply simp
  apply (clarsimp simp: the_equality)
  apply (drule_tac x=x and y=scp in spec2)
  apply (clarsimp simp: sc_replies_sc_at_def obj_at_def)
  done

(** end : sc_with_reply' **)

(* sr_inv lemmas for reply_remove_tcb_corres *)

lemma pspace_relation_reply_at:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "ksPSpace s' p = Some (KOReply reply')"
  shows "reply_at p s" using assms
  apply -
  apply (erule (1) pspace_dom_relatedE)
  apply (erule (1) obj_relation_cutsE)
  apply (clarsimp simp: other_obj_relation_def is_reply obj_at_def
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        ARM_A.arch_kernel_obj.split_asm)+
  done

lemma next_is_not_head[simp]:
  "isNext x \<Longrightarrow> \<not> isHead x"
  by (clarsimp simp: isNext_def isHead_def split: option.splits reply_next.splits)

lemma sc_replies_relation_sc_with_reply_None:
  "\<lbrakk>sc_replies_relation s s'; reply_at rp s; replies_of' s' rp \<noteq> None;
    sc_with_reply rp s = None; valid_replies s\<rbrakk>
     \<Longrightarrow> sc_replies_relation s (s'\<lparr>ksPSpace := (ksPSpace s')(rp \<mapsto> KOReply r)\<rparr>)"
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
                 split: if_split_asm option.split_asm dest!: readObject_misc_ko_at')
  apply (rename_tac reply')
  apply (prop_tac "ko_at' reply' rp s'")
   apply (clarsimp simp: obj_at'_def objBits_simps' projectKOs)
  apply (frule (1) pspace_relation_reply_at[OF state_relation_pspace_relation])
  apply (clarsimp simp: obj_at_def is_reply)
  apply (rename_tac reply)
  apply (clarsimp simp: state_relation_def)
  apply (rule conjI)
   apply (frule (1) pspace_relation_absD)
   apply (fastforce elim!: pspace_relation_reply_update_conc_only simp: obj_at'_def )
  apply (clarsimp simp: caps_of_state_after_update cte_wp_at_after_update
                        swp_def fun_upd_def obj_at_def map_to_ctes_upd_other
              simp del: fun_upd_def)
  done

lemma updateReply_sr_inv_prev:
  "sr_inv ((\<lambda>s. sc_with_reply rp s = None) and valid_replies)
           (reply_at' rp) (updateReply rp (replyPrev_update (\<lambda>_. Nothing)))"
  apply (rule updateReply_sr_inv)
   apply (clarsimp simp: reply_relation_def)
  by (fastforce elim!: sc_replies_relation_sc_with_reply_None
                          [where r="replyPrev_update Map.empty reply'" for reply', simplified]
                 simp: opt_map_red obj_at'_def projectKOs)

lemma updateReply_sr_inv_next:
  "sr_inv (P and (\<lambda>s. sc_with_reply rp s = None) and valid_replies
           and (\<lambda>s. sym_refs (state_refs_of s)))
           P' (updateReply rp (replyNext_update (\<lambda>_. Nothing)))"
  unfolding updateReply_def sr_inv_def
  apply (clarsimp simp: setReply_def getReply_def getObject_def setObject_def projectKOs
                        updateObject_default_def loadObject_default_def split_def
                        in_monad return_def fail_def objBits_simps' in_magnitude_check
                 split: if_split_asm option.split_asm dest!: readObject_misc_ko_at')
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
    apply (fastforce elim!: sc_replies_relation_sc_with_reply_None
                              [where r="replyPrev_update Map.empty reply'" for reply', simplified]
                     simp: opt_map_red obj_at'_def projectKOs)
   apply wpsimp
  apply (clarsimp intro!: updateReply_sr_inv_next[simplified])
  done

(* replyRemoveTCB_corres specific wp rules *)

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
    update_sched_context scp (sc_replies_update (takeWhile ((\<noteq>) rp)))
   \<lbrace>\<lambda>rv s. sc_with_reply rp s = None\<rbrace>"
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

(* FIXME RT: maybe move *)
lemma update_sched_context_not_tcb_at[wp]:
  "update_sched_context ref f \<lbrace>\<lambda>s. P (ko_at (TCB tcb) t s)\<rbrace>"
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
(* end: maybe move *)

lemma sc_replies_update_takeWhile_middle_sym_refs:
  "\<lbrakk> hd (sc_replies sc) \<noteq> rp; rp \<in> set (sc_replies sc) \<rbrakk> \<Longrightarrow>
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
  by (clarsimp simp: obj_at'_def projectKOs ps_clear_upd)

lemma update_replyPrev_replyNexts_inv[wp]:
  "updateReply rp (replyPrev_update prev) \<lbrace>\<lambda>s. P (replyNexts_of s)\<rbrace>"
  unfolding updateReply_def supply fun_upd_apply[simp del]
  apply wpsimp
  by (metis ko_at'_replies_of' map_upd_triv opt_map_upd_Some)

(* replyRemoveTCB_corres specific corres rules *)

lemma setSchedContext_scReply_update_None_corres:
  "corres dc ((\<lambda>s. (sc_replies_of s |> hd_opt) ptr = Some rp) and valid_objs and pspace_aligned and pspace_distinct)
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
          apply (rule_tac P="(\<lambda>s. kheap s ptr = Some (kernel_object.SchedContext sc (objBits sc'
                                                                                    - minSchedContextBits)))
                              and K (rp = hd (sc_replies sc))"
                      and P'="ko_at' sc' ptr"  in corres_inst)
          apply (rule corres_gen_asm')
          apply (rule corres_guard_imp)
            apply (rule_tac sc=sc and sc'=sc' in setSchedContext_update_corres; simp?)
             apply (clarsimp simp: sc_relation_def objBits_simps)+
         apply (wpsimp wp: get_sched_context_exs_valid simp: is_sc_obj_def obj_at_def)
          apply (rename_tac ko; case_tac ko; clarsimp)
         apply simp
        apply (wpsimp simp: obj_at_def is_sc_obj_def vs_heap_simps)
       apply (wpsimp wp: get_sched_context_no_fail)
      apply (clarsimp simp: obj_at_def is_sc_obj_def)
     apply simp
    apply wpsimp+
  done

lemma replyPrevNext_update_commute:
  "replyPrev_update f (replyNext_update g reply)
   = replyNext_update g (replyPrev_update f reply)"
  by (cases reply; clarsimp)

lemma updateReply_Prev_Next_rewrite:
  "monadic_rewrite False True (reply_at' rp)
    (do y <- updateReply rp (replyPrev_update f);
         updateReply rp (replyNext_update g)
     od)
    (do y <- updateReply rp (replyNext_update g);
         updateReply rp (replyPrev_update f)
     od)"
  apply (clarsimp simp: monadic_rewrite_def)
  apply (rule monad_state_eqI)
    apply (find_goal \<open>match conclusion in "_ = _" \<Rightarrow> -\<close>)
    subgoal
    apply (insert no_fail_updateReply, drule_tac x=rp and y="replyPrev_update f" in meta_spec2)
    apply (insert no_fail_updateReply, drule_tac x=rp and y="replyNext_update g" in meta_spec2)
    apply (rule; clarsimp simp: in_monad no_fail_def snd_bind split_def)
     apply (drule (1) use_valid[OF _ updateReply.typ_at_lifts'(5)], fastforce)+
    done
   apply (all \<open>clarsimp simp: updateReply_def getReply_def setReply_def getObject_def2
                              obj_at'_def projectKOs updateObject_default_def setObject_def
                              loadObject_default_def2[simplified] ARM_H.fromPPtr_def
                              split_def in_monad in_magnitude_check' objBits_simps'\<close>)
   apply (fastforce simp add: fun_upd_def replyPrevNext_update_commute)+
  done

lemma reply_sc_update_sc_with_reply_None:
  "set_reply_obj_ref reply_sc_update rp None \<lbrace>\<lambda>s. sc_with_reply rp s = None\<rbrace>"
  apply (wpsimp wp: update_sk_obj_ref_wp)
  apply (drule sc_with_reply_NoneD)
  apply (simp add: sc_with_reply_def sc_replies_sc_at_def obj_at_def)
  apply (rule the_pred_option_None)
  by (metis Structures_A.kernel_object.simps(45) option.simps(1))

lemma reply_sc_update_sc_with_reply_None_exs_valid:
  "\<lbrakk> reply_at rp s; sc_with_reply rp s = None; valid_replies s;
     sym_refs (state_refs_of s) \<rbrakk> \<Longrightarrow>
   \<lbrace>(=) s\<rbrace> set_reply_obj_ref reply_sc_update rp None \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  apply (drule (3) sc_with_reply_None_reply_sc_reply_at)
  apply (clarsimp simp: reply_sc_reply_at_def obj_at_def is_reply update_sk_obj_ref_def)
  apply (simp add: exs_valid_def set_simple_ko_def get_object_def2 exec_gets bind_assoc
                   set_object_def exec_get put_def return_def in_monad split_def bind_def
                   get_simple_ko_def partial_inv_inj_Some)
  apply (simp add: gets_def exec_get return_def partial_inv_def)
  apply (simp add: get_def)
  apply (drule sym[where s=None])
  by (cases s; auto)

(* cleanReply corres when rp is not in a reply stack *)
lemma cleanReply_sc_with_reply_None_corres':
  "corres dc (reply_at rp and pspace_aligned and pspace_distinct
    and valid_replies and (\<lambda>s. sym_refs (state_refs_of s)) and (\<lambda>s. sc_with_reply rp s = None))
    \<top>
     (set_reply_obj_ref reply_sc_update rp None)
     (cleanReply rp)"
  apply (rule_tac Q="reply_at' rp" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD reply_at_cross)
  apply (rule corres_guard_imp)
  apply (rule corres_noop_sr2[OF reply_sc_update_sc_with_reply_None_exs_valid
                                 cleanReply_sr_inv[where P="reply_at rp" and P'="reply_at' rp"]])
  by wpsimp+

(* cleanReply corres version 2:
   we don't want sym_refs in the preconditions for replyRemoveTCB_corres
   we can achieve that by unfolding cleanReply and not using cleanReply_sr_inv *)
lemma cleanReply_sc_with_reply_None_corres:
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
      apply (rule corres_split[OF updateReply_replyNext_not_head_corres])
         apply (simp add: isHead_def)
        apply (rule_tac P="reply_at rp and valid_replies and (\<lambda>s. sc_with_reply rp s = None)"
                    and P'="reply_at' rp" in corres_noop_sr)
          apply (rule sr_inv_imp)
            apply (rule updateReply_sr_inv_prev[simplified])
           apply (clarsimp simp: reply_relation_def)
          apply simp
         apply (wpsimp wp: reply_sc_update_sc_with_reply_None simp: isHead_def)+
     apply simp+
  done

(* corres between update_sched_context and updateReply *)
lemma updateReply_replyPrev_takeWhile_middle_corres:
  assumes
    "rp \<in> set (sc_replies sc)"
    "hd (sc_replies sc) \<noteq> rp"
  shows
  "corres dc
      (valid_objs and pspace_aligned and pspace_distinct and valid_replies
        and  (\<lambda>s. sym_refs (state_refs_of s))
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
    (* crossing information *)
    apply (rule_tac Q="reply_at' rp and reply_at' nrp and sc_at' scp
                      and pspace_distinct' and pspace_aligned'
                      and  (\<lambda>s. sym_refs (state_refs_of' s))
                      and (\<lambda>s'. sc_with_reply' rp s' = Some scp)" in corres_cross_add_guard)
     apply clarsimp
     apply (prop_tac "reply_at' rp s'")
      apply (fastforce dest!: state_relationD intro!: reply_at_cross
                        simp: reply_sc_reply_at_def obj_at_def is_reply)
     apply (intro conjI, simp)
           apply (fastforce dest!: valid_objs'_replyNexts_of_reply_at')
          apply (fastforce dest!: state_relationD sc_at_cross elim: valid_objs_valid_sched_context_size
                            simp: obj_at_def is_sc_obj)
         apply (fastforce dest!: state_relationD pspace_distinct_cross)
        apply (fastforce dest!: state_relationD pspace_aligned_cross)
      apply (fastforce dest!: state_refs_of_cross_eq)
     apply (fastforce dest: state_relationD simp: sc_replies_relation_sc_with_reply_cross_eq)
    (* corres proof *)
    apply (clarsimp simp: corres_underlying_def)
    apply (rename_tac s s')
    apply (rule conjI)
     apply (clarsimp simp: update_sched_context_def updateReply_def getReply_def
                           setReply_def getObject_def2 setObject_def in_monad ARM_H.fromPPtr_def
                           get_object_def2 set_object_def bind_assoc loadObject_default_def2[simplified]
                           scBits_simps split_def lookupAround2_known1 exec_gets a_type_def
                           obj_at'_def projectKOs reply_sc_reply_at_def obj_at_def
                           updateObject_default_def in_magnitude_check objBits_simps')
     apply (clarsimp simp: get_def put_def bind_def)
     apply (rename_tac reply' sc' nextr)
     apply (prop_tac "reply_at' nrp s'")
      apply (clarsimp simp: obj_at'_def projectKOs objBits_simps')
     apply (prop_tac "reply_at nrp s")
      apply (drule (1) valid_sched_context_objsI)
      apply (clarsimp simp: valid_sched_context_def)
      apply (frule_tac nrp=nrp in next_reply_in_sc_replies[where rp=rp, OF state_relation_sc_replies_relation])
            apply (simp add: obj_at'_def projectKOs objBits_simps' opt_map_red)+
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
      apply (rule ballI, drule (1) bspec)
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
      apply (clarsimp simp: projectKO_opt_sc opt_map_red)
      apply (clarsimp simp: sc_replies_relation_def sc_replies_of_scs_def map_project_def scs_of_kh_def)
      apply (drule_tac x=p in spec)
      apply (intro conjI impI allI)
      (* p =  scp *)
       apply (clarsimp simp: opt_map_red sc_of_def)
       apply (prop_tac "replyPrevs_of s' nrp = Some rp")
        apply (simp add: sym_refs_replyNext_replyPrev_sym[symmetric])
        apply (clarsimp simp: opt_map_red)
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
      apply (clarsimp simp: opt_map_red sc_of_def)
      apply (prop_tac "replyPrevs_of s' nrp = Some rp")
       apply (simp add: sym_refs_replyNext_replyPrev_sym[symmetric])
       apply (clarsimp simp: opt_map_red)
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
  by (erule no_failD[OF no_fail_updateReply])
qed

(* end : related corres rules *)

end
