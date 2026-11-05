(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Reply_R
imports ArchSchedule_R
begin

defs replyUnlink_assertion_def:
  "replyUnlink_assertion
    \<equiv> \<lambda>replyPtr state s. state = BlockedOnReply (Some replyPtr)
                          \<or> (\<exists>ep d. state = BlockedOnReceive ep d (Some replyPtr))"

crunch updateReply
  for pred_tcb_at'[wp]: "\<lambda>s. P (pred_tcb_at' proj test t s)"
  and obj_at'_tcb[wp]: "\<lambda>s. Q (obj_at' (P :: tcb \<Rightarrow> bool) t s)"
  and sc_obj_at'[wp]: "\<lambda>s. Q (obj_at' (P :: sched_context \<Rightarrow> bool) scp s)"

crunch updateReply, updateSchedContext
  for ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"
  and gsUserPages[wp]: "\<lambda>s. P (gsUserPages s)"
  and gsCNodes[wp]: "\<lambda>s. P (gsCNodes s)"
  and ksArchState[wp]: "\<lambda>s. P (ksArchState s)"
  and ksIdleSC[wp]: "\<lambda>s. P (ksIdleSC s)"
  and ksWorkUnitsCompleted[wp]: "\<lambda>s. P (ksWorkUnitsCompleted s)"
  and ksDomainTime[wp]: "\<lambda>s. P (ksDomainTime s)"
  and ksConsumedTime[wp]: "\<lambda>s. P (ksConsumedTime s)"
  and ksCurTime[wp]: "\<lambda>s. P (ksCurTime s)"
  and ksCurSc[wp]: "\<lambda>s. P (ksCurSc s)"
  and ksReprogramTimer[wp]: "\<lambda>s. P (ksReprogramTimer s)"
  and pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and pspace_bounded'[wp]: pspace_bounded'
  and no_0_obj'[wp]: "no_0_obj'"
  and valid_mdb'[wp]: "valid_mdb'"

global_interpretation updateReply: gen_typ_at_all_props' "updateReply p f"
  by typ_at_props'

lemma replyUnlink_st_tcb_at':
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> (t' = t \<longrightarrow> P (P' Inactive)) \<and> (t' \<noteq> t \<longrightarrow> P (st_tcb_at' P' t' s))\<rbrace>
    replyUnlink r t
   \<lbrace>\<lambda>rv s. P (st_tcb_at' P' t' s)\<rbrace>"
  unfolding replyUnlink_def
  by (wpsimp wp: sts_st_tcb_at'_cases_strong gts_wp' hoare_vcg_imp_lift
           cong: conj_cong split: if_split_asm)

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

crunch breakReplyChainAt
  for pred_tcb_at'[wp]: "\<lambda>s. Q (pred_tcb_at' proj P t s)"
  (simp: crunch_simps wp: crunch_wps)

lemma replyRemove_st_tcb_at'_Inactive:
  "\<lbrace>\<top>\<rbrace> replyRemove replyPtr tcbPtr \<lbrace>\<lambda>_. st_tcb_at' ((=) Inactive) tcbPtr\<rbrace>"
  apply (clarsimp simp: replyRemove_def replyPop_def)
  apply (wpsimp wp: replyUnlink_st_tcb_at' threadGet_wp hoare_vcg_if_lift)
  done

lemma replyRemove_st_tcb_at'[wp]:
  "P Inactive \<Longrightarrow> \<lbrace>\<top>\<rbrace> replyRemove r t \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (rule replyRemove_st_tcb_at'_Inactive)
  apply (clarsimp elim!: pred_tcb'_weakenE)
  done

lemma updateReply_field_inv:
  "(\<And>reply. f (upd reply) = f reply) \<Longrightarrow> updateReply replyPtr upd \<lbrace>\<lambda>s. P (replies_of' s |> f)\<rbrace>"
  apply (wpsimp wp: updateReply_wp)
  apply (fastforce elim!: rsubst[where P=P] simp: opt_map_def obj_at'_def)
  done

crunch replyUnlink
  for replyNexts_of[wp]: "\<lambda>s. P (replyNexts_of s)"
  and replyPrevs_of[wp]: "\<lambda>s. P (replyPrevs_of s)"
  and ex_nonz_cap_to'[wp]: "(\<lambda>s. ex_nonz_cap_to' t s)"
  and valid_irq_handlers'[wp]: valid_irq_handlers'
  and valid_irq_states'[wp]: valid_irq_states'
  and irqs_masked'[wp]: irqs_masked'
  and pspace_domain_valid[wp]: pspace_domain_valid
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and ksArchState[wp]: "\<lambda>s. P (ksArchState s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and sch_act_not[wp]: "sch_act_not t"
  and aligned'[wp]: pspace_aligned'
  and distinct'[wp]: pspace_distinct'
  and bounded'[wp]: pspace_bounded'
  and pspace_canonical'[wp]: pspace_canonical'
  and no_0_obj'[wp]: "no_0_obj'"
  and valid_mdb'[wp]: "valid_mdb'"
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  (wp: crunch_wps updateReply_field_inv simp: crunch_simps)

lemma updateReply_valid_objs':
  "\<lbrace>valid_objs' and (\<lambda>s. \<forall>r. valid_reply' r s \<longrightarrow> valid_reply' (upd r) s)\<rbrace>
   updateReply rptr upd
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding updateReply_def
  apply wpsimp
  apply (frule(1) reply_ko_at_valid_objs_valid_reply')
  apply clarsimp
  done

lemma replyUnlink_valid_objs'[wp]:
  "replyUnlink rptr tptr \<lbrace>valid_objs'\<rbrace>"
  unfolding replyUnlink_def
  apply (wpsimp wp: updateReply_valid_objs' gts_wp')
  apply (clarsimp simp: valid_reply'_def)
  done

lemma setReply_valid_replies':
  "\<lbrace>\<lambda>s. valid_replies' s
        \<and> (replyNext reply \<noteq> None \<or> replyPrev reply \<noteq> None \<longrightarrow>
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
            (replyNext (f reply) \<noteq> None \<or> replyPrev (f reply) \<noteq> None \<longrightarrow>
              (\<exists>tptr. replyTCB (f reply) = Some tptr
                      \<and> st_tcb_at'
                        ((=) (Structures_H.thread_state.BlockedOnReply (Some rptr)))
                        tptr s)))\<rbrace>
   updateReply rptr f
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  unfolding updateReply_def
  by (wpsimp wp: setReply_valid_replies')

lemma replyUnlink_valid_replies'[wp]:
  "\<lbrace>\<lambda>s. replyTCBs_of s rptr = Some tptr \<longrightarrow> valid_replies' s \<and> \<not> is_reply_linked rptr s\<rbrace>
   replyUnlink rptr tptr
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  unfolding replyUnlink_def
  apply (wpsimp wp: updateReply_valid_replies' sts'_valid_replies'
                    updateReply_field_inv hoare_vcg_all_lift hoare_vcg_imp_lift' gts_wp')
  apply normalise_obj_at'
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def replyUnlink_assertion_def)
  apply (auto simp: opt_map_def split: option.splits)
  done

lemma replyUnlink_valid_pspace'[wp]:
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> (replyTCBs_of s rptr = Some tptr \<longrightarrow> \<not> is_reply_linked rptr s)\<rbrace>
   replyUnlink rptr tptr
   \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  by (wpsimp simp: valid_pspace'_def)

lemma setReply_valid_tcbs'[wp]:
  "setReply rp new  \<lbrace>valid_tcbs'\<rbrace>"
  unfolding valid_tcbs'_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' set_reply'.setObject_wp
           simp: setReply_def)

crunch replyRemoveTCB
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and aligned'[wp]: pspace_aligned'
  and distinct'[wp]: pspace_distinct'
  and bounded'[wp]: pspace_bounded'
  and pspace_canonical'[wp]: pspace_canonical'
  and no_0_obj'[wp]: "no_0_obj'"
  and it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  and ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and ksMachineState[wp]: "\<lambda>s. P (ksMachineState s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and ksDomScheduleStart[wp]: "\<lambda>s. P (ksDomScheduleStart s)"
  and sch_act_simple[wp]: "sch_act_simple"
  and untyped_ranges_zero'[wp]: "untyped_ranges_zero'"
  and ifunsafe'[wp]: "if_unsafe_then_cap'"
  and global_refs'[wp]: "valid_global_refs'"
  and valid_arch'[wp]: "valid_arch_state'"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n T p s)"
  and vms'[wp]: "valid_machine_state'"
  and pspace_domain_valid[wp]: pspace_domain_valid
  and valid_mdb'[wp]: valid_mdb'
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  and tcbInReleaseQueue[wp]: "\<lambda>s. P (tcbInReleaseQueue |< tcbs_of' s)"
  (wp: hoare_vcg_all_lift crunch_wps hoare_vcg_if_lift valid_mdb'_lift
   simp: pred_tcb_at'_def if_distribR if_bool_eq_conj)

crunch replyPush, replyPop, breakReplyChainAt
  for pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and bounded'[wp]: pspace_bounded'
  and pspace_canonical'[wp]: pspace_canonical'
  and if_unsafe_then_cap'[wp]: if_unsafe_then_cap'
  and valid_global_refs'[wp]: valid_global_refs'
  and valid_arch_state'[wp]: valid_arch_state'
  and valid_irq_node'[wp]: "\<lambda>s. valid_irq_node' (irq_node' s) s"
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and valid_irq_handlers'[wp]: valid_irq_handlers'
  and valid_irq_states'[wp]: valid_irq_states'
  and valid_machine_state'[wp]: valid_machine_state'
  and irqs_masked'[wp]: irqs_masked'
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and valid_dom_schedule'[wp]: valid_dom_schedule'
  and no_0_obj'[wp]: no_0_obj'
  and valid_mdb'[wp]: valid_mdb'
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n T p s)"
  and cte_wp_at'[wp]: "cte_wp_at' P p"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  (wp: crunch_wps hoare_vcg_all_lift valid_irq_node_lift valid_dom_schedule'_lift
   simp: crunch_simps valid_mdb'_def replyPush'_def replyPop'_def)

global_interpretation replyUnlink: gen_typ_at_all_props' "replyUnlink replyPtr tcbPtr"
  by typ_at_props'

global_interpretation replyPush: gen_typ_at_all_props' "replyPush' scPtr replyPtr scReplyOpt"
  by typ_at_props'

global_interpretation replyPush': gen_typ_at_all_props' "replyPush scPtr replyPtr"
  by typ_at_props'

global_interpretation replyPop: gen_typ_at_all_props' "replyPop replyPtr"
  by typ_at_props'

global_interpretation breakReplyChainAt': gen_typ_at_all_props' "breakReplyChainAt' replyPtr"
  by typ_at_props'

global_interpretation breakReplyChainAt: gen_typ_at_all_props' "breakReplyChainAt replyPtr"
  by typ_at_props'

lemma replyRemoveTCB_st_tcb_at'_cases:
  "\<lbrace>\<lambda>s. (t = t' \<longrightarrow> Q (P Inactive)) \<and> (t \<noteq> t' \<longrightarrow> Q (st_tcb_at' P t s))\<rbrace>
   replyRemoveTCB t'
   \<lbrace>\<lambda>_ s. Q (st_tcb_at' P t s)\<rbrace>"
  unfolding replyRemoveTCB_def
  by (wpsimp wp: replyUnlink_st_tcb_at' gts_wp' hoare_vcg_imp_lift')

lemma replyNext_update_valid_objs'[wp]:
  "\<lbrace>valid_objs' and valid_bound_reply' ptrOpt\<rbrace>
   updateReply replyPtr (replyNext_update (\<lambda>_. ptrOpt))
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  by (wpsimp wp: updateReply_valid_objs' hoare_vcg_all_lift simp: valid_reply'_def)

lemma replyPrev_update_valid_objs'[wp]:
  "\<lbrace>valid_objs' and valid_bound_reply' ptrOpt\<rbrace>
   updateReply replyPtr (replyPrev_update (\<lambda>_. ptrOpt))
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  by (wpsimp wp: updateReply_valid_objs' hoare_vcg_all_lift simp: valid_reply'_def)

lemma updateSchedContext_scReply_update_valid_objs'[wp]:
  "updateSchedContext scp (scReply_update f) \<lbrace>valid_objs'\<rbrace>"
  apply (wpsimp wp: updateSchedContext_valid_objs')
  apply (clarsimp simp: valid_obj'_def valid_sched_context'_def refillSize_def split: if_splits)
  done

lemma replySC_update_valid_objs'[wp]:
  "\<lbrace>valid_objs' and valid_bound_sc' ptrOpt\<rbrace>
   updateReply replyPtr (replySC_update (\<lambda>_. ptrOpt))
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  by (wpsimp wp: updateReply_valid_objs' hoare_vcg_all_lift simp: valid_reply'_def)

lemma breakReplyChainAt_valid_objs'[wp]:
  "breakReplyChainAt replyPtr \<lbrace>valid_objs'\<rbrace>"
  unfolding breakReplyChainAt_def breakReplyChainAt'_def
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_const_imp_lift)

lemma replyRemoveTCB_valid_objs'[wp]:
  "replyRemoveTCB tptr \<lbrace>valid_objs'\<rbrace>"
  unfolding replyRemoveTCB_def
  by (wpsimp wp: updateReply_valid_objs' gts_wp')

lemma replyPrev_update_valid_replies'[wp]:
  "\<lbrace>\<lambda>s. valid_replies' s \<and> (\<forall>ptr. replyPtrOpt = Some ptr \<longrightarrow> is_replyObject replyPtr s)\<rbrace>
   updateReply replyPtr (replyPrev_update (\<lambda>_. replyPtrOpt))
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  apply (wpsimp wp: updateReply_valid_replies')
  apply (fastforce dest: spec[where x=replyPtr] simp: obj_at'_def opt_map_red valid_replies'_def)
  done

lemma replyNext_update_valid_replies'[wp]:
  "\<lbrace>\<lambda>s. valid_replies' s \<and> (\<forall>ptr. replyPtrOpt = Some ptr \<longrightarrow> is_replyObject replyPtr s)\<rbrace>
   updateReply replyPtr (replyNext_update (\<lambda>_. replyPtrOpt))
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  apply (wpsimp wp: updateReply_valid_replies')
  apply (fastforce dest: spec[where x=replyPtr] simp: obj_at'_def opt_map_red valid_replies'_def)
  done

lemma updateReply_replySC_None_valid_replies[wp]:
  "updateReply rptr (replySC_update f) \<lbrace>valid_replies'\<rbrace>"
  unfolding valid_replies'_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' updateReply_field_inv hoare_vcg_ex_lift)

crunch breakReplyChainAt, replyPop, replyPush
  for replyTCBs_of[wp]: "\<lambda>s. P (replyTCBs_of s)"
  (wp: crunch_wps updateReply_field_inv simp: crunch_simps)

lemma breakReplyChainAt'_valid_replies'[wp]:
  "\<lbrace>valid_replies' and pspace_aligned' and pspace_distinct'\<rbrace>
   breakReplyChainAt' replyPtr
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  unfolding breakReplyChainAt'_def
  by (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_if_lift2)

lemma breakReplyChainAt_valid_replies'[wp]:
  "\<lbrace>valid_replies' and pspace_aligned' and pspace_distinct'\<rbrace>
   breakReplyChainAt replyPtr
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  unfolding breakReplyChainAt_def
  by (wpsimp wp: hoare_drop_imps)

lemma breakReplyChainAt'_not_reply_linked[wp]:
  "\<lbrace>\<top>\<rbrace> breakReplyChainAt' rptr \<lbrace>\<lambda>_ s. \<not> is_reply_linked rptr s\<rbrace>"
  unfolding breakReplyChainAt'_def
  apply (wpsimp wp: updateReply_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma breakReplyChainAt_not_reply_linked[wp]:
  "\<lbrace>\<top>\<rbrace> breakReplyChainAt rptr \<lbrace>\<lambda>_ s. \<not> is_reply_linked rptr s\<rbrace>"
  unfolding breakReplyChainAt_def
  by (wpsimp wp: breakReplyChainAt'_not_reply_linked[simplified] updateReply_field_inv
                 hoare_vcg_if_lift2 hoare_drop_imps)

crunch breakReplyChainAt'
  for replySCs_of[wp]: "\<lambda>s. P (replySCs_of s)"
  (wp: updateReply_field_inv simp: crunch_simps)

lemma breakReplyChainAt_replySCs_of_None[wp]:
  "\<lbrace>\<top>\<rbrace> breakReplyChainAt rptr \<lbrace>\<lambda>_ s. replySCs_of s rptr = None\<rbrace>"
  unfolding breakReplyChainAt_def
  apply (wpsimp wp: updateReply_wp hoare_vcg_if_lift2)
  apply (clarsimp simp: obj_at'_def opt_map_red)
  done

defs replyPop'_asrt_def:
  "replyPop'_asrt \<equiv> \<lambda>replyPtr scPtr s.
     (\<exists>ls. heap_ls (replyPrevs_of s) (scReplies_of s scPtr) ls \<and> ls \<noteq> [] \<and> replyPtr = hd ls
           \<and> replyNexts_of s replyPtr = None)
     \<and> is_replyObject replyPtr s"

lemma replyPop'_not_reply_linked[simplified, wp]:
  "\<lbrace>\<top>\<rbrace> replyPop' replyPtr scPtr prevReplyOpt \<lbrace>\<lambda>_ s. \<not> is_reply_linked replyPtr s\<rbrace>"
  unfolding replyPop'_def
  apply (wpsimp wp: updateReply_wp)
  apply (fastforce simp: obj_at'_def opt_map_def replyPop'_asrt_def split: option.splits)
  done

lemma replyPop_not_reply_linked[wp]:
  "\<lbrace>\<top>\<rbrace> replyPop replyPtr \<lbrace>\<lambda>_ s. \<not> is_reply_linked replyPtr s\<rbrace>"
  unfolding replyPop_def
  by (wpsimp wp: updateReply_field_inv hoare_vcg_if_lift2 hoare_vcg_all_lift hoare_drop_imps)

crunch replyRemoveTCB
  for valid_replies'[wp]: valid_replies'
  (wp: crunch_wps)

lemma breakReplyChainAt'_sym_heap_reply_pointers[wp]:
  "breakReplyChainAt' replyPtr \<lbrace>sym_heap_reply_pointers\<rbrace>"
  apply (clarsimp simp: breakReplyChainAt'_def)
  apply (rule bind_wp[OF _ get_reply_sp'], rename_tac reply)
  apply (case_tac "\<exists>prevPtr. replyPrev reply = Some prevPtr"; clarsimp)
   apply (rule_tac P'1="\<lambda>s. replyNexts_of s prevPtr = Some replyPtr" in hoare_pre_add[THEN iffD2])
    apply (force elim: sym_heapD1 simp: obj_at'_def opt_map_red)
   apply (case_tac "\<exists>nextPtr. replyNext reply = Some nextPtr"; clarsimp)
    apply (rule_tac P'1="\<lambda>s. replyPrevs_of s nextPtr = Some replyPtr" in hoare_pre_add[THEN iffD2])
     apply (force elim: sym_heapD2 simp: obj_at'_def opt_map_red)
    apply (wpsimp wp: updateReply_wp)
    apply (drule obj_at'_prop)+
    apply (clarsimp split: if_splits)
        apply (simp add: opt_map_red sym_heap_remove_only)
       apply (subst fun_upd_swap)
        apply fastforce
       apply (force intro!: sym_heap_remove_only' simp: opt_map_red)
      apply (clarsimp simp: opt_map_red)
     apply (clarsimp simp: opt_map_red)
    apply (fastforce dest: sym_heap_break_middle_of_chain[where middle=replyPtr]
                     elim: sym_heap_cong
                     simp: opt_map_red)
   apply (wpsimp wp: updateReply_wp)
   apply (force simp: opt_map_upd_triv opt_map_red sym_heap_remove_only obj_at'_def)
  apply (wpsimp wp: updateReply_wp)
  apply (force simp: opt_map_upd_triv opt_map_red sym_heap_remove_only obj_at'_def)
  done

lemma sym_heap_reply_pointers_lift:
  assumes nexts: "\<And>P. f \<lbrace>\<lambda>s. P (replyNexts_of s)\<rbrace>"
  assumes prevs: "\<And>P. f \<lbrace>\<lambda>s. P (replyPrevs_of s)\<rbrace>"
  shows "f \<lbrace>sym_heap_reply_pointers\<rbrace>"
  by (rule_tac f=replyNexts_of in hoare_lift_Pf2; wpsimp wp: assms)

lemma breakReplyChainAt_sym_heap_reply_pointers[wp]:
  "breakReplyChainAt replyPtr \<lbrace>sym_heap_reply_pointers\<rbrace>"
  unfolding breakReplyChainAt_def
  by (wpsimp | wpsimp wp: sym_heap_reply_pointers_lift updateReply_field_inv)+

crunch replyUnlink, replyRemoveTCB
  for sym_heap_reply_pointers[wp]: sym_heap_reply_pointers
  (rule: sym_heap_reply_pointers_lift)

lemma setSchedContext_valid_tcbs'[wp]:
  "setSchedContext scPtr sc \<lbrace>valid_tcbs'\<rbrace>"
  unfolding setSchedContext_def
  apply (wpsimp wp: setObject_valid_tcbs'[where P=\<top>])
   apply (clarsimp simp: updateObject_default_def in_monad project_inject)
  apply simp
  done

crunch replyRemoveTCB
  for valid_bitmaps[wp]: valid_bitmaps
  (simp: crunch_simps wp: crunch_wps)

lemma setThreadState_not_queued_valid_sched_pointers:
  "\<lbrace>\<lambda>s. valid_sched_pointers s \<and> \<not> (inIPCQueueThreadState |< tcbStates_of' s) t\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  by (wpsimp wp: setThreadState_valid_sched_pointers)

crunch breakReplyChainAt
  for valid_sched_pointers[wp]: valid_sched_pointers
  and tcbStates_of[wp]: "\<lambda>s. P (tcbStates_of' s)"
  (simp: crunch_simps wp: crunch_wps)

lemma replyRemove_valid_sched_pointers[wp]:
  "replyRemoveTCB tptr \<lbrace>valid_sched_pointers\<rbrace>"
  apply (clarsimp simp: replyRemoveTCB_def replyUnlink_def)
  apply (rule bind_wp[OF _ stateAssert_sp])
  apply (wpsimp wp: setThreadState_not_queued_valid_sched_pointers
                    gts_wp' hoare_vcg_all_lift hoare_drop_imps)
  apply (clarsimp simp: st_tcb_at'_def)
  apply normalise_obj_at'
  apply (rename_tac tcb, case_tac "tcbState tcb";
         clarsimp simp: isReply_def obj_at'_def opt_pred_def opt_map_def)
  done

crunch replyRemoveTCB
  for tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
  and tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  (simp: crunch_simps wp: crunch_wps)

lemma replyRemoveTCB_invs':
  "replyRemoveTCB tptr \<lbrace>invs'\<rbrace>"
  unfolding invs'_def valid_pspace'_def
  by (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift' valid_irq_states_lift'
                 irqs_masked_lift valid_dom_schedule'_lift
           simp: cteCaps_of_def)

lemma setReply_corres: (* for reply update that doesn't touch the reply stack *)
  "reply_relation ae ae' \<Longrightarrow>
   corres dc
     \<top> (obj_at' (\<lambda>reply. replyPrev reply = replyPrev ae' \<and> replyNext reply = replyNext ae') ptr)
     (set_reply ptr ae) (setReply ptr ae')"
  apply (rule_tac Q="reply_at ptr" in corres_cross_add_abs_guard)
   apply (fastforce intro: reply_at'_cross simp: obj_at'_def)
  apply (rule corres_underlying_from_rcorres)
   apply (wpsimp simp: setReply_def obj_at'_def gen_objBits_simps)
  apply (clarsimp simp: state_relation_def ghost_relation_heap_ghost_relation
                        pspace_relation_heap_pspace_relation heap_pspace_relation_def)
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   apply (rcorres_conj_lift fastforce)+
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
    \<comment>\<open>replies_relation\<close>
   apply (rule rcorres_from_valid_det; (solves wpsimp)?)
   apply (drule in_set_reply)
   apply (wpsimp simp: setReply_def)
   apply (fastforce intro: map_relation_fun_upd simp flip: fun_upd_def)
  apply (rcorres_conj_lift fastforce)+
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
    \<comment>\<open>sc_replies_relation\<close>
   apply (rule rcorres_weaken_pre)
    apply (rule_tac Q="\<lambda>s s'. reply_at ptr s \<and> obj_at' (\<lambda>reply. replyPrev reply = replyPrev ae') ptr s'
                              \<and> obj_at' (\<lambda>reply. replyNext reply = replyNext ae') ptr s'"
                 in sc_replies_relation_lift_rcorres;
           wpsimp)
     apply (rename_tac P s s')
     apply (erule_tac P=P in rsubst)
     apply (fastforce simp: obj_at'_def opt_map_def)
    apply (rename_tac P s s')
    apply (erule_tac P=P in rsubst)
    apply (fastforce simp: obj_at'_def opt_map_red)
   apply (fastforce simp: obj_at'_def)
  apply (rcorres_conj_lift fastforce)+
  done

lemma updateReply_corres: (* for reply update that doesn't touch the reply stack *)
  "\<lbrakk>\<And>reply reply'. reply_relation reply reply' \<Longrightarrow> reply_relation (f reply) (f' reply');
    \<And>reply'. replyPrev (f' reply') = replyPrev reply';
    \<And>reply'. replyNext (f' reply') = replyNext reply'; reply_ptr = replyPtr\<rbrakk> \<Longrightarrow>
   corres dc (reply_at reply_ptr and pspace_aligned and pspace_distinct) \<top>
     (update_reply f reply_ptr) (updateReply replyPtr f')"
  apply add_pspace_adb'
  apply (rule_tac Q'="reply_at' replyPtr" in corres_cross_add_guard)
   apply (fastforce intro: reply_at_cross)
  apply (clarsimp simp: update_reply_def updateReply_def)
  apply (corres corres: get_reply_corres setReply_corres)
  apply (clarsimp simp: obj_at'_def)
  done

lemma not_in_replies_with_sc_not_in_set:
  "\<lbrakk>ptr \<notin> fst ` replies_with_sc s; sc_replies_of s p = Some replies\<rbrakk> \<Longrightarrow> ptr \<notin> set replies"
   by (fastforce simp: scs_of_kh_def sc_at_pred_n_def obj_at_def replies_with_sc_def image_def
                       opt_map_def
                split: option.splits)

defs valid_bound_reply'_asrt_def:
  "valid_bound_reply'_asrt replyOpt \<equiv> valid_bound_reply' replyOpt"

declare valid_bound_reply'_asrt_def[simp]

lemma no_fail_setReply[wp]:
  "no_fail (reply_at' p) (setReply p reply)"
  unfolding setReply_def
  by (wpsimp simp: gen_objBits_simps)

lemma no_fail_updateReply[wp]:
  "no_fail (reply_at' rp) (updateReply rp f)"
  unfolding updateReply_def
  by wpsimp

lemma get_reply_det_wp[wp]:
  "det_wp (reply_at reply_ptr) (get_reply reply_ptr)"
  unfolding get_simple_ko_def
  apply (wpsimp wp: set_object_det_wp get_object_wp get_simple_ko_wp)
  apply (clarsimp simp: obj_at_def is_reply_def)
  apply (rename_tac ko, case_tac ko; clarsimp)
  done

lemma update_reply_det_wp[wp]:
  "det_wp (reply_at reply_ptr) (update_reply f reply_ptr)"
  unfolding update_reply_def
  by wpsimp

lemmas update_reply_no_fail[wp] = update_reply_det_wp[THEN det_wp_no_fail]

lemma update_sched_context_det_wp_weak:
  "det_wp (sc_at ptr) (update_sched_context ptr f)"
  apply (clarsimp simp: det_wp_def update_sched_context_def get_object_def gets_the_def gets_def
                        get_def bind_def obj_at_def is_sc_obj_def set_object_def)
  apply (rename_tac ko n, case_tac ko; clarsimp simp: return_def assert_def put_def a_type_def)
  done

lemmas update_sched_context_no_fail_weak = update_sched_context_det_wp_weak[THEN det_wp_no_fail]

crunch update_reply
  for (empty_fail) empty_fail[wp, simp]

lemma updateSchedContext_dom_scs_of'[wp]:
  "updateSchedContext ptr f \<lbrace>\<lambda>s. P (dom (scs_of' s))\<rbrace>"
  apply (wpsimp wp: updateSchedContext_wp)
  apply (fastforce elim!: rsubst[where P=P] simp: projectKO_opts_defs obj_at'_def opt_map_red)
  done

lemma updateSchedContext_field_inv:
  "(\<And>sc. f (upd sc) = f sc) \<Longrightarrow> updateSchedContext scPtr upd \<lbrace>\<lambda>s. P (scs_of' s |> f)\<rbrace>"
  apply (wpsimp wp: updateSchedContext_wp)
  apply (fastforce elim!: rsubst[where P=P] simp: opt_map_def obj_at'_def)
  done

crunch replyPush, breakReplyChainAt, replyPop
  for tcbs_of'[wp]: "\<lambda>s. P (tcbs_of' s)"
  and cnode_ctes_of'[wp]: "\<lambda>s. P (cnode_ctes_of' s)"
  and dom_scs_of'[wp]: "\<lambda>s. P (dom (scs_of' s))"
  and dom_replies_of'[wp]: "\<lambda>s. P (dom (replies_of' s))"
  and eps_of'[wp]: "\<lambda>s. P (eps_of' s)"
  and ntfns_of'[wp]: "\<lambda>s. P (ntfns_of' s)"
  and aobjs_of'[wp]: "\<lambda>s. P (aobjs_of' s)"
  and kernelData_at[wp]: "\<lambda>s. P (kernelData_at s)"
  and userDataDevice_at[wp]: "\<lambda>s. P (userDataDevice_at s)"
  and userData_at[wp]: "\<lambda>s. P (userData_at s)"
  (wp: crunch_wps simp: crunch_simps)

lemma reply_at_cross_replies_relation:
  "\<lbrakk>reply_at reply_ptr s; replies_relation s s'; pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> reply_at' reply_ptr s'"
  apply (clarsimp simp: obj_at_def is_reply_def)
  apply (clarsimp split: Structures_A.kernel_object.splits)
  apply (frule (3) replies_relation_reply_relation_abs_obj_at')
  apply (clarsimp simp: obj_at'_def)
  done

lemma reply_at'_scReply:
  "\<lbrakk>scReply sc' = Some replyPtr; ksPSpace s' scPtr = Some (KOSchedContext sc');
    sc_replies_relation s s'; replies_relation s s'; scs_relation s s';
    valid_objs s; pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> reply_at' replyPtr s'"
  apply (frule (1) scs_relation_sc_relation_conc)
  apply (clarsimp simp: sc_replies_relation_def)
  apply (rename_tac sc n)
  apply (drule_tac x=scPtr in spec)
  apply (prop_tac "sc_replies sc \<noteq> []")
   apply (clarsimp simp: vs_all_heap_simps in_opt_pred opt_map_red)
  apply (fastforce intro: reply_at_cross_replies_relation
                   dest!: heap_path_head valid_objs_valid_sched_context
                    simp: vs_all_heap_simps valid_sched_context_def list_all_iff opt_map_red)
  done

lemma is_replyObject_cross:
  "\<lbrakk>(s, s') \<in> state_relation; valid_replies s; sym_refs (state_refs_of s);
    pspace_aligned' s'; pspace_distinct' s'; \<exists>ls. sc_replies_of s scPtr = Some (replyPtr # ls)\<rbrakk>
   \<Longrightarrow> is_replyObject replyPtr s'"
  apply (frule valid_repliesE1[where r=replyPtr])
   apply (fastforce simp: scs_of_kh_def sc_at_ppred_def obj_at_def opt_map_def split: option.splits)
  apply (clarsimp simp: pred_tcb_at_eq_commute[symmetric])
  apply (frule (1) st_tcb_reply_state_refs)
  apply (fastforce dest: replyTCBs_of_cross st_tcb_at_coerce_concrete elim: pred_tcb'_weakenE)
  done

crunch update_sched_context, update_reply
  for work_units_completed[wp]: "\<lambda>s. P (work_units_completed s)"
  and reprogram_timer[wp]: "\<lambda>s. P (reprogram_timer s)"
  (wp: crunch_wps)

lemma updateSchedContext_scs_of'_other:
  "\<lbrace>\<lambda>s. P ((scs_of' s |> f) scPtr') \<and> scPtr' \<noteq> scPtr\<rbrace>
   updateSchedContext scPtr upd
   \<lbrace>\<lambda>_ s. P ((scs_of' s |> f) scPtr')\<rbrace>"
  by (wpsimp wp: updateSchedContext_wp)

lemma updateReply_replyNext_update_heap_ls[wp]:
  "updateReply replyPtr (replyNext_update f) \<lbrace>\<lambda>s. heap_ls (replyPrevs_of s) st ls\<rbrace>"
  by (wpsimp wp: updateReply_field_inv)

lemma updateReply_heap_ls_other:
  "\<lbrace>\<lambda>s. heap_ls (replyPrevs_of s) st ls \<and> (ls \<noteq> [] \<longrightarrow> replyPtr \<notin> set ls)\<rbrace>
   updateReply replyPtr (replyPrev_update f)
   \<lbrace>\<lambda>_ s. heap_ls (replyPrevs_of s) st ls\<rbrace>"
  apply (wpsimp wp: updateReply_wp)
  apply (fastforce dest: heap_path_heap_upd_not_in)
  done

lemma prev_list_head_replyNexts_of_replyPrev_update[wp]:
  "updateReply replyPtr (replyPrev_update f) \<lbrace>\<lambda>s. prev_list_head st (replyNexts_of s)\<rbrace>"
  by (wpsimp wp: updateReply_field_inv)

lemma prev_list_head_other:
  "\<lbrace>\<lambda>s. prev_list_head st (replyNexts_of s) \<and> (\<forall>ptr. st = Some ptr \<and> v \<noteq> None \<longrightarrow> replyPtr \<noteq> ptr)\<rbrace>
   updateReply replyPtr (replyNext_update (\<lambda>_. v))
   \<lbrace>\<lambda>_ s. prev_list_head st (replyNexts_of s)\<rbrace>"
  apply (wpsimp wp: updateReply_wp)
  apply (clarsimp simp: prev_list_head_def)
  done

lemma updateReply_replies_of'_other:
  "\<lbrace>\<lambda>s. P ((replies_of' s |> f) replyPtr') \<and> replyPtr' \<noteq> replyPtr\<rbrace>
   updateReply replyPtr upd
   \<lbrace>\<lambda>_ s. P ((replies_of' s |> f) replyPtr')\<rbrace>"
  by (wpsimp wp: updateReply_wp)

lemma sc_replies_disjoint:
  "\<lbrakk>sc_replies_of s sc_ptr = Some replies; sc_replies_of s sc_ptr' = Some replies';
    sc_ptr \<noteq> sc_ptr'; valid_replies s\<rbrakk>
   \<Longrightarrow> set replies \<inter> set replies' = {}"
  by (force dest: valid_replies_sc_replies_unique
            simp: opt_map_def sc_at_ppred_def obj_at_def scs_of_kh_def
           split: option.splits)

lemma scReplies_of_sc_replies_of_Some:
  "\<lbrakk>scReplies_of s' scPtr = Some ptr; sc_replies_relation s s'; scs_relation s s'\<rbrakk>
   \<Longrightarrow> \<exists>ls. sc_replies_of s scPtr = Some (ptr # ls)"
  apply (clarsimp simp: sc_replies_relation_def)
  apply (prop_tac "\<exists>sc'. ksPSpace s' scPtr = Some (KOSchedContext sc')")
   apply (clarsimp simp: opt_map_def split: option.splits)
  apply clarsimp
  apply (frule (1) scs_relation_sc_relation_conc)
  apply clarsimp
  apply (rename_tac sc n)
  apply (case_tac "sc_replies sc";
         fastforce dest: sc_replies_relation_scReplies_of
                   simp: scs_of_kh_def opt_map_def split: option.splits)
  done

lemma scReplies_not_equal:
  "\<lbrakk>scReplies_of s' scPtr = Some ptr; scReplies_of s' scPtr' = Some ptr'; scPtr \<noteq> scPtr';
    sc_replies_relation s s'; scs_relation s s'; valid_replies s\<rbrakk>
   \<Longrightarrow> ptr \<noteq> ptr'"
  by (fastforce dest: scReplies_of_sc_replies_of_Some sc_replies_disjoint)

defs replyPush'_asrt_def:
  "replyPush'_asrt \<equiv>
     \<lambda>ptrOpt s. (\<forall>ptr. ptrOpt = Some ptr \<longrightarrow> is_replyObject ptr s \<and> replyNexts_of s ptr = None)"

lemma replyPush'_corres:
  "corres dc
     (\<lambda>s. sc_at scPtr s \<and> (\<exists>n. ko_at (Structures_A.SchedContext sc n) scPtr s )
          \<and> reply_at replyPtr s \<and> replyPtr \<notin> fst ` replies_with_sc s
          \<and> valid_replies s \<and> valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s)
     (\<lambda>s'. ko_at' sc' scPtr s' \<and> (\<forall>ptr. scReplies_of s' scPtr = Some ptr \<longrightarrow> is_replyObject ptr s'))
     (set_sc_obj_ref sc_replies_update scPtr (replyPtr # sc_replies sc))
     (replyPush' scPtr replyPtr (scReply sc'))"
  supply if_split[split del] heap_path_append[simp del]
         update_sched_context_det_wp_weak[wp] update_sched_context_no_fail_weak[wp]
  apply add_pspace_adb'
  apply (rule_tac Q'="reply_at' replyPtr" in corres_cross_add_guard)
   apply (fastforce intro: reply_at_cross)
  apply (rule corres_underlying_from_rcorres)
   apply (clarsimp simp: replyPush'_def)
   apply (wpsimp wp: no_fail_stateAssert hoare_vcg_if_lift2 hoare_vcg_imp_lift'
               simp: replyPush'_def replyPush'_asrt_def)
   apply (rename_tac s' s n)
   apply (frule state_relation_pspace_relation)
   apply (frule state_relation_sc_replies_relation)
   apply (clarsimp simp: pspace_relation_heap_pspace_relation)
   apply (intro conjI impI allI; clarsimp?)
       apply (clarsimp simp: obj_at'_def opt_map_red)
      apply (prop_tac "scReplies_of s' scPtr = Some ptr")
       apply (clarsimp simp: obj_at'_def opt_map_red)
      apply (fastforce dest!: scReplies_of_sc_replies_of_Some state_relation_sc_replies_relation
                        simp: sc_replies_relation_2_def prev_list_head_def)
     apply (fastforce intro!: reply_at'_scReply simp: obj_at'_def)
    apply (clarsimp simp: in_opt_pred obj_at'_def opt_map_red)
   apply (clarsimp simp: in_opt_pred obj_at'_def opt_map_red)
  apply (clarsimp simp: state_relation_def ghost_relation_heap_ghost_relation
                        pspace_relation_heap_pspace_relation heap_pspace_relation_def)
  apply (rcorres_conj_lift clarsimp
                           wp: update_sched_context_field_inv updateSchedContext_field_inv
                               updateReply_field_inv
                           simp: replyPush'_def)+
  apply (rule rcorres_conj_lift_fwd)
    apply (wpsimp wp: update_sched_context_det_wp_weak)
   \<comment> \<open>sc_replies_relation\<close>
   apply (clarsimp simp: replyPush'_def update_sched_context_def)
   apply (rule rcorres_symb_exec_l[OF get_object_sp get_object_exs_valid])
    apply (clarsimp simp: obj_at_def)
   apply (rename_tac ko, case_tac ko; clarsimp;
          (solves \<open>rcorres rcorres: rcorres_fail, clarsimp simp: obj_at_def is_sc_obj_def\<close>)?)
   apply (rename_tac n)
   apply (rule_tac F="replyPtr \<noteq> scPtr" in rcorres_req)
    apply (clarsimp simp: obj_at_def is_reply)
   apply (rule_tac Q="\<lambda>s s'. sc_replies_of s scPtr = Some (sc_replies sc)" in rcorres_add_to_pre)
    apply (clarsimp simp: obj_at_def scs_of_kh_def opt_map_red)
   apply (rule_tac F="\<forall>r. scReply sc' = Some r
                          \<longrightarrow> (sc_replies sc \<noteq> [] \<and> hd (sc_replies sc) = r \<and> r \<noteq> replyPtr)"
                in rcorres_req)
    apply clarsimp
    apply (frule (1) sc_replies_relation_scReplies_of)
     apply (clarsimp simp: in_opt_pred opt_map_red obj_at'_def)
    apply (frule (1) not_in_replies_with_sc_not_in_set)
    apply (force simp: sc_at_ppred_def obj_at_def opt_map_red obj_at'_def scs_of_kh_def)
   apply (rule_tac Q="\<lambda>s _. sc_obj_at n scPtr s" in rcorres_add_to_pre)
    apply (clarsimp simp: is_sc_obj_def obj_at_def)
   apply (simp only: sc_replies_relation_def)
   apply (rule rcorres_allI_fwd; (solves wpsimp)?)
   apply (rename_tac p)
   apply (case_tac "p \<noteq> scPtr")
    apply (intro rcorres_allI_fwd; (solves wpsimp)?)
    apply (rule rcorres_imp_lift_fwd)
     apply (rcorres wp: set_sched_context_scs_of_other)
     apply clarsimp
    apply (rule rcorres_imp_lift_fwd)
     apply (rcorres wp: updateSchedContext_scs_of'_other)
     apply fastforce
    apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
     apply (rcorres wp: updateReply_heap_ls_other)
     apply (force dest!: not_in_replies_with_sc_not_in_set simp: is_sc_obj_def obj_at_def)
    apply (rcorres wp: prev_list_head_other hoare_vcg_if_lift2 hoare_vcg_const_imp_lift)
    apply clarsimp
    apply (frule scReplies_not_equal[where scPtr'=scPtr and ptr'="hd (sc_replies sc)"];
           fastforce simp: sc_replies_relation_def opt_map_red obj_at'_def)
   \<comment> \<open>p = sc_ptr\<close>
   apply (rule rcorres_from_valid_det; (solves wpsimp)?)
   apply (drule in_set_object)
   apply (case_tac "\<exists>head. scReply sc' = Some head"; clarsimp)
    apply (wpsimp wp: updateReply_wp updateSchedContext_wp)
    apply (drule_tac x=scPtr in spec)+
    apply (rule conjI)
     apply (drule obj_at'_prop)+
     apply (clarsimp simp: sc_replies_relation_def)
     apply (frule (1) not_in_replies_with_sc_not_in_set[where p=scPtr and replies="sc_replies sc"])
     apply (drule (2) heap_ls_prepend[where new=replyPtr])
     apply (clarsimp simp: projectKO_opts_defs)
     apply (subst fun_upd_swap)
      apply fastforce
     apply (subst opt_map_upd_triv)
      apply (clarsimp simp: opt_map_red)
     subgoal by (fastforce simp: scs_of_kh_def opt_map_def split: option.splits)
    subgoal by (force simp: projectKO_opts_defs obj_at'_def prev_list_head_def)
   apply (wpsimp wp: updateReply_wp updateSchedContext_wp)
   subgoal
     by (force simp: scs_of_kh_def opt_map_def obj_at'_def prev_list_head_def)
  apply (rcorres_conj_lift clarsimp simp: replyPush'_def)+
  done

lemma replyPush_corres:
  "corres dc
     (\<lambda>s. reply_at replyPtr s \<and> sc_at scPtr s \<and> replyPtr \<notin> fst ` replies_with_sc s
          \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_objs s
          \<and> valid_replies s \<and> sym_refs (state_refs_of s))
     \<top>
     (reply_push scPtr replyPtr) (replyPush scPtr replyPtr)"
  supply if_split[split del]
  apply add_pspace_adb'
  apply (rule_tac Q'="sc_at' scPtr" in corres_cross_add_guard)
   apply (fastforce intro!: sc_at_cross)
  apply (rule_tac Q'="reply_at' replyPtr" in corres_cross_add_guard)
   apply (fastforce intro!: reply_at_cross)
  apply (rule_tac Q'="\<lambda>s'. \<forall>ptr. scReplies_of s' scPtr = Some ptr \<longrightarrow> is_replyObject ptr s'"
               in corres_cross_add_guard)
   apply clarsimp
   apply (rule is_replyObject_cross[where scPtr=scPtr], fastforce+)
   apply (fastforce dest!: sc_replies_relation_scReplies_of state_relation_sc_replies_relation
                     simp: sc_at_ppred_def obj_at_def scs_of_kh_def opt_map_def
                    split: option.splits)
  apply (clarsimp simp: reply_push_def replyPush_def case_list_when liftM_def)
  apply (rule corres_symb_exec_l[OF _ get_sched_context_exs_valid get_sched_context_sp, rotated])
    apply (fastforce intro: sc_atD1)
   apply wpsimp
   apply (fastforce intro: sc_atD1)
  apply (rename_tac sc)
  apply add_sym_refs
  apply (rule corres_stateAssert_ignore, fastforce)
  apply (rule corres_symb_exec_r[OF _ get_sc_sp']; (solves wpsimp)?)
  apply (rename_tac sc')
  apply (rule_tac Q="\<lambda>s. sc_replies sc \<noteq> [] \<longrightarrow> reply_at (hd (sc_replies sc)) s"
               in corres_cross_add_abs_guard)
   apply (clarsimp simp: obj_at_def)
   apply (frule (1) valid_sched_context_objsI)
   apply (clarsimp simp: valid_sched_context_def obj_at_def split: list.splits)
   apply (case_tac "sc_replies sc"; fastforce simp: obj_at_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (clarsimp simp: valid_bound_obj'_def split: option.splits)
   apply (frule state_relation_pspace_relation)
   apply (frule state_relation_sc_replies_relation)
   apply (fastforce intro!: reply_at'_scReply
                      simp: pspace_relation_heap_pspace_relation obj_at'_def)
  apply (rule_tac F="((sc_replies sc \<noteq> []) \<longleftrightarrow> (scReply sc' \<noteq> None))
                     \<and> (\<forall>p. sc_replies sc \<noteq> [] \<longrightarrow> hd (sc_replies sc) = p \<longleftrightarrow> scReply sc' = Some p)"
               in corres_req)
   apply (fastforce dest!: sc_replies_relation_scReplies_of state_relation_sc_replies_relation
                     simp: opt_map_red obj_at_def scs_of_kh_def obj_at'_def hd_opt_def
                    split: list.splits)
  apply (rule corres_split_forwards'[where r'=dc])
     apply (clarsimp simp: when_def split: if_splits)
     apply (corres corres: updateReply_corres simp: reply_relation_def)
    apply (find_goal \<open>match conclusion in "corres _ _ _ _ _" \<Rightarrow> -\<close>)
    apply (corres corres: replyPush'_corres updateReply_corres
                    simp: reply_relation_def)
   apply (wpsimp wp: hoare_vcg_ex_lift)
   apply fastforce
  apply (wpsimp wp: updateReply_field_inv hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (clarsimp split: if_splits)
  done

lemma updateReply_obj_at':
  "\<lbrace>\<lambda>s. reply_at' rptr s \<longrightarrow>
          P (obj_at' (\<lambda>ko. if rptr = p then Q (f ko) else Q ko) p s)\<rbrace>
   updateReply rptr f
   \<lbrace>\<lambda>rv s. P (obj_at' Q p s)\<rbrace>"
  apply (simp only: obj_at'_real_def updateReply_def)
  apply (wp set_reply'.ko_wp_at)
  apply (auto simp: ko_wp_at'_def obj_at'_def split: if_splits)
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

lemma updateReply_obj_at'_inv:
  "\<forall>x. P (f x) = P x \<Longrightarrow>
   updateReply rPtr f \<lbrace>\<lambda>s. Q (obj_at' (P :: reply \<Rightarrow> bool) rp s)\<rbrace>"
  apply (wpsimp wp: updateReply_wp)
  apply (subgoal_tac "obj_at' P rp s = (obj_at' P rp (s\<lparr>ksPSpace := (ksPSpace s)(rPtr \<mapsto> KOReply (f ko))\<rparr>))")
   apply simp
  by (force simp: obj_at'_real_def ko_wp_at'_def objBitsKO_def ps_clear_def)

lemma updateReply_replyTCB_invs':
  "\<lbrace>invs' and case_option \<top> (\<lambda>t. tcb_at' t) p and
    (\<lambda>s. is_reply_linked rptr s
         \<longrightarrow> (\<exists>tptr. p = Some tptr \<and> st_tcb_at' ((=) (BlockedOnReply (Some rptr))) tptr s))\<rbrace>
   updateReply rptr (replyTCB_update (\<lambda>_. p))
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wpsimp wp: updateReply_valid_objs' sym_heap_reply_pointers_lift
                    updateReply_valid_replies' updateReply_field_inv
              simp: invs'_def valid_pspace'_def valid_reply'_def
             split: option.split_asm)
   apply (auto simp: obj_at'_def opt_map_def)
  done

lemma replyPush'_valid_objs'[wp]:
  "\<lbrace>valid_objs' and reply_at' replyPtr and valid_bound_reply' headOpt\<rbrace>
   replyPush' scPtr replyPtr headOpt
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding replyPush'_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_if_lift2 hoare_vcg_const_imp_lift)

lemma replyPush_valid_objs'[wp]:
  "\<lbrace>valid_objs' and reply_at' replyPtr\<rbrace> replyPush scp replyPtr \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding replyPush_def
  apply wpsimp
  apply fastforce
  done

crunch updateSchedContext
  for obj_at'_reply[wp]: "\<lambda>s. Q (obj_at' (P :: reply \<Rightarrow> bool) replyPtr s)"
  and is_replyObject[wp]: "is_replyObject replyPtr"

lemma replyTCB_update_is_replyObject:
  "(\<And>reply. replyTCB (upd reply) = replyTCB reply)
   \<Longrightarrow> updateReply replyPtr upd \<lbrace>is_replyObject rptr\<rbrace>"
  apply (wpsimp wp: updateReply_wp)
  apply (fastforce simp: pred_tcb_at'_def obj_at'_def opt_map_red)
  done

lemma replyPush'_valid_replies'[wp]:
  "\<lbrace>valid_replies' and is_replyObject replyPtr and pspace_aligned' and pspace_distinct'\<rbrace>
   replyPush' scPtr replyPtr scReplyOpt
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  unfolding replyPush'_def replyPush'_asrt_def
  by (cases scReplyOpt; wpsimp wp: replyTCB_update_is_replyObject)

lemma replyPush'_sym_heap_reply_pointers:
  "\<lbrace>sym_heap_reply_pointers and not is_reply_linked replyPtr\<rbrace>
   replyPush' scPtr replyPtr scReplyOpt
   \<lbrace>\<lambda>_. sym_heap_reply_pointers\<rbrace>"
  unfolding replyPush'_def replyPush'_asrt_def
  by (cases scReplyOpt;
      wpsimp wp: updateReply_wp,
      fastforce simp: sym_heap_connect obj_at'_def fun_upd_swap opt_map_red opt_map_upd_triv
               split: if_splits)

lemma replyPush_valid_replies'[wp]:
  "\<lbrace>valid_replies' and is_replyObject replyPtr and pspace_aligned' and pspace_distinct'\<rbrace>
   replyPush scPtr replyPtr
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  unfolding replyPush_def
  by (wpsimp wp: replyTCB_update_is_replyObject)

lemma replyPush_sym_heap_reply_pointers:
  "\<lbrace>sym_heap_reply_pointers and not is_reply_linked replyPtr\<rbrace>
   replyPush scPtr replyPtr
   \<lbrace>\<lambda>_. sym_heap_reply_pointers\<rbrace>"
  unfolding replyPush_def
  by (wpsimp wp: replyPush'_sym_heap_reply_pointers
      | wpsimp wp: sym_heap_reply_pointers_lift updateReply_field_inv)+

end
