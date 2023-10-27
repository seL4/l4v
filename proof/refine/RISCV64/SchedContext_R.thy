(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory SchedContext_R
imports VSpace_R
begin

lemma live_sc'_scConsumed_update[simp]:
  "live_sc' (scConsumed_update f koc) = live_sc' koc"
  by (clarsimp simp: live_sc'_def)

lemma live_sc'_scRefills_update[simp]:
  "live_sc' (scRefills_update f koc) = live_sc' koc"
  by (clarsimp simp: live_sc'_def)

lemma live_sc'_scRefillTail_update[simp]:
  "live_sc' (scRefillTail_update f koc) = live_sc' koc"
  by (clarsimp simp: live_sc'_def)

lemma valid_sched_context'_updates[simp]:
  "\<And>f. valid_sched_context' sc' (ksReprogramTimer_update f s) = valid_sched_context' sc' s"
  "\<And>f. valid_sched_context' sc' (ksReleaseQueue_update f s) = valid_sched_context' sc' s"
  by (auto simp: valid_sched_context'_def valid_bound_obj'_def split: option.splits)

lemma refillSize_scConsumed_update[simp]:
  "refillSize (scConsumed_update f sc') = refillSize sc'"
  by (clarsimp simp: refillSize_def split: if_split)

lemma valid_sched_context'_scConsumed_update[simp]:
  "valid_sched_context' (scConsumed_update f ko) s = valid_sched_context' ko s"
  by (clarsimp simp: valid_sched_context'_def)

lemma valid_sched_context_size'_scConsumed_update[simp]:
  "valid_sched_context_size' (scConsumed_update f sc') = valid_sched_context_size' sc'"
  by (clarsimp simp: valid_sched_context_size'_def objBits_simps)

lemma readSchedContext_SomeD:
  "readSchedContext scp s = Some sc'
   \<Longrightarrow> ksPSpace s scp = Some (KOSchedContext sc')"
  by (clarsimp simp: readSchedContext_def asks_def obj_at'_def
              dest!: readObject_misc_ko_at')

lemma no_ofail_readSchedContext:
  "no_ofail (sc_at' p) (readSchedContext p)"
  unfolding readSchedContext_def by wpsimp

lemma sym_refs_tcbSchedContext:
  "\<lbrakk>ko_at' tcb tcbPtr s; sym_refs (state_refs_of' s); tcbSchedContext tcb = Some scPtr\<rbrakk>
   \<Longrightarrow> obj_at' (\<lambda>sc. scTCB sc = Some tcbPtr) scPtr s"
  apply (drule (1) sym_refs_obj_atD')
  apply (auto simp: state_refs_of'_def ko_wp_at'_def obj_at'_def refs_of_rev' tcb_bound_refs'_def)
  done

lemma setSchedContext_valid_idle'[wp]:
  "\<lbrace>valid_idle' and K (scPtr = idle_sc_ptr \<longrightarrow> idle_sc' v)\<rbrace>
   setSchedContext scPtr v
   \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (rule hoare_weaken_pre)
  apply (simp add: valid_idle'_def)
  apply (wpsimp simp: setSchedContext_def wp: setObject_ko_wp_at)
  apply (rule hoare_lift_Pf3[where f=ksIdleThread])
  apply (wpsimp wp: hoare_vcg_conj_lift)
   apply (wpsimp simp: obj_at'_real_def wp: setObject_ko_wp_at)
  apply wpsimp
  apply (wpsimp wp: updateObject_default_inv)
  by (auto simp: valid_idle'_def obj_at'_real_def ko_wp_at'_def)[1]

lemma setSchedContext_invs':
  "\<lbrace>invs'
    and (\<lambda>s. live_sc' sc \<longrightarrow> ex_nonz_cap_to' scPtr s)
    and valid_sched_context' sc
    and (\<lambda>_. valid_sched_context_size' sc)\<rbrace>
    setSchedContext scPtr sc
    \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_dom_schedule'_def)
  apply (wpsimp wp: untyped_ranges_zero_lift simp: cteCaps_of_def o_def)
  done

lemma setSchedContext_active_sc_at':
  "\<lbrace>active_sc_at' scPtr' and K (scPtr' = scPtr \<longrightarrow> 0 < scRefillMax sc)\<rbrace>
   setSchedContext scPtr sc
   \<lbrace>\<lambda>rv s. active_sc_at' scPtr' s\<rbrace>"
  apply (simp add: active_sc_at'_def obj_at'_real_def setSchedContext_def)
  apply (wpsimp wp: setObject_ko_wp_at)
  apply (clarsimp simp: ko_wp_at'_def obj_at'_real_def)
  done

lemma updateSchedContext_invs':
  "\<lbrace>invs'
    and (\<lambda>s. \<forall>ko. ko_at' ko scPtr s \<longrightarrow> live_sc' (f ko) \<longrightarrow> ex_nonz_cap_to' scPtr s)
    and (\<lambda>s. \<forall>ko. ko_at' ko scPtr s \<longrightarrow> valid_sched_context' (f ko) s
                                        \<and> valid_sched_context_size' (f ko))\<rbrace>
    updateSchedContext scPtr f
    \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: updateSchedContext_def)
  by (wpsimp wp: setSchedContext_invs')

lemma sym_refs_sc_trivial_update:
  "ko_at' ko scPtr s
   \<Longrightarrow> sym_refs (\<lambda>a. if a = scPtr
                   then get_refs SCNtfn (scNtfn ko) \<union>
                        get_refs SCTcb (scTCB ko) \<union>
                        get_refs SCYieldFrom (scYieldFrom ko) \<union>
                        get_refs SCReply (scReply ko)
                   else state_refs_of' s a)
       = sym_refs (state_refs_of' s)"
  apply (rule arg_cong[where f=sym_refs])
  apply (rule ext)
  by (clarsimp simp: state_refs_of'_def obj_at'_real_def ko_wp_at'_def)

lemma live_sc'_ko_ex_nonz_cap_to':
  "\<lbrakk>invs' s; ko_at' ko scPtr s\<rbrakk> \<Longrightarrow> live_sc' ko \<Longrightarrow> ex_nonz_cap_to' scPtr s"
  apply (drule invs_iflive')
  apply (erule if_live_then_nonz_capE')
  by (clarsimp simp: ko_wp_at'_def obj_at'_real_def)

lemma updateSchedContext_refills_invs':
  "\<lbrace>invs'
    and (\<lambda>s. \<forall>ko. ko_at' ko scPtr s \<longrightarrow> valid_sched_context' (f ko) s \<and> valid_sched_context_size' (f ko))
    and (\<lambda>_. \<forall>ko. scNtfn (f ko) = scNtfn ko)
    and (\<lambda>_. \<forall>ko. scTCB (f ko) = scTCB ko)
    and (\<lambda>_. \<forall>ko. scYieldFrom (f ko) = scYieldFrom ko)
    and (\<lambda>_. \<forall>ko. scReply (f ko) = scReply ko)\<rbrace>
    updateSchedContext scPtr f
    \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: updateSchedContext_def)
  apply (wpsimp wp: setSchedContext_invs')
  apply (erule (1) live_sc'_ko_ex_nonz_cap_to')
  apply (clarsimp simp: live_sc'_def)
  done

lemma updateSchedContext_active_sc_at':
  "\<lbrace>active_sc_at' scPtr'
    and (\<lambda>s. scPtr = scPtr' \<longrightarrow> (\<forall>ko. ko_at' ko scPtr s \<longrightarrow> 0 < scRefillMax ko \<longrightarrow> 0 < scRefillMax (f ko)))\<rbrace>
    updateSchedContext scPtr f
    \<lbrace>\<lambda>rv. active_sc_at' scPtr'\<rbrace>"
  apply (simp add: updateSchedContext_def)
  apply (wpsimp wp: setSchedContext_active_sc_at')
  apply (clarsimp simp: active_sc_at'_def obj_at'_real_def ko_wp_at'_def)
  done

lemma invs'_ko_at_valid_sched_context':
  "\<lbrakk>invs' s; ko_at' ko scPtr s\<rbrakk> \<Longrightarrow> valid_sched_context' ko s \<and> valid_sched_context_size' ko"
  apply (drule invs_valid_objs')
  apply (drule (1) sc_ko_at_valid_objs_valid_sc', simp)
  done

lemma ksPSpace_valid_sched_context':
  "\<lbrakk>ksPSpace s scPtr = Some (KOSchedContext sc); valid_objs' s\<rbrakk>
   \<Longrightarrow> valid_sched_context' sc s \<and> valid_sched_context_size' sc"
  by (fastforce simp: valid_objs'_def valid_obj'_def split: kernel_object.splits)

lemma updateSchedContext_invs'_indep:
  "\<lbrace>invs'
    and (\<lambda>s. \<forall>ko. valid_sched_context' ko s \<longrightarrow> valid_sched_context' (f ko) s)
    and (\<lambda>_. \<forall>ko. valid_sched_context_size' ko \<longrightarrow> valid_sched_context_size' (f ko))
    and (\<lambda>s. \<forall>ko. scNtfn (f ko) = scNtfn ko
                  \<and> scTCB (f ko) = scTCB ko
                  \<and> scYieldFrom (f ko) = scYieldFrom ko
                  \<and> scReply (f ko) = scReply ko )\<rbrace>
    updateSchedContext scPtr f
    \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wpsimp wp: updateSchedContext_invs')
  apply (intro conjI; intro allI impI; (drule_tac x=ko in spec)+)
   apply (clarsimp simp: invs'_def valid_objs'_def obj_at'_def)
   apply (erule if_live_then_nonz_capE')
   apply (clarsimp simp: ko_wp_at'_def live_sc'_def)
  apply (frule (1) invs'_ko_at_valid_sched_context', simp)
  done

context begin interpretation Arch . (*FIXME: arch_split*)

lemma schedContextUpdateConsumed_corres:
 "corres (=) (sc_at scp) (sc_at' scp)
            (sched_context_update_consumed scp)
            (schedContextUpdateConsumed scp)"
  apply (clarsimp simp: sched_context_update_consumed_def schedContextUpdateConsumed_def)
  apply (simp add: maxTicksToUs_def ticksToUs_def)
  apply (rule corres_underlying_split[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corresKsimp corres: get_sc_corres)
  apply (rename_tac abs_sc conc_sc)
  apply (rule corres_if_split)
    apply (clarsimp simp: sc_relation_def)
   apply (rule corres_underlying_split)
      apply (rule corres_guard_imp)
        apply clarsimp
        apply (rule_tac f="\<lambda>sc. sc\<lparr>sc_consumed := sc_consumed abs_sc - max_ticks_to_us\<rparr>"
                    and f'="\<lambda>sc'. scConsumed_update (\<lambda>_. scConsumed conc_sc - maxTicksToUs) sc'"
                     in setSchedContext_update_sched_context_no_stack_update_corres)
           apply (clarsimp simp: sc_relation_def maxTicksToUs_def)
          apply (clarsimp simp: sc_relation_def)
         apply (clarsimp simp: sc_relation_def objBits_simps)
        apply (clarsimp simp: sc_relation_def)
       apply (clarsimp simp: obj_at_def)
      apply (clarsimp simp: obj_at_simps)
     apply (clarsimp simp: maxTicksToUs_def ticksToUs_def)
    apply wpsimp
   apply wpsimp
  apply (rule corres_underlying_split)
     apply (rule corres_guard_imp)
       apply clarsimp
       apply (rule_tac f="\<lambda>sc. sc\<lparr>sc_consumed := 0\<rparr>"
                   and f'="\<lambda>sc'. scConsumed_update (\<lambda>_. 0) sc'"
                    in setSchedContext_update_sched_context_no_stack_update_corres)
          apply (clarsimp simp: sc_relation_def maxTicksToUs_def)
         apply (clarsimp simp: sc_relation_def)
        apply (clarsimp simp: sc_relation_def objBits_simps)
       apply (clarsimp simp: sc_relation_def)
      apply (clarsimp simp: obj_at_def)
     apply (clarsimp simp: obj_at_simps)
    apply (clarsimp simp: maxTicksToUs_def ticksToUs_def sc_relation_def)
   apply wpsimp
  apply wpsimp
  done

end

crunches sched_context_update_consumed
  for in_user_Frame[wp]: "in_user_frame buffer"

lemma schedContextUpdateConsumed_valid_ipc_buffer_ptr'[wp]:
  "schedContextUpdateConsumed scp \<lbrace>valid_ipc_buffer_ptr' x\<rbrace>"
  unfolding schedContextUpdateConsumed_def valid_ipc_buffer_ptr'_def
  by wpsimp

lemma schedContextUpdateConsumed_iflive[wp]:
  "schedContextUpdateConsumed scp \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (wpsimp simp: schedContextUpdateConsumed_def)
  apply (clarsimp elim!: if_live_then_nonz_capE' simp: obj_at'_def ko_wp_at'_def)
  done

lemma schedContextUpdateConsumed_valid_idle'[wp]:
  "schedContextUpdateConsumed scp \<lbrace>valid_idle'\<rbrace>"
  apply (wpsimp simp: schedContextUpdateConsumed_def)
  apply (clarsimp simp: valid_idle'_def obj_at'_def)
  done

lemma schedContextUpdateConsumed_state_refs_of:
  "schedContextUpdateConsumed sc \<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>"
  unfolding schedContextUpdateConsumed_def
  apply wpsimp
  apply (clarsimp dest!: ko_at_state_refs_ofD' elim!: rsubst[where P=P])
  apply (rule ext; clarsimp)
  done

lemma schedContextUpdateConsumed_objs'[wp]:
  "schedContextUpdateConsumed sc \<lbrace>valid_objs'\<rbrace>"
  unfolding schedContextUpdateConsumed_def
  apply wpsimp
  apply (drule (1) ko_at_valid_objs'_pre)
  apply (clarsimp simp: valid_obj'_def valid_sched_context'_def valid_sched_context_size'_def)
  done

lemma schedContextUpdateConsumed_sym_refs_lis_refs_of_replies'[wp]:
  "schedContextUpdateConsumed scPtr \<lbrace>\<lambda>s. sym_refs (list_refs_of_replies' s)\<rbrace>"
  apply (clarsimp simp: schedContextUpdateConsumed_def)
  apply wpsimp
  apply (clarsimp simp: opt_map_def o_def)
  done

crunches schedContextUpdateConsumed
  for aligned'[wp]: "pspace_aligned'"
  and distinct'[wp]:"pspace_distinct'"
  and bounded'[wp]: "pspace_bounded'"
  and pspace_canonical'[wp]: pspace_canonical'
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  and it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and no_0_obj'[wp]: no_0_obj'
  and valid_mdb'[wp]: valid_mdb'
  and sch_act_wf[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  and valid_global_refs'[wp]: valid_global_refs'
  and valid_arch_state'[wp]: valid_arch_state'
  and interrupt_state[wp]: "\<lambda>s. P (ksInterruptState s)"
  and valid_irq_state'[wp]: valid_irq_states'
  and valid_machine_state'[wp]: valid_machine_state'
  and valid_queues'[wp]: valid_queues'
  and ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  and valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'
  and ct_not_inQ[wp]: ct_not_inQ
  and valid_queues[wp]: valid_queues
  and ksQ[wp]: "\<lambda>s. P (ksReadyQueues s p)"
  and reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and valid_replies' [wp]: valid_replies'
  and st_tcb_at'[wp]: "\<lambda>s. P (st_tcb_at' P' t s)"
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  (wp: crunch_wps simp: crunch_simps)

global_interpretation schedContextUpdateConsumed: typ_at_all_props' "schedContextUpdateConsumed scPtr"
  by typ_at_props'

lemma schedContextUpdateConsumed_if_unsafe_then_cap'[wp]:
  "schedContextUpdateConsumed scPtr \<lbrace>if_unsafe_then_cap'\<rbrace>"
  apply (clarsimp simp: schedContextUpdateConsumed_def)
  apply (wpsimp wp: threadSet_ifunsafe' threadGet_wp)
  done

lemma schedContextUpdateConsumed_invs'[wp]:
  "schedContextUpdateConsumed scPtr \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_pspace'_def valid_dom_schedule'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift cur_tcb_lift
                    untyped_ranges_zero_lift
              simp: cteCaps_of_def o_def)
  done

(* FIXME RT: should other update wp rules for valid_objs/valid_objs' be in this form?
   The following might be nicer:
   \<forall>sc'. scs_of' s scp = Some sc' \<longrightarrow> valid_obj' (injectKO sc') s
         \<longrightarrow> valid_obj' (injectKO (f' sc') s) *)
lemma updateSchedContext_valid_objs'[wp]:
  "\<lbrace>valid_objs' and
    (\<lambda>s. ((\<lambda>sc'. valid_obj' (injectKO sc') s \<longrightarrow> valid_obj' (injectKO (f' sc')) s)
              |< scs_of' s) scp)\<rbrace>
   updateSchedContext scp f'
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wpsimp simp: updateSchedContext_def wp: set_sc'.valid_objs')
  by (fastforce simp: valid_obj'_def valid_sched_context'_def valid_sched_context_size'_def
                      obj_at'_def scBits_simps objBits_simps opt_map_red opt_pred_def)

lemma valid_tcb'_tcbYieldTo_update:
  "valid_tcb' tcb s \<Longrightarrow> valid_tcb' (tcbYieldTo_update Map.empty tcb) s"
  by (simp add: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def )

lemma schedContextCancelYieldTo_valid_objs'[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>valid_objs'\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def)
  apply (wpsimp wp: threadSet_valid_objs' hoare_vcg_all_lift threadGet_wp
         | strengthen valid_tcb'_tcbYieldTo_update)+
  apply normalise_obj_at'
  apply (rename_tac ko)
  apply (rule_tac x=ko in exI)
  apply clarsimp
  apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
  by (fastforce simp: valid_obj'_def opt_map_def obj_at_simps valid_tcb'_def refillSize_def
                      valid_sched_context'_def valid_sched_context_size'_def opt_pred_def)

lemma schedContextCancelYieldTo_valid_mdb'[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>valid_mdb'\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def updateSchedContext_def threadSet_def)
  apply (wpsimp wp: getObject_tcb_wp hoare_drop_imps hoare_vcg_ex_lift threadGet_wp)
  apply (fastforce simp: obj_at'_def tcb_cte_cases_def cteSizeBits_def)
  done

lemma schedContextCancelYieldTo_sch_act_wf[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def updateSchedContext_def)
  apply (wpsimp wp: threadSet_sch_act threadGet_wp)
  apply (fastforce simp: obj_at'_def)
  done

lemma schedContextCancelYieldTo_if_live_then_nonz_cap'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s\<rbrace>
   schedContextCancelYieldTo tptr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def updateSchedContext_def)
  apply (wpsimp wp: threadSet_iflive' setSchedContext_iflive' hoare_vcg_imp_lift' hoare_vcg_all_lift
                    threadGet_wp)
  by (fastforce elim: if_live_then_nonz_capE'
                simp: ko_wp_at'_def obj_at'_def live_sc'_def)

lemma schedContextCancelYieldTo_if_unsafe_then_cap'[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>if_unsafe_then_cap'\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def updateSchedContext_def)
  apply (wpsimp wp: threadSet_ifunsafe' threadGet_wp)
  apply (fastforce simp: obj_at'_def)
  done

lemma schedContextCancelYieldTo_valid_idle'[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>valid_idle'\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def updateSchedContext_def)
  apply (wpsimp wp: threadSet_idle' setObject_sc_idle' updateObject_default_inv
                    threadGet_wp hoare_vcg_imp_lift' hoare_vcg_all_lift)
  apply (fastforce simp: valid_idle'_def obj_at'_def idle_tcb'_def)
  done

lemma schedContextCancelYieldTo_valid_release_queue[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>valid_release_queue\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def updateSchedContext_def)
  apply (wpsimp wp: threadSet_valid_release_queue threadGet_wp)
  apply (fastforce simp: obj_at'_def)
  done

lemma schedContextCancelYieldTo_ct_not_inQ[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>ct_not_inQ\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def updateSchedContext_def)
  apply (wpsimp wp: threadSet_not_inQ threadGet_wp)
  apply (fastforce simp: obj_at'_def)
  done

lemma schedContextCancelYieldTo_cur_tcb'[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>cur_tcb'\<rbrace>"
  apply (wpsimp simp: schedContextCancelYieldTo_def updateSchedContext_def
                  wp: threadSet_cur threadGet_wp)
  apply (fastforce simp: obj_at'_def)
  done

lemma schedContextCancelYeldTo_valid_release_queue'[wp]:
  "schedContextCancelYieldTo t \<lbrace>valid_release_queue'\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def updateSchedContext_def)
  apply (rule hoare_seq_ext[OF _ threadGet_sp])
  apply (rule hoare_when_cases; (solves \<open>wpsimp\<close>)?)
  apply (rule_tac B="\<lambda>_. valid_release_queue'" in hoare_seq_ext[rotated])
   apply wpsimp
  apply (wpsimp wp: threadSet_valid_release_queue' setObject_tcb_wp)
  apply (clarsimp simp: valid_release_queue'_def obj_at'_def)
  done

crunches schedContextCancelYieldTo
  for pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and pspace_bounded'[wp]: pspace_bounded'
  and pspace_canonical'[wp]: pspace_canonical'
  and no_0_obj'[wp]: no_0_obj'
  and ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and list_refs_of_replies[wp]: "\<lambda>s. sym_refs (list_refs_of_replies' s)"
  and valid_global_refs'[wp]: valid_global_refs'
  and valid_arch_state'[wp]: valid_arch_state'
  and irq_node[wp]: "\<lambda>s. P (irq_node' s)"
  and typ_at[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
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
  and reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and valid_replies' [wp]: valid_replies'
  and st_tcb_at'[wp]: "\<lambda>s. P (st_tcb_at' P' t s)"
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  (wp: crunch_wps threadSet_pred_tcb_no_state simp: crunch_simps updateSchedContext_def comp_def)

global_interpretation schedContextCancelYieldTo: typ_at_all_props' "schedContextCancelYieldTo t"
  by typ_at_props'

lemma schedContextCancelYieldTo_invs':
  "schedContextCancelYieldTo t \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_pspace'_def setSchedContext_def valid_dom_schedule'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
                    untyped_ranges_zero_lift
              simp: cteCaps_of_def o_def)
  apply (fastforce simp: inQ_def valid_queues_def valid_queues_no_bitmap_def)
  done

crunches schedContextCompleteYieldTo
  for ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and tcb_at'[wp]: "\<lambda>s. Q (tcb_at' t s)"
  (simp: crunch_simps wp: crunch_wps)

crunches setConsumed
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
  (wp: crunch_wps simp: crunch_simps)

lemma setConsumed_invs':
  "setConsumed scp buffer \<lbrace>invs'\<rbrace>"
  apply (simp add: setConsumed_def cur_tcb'_asrt_def)
  apply (wpsimp wp: schedContextUpdateConsumed_invs'
              simp: cur_tcb'_def
         | wps)+
  done

lemma schedContextCompleteYieldTo_invs'[wp]:
  "schedContextCompleteYieldTo thread \<lbrace>invs'\<rbrace>"
  unfolding schedContextCompleteYieldTo_def
  by (wpsimp wp: schedContextCancelYieldTo_invs' setConsumed_invs'
                 hoare_drop_imp hoare_vcg_if_lift2
           simp: sch_act_simple_def)

lemma setConsumed_corres:
 "corres dc (case_option \<top> in_user_frame buf and sc_at scp
             and cur_tcb and pspace_aligned and pspace_distinct)
            (case_option \<top> valid_ipc_buffer_ptr' buf and sc_at' scp)
            (set_consumed scp buf)
            (setConsumed scp buf)"
  apply add_cur_tcb'
  apply (simp add: set_consumed_def setConsumed_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (clarsimp simp: cur_tcb'_asrt_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF schedContextUpdateConsumed_corres])
      apply (rule corres_split[OF getCurThread_corres], simp)
        apply (rule corres_split[OF setMRs_corres setMessageInfo_corres])
  by (wpsimp wp: hoare_case_option_wp simp: setTimeArg_def cur_tcb_def cur_tcb'_def | wps)+

lemma get_tcb_yield_to_corres:
  "corres (=) (pspace_aligned and pspace_distinct and tcb_at t) \<top>
          (get_tcb_obj_ref tcb_yield_to t) (threadGet tcbYieldTo t)"
  apply (rule_tac Q="tcb_at' t" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: tcb_at_cross)
  apply (simp add: get_tcb_obj_ref_def getBoundNotification_def)
  apply (rule corres_guard_imp)
    apply (rule threadGet_corres)
    apply (simp add: tcb_relation_def)+
  done

lemma tcb_yield_to_update_corres:
  "corres dc (pspace_aligned and pspace_distinct and tcb_at t) \<top>
          (set_tcb_obj_ref tcb_yield_to_update t yt) (threadSet (tcbYieldTo_update (\<lambda>_. yt)) t)"
  apply (rule_tac Q="tcb_at' t" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: tcb_at_cross)
  apply (rule corres_guard_imp)
    apply (rule set_tcb_obj_ref_corres; simp add: tcb_relation_def)
   apply simp+
  done

lemma sc_relation_tcb_yield_to_update:
  "sc_relation sc n sc'
   \<Longrightarrow> sc_relation (sc_yield_from_update Map.empty (sc)) n (scYieldFrom_update Map.empty sc')"
  by (clarsimp simp: sc_relation_def refillSize_def)

lemma schedContextCancelYieldTo_corres:
  "corres dc
          (pspace_aligned and pspace_distinct and valid_objs and tcb_at t)
          \<top>
          (sched_context_cancel_yield_to t)
          (schedContextCancelYieldTo t)" (is "corres _ ?abs_guard _ _ _")
  apply (rule_tac Q="tcb_at' t" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: tcb_at_cross)
  apply (clarsimp simp: sched_context_cancel_yield_to_def schedContextCancelYieldTo_def
                        updateSchedContext_def maybeM_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF get_tcb_yield_to_corres _ gyt_sp threadGet_sp
                             , where Q="?abs_guard"])
    defer
    apply (simp add: obj_at_def is_tcb_def)
   apply simp
  apply (case_tac scPtrOpt; clarsimp?)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF update_sc_no_reply_stack_update_corres])
          apply (simp add: sc_relation_tcb_yield_to_update)
         apply simp
        apply (clarsimp simp: objBits_simps')
       apply simp
      apply (rule tcb_yield_to_update_corres)
     apply wpsimp
    apply wpsimp
   apply (clarsimp simp: valid_objs_def obj_at_def is_tcb_def)
   apply (fastforce simp: valid_obj_def valid_tcb_def valid_bound_obj_def pred_tcb_at_def obj_at_def
                   dest!: bspec
                   split: option.splits)
  apply clarsimp
  done

lemma schedContextCompleteYieldTo_corres:
  "corres dc (invs and tcb_at thread) (invs' and tcb_at' thread)
    (complete_yield_to thread) (schedContextCompleteYieldTo thread)"
  apply add_cur_tcb'
  apply (simp add: complete_yield_to_def schedContextCompleteYieldTo_def)
  apply (subst maybeM_when)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF get_tcb_yield_to_corres], simp)
      apply (rule corres_when2[OF refl])
      apply (clarsimp, wpfix)
      apply (rule corres_split[OF lookupIPCBuffer_corres], simp)
        apply (rule corres_split[OF setConsumed_corres])
          apply (rule schedContextCancelYieldTo_corres[simplified dc_def])
         apply wpsimp
        apply wpsimp
       apply wpsimp
      apply wpsimp
     apply (wpsimp wp: get_tcb_obj_ref_wp)
    apply (wpsimp wp: threadGet_wp)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def cur_tcb_def)
   apply (subgoal_tac "valid_tcb thread tcb s", clarsimp simp: valid_tcb_def)
   apply (fastforce simp: obj_at'_def valid_tcb_valid_obj elim: valid_objs_ko_at
                    dest: invs_valid_objs)
  apply (clarsimp simp: invs'_def valid_pspace'_def cur_tcb'_def
                        obj_at'_real_def ko_wp_at'_def pred_tcb_at'_def)
  apply (subgoal_tac "valid_tcb' obj s", clarsimp simp: valid_tcb'_def cur_tcb'_def)
   apply (fastforce simp: obj_at'_real_def ko_wp_at'_def)
  apply (fastforce simp: valid_objs'_def valid_obj'_def)
  done

crunches schedContextDonate
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"

global_interpretation schedContextDonate: typ_at_all_props' "schedContextDonate scPtr tcbPtr"
  by typ_at_props'

crunches schedContextDonate
  for aligned'[wp]: "pspace_aligned'"
  and distinct'[wp]:"pspace_distinct'"
  and it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and ksCurDomain[wp]:  "\<lambda>s. P (ksCurDomain s)"
  and ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and cte_wp_at'[wp]: "cte_wp_at' P p"

crunches schedContextDonate
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"

crunches schedContextDonate, schedContextUnbindAllTCBs, unbindFromSC,
         schedContextSetInactive, schedContextUnbindYieldFrom, schedContextUnbindReply
  for st_tcb_at'[wp]: "\<lambda>s. P (st_tcb_at' P' p s)"
  (simp: crunch_simps wp: threadSet_pred_tcb_no_state crunch_wps)

lemma setSchedContext_ct_in_state'[wp]:
  "setSchedContext ptr sc \<lbrace>ct_in_state' P\<rbrace>"
  by (rule ct_in_state_thread_state_lift'; wpsimp)

crunches setSchedContext
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (wp: weak_sch_act_wf_lift)

lemma schedContextDonate_weak_sch_act_wf[wp]:
  "schedContextDonate scPtr tcbPtr \<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp only: schedContextDonate_def)
  apply (wpsimp wp: threadSet_weak_sch_act_wf)
         apply (rule_tac Q="\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s" in hoare_strengthen_post[rotated], fastforce)
         apply (wpsimp wp: threadSet_weak_sch_act_wf)
        apply wpsimp+
  done

lemma schedContextDonate_valid_objs':
  "\<lbrace>valid_objs' and tcb_at' tcbPtr\<rbrace>
   schedContextDonate scPtr tcbPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  (is "valid ?pre _ _")
  apply (clarsimp simp: schedContextDonate_def)
  apply (rule hoare_seq_ext[OF _ get_sc_sp'], rename_tac sc)
  apply (rule_tac Q="?pre and valid_sched_context' sc and K (valid_sched_context_size' sc) and sc_at' scPtr"
               in hoare_weaken_pre[rotated])
   apply (fastforce simp: sc_ko_at_valid_objs_valid_sc' obj_at'_def)
  apply (rule hoare_seq_ext_skip)
   apply (rule hoare_when_cases, clarsimp)
   apply (rule hoare_seq_ext_skip, wpsimp wp: tcbSchedDequeue_valid_objs')
   apply (rule hoare_seq_ext_skip, wpsimp)
   apply (rule hoare_seq_ext_skip, wpsimp wp: threadSet_valid_objs')
    apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
   apply wpsimp
  apply (rule_tac B="\<lambda>_. ?pre and sc_at' scPtr" in hoare_seq_ext[rotated])
   apply (wpsimp wp: set_sc_valid_objs')
   apply (clarsimp simp: valid_sched_context'_def valid_sched_context_size'_def
                         sc_size_bounds_def objBits_def objBitsKO_def refillSize_def
                  split: if_splits)
  apply (wpsimp wp: threadSet_valid_objs')
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

lemma tcbReleaseRemove_list_refs_of_replies'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>\<lambda>s. P (list_refs_of_replies' s)\<rbrace>"
  by (wpsimp simp: tcbReleaseRemove_def)

lemma schedContextDonate_list_refs_of_replies' [wp]:
  "schedContextDonate scPtr tcbPtr \<lbrace>\<lambda>s. P (list_refs_of_replies' s)\<rbrace>"
  unfolding schedContextDonate_def
  by (wpsimp simp: comp_def | rule hoare_strengthen_post[where Q="\<lambda>_ s. P (list_refs_of_replies' s)"])+

lemma schedContextDonate_sch_act_wf [wp]:
  "schedContextDonate scPtr tcbPtr \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp only: schedContextDonate_def)
  apply (wpsimp wp: threadSet_sch_act threadSet_wp)
       apply (rule_tac Q="\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s" in hoare_strengthen_post[rotated])
        apply (fastforce simp: sch_act_wf_def ct_in_state'_def tcb_in_cur_domain'_def
                               pred_tcb_at'_def obj_at'_def
                        split: if_splits)
       apply wpsimp+
  done

lemma schedContextDonate_valid_idle':
  "\<lbrace>\<lambda>s. valid_idle' s \<and> tcbPtr \<noteq> idle_thread_ptr \<and>
        obj_at' (\<lambda>sc. scTCB sc \<noteq> Some idle_thread_ptr) scPtr s\<rbrace>
   schedContextDonate scPtr tcbPtr
   \<lbrace>\<lambda>_. valid_idle'\<rbrace>"
  apply (simp only: schedContextDonate_def)
  apply (wp threadSet_idle' setSchedContext_valid_idle')
       apply (rule_tac Q="\<lambda>_ s. tcbPtr \<noteq> ksIdleThread s" in hoare_strengthen_post; wpsimp)
      apply (rule_tac Q="\<lambda>_ s. valid_idle' s \<and> scPtr \<noteq> idle_sc_ptr \<and> tcbPtr \<noteq> ksIdleThread s"
                   in hoare_strengthen_post; wpsimp)
         apply (wpsimp wp: threadSet_idle' hoare_drop_imps threadSet_idle')
        apply (rule_tac Q="\<lambda>_ s. valid_idle' s \<and> scPtr \<noteq> idle_sc_ptr \<and>
                                 tcbPtr \<noteq> ksIdleThread s \<and> from \<noteq> ksIdleThread s"
                     in hoare_strengthen_post)
         apply wpsimp+
  apply (auto simp: obj_at'_def valid_idle'_def)
  done

lemma schedContextDonate_bound_tcb_sc_at[wp]:
  "\<lbrace>\<top>\<rbrace> schedContextDonate scPtr tcbPtr \<lbrace>\<lambda>_. obj_at' (\<lambda>a. \<exists>y. scTCB a = Some y) scPtr\<rbrace>"
   unfolding schedContextDonate_def
   by (wpsimp wp: set_sc'.obj_at')

lemma updateSchedContext_obj_at'[wp]:
  "\<forall>sc'. objBits sc' = objBits (f' sc'::sched_context) \<Longrightarrow>
   updateSchedContext scp f' \<lbrace>\<lambda>s. P (sc_at' p s)\<rbrace>"
  apply (wpsimp simp: updateSchedContext_def wp: set_sc'.set_wp)
  apply (clarsimp simp: obj_at'_def ps_clear_upd objBits_simps)
  done

(* corres rules for updateRefillHd / updateRefillTl *)

(* using the abstract side size *)
lemma state_relation_sc_relation:
  "\<lbrakk>(s, s') \<in> state_relation; sc_at ptr s; sc_at' ptr s'\<rbrakk> \<Longrightarrow>
   sc_relation (the ((scs_of2 s) ptr)) (obj_bits (the (kheap s ptr)) - min_sched_context_bits) (the ((scs_of' s') ptr))"
  supply projection_rewrites[simp]
  apply (clarsimp simp: obj_at_simps is_sc_obj)
  apply (drule (1) pspace_relation_absD[OF _ state_relation_pspace_relation, rotated])
  by (clarsimp simp: sc_relation_def scBits_simps opt_map_red)

(* using the concrete side size *)
lemma state_relation_sc_relation':
  "\<lbrakk>(s, s') \<in> state_relation; sc_at ptr s; sc_at' ptr s'\<rbrakk> \<Longrightarrow>
   sc_relation (the ((scs_of2 s) ptr)) (objBits (the (scs_of' s' ptr)) - minSchedContextBits) (the ((scs_of' s') ptr))"
  supply projection_rewrites[simp]
  apply (clarsimp simp: obj_at_simps is_sc_obj)
  apply (drule (1) pspace_relation_absD[OF _ state_relation_pspace_relation, rotated])
  by (clarsimp simp: sc_relation_def scBits_simps opt_map_red)

lemma state_relation_sc_replies_relation_sc:
  "\<lbrakk>(s, s') \<in> state_relation; sc_at ptr s; sc_at' ptr s'\<rbrakk>
   \<Longrightarrow> heap_ls (replyPrevs_of s') (scReplies_of s' ptr) (sc_replies (the ((scs_of2 s) ptr)))"
  supply projection_rewrites[simp] opt_map_red[simp]
  apply (clarsimp simp: obj_at_simps is_sc_obj)
  by (fastforce dest!: sc_replies_relation_prevs_list[OF state_relation_sc_replies_relation])

lemma sc_relation_updateRefillHd:
  "\<lbrakk>sc_relation sc n sc'; \<forall>refill'. f (refill_map refill') = refill_map (f' refill');
    sc_valid_refills' sc'\<rbrakk>
   \<Longrightarrow> sc_relation (sc_refills_update (\<lambda>refills. f (hd refills) # tl refills) sc) n
                   (scRefills_update (\<lambda>_. updateAt (scRefillHead sc') (scRefills sc') f') sc')"
  apply (prop_tac "wrap_slice (scRefillHead sc') (refillSize sc') (scRefillMax sc') (scRefills sc') \<noteq> []")
   apply (clarsimp intro!: neq_Nil_lengthI simp: refillSize_def split: if_splits)
  apply (clarsimp simp: sc_relation_def refills_map_def tl_map hd_map)
  apply (subst hd_Cons_tl[where xs="wrap_slice _ _ _ (updateAt _ _ _)", symmetric])
   apply (clarsimp intro!: neq_Nil_lengthI simp: refillSize_def split: if_splits)
  apply simp
  apply (subst hd_wrap_slice; (simp add: updateAt_index tl_wrap_slice neq_Nil_lengthI refillSize_def)?)+
  apply (case_tac "Suc (scRefillHead sc') < scRefillMax sc'")
   apply (prop_tac "wrap_slice (Suc (scRefillHead sc')) (refillSize sc' - Suc 0)
                 (scRefillMax sc') (updateAt (scRefillHead sc') (scRefills sc') f')
          = wrap_slice (Suc (scRefillHead sc')) (refillSize sc' - Suc 0) (scRefillMax sc') (scRefills sc')")
    apply (subst wrap_slice_updateAt_eq[symmetric]; clarsimp)
     apply (fastforce simp: neq_Nil_lengthI refillSize_def)+
  apply (clarsimp simp: not_less le_eq_less_or_eq[where m="scRefillMax sc'" for sc'])
  done

lemma updateRefillHd_corres:
  "\<lbrakk>sc_ptr = scPtr;
    \<forall>refill refill'. refill = refill_map refill' \<longrightarrow> f refill = refill_map (f' refill')\<rbrakk>
   \<Longrightarrow> corres dc
        (sc_at sc_ptr)
        (valid_refills' sc_ptr and sc_at' sc_ptr)
        (update_refill_hd sc_ptr f)
        (updateRefillHd scPtr f')"
  apply (clarsimp simp: update_refill_hd_def updateRefillHd_def)
  apply (rule corres_guard_imp)
    apply (rule updateSchedContext_no_stack_update_corres_Q[where Q=\<top> and Q'="sc_valid_refills'"])
      apply (fastforce simp: is_sc_obj obj_at_simps opt_map_red opt_pred_def valid_refills'_def
                      elim!: sc_relation_updateRefillHd)
      apply fastforce
     apply (fastforce simp: obj_at_simps)
    apply fastforce
   apply (fastforce simp: obj_at_simps is_sc_obj )
  apply (clarsimp simp: valid_refills'_def in_omonad obj_at'_def)
  done

lemma sc_relation_updateRefillTl:
  "\<lbrakk> sc_relation sc n sc'; \<forall>refill'. f (refill_map refill') = refill_map (f' refill');
        sc_valid_refills' sc'\<rbrakk>
       \<Longrightarrow> sc_relation
            (sc_refills_update (\<lambda>refills. butlast refills @ [f (last refills)]) sc) n
            (scRefills_update (\<lambda>_. updateAt (scRefillTail sc') (scRefills sc') f') sc')"
  apply (prop_tac "scRefills sc' \<noteq> []")
   apply fastforce
  apply (clarsimp simp: sc_relation_def refills_map_def)
  apply (simp add: snoc_eq_iff_butlast)
  apply (prop_tac "wrap_slice (scRefillHead sc') (refillSize sc') (scRefillMax sc')
                              (scRefills sc') \<noteq> []")
   apply (clarsimp intro!: neq_Nil_lengthI simp: refillSize_def split: if_splits)
  apply (prop_tac "wrap_slice (scRefillHead sc') (refillSize sc') (scRefillMax sc')
                              (updateAt (scRefillTail sc') (scRefills sc') f') \<noteq> []")
   apply (clarsimp intro!: neq_Nil_lengthI simp: refillSize_def split: if_splits)
  apply (prop_tac "wrap_slice (scRefillHead sc') (refillSize sc' - Suc 0)
             (scRefillMax sc')
             (updateAt (scRefillTail sc') (scRefills sc') f') = wrap_slice (scRefillHead sc')
                       (refillSize sc' - Suc 0)
             (scRefillMax sc')
             (scRefills sc')")
   apply (subst wrap_slice_updateAt_eq[symmetric];
          (simp add: Let_def refillSize_def split: if_split_asm)?)
  apply (intro conjI impI)
    apply (clarsimp simp: refillSize_def split: if_splits)
   apply (clarsimp simp: butlast_map butlast_wrap_slice refillSize_def split: if_splits)
  apply (clarsimp simp: last_map refillSize_def split: if_splits)
   apply (fastforce simp: last_wrap_slice updateAt_index)
  apply (fastforce simp: last_wrap_slice updateAt_index)
  done

lemma updateRefillTl_corres:
  "\<lbrakk>sc_ptr = scPtr;
    \<forall>refill refill'. refill = refill_map refill' \<longrightarrow> f refill = (refill_map (f' refill'))\<rbrakk>
   \<Longrightarrow> corres dc
              (sc_at sc_ptr)
              (sc_at' scPtr and valid_refills' scPtr)
              (update_refill_tl sc_ptr f)
              (updateRefillTl scPtr f')"
  apply (clarsimp simp: update_refill_tl_def updateRefillTl_def)
  apply (rule corres_guard_imp)
    apply (rule updateSchedContext_no_stack_update_corres_Q[where Q=\<top> and Q'="sc_valid_refills'"])
       apply (clarsimp simp: is_sc_obj obj_at_simps is_active_sc'_def valid_refills'_def
                             sc_relation_updateRefillTl)
      apply fastforce
     apply (fastforce simp: obj_at_simps)
    apply fastforce
   apply (fastforce simp: obj_at_simps is_sc_obj)
  apply (clarsimp simp: valid_refills'_def in_omonad obj_at'_def)
  done

lemma readRefillReady_no_ofail[wp]:
  "no_ofail (sc_at' t) (readRefillReady t)"
  apply (clarsimp simp: readRefillReady_def readSchedContext_def)
  apply (wpsimp wp: no_ofail_readCurTime)
  done

context begin interpretation Arch . (*FIXME: arch_split*)

lemma get_sc_released_corres:
  "corres (=) (active_scs_valid and sc_at sc_ptr) (valid_objs' and sc_at' sc_ptr)
          (get_sc_released sc_ptr) (scReleased sc_ptr)"
  apply (simp add: get_sc_released_def read_sc_released_def read_sched_context_get_sched_context
                   scReleased_def scActive_def refillReady_def gets_the_ogets)
  apply (rule corres_underlying_split[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corresKsimp corres: get_sc_corres)
  apply (rename_tac sc sc')
  apply (rule corres_symb_exec_l[rotated 2, OF gets_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[rotated, OF gets_the_sp]; (solves wpsimp)?)
   apply (wpsimp wp: no_ofail_gets_the readRefillReady_no_ofail)
  apply (clarsimp simp: sc_released_def readRefillReady_def readSchedContext_def
                 dest!: readObject_misc_ko_at')
  apply normalise_obj_at'
  apply (rename_tac sc' current_time)
  apply (subgoal_tac "sc_active sc = (0 < scRefillMax sc')")
   apply (case_tac "sc_active sc"; clarsimp)
   apply (drule active_scs_validE[where scp=sc_ptr, rotated])
    apply (clarsimp simp: is_active_sc_def sc_at_ppred_def obj_at_def)
   apply (drule_tac s'=s' in refill_hd_relation2)
      apply (fastforce simp: refill_ready_def refill_sufficient_def refill_capacity_def
                             kernelWCETTicks_def vs_all_heap_simps cfg_valid_refills_def
                             rr_valid_refills_def sp_valid_refills_def obj_at_def
                             valid_obj'_def obj_at'_def readCurTime_def ogets_def
                             state_relation_def
                      dest!: readObject_ko_at'_sc
                      split: if_splits)+
  apply (clarsimp simp: refill_ready_def readCurTime_def ogets_def sc_relation_def active_sc_def)
  done

end

end
