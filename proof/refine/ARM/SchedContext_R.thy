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

lemma live_sc'_scRefillCount_update[simp]:
  "live_sc' (scRefillCount_update f koc) = live_sc' koc"
  by (clarsimp simp: live_sc'_def)

lemma valid_sched_context'_scRefills_update:
  "valid_sched_context' koc s
   \<Longrightarrow> (MIN_REFILLS \<le> length (f (scRefills koc))
        \<and> scRefillMax koc \<le> length (f (scRefills koc)))
   \<Longrightarrow> valid_sched_context' (scRefills_update f koc) s"
  by (clarsimp simp: valid_sched_context'_def)

lemma valid_sched_context'_updates[simp]:
  "\<And>f. valid_sched_context' sc' (ksReprogramTimer_update f s) = valid_sched_context' sc' s"
  "\<And>f. valid_sched_context' sc' (ksReleaseQueue_update f s) = valid_sched_context' sc' s"
  by (auto simp: valid_sched_context'_def valid_bound_obj'_def split: option.splits)

lemma valid_sched_context'_scConsumed_update[simp]:
  "valid_sched_context' (scConsumed_update f ko) s = valid_sched_context' ko s"
  by (clarsimp simp: valid_sched_context'_def)

lemma valid_sched_context_size'_scConsumed_update[simp]:
  "valid_sched_context_size' (scConsumed_update f sc') = valid_sched_context_size' sc'"
  by (clarsimp simp: valid_sched_context_size'_def objBits_simps)

lemma readSchedContext_SomeD:
  "readSchedContext scp s = Some sc'
   \<Longrightarrow> ksPSpace s scp = Some (KOSchedContext sc')"
  by (clarsimp simp: readSchedContext_def asks_def obj_at'_def projectKOs
              dest!: readObject_misc_ko_at')

lemma no_ofail_readSchedContext:
  "no_ofail (sc_at' p) (readSchedContext p)"
  unfolding readSchedContext_def by wpsimp

lemma sym_refs_tcbSchedContext:
  "\<lbrakk>ko_at' tcb tcbPtr s; sym_refs (state_refs_of' s); tcbSchedContext tcb = Some scPtr\<rbrakk>
   \<Longrightarrow> obj_at' (\<lambda>sc. scTCB sc = Some tcbPtr) scPtr s"
  apply (drule (1) sym_refs_obj_atD')
  apply (auto simp: state_refs_of'_def ko_wp_at'_def obj_at'_def
                    refs_of_rev' projectKOs)
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
   apply (wpsimp simp: obj_at'_real_def sc_objBits_pos_power2 wp: setObject_ko_wp_at)
  apply wpsimp
  apply (wpsimp wp: updateObject_default_inv)
  by (auto simp: valid_idle'_def obj_at'_real_def ko_wp_at'_def)[1]

lemma setSchedContext_invs':
  "\<lbrace>invs' and K (scPtr = idle_sc_ptr \<longrightarrow> idle_sc' sc)
    and (\<lambda>s. live_sc' sc \<longrightarrow> ex_nonz_cap_to' scPtr s)
    and valid_sched_context' sc
    and (\<lambda>_. valid_sched_context_size' sc)\<rbrace>
    setSchedContext scPtr sc
    \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_dom_schedule'_def)
  apply (wpsimp wp: valid_pde_mappings_lift' untyped_ranges_zero_lift simp: cteCaps_of_def o_def)
  done

lemma setSchedContext_active_sc_at':
  "\<lbrace>active_sc_at' scPtr' and K (scPtr' = scPtr \<longrightarrow> 0 < scRefillMax sc)\<rbrace>
   setSchedContext scPtr sc
   \<lbrace>\<lambda>rv s. active_sc_at' scPtr' s\<rbrace>"
  apply (simp add: active_sc_at'_def obj_at'_real_def setSchedContext_def)
  apply (wpsimp wp: setObject_ko_wp_at simp: sc_objBits_pos_power2)
  apply (clarsimp simp: ko_wp_at'_def obj_at'_real_def)
  done

lemma updateSchedContext_invs':
  "\<lbrace>invs'
    and (\<lambda>s. scPtr = idle_sc_ptr \<longrightarrow> (\<forall>ko. ko_at' ko scPtr s \<longrightarrow> idle_sc' (f ko)))
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
  by (clarsimp simp: state_refs_of'_def obj_at'_real_def ko_wp_at'_def projectKO_sc)

lemma live_sc'_ko_ex_nonz_cap_to':
  "\<lbrakk>invs' s; ko_at' ko scPtr s\<rbrakk> \<Longrightarrow> live_sc' ko \<Longrightarrow> ex_nonz_cap_to' scPtr s"
  apply (drule invs_iflive')
  apply (erule if_live_then_nonz_capE')
  by (clarsimp simp: ko_wp_at'_def obj_at'_real_def projectKO_sc)

lemma updateSchedContext_refills_invs':
  "\<lbrace>invs'
    and (\<lambda>s. scPtr = idle_sc_ptr \<longrightarrow> (\<forall>ko. ko_at' ko scPtr s \<longrightarrow> idle_sc' (f ko)))
    and (\<lambda>s. \<forall>ko. ko_at' ko scPtr s \<longrightarrow> valid_sched_context' (f ko) s \<and> valid_sched_context_size' (f ko))
    and (\<lambda>_. \<forall>ko. scNtfn (f ko) = scNtfn ko)
    and (\<lambda>_. \<forall>ko. scTCB (f ko) = scTCB ko)
    and (\<lambda>_. \<forall>ko. scYieldFrom (f ko) = scYieldFrom ko)
    and (\<lambda>_. \<forall>ko. scReply (f ko) = scReply ko)\<rbrace>
    updateSchedContext scPtr f
    \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: updateSchedContext_def)
  apply (wpsimp wp: setSchedContext_invs')
  apply (intro conjI)
   apply fastforce
  apply clarsimp
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
  apply (clarsimp simp: active_sc_at'_def obj_at'_real_def ko_wp_at'_def projectKO_sc)
  done

lemma invs'_ko_at_valid_sched_context':
  "\<lbrakk>invs' s; ko_at' ko scPtr s\<rbrakk> \<Longrightarrow> valid_sched_context' ko s \<and> valid_sched_context_size' ko"
  apply (drule invs_valid_objs')
  apply (drule (1) sc_ko_at_valid_objs_valid_sc', simp)
  done

lemma updateSchedContext_invs'_indep:
  "\<lbrace>invs' and (\<lambda>s. scPtr = idle_sc_ptr \<longrightarrow> (\<forall>ko. ko_at' ko scPtr s \<longrightarrow> idle_sc' (f ko)))
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
   apply (clarsimp simp: invs'_def valid_state'_def valid_objs'_def obj_at'_def)
   apply (erule if_live_then_nonz_capE')
   apply (clarsimp simp: ko_wp_at'_def projectKO_eq projectKO_sc live_sc'_def)
  apply (frule (1) invs'_ko_at_valid_sched_context', simp)
  done

context begin interpretation Arch . (*FIXME: arch_split*)

lemma scConsumed_update_corres:
  "x = y \<Longrightarrow>
   corres dc (sc_at scPtr) (ko_at' sc' scPtr)
          (set_sc_obj_ref sc_consumed_update scPtr x)
          (setSchedContext scPtr (scConsumed_update (\<lambda>_. y) sc'))"
  unfolding update_sched_context_def
  apply (rule corres_guard_imp)
    apply (rule corres_symb_exec_l'[where Q'="\<lambda>r s. ko_at r scPtr s \<and> (\<exists>n. is_sc_obj n r)",
                                    where P="\<lambda>s. obj_at \<top> scPtr s"])
      apply (rule corres_guard_imp[where P'=R and Q'=R for R])
        apply (rule_tac F="(\<exists>n. is_sc_obj n obj)" in corres_gen_asm)
        apply (case_tac obj; simp add: is_sc_obj_def)
        apply (rule setSchedContext_no_stack_update_corres[where f'="scConsumed_update (\<lambda>_. y)"])
           apply (clarsimp simp: sc_relation_def objBits_def objBitsKO_def obj_at_def)+
     apply (fastforce simp: exs_valid_def get_object_def in_monad obj_at_def)
    apply (wpsimp wp: get_object_wp)
   apply (fastforce simp: obj_at_def)
  apply simp
  done

lemma schedContextUpdateConsumed_corres:
 "corres (=) (sc_at scp) (sc_at' scp)
            (sched_context_update_consumed scp)
            (schedContextUpdateConsumed scp)"
  using if_cong[cong]
  unfolding sched_context_update_consumed_def schedContextUpdateConsumed_def
  apply (simp add: maxTicksToUs_def ticksToUs_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated [OF _ get_sc_corres])
      apply (rule corres_if2, clarsimp simp: sc_relation_def)
       apply (rule corres_split_deprecated[OF corres_return_eq_same[OF refl]])
         apply (rule scConsumed_update_corres, clarsimp simp: sc_relation_def)
        apply wpsimp+
      apply (rule corres_split_deprecated[OF corres_return_eq_same scConsumed_update_corres],
             clarsimp simp: sc_relation_def)
        apply wpsimp+
  done

end

crunches sched_context_update_consumed
  for in_user_Frame[wp]: "in_user_frame buffer"

lemma schedContextUpdateConsumed_tcb_at'CT[wp]:
  "schedContextUpdateConsumed scp \<lbrace>\<lambda>s. tcb_at' (ksCurThread s) s\<rbrace>"
  unfolding schedContextUpdateConsumed_def
  by (wpsimp | wps)+

lemma schedContextUpdateConsumed_valid_ipc_buffer_ptr'[wp]:
  "schedContextUpdateConsumed scp \<lbrace>valid_ipc_buffer_ptr' x\<rbrace>"
  unfolding schedContextUpdateConsumed_def valid_ipc_buffer_ptr'_def
  by wpsimp

lemma schedContextUpdateConsumed_iflive[wp]:
  "schedContextUpdateConsumed scp \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (wpsimp simp: schedContextUpdateConsumed_def)
  apply (clarsimp elim!: if_live_then_nonz_capE' simp: obj_at'_def projectKOs ko_wp_at'_def)
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
  and valid_pde_mappings'[wp]: valid_pde_mappings'
  and valid_queues[wp]: valid_queues
  and ksQ[wp]: "\<lambda>s. P (ksReadyQueues s p)"
  and reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and valid_replies' [wp]: valid_replies'
  and st_tcb_at'[wp]: "\<lambda>s. P (st_tcb_at' P' t s)"
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
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def valid_dom_schedule'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift cur_tcb_lift
                    untyped_ranges_zero_lift
              simp: cteCaps_of_def o_def)
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
  apply (fastforce simp: valid_pde_mappings'_def obj_at'_def projectKOs ps_clear_upd)
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
  (wp: crunch_wps threadSet_pred_tcb_no_state simp: crunch_simps)

global_interpretation schedContextCancelYieldTo: typ_at_all_props' "schedContextCancelYieldTo t"
  by typ_at_props'

lemma schedContextCancelYieldTo_invs':
  "\<lbrace>invs' and sch_act_simple and tcb_at' t\<rbrace>
   schedContextCancelYieldTo t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def setSchedContext_def
                   valid_dom_schedule'_def)
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
  apply (simp add: setConsumed_def)
  by (wpsimp wp: schedContextUpdateConsumed_invs'
      | strengthen tcb_at_invs')+

lemma schedContextCompleteYieldTo_invs'[wp]:
  "\<lbrace>invs' and sch_act_simple and tcb_at' thread\<rbrace>
   schedContextCompleteYieldTo thread
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding schedContextCompleteYieldTo_def
  by (wpsimp wp: schedContextCancelYieldTo_invs' setConsumed_invs'
                 hoare_drop_imp hoare_vcg_if_lift2
           simp: sch_act_simple_def)

lemma setConsumed_corres:
 "corres dc ((\<lambda>s. tcb_at (cur_thread s) s) and case_option \<top> in_user_frame buf and sc_at scp)
            (\<lambda>s. tcb_at' (ksCurThread s) s \<and> case_option \<top> valid_ipc_buffer_ptr' buf s \<and> sc_at' scp s)
            (set_consumed scp buf)
            (setConsumed scp buf)"
  apply (simp add: set_consumed_def setConsumed_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated [OF _ schedContextUpdateConsumed_corres])
      apply (rule corres_split_deprecated [OF _ gct_corres], simp)
        apply (rule corres_split_deprecated [OF set_mi_corres set_mrs_corres])
  by (wpsimp wp: hoare_case_option_wp simp: setTimeArg_def)+

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
  apply (rule corres_guard_imp)
    apply (rule set_tcb_obj_ref_corres; simp add: tcb_relation_def)
   apply simp+
  done

lemma complete_yield_to_corres:
  "corres dc (invs and tcb_at thread) (invs' and tcb_at' thread)
    (complete_yield_to thread) (schedContextCompleteYieldTo thread)"
  apply (simp add: complete_yield_to_def schedContextCompleteYieldTo_def)
  apply (subst maybeM_when)
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated [OF _ get_tcb_yield_to_corres], simp)
      apply (rule corres_when2[OF refl])
      apply (clarsimp, wpfix)
      apply (rule corres_split_deprecated[OF _ lipcb_corres], simp)
        apply (rule corres_split_deprecated[OF _ setConsumed_corres])
          apply (clarsimp simp: schedContextCancelYieldTo_def)
          apply (rule corres_symb_exec_r'[where Q'=\<top>])
             apply (rule_tac F="scPtrOpt = Some y" in corres_gen_asm2)
             apply simp
             apply (subst dc_def[symmetric])
             apply (subst bind_assoc[symmetric])
             apply (rule corres_split_deprecated[OF tcb_yield_to_update_corres update_sc_no_reply_stack_update_corres])
                  apply (clarsimp simp: sc_relation_def objBits_def objBitsKO_def)+
              apply (wpsimp wp: threadGet_wp)+
           apply (clarsimp simp: obj_at'_def)
          apply wpsimp
         apply (wpsimp wp: sc_at_typ_at)
        apply (clarsimp cong: conj_cong)
        apply (rule_tac Q="\<lambda>rv. pred_tcb_at' itcbYieldTo ((=) (Some y)) thread"
               in hoare_strengthen_post[rotated])
         apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
        apply wpsimp
       apply wpsimp
      apply wpsimp
     apply (wpsimp wp: get_tcb_obj_ref_wp)
    apply (wpsimp wp: threadGet_wp)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def cur_tcb_def)
   apply (subgoal_tac "valid_tcb thread tcb s", clarsimp simp: valid_tcb_def)
   apply (fastforce simp: obj_at'_def valid_tcb_valid_obj elim: valid_objs_ko_at
                    dest: invs_valid_objs)
  apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def cur_tcb'_def
                        obj_at'_real_def ko_wp_at'_def pred_tcb_at'_def projectKO_tcb)
  apply (subgoal_tac "valid_tcb' obja s", clarsimp simp: valid_tcb'_def)
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def pred_tcb_at'_def valid_bound_obj'_def)
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
         schedContextZeroRefillMax, schedContextUnbindYieldFrom, schedContextUnbindReply
  for st_tcb_at'[wp]: "\<lambda>s. P (st_tcb_at' P' p s)"
  (simp: crunch_simps wp: threadSet_pred_tcb_no_state crunch_wps)

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
    apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def)
   apply wpsimp
  apply (rule_tac B="\<lambda>_. ?pre and sc_at' scPtr" in hoare_seq_ext[rotated])
   apply (wpsimp wp: set_sc_valid_objs')
   apply (clarsimp simp: valid_sched_context'_def valid_sched_context_size'_def
                         sc_size_bounds_def objBits_def objBitsKO_def)
  apply (wpsimp wp: threadSet_valid_objs')
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def)
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
                               pred_tcb_at'_def obj_at'_def projectKO_eq projectKO_tcb
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
  apply (auto simp: obj_at'_def projectKO_eq projectKO_sc valid_idle'_def)
  done

lemma schedContextDonate_bound_tcb_sc_at[wp]:
  "\<lbrace>\<top>\<rbrace> schedContextDonate scPtr tcbPtr \<lbrace>\<lambda>_. obj_at' (\<lambda>a. \<exists>y. scTCB a = Some y) scPtr\<rbrace>"
   unfolding schedContextDonate_def
   by (wpsimp wp: set_sc'.obj_at')

(* FIXME RT: move *)
lemmas sc_inv_state_eq' = getObject_sc_inv[THEN use_valid[rotated], rotated
                                           , where s=s and P="(=) s" for s, OF _ refl]

lemma sc_inv_state_eq:
  "(a :: sched_context, s') \<in> fst (getSchedContext p s) \<Longrightarrow> s' = s"
  apply (fastforce dest: sc_inv_state_eq' simp: getSchedContext_def)
  done

lemma getObject_idempotent:
  "monadic_rewrite False True (sc_at' ptr)
   (do rv \<leftarrow> (getObject ptr :: sched_context kernel);
       getObject ptr
    od)
   (getObject ptr :: sched_context kernel)"
  apply (clarsimp simp: monadic_rewrite_def)
  apply (rule monad_state_eqI)
    apply ((clarsimp simp: in_monad getObject_def split_def
                           loadObject_default_def projectKOs scBits_pos_power2 objBits_simps'
                           lookupAround2_known1 in_magnitude_check)+)[2]
  apply (fastforce dest!: sc_inv_state_eq[simplified getSchedContext_def]
                          no_fail_getObject_misc[simplified no_fail_def, rule_format]
                    simp: snd_bind)
  done

lemma getSchedContext_setSchedContext_decompose:
   "monadic_rewrite False True
     (sc_at' scPtr and K (\<forall>sc. objBits (f sc) = objBits sc) and K (\<forall>sc. objBits (g sc) = objBits sc))
     (do sc \<leftarrow> getSchedContext scPtr;
         setSchedContext scPtr (g (f sc))
      od)
     (do sc \<leftarrow> getSchedContext scPtr;
         setSchedContext scPtr (f sc);
         sc \<leftarrow> getSchedContext scPtr;
         setSchedContext scPtr (g sc)
      od)"
  apply (clarsimp simp: monadic_rewrite_def)
  apply (rule monad_state_eqI)
    apply (simp add: in_monad getSchedContext_def getObject_def)
    apply (frule no_ofailD[OF no_ofail_sc_at'_readObject])
    apply (clarsimp del: readObject_misc_ko_at' simp del: readObject_misc_obj_at')
    apply (clarsimp simp: setSchedContext_def setObject_def obj_at'_def projectKOs objBits_simps'
                          in_monad ARM_H.fromPPtr_def scBits_pos_power2 updateObject_default_def
                          in_magnitude_check ps_clear_upd magnitudeCheck_assert split_def
                     del: readObject_misc_ko_at'
                   split: option.split_asm)
     apply (rename_tac sc sc')
     apply (rule_tac x="f sc" in exI)
     apply (rule conjI;
            fastforce simp: readObject_def obind_def omonad_defs split_def ARM_H.fromPPtr_def
                            ps_clear_upd loadObject_default_def lookupAround2_known1 projectKOs
                            objBits_simps' scBits_pos_power2 lookupAround2_None2 lookupAround2_char2
                     split: option.splits if_split_asm dest!: readObject_misc_ko_at')
    apply (rename_tac sc p sc')
    apply (rule_tac x="f sc" in exI)
    apply (rule conjI)
     apply (thin_tac "scBitsFromRefillLength' _=_")
     apply (clarsimp simp: readObject_def obind_def omonad_defs fun_upd_def split_def ARM_H.fromPPtr_def
                           ps_clear_upd loadObject_default_def lookupAround2_known1 projectKOs
                           objBits_simps' scBits_pos_power2 lookupAround2_None2 lookupAround2_char2
                    split: option.splits if_split_asm)
     apply (metis option.simps(3) word_le_less_eq word_le_not_less)
    apply (clarsimp simp: split: option.splits)
    apply (metis (no_types) array_rules(2) lookupAround2_char2 mcs(1) order.strict_trans2
                            word_le_less_eq word_le_not_less)
   apply (simp add: in_monad getSchedContext_def getObject_def)
   apply (frule no_ofailD[OF no_ofail_sc_at'_readObject])
   apply (clarsimp del: readObject_misc_ko_at' simp del: readObject_misc_obj_at')
   apply (clarsimp simp: setSchedContext_def setObject_def projectKOs in_monad ps_clear_upd obj_at'_def
                         split_def updateObject_default_def magnitudeCheck_assert ARM_H.fromPPtr_def
                  dest!: readObject_misc_ko_at')

   apply (frule no_failD[OF no_fail_getMiscObject(4)])
  apply (simp add: snd_bind)
  apply (rule iffI; clarsimp simp: snd_bind split_def setSchedContext_def; rename_tac sc s')
   apply (frule sc_inv_state_eq, simp)
   apply (rule_tac x="(sc, s)" in bexI[rotated], simp)
   apply (rule disjI2)
   apply (drule use_valid[OF _ get_sc_ko'], simp)
   apply (clarsimp simp: obj_at'_def projectKOs)
   apply (prop_tac "obj_at' (\<lambda>k. objBits k = objBits (g (f sc))) scPtr s")
    apply (clarsimp simp: obj_at'_def projectKOs projectKO_opt_sc)
    apply (rule_tac x=sc in exI, clarsimp simp: projectKO_opt_sc)
   apply (drule_tac ob1="g (f sc)" in no_failD[OF no_fail_setObject_other, rotated])
    apply simp
   apply clarsimp
  apply (frule sc_inv_state_eq, simp)
  apply (rule_tac x="(sc, s)" in bexI[rotated], simp)
  apply (drule use_valid[OF _ get_sc_ko'], simp)
  apply (erule disjE; clarsimp)
   apply (clarsimp simp: obj_at'_def projectKOs)
   apply (prop_tac "obj_at' (\<lambda>k. objBits k = objBits (f sc)) scPtr s")
    apply (clarsimp simp: obj_at'_def projectKOs projectKO_opt_sc)
    apply (rule_tac x=sc in exI, clarsimp simp: projectKO_opt_sc)
   apply (drule_tac ob1="(f sc)" in no_failD[OF no_fail_setObject_other, rotated])
    apply simp+

  apply (rename_tac s'; erule disjE; clarsimp?)
   apply (drule_tac Q2="\<lambda>s'. s' = (s\<lparr>ksPSpace := ksPSpace s(scPtr \<mapsto> injectKO (f sc))\<rparr>)"
                 in use_valid[OF _ setObject_sc_wp])
    apply simp+

   apply (prop_tac "sc_at' scPtr (s\<lparr>ksPSpace := ksPSpace s(scPtr \<mapsto> KOSchedContext (f sc))\<rparr>)")
    apply (clarsimp simp: obj_at'_def projectKOs objBits_simps' ps_clear_upd)
   apply (frule_tac s="s\<lparr>ksPSpace := ksPSpace s(scPtr \<mapsto> KOSchedContext (f sc))\<rparr>"
                 in no_failD[OF no_fail_getMiscObject(4)])
   apply clarsimp

 apply (rename_tac s')
   apply (drule_tac Q2="\<lambda>s'. s' = (s\<lparr>ksPSpace := ksPSpace s(scPtr \<mapsto> injectKO (f sc))\<rparr>)"
                 in use_valid[OF _ setObject_sc_wp])
    apply simp+

  apply (frule sc_inv_state_eq, simp)
  apply (drule use_valid[OF _ get_sc_ko'], simp)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (prop_tac "obj_at' (\<lambda>k. objBits k = objBits (g (f sc))) scPtr
                           (s\<lparr>ksPSpace := ksPSpace s(scPtr \<mapsto> KOSchedContext (f sc))\<rparr>)")
   apply (clarsimp simp: obj_at'_def projectKOs projectKO_opt_sc)
   apply (rule_tac x="f sc" in exI, clarsimp simp: projectKO_opt_sc)
  apply (drule_tac ob1="g (f sc)" in no_failD[OF no_fail_setObject_other, rotated])
   apply simp+
  done

lemmas getSchedContext_setSchedContext_decompose_decompose_ext
  = getSchedContext_setSchedContext_decompose[where f="f x" and g="g y" for f g x y]
lemmas getSchedContext_setSchedContext_decompose_decompose2
  = getSchedContext_setSchedContext_decompose[where g="\<lambda>sc. g (h sc)" for g h]
lemmas getSchedContext_setSchedContext_decompose_decompose_ext2
  = getSchedContext_setSchedContext_decompose[where f="f x" and g="g y" for f g x y]

(* rewrite rules for updateSchedCOntext *)
lemma updateSchedContext_decompose:
   "monadic_rewrite False True
     (sc_at' scPtr and K (\<forall>sc. objBits (f sc) = objBits sc) and K (\<forall>sc. objBits (g sc) = objBits sc))
     (updateSchedContext scPtr (g o f))
     (do updateSchedContext scPtr f;
         updateSchedContext scPtr g
      od)"
  unfolding updateSchedContext_def bind_assoc o_def
  using getSchedContext_setSchedContext_decompose by blast

lemma updateSchedContext_decompose_fold:
  "\<lbrakk>\<forall>f\<in> set fs. \<forall>sc. objBits (f sc) = objBits sc; \<forall>sc. objBits (f sc) = objBits sc\<rbrakk> \<Longrightarrow>
   monadic_rewrite False True
     (sc_at' scPtr)
     (updateSchedContext scPtr (fold (o) fs f))
     (do _ \<leftarrow> updateSchedContext scPtr f;
        mapM_x (updateSchedContext scPtr) fs
      od)"
  apply (induction fs arbitrary: f)
   apply (clarsimp simp: mapM_x_Nil)
   apply (rule monadic_rewrite_imp)
    apply (rule monadic_rewrite_refl, simp)
  apply (clarsimp simp: mapM_x_Cons)
  apply (drule_tac x="a o f" in meta_spec)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply simp
   apply (subst bind_assoc[symmetric])
   apply (rule monadic_rewrite_imp)
    apply (rule monadic_rewrite_bind_head)
    apply (rule updateSchedContext_decompose[simplified])
   apply simp
  apply simp
  done

lemmas updateSchedContext_decompose_x2 = updateSchedContext_decompose_fold[where fs="[g, h]" for f g h,
 simplified mapM_x_Cons mapM_x_Nil fold_Cons fold_Nil id_def, simplified]

lemmas updateSchedContext_decompose_x3 = updateSchedContext_decompose_fold[where fs="[g, h, k]" for f g h k,
 simplified mapM_x_Cons mapM_x_Nil fold_Cons fold_Nil id_def, simplified]

(* should other update wp rules for valid_objs/valid_objs' be in this form? *)
lemma updateSchedContext_valid_objs'[wp]:
  "\<lbrace>valid_objs' and
    (\<lambda>s. ((\<lambda>sc'. valid_obj' (injectKO sc') s \<longrightarrow> valid_obj' (injectKO (f' sc')) s)
              |< scs_of' s) scp)\<rbrace>
    updateSchedContext scp f'
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wpsimp simp: updateSchedContext_def wp: set_sc'.valid_objs')
  by (fastforce simp: valid_obj'_def valid_sched_context'_def valid_sched_context_size'_def
                      obj_at'_def projectKOs scBits_simps objBits_simps opt_map_red)

lemma updateSchedContext_obj_at'[wp]:
  "\<forall>sc'. objBits sc' = objBits (f' sc'::sched_context) \<Longrightarrow>
   updateSchedContext scp f' \<lbrace>\<lambda>s. P (sc_at' p s)\<rbrace>"
  apply (wpsimp simp: updateSchedContext_def wp: set_sc'.set_wp)
  apply (clarsimp simp: obj_at'_def ps_clear_upd projectKOs objBits_simps)
  done

end
