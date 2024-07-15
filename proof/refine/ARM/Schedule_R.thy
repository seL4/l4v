(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Schedule_R
imports SchedContext_R InterruptAcc_R
begin

crunch scReleased, getReprogramTimer, getCurTime, getRefills, getReleaseQueue, refillSufficient,
         refillReady, isRoundRobin
  for inv[wp]: P

context begin interpretation Arch . (*FIXME: arch_split*)

declare hoare_weak_lift_imp[wp_split del]

(* Levity: added (20090713 10:04:12) *)
declare sts_rel_idle [simp]

crunch refillHeadOverlappingLoop, headInsufficientLoop, setRefillHd
  for valid_queues[wp]: valid_queues
  and valid_queues'[wp]: valid_queues'
  and valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n T p s)"
  (wp: crunch_wps)

crunch tcbReleaseDequeue
  for sc_at'_n[wp]: "\<lambda>s. Q (sc_at'_n n p s)"
  (simp: crunch_simps wp: crunch_wps)

crunch refillUnblockCheck, refillBudgetCheck, ifCondRefillUnblockCheck, refillBudgetCheckRoundRobin
  for valid_queues[wp]: valid_queues
  and valid_queues'[wp]: valid_queues'
  and valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. Q (sc_at'_n n p s)"
  and pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and pspace_bounded'[wp]: pspace_bounded'
  and no_0_obj'[wp]: no_0_obj'
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and sch_act_wf[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  and if_unsafe_then_cap'[wp]: if_unsafe_then_cap'
  and valid_global_refs'[wp]: valid_global_refs'
  and valid_arch_state'[wp]: valid_arch_state'
  and valid_irq_node[wp]: "\<lambda>s. valid_irq_node' (irq_node' s) s"
  and valid_irq_handlers'[wp]: valid_irq_handlers'
  and valid_irq_states'[wp]: valid_irq_states'
  and irqs_masked'[wp]: irqs_masked'
  and valid_pde_mappings'[wp]: valid_pde_mappings'
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksCurdomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and untyped_ranges_zero'[wp]: untyped_ranges_zero'
  and cur_tcb'[wp]: cur_tcb'
  and ct_not_inQ[wp]: ct_not_inQ
  and valid_dom_schedule'[wp]: valid_dom_schedule'
  and ksCurSc[wp]: "\<lambda>s. P (ksCurSc s)"
  (wp: crunch_wps valid_dom_schedule'_lift simp: crunch_simps refillSingle_def)

crunch commitTime, refillNew, refillUpdate
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps simp: crunch_simps)

end

global_interpretation tcbReleaseDequeue: typ_at_all_props' tcbReleaseDequeue
  by typ_at_props'

global_interpretation refillPopHead: typ_at_all_props' "refillPopHead scPtr"
  by typ_at_props'

global_interpretation updateRefillTl: typ_at_all_props' "updateRefillTl scPtr f"
  by typ_at_props'

global_interpretation handleOverrunLoopBody: typ_at_all_props' "handleOverrunLoopBody usage"
  by typ_at_props'

global_interpretation handleOverrunLoop: typ_at_all_props' "handleOverrunLoop usage"
  by typ_at_props'

global_interpretation scheduleUsed: typ_at_all_props' "scheduleUsed scPtr new"
  by typ_at_props'

global_interpretation updateRefillHd: typ_at_all_props' "updateRefillHd scPtr f"
  by typ_at_props'

global_interpretation mergeRefills: typ_at_all_props' "mergeRefills scPtr"
  by typ_at_props'

global_interpretation setRefillHd: typ_at_all_props' "setRefillHd scPtr v"
  by typ_at_props'

global_interpretation nonOverlappingMergeRefills: typ_at_all_props' "nonOverlappingMergeRefills scPtr"
  by typ_at_props'

global_interpretation refillBudgetCheck: typ_at_all_props' "refillBudgetCheck usage"
  by typ_at_props'

global_interpretation refillBudgetCheckRoundRobin: typ_at_all_props' "refillBudgetCheckRoundRobin usage"
  by typ_at_props'

global_interpretation commitTime: typ_at_all_props' "commitTime"
   by typ_at_props'

global_interpretation refillNew: typ_at_all_props' "refillNew scPtr maxRefills budget period"
  by typ_at_props'

global_interpretation refillUpdate: typ_at_all_props' "refillUpdate  scPtr newPeriod newBudget newMaxRefills"
  by typ_at_props'

global_interpretation updateSchedContext: typ_at_all_props' "updateSchedContext scPtr f"
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch_split*)

lemma findM_awesome':
  assumes x: "\<And>x xs. suffix (x # xs) xs' \<Longrightarrow>
                  corres (\<lambda>a b. if b then (\<exists>a'. a = Some a' \<and> r a' (Some x)) else a = None)
                      P (P' (x # xs))
                      ((f >>= (\<lambda>x. return (Some x))) \<sqinter> (return None)) (g x)"
  assumes y: "corres r P (P' []) f (return None)"
  assumes z: "\<And>x xs. suffix (x # xs) xs' \<Longrightarrow>
                 \<lbrace>P' (x # xs)\<rbrace> g x \<lbrace>\<lambda>rv s. \<not> rv \<longrightarrow> P' xs s\<rbrace>"
  assumes p: "suffix xs xs'"
  shows      "corres r P (P' xs) f (findM g xs)"
proof -
  have P: "f = do x \<leftarrow> (do x \<leftarrow> f; return (Some x) od) \<sqinter> return None; if x \<noteq> None then return (the x) else f od"
    apply (rule ext)
    apply (auto simp add: bind_def alternative_def return_def split_def prod_eq_iff)
    done
  have Q: "\<lbrace>P\<rbrace> (do x \<leftarrow> f; return (Some x) od) \<sqinter> return None \<lbrace>\<lambda>rv. if rv \<noteq> None then \<top> else P\<rbrace>"
    by (wp | simp)+
  show ?thesis using p
    apply (induct xs)
     apply (simp add: y del: dc_simp)
    apply (simp only: findM.simps)
    apply (subst P)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF x])
         apply assumption
        apply (rule corres_if3)
          apply (case_tac ra, clarsimp+)[1]
         apply (rule corres_trivial, clarsimp)
         apply (case_tac ra, simp_all)[1]
        apply (erule(1) meta_mp [OF _ suffix_ConsD])
       apply (rule Q)
      apply (rule hoare_post_imp [OF _ z])
       apply simp+
    done
qed

lemmas findM_awesome = findM_awesome' [OF _ _ _ suffix_order.refl]

lemma arch_switchToThread_corres:
  "corres dc (valid_arch_state and valid_objs and valid_asid_map
              and valid_vspace_objs and pspace_aligned and pspace_distinct
              and valid_vs_lookup and valid_global_objs
              and unique_table_refs o caps_of_state
              and st_tcb_at runnable t)
             (valid_arch_state' and st_tcb_at' runnable' t and no_0_obj')
             (arch_switch_to_thread t) (Arch.switchToThread t)"
  apply (rule_tac Q="tcb_at t" in corres_cross_add_abs_guard)
   apply (fastforce dest: st_tcb_at_tcb_at)
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest: pspace_distinct_cross)
  apply (simp add: arch_switch_to_thread_def ARM_H.switchToThread_def)
  apply (rule corres_guard_imp)
    apply (rule corres_underlying_split [OF setVMRoot_corres])
      apply (rule corres_machine_op[OF corres_rel_imp])
      apply (rule corres_underlying_trivial)
       apply (simp add: ARM.clearExMonitor_def | wp)+
   apply clarsimp
  apply (clarsimp simp: valid_pspace'_def)
  done

lemma schedule_choose_new_thread_sched_act_rct[wp]:
  "\<lbrace>\<top>\<rbrace> schedule_choose_new_thread \<lbrace>\<lambda>rs s. scheduler_action s = resume_cur_thread\<rbrace>"
  unfolding schedule_choose_new_thread_def
  by wp

lemma obj_at'_tcbQueued_cross:
  "(s,s') \<in> state_relation \<Longrightarrow> obj_at' tcbQueued t s' \<Longrightarrow> valid_queues' s' \<Longrightarrow>
    obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> tcb_priority tcb = p \<and> tcb_domain tcb = d) t s \<Longrightarrow>
    t \<in> set (ready_queues s d p)"
  apply (clarsimp simp: state_relation_def ready_queues_relation_def valid_queues'_def)
  apply (subgoal_tac "obj_at' (inQ d p) t s'", simp)
  apply (clarsimp simp: obj_at'_def inQ_def obj_at_def projectKO_eq projectKO_tcb)
  apply (frule (2) pspace_relation_tcb_domain_priority)
  apply clarsimp
  done

lemma tcbSchedAppend_corres:
  "tcb_ptr = tcbPtr \<Longrightarrow>
   corres dc
     (in_correct_ready_q and ready_qs_distinct and valid_etcbs and st_tcb_at runnable tcb_ptr
      and pspace_aligned and pspace_distinct)
     (sym_heap_sched_pointers and valid_sched_pointers and valid_tcbs')
     (tcb_sched_action tcb_sched_append tcb_ptr) (tcbSchedAppend tcbPtr)"
  supply if_split[split del]
         heap_path_append[simp del] fun_upd_apply[simp del] distinct_append[simp del]
  apply (rule_tac Q'="st_tcb_at' runnable' tcbPtr" in corres_cross_add_guard)
   apply (fastforce intro!: st_tcb_at_runnable_cross simp: obj_at_def is_tcb_def)
  apply (rule_tac Q="tcb_at tcb_ptr" in corres_cross_add_abs_guard)
   apply (fastforce dest: st_tcb_at_tcb_at)
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest: pspace_distinct_cross)
  apply (clarsimp simp: tcb_sched_action_def tcb_sched_append_def get_tcb_queue_def
                        tcbSchedAppend_def getQueue_def unless_def when_def)
  apply (rule corres_symb_exec_l[OF _ _ ethread_get_sp]; (solves wpsimp)?)
  apply (rename_tac domain)
  apply (rule corres_symb_exec_l[OF _ _ ethread_get_sp]; (solves wpsimp)?)
  apply (rename_tac priority)
  apply (rule corres_symb_exec_l[OF _ _ gets_sp]; (solves wpsimp)?)
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro: ksReadyQueues_asrt_cross)
  apply (rule corres_symb_exec_r[OF _ isRunnable_sp]; wpsimp?)
  apply (rule corres_symb_exec_r[OF _ assert_sp, rotated]; (solves wpsimp)?)
   apply wpsimp
   apply (fastforce simp: st_tcb_at'_def runnable_eq_active' obj_at'_def)
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; (solves wpsimp)?)
  apply (subst if_distrib[where f="set_tcb_queue domain prio" for domain prio])
  apply (rule corres_if_strong')
    apply (frule state_relation_ready_queues_relation)
    apply (frule in_ready_q_tcbQueued_eq[where t=tcbPtr])
    subgoal
      by (fastforce dest: tcb_at_ekheap_dom pred_tcb_at_tcb_at
                    simp: obj_at'_def projectKOs opt_pred_def opt_map_def obj_at_def is_tcb_def
                          in_correct_ready_q_def etcb_at_def is_etcb_at_def)
   apply (find_goal \<open>match conclusion in "corres _ _ _ _ (return ())" \<Rightarrow> \<open>-\<close>\<close>)
   apply (rule monadic_rewrite_corres_l[where P=P and Q=P for P, simplified])
    apply (clarsimp simp: set_tcb_queue_def)
    apply (rule monadic_rewrite_guard_imp)
     apply (rule monadic_rewrite_modify_noop)
    apply (prop_tac "(\<lambda>d p. if d = domain \<and> p = priority
                            then ready_queues s domain priority
                            else ready_queues s d p)
                     = ready_queues s")
     apply (fastforce split: if_splits)
    apply fastforce
   apply clarsimp
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ gets_sp]; (solves wpsimp)?)

  \<comment> \<open>break off the addToBitmap\<close>
  apply (rule corres_add_noop_lhs)
  apply (rule corres_underlying_split[rotated 2,
                                      where Q="\<lambda>_. P" and P=P and Q'="\<lambda>_. P'" and P'=P' for P P'])

     apply wpsimp
    apply (wpsimp wp: hoare_vcg_if_lift hoare_vcg_ex_lift)
   apply (corres corres: addToBitmap_if_null_noop_corres)

  apply (rule corres_from_valid_det)
    apply (fastforce intro: det_wp_modify det_wp_pre simp: set_tcb_queue_def)
   apply (wpsimp simp: tcbQueueAppend_def wp: hoare_vcg_if_lift2 | drule Some_to_the)+
   apply (clarsimp simp: ex_abs_underlying_def split: if_splits)
   apply (frule state_relation_ready_queues_relation)
   apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
   apply (drule_tac x="tcbDomain tcb" in spec)
   apply (drule_tac x="tcbPriority tcb" in spec)
   subgoal by (force dest!: obj_at'_tcbQueueEnd_ksReadyQueues simp: obj_at'_def projectKOs)

  apply (rename_tac s rv t)
  apply (clarsimp simp: state_relation_def)
  apply (intro hoare_vcg_conj_lift_pre_fix;
         (solves \<open>frule singleton_eqD, frule set_tcb_queue_projs_inv, wpsimp simp: swp_def\<close>)?)

  \<comment> \<open>ready_queues_relation\<close>
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
  apply (intro hoare_allI)
  apply (drule singleton_eqD)
  apply (drule set_tcb_queue_new_state)
  apply (wpsimp wp: threadSet_wp simp: setQueue_def tcbQueueAppend_def)
  apply normalise_obj_at'
  apply (frule (1) tcb_at_is_etcb_at)
  apply (clarsimp simp: obj_at_def is_etcb_at_def etcb_at_def)
  apply (rename_tac s d p s' tcb' tcb etcb)
  apply (frule_tac t=tcbPtr in ekheap_relation_tcb_domain_priority)
    apply (force simp: obj_at_def)
   apply (force simp: obj_at'_def projectKOs)
  apply (clarsimp split: if_splits)
  apply (cut_tac ts="ready_queues s d p" in list_queue_relation_nil)
   apply (force dest!: spec simp: list_queue_relation_def)
  apply (cut_tac ts="ready_queues s (tcb_domain etcb) (tcb_priority etcb)"
              in obj_at'_tcbQueueEnd_ksReadyQueues)
      apply fast
     apply fast
    apply fastforce
   apply fastforce
  apply (cut_tac xs="ready_queues s d p" in heap_path_head')
   apply (force dest!: spec simp: list_queue_relation_def)
  apply (clarsimp simp: list_queue_relation_def)

  apply (case_tac "d \<noteq> tcb_domain etcb \<or> p \<noteq> tcb_priority etcb")
   apply (cut_tac d=d and d'="tcb_domain etcb" and p=p and p'="tcb_priority etcb"
               in ready_queues_disjoint)
      apply force
     apply fastforce
    apply fastforce
   apply (prop_tac "tcbPtr \<notin> set (ready_queues s d p)")
    apply (clarsimp simp: obj_at'_def projectKOs opt_pred_def opt_map_def)
    apply (metis inQ_def option.simps(5) tcb_of'_TCB)
   apply (intro conjI impI; clarsimp)

    \<comment> \<open>the ready queue was originally empty\<close>
         apply (rule heap_path_heap_upd_not_in)
          apply (clarsimp simp: fun_upd_apply split: if_splits)
         apply fastforce
        apply (clarsimp simp: queue_end_valid_def fun_upd_apply split: if_splits)
       apply (rule prev_queue_head_heap_upd)
        apply (clarsimp simp: fun_upd_apply split: if_splits)
       apply (case_tac "ready_queues s d p";
              clarsimp simp: fun_upd_apply tcbQueueEmpty_def split: if_splits)
      apply (clarsimp simp: inQ_def in_opt_pred fun_upd_apply obj_at'_def split: if_splits)
     apply (clarsimp simp: fun_upd_apply split: if_splits)
    apply (clarsimp simp: fun_upd_apply split: if_splits)

   \<comment> \<open>the ready queue was not originally empty\<close>
   apply (clarsimp simp: etcb_at_def obj_at'_def)
   apply (prop_tac "the (tcbQueueEnd (ksReadyQueues s' (tcb_domain etcb, tcb_priority etcb)))
                    \<notin> set (ready_queues s d p)")
    apply (erule orthD2)
    apply (drule_tac x="tcb_domain etcb" in spec)
    apply (drule_tac x="tcb_priority etcb" in spec)
    apply clarsimp
    apply (drule_tac x="the (tcbQueueEnd (ksReadyQueues s' (tcb_domain etcb, tcb_priority etcb)))"
                 in spec)
    subgoal by (auto simp: in_opt_pred opt_map_red projectKOs)
   apply (intro conjI impI allI)
        apply (intro heap_path_heap_upd_not_in)
          apply (clarsimp simp: fun_upd_apply split: if_splits)
         apply simp
        apply fastforce
       apply (clarsimp simp: queue_end_valid_def fun_upd_apply split: if_splits)
      apply (intro prev_queue_head_heap_upd)
        apply (force simp: fun_upd_apply split: if_splits)
       apply (case_tac "ready_queues s d p";
              clarsimp simp: fun_upd_apply tcbQueueEmpty_def split: if_splits)
      apply (clarsimp simp: fun_upd_apply inQ_def split: if_splits)
      apply (case_tac "ready_queues s d p"; force simp: tcbQueueEmpty_def)
     apply (case_tac "t = tcbPtr")
      apply (clarsimp simp: projectKOs inQ_def fun_upd_apply split: if_splits)
     apply (case_tac "t = the (tcbQueueEnd (ksReadyQueues s' (tcb_domain etcb, tcb_priority etcb)))")
      apply (clarsimp simp: projectKOs inQ_def opt_pred_def fun_upd_apply)
     apply (clarsimp simp: inQ_def in_opt_pred opt_map_def fun_upd_apply)
    apply (clarsimp simp: fun_upd_apply split: if_splits)
   apply (clarsimp simp: fun_upd_apply split: if_splits)

  \<comment> \<open>d = tcb_domain tcb \<and> p = tcb_priority tcb\<close>
  apply clarsimp
  apply (drule_tac x="tcb_domain etcb" in spec)
  apply (drule_tac x="tcb_priority etcb" in spec)
  apply (cut_tac ts="ready_queues s (tcb_domain etcb) (tcb_priority etcb)"
              in tcbQueueHead_iff_tcbQueueEnd)
   apply (force simp: list_queue_relation_def)
  apply (frule valid_tcbs'_maxDomain[where t=tcbPtr], simp add: obj_at'_def projectKOs)
  apply (frule valid_tcbs'_maxPriority[where t=tcbPtr], simp add: obj_at'_def projectKOs)
  apply (drule valid_sched_pointersD[where t=tcbPtr])
   apply (clarsimp simp: in_opt_pred opt_map_red obj_at'_def projectKOs)
  apply (intro conjI; clarsimp)

   \<comment> \<open>the ready queue was originally empty\<close>
   apply (force simp: inQ_def in_opt_pred fun_upd_apply opt_map_def obj_at'_def projectKOs
                      queue_end_valid_def prev_queue_head_def
               split: if_splits option.splits)

   \<comment> \<open>the ready queue was not originally empty\<close>
  apply (drule (2) heap_ls_append[where new=tcbPtr])
  apply (rule conjI)
   apply (clarsimp simp: fun_upd_apply queue_end_valid_def opt_map_def obj_at'_def projectKOs
                  split: if_splits)
  apply (rule conjI)
   apply (clarsimp simp: fun_upd_apply queue_end_valid_def)
  apply (rule conjI)
   apply (subst opt_map_upd_triv)
    apply (clarsimp simp: opt_map_def fun_upd_apply queue_end_valid_def obj_at'_def projectKOs
                   split: if_splits)
   apply (clarsimp simp: prev_queue_head_def fun_upd_apply split: if_splits)
  by (clarsimp simp: inQ_def in_opt_pred fun_upd_apply queue_end_valid_def
                     obj_at'_def projectKOs
              split: if_splits)

lemma tcbQueueAppend_valid_objs'[wp]:
  "\<lbrace>\<lambda>s. valid_objs' s \<and> tcb_at' tcbPtr s \<and> (\<forall>end. tcbQueueEnd queue = Some end \<longrightarrow> tcb_at' end s)\<rbrace>
   tcbQueueAppend queue tcbPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding tcbQueueAppend_def
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')
  apply (clarsimp simp: tcbQueueEmpty_def valid_bound_tcb'_def split: option.splits)
  done

lemma tcbSchedAppend_valid_objs'[wp]:
  "\<lbrace>valid_objs' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedAppend tcbPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (clarsimp simp: tcbSchedAppend_def setQueue_def)
  apply (wpsimp wp: threadSet_valid_objs' threadGet_wp hoare_vcg_all_lift)
  apply (normalise_obj_at', rename_tac tcb "end")
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply clarsimp
  apply (frule tcbQueueHead_iff_tcbQueueEnd)
  apply (force dest!: obj_at'_tcbQueueEnd_ksReadyQueues simp: tcbQueueEmpty_def obj_at'_def)
  done

crunch tcbSchedAppend, tcbSchedDequeue
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
  (wp: threadSet_pred_tcb_no_state simp: unless_def tcb_to_itcb'_def)

(* FIXME move *)
lemmas obj_at'_conjI = obj_at_conj'

crunch tcbSchedAppend, tcbSchedDequeue, tcbSchedEnqueue
  for tcb_at'[wp]: "tcb_at' t"
  and cap_to'[wp]: "ex_nonz_cap_to' p"
  and ifunsafe'[wp]: if_unsafe_then_cap'
  (wp: crunch_wps simp: crunch_simps)

lemma tcbSchedAppend_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedAppend tcbPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding tcbSchedAppend_def
  apply (wpsimp wp: tcbQueueAppend_if_live_then_nonz_cap' threadGet_wp simp: bitmap_fun_defs)
  apply (frule_tac p=tcbPtr in if_live_then_nonz_capE')
   apply (fastforce simp: ko_wp_at'_def st_tcb_at'_def obj_at'_def projectKOs runnable_eq_active')
  apply (clarsimp simp: tcbQueueEmpty_def)
  apply (erule if_live_then_nonz_capE')
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply (fastforce dest!: obj_at'_tcbQueueEnd_ksReadyQueues
                    simp: ko_wp_at'_def inQ_def obj_at'_def projectKOs tcbQueueEmpty_def)
  done

lemma tcbSchedDequeue_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and valid_objs' and sym_heap_sched_pointers\<rbrace>
   tcbSchedDequeue tcbPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wpsimp wp: tcbQueueRemove_if_live_then_nonz_cap' threadGet_wp)
  apply (fastforce elim: if_live_then_nonz_capE' simp: obj_at'_def projectKOs ko_wp_at'_def)
  done

crunch tcbSchedAppend, tcbSchedDequeue, tcbSchedEnqueue
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and tcb_at'[wp]: "tcb_at' t"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and ksInterrupt[wp]: "\<lambda>s. P (ksInterruptState s)"
  and irq_states[wp]: valid_irq_states'
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  and global_refs'[wp]: valid_global_refs'
  and ifunsafe'[wp]: if_unsafe_then_cap'
  and cap_to'[wp]: "ex_nonz_cap_to' p"
  and state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  and idle'[wp]: valid_idle'
  and valid_pde_mappings'[wp]: valid_pde_mappings'
  (simp: unless_def crunch_simps wp: crunch_wps)

lemma tcbSchedEnqueue_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift tcbSchedEnqueue_ksMachine)
  done

lemma tcbSchedEnqueue_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_. tcb_in_cur_domain' t' \<rbrace>"
  apply (rule tcb_in_cur_domain'_lift)
   apply wp
  apply (clarsimp simp: tcbSchedEnqueue_def)
  apply (wpsimp simp: unless_def)+
  done

lemma ct_idle_or_in_cur_domain'_lift2:
  "\<lbrakk> \<And>t. \<lbrace>tcb_in_cur_domain' t\<rbrace>         f \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>;
     \<And>P. \<lbrace>\<lambda>s. P (ksCurThread s) \<rbrace>       f \<lbrace>\<lambda>_ s. P (ksCurThread s) \<rbrace>;
     \<And>P. \<lbrace>\<lambda>s. P (ksIdleThread s) \<rbrace>      f \<lbrace>\<lambda>_ s. P (ksIdleThread s) \<rbrace>;
     \<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s) \<rbrace> f \<lbrace>\<lambda>_ s. P (ksSchedulerAction s) \<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace> ct_idle_or_in_cur_domain'\<rbrace> f \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain' \<rbrace>"
  apply (unfold ct_idle_or_in_cur_domain'_def)
  apply (rule hoare_lift_Pf2[where f=ksCurThread])
  apply (rule hoare_lift_Pf2[where f=ksSchedulerAction])
  apply (wp hoare_weak_lift_imp hoare_vcg_disj_lift | assumption)+
  done

lemma threadSet_mdb':
  "\<lbrace>valid_mdb' and obj_at' (\<lambda>t. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF t = getF (f t)) t\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (wpsimp wp: setObject_tcb_mdb' getTCB_wp simp: threadSet_def obj_at'_def)

lemma tcbSchedNext_update_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and tcb_at' tcbPtr\<rbrace> threadSet (tcbSchedNext_update f) tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (wpsimp wp: threadSet_mdb')
  apply (fastforce simp: obj_at'_def valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

lemma tcbSchedPrev_update_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and tcb_at' tcbPtr\<rbrace> threadSet (tcbSchedPrev_update f) tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (wpsimp wp: threadSet_mdb')
  apply (fastforce simp: obj_at'_def valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

lemma tcbQueueRemove_valid_mdb':
  "\<lbrace>\<lambda>s. valid_mdb' s \<and> valid_objs' s\<rbrace> tcbQueueRemove q tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding tcbQueueRemove_def
  apply (wpsimp wp: getTCB_wp)
  apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
  apply (fastforce simp: valid_tcb'_def obj_at'_def)
  done

lemma tcbQueuePrepend_valid_mdb':
  "\<lbrace>valid_mdb' and tcb_at' tcbPtr
    and (\<lambda>s. \<not> tcbQueueEmpty queue \<longrightarrow> tcb_at' (the (tcbQueueHead queue)) s)\<rbrace>
   tcbQueuePrepend queue tcbPtr
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding tcbQueuePrepend_def
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')

lemma tcbQueueAppend_valid_mdb':
  "\<lbrace>\<lambda>s. valid_mdb' s \<and> tcb_at' tcbPtr s
        \<and> (\<not> tcbQueueEmpty queue \<longrightarrow> tcb_at' (the (tcbQueueEnd queue)) s)\<rbrace>
   tcbQueueAppend queue tcbPtr
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding tcbQueueAppend_def
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')

lemma tcbQueued_update_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and tcb_at' tcbPtr\<rbrace> threadSet (tcbQueued_update f) tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (wpsimp wp: threadSet_mdb')
  apply (fastforce simp: obj_at'_def valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

lemma valid_mdb'_ksReadyQueuesL1Bitmap_update[simp]:
  "valid_mdb' (ksReadyQueuesL1Bitmap_update f s) = valid_mdb' s"
  by (simp add: valid_mdb'_def)

lemma valid_mdb'_ksReadyQueuesL2Bitmap_update[simp]:
  "valid_mdb' (ksReadyQueuesL2Bitmap_update f s) = valid_mdb' s"
  by (simp add: valid_mdb'_def)

lemma tcbSchedEnqueue_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and valid_objs' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedEnqueue tcbPtr
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (clarsimp simp: tcbSchedEnqueue_def setQueue_def)
  apply (wpsimp wp: tcbQueuePrepend_valid_mdb' threadGet_wp simp: bitmap_fun_defs)
  apply normalise_obj_at'
  apply (fastforce dest!: obj_at'_tcbQueueHead_ksReadyQueues
                    simp: ready_queue_relation_def ksReadyQueues_asrt_def obj_at'_def)
  done

crunch tcbSchedEnqueue
  for cur_tcb'[wp]: cur_tcb'
  (wp: threadSet_cur)

lemma tcbSchedEnqueue_invs'[wp]:
  "\<lbrace>invs' and st_tcb_at' runnable' t\<rbrace>
   tcbSchedEnqueue t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_dom_schedule'_def)
  apply (wpsimp wp: valid_irq_node_lift irqs_masked_lift valid_irq_handlers_lift' cur_tcb_lift
                    untyped_ranges_zero_lift
              simp: cteCaps_of_def o_def)
  apply (auto elim!: st_tcb_ex_cap'')
  done

crunch tcbSchedAppend
  for ksMachine[wp]: "\<lambda>s. P (ksMachineState s)"
  (simp: unless_def)

lemma tcbSchedAppend_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> tcbSchedAppend t \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

crunch tcbSchedAppend
  for pspace_domain_valid[wp]: "pspace_domain_valid"
  (simp: unless_def)

crunch tcbSchedAppend
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
(simp: unless_def)

crunch tcbSchedAppend
  for ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
(simp: unless_def)

crunch tcbSchedAppend
  for ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
(simp: unless_def)

lemma tcbQueueAppend_tcbPriority_obj_at'[wp]:
  "tcbQueueAppend queue tptr \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  unfolding tcbQueueAppend_def
  apply (wpsimp wp: threadSet_wp)
  by (auto simp: obj_at'_def projectKOs objBits_simps ps_clear_def split: if_splits)

lemma tcbQueueAppend_tcbDomain_obj_at'[wp]:
  "tcbQueueAppend queue tptr \<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  unfolding tcbQueueAppend_def
  apply (wpsimp wp: threadSet_wp)
  by (auto simp: obj_at'_def projectKOs objBits_simps ps_clear_def split: if_splits)

lemma tcbSchedAppend_tcbDomain[wp]:
  "tcbSchedAppend t \<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  apply (clarsimp simp: tcbSchedAppend_def)
  by wpsimp

lemma tcbSchedAppend_tcbPriority[wp]:
  "tcbSchedAppend t \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  apply (clarsimp simp: tcbSchedAppend_def)
  by wpsimp

lemma tcbSchedAppend_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> tcbSchedAppend t \<lbrace>\<lambda>_. tcb_in_cur_domain' t' \<rbrace>"
  apply (rule tcb_in_cur_domain'_lift)
   apply wp+
  done

crunch tcbSchedAppend, tcbSchedDequeue
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (simp: unless_def)

lemma tcbSchedAppend_sch_act_wf[wp]:
  "tcbSchedAppend thread \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wpsimp wp: sch_act_wf_lift)

lemma tcbSchedAppend_valid_bitmapQ[wp]:
  "\<lbrace>valid_bitmaps\<rbrace> tcbSchedAppend tcbPtr \<lbrace>\<lambda>_. valid_bitmapQ\<rbrace>"
  supply if_split[split del]
  unfolding tcbSchedAppend_def
  apply (wpsimp simp: tcbQueueAppend_def
                  wp: setQueue_valid_bitmapQ' addToBitmap_valid_bitmapQ_except addToBitmap_bitmapQ
                      threadGet_wp hoare_vcg_if_lift2)
  apply (clarsimp simp: ksReadyQueues_asrt_def split: if_splits)
  apply normalise_obj_at'
  apply (force dest: tcbQueueHead_iff_tcbQueueEnd
               simp: valid_bitmaps_def valid_bitmapQ_def tcbQueueEmpty_def)
  done

lemma tcbSchedAppend_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and valid_tcbs' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedAppend tcbPtr
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (clarsimp simp: tcbSchedAppend_def setQueue_def)
  apply (wpsimp wp: tcbQueueAppend_valid_mdb' threadGet_wp simp: bitmap_fun_defs)
  by (fastforce dest: obj_at'_tcbQueueEnd_ksReadyQueues
                simp: ready_queue_relation_def ksReadyQueues_asrt_def obj_at'_def projectKOs)

lemma tcbSchedAppend_valid_bitmaps[wp]:
  "tcbSchedAppend tcbPtr \<lbrace>valid_bitmaps\<rbrace>"
  unfolding valid_bitmaps_def
  apply wpsimp
  apply (clarsimp simp: valid_bitmaps_def)
  done

crunch tcbSchedAppend
  for list_refs_of_replies'[wp]: "\<lambda>s. P (list_refs_of_replies' s)"

lemma tcbSchedAppend_valid_release_queue[wp]:
  "tcbSchedAppend t \<lbrace>valid_release_queue\<rbrace>"
  unfolding tcbSchedAppend_def
  apply (wpsimp simp: valid_release_queue_def Ball_def addToBitmap_def
                      modifyReadyQueuesL2Bitmap_def getReadyQueuesL2Bitmap_def
                      modifyReadyQueuesL1Bitmap_def getReadyQueuesL1Bitmap_def
                  wp: hoare_vcg_all_lift hoare_vcg_imp_lift' threadGet_wp)
  by (auto simp: obj_at'_def)

crunch addToBitmap
  for ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"

lemma tcbSchedAppend_valid_release_queue'[wp]:
  "tcbSchedAppend t \<lbrace>valid_release_queue'\<rbrace>"
  unfolding tcbSchedAppend_def threadGet_def
  apply (wpsimp simp: valid_release_queue'_def
                  wp: threadSet_valid_release_queue' hoare_vcg_all_lift hoare_vcg_imp_lift'
                      getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma tcbSchedAppend_invs'[wp]:
  "\<lbrace>invs' and st_tcb_at' runnable' t\<rbrace>
   tcbSchedAppend t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_dom_schedule'_def)
  apply (rule hoare_pre)
   apply (wp tcbSchedAppend_ct_not_inQ valid_irq_node_lift irqs_masked_lift hoare_vcg_disj_lift
             valid_irq_handlers_lift' cur_tcb_lift ct_idle_or_in_cur_domain'_lift2
             untyped_ranges_zero_lift
        | simp add: cteCaps_of_def o_def
        | auto elim!: st_tcb_ex_cap'' valid_objs'_maxDomain valid_objs'_maxPriority split: thread_state.split_asm simp: valid_pspace'_def)+
  done

lemma tcb_at'_has_tcbDomain:
 "tcb_at' t s \<Longrightarrow> \<exists>p. obj_at' (\<lambda>tcb. tcbDomain tcb = p) t s"
 by (clarsimp simp add: obj_at'_def)

crunch tcbSchedDequeue
  for ksMachine[wp]: "\<lambda>s. P (ksMachineState s)"
  (simp: unless_def)

lemma tcbSchedDequeue_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

crunch tcbSchedDequeue
  for pspace_domain_valid[wp]: "pspace_domain_valid"

crunch tcbSchedDequeue
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
(simp: unless_def)

crunch tcbSchedDequeue
  for ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
(simp: unless_def)

crunch tcbSchedDequeue
  for ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
(simp: unless_def)

lemma tcbSchedDequeue_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. tcb_in_cur_domain' t' \<rbrace>"
  apply (rule tcb_in_cur_domain'_lift)
   apply wp
  apply (clarsimp simp: tcbSchedDequeue_def tcbQueueRemove_def)
  apply (wpsimp wp: hoare_when_weak_wp getObject_tcb_wp threadGet_wp)
  done

crunch tcbSchedDequeue
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  (simp: unless_def)

lemma tcbSchedDequeue_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and valid_objs'\<rbrace> tcbSchedDequeue tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (wpsimp simp: bitmap_fun_defs setQueue_def wp: threadSet_mdb' tcbQueueRemove_valid_mdb')
      apply (rule_tac Q="\<lambda>_. tcb_at' tcbPtr" in hoare_post_imp)
       apply (fastforce simp: tcb_cte_cases_def cteSizeBits_def)
      apply (wpsimp wp: threadGet_wp)+
  apply (fastforce simp: obj_at'_def)
  done

lemma tcbSchedDequeue_invs'[wp]:
  "tcbSchedDequeue t \<lbrace>invs'\<rbrace>"
  unfolding invs'_def
  apply (rule hoare_pre)
   apply (wp valid_irq_node_lift irqs_masked_lift
             valid_irq_handlers_lift' cur_tcb_lift ct_idle_or_in_cur_domain'_lift2
             tcbSchedDequeue_valid_queues untyped_ranges_zero_lift
          | simp add: cteCaps_of_def o_def valid_dom_schedule'_def)+
  apply (auto simp: valid_pspace'_def obj_at'_def
              dest: valid_objs'_maxDomain[where t=t] valid_objs'_maxPriority[where t=t])
  done

lemma ready_qs_runnable_cross:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s; valid_queues s\<rbrakk>
   \<Longrightarrow> ready_qs_runnable s'"
  apply (clarsimp simp: ready_qs_runnable_def)
  apply normalise_obj_at'
  apply (frule state_relation_ready_queues_relation)
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def
                        list_queue_relation_def)
  apply (drule_tac x="tcbDomain ko" in spec)
  apply (drule_tac x="tcbPriority ko" in spec)
  apply (clarsimp simp: valid_queues_def)
  apply (drule_tac x="tcbDomain ko" in spec)
  apply (drule_tac x="tcbPriority ko" in spec)
  apply clarsimp
  apply (drule_tac x=t in bspec)
   apply (fastforce simp: inQ_def in_opt_pred obj_at'_def projectKOs opt_map_red)
  apply (fastforce dest: st_tcb_at_runnable_cross simp: obj_at'_def projectKOs st_tcb_at'_def)
  done

method add_ready_qs_runnable =
  rule_tac Q'=ready_qs_runnable in corres_cross_add_guard,
  (clarsimp simp: pred_conj_def)?,
  (frule valid_sched_valid_queues)?, (frule invs_psp_aligned)?, (frule invs_distinct)?,
  fastforce dest: ready_qs_runnable_cross

defs idleThreadNotQueued_def:
  "idleThreadNotQueued s \<equiv> obj_at' (Not \<circ> tcbQueued) (ksIdleThread s) s"

lemma idle_thread_not_queued:
  "\<lbrakk>valid_idle s; valid_queues s; valid_etcbs s\<rbrakk>
   \<Longrightarrow> \<not> (\<exists>d p. idle_thread s \<in> set (ready_queues s d p))"
  apply (clarsimp simp: valid_queues_def)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (drule_tac x="idle_thread s" in bspec)
   apply fastforce
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def valid_etcbs_def)
  done

lemma valid_idle_tcb_at:
  "valid_idle s \<Longrightarrow> tcb_at (idle_thread s) s"
  by (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def is_tcb_def)

lemma setCurThread_corres:
  "corres dc (pspace_aligned and pspace_distinct and valid_ready_qs) \<top>
             (modify (cur_thread_update (\<lambda>_. t))) (setCurThread t)"
  apply add_ready_qs_runnable
  apply (unfold setCurThread_def)
  apply (rule corres_stateAssert_add_assertion[rotated]; clarsimp)
  apply (rule corres_modify)
  apply (simp add: state_relation_def swp_def)
  done

lemma arch_switch_thread_tcb_at' [wp]:
  "Arch.switchToThread t \<lbrace>\<lambda>s. P (tcb_at' t s)\<rbrace>"
  by (unfold ARM_H.switchToThread_def, wp typ_at_lifts)

crunch "switchToThread"
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (ignore: clearExMonitor)

lemma Arch_switchToThread_pred_tcb'[wp]:
  "\<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>
   Arch.switchToThread t \<lbrace>\<lambda>rv s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
proof -
  have pos: "\<And>P t t'. \<lbrace>pred_tcb_at' proj P t'\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>rv. pred_tcb_at' proj P t'\<rbrace>"
    apply (simp add:  pred_tcb_at'_def ARM_H.switchToThread_def)
    apply (rule bind_wp)+
       apply (rule doMachineOp_obj_at)
     apply (rule setVMRoot_obj_at)
    done
  show ?thesis
    apply (rule P_bool_lift [OF pos])
    by (rule lift_neg_pred_tcb_at' [OF ArchThreadDecls_H_ARM_H_switchToThread_typ_at' pos])
qed

crunch doMachineOp
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"

crunch storeWordUser
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s p)"
crunch setVMRoot
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
(wp: crunch_wps simp: crunch_simps)
crunch storeWordUser
  for ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
crunch asUser
  for ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
(wp: crunch_wps simp: crunch_simps)
crunch asUser
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s p)"
(wp: crunch_wps simp: crunch_simps)

lemma arch_switch_thread_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s p)\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>_ s. P (ksReadyQueues s p)\<rbrace>"
  apply (simp add: ARM_H.switchToThread_def)
  apply (wp)
  done

crunch storeWordUser, setVMRoot, asUser, storeWordUser, Arch.switchToThread
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s p)"
  and ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_objs'[wp]: valid_objs'
  (wp: crunch_wps threadSet_sched_pointers simp: crunch_simps)

crunch arch_switch_to_thread, arch_switch_to_idle_thread
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  and ready_qs_distinct[wp]: ready_qs_distinct
  and valid_idle[wp]: valid_idle
  (wp: ready_qs_distinct_lift)

lemma valid_queues_in_correct_ready_q[elim!]:
  "valid_queues s \<Longrightarrow> in_correct_ready_q s"
  by (clarsimp simp: valid_queues_def in_correct_ready_q_def)

lemma valid_queues_ready_qs_distinct[elim!]:
  "valid_queues s \<Longrightarrow> ready_qs_distinct s"
  by (clarsimp simp: valid_queues_def ready_qs_distinct_def)

crunch arch_switch_to_thread
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct

lemma switchToThread_corres:
  "corres dc (valid_arch_state and valid_objs and valid_asid_map
                and valid_vspace_objs and pspace_aligned and pspace_distinct and valid_ready_qs
                and valid_vs_lookup and valid_global_objs
                and unique_table_refs o caps_of_state
                and st_tcb_at runnable t)
             (valid_arch_state' and valid_pspace' and Invariants_H.valid_queues
                and st_tcb_at' runnable' t and cur_tcb')
             (switch_to_thread t) (switchToThread t)"
  apply (rule_tac Q'="st_tcb_at' runnable' t" in corres_cross_add_guard)
   apply (fastforce intro!: st_tcb_at_runnable_cross simp: obj_at_def is_tcb_def)
  apply add_ready_qs_runnable
  apply (simp add: switch_to_thread_def Thread_H.switchToThread_def)
  apply (rule corres_symb_exec_l[OF _ _ get_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_l[OF _ _ assert_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ isRunnable_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ assert_sp, rotated]; (solves wpsimp)?)
   apply wpsimp
   apply (fastforce simp: st_tcb_at'_def runnable_eq_active' obj_at'_def)
    apply (rule corres_stateAssert_ignore)
     apply (fastforce dest!: state_relation_ready_queues_relation intro: ksReadyQueues_asrt_cross)
    apply (rule corres_stateAssert_add_assertion[rotated])
     apply fastforce
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF arch_switchToThread_corres])
        apply (rule corres_split[OF tcbSchedDequeue_corres setCurThread_corres])
         apply (wpsimp wp: tcb_sched_dequeue_valid_ready_qs | clarsimp simp: st_tcb_at_tcb_at)+
    done

  show ?thesis
    apply -
    apply (simp add: switch_to_thread_def Thread_H.switchToThread_def)
    apply add_ready_qs_runnable
    apply (rule corres_stateAssert_add_assertion)
     apply (rule corres_symb_exec_l[where Q = "\<lambda> s rv. (?PA and (=) rv) s"])
        apply (rule corres_symb_exec_l)
           apply (rule corres_guard_imp[OF mainpart])
            apply (auto intro: no_fail_pre [OF no_fail_assert] no_fail_pre [OF no_fail_get]
                         dest: st_tcb_at_tcb_at [THEN get_tcb_at]
                   | simp add: assert_def
                   | wp)+
    done
qed

lemma arch_switchToIdleThread_corres:
  "corres dc (valid_arch_state and valid_objs and valid_asid_map and unique_table_refs \<circ> caps_of_state and
      valid_vs_lookup and valid_global_objs and pspace_aligned and pspace_distinct and valid_vspace_objs and valid_idle)
     (valid_arch_state' and pspace_aligned' and pspace_distinct' and no_0_obj' and valid_idle')
        arch_switch_to_idle_thread
        Arch.switchToIdleThread"
  apply (simp add: arch_switch_to_idle_thread_def
                ARM_H.switchToIdleThread_def)
  apply (corresKsimp corres: getIdleThread_corres setVMRoot_corres[@lift_corres_args])
  apply (clarsimp simp: valid_idle_def valid_idle'_def pred_tcb_at_def obj_at_def is_tcb obj_at'_def)
  done

crunch switchToIdleThread
  for ready_qs_runnable[wp]: "\<lambda>s. \<forall>d p. \<forall>t\<in>set (ksReadyQueues s (d, p)).
                       st_tcb_at' runnable' t s"
  (simp: crunch_simps)

lemma switchToIdleThread_corres:
  "corres dc (invs and valid_ready_qs) invs' switch_to_idle_thread switchToIdleThread"
  apply add_ready_qs_runnable
  apply add_valid_idle'
  apply (simp add: switch_to_idle_thread_def Thread_H.switchToIdleThread_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply clarsimp
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (clarsimp simp: valid_idle'_asrt_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getIdleThread_corres])
      apply (rule corres_split[OF arch_switchToIdleThread_corres])
        apply (unfold setCurThread_def)
        apply (rule corres_stateAssert_add_assertion)
         apply clarsimp
         apply (rule corres_modify)
        apply (simp add: state_relation_def cdt_relation_def)
        apply (simp only: ready_qs_runnable_def)
       apply wpsimp+
   apply (simp add: invs_unique_refs invs_valid_vs_lookup invs_valid_objs invs_valid_asid_map
                    invs_arch_state invs_valid_global_objs invs_psp_aligned invs_distinct
                    invs_valid_idle invs_vspace_objs)
  apply (simp add: invs'_def valid_pspace'_def ready_qs_runnable_def)
  done

lemma gq_sp: "\<lbrace>P\<rbrace> getQueue d p \<lbrace>\<lambda>rv. P and (\<lambda>s. ksReadyQueues s (d, p) = rv)\<rbrace>"
  by (unfold getQueue_def, rule gets_sp)

lemma sch_act_wf:
  "sch_act_wf sa s = ((\<forall>t. sa = SwitchToThread t \<longrightarrow> st_tcb_at' runnable' t s \<and>
                                                    tcb_in_cur_domain' t s) \<and>
                      (sa = ResumeCurrentThread \<longrightarrow> ct_in_state' activatable' s))"
  by (case_tac sa,  simp_all add: )

declare gq_wp[wp]
declare setQueue_obj_at[wp]

lemma setCurThread_invs':
  "\<lbrace>invs' and tcb_at' t\<rbrace>
   setCurThread t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: setCurThread_def)
  apply wp
  apply (clarsimp simp add: invs'_def cur_tcb'_def valid_queues_def valid_release_queue_def
                            valid_release_queue'_def sch_act_wf ct_in_state'_def
                            state_refs_of'_def ps_clear_def valid_irq_node'_def valid_queues'_def
                            ct_idle_or_in_cur_domain'_def
                            bitmapQ_defs valid_queues_no_bitmap_def valid_dom_schedule'_def
                      cong: option.case_cong)
  done

lemma valid_queues_not_runnable_not_queued:
  fixes s
  assumes  vq: "valid_queues s"
      and rqr: "\<forall>d p. (\<forall>t \<in> set (ksReadyQueues s (d, p)). st_tcb_at' runnable' t s)"
      and vq': "valid_queues' s"
      and  st: "st_tcb_at' (Not \<circ> runnable') t s"
  shows "obj_at' (Not \<circ> tcbQueued) t s"
proof (rule ccontr)
  assume "\<not> obj_at' (Not \<circ> tcbQueued) t s"
  moreover from st have "typ_at' TCBT t s"
    by (rule pred_tcb_at' [THEN tcb_at_typ_at' [THEN iffD1]])
  ultimately have "obj_at' tcbQueued t s"
    by (clarsimp simp: not_obj_at' comp_def)

  moreover
  from st [THEN pred_tcb_at', THEN tcb_at'_has_tcbPriority]
  obtain p where tp: "obj_at' (\<lambda>tcb. tcbPriority tcb = p) t s"
    by clarsimp

  moreover
  from st [THEN pred_tcb_at', THEN tcb_at'_has_tcbDomain]
  obtain d where td: "obj_at' (\<lambda>tcb. tcbDomain tcb = d) t s"
    by clarsimp

  ultimately
  have "t \<in> set (ksReadyQueues s (d, p))" using vq'
    unfolding valid_queues'_def
    apply -
    apply (drule_tac x=d in spec)
    apply (drule_tac x=p in spec)
    apply (drule_tac x=t in spec)
    apply (erule impE)
     apply (fastforce simp add: inQ_def obj_at'_def)
    apply (assumption)
    done

  with vq rqr have "st_tcb_at' runnable' t s"
    unfolding Invariants_H.valid_queues_def valid_queues_no_bitmap_def
    apply -
    apply clarsimp
    done

  with st show False
    apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
    done
qed

(*
 * The idle thread is not part of any ready queues.
 *)
lemma idle'_not_tcbQueued':
 assumes   vq:  "Invariants_H.valid_queues s"
     and  rqr:  "\<forall>d p. (\<forall>t \<in> set (ksReadyQueues s (d, p)). st_tcb_at' runnable' t s)"
     and  vq':  "valid_queues' s"
     and idle: "valid_idle' s"
 shows "obj_at' (Not \<circ> tcbQueued) (ksIdleThread s) s"
 proof -
   from idle have stidle: "st_tcb_at' (Not \<circ> runnable') (ksIdleThread s) s"
     by (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def projectKOs idle_tcb'_def)

   with vq rqr vq' show ?thesis
     by (rule valid_queues_not_runnable_not_queued)
 qed

lemma clearExMonitor_invs'[wp]:
  "doMachineOp ARM.clearExMonitor \<lbrace>invs'\<rbrace>"
  apply (wp dmo_invs' no_irq)
   apply (simp add: no_irq_clearExMonitor)
  apply (clarsimp simp: ARM.clearExMonitor_def machine_op_lift_def
                        in_monad select_f_def)
  done

lemma Arch_switchToThread_invs[wp]:
  "\<lbrace>invs'\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: ARM_H.switchToThread_def)
  apply (wp; auto)
  done

crunch "Arch.switchToThread"
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
(simp: crunch_simps)

lemma Arch_swichToThread_tcbDomain_triv[wp]:
  "\<lbrace> obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t' \<rbrace> Arch.switchToThread t \<lbrace> \<lambda>_. obj_at'  (\<lambda>tcb. P (tcbDomain tcb)) t' \<rbrace>"
  apply (clarsimp simp: ARM_H.switchToThread_def storeWordUser_def)
  apply (wp hoare_drop_imp | simp)+
  done

lemma Arch_swichToThread_tcbPriority_triv[wp]:
  "\<lbrace> obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t' \<rbrace> Arch.switchToThread t \<lbrace> \<lambda>_. obj_at'  (\<lambda>tcb. P (tcbPriority tcb)) t' \<rbrace>"
  apply (clarsimp simp: ARM_H.switchToThread_def storeWordUser_def)
  apply (wp hoare_drop_imp | simp)+
  done

lemma Arch_switchToThread_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>_. tcb_in_cur_domain' t' \<rbrace>"
  apply (rule tcb_in_cur_domain'_lift)
   apply wp+
  done

lemma tcbSchedDequeue_not_tcbQueued:
  "\<lbrace>\<top>\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. obj_at' (\<lambda>x. \<not> tcbQueued x) t\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp|clarsimp)+
  apply (rule_tac Q="\<lambda>queued. obj_at' (\<lambda>x. tcbQueued x = queued) t" in hoare_post_imp)
     apply (clarsimp simp: obj_at'_def)
    apply (wpsimp wp: threadGet_wp)+
  apply (clarsimp simp: obj_at'_def)
  done

lemma Arch_switchToThread_obj_at[wp]:
  "\<lbrace>obj_at' (P \<circ> tcbState) t\<rbrace>
   Arch.switchToThread t
   \<lbrace>\<lambda>rv. obj_at' (P \<circ> tcbState) t\<rbrace>"
  apply (simp add: ARM_H.switchToThread_def )
  apply (rule bind_wp)+
   apply (rule doMachineOp_obj_at)
  apply (rule setVMRoot_obj_at)
  done

declare doMachineOp_obj_at[wp]

crunch asUser
 for valid_arch_state'[wp]: "valid_arch_state'"
(wp: crunch_wps simp: crunch_simps)

crunch asUser
  for valid_irq_states'[wp]: "valid_irq_states'"
(wp: crunch_wps simp: crunch_simps)

crunch asUser
  for valid_machine_state'[wp]: "valid_machine_state'"
(wp: crunch_wps simp: crunch_simps)

crunch asUser
  for irq_masked'_helper: "\<lambda>s. P (intStateIRQTable (ksInterruptState s))"
(wp: crunch_wps simp: crunch_simps)

crunch asUser
  for valid_pde_mappings'[wp]: "valid_pde_mappings'"
(wp: crunch_wps simp: crunch_simps)

crunch asUser
  for pspace_domain_valid[wp]: "pspace_domain_valid"
(wp: crunch_wps simp: crunch_simps)

crunch asUser
  for valid_dom_schedule'[wp]: "valid_dom_schedule'"
(wp: crunch_wps simp: crunch_simps)

crunch asUser
  for gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps simp: unless_def)

crunch asUser
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps simp: unless_def)

lemmas asUser_cteCaps_of[wp] = cteCaps_of_ctes_of_lift[OF asUser_ctes_of]

lemma switchToThread_invs'_helper:
  "\<lbrace>invs' and tcb_at' t\<rbrace>
   do y \<leftarrow> ARM_H.switchToThread t;
      y \<leftarrow> tcbSchedDequeue t;
      setCurThread t
   od
   \<lbrace>\<lambda>rv. invs' \<rbrace>"
  apply (wp setCurThread_invs' tcbSchedDequeue_not_tcbQueued Arch_switchToThread_pred_tcb')
  apply auto
  done

lemma switchToThread_invs'[wp]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> switchToThread t \<lbrace>\<lambda>_. invs' \<rbrace>"
  apply (simp add: Thread_H.switchToThread_def )
  apply (wp setCurThread_invs' Arch_switchToThread_invs dmo_invs'
            doMachineOp_obj_at tcbSchedDequeue_not_tcbQueued)
  by (auto elim!: pred_tcb'_weakenE)

lemma setCurThread_ct_in_state:
  "\<lbrace>obj_at' (P \<circ> tcbState) t\<rbrace> setCurThread t \<lbrace>\<lambda>rv. ct_in_state' P\<rbrace>"
proof -
  show ?thesis
    apply (simp add: setCurThread_def)
    apply wp
    apply (simp add: ct_in_state'_def pred_tcb_at'_def o_def)
    done
qed

lemma switchToThread_ct_in_state[wp]:
  "\<lbrace>obj_at' (P \<circ> tcbState) t\<rbrace> switchToThread t \<lbrace>\<lambda>rv. ct_in_state' P\<rbrace>"
  apply (simp add: Thread_H.switchToThread_def tcbSchedEnqueue_def unless_def)
  apply (wp setCurThread_ct_in_state Arch_switchToThread_obj_at
         | simp add: o_def cong: if_cong)+
  done

lemma setCurThread_obj_at[wp]:
  "\<lbrace>obj_at' P addr\<rbrace> setCurThread t \<lbrace>\<lambda>rv. obj_at' P addr\<rbrace>"
  apply (simp add: setCurThread_def)
  apply wp
  apply (fastforce intro: obj_at'_pspaceI)
  done

lemma dmo_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace>
     doMachineOp m
   \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  by (wp ex_nonz_cap_to_pres')

lemma sct_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> setCurThread t \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp add: setCurThread_def)
  apply (wpsimp wp: ex_nonz_cap_to_pres')
  done


crunch "Arch.switchToThread"
  for cap_to'[wp]: "ex_nonz_cap_to' p"
  (simp: crunch_simps ignore: ARM.clearExMonitor)

crunch switchToThread
  for cap_to'[wp]: "ex_nonz_cap_to' p"
  (simp: crunch_simps ignore: ARM.clearExMonitor)

lemma iflive_inQ_nonz_cap_strg:
  "if_live_then_nonz_cap' s \<and> obj_at' (inQ d prio) t s
          \<longrightarrow> ex_nonz_cap_to' t s"
  by (clarsimp simp: obj_at'_real_def projectKOs inQ_def
              elim!: if_live_then_nonz_capE' ko_wp_at'_weakenE)

lemmas iflive_inQ_nonz_cap[elim]
    = mp [OF iflive_inQ_nonz_cap_strg, OF conjI[rotated]]

declare Cons_eq_tails[simp]

crunch "ThreadDecls_H.switchToThread"
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"

(* FIXME move *)
lemma obj_tcb_at':
  "obj_at' (\<lambda>tcb::tcb. P tcb) t s \<Longrightarrow> tcb_at' t s"
  by (clarsimp simp: obj_at'_def)

lemma valid_queues_not_tcbQueued_not_ksQ:
  fixes s
  assumes   vq: "valid_queues s"
      and notq: "obj_at' (Not \<circ> tcbQueued) t s"
  shows "\<forall>d p. t \<notin> set (ksReadyQueues s (d, p))"
proof (rule ccontr, simp , erule exE, erule exE)
  fix d p
  assume "t \<in> set (ksReadyQueues s (d, p))"
  with vq have "obj_at' (inQ d p) t s"
    by (fastforce intro: valid_queues_obj_at'D)
  hence "obj_at' tcbQueued t s"
    apply (rule obj_at'_weakenE)
    apply (simp only: inQ_def)
    done
  with notq show "False"
    by (clarsimp simp: obj_at'_def)
qed

lemma not_tcbQueued_not_ksQ:
  fixes s
  assumes "invs' s"
      and "obj_at' (Not \<circ> tcbQueued) t s"
  shows "\<forall>d p. t \<notin> set (ksReadyQueues s (d, p))"
  apply (insert assms)
  apply (clarsimp simp add: invs'_def)
  apply (drule(1) valid_queues_not_tcbQueued_not_ksQ)
  apply clarsimp
  done

lemma ct_not_ksQ:
  "\<lbrakk> ct_not_inQ s; valid_queues s; ksSchedulerAction s = ResumeCurrentThread \<rbrakk>
   \<Longrightarrow> \<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p)"
  apply (clarsimp simp: ct_not_inQ_def)
  apply (frule(1) valid_queues_not_tcbQueued_not_ksQ)
  apply (fastforce)
  done

lemma scheduleTCB_rct:
  "\<lbrace>\<lambda>s. (t = ksCurThread s \<longrightarrow> isSchedulable_bool t s)
        \<and> ksSchedulerAction s = ResumeCurrentThread\<rbrace>
   scheduleTCB t
   \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread\<rbrace>"
  unfolding scheduleTCB_def
  by (wpsimp wp: isSchedulable_wp | rule hoare_pre_cont)+

lemma setThreadState_rct:
  "\<lbrace>\<lambda>s. (t = ksCurThread s \<longrightarrow> runnable' st
      \<and> pred_map (\<lambda>tcb. \<not>(tcbInReleaseQueue tcb)) (tcbs_of' s) t
      \<and> pred_map (\<lambda>scPtr. isScActive scPtr s) (tcbSCs_of s) t)
        \<and> ksSchedulerAction s = ResumeCurrentThread\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread\<rbrace>"
  unfolding setThreadState_def
  by (wpsimp wp: scheduleTCB_rct hoare_vcg_all_lift hoare_vcg_imp_lift' threadSet_isSchedulable_bool)

lemma bitmapQ_lookupBitmapPriority_simp: (* neater unfold, actual unfold is really ugly *)
  "\<lbrakk> ksReadyQueuesL1Bitmap s d \<noteq> 0 ;
     valid_bitmapQ s ; bitmapQ_no_L1_orphans s \<rbrakk> \<Longrightarrow>
   bitmapQ d (lookupBitmapPriority d s) s =
    (ksReadyQueuesL1Bitmap s d !! word_log2 (ksReadyQueuesL1Bitmap s d) \<and>
     ksReadyQueuesL2Bitmap s (d, invertL1Index (word_log2 (ksReadyQueuesL1Bitmap s d))) !!
       word_log2 (ksReadyQueuesL2Bitmap s (d, invertL1Index (word_log2 (ksReadyQueuesL1Bitmap s d)))))"
  unfolding bitmapQ_def lookupBitmapPriority_def
  apply (drule word_log2_nth_same, clarsimp)
  apply (drule (1) bitmapQ_no_L1_orphansD, clarsimp)
  apply (drule word_log2_nth_same, clarsimp)
  apply (frule test_bit_size[where n="word_log2 (ksReadyQueuesL2Bitmap _ _)"])
  apply (clarsimp simp: numPriorities_def wordBits_def word_size)
  apply (subst prioToL1Index_l1IndexToPrio_or_id)
    apply (subst unat_of_nat_eq)
    apply (fastforce intro: unat_less_helper word_log2_max[THEN order_less_le_trans]
                      simp: wordRadix_def word_size l2BitmapSize_def')+
  apply (subst prioToL1Index_l1IndexToPrio_or_id)
    apply (fastforce intro: unat_less_helper word_log2_max of_nat_mono_maybe
                      simp: wordRadix_def word_size l2BitmapSize_def')+
  apply (simp add: word_ao_dist)
  apply (subst less_mask_eq)
   apply (fastforce intro: word_of_nat_less simp: wordRadix_def' unat_of_nat word_size)+
  apply (subst unat_of_nat_eq)
   apply (fastforce intro: word_log2_max[THEN order_less_le_trans] simp: word_size)+
  done

lemma bitmapQ_from_bitmap_lookup:
  "\<lbrakk> ksReadyQueuesL1Bitmap s d \<noteq> 0 ;
     valid_bitmapQ s ; bitmapQ_no_L1_orphans s
     \<rbrakk>
   \<Longrightarrow> bitmapQ d (lookupBitmapPriority d s) s"
  apply (simp add: bitmapQ_lookupBitmapPriority_simp)
  apply (drule word_log2_nth_same)
  apply (drule (1) bitmapQ_no_L1_orphansD)
  apply (fastforce dest!: word_log2_nth_same
                   simp: word_ao_dist lookupBitmapPriority_def word_size numPriorities_def
                         wordBits_def)
  done

lemma lookupBitmapPriority_obj_at':
  "\<lbrakk>ksReadyQueuesL1Bitmap s d \<noteq> 0; valid_bitmapQ s; bitmapQ_no_L1_orphans s;
    ksReadyQueues_asrt s; ready_qs_runnable s; pspace_aligned' s; pspace_distinct' s\<rbrakk>
   \<Longrightarrow> obj_at' (inQ d (lookupBitmapPriority d s) and runnable' \<circ> tcbState)
               (the (tcbQueueHead (ksReadyQueues s (d, lookupBitmapPriority d s)))) s"
  apply (drule (2) bitmapQ_from_bitmap_lookup)
  apply (simp add: valid_bitmapQ_bitmapQ_simp)
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def tcbQueueEmpty_def)
  apply (drule_tac x=d in spec)
  apply (drule_tac x="lookupBitmapPriority d s" in spec)
  apply clarsimp
  apply (frule (3) obj_at'_tcbQueueHead_ksReadyQueues)
  apply (fastforce simp: obj_at'_and ready_qs_runnable_def obj_at'_def st_tcb_at'_def inQ_def
                         tcbQueueEmpty_def)
  done

lemma bitmapL1_zero_ksReadyQueues:
  "\<lbrakk> valid_bitmapQ s ; bitmapQ_no_L1_orphans s \<rbrakk>
   \<Longrightarrow> (ksReadyQueuesL1Bitmap s d = 0) = (\<forall>p. tcbQueueEmpty (ksReadyQueues s (d, p)))"
  apply (cases "ksReadyQueuesL1Bitmap s d = 0")
   apply (force simp add: bitmapQ_def valid_bitmapQ_def)
  apply (fastforce dest: bitmapQ_from_bitmap_lookup simp: valid_bitmapQ_bitmapQ_simp)
  done

lemma prioToL1Index_le_mask:
  "\<lbrakk> prioToL1Index p = prioToL1Index p' ; p && mask wordRadix \<le> p' && mask wordRadix \<rbrakk>
   \<Longrightarrow> p \<le> p'"
  unfolding prioToL1Index_def
  apply (simp add: wordRadix_def word_le_nat_alt[symmetric])
  apply (drule shiftr_eq_neg_mask_eq)
  apply (metis add.commute word_and_le2 word_plus_and_or_coroll2 word_plus_mono_left)
  done

lemma prioToL1Index_le_index:
  "\<lbrakk> prioToL1Index p \<le> prioToL1Index p' ; prioToL1Index p \<noteq> prioToL1Index p' \<rbrakk>
   \<Longrightarrow> p \<le> p'"
  unfolding prioToL1Index_def
  apply (simp add: wordRadix_def word_le_nat_alt[symmetric])
  apply (erule (1) le_shiftr')
  done

lemma bitmapL1_highest_lookup:
  "\<lbrakk> valid_bitmapQ s ; bitmapQ_no_L1_orphans s ;
     bitmapQ d p' s \<rbrakk>
   \<Longrightarrow> p' \<le> lookupBitmapPriority d s"
  apply (subgoal_tac "ksReadyQueuesL1Bitmap s d \<noteq> 0")
   prefer 2
   apply (clarsimp simp add: bitmapQ_def)
  apply (case_tac "prioToL1Index (lookupBitmapPriority d s) = prioToL1Index p'")
   apply (rule prioToL1Index_le_mask, simp)
   apply (frule (2) bitmapQ_from_bitmap_lookup)
   apply (clarsimp simp: bitmapQ_lookupBitmapPriority_simp)
   apply (clarsimp simp: bitmapQ_def lookupBitmapPriority_def)
   apply (subst mask_or_not_mask[where n=wordRadix and x=p', symmetric])
   apply (subst word_bw_comms(2)) (* || commute *)
   apply (simp add: word_ao_dist mask_AND_NOT_mask mask_twice)
   apply (subst less_mask_eq[where x="of_nat _"])
    apply (subst word_less_nat_alt)
    apply (subst unat_of_nat_eq)
     apply (rule order_less_le_trans[OF word_log2_max])
     apply (simp add: word_size)
    apply (rule order_less_le_trans[OF word_log2_max])
    apply (simp add: word_size wordRadix_def')
   apply (subst word_le_nat_alt)
   apply (subst unat_of_nat_eq)
    apply (rule order_less_le_trans[OF word_log2_max], simp add: word_size)
   apply (rule word_log2_highest)
   apply (subst (asm) prioToL1Index_l1IndexToPrio_or_id)
     apply (subst unat_of_nat_eq)
      apply (rule order_less_le_trans[OF word_log2_max], simp add: word_size)
     apply (rule order_less_le_trans[OF word_log2_max], simp add: word_size wordRadix_def')
    apply (simp add: word_size)
    apply (drule (1) bitmapQ_no_L1_orphansD[where d=d and i="word_log2 _"])
    apply (simp add: numPriorities_def wordBits_def word_size l2BitmapSize_def')
   apply simp
  apply (rule prioToL1Index_le_index[rotated], simp)
  apply (frule (2) bitmapQ_from_bitmap_lookup)
  apply (clarsimp simp: bitmapQ_lookupBitmapPriority_simp)
  apply (clarsimp simp: bitmapQ_def lookupBitmapPriority_def)
  apply (subst prioToL1Index_l1IndexToPrio_or_id)
    apply (subst unat_of_nat_eq)
     apply (rule order_less_le_trans[OF word_log2_max], simp add: word_size)
    apply (rule order_less_le_trans[OF word_log2_max], simp add: word_size wordRadix_def')
   apply (fastforce dest: bitmapQ_no_L1_orphansD
                    simp: wordBits_def numPriorities_def word_size l2BitmapSize_def')
  apply (erule word_log2_highest)
  done

lemma bitmapQ_ksReadyQueuesI:
  "\<lbrakk> bitmapQ d p s ; valid_bitmapQ s \<rbrakk> \<Longrightarrow> \<not> tcbQueueEmpty (ksReadyQueues s (d, p))"
  unfolding valid_bitmapQ_def by simp

lemma getReadyQueuesL2Bitmap_inv[wp]:
  "\<lbrace> P \<rbrace> getReadyQueuesL2Bitmap d i \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding getReadyQueuesL2Bitmap_def by wp

lemma switchToThread_lookupBitmapPriority_wp:
  "\<lbrace>\<lambda>s. invs' s \<and> bitmapQ (ksCurDomain s) (lookupBitmapPriority (ksCurDomain s) s) s \<and>
        t = hd (ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s)) \<rbrace>
   ThreadDecls_H.switchToThread t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  have switchToThread_pre:
    "\<And>s p t.\<lbrakk> valid_queues s ; \<forall>d p. \<forall>t \<in> set (ksReadyQueues s (d, p)). st_tcb_at' runnable' t s;
              bitmapQ (ksCurDomain s) p s ; t = hd (ksReadyQueues s (ksCurDomain s, p)) \<rbrakk>
            \<Longrightarrow> st_tcb_at' runnable' t s \<and> tcb_in_cur_domain' t s"
    unfolding valid_queues_def
    apply (clarsimp dest!: bitmapQ_ksReadyQueuesI)
    apply (case_tac "ksReadyQueues s (ksCurDomain s, p)", simp)
    apply (rename_tac t ts)
    apply (drule_tac t=t and p=p and d="ksCurDomain s" in valid_queues_no_bitmap_objD)
     apply simp
    apply (fastforce intro: cons_set_intro
                      elim: obj_at'_weaken
                      simp: inQ_def tcb_in_cur_domain'_def)
    done
  thus ?thesis
    apply (simp add: Thread_H.switchToThread_def)
    apply (rule bind_wp[OF _ stateAssert_sp])
    apply (wp switchToThread_invs'_helper)
    apply (fastforce simp: st_tcb_at'_def obj_at_simps invs'_def ready_qs_runnable_def)
    done
qed

lemma switchToIdleThread_invs':
  "switchToIdleThread \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: Thread_H.switchToIdleThread_def ARM_H.switchToIdleThread_def)
  apply (wpsimp wp: setCurThread_invs')
  apply (clarsimp simp: invs'_def valid_idle'_asrt_def
                 dest!: valid_idle'_tcb_at')
  done

crunch "Arch.switchToIdleThread"
  for obj_at'[wp]: "\<lambda>s. obj_at' P t s"


declare hoare_weak_lift_imp_conj[wp_split del]

lemma setCurThread_const:
  "\<lbrace>\<lambda>_. P t \<rbrace> setCurThread t \<lbrace>\<lambda>_ s. P (ksCurThread s) \<rbrace>"
  by (simp add: setCurThread_def | wp)+



crunch switchToIdleThread, switchToThread, chooseThread
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps)

lemma switchToIdleThread_curr_is_idle:
  "\<lbrace>\<top>\<rbrace> switchToIdleThread \<lbrace>\<lambda>rv s. ksCurThread s = ksIdleThread s\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (wps switchToIdleThread_it)
   apply (simp add: Thread_H.switchToIdleThread_def)
   apply (wp setCurThread_const)
  apply (simp)
 done

lemma corres_split_sched_act:
  "\<lbrakk>sched_act_relation act act';
    corres r P P' f1 g1;
    \<And>t. corres r (Q t) (Q' t) (f2 t) (g2 t);
    corres r R R' f3 g3\<rbrakk>
    \<Longrightarrow> corres r (case act of resume_cur_thread \<Rightarrow> P
                           | switch_thread t \<Rightarrow> Q t
                           | choose_new_thread \<Rightarrow> R)
               (case act' of ResumeCurrentThread \<Rightarrow> P'
                           | SwitchToThread t \<Rightarrow> Q' t
                           | ChooseThread \<Rightarrow> R')
       (case act of resume_cur_thread \<Rightarrow> f1
                  | switch_thread t \<Rightarrow> f2 t
                  | choose_new_thread \<Rightarrow> f3)
       (case act' of ResumeCurrentThread \<Rightarrow> g1
                   | ChooseNewThread \<Rightarrow> g3
                   | SwitchToThread t \<Rightarrow> g2 t)"
  apply (cases act)
    apply (rule corres_guard_imp, force+)+
    done

crunch tcbSchedEnqueue
 for cur[wp]: cur_tcb'
  (simp: unless_def)

lemma is_schedulable_exs_valid[wp]:
  "active_sc_tcb_at t s \<Longrightarrow> \<lbrace>(=) s\<rbrace> is_schedulable t \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  apply (clarsimp simp: is_schedulable_def exs_valid_def Bex_def pred_map_def vs_all_heap_simps
                 split: option.splits)
  apply (clarsimp simp: in_monad get_tcb_ko_at obj_at_def get_sched_context_def Option.is_none_def
                        get_object_def)
  done

lemma gts_exs_valid[wp]:
  "tcb_at t s \<Longrightarrow> \<lbrace>(=) s\<rbrace> get_thread_state t \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  apply (clarsimp simp: get_thread_state_def  assert_opt_def fail_def
             thread_get_def gets_the_def exs_valid_def gets_def
             get_def bind_def return_def split: option.splits)
  apply (erule get_tcb_at)
  done

lemma guarded_switch_to_corres:
  "corres dc (valid_arch_state and valid_objs and valid_asid_map
                and valid_vspace_objs and pspace_aligned and pspace_distinct
                and valid_vs_lookup and valid_global_objs
                and unique_table_refs o caps_of_state
                and schedulable t and valid_ready_qs)
             (valid_arch_state' and valid_pspace' and Invariants_H.valid_queues
                and st_tcb_at' runnable' t and cur_tcb')
             (guarded_switch_to t) (switchToThread t)"
  apply (simp add: guarded_switch_to_def)
  apply (rule corres_guard_imp)
    apply (rule corres_symb_exec_l'[OF _ thread_get_exs_valid])
      apply (rule corres_assert_opt_assume_l)
      apply (rule corres_symb_exec_l'[OF _ is_schedulable_exs_valid])
        apply (rule corres_assert_assume_l)
        apply (rule switchToThread_corres)
       apply assumption
      apply (wpsimp wp: is_schedulable_wp)
     apply assumption
    apply (wpsimp wp: thread_get_wp')
   apply (clarsimp simp: schedulable_def2 tcb_at_kh_simps pred_map_def vs_all_heap_simps
                         obj_at_def is_tcb)
  apply simp
  done

abbreviation "enumPrio \<equiv> [0.e.maxPriority]"

lemma curDomain_corres: "corres (=) \<top> \<top> (gets cur_domain) (curDomain)"
  by (simp add: curDomain_def state_relation_def)

lemma curDomain_corres':
  "corres (=) \<top> (\<lambda>s. ksCurDomain s \<le> maxDomain)
    (gets cur_domain) (if Suc 0 < numDomains then curDomain else return 0)"
  apply (case_tac "1 < numDomains"; simp)
   apply (rule corres_guard_imp[OF curDomain_corres]; solves simp)
  (* if we have only one domain, then we are in it *)
  apply (clarsimp simp: return_def simpler_gets_def bind_def maxDomain_def
                        state_relation_def corres_underlying_def)
  done

lemma lookupBitmapPriority_Max_eqI:
  "\<lbrakk> valid_bitmapQ s ; bitmapQ_no_L1_orphans s ; ksReadyQueuesL1Bitmap s d \<noteq> 0 \<rbrakk>
   \<Longrightarrow> lookupBitmapPriority d s = (Max {prio. \<not> tcbQueueEmpty (ksReadyQueues s (d, prio))})"
  apply (rule Max_eqI[simplified eq_commute]; simp)
   apply (fastforce simp: bitmapL1_highest_lookup valid_bitmapQ_bitmapQ_simp)
  apply (metis valid_bitmapQ_bitmapQ_simp bitmapQ_from_bitmap_lookup)
  done

lemma corres_gets_queues_getReadyQueuesL1Bitmap:
  "corres (\<lambda>qs l1. (l1 = 0) = (\<forall>p. qs p = [])) \<top> valid_bitmaps
    (gets (\<lambda>s. ready_queues s d)) (getReadyQueuesL1Bitmap d)"
  unfolding state_relation_def valid_bitmaps_def getReadyQueuesL1Bitmap_def
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
  apply (drule_tac x=d in spec)
  apply (fastforce simp: bitmapL1_zero_ksReadyQueues list_queue_relation_def tcbQueueEmpty_def)
  done

lemma tcb_at'_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and tcb_at t) (tcb_at' t)"
  unfolding cross_rel_def state_relation_def
  apply clarsimp
  by (erule (3) tcb_at_cross)

lemma sc_at'_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and sc_at t) (sc_at' t)"
  unfolding cross_rel_def state_relation_def
  apply clarsimp
  by (erule (3) sc_at_cross)

lemma ntfn_at'_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and ntfn_at t) (ntfn_at' t)"
  unfolding cross_rel_def state_relation_def
  apply clarsimp
  by (erule (3) ntfn_at_cross)

lemma runnable_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and st_tcb_at runnable t)
             (\<lambda>s'. pred_map (\<lambda>tcb. runnable' (tcbState tcb)) (tcbs_of' s') t)"
  apply (rule cross_rel_imp[OF tcb_at'_cross_rel[where t=t]])
  apply (clarsimp simp: cross_rel_def)
  apply (subgoal_tac "pspace_relation (kheap s) (ksPSpace s')")
  apply (clarsimp simp: tcb_at_kh_simps pred_map_def cross_rel_def obj_at'_def)
  apply (clarsimp simp: vs_all_heap_simps pspace_relation_def)
  apply (drule_tac x=t in bspec; clarsimp)
  apply (clarsimp simp: other_obj_relation_def split: option.splits)
  apply (case_tac "ko"; simp)
  apply (clarsimp simp: opt_map_def)
  apply (clarsimp simp: tcb_relation_def thread_state_relation_def)
  apply (case_tac "tcb_state b"; simp add: runnable_def)
  apply clarsimp
  apply clarsimp
  done

lemma tcbInReleaseQueue_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and tcb_at t and not_in_release_q t)
             (\<lambda>s'. valid_release_queue' s' \<longrightarrow> pred_map (\<lambda>tcb. \<not> tcbInReleaseQueue tcb) (tcbs_of' s') t)"
  apply (rule cross_rel_imp[OF tcb_at'_cross_rel[where t=t]])
  apply (clarsimp simp: cross_rel_def)
  apply (subgoal_tac "pspace_relation (kheap s) (ksPSpace s')")
  apply (clarsimp simp: pred_map_def cross_rel_def obj_at'_def obj_at_def is_tcb)
  apply (clarsimp simp: vs_all_heap_simps pspace_relation_def)
  apply (drule_tac x=t in bspec; clarsimp)
  apply (clarsimp simp: other_obj_relation_def split: option.splits)
  apply (case_tac "koa"; simp)
  apply (clarsimp simp: opt_map_def)
  apply (subgoal_tac "obj_at' tcbInReleaseQueue t s'")
  apply (subgoal_tac "release_queue_relation (release_queue s) (ksReleaseQueue s')")
  apply (clarsimp simp: release_queue_relation_def not_in_release_q_def valid_release_queue'_def)
  apply (clarsimp simp: state_relation_def)
  apply (clarsimp simp: obj_at'_def projectKO_eq Bits_R.projectKO_tcb)
  apply clarsimp
  apply clarsimp
  done

lemma isScActive_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and valid_objs and active_sc_tcb_at t)
             (\<lambda>s'. pred_map ((\<lambda>scPtr. isScActive scPtr s')) (tcbSCs_of s') t)"
  apply (rule cross_rel_imp[OF tcb_at'_cross_rel[where t=t]])
   apply (clarsimp simp: cross_rel_def)
   apply (subgoal_tac "pspace_relation (kheap s) (ksPSpace s')")
    apply (clarsimp simp: pred_map_def obj_at'_real_def ko_wp_at'_def vs_all_heap_simps)
    apply (subgoal_tac "sc_at' ref' s'")
     apply (clarsimp simp: vs_all_heap_simps pspace_relation_def)
     apply (drule_tac x=t in bspec, clarsimp)
     apply (clarsimp simp: other_obj_relation_def split: option.splits)
     apply (rename_tac s s' scp ko' tcb sc n x)
     apply (case_tac "ko'"; simp)
     apply (subgoal_tac "pspace_relation (kheap s) (ksPSpace s')")
      apply (clarsimp simp: vs_all_heap_simps pspace_relation_def)
      apply (drule_tac x=scp in bspec, clarsimp)
      apply (subgoal_tac "valid_sched_context_size n")
       apply (clarsimp simp: other_obj_relation_def split: option.splits)
       apply (clarsimp simp: obj_at'_def projectKO_eq Bits_R.projectKO_sc)
       apply (clarsimp simp: opt_map_def tcb_relation_def)
       apply (rule_tac x=scp in exI, simp)
       apply (clarsimp simp: isScActive_def active_sc_def)
       apply (clarsimp simp: obj_at'_def projectKO_eq Bits_R.projectKO_sc pred_map_def opt_map_def)
       apply (clarsimp simp: sc_relation_def)
      apply (rule_tac sc=sc in  valid_objs_valid_sched_context_size, assumption)
      apply (fastforce)
     apply clarsimp
    apply (erule (2) sc_at_cross)
    apply (clarsimp simp: obj_at_def is_sc_obj_def)
    apply (rule_tac sc=ya in  valid_objs_valid_sched_context_size, assumption)
    apply (fastforce)
   apply clarsimp
  apply (clarsimp simp: obj_at_kh_kheap_simps pred_map_def vs_all_heap_simps is_tcb)
  done

lemma isSchedulable_bool_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and valid_objs and schedulable t) (\<lambda>s'. valid_release_queue' s' \<longrightarrow> isSchedulable_bool t s')"
  apply (rule cross_rel_imp[OF isScActive_cross_rel[where t=t]])
   apply (rule cross_rel_imp[OF tcbInReleaseQueue_cross_rel[where t=t]])
    apply (rule cross_rel_imp[OF runnable_cross_rel[where t=t]])
     apply (clarsimp simp: isSchedulable_bool_def pred_map_conj[simplified pred_conj_def])
    apply (clarsimp simp: schedulable_def2)+
  done

lemmas tcb_at'_example = corres_cross[where Q' = "tcb_at' t" for t, OF tcb_at'_cross_rel]

lemma guarded_switch_to_chooseThread_fragment_corres:
  "corres dc
    (P and schedulable t and invs and valid_ready_qs)
    (P' and invs' and tcb_at' t)
          (guarded_switch_to t)
          (do schedulable \<leftarrow> isSchedulable t;
              y \<leftarrow> assert schedulable;
              ThreadDecls_H.switchToThread t
           od)"
  apply add_cur_tcb'
  apply (rule corres_cross'[OF isSchedulable_bool_cross_rel[where t=t], rotated])
    apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (clarsimp simp: invs'_def)
   unfolding guarded_switch_to_def
   apply simp
   apply (rule corres_guard_imp)
     apply (rule corres_symb_exec_l_Ex)
     apply (rule corres_symb_exec_l_Ex)
     apply (rule corres_split[OF isSchedulable_corres])
       apply (rule corres_assert_assume_l)
       apply (rule corres_assert_assume_r)
       apply (rule switchToThread_corres)
      apply (wpsimp wp: is_schedulable_wp)
     apply (wpsimp wp: isSchedulable_wp)
    apply (prop_tac "st_tcb_at runnable t s \<and> bound_sc_tcb_at bound t s")
     apply (clarsimp simp: schedulable_def2 tcb_at_kh_simps pred_map_def vs_all_heap_simps)
    apply (clarsimp simp: st_tcb_at_tcb_at invs_def valid_state_def valid_pspace_def valid_sched_def
                          invs_valid_vs_lookup invs_unique_refs)
    apply (clarsimp simp: thread_get_def in_monad pred_tcb_at_def obj_at_def get_tcb_ko_at)
   apply (prop_tac "st_tcb_at' runnable' t s")
    apply (clarsimp simp: pred_tcb_at'_def isSchedulable_bool_def pred_map_def obj_at'_def
                          projectKO_eq
                   elim!: opt_mapE)
   apply fastforce
  by (auto simp: invs'_def)

lemma Max_prio_helper:
  "ready_queues_relation s s'
   \<Longrightarrow> Max {prio. ready_queues s d prio \<noteq> []}
       = Max {prio. \<not> tcbQueueEmpty (ksReadyQueues s' (d, prio))}"
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def
                        list_queue_relation_def tcbQueueEmpty_def)
  apply (rule Max_eq_if)
     apply fastforce
    apply fastforce
   apply (fastforce dest: heap_path_head)
  apply clarsimp
  apply (drule_tac x=d in spec)
  apply (drule_tac x=b in spec)
  apply force
  done

lemma bitmap_lookup_queue_is_max_non_empty:
  "\<lbrakk> valid_bitmaps s'; (s, s') \<in> state_relation; invs s;
     ksReadyQueuesL1Bitmap s' (ksCurDomain s') \<noteq> 0 \<rbrakk>
   \<Longrightarrow> ksReadyQueues s' (ksCurDomain s', lookupBitmapPriority (ksCurDomain s') s') =
        max_non_empty_queue (ready_queues s (cur_domain s))"
  unfolding valid_queues_def
  by (clarsimp simp add: max_non_empty_queue_def lookupBitmapPriority_Max_eqI
                         state_relation_def ready_queues_relation_def)

lemma ksReadyQueuesL1Bitmap_return_wp:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s d) s \<rbrace> getReadyQueuesL1Bitmap d \<lbrace>\<lambda>rv s. P rv s\<rbrace>"
  unfolding getReadyQueuesL1Bitmap_def
  by wp

lemma ksReadyQueuesL1Bitmap_st_tcb_at':
  "\<lbrakk> ksReadyQueuesL1Bitmap s (ksCurDomain s) \<noteq> 0; valid_queues s;
    (\<forall>d p. (\<forall>t \<in> set (ksReadyQueues s (d, p)). st_tcb_at' runnable' t s))\<rbrakk>
   \<Longrightarrow> st_tcb_at' runnable' (hd (ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s))) s"
  apply (drule bitmapQ_from_bitmap_lookup; clarsimp simp: valid_queues_def)
  apply (clarsimp simp add: valid_bitmapQ_bitmapQ_simp)
  apply (case_tac "ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s)")
   apply simp
  apply (fastforce intro: cons_set_intro)
  done

lemma curDomain_or_return_0:
  "\<lbrakk> \<lbrace>P\<rbrace> curDomain \<lbrace>\<lambda>rv s. Q rv s \<rbrace>; \<And>s. P s \<Longrightarrow> ksCurDomain s \<le> maxDomain \<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace> if 1 < numDomains then curDomain else return 0 \<lbrace>\<lambda>rv s. Q rv s \<rbrace>"
  apply (case_tac "1 < numDomains"; simp)
  apply (simp add: valid_def curDomain_def simpler_gets_def return_def maxDomain_def)
  done

lemma chooseThread_corres:
  "corres dc (invs and valid_ready_qs and ready_or_release) invs'
     choose_thread chooseThread" (is "corres _ ?PREI ?PREH _ _")
  apply add_ready_qs_runnable
  unfolding choose_thread_def chooseThread_def
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (clarsimp simp: ready_qs_runnable_def)
  apply (simp only: return_bind Let_def K_bind_def)
  apply (subst if_swap[where P="_ \<noteq> 0"]) (* put switchToIdleThread on first branch*)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF curDomain_corres'])
      apply clarsimp
      apply (rule corres_split[OF corres_gets_queues_getReadyQueuesL1Bitmap])
        apply (erule corres_if2[OF sym])
         apply (rule switchToIdleThread_corres)
        apply (rule corres_symb_exec_r)
           apply (rule corres_symb_exec_r)
              apply (rule_tac
                       P="\<lambda>s. ?PREI s \<and> queues = ready_queues s (cur_domain s) \<and>
                              schedulable (hd (max_non_empty_queue queues)) s" and
                       P'="\<lambda>s. (?PREH s ) \<and> st_tcb_at' runnable' (hd queue) s \<and>
                               l1 = ksReadyQueuesL1Bitmap s (ksCurDomain s) \<and>
                               l1 \<noteq> 0 \<and>
                               queue = ksReadyQueues s (ksCurDomain s,
                                         lookupBitmapPriority (ksCurDomain s) s)" and
                       F="hd queue = hd (max_non_empty_queue queues)" in corres_req)
               apply (fastforce simp: bitmap_lookup_queue_is_max_non_empty invs'_def)
              apply clarsimp
              apply (rule corres_guard_imp)
                apply (rule_tac P=\<top> and P'=\<top> in guarded_switch_to_chooseThread_fragment_corres)
               apply (wp | clarsimp simp: getQueue_def getReadyQueuesL2Bitmap_def)+
      apply (wp hoare_vcg_conj_lift hoare_vcg_imp_lift ksReadyQueuesL1Bitmap_return_wp)
     apply (wpsimp wp: curDomain_or_return_0)+
    apply (fastforce simp: invs_ksCurDomain_maxDomain')
   apply (clarsimp simp: valid_sched_def DetSchedInvs_AI.valid_ready_qs_def max_non_empty_queue_def)
   apply (erule_tac x="cur_domain s" in allE)
   apply (erule_tac x="Max {prio. ready_queues s (cur_domain s) prio \<noteq> []}" in allE)
   apply (case_tac "ready_queues s (cur_domain s) (Max {prio. ready_queues s (cur_domain s) prio \<noteq> []})")
    apply (clarsimp)
    apply (subgoal_tac
             "ready_queues s (cur_domain s) (Max {prio. ready_queues s (cur_domain s) prio \<noteq> []}) \<noteq> []")
     apply (fastforce elim!: setcomp_Max_has_prop)
    apply (fastforce elim!: setcomp_Max_has_prop)
   apply (clarsimp simp: tcb_at_kh_simps schedulable_def2 released_sc_tcb_at_def)
   apply (subgoal_tac "in_ready_q a s", fastforce simp: ready_or_release_def)
   apply (clarsimp simp: in_ready_q_def)
    apply (rule_tac x="cur_domain s" in exI)
    apply (rule_tac x="Max {prio. ready_queues s (cur_domain s) prio \<noteq> []}" in exI)
    apply clarsimp
  apply (simp add: invs_ksCurDomain_maxDomain')
  apply (clarsimp simp: ready_qs_runnable_def)
  apply (fastforce intro: ksReadyQueuesL1Bitmap_st_tcb_at')
  done

lemma thread_get_comm: "do x \<leftarrow> thread_get f p; y \<leftarrow> gets g; k x y od =
           do y \<leftarrow> gets g; x \<leftarrow> thread_get f p; k x y od"
  apply (rule ext)
  apply (clarsimp simp add: gets_the_def assert_opt_def
                   bind_def gets_def get_def return_def
                   thread_get_def
                   fail_def split: option.splits)
  done

lemma schact_bind_inside: "do x \<leftarrow> f; (case act of resume_cur_thread \<Rightarrow> f1 x
                     | switch_thread t \<Rightarrow> f2 t x
                     | choose_new_thread \<Rightarrow> f3 x) od
          = (case act of resume_cur_thread \<Rightarrow> (do x \<leftarrow> f; f1 x od)
                     | switch_thread t \<Rightarrow> (do x \<leftarrow> f; f2 t x od)
                     | choose_new_thread \<Rightarrow> (do x \<leftarrow> f; f3 x od))"
  apply (case_tac act,simp_all)
  done

lemma getDomainTime_corres:
  "corres (=) \<top> \<top> (gets domain_time) getDomainTime"
  by (simp add: getDomainTime_def state_relation_def)

lemma \<mu>s_in_ms_equiv:
  "\<mu>s_in_ms = usInMs"
  by (simp add: usInMs_def \<mu>s_in_ms_def)

lemma us_to_ticks_equiv:
  "us_to_ticks = usToTicks"
  by (simp add: usToTicks_def)

lemma reset_work_units_equiv:
  "do_extended_op (modify (work_units_completed_update (\<lambda>_. 0)))
   = (modify (work_units_completed_update (\<lambda>_. 0)))"
  by (clarsimp simp: reset_work_units_def[symmetric])

lemma nextDomain_corres:
  "corres dc \<top> \<top> next_domain nextDomain"
  apply (clarsimp simp: next_domain_def nextDomain_def reset_work_units_equiv modify_modify)
  apply (rule corres_modify)
  apply (simp add: state_relation_def Let_def dschLength_def dschDomain_def cdt_relation_def
                   \<mu>s_in_ms_equiv us_to_ticks_equiv)
  done

lemma next_domain_valid_sched[wp]:
  "\<lbrace> valid_sched and (\<lambda>s. scheduler_action s  = choose_new_thread)\<rbrace> next_domain \<lbrace> \<lambda>_. valid_sched \<rbrace>"
  apply (simp add: next_domain_def Let_def)
  apply (wp, simp add: valid_sched_def valid_sched_action_2_def ct_not_in_q_2_def)
  apply (fastforce simp: valid_blocked_defs)
  done

lemma nextDomain_invs':
  "nextDomain \<lbrace>invs'\<rbrace>"
  apply (simp add: nextDomain_def Let_def dschLength_def)
  apply wp
  apply (clarsimp simp: invs'_def valid_machine_state'_def dschDomain_def valid_dom_schedule'_def)
  done

lemma scheduleChooseNewThread_fragment_corres:
  "corres dc (invs and valid_ready_qs and ready_or_release
              and (\<lambda>s. scheduler_action s = choose_new_thread))
             (invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread))
     (do _ \<leftarrow> when (domainTime = 0) next_domain;
         choose_thread
      od)
     (do _ \<leftarrow> when (domainTime = 0) nextDomain;
          chooseThread
      od)"
  apply (subst bind_dummy_ret_val)
  apply (subst bind_dummy_ret_val)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF corres_when])
        apply simp
       apply (rule nextDomain_corres)
      apply simp
      apply (rule chooseThread_corres)
     apply (wp nextDomain_invs')+
   apply (clarsimp simp: valid_sched_def invs'_def)+
  done

lemma scheduleSwitchThreadFastfail_corres:
  "\<lbrakk> ct \<noteq> it \<longrightarrow> (tp = tp' \<and> cp = cp') ; ct = ct' ; it = it' \<rbrakk> \<Longrightarrow>
   corres ((=)) (tcb_at ct) (tcb_at' ct)
     (schedule_switch_thread_fastfail ct it cp tp)
     (scheduleSwitchThreadFastfail ct' it' cp' tp')"
  by (clarsimp simp: schedule_switch_thread_fastfail_def scheduleSwitchThreadFastfail_def)

lemma gets_is_highest_prio_expand:
  "gets (is_highest_prio d p) \<equiv> do
    q \<leftarrow> gets (\<lambda>s. ready_queues s d);
    return ((\<forall>p. q p = []) \<or> Max {prio. q prio \<noteq> []} \<le> p)
   od"
  by (clarsimp simp: is_highest_prio_def gets_def)

lemma isHighestPrio_corres:
  assumes "d' = d"
  assumes "p' = p"
  shows
    "corres ((=)) \<top> valid_bitmaps
      (gets (is_highest_prio d p))
      (isHighestPrio d' p')"
  using assms
  apply (clarsimp simp: gets_is_highest_prio_expand isHighestPrio_def)
  apply (subst getHighestPrio_def')
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF corres_gets_queues_getReadyQueuesL1Bitmap])
      apply (rule corres_if_r'[where P'="\<lambda>_. True",rotated])
       apply (rule_tac corres_symb_exec_r)
          apply (rule_tac P="\<lambda>s. q = ready_queues s d"
                      and P'="\<lambda>s. valid_bitmaps s \<and> l1 = ksReadyQueuesL1Bitmap s d \<and>
                                  l1 \<noteq> 0 \<and> hprio = lookupBitmapPriority d s"
                      and F="hprio = Max {prio. q prio \<noteq> []}" in corres_req)
           apply (elim conjE)
           apply (clarsimp simp: valid_bitmaps_def)
           apply (subst lookupBitmapPriority_Max_eqI; blast?)
           apply (fastforce dest: state_relation_ready_queues_relation Max_prio_helper[where d=d]
                            simp: tcbQueueEmpty_def)
          apply fastforce
         apply (wpsimp simp: if_apply_def2 wp: hoare_drop_imps ksReadyQueuesL1Bitmap_return_wp)+
  done

crunch isHighestPrio
 for inv[wp]: P
crunch curDomain
 for inv[wp]: P
crunch scheduleSwitchThreadFastfail
 for inv[wp]: P

lemma setSchedulerAction_invs': (* not in wp set, clobbered by ssa_wp *)
  "\<lbrace>\<lambda>s. invs' s \<rbrace> setSchedulerAction ChooseNewThread \<lbrace>\<lambda>_. invs' \<rbrace>"
  by (wpsimp simp: invs'_def cur_tcb'_def valid_irq_node'_def ct_not_inQ_def
                   valid_queues_def valid_release_queue_def valid_release_queue'_def
                   valid_queues_no_bitmap_def valid_queues'_def ct_idle_or_in_cur_domain'_def
                   valid_dom_schedule'_def)

lemma scheduleChooseNewThread_corres:
  "corres dc
    (\<lambda>s. invs s \<and> valid_ready_qs s \<and> ready_or_release s \<and> scheduler_action s = choose_new_thread)
    (\<lambda>s. invs' s \<and> ksSchedulerAction s = ChooseNewThread)
           schedule_choose_new_thread scheduleChooseNewThread"
  unfolding schedule_choose_new_thread_def scheduleChooseNewThread_def
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getDomainTime_corres], clarsimp)
      apply (rule corres_split[OF scheduleChooseNewThread_fragment_corres, simplified bind_assoc])
        apply (rule setSchedulerAction_corres)
        apply (wp | simp)+
    apply (wp | simp add: getDomainTime_def)+
  done

lemma ssa_ct_not_inQ:
  "\<lbrace>\<lambda>s. sa = ResumeCurrentThread \<longrightarrow> obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>
   setSchedulerAction sa \<lbrace>\<lambda>rv. ct_not_inQ\<rbrace>"
  by (simp add: setSchedulerAction_def ct_not_inQ_def, wp, clarsimp)

lemma ssa_invs':
  "setSchedulerAction sa \<lbrace>invs'\<rbrace>"
  apply (wp ssa_ct_not_inQ)
  apply (clarsimp simp: invs'_def valid_irq_node'_def valid_dom_schedule'_def)
  done

lemma getDomainTime_wp[wp]: "\<lbrace>\<lambda>s. P (ksDomainTime s) s \<rbrace> getDomainTime \<lbrace> P \<rbrace>"
  unfolding getDomainTime_def
  by wp

lemma switchToThread_ct_not_queued_2:
  "\<lbrace>invs' and tcb_at' t\<rbrace> switchToThread t \<lbrace>\<lambda>rv s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>"
  (is "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_. ?POST\<rbrace>")
  apply (simp add: Thread_H.switchToThread_def)
  apply wp
    apply (simp add: ARM_H.switchToThread_def setCurThread_def)
    apply (wpsimp wp: tcbSchedDequeue_not_tcbQueued hoare_drop_imps)+
  done

lemma setCurThread_obj_at':
  "\<lbrace> obj_at' P t \<rbrace> setCurThread t \<lbrace>\<lambda>rv s. obj_at' P (ksCurThread s) s \<rbrace>"
proof -
  show ?thesis
    apply (simp add: setCurThread_def)
    apply wp
    apply (simp add: ct_in_state'_def st_tcb_at'_def)
    done
qed

lemma switchToIdleThread_ct_not_queued:
  "\<lbrace> invs' \<rbrace> switchToIdleThread \<lbrace>\<lambda>_ s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s \<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def)
  apply (wp setCurThread_obj_at')
  apply (intro impI)
  apply (rule idle'_not_tcbQueued')
     apply (simp add: ready_qs_runnable_def invs'_def valid_idle'_asrt_def)+
  done

lemma switchToIdleThread_activatable_2[wp]:
  "\<lbrace>invs'\<rbrace> switchToIdleThread \<lbrace>\<lambda>_. ct_in_state' activatable'\<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def
                   ARM_H.switchToIdleThread_def)
  apply (wp setCurThread_ct_in_state)
  apply (clarsimp simp: invs'_def valid_idle'_def valid_idle'_asrt_def
                        pred_tcb_at'_def obj_at'_def idle_tcb'_def)
  done

lemma switchToThread_tcb_in_cur_domain':
  "\<lbrace>tcb_in_cur_domain' thread\<rbrace>
   ThreadDecls_H.switchToThread thread
   \<lbrace>\<lambda>_ s. tcb_in_cur_domain' (ksCurThread s) s\<rbrace>"
  apply (simp add: Thread_H.switchToThread_def setCurThread_def)
  apply (wpsimp wp: tcbSchedDequeue_not_tcbQueued tcbSchedDequeue_tcbDomain
                    hoare_drop_imps)
  done

lemma chooseThread_invs'_posts: (* generic version *)
  "\<lbrace> invs' \<rbrace> chooseThread
   \<lbrace>\<lambda>rv s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s \<and>
           ct_in_state' activatable' s \<and>
           (ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s) \<rbrace>"
  unfolding chooseThread_def Let_def
  apply (simp only: return_bind, simp split del: if_split)
  apply (rule bind_wp[OF _ stateAssert_sp])
  apply (rule bind_wp[where Q'="\<lambda>rv s. invs' s \<and> rv = ksCurDomain s \<and> ready_qs_runnable s"])
   apply (rule_tac Q'="\<lambda>rv s. invs' s \<and> curdom = ksCurDomain s \<and>
                             rv = ksReadyQueuesL1Bitmap s curdom \<and> ready_qs_runnable s"
                in bind_wp)
    apply (rename_tac l1)
    apply (case_tac "l1 = 0")
     (* switch to idle thread *)
     apply simp
     apply (rule hoare_pre)
      apply (wp (once) switchToIdleThread_ct_not_queued)
      apply (wp (once))
      apply ((wp hoare_disjI1 switchToIdleThread_curr_is_idle)+)[1]
       apply simp
      (* we have a thread to switch to *)
    apply (clarsimp simp: bitmap_fun_defs)
    apply (wp assert_inv switchToThread_ct_not_queued_2 assert_inv hoare_disjI2
              switchToThread_tcb_in_cur_domain' isSchedulable_wp)
    apply clarsimp
    apply (clarsimp simp: valid_queues_def lookupBitmapPriority_def[symmetric]
                          ready_qs_runnable_def invs'_def)
    apply (drule (3) lookupBitmapPriority_obj_at')
    apply normalise_obj_at'
    apply (fastforce simp: tcb_in_cur_domain'_def inQ_def elim: obj_at'_weaken)
   apply (wpsimp simp: bitmap_fun_defs)
  apply (wpsimp wp: curDomain_or_return_0[simplified] simp: invs_ksCurDomain_maxDomain')
  done

lemma chooseThread_activatable_2:
  "\<lbrace>invs'\<rbrace> chooseThread \<lbrace>\<lambda>_. ct_in_state' activatable'\<rbrace>"
  apply (rule hoare_pre, rule hoare_strengthen_post)
    apply (rule chooseThread_invs'_posts)
   apply simp+
  done

lemma chooseThread_ct_not_queued_2:
  "\<lbrace> invs' \<rbrace> chooseThread \<lbrace>\<lambda>_ s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>"
    (is "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_. ?POST\<rbrace>")
  apply (rule hoare_pre, rule hoare_strengthen_post)
    apply (rule chooseThread_invs'_posts)
   apply simp+
  done

lemma chooseThread_invs'':
  "chooseThread \<lbrace>invs'\<rbrace>"
  unfolding chooseThread_def Let_def
  apply (simp only: return_bind, simp split del: if_split)
  apply (rule bind_wp[OF _ stateAssert_sp])
  apply (rule bind_wp[where Q'="\<lambda>rv s. invs' s \<and> rv = ksCurDomain s \<and> ready_qs_runnable s"])
   apply (rule_tac Q'="\<lambda>rv s. invs' s \<and> curdom = ksCurDomain s \<and>
                             rv = ksReadyQueuesL1Bitmap s curdom \<and> ready_qs_runnable s"
                in bind_wp)
    apply (rename_tac l1)
    apply (case_tac "l1 = 0")
     (* switch to idle thread *)
     apply (simp, wp switchToIdleThread_invs', simp)
    (* we have a thread to switch to *)
    apply (clarsimp simp: bitmap_fun_defs)
    apply (wp assert_inv isSchedulable_wp)
    apply (clarsimp simp: valid_queues_def invs'_def)
   apply (wpsimp simp: bitmap_fun_defs)
  apply (wpsimp wp: curDomain_or_return_0[simplified] simp: invs_ksCurDomain_maxDomain')
  done

lemma chooseThread_in_cur_domain':
  "\<lbrace> invs' \<rbrace> chooseThread \<lbrace>\<lambda>rv s. ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s\<rbrace>"
  apply (rule hoare_pre, rule hoare_strengthen_post)
    apply (rule chooseThread_invs'_posts, simp_all)
  done

lemma scheduleChooseNewThread_invs':
  "scheduleChooseNewThread \<lbrace>invs'\<rbrace>"
  unfolding scheduleChooseNewThread_def
  apply (wpsimp wp: ssa_invs' chooseThread_invs'' chooseThread_ct_not_queued_2
                    chooseThread_activatable_2 chooseThread_invs''
                    chooseThread_in_cur_domain' nextDomain_invs' chooseThread_ct_not_queued_2)
  done

lemma setReprogramTimer_invs'[wp]:
  "setReprogramTimer v \<lbrace>invs'\<rbrace>"
  unfolding setReprogramTimer_def
  apply wpsimp
  by (clarsimp simp: invs'_def valid_machine_state'_def cur_tcb'_def
                     ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def ct_not_inQ_def
                     valid_dom_schedule'_def)

lemma machine_op_lift_underlying_memory_invar:
  "(x, b) \<in> fst (machine_op_lift a m) \<Longrightarrow> underlying_memory b = underlying_memory m"
  by (clarsimp simp: in_monad machine_op_lift_def machine_rest_lift_def select_f_def)

lemma setNextInterrupt_invs'[wp]:
  "setNextInterrupt \<lbrace>invs'\<rbrace>"
  unfolding setNextInterrupt_def
  apply (wpsimp wp: dmo_invs' ARM.setDeadline_irq_masks threadGet_wp getReleaseQueue_wp)
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  by (auto simp: in_monad setDeadline_def machine_op_lift_underlying_memory_invar)

lemma setCurSc_invs'[wp]:
  "setCurSc v \<lbrace>invs'\<rbrace>"
  unfolding setCurSc_def
  apply wpsimp
  apply (clarsimp simp: invs'_def valid_machine_state'_def cur_tcb'_def
                        ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def ct_not_inQ_def
                        valid_queues_def valid_queues_no_bitmap_def valid_bitmapQ_def bitmapQ_def
                        bitmapQ_no_L2_orphans_def bitmapQ_no_L1_orphans_def valid_irq_node'_def
                        valid_queues'_def valid_release_queue_def valid_release_queue'_def
                        valid_dom_schedule'_def)
  done

lemma setConsumedTime_invs'[wp]:
  "setConsumedTime v \<lbrace>invs'\<rbrace>"
  unfolding setConsumedTime_def
  apply wpsimp
  apply (clarsimp simp: invs'_def valid_machine_state'_def cur_tcb'_def
                        ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def ct_not_inQ_def
                        valid_queues_def valid_queues_no_bitmap_def valid_bitmapQ_def bitmapQ_def
                        bitmapQ_no_L2_orphans_def bitmapQ_no_L1_orphans_def valid_irq_node'_def
                        valid_queues'_def valid_release_queue_def valid_release_queue'_def
                        valid_dom_schedule'_def)
  done

lemma setDomainTime_invs'[wp]:
  "setDomainTime v \<lbrace>invs'\<rbrace>"
  unfolding setDomainTime_def
  apply wpsimp
  done

lemma valid_idle'_ko_at_idle_sc_is_idle':
  "\<lbrakk>valid_idle' s; ko_at' ko scPtr s\<rbrakk> \<Longrightarrow> (scPtr = idle_sc_ptr \<longrightarrow> idle_sc' ko)"
  apply (clarsimp simp: valid_idle'_def obj_at'_real_def ko_wp_at'_def)
  done

lemma refillTailIndex_bounded:
  "valid_sched_context' ko s \<Longrightarrow> 0 < scRefillMax ko \<longrightarrow> refillTailIndex ko < scRefillMax ko"
  apply (clarsimp simp: valid_sched_context'_def refillTailIndex_def Let_def split: if_split)
  by linarith

lemma refillAddTail_valid_objs'[wp]:
  "refillAddTail scPtr t \<lbrace>valid_objs'\<rbrace>"
  apply (simp add: refillAddTail_def)
  apply (wpsimp wp: set_sc_valid_objs' getRefillNext_wp getRefillSize_wp
              simp: updateSchedContext_def)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc', clarsimp)
  apply (clarsimp simp: valid_obj'_def obj_at'_def projectKOs opt_map_red opt_pred_def)
  apply (intro conjI)
   apply (frule refillTailIndex_bounded)
   apply (clarsimp simp: valid_sched_context'_def)
  apply (frule refillTailIndex_bounded)
  apply (clarsimp simp: valid_sched_context_size'_def objBits_simps valid_sched_context'_def)
  done

lemma refillAddTail_invs'[wp]:
  "refillAddTail scPtr t \<lbrace>invs'\<rbrace>"
  apply (simp add: refillAddTail_def)
  apply (wpsimp wp: setSchedContext_invs' getRefillNext_wp getRefillSize_wp
              simp: updateSchedContext_def)
  apply (frule (1) invs'_ko_at_valid_sched_context', clarsimp)
  apply (drule ko_at'_inj, assumption, clarsimp)+
  apply (intro conjI)
    apply (fastforce dest: live_sc'_ko_ex_nonz_cap_to')
   apply (frule refillTailIndex_bounded)
   apply (clarsimp simp: valid_sched_context'_def)
  apply (frule refillTailIndex_bounded)
  apply (clarsimp simp: valid_sched_context_size'_def objBits_def objBitsKO_def valid_sched_context'_def)
  done

lemma refillBudgetCheckRoundRobin_invs'[wp]:
  "\<lbrace>invs' and (\<lambda>s. active_sc_at' (ksCurSc s) s)\<rbrace>
   refillBudgetCheckRoundRobin consumed
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  supply if_split [split del]
  apply (simp add: refillBudgetCheckRoundRobin_def updateRefillTl_def updateRefillHd_def)
  apply (wpsimp simp:  wp: updateSchedContext_refills_invs')
    apply (rule_tac Q="\<lambda>_. invs' and active_sc_at' scPtr" in hoare_strengthen_post[rotated])
     apply clarsimp
     apply (frule (1) invs'_ko_at_valid_sched_context', clarsimp)
     apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def
                           ko_wp_at'_def valid_sched_context_size'_def objBits_def objBitsKO_def)
    apply (wpsimp wp: updateSchedContext_refills_invs' getCurTime_wp updateSchedContext_active_sc_at')
   apply (wpsimp wp: )
  apply clarsimp
  apply (frule invs'_ko_at_valid_sched_context', simp, clarsimp)
  apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def ko_wp_at'_def
                        valid_sched_context_size'_def objBits_def objBitsKO_def)
  done

lemma updateRefillTl_valid_objs'[wp]:
  "updateRefillTl scPtr f \<lbrace>valid_objs'\<rbrace>"
  apply (clarsimp simp: updateRefillTl_def updateSchedContext_def)
  apply (wpsimp wp: set_sc_valid_objs')
  apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                   simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps)
  done

crunch scheduleUsed
  for valid_objs'[wp]: valid_objs'
  (simp: refillFull_def refillEmpty_def)

lemma updateRefillTl_invs'[wp]:
  "updateRefillTl scPtr f \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: updateRefillTl_def)
  apply (wpsimp wp: updateSchedContext_invs')
  apply (intro conjI)
   apply (fastforce dest: invs_iflive'
                    elim: if_live_then_nonz_capE'
                    simp: valid_idle'_def obj_at'_def ko_wp_at'_def live_sc'_def projectKOs)
  apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                   simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps)
  done

lemma updateRefillTl_if_live_then_nonz_cap'[wp]:
  "updateRefillTl scPtr f \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: updateRefillTl_def updateSchedContext_def)
  apply (wpsimp wp: setSchedContext_iflive')
  apply (fastforce elim: if_live_then_nonz_capE'
                   simp: valid_idle'_def obj_at'_def ko_wp_at'_def live_sc'_def projectKOs)
  done

lemma scheduleUsed_if_live_then_nonz_cap'[wp]:
  "scheduleUsed scPtr refill \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (wpsimp simp: scheduleUsed_def refillAddTail_def updateSchedContext_def
                  wp: getRefillSize_wp refillFull_wp refillEmpty_wp getRefillNext_wp)
  apply (fastforce intro: if_live_then_nonz_capE'
                    simp: ko_wp_at'_def obj_at'_real_def projectKO_sc live_sc'_def)
  done

lemma updateSchedContext_valid_idle':
  "\<lbrace>valid_idle' and (\<lambda>s. \<forall>sc. idle_sc' sc \<longrightarrow> idle_sc' (f sc))\<rbrace>
   updateSchedContext scPtr f
   \<lbrace>\<lambda>_. valid_idle'\<rbrace>"
  apply (clarsimp simp: updateSchedContext_def)
  apply wpsimp
  apply (fastforce simp: valid_idle'_def obj_at'_def)
  done

crunch scheduleUsed, updateRefillHd, refillPopHead
  for valid_idle'[wp]: valid_idle'
  (wp: updateSchedContext_valid_idle')

lemma scheduleUsed_invs'[wp]:
  "scheduleUsed scPtr refill \<lbrace>invs'\<rbrace>"
  apply (simp add: scheduleUsed_def)
  apply (wpsimp wp: refillFull_wp refillEmpty_wp)
  done

lemma refillPopHead_valid_objs'[wp]:
  "\<lbrace>valid_objs' and obj_at' (\<lambda>sc'. 1 < scRefillCount sc') scPtr \<rbrace>
   refillPopHead scPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (clarsimp simp: refillPopHead_def updateSchedContext_def getRefillNext_def)
  apply (wpsimp wp: set_sc_valid_objs')
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply (clarsimp simp: readRefillNext_def readSchedContext_def)
  by (fastforce simp: obj_at'_def projectKOs scBits_simps refillNextIndex_def
                      valid_sched_context'_def valid_sched_context_size'_def objBits_simps'
               dest!: readObject_misc_ko_at')

lemma refillPopHead_invs'[wp]:
  "\<lbrace>invs' and obj_at' (\<lambda>sc'. 1 < scRefillCount sc') scPtr\<rbrace>
   refillPopHead scPtr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: refillPopHead_def)
  apply (wpsimp wp: updateSchedContext_invs' getRefillNext_wp)
  apply (intro conjI; intro allI impI)
   apply (clarsimp simp: obj_at'_def)
   apply (rule if_live_then_nonz_capE')
    apply (erule invs_iflive')
   apply (clarsimp simp: ko_wp_at'_def obj_at'_def projectKO_eq projectKO_sc live_sc'_def)
  apply (fastforce dest!: invs'_ko_at_valid_sched_context'
                    simp: valid_sched_context'_def valid_sched_context_size'_def
                          refillNextIndex_def obj_at_simps)
  done

lemma refillPopHead_active_sc_at'[wp]:
  "refillPopHead scPtr \<lbrace>active_sc_at' scPtr'\<rbrace>"
  apply (simp add: refillPopHead_def)
  apply (wpsimp wp: updateSchedContext_active_sc_at' getRefillNext_wp)
  done

lemma refillAddTail_active_sc_at'[wp]:
  "refillAddTail scPtr refill \<lbrace>active_sc_at' scPtr'\<rbrace>"
  apply (simp add: refillAddTail_def getRefillSize_def refillTailIndex_def)
  apply (wpsimp wp: updateSchedContext_active_sc_at' hoare_drop_imps getRefillNext_wp)
  done

lemma updateRefillTl_active_sc_at'[wp]:
  "updateRefillTl scPtr f \<lbrace>active_sc_at' scPtr'\<rbrace>"
  apply (simp add: updateRefillTl_def)
  apply (wpsimp wp: updateSchedContext_active_sc_at' hoare_drop_imps getRefillNext_wp)
  done

crunch scheduleUsed
  for active_sc_at'[wp]: "active_sc_at' scPtr"
  (wp: crunch_wps)

crunch refillPopHead
  for ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' scPtr"

lemma updateRefillHd_invs':
  "\<lbrace>invs' and active_sc_at' scPtr\<rbrace> updateRefillHd scPtr f \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: updateRefillHd_def)
  apply (wpsimp wp: updateSchedContext_invs')
  apply (intro conjI; intro allI impI)
   apply (fastforce dest: live_sc'_ko_ex_nonz_cap_to')
  apply (frule invs'_ko_at_valid_sched_context', simp, clarsimp)
  apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def ko_wp_at'_def
                        valid_sched_context_size'_def objBits_def objBitsKO_def)
  done

lemma updateRefillHd_active_sc_at'[wp]:
  "updateRefillHd scPtr f \<lbrace>active_sc_at' scPr\<rbrace>"
  apply (clarsimp simp: updateRefillHd_def)
  apply (wpsimp wp: updateSchedContext_active_sc_at')
  done

lemma updateRefillHd_active_sc_at'_ksCurSc[wp]:
  "updateRefillHd scPtr f \<lbrace>\<lambda>s. active_sc_at' (ksCurSc s) s\<rbrace>"
  apply (rule_tac f=ksCurSc in hoare_lift_Pf)
   apply wpsimp
  apply (clarsimp simp: updateRefillHd_def updateSchedContext_def)
  apply wpsimp
  done

lemma setRefillHd_active_sc_at'[wp]:
  "setRefillHd scPtr f \<lbrace>active_sc_at' scPr\<rbrace>"
  apply (clarsimp simp: setRefillHd_def)
  apply (wpsimp wp: updateSchedContext_active_sc_at')
  done

lemma setReprogramTimer_obj_at'[wp]:
  "setReprogramTimer b \<lbrace>\<lambda>s. Q (obj_at' P t s)\<rbrace>"
  unfolding active_sc_at'_def
  by (wpsimp simp: setReprogramTimer_def)

lemma setReprogramTimer_active_sc_at'[wp]:
  "setReprogramTimer b \<lbrace>active_sc_at' scPtr\<rbrace>"
  unfolding active_sc_at'_def
  by wpsimp

crunch refillBudgetCheck, refillUnblockCheck
  for valid_queues[wp]: valid_queues
  and valid_queues'[wp]: valid_queues'
  and valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n T p s)"
  and active_sc_at'[wp]: "active_sc_at' scPtr"
  (wp: crunch_wps)

lemma mergeRefills_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> sc_at' scPtr s \<and> ((\<lambda>sc. 1 < scRefillCount sc) |< scs_of' s) scPtr\<rbrace>
   mergeRefills scPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (clarsimp simp: mergeRefills_def updateRefillHd_def)
  apply (rule_tac Q'="\<lambda>_ s. valid_objs' s \<and> sc_at' scPtr s" in bind_wp_fwd)
   apply wpsimp
   apply (clarsimp simp: obj_at_simps opt_map_red opt_pred_def)
  apply (wpsimp wp: set_sc_valid_objs' simp: updateSchedContext_def)
  apply (clarsimp simp: valid_sched_context'_def obj_at_simps valid_obj'_def
                        valid_sched_context_size'_def opt_map_red opt_pred_def
                 dest!: sc_ko_at_valid_objs_valid_sc')
  done

lemma no_ofail_refillHeadOverlapping:
  "no_ofail (sc_at' scp) (refillHeadOverlapping scp)"
  unfolding refillHeadOverlapping_def oreturn_def obind_def oliftM_def no_ofail_def
            readRefillSize_def readRefillNext_def
  by (clarsimp dest!: no_ofailD[OF no_ofail_readSchedContext])

lemma refillHeadOverlapping_implies_count_greater_than_one:
  "\<lbrakk>the (refillHeadOverlapping scPtr s); sc_at' scPtr s\<rbrakk>
   \<Longrightarrow> ((\<lambda>sc. 1 < scRefillCount sc) |< scs_of' s) scPtr"
  apply (clarsimp simp: refillHeadOverlapping_def readSchedContext_def oliftM_def
                        readRefillNext_def readRefillSize_def obind_def omonad_defs
                 split: option.splits dest!: readObject_misc_ko_at')
   apply (fastforce dest: no_ofail_sc_at'_readObject[unfolded no_ofail_def, rule_format])
  apply (clarsimp simp: obj_at_simps opt_map_red opt_pred_def MIN_REFILLS_def)
  done

lemma refillHeadOverlappingLoop_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> sc_at' scPtr s\<rbrace>
   refillHeadOverlappingLoop scPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  (is "valid ?pre _ _")
  apply (clarsimp simp: refillHeadOverlappingLoop_def)
  apply (wpsimp wp: valid_whileLoop[where I="\<lambda>_. ?pre"] mergeRefills_valid_objs')
    apply (clarsimp simp: runReaderT_def)
    apply (prop_tac "((\<lambda>sc. 1 < scRefillCount sc) |< scs_of' s) scPtr")
     apply (fastforce elim: refillHeadOverlapping_implies_count_greater_than_one
                      simp: obj_at_simps opt_map_red)
    apply simp+
  done

lemma updateRefillHd_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> sc_at' scPtr s\<rbrace>
   updateRefillHd scPtr f
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (clarsimp simp: updateRefillHd_def)
  apply (wpsimp wp: set_sc_valid_objs' simp: updateSchedContext_def)
  apply (clarsimp simp: is_active_sc'_def valid_sched_context'_def obj_at_simps valid_obj'_def
                        valid_sched_context_size'_def opt_map_red opt_pred_def active_sc_at'_rewrite
                 dest!: sc_ko_at_valid_objs_valid_sc')
  done

lemma setRefillHd_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> sc_at' scPtr s\<rbrace>
   setRefillHd scPtr f
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wpsimp simp: setRefillHd_def
                  wp: updateRefillHd_valid_objs')
  done

lemma refillUnblockCheck_valid_objs'[wp]:
  "refillUnblockCheck scPtr \<lbrace>valid_objs'\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def isRoundRobin_def refillReady_def)
  apply (wpsimp wp: updateRefillHd_valid_objs' refillHeadOverlappingLoop_valid_objs' scActive_wp)
  done

lemma refillUnblockCheck_valid_mdb'[wp]:
  "refillUnblockCheck scPtr \<lbrace>valid_mdb'\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def valid_mdb'_def)
  apply (wpsimp wp: scActive_wp)
  done

lemma refillUnblockCheck_valid_machine_state'[wp]:
  "refillUnblockCheck scPtr \<lbrace>valid_machine_state'\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def refillReady_def isRoundRobin_def
                        refillHeadOverlappingLoop_def mergeRefills_def updateRefillHd_def
                        refillPopHead_def updateSchedContext_def setReprogramTimer_def
                        valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wpsimp wp: whileLoop_valid_inv hoare_vcg_all_lift hoare_vcg_disj_lift scActive_wp
                    hoare_drop_imps getRefillNext_wp)
  apply fastforce
  done

lemma refillUnblockCheck_list_refs_of_replies'[wp]:
  "refillUnblockCheck scPtr \<lbrace>\<lambda>s. P (list_refs_of_replies' s)\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def valid_mdb'_def refillHeadOverlappingLoop_def
                        mergeRefills_def updateRefillHd_def refillPopHead_def updateSchedContext_def
                        setReprogramTimer_def refillReady_def isRoundRobin_def)
  apply (wpsimp wp: whileLoop_valid_inv hoare_drop_imps scActive_wp getRefillNext_wp
              simp: o_def)
  done

lemma refillPopHead_if_live_then_nonz_cap'[wp]:
  "refillPopHead scPtr \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: refillPopHead_def updateSchedContext_def getRefillNext_def)
  apply wpsimp
  apply (fastforce intro: if_live_then_nonz_capE'
                    simp: ko_wp_at'_def obj_at'_real_def projectKO_sc live_sc'_def)
  done

lemma mergeRefills_if_live_then_nonz_cap'[wp]:
  "mergeRefills scPtr \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: mergeRefills_def)
  apply (rule bind_wp_fwd_skip, wpsimp)
  apply (wpsimp simp: updateRefillHd_def updateSchedContext_def)
  apply (fastforce intro: if_live_then_nonz_capE'
                    simp: ko_wp_at'_def obj_at'_real_def projectKO_sc live_sc'_def)
  done

lemma nonOverlappingMergeRefills_if_live_then_nonz_cap'[wp]:
  "nonOverlappingMergeRefills scPtr \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: nonOverlappingMergeRefills_def updateRefillHd_def)
  apply (rule bind_wp_fwd_skip, wpsimp)+
  by (wpsimp simp: updateSchedContext_def,
      fastforce intro: if_live_then_nonz_capE'
                 simp: ko_wp_at'_def obj_at'_real_def projectKO_sc live_sc'_def)+

crunch refillHeadOverlappingLoop, headInsufficientLoop
  for if_live_then_nonz_cap'[wp]: if_live_then_nonz_cap'
  (wp: crunch_wps)

lemma updateRefillHd_if_live_then_nonz_cap'[wp]:
  "updateRefillHd scPtr f \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: updateRefillHd_def updateSchedContext_def)
  apply wpsimp
  apply (fastforce intro: if_live_then_nonz_capE'
                    simp: ko_wp_at'_def obj_at'_real_def projectKO_sc live_sc'_def)
  done

lemma setRefillHd_if_live_then_nonz_cap'[wp]:
  "setRefillHd scPtr f \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (wpsimp simp: setRefillHd_def)
  done

crunch handleOverrunLoop
  for if_live_then_nonz_cap'[wp]: if_live_then_nonz_cap'
  (wp: crunch_wps)

lemma refillUnblockCheck_if_live_then_nonz_cap'[wp]:
  "refillUnblockCheck scPtr \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def setReprogramTimer_def refillReady_def
                        isRoundRobin_def)
  apply (wpsimp wp: scActive_wp)
  done

lemma mergeRefills_valid_idle'[wp]:
  "mergeRefills scPtr \<lbrace>valid_idle'\<rbrace>"
  apply (clarsimp simp: mergeRefills_def updateRefillHd_def updateSchedContext_def)
  apply (rule bind_wp_fwd_skip, wpsimp)
  apply (wpsimp simp: valid_idle'_def obj_at'_def)
  done

lemma nonOverlappingMergeRefills_valid_idle'[wp]:
  "nonOverlappingMergeRefills scPtr \<lbrace>valid_idle'\<rbrace>"
  apply (clarsimp simp: nonOverlappingMergeRefills_def updateRefillHd_def)
  apply (rule bind_wp_fwd_skip, wpsimp)+
  apply (clarsimp simp: updateSchedContext_def,
         rule bind_wp[OF _ get_sc_sp'],
         wpsimp simp: valid_idle'_def obj_at'_def)+
  done

crunch refillHeadOverlappingLoop, headInsufficientLoop, handleOverrunLoop
  for valid_idle'[wp]: valid_idle'
  (wp: crunch_wps)

lemma refillUnblockCheck_valid_idle'[wp]:
  "refillUnblockCheck scPtr \<lbrace>valid_idle'\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def isRoundRobin_def refillReady_def
                        setReprogramTimer_def updateRefillHd_def updateSchedContext_def)
  apply (wpsimp wp: scActive_wp)
  apply (clarsimp simp: valid_idle'_def obj_at'_def)
  done

crunch refillHeadOverlappingLoop, headInsufficientLoop, handleOverrunLoop
  for ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
  (wp: crunch_wps)

lemma refillUnblockCheck_ct_idle_or_in_cur_domain'[wp]:
  "refillUnblockCheck scPtr \<lbrace>ct_idle_or_in_cur_domain'\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def isRoundRobin_def refillReady_def
                        setReprogramTimer_def updateRefillHd_def)
  apply (wpsimp wp: scActive_wp)
  done

crunch refillUnblockCheck, refillBudgetCheck
  for reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and pred_tcb_at'[wp]: "pred_tcb_at' proj P p"
  and valid_replies'[wp]: valid_replies'
  (wp: crunch_wps valid_replies'_lift)

lemma refillUnblockCheck_invs':
  "refillUnblockCheck scPtr \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: invs'_def valid_pspace'_def pred_conj_def)
  apply wpsimp
  done

crunch ifCondRefillUnblockCheck
  for invs'[wp]: invs'
  (wp: hoare_vcg_if_lift2 crunch_wps simp: crunch_simps)

lemma nonOverlappingMergeRefills_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> sc_at' scPtr s\<rbrace>
   nonOverlappingMergeRefills scPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (clarsimp simp: nonOverlappingMergeRefills_def updateRefillHd_def)
  apply (rule bind_wp[OF _ get_sc_sp'])
  apply (rule_tac bind_wp[OF _ assert_sp])
  apply (rule_tac Q'="\<lambda>_ s. valid_objs' s \<and> sc_at' scPtr s" in bind_wp_fwd)
   apply wpsimp
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  apply (wpsimp wp: set_sc_valid_objs' simp: updateSchedContext_def)
    apply (rule_tac Q="\<lambda>_. valid_objs' and sc_at' scPtr" in hoare_strengthen_post[rotated])
     apply (clarsimp simp: valid_sched_context'_def obj_at_simps valid_obj'_def
                           valid_sched_context_size'_def opt_map_red opt_pred_def
                    dest!: sc_ko_at_valid_objs_valid_sc')
    apply (wpsimp wp: set_sc_valid_objs' setSchedContext_active_sc_at' simp: updateSchedContext_def)+
  apply (fastforce simp: valid_sched_context'_def obj_at_simps valid_obj'_def
                         valid_sched_context_size'_def opt_map_red opt_pred_def
                  dest!: sc_ko_at_valid_objs_valid_sc')
  done

crunch refillHeadOverlappingLoop, headInsufficientLoop, handleOverrunLoop
  for active_sc_at'[wp]: "active_sc_at' scPtr"
  and ksCurSc[wp]: "\<lambda>s. P (ksCurSc s)"
  (wp: crunch_wps)

lemma headInsufficientLoop_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> sc_at' scPtr s\<rbrace>
   headInsufficientLoop scPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  (is "valid ?pre _ _")
  apply (clarsimp simp: headInsufficientLoop_def)
  apply (wpsimp wp: valid_whileLoop[where I="\<lambda>_. ?pre"] nonOverlappingMergeRefills_valid_objs')
  done

lemma handleOverrunLoop_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> active_sc_at' (ksCurSc s) s\<rbrace>
   handleOverrunLoop usage
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  (is "valid ?pre _ _")
  apply (clarsimp simp: handleOverrunLoop_def)
  apply (wpsimp wp: valid_whileLoop[where I="\<lambda>_. ?pre"])
    apply (intro hoare_vcg_conj_lift_pre_fix)
     apply (clarsimp simp: handleOverrunLoopBody_def)
     apply (wpsimp wp: updateRefillHd_valid_objs' simp: refillSingle_def)
     apply (frule (1) sc_ko_at_valid_objs_valid_sc')
     apply (fastforce simp: valid_sched_context'_def active_sc_at'_def obj_at_simps refillTailIndex_def Let_def
                     split: if_split_asm)
    apply (rule_tac f=ksCurSc in hoare_lift_Pf3)
     apply wpsimp+
  done

lemma refillBudgetCheck_valid_objs':
  "refillBudgetCheck usage \<lbrace>valid_objs'\<rbrace>"
  apply (clarsimp simp: refillBudgetCheck_def isRoundRobin_def refillReady_def getCurSc_def)
  apply (rule bind_wp[OF _ gets_sp])
  apply (rule bind_wp[OF _ scActive_sp])
  apply (rule bind_wp[OF _ assert_sp])
  apply (wpsimp wp: headInsufficientLoop_valid_objs' handleOverrunLoop_valid_objs'
                    hoare_vcg_all_lift updateRefillHd_valid_objs' hoare_vcg_if_lift2 hoare_drop_imps)
  apply (clarsimp simp: active_sc_at'_def obj_at'_def)
  done

lemma refillBudgetCheck_valid_mdb'[wp]:
  "refillBudgetCheck usage \<lbrace>valid_mdb'\<rbrace>"
  apply (clarsimp simp: handleOverrunLoop_def valid_mdb'_def)
  apply (wpsimp wp: scActive_wp)
  done

lemma handleOverrunLoop_list_refs_of_replies'[wp]:
  "handleOverrunLoop usage \<lbrace>\<lambda>s. sym_refs (list_refs_of_replies' s)\<rbrace>"
  apply (clarsimp simp: handleOverrunLoop_def)
  apply (wpsimp wp: whileLoop_valid_inv hoare_drop_imps getRefillNext_wp
                    getRefillSize_wp refillFull_wp refillEmpty_wp
              simp: o_def handleOverrunLoopBody_def refillPopHead_def updateSchedContext_def
                    scheduleUsed_def refillAddTail_def  updateRefillHd_def setRefillTl_def
                    updateRefillTl_def refillSingle_def)
  done

lemma refillBudgetCheck_list_refs_of_replies'[wp]:
  "refillBudgetCheck usage \<lbrace>\<lambda>s. sym_refs (list_refs_of_replies' s)\<rbrace>"
  apply (clarsimp simp: refillBudgetCheck_def refillPopHead_def updateSchedContext_def
                        setReprogramTimer_def refillReady_def isRoundRobin_def
                        headInsufficientLoop_def nonOverlappingMergeRefills_def)
  apply (rule bind_wp_fwd_skip, solves wpsimp)+
  apply (wpsimp wp: whileLoop_valid_inv hoare_drop_imps refillFull_wp refillEmpty_wp getRefillNext_wp
                     getRefillSize_wp hoare_vcg_all_lift hoare_vcg_if_lift2
              simp: o_def scheduleUsed_def refillAddTail_def setRefillHd_def updateRefillHd_def
                    setRefillTl_def updateRefillTl_def updateSchedContext_def)
  done

lemma refillBudgetCheck_if_live_then_nonz_cap'[wp]:
  "refillBudgetCheck uage \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (wpsimp simp: refillBudgetCheck_def setReprogramTimer_def refillReady_def
                      isRoundRobin_def
                  wp: hoare_drop_imps)
  done

lemma refillBudgetCheck_valid_idle'[wp]:
  "refillBudgetCheck usage \<lbrace>valid_idle'\<rbrace>"
  apply (clarsimp simp: refillBudgetCheck_def isRoundRobin_def refillReady_def
                        setReprogramTimer_def updateRefillHd_def setRefillHd_def)
  apply (rule bind_wp_fwd_skip, solves wpsimp)+
  apply (wpsimp wp: updateSchedContext_valid_idle')
  done

lemma handleOverrunLoop_valid_machine_state'[wp]:
  "handleOverrunLoop usage \<lbrace>valid_machine_state'\<rbrace>"
  apply (clarsimp simp: handleOverrunLoop_def)
  apply (wpsimp wp: whileLoop_valid_inv hoare_drop_imps getRefillNext_wp
                    getRefillSize_wp refillFull_wp refillEmpty_wp
              simp: handleOverrunLoopBody_def refillPopHead_def updateSchedContext_def
                    scheduleUsed_def refillAddTail_def  updateRefillHd_def setRefillTl_def
                    updateRefillTl_def refillSingle_def)
  done

lemma refillBudgetCheck_valid_machine_state'[wp]:
  "refillBudgetCheck usage \<lbrace>valid_machine_state'\<rbrace>"
  apply (clarsimp simp: refillBudgetCheck_def refillPopHead_def updateSchedContext_def
                        setReprogramTimer_def refillReady_def isRoundRobin_def
                        headInsufficientLoop_def nonOverlappingMergeRefills_def)
  apply (rule bind_wp_fwd_skip, solves wpsimp)+
  apply (wpsimp wp: whileLoop_valid_inv hoare_vcg_all_lift hoare_vcg_disj_lift scActive_wp hoare_drop_imps
                    refillFull_wp refillEmpty_wp getRefillNext_wp  getRefillSize_wp
              simp: scheduleUsed_def refillAddTail_def setRefillTl_def updateRefillTl_def
                    setRefillHd_def updateRefillHd_def updateSchedContext_def)
  done

lemma refillBudgetCheck_ct_idle_or_in_cur_domain'[wp]:
  "refillBudgetCheck usage \<lbrace>ct_idle_or_in_cur_domain'\<rbrace>"
  apply (clarsimp simp: refillBudgetCheck_def isRoundRobin_def refillReady_def
                        setReprogramTimer_def updateRefillHd_def)
  apply (wpsimp wp: getRefillSize_wp refillFull_wp refillEmpty_wp hoare_vcg_all_lift hoare_drop_imps
                    hoare_vcg_if_lift2
              simp: scheduleUsed_def refillAddTail_def setRefillTl_def updateRefillTl_def
                    updateRefillHd_def setRefillHd_def)
  done

lemma refillBudgetCheck_invs'[wp]:
  "refillBudgetCheck usage \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: invs'_def valid_pspace'_def pred_conj_def)
  apply (wpsimp wp: refillBudgetCheck_valid_objs')
  done

lemma commitTime_invs':
  "commitTime \<lbrace>invs'\<rbrace>"
  apply (simp add: commitTime_def)
  apply wpsimp
       apply (wpsimp wp: updateSchedContext_invs'_indep)
      apply (clarsimp simp: valid_sched_context'_def valid_sched_context_size'_def objBits_def sc_size_bounds_def objBitsKO_def live_sc'_def)
      apply (rule_tac Q="\<lambda>_. invs'" in hoare_strengthen_post)
       apply (wpsimp wp: isRoundRobin_wp)
      apply (wpsimp wp: getConsumedTime_wp getCurSc_wp)+
  by (clarsimp simp: active_sc_at'_def obj_at'_real_def ko_wp_at'_def)

lemma switchSchedContext_invs':
  "switchSchedContext \<lbrace>invs'\<rbrace>"
  apply (simp add: switchSchedContext_def)
  apply (wpsimp wp: commitTime_invs' getReprogramTimer_wp refillUnblockCheck_invs' threadGet_wp simp: getCurSc_def)
  apply (fastforce simp: obj_at'_def projectKO_eq projectKO_opt_tcb)
  done

lemma isSchedulable_bool_runnableE:
  "isSchedulable_bool t s \<Longrightarrow> tcb_at' t s \<Longrightarrow> st_tcb_at' runnable' t s"
  unfolding isSchedulable_bool_def
  by (clarsimp simp: pred_tcb_at'_def obj_at'_def pred_map_def projectKO_eq projectKO_opt_tcb
              elim!: opt_mapE)

lemma rescheduleRequired_invs'[wp]:
  "rescheduleRequired \<lbrace>invs'\<rbrace>"
  unfolding rescheduleRequired_def
  apply (wpsimp wp: ssa_invs' isSchedulable_wp)
  apply (clarsimp simp: invs'_def isSchedulable_bool_def vs_all_heap_simps
                        st_tcb_at'_def obj_at_simps pred_map_simps
                 elim!: opt_mapE)
  done

lemma rescheduleRequired_ksSchedulerAction[wp]:
  "\<lbrace>\<lambda>_. P ChooseNewThread\<rbrace> rescheduleRequired \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  unfolding rescheduleRequired_def by (wpsimp wp: isSchedulable_wp)

lemma inReleaseQueue_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko tcb_ptr s \<longrightarrow> P (tcbInReleaseQueue ko) s\<rbrace>
   inReleaseQueue tcb_ptr
   \<lbrace>P\<rbrace>"
  unfolding inReleaseQueue_def threadGet_getObject
  apply (wpsimp wp: getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma possibleSwitchTo_weak_sch_act[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<and> st_tcb_at' runnable' t s\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding possibleSwitchTo_def
  apply (wpsimp wp: inReleaseQueue_wp threadGet_wp rescheduleRequired_weak_sch_act_wf)
  by (auto simp: obj_at'_def weak_sch_act_wf_def tcb_in_cur_domain'_def
                 projectKO_eq ps_clear_domE)

crunch possibleSwitchTo
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

lemmas possibleSwitchTo_typ_ats[wp] = typ_at_lifts[OF possibleSwitchTo_typ_at']

lemma possibleSwitchTo_sch_act[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> st_tcb_at' runnable' t s\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (wpsimp simp: possibleSwitchTo_def wp: inReleaseQueue_wp threadGet_wp)
  by (fastforce simp: obj_at'_def tcb_in_cur_domain'_def)

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

lemma possibleSwitchTo_invs'[wp]:
  "\<lbrace>invs' and st_tcb_at' runnable' tptr\<rbrace>
   possibleSwitchTo tptr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: possibleSwitchTo_def)
  apply (wpsimp wp: hoare_vcg_imp_lift threadGet_wp inReleaseQueue_wp ssa_invs')
  apply (clarsimp simp: invs'_def pred_tcb_at'_def obj_at'_def)
  done

lemma possibleSwitchTo_sch_act_not_other:
  "\<lbrace>\<lambda>s. sch_act_not t' s \<and> t' \<noteq> t\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>_. sch_act_not t'\<rbrace>"
  apply (clarsimp simp: possibleSwitchTo_def)
  apply (wpsimp wp: threadGet_wp inReleaseQueue_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma setReleaseQueue_tcb_at'[wp]:
 "setReleaseQueue qs \<lbrace>typ_at' T tcbPtr\<rbrace>"
  unfolding setReleaseQueue_def
  by wpsimp

lemma setReleaseQueue_ksReleaseQueue[wp]:
  "\<lbrace>\<lambda>_. P qs\<rbrace> setReleaseQueue qs \<lbrace>\<lambda>_ s. P (ksReleaseQueue s)\<rbrace>"
  by (wpsimp simp: setReleaseQueue_def)

lemma setReleaseQueue_pred_tcb_at'[wp]:
 "setReleaseQueue qs \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
  by (wpsimp simp: setReleaseQueue_def)

crunch setReprogramTimer, possibleSwitchTo
  for ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"
  (wp: crunch_wps simp: crunch_simps)

lemma tcbReleaseDequeue_distinct_release_queue[wp]:
  "tcbReleaseDequeue \<lbrace>distinct_release_queue\<rbrace>"
  unfolding tcbReleaseDequeue_def
  by (wpsimp simp: distinct_tl)

lemma getReleaseQueue_sp:
  "\<lbrace>Q\<rbrace> getReleaseQueue \<lbrace>\<lambda>r. (\<lambda>s. r = ksReleaseQueue s) and Q\<rbrace>"
  unfolding getReleaseQueue_def
  by wpsimp

lemma releaseQNonEmptyAndReady_implies_releaseQNonEmpty:
  "the (releaseQNonEmptyAndReady s) \<Longrightarrow> ksReleaseQueue s \<noteq> []"
  by (clarsimp simp: releaseQNonEmptyAndReady_def readTCBRefillReady_def readReleaseQueue_def
                     obind_def omonad_defs)

lemma awaken_invs':
  "awaken \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: awaken_def awakenBody_def)
  apply (rule_tac I="\<lambda>_. invs'" in valid_whileLoop; simp add: runReaderT_def)
  apply (rule bind_wp[OF _ getReleaseQueue_sp])
  apply (rule bind_wp[OF _ assert_sp])
  apply wpsimp
   apply (rule hoare_drop_imps)
   apply (rule tcbReleaseDequeue_invs')
  apply (fastforce intro!: releaseQNonEmptyAndReady_implies_releaseQNonEmpty)
  done

crunch tcbReleaseDequeue
  for st_tcb_at'[wp]: "\<lambda>s. Q (st_tcb_at' P p s)"
  and valid_replies' [wp]: valid_replies'
  (wp: crunch_wps threadSet_pred_tcb_no_state valid_replies'_lift)

lemma awaken_sch_act_wf[wp]:
  "awaken \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: awaken_def awakenBody_def)
  apply (rule_tac I="\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s" in valid_whileLoop; simp add: runReaderT_def)
  apply (rule bind_wp[OF _ getReleaseQueue_sp])
  apply (rule bind_wp[OF _ assert_sp])
  apply wpsimp
   apply (rule hoare_drop_imp)
   apply wpsimp
  apply (fastforce intro!: releaseQNonEmptyAndReady_implies_releaseQNonEmpty)
  done

crunch awaken
  for cur_tcb'[wp]: cur_tcb'
  (wp: crunch_wps)

crunch checkDomainTime
  for invs'[wp]: invs'
  and sch_act_wf[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  and cur_tcb'[wp]: cur_tcb'
  (simp: crunch_simps wp: crunch_wps)

lemma schedule_invs':
  "schedule \<lbrace>invs'\<rbrace>"
  supply if_split [split del]
  apply (simp add: schedule_def scAndTimer_def cur_tcb'_asrt_def)
  apply (intro bind_wp[OF _ stateAssert_sp])
  apply (clarsimp simp: sch_act_wf_asrt_def)
  apply (rule_tac bind_wp, rename_tac t)
   apply (rule_tac Q="invs' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and cur_tcb'" in hoare_weaken_pre)
    apply (rule bind_wp_fwd_skip, wpsimp)
    apply (rule_tac bind_wp[OF _ getCurThread_sp])
    apply (rule_tac bind_wp[OF _ isSchedulable_sp])
    apply (rule_tac bind_wp[OF _ getSchedulerAction_sp])
    apply (rule bind_wp)
     apply (wpsimp wp: switchSchedContext_invs')
    apply (wpsimp wp: scheduleChooseNewThread_invs' isSchedulable_wp setSchedulerAction_invs'
                      ssa_invs' hoare_vcg_disj_lift)
           apply (wpsimp simp: isHighestPrio_def')
          apply (wpsimp wp: curDomain_wp)
         apply (wpsimp simp: scheduleSwitchThreadFastfail_def)
        apply (rename_tac tPtr x idleThread targetPrio)
        apply (rule_tac Q="\<lambda>_. invs' and st_tcb_at' runnable' tPtr and cur_tcb'"
                     in hoare_strengthen_post[rotated])
         apply (prop_tac "st_tcb_at' runnable' tPtr s \<Longrightarrow> obj_at' (\<lambda>a. activatable' (tcbState a)) tPtr s")
          apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
         apply fastforce
        apply (wpsimp wp: threadGet_wp hoare_drop_imp hoare_vcg_ex_lift)
       apply (rename_tac tPtr x idleThread)
       apply (rule_tac Q="\<lambda>_. invs' and st_tcb_at' runnable' tPtr and cur_tcb'"
                    in hoare_strengthen_post[rotated])
        apply (subst obj_at_ko_at'_eq[symmetric], simp)
       apply (wpsimp wp: threadGet_wp hoare_drop_imp hoare_vcg_ex_lift)
      apply (rename_tac tPtr x)
      apply (rule_tac Q="\<lambda>_. invs' and st_tcb_at' runnable' tPtr and cur_tcb'"
                   in hoare_strengthen_post[rotated])
       apply (subst obj_at_ko_at'_eq[symmetric], simp)
      apply (wpsimp wp: tcbSchedEnqueue_invs' isSchedulable_wp)+
    apply (fastforce split: if_split dest: isSchedulable_bool_runnableE simp: cur_tcb'_def)
   apply assumption
  apply (wpsimp wp: awaken_invs')
  done

lemma setCurThread_nosch:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
  setCurThread t
  \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: setCurThread_def)
  apply wp
  apply simp
  done

lemma stt_nosch:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
  switchToThread t
  \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: Thread_H.switchToThread_def ARM_H.switchToThread_def storeWordUser_def)
  apply (wp setCurThread_nosch hoare_drop_imp |simp)+
  done

lemma stit_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
    switchToIdleThread
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def
                   ARM_H.switchToIdleThread_def  storeWordUser_def)
  apply (wp setCurThread_nosch | simp add: getIdleThread_def)+
  done

lemma chooseThread_nosch:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
  chooseThread
  \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  unfolding chooseThread_def Let_def curDomain_def
  supply if_split[split del]
  apply (simp only: return_bind, simp)
  apply (wp findM_inv | simp)+
  apply (case_tac queue)
  apply (wp stt_nosch isSchedulable_wp | simp add: curDomain_def bitmap_fun_defs)+
  done

crunch switchSchedContext, setNextInterrupt
  for ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

lemma schedule_sch:
  "\<lbrace>\<top>\<rbrace> schedule \<lbrace>\<lambda>rv s. ksSchedulerAction s = ResumeCurrentThread\<rbrace>"
  unfolding schedule_def scAndTimer_def
  by (wpsimp wp: setSchedulerAction_direct simp: getReprogramTimer_def scheduleChooseNewThread_def)

lemma schedule_sch_act_simple:
  "\<lbrace>\<top>\<rbrace> schedule \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  apply (rule hoare_strengthen_post [OF schedule_sch])
  apply (simp add: sch_act_simple_def)
  done

lemma ssa_ct:
  "\<lbrace>ct_in_state' P\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>rv. ct_in_state' P\<rbrace>"
proof -
  show ?thesis
    apply (unfold setSchedulerAction_def)
    apply wp
    apply (clarsimp simp add: ct_in_state'_def pred_tcb_at'_def)
    done
qed

lemma scheduleChooseNewThread_ct_activatable'[wp]:
  "\<lbrace> invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread) \<rbrace>
   scheduleChooseNewThread
   \<lbrace>\<lambda>_. ct_in_state' activatable'\<rbrace>"
  unfolding scheduleChooseNewThread_def
  by (wpsimp simp: ct_in_state'_def
                wp: ssa_invs' nextDomain_invs'
                    chooseThread_activatable_2[simplified ct_in_state'_def]
         | (rule hoare_lift_Pf[where f=ksCurThread], solves wp))+

lemma st_tcb_at_activatable_coerce_concrete:
  assumes t: "st_tcb_at activatable t s"
  assumes sr: "(s, s') \<in> state_relation"
  assumes tcb: "tcb_at' t s'"
  shows "st_tcb_at' activatable' t s'"
  using t
  apply -
  apply (rule ccontr)
  apply (drule pred_tcb_at'_Not[THEN iffD2, OF conjI, OF tcb])
  apply (drule st_tcb_at_coerce_abstract[OF _ sr])
  apply (clarsimp simp: st_tcb_def2)
  apply (case_tac "tcb_state tcb"; simp)
  done

lemma ct_in_state'_activatable_coerce_concrete:
  "\<lbrakk>ct_in_state activatable s; (s, s') \<in> state_relation; cur_tcb' s'\<rbrakk>
    \<Longrightarrow> ct_in_state' activatable' s'"
   unfolding ct_in_state'_def cur_tcb'_def ct_in_state_def
   apply (rule st_tcb_at_activatable_coerce_concrete[rotated], simp, simp)
   apply (frule curthread_relation, simp)
   done

lemma threadSet_sch_act_sane[wp]:
  "\<lbrace>sch_act_sane\<rbrace> threadSet f t \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  by (wp sch_act_sane_lift)

lemma rescheduleRequired_sch_act_sane[wp]:
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>rv. sch_act_sane\<rbrace>"
  apply (simp add: rescheduleRequired_def sch_act_sane_def
                   setSchedulerAction_def)
  by (wp isSchedulable_wp | wpc | clarsimp)+

crunch setThreadState, setBoundNotification
 for sch_act_sane[wp]: "sch_act_sane"
  (simp: crunch_simps wp: crunch_wps)

lemma weak_sch_act_wf_at_cross:
  assumes sr: "(s,s') \<in> state_relation"
  assumes aligned: "pspace_aligned s"
  assumes distinct: "pspace_distinct s"
  assumes t: "valid_sched_action s"
  shows "weak_sch_act_wf (ksSchedulerAction s') s'"
  using assms
  apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def weak_sch_act_wf_def)
  apply (frule state_relation_sched_act_relation)
  apply (rename_tac t)
  apply (drule_tac x=t in spec)
  apply (prop_tac "scheduler_action s = switch_thread t")
   apply (metis sched_act_relation.simps Structures_A.scheduler_action.exhaust
                scheduler_action.simps)
  apply (intro conjI impI)
   apply (rule st_tcb_at_runnable_cross; fastforce?)
   apply (clarsimp simp: vs_all_heap_simps pred_tcb_at_def obj_at_def)
  apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def etcb_at_def vs_all_heap_simps)
  apply (prop_tac "tcb_at t s")
   apply (clarsimp simp: obj_at_def is_tcb_def)
  apply (frule state_relation_pspace_relation)
  apply (frule (3) tcb_at_cross)
  apply (clarsimp simp: tcb_in_cur_domain'_def obj_at'_def projectKOs)
  apply (frule curdomain_relation)
  apply (frule (2) pspace_relation_tcb_domain_priority)
  apply simp
  done

lemma possibleSwitchTo_corres:
  "t = t' \<Longrightarrow>
   corres dc
    (valid_sched_action and tcb_at t and pspace_aligned and pspace_distinct
     and valid_tcbs and active_scs_valid)
    (valid_queues and valid_queues' and valid_release_queue_iff and valid_tcbs')
      (possible_switch_to t)
      (possibleSwitchTo t')"
  supply dc_simp [simp del]
  apply (rule corres_cross_add_guard[where Q="tcb_at' t"])
   apply (fastforce intro: tcb_at_cross)
  apply (simp add: possible_switch_to_def possibleSwitchTo_def cong: if_cong)
  apply (rule corres_guard_imp)
    apply (simp add: get_tcb_obj_ref_def)
    apply (rule corres_split)
       apply (rule threadGet_corres[where r="(=)"])
       apply (clarsimp simp: tcb_relation_def)
      apply (rule corres_split[OF inReleaseQueue_corres], simp)
        apply (rule corres_when[rotated])
         apply (rule corres_split[OF curDomain_corres], simp)
           apply (rule corres_split)
              apply (rule threadGet_corres[where r="(=)"])
              apply (clarsimp simp: tcb_relation_def)
             apply (rule corres_split[OF getSchedulerAction_corres])
               apply (rule corres_if, simp)
                apply (rule tcbSchedEnqueue_corres)
               apply (rule corres_if[rotated], simp)
                 apply (rule corres_split[OF rescheduleRequired_corres])
                   apply (rule tcbSchedEnqueue_corres)
                  apply wp+
                apply (rule setSchedulerAction_corres, simp)
               apply (rename_tac rv rv')
               apply (case_tac rv; simp)
              apply (wpsimp simp: if_apply_def2 valid_sched_action_def
                              wp: hoare_drop_imp inReleaseQueue_inv)+
  done

lemma ct_active_cross:
  "\<lbrakk> (s,s') \<in> state_relation; pspace_aligned s; pspace_distinct s; ct_active s \<rbrakk>
     \<Longrightarrow> ct_active' s'"
  by (clarsimp simp: state_relation_def ct_in_state_def ct_in_state'_def
                     st_tcb_at_runnable_cross runnable_eq_active runnable_eq_active'[symmetric])

\<comment> \<open>Strengthen the consequent as necessary, there's more that can be derived from the assumptions\<close>
lemma ct_released_cross_weak:
  "\<lbrakk> (s,s') \<in> state_relation; pspace_aligned s; pspace_distinct s; ct_released s; cur_tcb' s' \<rbrakk>
     \<Longrightarrow> bound_sc_tcb_at' bound (ksCurThread s') s'"
  apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps)
  apply (clarsimp simp: state_relation_def pspace_relation_def )
  apply (erule_tac x="ksCurThread s'" in ballE)
   apply (auto simp: vs_all_heap_simps other_obj_relation_def tcb_relation_def
                          cur_tcb'_def pred_tcb_at'_def obj_at'_def projectKOs
                   split: kernel_object.splits)
  done

lemma setReprogramTimer_corres[corres]:
  "corres dc \<top> \<top> (modify (reprogram_timer_update (\<lambda>_. b))) (setReprogramTimer b)"
  apply (unfold setReprogramTimer_def)
  apply (rule corres_modify)
  apply (simp add: state_relation_def swp_def)
  done

lemma getCurTime_corres[corres]:
  "corres (=) \<top> \<top> (gets cur_time) (getCurTime)"
  apply (clarsimp simp: getCurTime_def state_relation_def)
  done

lemma readRefillReady_simp:
  "readRefillReady scp s
   = (case readSchedContext scp s
        of None \<Rightarrow> None
         | Some sc' \<Rightarrow> Some (rTime (refillHd sc') \<le> (ksCurTime s) + kernelWCETTicks))"
  by (clarsimp simp: readRefillReady_def readCurTime_def readSchedContext_SomeD asks_def obind_def)

lemma refillReady_corres:
  "corres (=)
     (sc_at sc_ptr and
        (\<lambda>s. ((\<lambda>sc. sc_refills sc \<noteq> []) |< scs_of2 s) sc_ptr))
     (sc_at' sc_ptr and valid_refills' sc_ptr)
        (get_sc_refill_ready sc_ptr)
        (refillReady sc_ptr)"
  supply getSchedContext_wp[wp del] set_sc'.get_wp[wp del] projection_rewrites[simp]
  apply (clarsimp simp: refill_ready_def refillReady_def get_sc_refill_ready_def)
  apply (rule gets_the_corres)
    apply (wpsimp wp: no_ofail_read_sc_refill_ready)
    apply (clarsimp simp: is_sc_obj obj_at_def)
   apply wpsimp
  apply (clarsimp simp: obj_at_def is_sc_obj dest!: no_ofailD[OF readRefillReady_no_ofail]
                 intro: no_ofailD[OF no_ofail_read_sc_refill_ready])
  apply (insert no_ofailD[OF no_ofail_read_sc_refill_ready, rule_format])
  apply (drule_tac x=s and y=sc_ptr in meta_spec2)
  apply (prop_tac "\<exists>sc n. kheap s sc_ptr = Some (kernel_object.SchedContext sc n)")
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
  apply clarsimp
  apply (clarsimp simp: read_sc_refill_ready_simp readRefillReady_simp readSchedContext_def
                        read_sched_context_def
                 split: option.splits dest!: readObject_misc_ko_at')
  apply (rename_tac n sc' sc)
  apply (frule state_relation_sc_relation; (clarsimp simp: obj_at'_def obj_at_def projectKOs is_sc_obj))
     apply fastforce+
  apply (fastforce simp: kernelWCETTicks_def refill_ready_def state_relation_def refill_map_def
                         obj_at_def opt_map_red opt_pred_def valid_refills'_def
                  dest!: refill_hd_relation)
  done

lemma readTCBRefillReady_no_ofail:
  "no_ofail (\<lambda>s'. obj_at' (\<lambda>tcb. \<exists>sc. tcbSchedContext tcb = Some sc \<and> sc_at' sc s') t s')
            (readTCBRefillReady t)"
  unfolding readTCBRefillReady_def
  apply (wpsimp wp: ovalid_threadRead)
  apply (clarsimp simp: obj_at'_def)
  done

lemma readTCBRefillReady_simp:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s; valid_objs s;
    active_sc_tcb_at t s; active_scs_valid s; valid_objs' s'\<rbrakk>
   \<Longrightarrow> read_tcb_refill_ready t s = readTCBRefillReady t s'"
  apply (frule (1) active_scs_valid_tcb_at)
  apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps)
  apply (rename_tac scp tcb sc n)
  apply (prop_tac "tcb_at' t s' \<and> sc_at' scp s'")
   apply (fastforce dest!: state_relationD intro!: sc_at_cross tcb_at_cross
                     simp: obj_at_def is_tcb is_sc_obj
                     elim: valid_sched_context_size_objsI)
  apply clarsimp
  apply (prop_tac "bound (read_tcb_refill_ready t s)")
   apply (clarsimp intro!: no_ofailD[OF no_ofail_read_tcb_refill_ready]
                     simp: pred_tcb_at_def obj_at_def)
  apply (frule state_relation_pspace_relation)
  apply (clarsimp simp: pspace_relation_def)
  apply (drule_tac x=t in bspec, blast)
  apply (drule_tac x="(t, other_obj_relation)" in bspec, clarsimp)
  apply (clarsimp simp: other_obj_relation_def tcb_relation_def obj_at'_def projectKOs)
  apply (prop_tac "bound (readTCBRefillReady t s')")
   apply (clarsimp intro!: no_ofailD[OF readTCBRefillReady_no_ofail])
   apply (clarsimp simp: obj_at'_def projectKOs)
   apply (rule_tac x=scp in exI; clarsimp)
  apply clarsimp
  apply (clarsimp simp: read_tcb_refill_ready_def readTCBRefillReady_def oassert_opt_def
                        readRefillReady_simp read_sc_refill_ready_simp refill_ready'_def obj_at'_def
                        projectKOs
                 dest!: read_tcb_obj_ref_SomeD read_sched_context_SomeD readSchedContext_SomeD
                        threadRead_SomeD
                 split: option.split_asm)
  apply (rename_tac sc' sc_ptr tcbPtr)
  apply (prop_tac "valid_sched_context' sc' s' \<and> valid_sched_context_size' sc'")
   apply (frule_tac k=sc' and p=sc_ptr in sc_ko_at_valid_objs_valid_sc'[rotated])
    apply (clarsimp simp: obj_at'_def projectKOs)
   apply simp
  apply (frule state_relation_pspace_relation)
  apply (prop_tac "sc_relation sc n sc'")
   apply (clarsimp simp: pspace_relation_def)
   apply (drule_tac x=sc_ptr in bspec, blast)
   apply (fastforce simp: obj_at'_def projectKOs split: if_splits)
  apply (frule refill_hd_relation2)
    apply (clarsimp simp: valid_refills_tcb_at_def valid_refills_def rr_valid_refills_def
                          pred_tcb_at_def obj_at_def vs_all_heap_simps
                   split: if_splits)
   apply (fastforce dest!: sc_ko_at_valid_objs_valid_sc'
                     simp: obj_at'_def projectKOs)
  apply (clarsimp simp: kernelWCETTicks_def state_relation_def)
  done

lemma getReleaseQueue_corres[corres]:
  "corres (=) \<top> \<top> (gets release_queue) (getReleaseQueue)"
  unfolding getReleaseQueue_def
  apply (rule corres_gets_trivial)
  by (clarsimp simp: state_relation_def release_queue_relation_def)

lemma releaseQNonEmptyAndReady_simp:
  "releaseQNonEmptyAndReady s
    = (if ksReleaseQueue s = []
          then Some False
          else readTCBRefillReady (head (ksReleaseQueue s)) s)"
  by (clarsimp simp: releaseQNonEmptyAndReady_def readReleaseQueue_def asks_def obind_def)

lemma releaseQNonEmptyAndReady_eq:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s;
     valid_objs s; valid_release_q s;
     active_scs_valid s; valid_objs' s'\<rbrakk>
   \<Longrightarrow> read_release_q_non_empty_and_ready s = releaseQNonEmptyAndReady s'"
  apply (clarsimp simp: read_release_q_non_empty_and_ready_simp releaseQNonEmptyAndReady_simp)
  apply (fastforce simp: state_relation_def release_queue_relation_def
                 intro!: readTCBRefillReady_simp valid_release_q_active_sc)
  done

lemma ksReleaseQueue_length_well_founded:
  "wf {((r :: unit, s :: kernel_state), (r', s')). length (ksReleaseQueue s)
                                                    < length (ksReleaseQueue s')}"
  apply (insert wf_inv_image[where r="{(m, n). m < n}"
                               and f="\<lambda>(r :: unit, s :: kernel_state). length (ksReleaseQueue s)"])
  apply (clarsimp simp: inv_image_def)
  apply (prop_tac "wf {(m, n). m < n}")
   apply (fastforce intro: wf)
  apply (drule meta_mp)
   apply simp
  apply (prop_tac "{(x :: unit \<times> global.kernel_state, y ::  unit \<times> global.kernel_state).
                     (case x of (r, s) \<Rightarrow> length (ksReleaseQueue s))
                      < (case y of (r, s) \<Rightarrow> length (ksReleaseQueue s))}
                   = {((r, s), r', s'). length (ksReleaseQueue s) < length (ksReleaseQueue s')}")
   apply fastforce
  apply fastforce
  done

lemma tcbReleaseDequeue_ksReleaseQueue_length_helper:
  "\<lbrace>\<lambda>s'. ksReleaseQueue s' \<noteq> [] \<and> s' = s\<rbrace>
   tcbReleaseDequeue
   \<lbrace>\<lambda>r' s'. length (ksReleaseQueue s') < length (ksReleaseQueue s)\<rbrace>"
  apply (wpsimp simp: tcbReleaseDequeue_def getReleaseQueue_def setReleaseQueue_def)
  done

lemma tcbReleaseDequeue_ksReleaseQueue_length:
  "\<lbrace>\<lambda>s'. the (releaseQNonEmptyAndReady s') \<and> s' = s\<rbrace>
   tcbReleaseDequeue
   \<lbrace>\<lambda>r' s'. length (ksReleaseQueue s') < length (ksReleaseQueue s)\<rbrace>"
  apply (wpsimp wp: tcbReleaseDequeue_ksReleaseQueue_length_helper)
  apply (fastforce dest: releaseQNonEmptyAndReady_implies_releaseQNonEmpty)
  done

lemma awakenBody_ksReleaseQueue_length:
  "\<lbrace>\<lambda>s'. the (releaseQNonEmptyAndReady s') \<and> s' = s\<rbrace>
   awakenBody
   \<lbrace>\<lambda>r' s'. length (ksReleaseQueue s') < length (ksReleaseQueue s)\<rbrace>"
  apply (clarsimp simp: awakenBody_def)
  apply (wpsimp wp: tcbReleaseDequeue_ksReleaseQueue_length hoare_drop_imps)
  done

lemma awaken_terminates:
  "whileLoop_terminates (\<lambda>_ s'. (the (releaseQNonEmptyAndReady s'))) (\<lambda>_. awakenBody) r' s'"
  apply (rule_tac R="{((r', s'), (r, s)). length (ksReleaseQueue s') < length (ksReleaseQueue s)}"
               in whileLoop_terminates_inv)
    apply simp
   apply clarsimp
   apply (rule awakenBody_ksReleaseQueue_length)
  apply (rule ksReleaseQueue_length_well_founded)
  done

lemma reprogram_timer_update_release_queue_update_monad_commute:
  "monad_commute \<top> (modify (reprogram_timer_update (\<lambda>_. b))) (modify (release_queue_update q))"
  apply (clarsimp simp: monad_commute_def modify_def get_def put_def bind_def return_def)
  done

lemma release_queue_modify_tl:
  "\<lbrakk>(s, s') \<in> state_relation; valid_release_q s; release_queue s \<noteq> []\<rbrakk>
   \<Longrightarrow> (s\<lparr>release_queue := filter ((\<noteq>) (hd (release_queue s))) (release_queue s)\<rparr>,
        s'\<lparr>ksReleaseQueue := tl (release_queue s)\<rparr>) \<in> state_relation"
  apply (clarsimp simp: state_relation_def cdt_relation_def)
  apply (clarsimp simp: release_queue_relation_def)
  apply (prop_tac "ksReleaseQueue s' \<noteq> []", fastforce)
  apply (rule filter_hd_equals_tl)
   apply (prop_tac "distinct (release_queue s)")
    apply (clarsimp simp: valid_release_q_def)
   apply simp+
  done

lemma ksReleaseQueue_runnable'_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and valid_release_q)
             (\<lambda>s'. \<forall>t \<in> set (ksReleaseQueue s'). st_tcb_at' runnable' t s')"
  apply (clarsimp simp: cross_rel_def)
  apply (clarsimp simp: valid_release_q_def release_queue_relation_def)
  apply (frule state_relation_release_queue_relation)
  apply (clarsimp simp: release_queue_relation_def)
  apply (prop_tac "st_tcb_at runnable t s")
   apply (fastforce simp: obj_at_kh_kheap_simps)
  apply (fastforce intro: sts_rel_runnable
                   dest!: st_tcb_at_coerce_concrete
                    simp: st_tcb_at'_def obj_at'_def)
  done

lemma tcbReleaseDequeue_corres:
  "corres (=) (pspace_aligned and pspace_distinct and valid_release_q and (\<lambda>s. release_queue s \<noteq> []))
              \<top>
              tcb_release_dequeue
              tcbReleaseDequeue"
   (is "corres _ _ ?conc _ _")
  apply (rule corres_cross[where Q'="\<lambda>s'. \<forall>t \<in> set (ksReleaseQueue s'). st_tcb_at' runnable' t s'"
                           , OF ksReleaseQueue_runnable'_cross_rel], blast)
  apply (clarsimp simp: tcb_release_dequeue_def tcb_release_remove_def tcbReleaseDequeue_def
                        setReleaseQueue_def tcb_sched_dequeue_def)
  apply (rule corres_symb_exec_l[rotated 2, OF gets_sp]; (solves wpsimp)?)
  apply (rename_tac rq)
  apply (simp add: bind_assoc)
  apply (rule corres_underlying_split[rotated 2, OF gets_sp getReleaseQueue_sp])
   apply (corresKsimp corres: getReleaseQueue_corres)

  apply clarsimp
  apply (rename_tac rq')
  apply (rule_tac F="rq' \<noteq> [] \<and> rq' = rq" in corres_req)
   apply (clarsimp simp: state_relation_def release_queue_relation_def)
  apply clarsimp

  apply (subst monad_commute_simple'[OF reprogram_timer_update_release_queue_update_monad_commute])
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule_tac P="valid_release_q and (\<lambda>s. release_queue s \<noteq> [] \<and> release_queue s = rq)"
                   and P'="\<lambda>s'. ksReleaseQueue s' \<noteq> []"
                    in corres_inst)
       apply (rule corres_modify)
       apply (fastforce intro: release_queue_modify_tl)
      apply wpsimp
      apply (rule corres_add_noop_lhs)
      apply (rule corres_split[OF threadSet_corres_noop])
              apply (clarsimp simp: tcb_relation_def)+
        apply (rule corres_split[OF setReprogramTimer_corres])
          apply wpsimp+
  apply (fastforce simp: st_tcb_at'_def)
  done

lemma tcbInReleaseQueue_update_valid_tcbs'[wp]:
  "threadSet (tcbInReleaseQueue_update f) tcbPtr \<lbrace>valid_tcbs'\<rbrace>"
  apply (wpsimp wp: threadSet_valid_tcbs')
  done

lemma tcbReleaseDequeue_valid_tcbs'[wp]:
  "tcbReleaseDequeue \<lbrace>valid_tcbs'\<rbrace>"
  apply (clarsimp simp: tcbReleaseDequeue_def setReleaseQueue_def setReprogramTimer_def)
  apply ((rule bind_wp_fwd_skip, wpsimp simp: valid_tcbs'_def) | wpsimp)+
  done

lemma ksReleaseQueue_distinct_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and valid_release_q)
             (\<lambda>s'. distinct (ksReleaseQueue s'))"
  apply (clarsimp simp: cross_rel_def)
  apply (fastforce dest: state_relation_release_queue_relation
                 intro!: tcb_at_cross
                   simp: valid_release_q_def release_queue_relation_def vs_all_heap_simps
                         obj_at_def is_tcb_def)
  done

lemma ksReleaseQueue_nonempty_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and (\<lambda>s. release_queue s \<noteq> []))
             (\<lambda>s'. ksReleaseQueue s' \<noteq> [])"
  apply (clarsimp simp: cross_rel_def)
   apply (fastforce dest: state_relation_release_queue_relation
                  intro!: tcb_at_cross
                    simp: valid_release_q_def release_queue_relation_def vs_all_heap_simps
                          obj_at_def is_tcb_def)
  done

lemma isRunnable_no_fail[wp]:
  "no_fail (tcb_at' tcbPtr) (isRunnable tcbPtr)"
  apply (wpsimp simp: isRunnable_def)
  done

lemma awakenBody_corres:
  "corres dc ((pspace_aligned and pspace_distinct and valid_objs and valid_sched_action
               and valid_tcbs and valid_release_q and active_scs_valid)
              and (\<lambda>s. release_queue s \<noteq> []))
             (valid_objs' and valid_queues and valid_queues' and valid_release_queue_iff)
             awaken_body
             awakenBody"
  (is "corres _ (?pred and _) ?conc _ _")
  apply (rule corres_cross[where Q'="\<lambda>s'. distinct (ksReleaseQueue s')"
                           , OF ksReleaseQueue_distinct_cross_rel], blast)
  apply (rule corres_cross[where Q'="\<lambda>s'. ksReleaseQueue s' \<noteq> []"
                           , OF ksReleaseQueue_nonempty_cross_rel], blast)
  apply (rule corres_cross[where Q'="\<lambda>s'. \<forall>t \<in> set (ksReleaseQueue s'). st_tcb_at' runnable' t s'"
                           , OF ksReleaseQueue_runnable'_cross_rel], blast)

  apply (clarsimp simp: awaken_body_def awakenBody_def)
  apply (rule corres_symb_exec_r[rotated, OF getReleaseQueue_sp])
    apply (wpsimp wp: gets_sp simp: getReleaseQueue_def)
   apply (wpsimp wp: gets_exs_valid
               simp: getReleaseQueue_def)
  apply (rule corres_symb_exec_r[rotated, OF assert_inv]; (solves wpsimp)?)
  apply (rule_tac Q="\<lambda>rv. ?pred and tcb_at rv"
              and Q'="\<lambda>rv. ?conc and st_tcb_at' runnable' rv"
               in corres_underlying_split[rotated 2])
     apply (wpsimp simp: tcb_release_dequeue_def)
     apply (force simp: valid_release_q_def vs_all_heap_simps obj_at_def is_tcb_def)
    apply wpsimp
   apply (corresKsimp corres: tcbReleaseDequeue_corres)
  apply (rule corres_symb_exec_r[OF _ isRunnable_sp, rotated]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ assert_sp, rotated]; (solves wpsimp)?)
   apply wpsimp
   apply (clarsimp simp: st_tcb_at'_def obj_at'_def projectKOs objBitsKO_def)
   apply (case_tac "tcbState tcb'"; clarsimp)
  apply (corresKsimp corres: possibleSwitchTo_corres)
  done

lemma tcbReleaseDequeue_no_fail:
  "no_fail (\<lambda>s'. (\<forall>tcbPtr \<in> set (ksReleaseQueue s'). tcb_at' tcbPtr s') \<and> ksReleaseQueue s' \<noteq> [])
           tcbReleaseDequeue"
  apply (wpsimp simp: tcbReleaseDequeue_def getReleaseQueue_def setReleaseQueue_def
                      setReprogramTimer_def)
  done

lemma addToBitmap_no_fail[wp]:
  "no_fail \<top> (addToBitmap tdom tprio)"
  apply (wpsimp simp: bitmap_fun_defs)
  done

lemma tcbSchedEnqueue_no_fail[wp]:
  "no_fail (tcb_at' tcbPtr) (tcbSchedEnqueue tcbPtr)"
  apply (clarsimp simp: tcbSchedEnqueue_def)
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imps)
  done

lemma inReleaseQueue_no_fail[wp]:
  "no_fail (tcb_at' tcbPtr) (inReleaseQueue tcbPtr)"
  apply (wpsimp simp: inReleaseQueue_def)
  done

lemma isSchedulable_no_fail:
  "no_fail (tcb_at' tcbPtr and valid_objs') (isSchedulable tcbPtr)"
  apply (clarsimp simp: isSchedulable_def isRunnable_def inReleaseQueue_def)
  apply (wpsimp wp: no_fail_bind hoare_vcg_imp_lift' hoare_vcg_conj_lift getTCB_wp)
  apply (fastforce dest: tcb_ko_at_valid_objs_valid_tcb'
                   simp: valid_tcb'_def)
  done

lemma rescheduleRequired_no_fail:
  "no_fail (\<lambda>s'. weak_sch_act_wf (ksSchedulerAction s') s' \<and> valid_objs' s') rescheduleRequired"
  apply (clarsimp simp: rescheduleRequired_def getSchedulerAction_def isSchedulable_def
                        setSchedulerAction_def)
  apply (wpsimp wp: isSchedulable_no_fail hoare_vcg_if_lift2 hoare_drop_imps)
  apply (clarsimp simp: weak_sch_act_wf_def)
  done

lemma possibleSwitchTo_no_fail:
  "no_fail (\<lambda>s'. weak_sch_act_wf (ksSchedulerAction s') s' \<and> valid_objs' s' \<and> tcb_at' tcbPtr s')
           (possibleSwitchTo tcbPtr)"
  apply (clarsimp simp: possibleSwitchTo_def inReleaseQueue_def curDomain_def getSchedulerAction_def
                        setSchedulerAction_def)
  apply (wpsimp wp: rescheduleRequired_no_fail threadGet_wp simp: setSchedulerAction_def)
  apply (fastforce simp: obj_at'_def projectKOs objBitsKO_def)
  done

lemma tcbReleaseDequeue_weak_sch_act_wf[wp]:
  "tcbReleaseDequeue \<lbrace>\<lambda>s'. weak_sch_act_wf (ksSchedulerAction s') s'\<rbrace>"
  apply (clarsimp simp: tcbReleaseDequeue_def setReleaseQueue_def setReprogramTimer_def)
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: weak_sch_act_wf_def st_tcb_at'_def obj_at'_def projectKOs objBitsKO_def
                         tcb_in_cur_domain'_def ps_clear_def)
  done

lemma tcbReleaseQueue_tcb_at'_rv:
  "\<lbrace>\<lambda>s'. ksReleaseQueue s' \<noteq> [] \<and> tcb_at' (hd (ksReleaseQueue s')) s'\<rbrace>
   tcbReleaseDequeue
   \<lbrace>\<lambda>rv. tcb_at' rv\<rbrace>"
  apply (wpsimp simp: tcbReleaseDequeue_def setReleaseQueue_def)
  done

lemma awakenBody_no_fail:
  "no_fail (\<lambda>s'. weak_sch_act_wf (ksSchedulerAction s') s' \<and> valid_objs' s'
                 \<and> (\<forall>tcbPtr \<in> set (ksReleaseQueue s'). st_tcb_at' runnable' tcbPtr s')
                 \<and> ksReleaseQueue s' \<noteq> [] \<and> distinct (ksReleaseQueue s'))
           awakenBody"
  apply (clarsimp simp: awakenBody_def setReprogramTimer_def)
  apply (wpsimp wp: possibleSwitchTo_no_fail tcbReleaseDequeue_no_fail tcbReleaseQueue_tcb_at'_rv
                    hoare_drop_imps
              simp: getReleaseQueue_def)
  apply fastforce
  done

lemma tcbReleaseDequeue_dequeue_inv:
  "tcbReleaseDequeue \<lbrace>\<lambda>s. tcbPtr \<notin> set (ksReleaseQueue s)\<rbrace>"
  apply (clarsimp simp: tcbReleaseDequeue_def)
  apply wpsimp
  apply (case_tac "ksReleaseQueue s = []"; simp add: list.set_sel(2))
  done

lemma awaken_corres:
  "corres dc (pspace_aligned and pspace_distinct and valid_objs and valid_release_q
              and valid_sched_action and valid_tcbs and active_scs_valid)
             (\<lambda>s'. weak_sch_act_wf (ksSchedulerAction s') s' \<and> valid_objs' s' \<and> valid_queues s'
                   \<and> valid_queues' s' \<and> valid_release_queue_iff s')
             Schedule_A.awaken
             awaken"
  apply (rule corres_cross[where Q'="\<lambda>s'. \<forall>t \<in> set (ksReleaseQueue s'). st_tcb_at' runnable' t s'"
                           , OF ksReleaseQueue_runnable'_cross_rel], blast)
  apply (rule corres_cross[where Q'="\<lambda>s'. distinct (ksReleaseQueue s')"
                           , OF ksReleaseQueue_distinct_cross_rel], blast)
  apply (clarsimp simp: awaken_def Schedule_A.awaken_def runReaderT_def)
  apply (rule corres_whileLoop; simp)
       apply (simp add: releaseQNonEmptyAndReady_eq)
      apply (rule corres_guard_imp)
        apply (rule awakenBody_corres)
       apply (fastforce simp: read_release_q_non_empty_and_ready_simp)
      apply simp
     apply (clarsimp simp: pred_conj_def)
     apply (intro hoare_vcg_conj_lift_pre_fix
            ; (solves \<open>wpsimp simp: Schedule_A.awaken_body_def tcb_release_dequeue_def\<close>)?)
     apply (wpsimp wp: awaken_body_valid_sched_action)
     apply (frule valid_release_q_read_release_q_non_empty_and_ready_bound)
     apply (fastforce dest: read_release_q_non_empty_and_ready_True_simp)
    apply (wpsimp simp: awakenBody_def runReaderT_def
                    wp: hoare_vcg_ball_lift2 tcbReleaseDequeue_dequeue_inv hoare_drop_imps)
    apply (fastforce dest: releaseQNonEmptyAndReady_implies_releaseQNonEmpty)
   apply (fastforce intro: no_fail_pre awakenBody_no_fail
                     dest: releaseQNonEmptyAndReady_implies_releaseQNonEmpty)
  apply (fastforce intro!: awaken_terminates)
  done

lemma setDeadline_corres:
  "dl = dl' \<Longrightarrow> corres_underlying Id False True dc \<top> \<top> (setDeadline dl) (setDeadline dl')"
  by (simp, rule corres_underlying_trivial_gen; wpsimp simp: setDeadline_def)

(* This is not particularly insightful, it just shortens setNextInterrupt_corres *)
lemma setNextInterrupt_corres_helper:
  "\<lbrakk>valid_objs' s'; (s, s') \<in> state_relation; active_sc_tcb_at t s;
    valid_objs s; pspace_aligned s; pspace_distinct s\<rbrakk>
    \<Longrightarrow> \<exists>tcb. ko_at' tcb t s' \<and> sc_at' (the (tcbSchedContext tcb)) s' \<and>
        (\<forall>ko. ko_at' ko (the (tcbSchedContext tcb)) s' \<longrightarrow> sc_valid_refills' ko)"
  apply (subgoal_tac "\<exists>tcb'. ko_at' (tcb'  :: tcb) t s'", clarsimp)
   apply (clarsimp simp: pred_map_def vs_all_heap_simps)
   apply (rename_tac tcb' scp tcb sc n)
   apply (frule_tac pspace_relation_absD, erule state_relation_pspace_relation)
   apply (clarsimp simp: other_obj_relation_def)
   apply (subgoal_tac "z = KOTCB tcb'", clarsimp)
    apply (rule_tac x=tcb' in exI, simp)
    apply (prop_tac "tcbSchedContext tcb' = Some scp", clarsimp simp: tcb_relation_def, simp)
    apply (subgoal_tac "sc_at' scp s'", clarsimp)
     apply (frule_tac x=scp in pspace_relation_absD, erule state_relation_pspace_relation)
     apply (frule (1) valid_sched_context_size_objsI, clarsimp)
     apply (subgoal_tac "z = KOSchedContext ko", clarsimp)
      apply (frule (1) sc_ko_at_valid_objs_valid_sc', clarsimp)
      apply (clarsimp simp: valid_sched_context'_def sc_relation_def active_sc_def)
     apply (case_tac z; clarsimp simp: obj_at'_def projectKOs)
    apply (erule cross_relF [OF _ sc_at'_cross_rel], clarsimp simp: obj_at_def is_sc_obj)
    apply (erule (1) valid_sched_context_size_objsI)
   apply (case_tac z; clarsimp simp: obj_at'_def projectKOs)
  apply (subgoal_tac "tcb_at t s")
   apply (frule cross_relF [OF _ tcb_at'_cross_rel], clarsimp, assumption)
   apply (clarsimp simp: obj_at'_def projectKOs)
  apply (clarsimp simp: obj_at_def vs_all_heap_simps pred_map_def is_tcb)
  done

lemma setNextInterrupt_corres:
  "corres dc ((\<lambda>s. active_sc_tcb_at (cur_thread s) s)
              and (\<lambda>s. \<forall>t \<in> set (release_queue s). active_sc_tcb_at t s)
              and valid_objs and pspace_aligned and pspace_distinct)
             valid_objs'
             set_next_interrupt
             setNextInterrupt"
  unfolding setNextInterrupt_def set_next_interrupt_def
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split [OF getCurTime_corres])
      apply (rule corres_split [OF getCurThread_corres], simp)
        apply (rule corres_split_eqr[OF get_tcb_obj_ref_corres])
           apply (clarsimp simp: tcb_relation_def)
          apply (rule corres_assert_opt_assume_l)
          apply (rule corres_split [OF get_sc_corres])
            apply (rule_tac F="sc_valid_refills' rv'" in corres_gen_asm2)
            apply (rule corres_split [OF corres_if])
                 apply clarsimp
                apply (rule corres_split [OF getDomainTime_corres])
                  apply (simp only: fun_app_def)
                  apply (rule corres_return_eq_same)
                  apply (clarsimp simp: refill_hd_relation refill_map_def)
                 apply wpsimp
                apply wpsimp
               apply (rule corres_return_eq_same)
               apply (clarsimp simp: refill_hd_relation refill_map_def)
              apply (rule corres_split [OF getReleaseQueue_corres])
                apply (rule corres_split [OF corres_if], simp)
                    apply (rule corres_return_eq_same, simp)
                   apply (rule corres_split_eqr)
                      apply (simp, rule get_tcb_obj_ref_corres)
                      apply (clarsimp simp: tcb_relation_def)
                     apply (rule corres_assert_opt_assume_l)
                     apply simp
                     apply (rule corres_split [OF get_sc_corres])
                       apply (rule_tac F="sc_valid_refills' rv'c" in corres_gen_asm2)
                       apply (rule corres_return_eq_same)
                       apply (clarsimp simp: refill_hd_relation refill_map_def)
                      apply wpsimp
                     apply wpsimp
                    apply (wpsimp wp: get_tcb_obj_ref_wp)
                   apply (wpsimp wp: threadGet_wp)
                  apply (rule corres_machine_op)
                  apply (simp del: dc_simp, rule setDeadline_corres, simp)
                 apply wpsimp+
         apply (wpsimp wp: get_tcb_obj_ref_wp)
        apply (wpsimp wp: threadGet_wp)
       apply wpsimp+
   apply (fastforce intro!: valid_sched_context_size_objsI
                      dest: list.set_sel(1)
                      simp: vs_all_heap_simps obj_at_def is_tcb_def is_sc_obj_def)
  apply (clarsimp simp: valid_release_q_def)
  apply (subgoal_tac "(\<exists>tcb. ko_at' tcb (ksCurThread s') s' \<and>
                    sc_at' (the (tcbSchedContext tcb)) s' \<and>
                    (\<forall>ko. ko_at' ko (the (tcbSchedContext tcb)) s' \<longrightarrow> sc_valid_refills' ko)) \<and> (ksReleaseQueue s' \<noteq> [] \<longrightarrow> (\<exists>tcb. ko_at' tcb (hd (ksReleaseQueue s')) s' \<and>
                    sc_at' (the (tcbSchedContext tcb)) s' \<and>
                    (\<forall>ko. ko_at' ko (the (tcbSchedContext tcb)) s' \<longrightarrow> sc_valid_refills' ko)))")
   apply (safe, blast, blast)[1]
   apply (rule_tac x=tcb in exI, simp, safe, blast)[1]
   apply (prop_tac "ksCurThread s' = cur_thread s", clarsimp simp: state_relation_def, simp)
  apply (subgoal_tac "(ksReleaseQueue s') = release_queue s", simp)
   apply (intro conjI impI)
    apply (rule setNextInterrupt_corres_helper; simp)
   apply (clarsimp simp: state_relation_def release_queue_relation_def)
   apply (rule setNextInterrupt_corres_helper; simp?)
   apply (clarsimp simp: state_relation_def release_queue_relation_def)+
  done

(* refillUnblockCheck_corres *)

lemma isRoundRobin_corres:
  "corres (=) (sc_at sc_ptr) (sc_at' sc_ptr)
              (is_round_robin sc_ptr) (isRoundRobin sc_ptr)"
  apply (clarsimp simp: is_round_robin_def isRoundRobin_def)
  apply (corresKsimp corres: get_sc_corres
                      simp: sc_relation_def)
  done

lemma refillPopHead_corres:
  "corres (\<lambda>refill refill'. refill = refill_map refill')
     (pspace_aligned and pspace_distinct and sc_at sc_ptr
      and sc_refills_sc_at (\<lambda>refills. 1 < length refills) sc_ptr)
     (valid_refills' sc_ptr)
     (refill_pop_head sc_ptr) (refillPopHead sc_ptr)"
  (is "corres _ ?abs ?conc _ _")
  supply if_split[split del] opt_pred_def[simp add]
  apply (rule corres_cross[where Q' = "sc_at' sc_ptr", OF sc_at'_cross_rel], fastforce)
  apply (clarsimp simp: refill_pop_head_def refillPopHead_def)
  apply (clarsimp simp: getRefillNext_getSchedContext get_refills_def liftM_def)
  apply (rule corres_underlying_split[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (rule corres_guard_imp)
     apply (rule get_sc_corres)
    apply simp
   apply simp
  apply (rename_tac sc')
  apply (rule_tac F="refill_hd sc = refill_map (refillHd sc')" in corres_req)
   apply (clarsimp simp: obj_at_def is_sc_obj obj_at'_def projectKOs)
   apply (frule (1) pspace_relation_absD[OF _ state_relation_pspace_relation])
   apply (clarsimp elim!: refill_hd_relation simp: valid_refills'_def opt_map_red)
  apply (rule corres_guard_imp)
    apply (rule corres_underlying_split[OF updateSchedContext_corres_gen[where
                                    P="(\<lambda>s. ((\<lambda>sc. 1 < length (sc_refills sc)) |< scs_of2 s) sc_ptr)"
                                and P'="valid_refills' sc_ptr"]])
         apply (clarsimp, drule (2) state_relation_sc_relation)
         apply (clarsimp simp: sc_relation_def refills_map_def tl_map obj_at_simps is_sc_obj opt_map_red)
         apply (clarsimp simp: valid_refills'_def opt_map_red)
         apply (subst tl_wrap_slice; clarsimp simp: min_def split: if_split)
         apply (rule conjI impI; clarsimp simp: refillNextIndex_def wrap_slice_start_0 split: if_splits)
        apply (fastforce simp: obj_at_simps is_sc_obj opt_map_red dest!: state_relation_sc_replies_relation_sc)
        apply clarsimp
       apply (clarsimp simp: objBits_simps)
      apply simp
     apply (wpsimp wp: update_sched_context_wp)
    apply (wpsimp wp: updateSchedContext_wp)
   apply (clarsimp simp: sc_refills_sc_at_def obj_at_def opt_map_red)
  apply simp
  done

lemma refillPopHead_valid_refills'[wp]:
  "\<lbrace>\<lambda>s. valid_refills' scPtr' s
        \<and> (scPtr = scPtr' \<longrightarrow> obj_at' (\<lambda>sc'. Suc 0 < scRefillCount sc') scPtr s)\<rbrace>
   refillPopHead scPtr
   \<lbrace>\<lambda>_. valid_refills' scPtr'\<rbrace>"
  apply (clarsimp simp: refillPopHead_def updateSchedContext_def setSchedContext_def)
  apply (wpsimp wp: setObject_sc_wp)
  apply (fastforce simp: valid_refills'_def obj_at'_def projectKOs opt_map_def opt_pred_def
                         refillNextIndex_def)
  done

lemma refillHeadOverlapping_simp:
  "sc_at' sc_ptr s' \<Longrightarrow>
   refillHeadOverlapping sc_ptr s' =
    (scs_of' s' ||> (\<lambda>sc'. Suc 0 < scRefillCount sc'
                           \<and> rTime (scRefills sc' ! (if scRefillHead sc' = scRefillMax sc' - Suc 0
                                                     then 0 else Suc (scRefillHead sc')))
                                \<le> rTime (refillHd sc') + rAmount (refillHd sc'))) sc_ptr"
  unfolding refillHeadOverlapping_def
  apply (frule no_ofailD[OF no_ofail_readSchedContext])
  apply (fastforce simp: obind_def omonad_defs oliftM_def obj_at'_def projectKOs readRefillNext_def
                         readRefillSize_def refillIndex_def opt_map_red readSchedContext_def
                  dest!: readObject_ko_at'_sc split: option.splits)
  done

lemma refill_head_overlapping_simp:
  "sc_at sc_ptr s \<Longrightarrow>
   refill_head_overlapping sc_ptr s =
     (scs_of2 s ||> (\<lambda>sc. Suc 0 < length (sc_refills sc)
                         \<and> r_time (hd (tl (sc_refills sc)))
                                   \<le> r_time (refill_hd sc) + r_amount (refill_hd sc))) sc_ptr"
  unfolding refill_head_overlapping_def
  apply (insert no_ofailD[OF no_ofail_read_sched_context])
  apply (clarsimp simp: obind_def obj_at_def is_sc_obj opt_map_red
                 split: option.split)
  apply (drule_tac x=s and y=sc_ptr in meta_spec2)
  apply (clarsimp dest!: read_sched_context_SomeD)
  done

lemma refillHeadOverlapping_corres_eq:
  "\<lbrakk>(s, s') \<in> state_relation; sc_at sc_ptr s; sc_at' sc_ptr s'; valid_refills' sc_ptr s'\<rbrakk>
   \<Longrightarrow> refill_head_overlapping sc_ptr s = refillHeadOverlapping sc_ptr s'"
  apply (frule no_ofailD[OF no_ofail_refillHeadOverlapping])
  apply (insert refillHeadOverlapping_implies_count_greater_than_one[of sc_ptr s'])
  apply clarsimp
  apply (drule (2) state_relation_sc_relation)
  apply (clarsimp simp: obj_at_simps is_sc_obj)
  apply (rename_tac b n sc sc')
  apply (case_tac b;
         clarsimp simp: refillHeadOverlapping_simp refill_head_overlapping_simp obj_at_simps
                        is_sc_obj sc_relation_def valid_refills'_def refillHd_def
                        neq_Nil_lengthI tl_drop_1 hd_drop_conv_nth refills_map_def hd_map
                        hd_wrap_slice wrap_slice_index refill_map_def opt_map_red opt_pred_def
                 split: if_split_asm)
  by linarith+

lemma refillPopHead_scs_of'[wp]:
  "\<lbrace>\<lambda>s'. P ((scs_of' s')(scp \<mapsto> (\<lambda>sc'. scRefillCount_update (\<lambda>_. scRefillCount sc' - Suc 0)
                                      (scRefillHead_update
                                          (\<lambda>_. refillNextIndex (scRefillHead sc') sc') sc'))
                                        (the (scs_of' s' scp))))\<rbrace>
  refillPopHead scp
  \<lbrace>\<lambda>_ s'. P (scs_of' s')\<rbrace>"
  unfolding refillPopHead_def
  by (wpsimp wp: updateSchedContext_wp)

crunch update_refill_hd, refill_pop_head, merge_refills, schedule_used, handle_overrun_loop_body
  for is_active_sc2[wp]: "is_active_sc2 scp"
  (wp: crunch_wps ignore: update_sched_context
   simp: crunch_simps update_refill_hd_rewrite update_sched_context_set_refills_rewrite)

lemma merge_refills_scs_of2[wp]:
  "\<lbrace>\<lambda>s. P ((scs_of2 s)(scp \<mapsto> (\<lambda>sc. sc_refills_update
            (\<lambda>_. merge_refill (refill_hd sc) (hd (tl (sc_refills sc))) # tl (tl (sc_refills sc))) sc)
                          (the (scs_of2 s scp)))) \<rbrace>
   merge_refills scp
   \<lbrace>\<lambda>_ s. P (scs_of2 s)\<rbrace>"
  unfolding merge_refills_def
  apply (wpsimp simp: update_refill_hd_rewrite refill_pop_head_def
                  wp: get_refills_wp set_refills_wp update_sched_context_wp)
  by (clarsimp simp: is_active_sc2_def obj_at_def opt_map_red)

(* if the loop guard is true, the refill length is greater than one *)
lemma mergeRefills_corres:
  "corres dc (sc_at sc_ptr and pspace_aligned and pspace_distinct
              and (\<lambda>s. ((\<lambda>sc. 1 < length (sc_refills sc)) |< scs_of2 s) sc_ptr))
             (valid_refills' sc_ptr)
             (merge_refills sc_ptr) (mergeRefills sc_ptr)"
  unfolding mergeRefills_def merge_refills_def merge_refill_def
  apply (rule corres_cross[where Q' = "sc_at' sc_ptr", OF sc_at'_cross_rel], fastforce)
  apply (rule_tac Q="\<lambda>s'. ((\<lambda>sc'. 1 < scRefillCount sc') |< scs_of' s') sc_ptr" in corres_cross_add_guard)
   apply clarsimp
   apply (drule (2) state_relation_sc_relation)
   apply (clarsimp simp: sc_relation_def)
   apply (clarsimp simp: valid_refills'_def obj_at_simps is_sc_obj opt_map_red opt_pred_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF refillPopHead_corres])
      apply (rule updateRefillHd_corres, simp)
       apply (clarsimp simp: refill_map_def merge_refill_def)+
     apply (rule hoare_strengthen_post[where Q="\<lambda>_. sc_at sc_ptr", rotated])
      apply (simp add: active_sc_at_equiv is_active_sc_rewrite[symmetric])
     apply (wpsimp wp: refill_pop_head_sc_active)
    apply wpsimp
   apply (clarsimp simp: obj_at_def is_sc_obj opt_map_red is_active_sc_rewrite active_sc_at_equiv
                         sc_refills_sc_at_rewrite)
  apply (fastforce simp: valid_refills'_def obj_at_simps opt_map_red opt_pred_def refillNextIndex_def)
  done

lemma mergeRefills_valid_refills'[wp]:
  "\<lbrace>(\<lambda>s. ((\<lambda>sc. 1 < scRefillCount sc) |< scs_of' s) scp) and valid_refills' scp\<rbrace>
   mergeRefills p
   \<lbrace>\<lambda>_. valid_refills' scp\<rbrace>"
  unfolding mergeRefills_def
  apply (wpsimp simp: updateRefillHd_def refillPopHead_def wp: updateSchedContext_wp)
  by (fastforce simp: valid_refills'_def obj_at_simps refillNextIndex_def opt_map_red opt_pred_def)

lemma no_fail_refillPopHead[wp]:
  "no_fail (sc_at' scPtr) (refillPopHead scPtr)"
  by (wpsimp simp: refillPopHead_def obj_at'_def opt_map_def opt_pred_def objBits_simps projectKOs)

crunch mergeRefills
  for (no_fail) no_fail[wp]
  (simp: opt_map_red opt_pred_def obj_at_simps)

lemma refillPopHead_length_decreasing:
  "\<lbrace>\<lambda>s'. ((\<lambda>sc. 0 < scRefillCount sc) |< scs_of' s') scp \<and> s' = s\<rbrace>
   refillPopHead scp
   \<lbrace>\<lambda>r' s'. scRefillCount (the (scs_of' s' scp)) < scRefillCount (the (scs_of' s scp))\<rbrace>"
  unfolding refillPopHead_def
  apply (simp add: liftM_def bind_assoc refillHd_def)
  apply (wpsimp wp: updateSchedContext_wp)
  by (clarsimp simp: obj_at'_def projectKOs opt_map_red opt_pred_def)

lemma mergeRefills_length_decreasing:
  "\<lbrace>\<lambda>s'. ((\<lambda>sc. 0 < scRefillCount sc) |< scs_of' s') scp \<and> s' = s\<rbrace>
   mergeRefills scp
   \<lbrace>\<lambda>r' s'. scRefillCount (the (scs_of' s' scp)) < scRefillCount (the (scs_of' s scp))\<rbrace>"
  unfolding mergeRefills_def updateRefillHd_def
  apply (rule bind_wp[OF _ refillPopHead_length_decreasing])
  by (wpsimp wp: refillPopHead_length_decreasing updateSchedContext_wp)

lemma scRefillCount_wf:
  "wf {((r', s'), r, s).
        scRefillCount (the (scs_of' s' sc_ptr))
         < scRefillCount (the (scs_of' s sc_ptr))}"
  apply (prop_tac "{((r', s'), r, s). scRefillCount (the (scs_of' s' sc_ptr))
                                             < scRefillCount (the (scs_of' s sc_ptr))}
                     = measure (\<lambda>(r, s). scRefillCount (the (scs_of' s sc_ptr)))")
   apply (clarsimp simp: measure_def inv_image_def split_def)
  apply (drule sym)
  apply (erule subst)
  apply (rule wf_measure)
  done

lemma mergeRefills_terminates:
  "sc_at' sc_ptr s' \<Longrightarrow>
   whileLoop_terminates
               (\<lambda>_ s'. the (refillHeadOverlapping sc_ptr s'))
               (\<lambda>_. mergeRefills sc_ptr) r' s'"
  apply (rule_tac
           I="\<lambda>_. sc_at' sc_ptr" and
           R="{((r', s'), (r, s)). scRefillCount (the (scs_of' s' sc_ptr))
                                    < scRefillCount (the (scs_of' s sc_ptr))}"
         in whileLoop_terminates_inv)
    apply simp
   apply (wpsimp wp: mergeRefills_length_decreasing)
   apply (fastforce simp: obj_at_simps opt_map_red opt_pred_def
                   dest!: refillHeadOverlapping_implies_count_greater_than_one)
  apply (rule scRefillCount_wf)
  done

lemma refillHeadOverlappingLoop_corres:
  "corres dc (sc_at sc_ptr and  pspace_aligned and pspace_distinct)
             (valid_refills' sc_ptr)
             (refill_head_overlapping_loop sc_ptr) (refillHeadOverlappingLoop sc_ptr)"
  unfolding refill_head_overlapping_loop_def refillHeadOverlappingLoop_def runReaderT_def
  supply refillHeadOverlapping_implies_count_greater_than_one[dest!]
  apply (rule corres_cross[where Q' = "sc_at' sc_ptr", OF sc_at'_cross_rel], fastforce)
  apply (rule corres_whileLoop)
        apply (drule refillHeadOverlapping_corres_eq[where sc_ptr=sc_ptr]; simp add: runReaderT_def)
       apply simp
       apply (rule corres_guard_imp
                      [where P=P and Q=P for P,
                       where
                          P'= Q and
                          Q'="Q and (\<lambda>s. ((\<lambda>sc. 1 < scRefillCount sc) |< scs_of' s) sc_ptr)" for Q])
         apply (rule corres_cross_add_abs_guard
                       [where Q="(\<lambda>s. ((\<lambda>sc. 1 < length (sc_refills sc)) |< scs_of2 s) sc_ptr)"])
          apply clarsimp
          apply (drule (2) state_relation_sc_relation)
          apply (clarsimp simp: obj_at_simps is_sc_obj valid_refills'_def sc_relation_def
                                opt_map_red opt_pred_def)
         apply (rule corres_guard_imp)
           apply (rule mergeRefills_corres)
          apply clarsimp+
      apply (wpsimp+)[4]
  apply (fastforce intro!: mergeRefills_terminates)
  done

lemma refillUnblockCheck_corres:
  "corres dc
     (sc_at scp and pspace_aligned and pspace_distinct
      and (\<lambda>s. ((\<lambda>sc. 0 < length (sc_refills sc)) |< scs_of2 s) scp))
     (valid_refills' scp)
     (refill_unblock_check scp) (refillUnblockCheck scp)"
  unfolding refill_unblock_check_def refillUnblockCheck_def
  apply (rule corres_cross[where Q' = "sc_at' scp", OF sc_at'_cross_rel], fastforce)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF isRoundRobin_corres])
      apply (rule corres_split_eqr[OF refillReady_corres])
        apply simp
        apply (rule corres_when, fastforce)
        apply (rule corres_split[OF setReprogramTimer_corres])
          apply (rule corres_split[OF getCurTime_corres])
            apply (rule corres_split[OF updateRefillHd_corres], simp)
               apply (clarsimp simp: refill_map_def kernelWCETTicks_def)
              apply (rule refillHeadOverlappingLoop_corres)
             apply wpsimp
            apply (wpsimp wp: getCurTime_wp updateSchedContext_wp
                        simp: updateRefillHd_def)+
        apply (wpsimp wp: refillReady_wp is_round_robin_wp isRoundRobin_wp
                    simp: setReprogramTimer_def)+
      apply (clarsimp simp: obj_at_simps valid_refills'_def opt_map_red opt_pred_def)
  done

lemma sporadic_implies_active_cross:
  "\<lbrakk>(s, s') \<in> state_relation; active_scs_valid s; sc_at scPtr s; ko_at' sc scPtr s';
    scSporadic sc\<rbrakk>
   \<Longrightarrow> is_active_sc' scPtr s'"
  apply (frule (1) state_relation_sc_relation[where ptr=scPtr])
   apply fastforce
  apply (clarsimp simp: active_scs_valid_def)
  apply (drule_tac x=scPtr in spec)+
  by (fastforce dest: is_sc_objD
                simp: sc_relation_def vs_all_heap_simps active_sc_def is_active_sc'_def
                      obj_at_simps opt_map_def opt_pred_def)

lemma ifCondRefillUnblockCheck_corres:
  "corres dc
     (\<lambda>s. case_option True
                      (\<lambda>scp. sc_at scp s \<and> active_scs_valid s
                           \<and> pspace_aligned s \<and> pspace_distinct s
                           \<and> (((\<lambda>sc. case_option (sc_active sc) \<top> act) |< scs_of2 s) scp)) scp_opt)
     (\<lambda>s. case_option True (\<lambda>scp. case_option (valid_refills' scp s) (\<lambda>_. valid_objs' s) act) scp_opt)
        (if_cond_refill_unblock_check scp_opt act ast) (ifCondRefillUnblockCheck scp_opt act ast)"
  unfolding if_cond_refill_unblock_check_def ifCondRefillUnblockCheck_def
  apply (cases scp_opt; simp add: maybeM_def)
  apply (rename_tac scp)
  apply (rule corres_cross[OF sc_at'_cross_rel], fastforce)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF get_sc_corres _ get_sched_context_wp getSchedContext_wp])
    apply (rule corres_split[OF getCurSc_corres])
      apply (rule corres_when)
       apply (clarsimp simp: active_sc_def sc_relation_def case_bool_if option.case_eq_if)
      apply (rule corres_when)
       apply fastforce
      apply (rule refillUnblockCheck_corres)
     apply wpsimp+
   apply (prop_tac "is_active_sc scp s")
    apply (cases act; clarsimp)
     apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps opt_map_def opt_pred_def)
    apply (clarsimp simp: vs_all_heap_simps active_scs_valid_def obj_at_kh_kheap_simps
                   split: bool.splits)
    apply (drule_tac x=scp in spec)+
    apply force
   apply (drule_tac scp=scp in active_scs_validE[rotated, simplified is_active_sc_rewrite];
          clarsimp simp: opt_map_red obj_at_def is_active_sc2_def vs_all_heap_simps
                         valid_refills_def rr_valid_refills_def active_sc_def opt_pred_def
                  split: if_split_asm)
  apply (clarsimp simp: case_bool_if option.case_eq_if split: if_split_asm)
  apply (fastforce elim!: valid_objs'_valid_refills'
                   dest!: sporadic_implies_active_cross)
  done

lemma getCurTime_sp:
  "\<lbrace>P\<rbrace> getCurTime \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksCurTime s)\<rbrace>"
  by (wpsimp simp: getCurTime_def)

lemma ovalid_readRefillReady'[rule_format, simp]:
  "ovalid (\<lambda>s. sc_at' scp s \<longrightarrow> P (((\<lambda>sc'. rTime (refillHd sc') \<le> ksCurTime s + kernelWCETTicks) |< scs_of' s) scp) s)
              (readRefillReady scp) P"
  unfolding readRefillReady_def readSchedContext_def ovalid_def
  by (fastforce simp: obind_def opt_map_red obj_at'_def projectKOs opt_pred_def
                dest: use_ovalid[OF ovalid_readCurTime]
               dest!: readObject_misc_ko_at'
               split: option.split_asm)+

lemma refillReady_wp':
  "\<lbrace>\<lambda>s. sc_at' scp s \<longrightarrow>
        P (((\<lambda>sc'. rTime (refillHd sc') \<le> ksCurTime s + kernelWCETTicks) |< scs_of' s) scp) s\<rbrace>
   refillReady scp
   \<lbrace>P\<rbrace>"
  unfolding refillReady_def
  by wpsimp (drule use_ovalid[OF ovalid_readRefillReady'])

lemma refillAddTail_corres:
  "new = refill_map new'
   \<Longrightarrow> corres dc (sc_at sc_ptr)
                 (sc_at' sc_ptr and
                  (\<lambda>s'. ((\<lambda>sc'. scRefillCount sc' < scRefillMax sc' \<and> sc_valid_refills' sc') |< scs_of' s') sc_ptr))
                 (refill_add_tail sc_ptr new)
                 (refillAddTail sc_ptr new')"
  supply projection_rewrites[simp] opt_pred_def[simp add]
  apply (clarsimp simp: refill_add_tail_def refillAddTail_def getRefillNext_getSchedContext
                        getRefillSize_def2 liftM_def get_refills_def)
  apply (rule corres_symb_exec_r[OF _ get_sc_sp', rotated]; (solves wpsimp)?)+
  apply (rename_tac sc')
  apply (rule corres_guard_imp)
    apply (rule corres_assert_assume_r)
    apply (rule updateSchedContext_corres_gen[where P=\<top>
                and P'="(\<lambda>s'. ((\<lambda>sc'. scRefillCount sc' < scRefillMax sc' \<and> sc_valid_refills' sc') |< scs_of' s') sc_ptr)"])
      apply (clarsimp, drule (2) state_relation_sc_relation)
      apply (clarsimp simp: obj_at_simps is_sc_obj)
      apply (rename_tac sc')
      apply (clarsimp simp: sc_relation_def neq_Nil_lengthI opt_map_red)
      apply (prop_tac "scRefills sc' \<noteq> []")
       apply (clarsimp simp: neq_Nil_lengthI)
      apply (clarsimp simp: refills_map_def)
      apply (subst wrap_slice_append; simp)
      apply (insert less_linear)[1]
      apply (drule_tac x="scRefillMax sc'" and y="scRefillHead sc' + scRefillCount sc' + Suc 0" in meta_spec2)
      apply (erule disjE)
       apply (simp add: refillNextIndex_def refillTailIndex_def Let_def)
       apply (intro conjI impI;
              clarsimp simp: Suc_diff_Suc wrap_slice_updateAt_eq[symmetric] neq_Nil_lengthI
                             nat_le_Suc_less refill_map_def updateAt_index)
      apply (erule disjE)
       apply clarsimp
       apply (rule conjI)
        apply (simp add: refillNextIndex_def refillTailIndex_def Let_def)
        apply (clarsimp simp: wrap_slice_updateAt_eq not_le)
        apply (metis add_leE le_SucI le_refl lessI mult_is_add.mult_commute not_add_less2 not_less_eq wrap_slice_updateAt_eq)
       apply (clarsimp simp: refillNextIndex_def refillTailIndex_def Let_def not_le)
       apply (clarsimp simp: updateAt_index refill_map_def)
      apply clarsimp
      apply (rule conjI)
       apply (clarsimp simp: refillNextIndex_def refillTailIndex_def Let_def)
       apply (intro conjI impI; (clarsimp simp: not_le wrap_slice_updateAt_eq)?)
       apply (metis add_leE le_refl le_simps(1) less_SucI mult_is_add.mult_commute nat_neq_iff
                    not_less_eq trans_less_add2 wrap_slice_updateAt_eq)
      apply (clarsimp simp: refillNextIndex_def refillTailIndex_def Let_def not_le)
      apply (clarsimp simp: updateAt_index refill_map_def)
     apply (fastforce simp: obj_at_simps is_sc_obj opt_map_red
                     dest!: state_relation_sc_replies_relation_sc)
    apply (clarsimp simp: objBits_simps)
   apply (clarsimp simp: obj_at_def is_sc_obj)
  apply (clarsimp simp: obj_at'_def projectKOs opt_map_red)
  done

lemma isRoundRobin_sp:
  "\<lbrace>P\<rbrace>
   isRoundRobin scPtr
   \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. ko_at' sc scPtr s \<and> rv = (scPeriod sc = 0))\<rbrace>"
  apply (simp add: isRoundRobin_def)
  apply (rule bind_wp_fwd)
   apply (rule get_sc_sp')
  apply (wp hoare_return_sp)
  apply (clarsimp simp: obj_at'_def projectKOs)
  done

lemma maybeAddEmptyTail_corres:
  "corres dc
          (is_active_sc2 sc_ptr)
                 (sc_at' sc_ptr and
                  (\<lambda>s'. ((\<lambda>sc'. scRefillCount sc' < scRefillMax sc' \<and> sc_valid_refills' sc') |< scs_of' s') sc_ptr))
          (maybe_add_empty_tail sc_ptr)
          (maybeAddEmptyTail sc_ptr)" (is "corres _ ?abs ?conc _ _")
  supply projection_rewrites[simp]
  apply (rule corres_cross_add_abs_guard[where Q="sc_at sc_ptr"])
   apply (fastforce dest!: sc_at'_cross[OF state_relation_pspace_relation])
  apply (clarsimp simp: maybe_add_empty_tail_def maybeAddEmptyTail_def get_refills_def)
  apply (rule corres_underlying_split[rotated 2, OF is_round_robin_sp isRoundRobin_sp])
   apply (corresKsimp corres: isRoundRobin_corres)
  apply (clarsimp simp: obj_at_def is_sc_obj)
  apply (clarsimp simp: when_def)
  apply (rule corres_underlying_split[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corresKsimp corres: get_sc_corres)
   apply (fastforce intro: valid_objs_valid_sched_context_size
                     simp: obj_at_def is_sc_obj_def)
  apply (rename_tac sc')
  apply (corresKsimp corres: refillAddTail_corres)
  apply (frule refill_hd_relation; clarsimp simp: obj_at'_def projectKOs opt_map_red opt_pred_def)
  apply (fastforce dest: valid_objs_valid_sched_context_size
                   simp: obj_at_def is_sc_obj_def refill_map_def)
  done

lemma getRefills_sp:
  "\<lbrace>P\<rbrace>
   getRefills scPtr
   \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. ko_at' sc scPtr s \<and> (rv = scRefills sc))\<rbrace>"
  apply (simp add: getRefills_def)
  apply (rule bind_wp_fwd)
   apply (rule get_sc_sp')
  apply (wp hoare_return_sp)
  apply (clarsimp simp: obj_at'_def projectKOs)
  done

lemma getCurSc_sp:
  "\<lbrace>P\<rbrace>
   getCurSc
   \<lbrace>\<lambda>rv s. P s \<and> rv = ksCurSc s\<rbrace>"
  apply (simp add: getCurSc_def)
  apply (wpsimp wp: hoare_return_sp)
  done

lemma refillBudgetCheckRoundRobin_corres:
  "corres dc
          (cur_sc_active and (\<lambda>s. sc_at (cur_sc s) s))
          ((\<lambda>s'. valid_refills' (ksCurSc s') s') and (\<lambda>s'. sc_at' (ksCurSc s') s'))
          (refill_budget_check_round_robin usage) (refillBudgetCheckRoundRobin usage)"
  supply projection_rewrites[simp]
  apply (subst is_active_sc_rewrite)
  apply (clarsimp simp: refill_budget_check_round_robin_def refillBudgetCheckRoundRobin_def)
  apply (rule corres_underlying_split[rotated 2, OF gets_sp getCurSc_sp])
   apply (corresKsimp corres: getCurSc_corres)
  apply (rule_tac Q="\<lambda>s. is_active_sc' (ksCurSc s) s" in corres_cross_add_guard)
   apply (rule_tac ptr="ksCurSc s'" in is_active_sc'_cross[OF state_relation_pspace_relation]; simp)
   apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF updateRefillHd_corres], simp)
       apply (clarsimp simp: refill_map_def)
      apply (rule updateRefillTl_corres, simp)
      apply (clarsimp simp: refill_map_def)
     apply (wpsimp simp: update_refill_hd_rewrite wp: set_refills_wp get_refills_wp)
    apply (wpsimp wp: hoare_vcg_conj_lift)
     apply (wpsimp simp: updateRefillHd_def wp: updateSchedContext_wp)
    apply (wpsimp wp: updateRefillHd_valid_objs')
   apply (clarsimp simp: obj_at_def is_active_sc2_def is_sc_obj opt_map_red
                  split: option.split_asm Structures_A.kernel_object.split_asm)
  apply (clarsimp simp: obj_at_simps fun_upd_def[symmetric] scBits_simps ps_clear_upd)
  apply (clarsimp simp: is_active_sc'_def valid_obj'_def valid_sched_context'_def valid_refills'_def
                        opt_pred_def
                 split: option.split_asm)
  done

lemma head_insufficient_length_greater_than_one:
  "\<lbrakk>the (head_insufficient sc_ptr s);
    pred_map (\<lambda>cfg. unat MIN_BUDGET \<le> refills_unat_sum (scrc_refills cfg)) (sc_refill_cfgs_of s) sc_ptr\<rbrakk>
   \<Longrightarrow> pred_map (\<lambda>cfg. Suc 0 < length (scrc_refills cfg)) (sc_refill_cfgs_of s) sc_ptr"
  apply (frule head_insufficient_true_imp_insufficient)
   apply (clarsimp simp: vs_all_heap_simps)
  apply (clarsimp simp: vs_all_heap_simps sc_at_ppred_def refills_unat_sum_def word_less_nat_alt)
  apply (case_tac "sc_refills y"; fastforce dest!: member_le_sum_list)
  done

lemma length_sc_refills_cross:
  "\<lbrakk>(s, s') \<in> state_relation; sc_at scp s; sc_at' scp s'; valid_refills' scp s'\<rbrakk>
   \<Longrightarrow> ((\<lambda>sc. P (length (sc_refills sc))) |< scs_of2 s) scp
        = ((\<lambda>sc'. P (scRefillCount sc')) |< scs_of' s') scp"
  apply (drule (2) state_relation_sc_relation)
  apply (clarsimp simp: obj_at_simps is_sc_obj valid_refills'_def sc_relation_def opt_map_red
                        opt_pred_def)
  done

lemma update_refill_hd_comp:
  "update_refill_hd scPtr (f \<circ> g)
   = do update_refill_hd scPtr g;
        update_refill_hd scPtr f
     od"
  apply (clarsimp simp: update_refill_hd_def)
  apply (rule box_equals[OF update_sched_context_decompose]; fastforce)
  done

lemma updateRefillHd_valid_refills'[wp]:
  "updateRefillHd scPtr f \<lbrace>valid_refills' scPtr'\<rbrace>"
  apply (clarsimp simp: updateRefillHd_def updateSchedContext_def setSchedContext_def)
  apply (wpsimp wp: setObject_sc_wp)
  apply (clarsimp simp: valid_refills'_def obj_at'_def projectKOs opt_map_def opt_pred_def)
  done

lemma updateRefillTl_valid_refills'[wp]:
  "updateRefillTl scPtr f \<lbrace>valid_refills' scPtr'\<rbrace>"
  apply (clarsimp simp: updateRefillTl_def updateSchedContext_def setSchedContext_def)
  apply (wpsimp wp: setObject_sc_wp)
  apply (clarsimp simp: valid_refills'_def obj_at'_def projectKOs opt_map_def opt_pred_def)
  done

lemma refill_pop_head_is_active_sc[wp]:
  "refill_pop_head sc_ptr \<lbrace>is_active_sc sc_ptr'\<rbrace>"
  apply (wpsimp simp: refill_pop_head_def wp: update_sched_context_wp)
  apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps active_sc_def)
  done

lemma setSchedContext_is_active_sc_at':
  "\<lbrace>is_active_sc' scPtr' and K (scPtr' = scPtr \<longrightarrow> 0 < scRefillMax sc)\<rbrace>
   setSchedContext scPtr sc
   \<lbrace>\<lambda>_ s. is_active_sc' scPtr' s\<rbrace>"
  apply (wpsimp wp: set_sc'.set_wp opt_map_red
              simp: StateRelation.is_active_sc'_def opt_pred_def split: if_splits)
  done

lemma updateSchedContext_is_active_sc_at':
  "\<lbrace>is_active_sc' scPtr'
    and (\<lambda>s. scPtr = scPtr' \<longrightarrow> (\<forall>ko. ko_at' ko scPtr s \<longrightarrow> 0 < scRefillMax ko \<longrightarrow> 0 < scRefillMax (f ko)))\<rbrace>
   updateSchedContext scPtr f
   \<lbrace>\<lambda>_. is_active_sc' scPtr'\<rbrace>"
  apply (simp add: updateSchedContext_def)
  apply (wpsimp wp: setSchedContext_is_active_sc_at')
  apply (clarsimp simp: is_active_sc'_def obj_at'_def projectKOs opt_map_red opt_pred_def)
  done

lemma refillPopHead_is_active_sc_at'[wp]:
  "refillPopHead scPtr \<lbrace>is_active_sc' scPtr'\<rbrace>"
  apply (simp add: refillPopHead_def)
  apply (wpsimp wp: updateSchedContext_is_active_sc_at' getRefillNext_wp)
  done

lemma nonOverlappingMergeRefills_corres:
  "sc_ptr = scPtr \<Longrightarrow>
    corres dc (pspace_aligned and pspace_distinct and sc_at sc_ptr and is_active_sc sc_ptr
                and valid_objs
                and (\<lambda>s. pred_map (\<lambda>cfg. Suc 0 < length (scrc_refills cfg)) (sc_refill_cfgs_of s) sc_ptr))
              (valid_refills' sc_ptr)
    (non_overlapping_merge_refills sc_ptr)
    (nonOverlappingMergeRefills scPtr)"
  apply (clarsimp simp: non_overlapping_merge_refills_def nonOverlappingMergeRefills_def)
  apply (rule corres_cross[OF sc_at'_cross_rel[where t=scPtr]], simp)
  apply (rule corres_symb_exec_r[OF _ get_sc_sp', rotated]; (solves wpsimp)?)
  apply (rule_tac Q="is_active_sc' scPtr" in corres_cross_add_guard)
   apply (fastforce dest: is_active_sc'2_cross)
  apply (rule_tac Q="obj_at' (\<lambda>sc'. Suc 0 < scRefillCount sc') scPtr"
               in corres_cross_add_guard)
   apply (fastforce dest!: length_sc_refills_cross[where P="\<lambda>l. Suc 0 < l"]
                     simp: opt_map_red opt_pred_def vs_all_heap_simps obj_at'_def projectKOs)
  apply (rule corres_symb_exec_r[OF _ assert_sp, rotated])
    apply wpsimp
   apply (rule no_fail_pre)
    apply (rule no_fail_assert)
   apply (clarsimp simp: no_fail_def obj_at'_def projectKOs)

  apply (rule_tac Q="\<lambda>_. sc_at sc_ptr and is_active_sc sc_ptr"
              and Q'="\<lambda>_. valid_refills' scPtr and sc_at' scPtr"
               in corres_underlying_split
         ; (solves wpsimp)?)
   apply (corresKsimp corres: refillPopHead_corres
                       simp: obj_at_def vs_all_heap_simps pred_map_simps sc_at_ppred_def)
  apply (subst update_refill_hd_comp)
  apply (rule corres_guard_imp)
     apply (rule corres_underlying_split[OF updateRefillHd_corres])
         apply blast
        apply (clarsimp simp: refill_map_def)
       apply (fastforce intro: updateRefillHd_corres
                         simp: refill_map_def)
      apply (wpsimp simp: update_refill_hd_def wp: update_sched_context_wp)
      apply (clarsimp simp: vs_all_heap_simps active_sc_def is_active_sc2_def obj_at_def opt_map_def)
     apply (wpsimp simp: updateRefillHd_def simp: objBits_simps)
    apply (simp add: is_active_sc_rewrite[symmetric])
   apply blast
  done

lemma head_insufficient_simp:
  "sc_at scp s
   \<Longrightarrow> head_insufficient scp s = Some (sc_at_pred (\<lambda>sc. r_amount (refill_hd sc) < MIN_BUDGET) scp s)"
  unfolding head_insufficient_def
  by (clarsimp simp: obind_def read_sched_context_def obj_at_def is_sc_obj sc_at_pred_n_def)

lemma refillHdInsufficient_simp:
  "sc_at' scp s
   \<Longrightarrow> refillHdInsufficient scp s
       = Some (obj_at' (\<lambda>sc :: sched_context. rAmount (refillHd sc) < minBudget) scp s)"
  unfolding refillHdInsufficient_def
  apply (clarsimp simp: obind_def readSchedContext_def split: option.splits)
  apply (frule no_ofailD[OF no_ofail_sc_at'_readObject])
  apply (clarsimp simp: obj_at'_def dest!: readObject_misc_ko_at')
  done

lemma head_insufficient_equiv:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s; valid_objs s;
    pred_map (\<lambda>cfg. scrc_refills cfg \<noteq> []) (sc_refill_cfgs_of s) scPtr; valid_refills' scPtr s'\<rbrakk>
   \<Longrightarrow> head_insufficient scPtr s = refillHdInsufficient scPtr s'"
  apply (prop_tac "sc_at scPtr s")
   apply (fastforce dest: valid_objs_valid_sched_context_size
                    simp: vs_all_heap_simps obj_at_kh_kheap_simps is_sc_obj_def)
  apply (frule state_relation_pspace_relation)
  apply (frule sc_at_cross; simp?)
  apply (frule state_relation_sc_relation; simp?)
  apply (subst head_insufficient_simp; simp?)
  apply (subst refillHdInsufficient_simp; simp)
  apply (frule refill_hd_relation)
   apply (fastforce simp: vs_all_heap_simps valid_refills'_def opt_map_def opt_pred_def obj_at_simps)
  apply (clarsimp simp: obj_at_def sc_at_ppred_def obj_at'_def projectKOs minBudget_def refill_map_def
                        MIN_BUDGET_def kernelWCETTicks_def opt_map_def vs_all_heap_simps)
  done

lemma refill_pop_head_no_fail:
  "no_fail (\<lambda>s. (\<exists>sc n. kheap s sc_ptr = Some (Structures_A.SchedContext sc n))
                \<and> pred_map (\<lambda>cfg. scrc_refills cfg \<noteq> []) (sc_refill_cfgs_of s) sc_ptr)
           (refill_pop_head sc_ptr)"
  apply (wpsimp simp: refill_pop_head_def get_refills_def get_sched_context_def
                  wp: get_object_wp update_sched_context_no_fail)
  apply (clarsimp simp: obj_at_def a_type_def vs_all_heap_simps is_sc_obj_def)
  done

lemma refill_pop_head_sched_context_at[wp]:
  "refill_pop_head sc_ptr' \<lbrace>\<lambda>s. \<exists>sc n. kheap s sc_ptr = Some (Structures_A.SchedContext sc n)\<rbrace>"
  apply (clarsimp simp: refill_pop_head_def)
  apply (wpsimp wp: update_sched_context_wp)
  done

lemma non_overlapping_merge_refills_no_fail:
  "no_fail (\<lambda>s. (\<exists>sc n. kheap s sc_ptr = Some (Structures_A.SchedContext sc n))
                \<and> pred_map (\<lambda>cfg. scrc_refills cfg \<noteq> []) (sc_refill_cfgs_of s) sc_ptr)
           (non_overlapping_merge_refills sc_ptr)"
  apply (wpsimp wp: refill_pop_head_no_fail
              simp: non_overlapping_merge_refills_def update_refill_hd_def)
  done

lemma non_overlapping_merge_refills_is_active_sc[wp]:
  "non_overlapping_merge_refills sc_ptr \<lbrace>is_active_sc sc_ptr'\<rbrace>"
  apply (clarsimp simp: non_overlapping_merge_refills_def update_refill_hd_def)
  apply (rule bind_wp_fwd_skip, solves wpsimp)
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: vs_all_heap_simps obj_at_def)
  done

crunch non_overlapping_merge_refills
  for valid_objs[wp]: valid_objs

lemma nonOverLappingMergeRefills_valid_refills'[wp]:
  "nonOverlappingMergeRefills scPtr \<lbrace>valid_refills' scPtr\<rbrace>"
  apply (wpsimp simp: nonOverlappingMergeRefills_def)
  apply (clarsimp simp: obj_at'_def)
  done

definition head_insufficient_loop_measure where
  "head_insufficient_loop_measure sc_ptr
     \<equiv> measure (\<lambda>(_, s). case kheap s sc_ptr of Some (Structures_A.SchedContext sc _)
                                             \<Rightarrow> (length (sc_refills sc)))"

lemma non_overlapping_merge_refills_terminates:
  "\<lbrakk>pred_map (\<lambda>cfg. refills_unat_sum (scrc_refills cfg) \<le> unat max_time)
             (sc_refill_cfgs_of s) sc_ptr;
    pred_map (\<lambda>cfg. unat MIN_BUDGET \<le> refills_unat_sum (scrc_refills cfg))
             (sc_refill_cfgs_of s) sc_ptr\<rbrakk>
   \<Longrightarrow> whileLoop_terminates (\<lambda>_ s. the (head_insufficient sc_ptr s))
                            (\<lambda>_. non_overlapping_merge_refills sc_ptr) r s"
  (is "\<lbrakk>?P s; ?Q s\<rbrakk> \<Longrightarrow> _")
  apply (rule_tac I="\<lambda>_. ?P and ?Q"
               in whileLoop_terminates_inv[where R="head_insufficient_loop_measure sc_ptr"])
    apply simp
   apply (intro hoare_vcg_conj_lift_pre_fix)
    apply (wpsimp wp: non_overlapping_merge_refills_refills_unat_sum_lower_bound
                      non_overlapping_merge_refills_refills_unat_sum)
    apply (fastforce dest: head_insufficient_length_at_least_two)
   apply (wpsimp wp: update_sched_context_wp
               simp: head_insufficient_loop_measure_def non_overlapping_merge_refills_def
                     refill_pop_head_def update_refill_hd_def)
   apply (fastforce dest: head_insufficient_length_at_least_two
                    simp: vs_all_heap_simps obj_at_def)
  apply (clarsimp simp: head_insufficient_loop_measure_def)
  done

lemma refills_unat_sum_MIN_BUDGET_implies_non_empty_refills:
  "pred_map (\<lambda>cfg. unat MIN_BUDGET \<le> refills_unat_sum (scrc_refills cfg)) (sc_refill_cfgs_of s) sc_ptr
   \<Longrightarrow> pred_map (\<lambda>cfg. scrc_refills cfg \<noteq> []) (sc_refill_cfgs_of s) sc_ptr"
  apply (auto simp: vs_all_heap_simps refills_unat_sum_def MIN_BUDGET_nonzero unat_eq_zero)
  done

lemma headInsufficientLoop_corres:
  "sc_ptr = scPtr
   \<Longrightarrow> corres dc (pspace_aligned and pspace_distinct and sc_at sc_ptr and is_active_sc sc_ptr
                  and valid_objs
                  and (\<lambda>s. pred_map (\<lambda>cfg. unat MIN_BUDGET \<le> refills_unat_sum (scrc_refills cfg))
                                    (sc_refill_cfgs_of s) sc_ptr)
                  and (\<lambda>s. pred_map (\<lambda>cfg. refills_unat_sum (scrc_refills cfg) \<le> unat max_time)
                                    (sc_refill_cfgs_of s) sc_ptr))
                 (valid_refills' sc_ptr)
                 (head_insufficient_loop sc_ptr)
                 (headInsufficientLoop scPtr)"
  apply (clarsimp simp: head_insufficient_loop_def headInsufficientLoop_def runReaderT_def)
  apply (rule_tac Q="active_sc_at' scPtr" in corres_cross_add_guard)
   apply (fastforce dest: active_sc_at'_cross)
  apply (rule corres_whileLoop_abs; simp?)
      apply (frule head_insufficient_equiv[where scPtr=scPtr]; simp?)
      apply (fastforce intro: refills_unat_sum_MIN_BUDGET_implies_non_empty_refills)
     apply (corresKsimp corres: nonOverlappingMergeRefills_corres)
     apply (fastforce dest: head_insufficient_length_at_least_two)
    apply (wpsimp wp: non_overlapping_merge_refills_no_fail)
     apply (wpsimp wp: non_overlapping_merge_refills_refills_unat_sum_lower_bound
                       non_overlapping_merge_refills_refills_unat_sum)
    apply (fastforce dest: head_insufficient_length_greater_than_one)
   apply (wpsimp wp: nonOverlappingMergeRefills_valid_objs')
  apply (fastforce intro!: non_overlapping_merge_refills_terminates)
  done

lemma refillEmpty_sp:
  "\<lbrace>P\<rbrace>refillEmpty scp \<lbrace>\<lambda>rv s. P s \<and> (\<forall>ko. ko_at' ko scp s \<longrightarrow> rv = (scRefillCount ko = 0))\<rbrace>"
  apply (wpsimp wp: refillEmpty_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma refillFull_sp:
  "\<lbrace>P\<rbrace> refillFull scp \<lbrace>\<lambda>rv s. P s \<and> (\<forall>ko. ko_at' ko scp s \<longrightarrow> rv = (scRefillCount ko = scRefillMax ko))\<rbrace>"
  apply (wpsimp wp: refillFull_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma refillFull_corres:
  "sc_ptr = scPtr
   \<Longrightarrow> corres (=) (sc_at sc_ptr and pspace_aligned and pspace_distinct)
                  (valid_refills' scPtr)
                  (refill_full sc_ptr)
                  (refillFull scPtr)"
  apply (rule_tac Q="sc_at' scPtr" in corres_cross_add_guard)
   apply (fastforce intro: sc_at_cross)
  apply (clarsimp simp: refill_full_def refillFull_def)
  apply (rule corres_underlying_split[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corresKsimp corres: get_sc_corres)
  apply (corresKsimp corres: corres_return_eq_same)
  apply (fastforce simp: sc_relation_def obj_at_simps valid_refills'_def opt_map_red opt_pred_def)
  done

lemma scheduleUsed_corres:
  "\<lbrakk>sc_ptr = scPtr; new = refill_map new'\<rbrakk> \<Longrightarrow>
    corres dc (sc_at sc_ptr and is_active_sc2 sc_ptr and pspace_aligned and pspace_distinct)
              (valid_refills' scPtr)
              (schedule_used sc_ptr new)
              (scheduleUsed scPtr new')"
  apply (clarsimp simp: schedule_used_def scheduleUsed_def get_refills_def bind_assoc)
  apply (rule_tac Q="sc_at' scPtr" in corres_cross_add_guard)
   apply (fastforce intro: sc_at_cross)
  apply (rule_tac Q="is_active_sc' scPtr" in corres_cross_add_guard)
   apply (fastforce intro: is_active_sc'_cross)
  apply (rule corres_underlying_split[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corresKsimp corres: get_sc_corres)
  apply (rename_tac sc sc')
  apply (rule corres_symb_exec_r[rotated, OF assert_sp]; (solves wpsimp)?)
   apply wpsimp
   apply (clarsimp simp: is_active_sc'_def obj_at_simps opt_map_red opt_pred_def)
  apply (rule corres_symb_exec_r[rotated, OF refillEmpty_sp]
         ; (solves \<open>wpsimp simp: refillEmpty_def\<close>)?)
  apply (rule_tac F="empty = (sc_refills sc = [])" in corres_req)
   apply (fastforce dest: length_sc_refills_cross[where P="\<lambda>l. 0 = l"]
                    simp: valid_refills'_def obj_at_simps opt_map_red opt_pred_def)
  apply (rule corres_if_split; (solves simp)?)
   apply (corresKsimp corres: refillAddTail_corres simp: refill_map_def)
   apply (clarsimp simp: valid_refills'_def obj_at_simps opt_map_red opt_pred_def)
  apply (rule_tac F="sc_valid_refills' sc'" in corres_req)
   apply (clarsimp simp: valid_refills'_def obj_at_simps opt_map_red opt_pred_def)
  apply (rule corres_if_split; (solves simp)?)
    apply (fastforce dest: refills_tl_equal
                     simp: refill_map_def can_merge_refill_def)
   apply (corresKsimp corres: updateRefillTl_corres
                       simp: refill_map_def)
  apply (rule corres_underlying_split[rotated 2, OF refill_full_sp refillFull_sp])
   apply (corresKsimp corres: refillFull_corres)
  apply (rule corres_if_split; (solves simp)?)
   apply (corresKsimp corres: refillAddTail_corres)
   apply (clarsimp simp: refill_map_def obj_at_simps opt_map_red opt_pred_def)
  apply (corresKsimp corres: updateRefillTl_corres simp: refill_map_def)
  done

lemma head_time_buffer_simp:
  "sc_at (cur_sc s) s
   \<Longrightarrow> head_time_buffer usage s
       = Some (sc_at_pred (\<lambda>sc. r_amount (refill_hd sc) \<le> usage
                                \<and> r_time (refill_hd sc) < MAX_RELEASE_TIME)
                          (cur_sc s) s)"
  unfolding head_time_buffer_def
  apply (clarsimp simp: obind_def read_sched_context_def obj_at_def is_sc_obj sc_at_pred_n_def
                        ogets_def)
  done

lemma headTimeBuffer_simp:
  "sc_at' (ksCurSc s) s
   \<Longrightarrow> headTimeBuffer usage s
       = Some (obj_at' (\<lambda>sc :: sched_context. rAmount (refillHd sc) \<le> usage
                                              \<and> rTime (refillHd sc) < maxReleaseTime)
                       (ksCurSc s) s)"
  unfolding headTimeBuffer_def
  apply (clarsimp simp: obind_def readSchedContext_def split: option.splits)
  apply (frule no_ofailD[OF no_ofail_sc_at'_readObject])
  apply (fastforce simp: readObject_def obind_def omonad_defs split_def loadObject_default_def
                         readCurSc_def obj_at'_def ogets_def
                  split: option.splits if_split_asm)
  done

lemma head_time_buffer_equiv:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s; valid_objs s;
    pred_map (\<lambda>cfg. scrc_refills cfg \<noteq> []) (sc_refill_cfgs_of s) (cur_sc s);
    valid_refills' (ksCurSc s') s'; usage = usage'\<rbrakk>
   \<Longrightarrow> head_time_buffer usage s = headTimeBuffer usage' s'"
  apply (prop_tac "sc_at (cur_sc s) s")
   apply (fastforce dest: valid_objs_valid_sched_context_size
                    simp: vs_all_heap_simps obj_at_kh_kheap_simps is_sc_obj_def)
  apply (frule state_relation_pspace_relation)
  apply (frule sc_at_cross; simp?)
  apply (frule state_relation_sc_relation; simp?)
  apply (subst head_time_buffer_simp; simp?)
  apply (subst headTimeBuffer_simp)
   apply (clarsimp simp: state_relation_def)
  apply (frule refill_hd_relation)
    apply (clarsimp simp: valid_refills'_def obj_at_simps state_relation_def)
   apply (clarsimp simp: sc_ko_at_valid_objs_valid_sc' opt_map_def opt_pred_def obj_at_simps)
  apply (clarsimp simp: obj_at_def sc_at_ppred_def obj_at'_def projectKOs state_relation_def
                        maxReleaseTime_equiv opt_map_def vs_all_heap_simps refill_map_def)
  done

lemma refillSingle_sp:
  "\<lbrace>P\<rbrace>
   refillSingle scp
   \<lbrace>\<lambda>rv s. P s \<and> (\<forall>ko. ko_at' ko scp s \<longrightarrow> rv = (scRefillHead ko = refillTailIndex ko))\<rbrace>"
  apply (clarsimp simp: refillSingle_def)
  apply wpsimp
  apply (clarsimp simp: obj_at'_def)
  done

crunch updateRefillHd, scheduleUsed
   for valid_sched_context'[wp]: "valid_sched_context' sc"

lemma handleOverrunLoopBody_corres:
  "r = r'
   \<Longrightarrow> corres (=) (\<lambda>s. sc_at (cur_sc s) s \<and> is_active_sc2 (cur_sc s) s
                       \<and> pspace_aligned s \<and> pspace_distinct s
                       \<and> pred_map (\<lambda>cfg. scrc_refills cfg \<noteq> []) (sc_refill_cfgs_of s) (cur_sc s))
                  (\<lambda>s'. valid_refills' (ksCurSc s') s')
                  (handle_overrun_loop_body r)
                  (handleOverrunLoopBody r')"
  apply (rule_tac Q="\<lambda>s'. sc_at' (ksCurSc s') s'" in corres_cross_add_guard)
   apply (fastforce intro: sc_at_cross simp: state_relation_def)
  apply (rule_tac Q="\<lambda>s'. is_active_sc' (ksCurSc s') s'" in corres_cross_add_guard)
   apply (fastforce intro: is_active_sc'_cross simp: state_relation_def)
  apply (clarsimp simp: handle_overrun_loop_body_def handleOverrunLoopBody_def)
  apply (rule corres_underlying_split[rotated 2, OF gets_sp getCurSc_sp])
   apply (corresKsimp corres: getCurSc_corres)
  apply (rule corres_underlying_split[rotated 2, OF refill_single_sp refillSingle_sp])
   apply (corresKsimp corres: refillSingle_corres)
   apply (fastforce simp: obj_at_simps valid_refills'_def opt_map_red opt_pred_def)
  apply (rule corres_underlying_split[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corresKsimp corres: get_sc_corres)
  apply (rename_tac sc sc')
  apply (rule_tac Q="\<lambda>_ s. sc_refills sc \<noteq> []"
              and Q'="\<lambda>_ _. sc_valid_refills' sc'"
              and r'=dc
               in corres_underlying_split[rotated])
     apply corresKsimp
     apply (fastforce dest: refill_hd_relation simp: refill_map_def)
    apply (wpsimp simp: update_refill_hd_def
                    wp: update_sched_context_wp)
    apply (clarsimp simp: vs_all_heap_simps obj_at_def)
   apply wpsimp
   apply (clarsimp simp: valid_refills'_def obj_at_simps opt_map_red opt_pred_def)
  apply (rule corres_if_split; simp?)
   apply (corresKsimp corres: updateRefillHd_corres)
   apply (fastforce simp: refill_map_def sc_relation_def)
  apply (rule_tac F="1 < scRefillCount sc'" in corres_req)
   apply (frule_tac scp="scPtr" and P="\<lambda>l. 1 < l" in length_sc_refills_cross)
      apply (clarsimp simp: state_relation_def)
     apply simp
    apply (fastforce simp: refill_map_def sc_relation_def)
   apply (clarsimp simp: opt_map_red opt_pred_def vs_all_heap_simps obj_at'_def projectKOs Suc_lessI)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF refillPopHead_corres])
      apply (rule scheduleUsed_corres)
       apply simp
      apply (clarsimp simp: refill_map_def sc_relation_def)
     apply wpsimp
    apply wpsimp
   apply (clarsimp simp: is_active_sc2_def sc_at_ppred_def obj_at_def is_sc_obj_def active_sc_def
                         vs_all_heap_simps opt_map_red Suc_lessI)
  apply (clarsimp simp: obj_at_simps)
  done

lemma schedule_used_no_fail[wp]:
  "no_fail (\<lambda>s. (\<exists>sc n. kheap s sc_ptr = Some (Structures_A.SchedContext sc n)))
           (schedule_used sc_ptr new)"
  apply (wpsimp simp: schedule_used_defs get_refills_def refill_full_def
                  wp: update_sched_context_wp)
  done

lemma handle_overrun_loop_body_no_fail:
  "no_fail (\<lambda>s. (\<exists>sc n. kheap s (cur_sc s) = Some (Structures_A.SchedContext sc n))
                \<and> pred_map (\<lambda>cfg. scrc_refills cfg \<noteq> []) (sc_refill_cfgs_of s) (cur_sc s))
           (handle_overrun_loop_body usage)"
  unfolding handle_overrun_loop_body_def
  apply (wpsimp simp: refill_single_def refill_size_def get_refills_def update_refill_hd_def
                  wp: refill_pop_head_no_fail)
  done

lemma scheduleUsed_is_active_sc'[wp]:
  "scheduleUsed scPtr new \<lbrace>is_active_sc' sc_Ptr'\<rbrace>"
  apply (clarsimp simp: scheduleUsed_def)
  apply (wpsimp simp: refillAddTail_def updateRefillTl_def
                  wp: updateSchedContext_wp refillFull_wp refillEmpty_wp)
  apply (clarsimp simp: obj_at_simps is_active_sc'_def opt_map_def opt_pred_def)
  done

lemma handleOverrunLoopBody_is_active_sc'[wp]:
  "handleOverrunLoopBody usage \<lbrace>is_active_sc' sc_ptr\<rbrace>"
  apply (clarsimp simp: handleOverrunLoopBody_def)
  apply (wpsimp simp: updateRefillHd_def refillSingle_def
                  wp: updateSchedContext_wp)
  apply (clarsimp simp: obj_at_simps is_active_sc'_def opt_map_def opt_pred_def)
  done

lemma refillAddTail_valid_refills'[wp]:
  "refillAddTail scPtr refill \<lbrace>valid_refills' ptr\<rbrace>"
  apply (clarsimp simp: refillAddTail_def)
  apply (wpsimp wp: updateSchedContext_wp)
  apply (clarsimp simp: valid_refills'_def obj_at_simps opt_map_red opt_pred_def)
  done

lemma scheduleUsed_valid_refills'[wp]:
  "scheduleUsed ptr new \<lbrace>valid_refills' scPtr\<rbrace>"
  apply (clarsimp simp: scheduleUsed_def)
  apply (wpsimp wp: refillFull_wp refillEmpty_wp)
  done

crunch handle_overrun_loop_body
  for valid_objs[wp]: valid_objs

lemma handleOverrunLoopBody_valid_refills'[wp]:
  "handleOverrunLoopBody r'  \<lbrace>valid_refills' scPtr\<rbrace>"
  apply (clarsimp simp: handleOverrunLoopBody_def updateRefillHd_def refillSingle_def)
  apply wpsimp
  apply (fastforce simp: valid_refills'_def opt_map_red opt_pred_def obj_at_simps
                         refillSingle_equiv[THEN arg_cong_Not, symmetric])
  done

lemma schedule_used_length_nonzero[wp]:
  "\<lbrace>\<lambda>s. if sc_ptr' = sc_ptr
        then pred_map \<top> (scs_of s) sc_ptr
        else pred_map (\<lambda>cfg. scrc_refills cfg \<noteq> []) (sc_refill_cfgs_of s) sc_ptr\<rbrace>
   schedule_used sc_ptr' new
   \<lbrace>\<lambda>_ s. pred_map (\<lambda>cfg. scrc_refills cfg \<noteq> []) (sc_refill_cfgs_of s) sc_ptr\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp get_refills_wp
              simp: schedule_used_defs)
  apply (clarsimp simp: obj_at_def vs_all_heap_simps)
  done

lemma handle_overrun_loop_body_terminates_wf_helper:
  "wf {((r' :: ticks, s' :: 'a state), (r, s)). unat r' < unat r}"
  apply (insert wf_inv_image[where r="{(m, n). m < n}"
                               and f="\<lambda>(r :: ticks, s :: 'a state). unat r"])
  apply (clarsimp simp: inv_image_def)
  apply (prop_tac "wf {(m, n). m < n}")
   apply (fastforce intro: wf)
  apply (drule meta_mp, simp)
  apply (prop_tac "{(x :: ticks \<times> 'a state, y :: ticks \<times> 'a state).
                     (case x of (r, s) \<Rightarrow> unat r)
                      < (case y of (r, s) \<Rightarrow> unat r)}
                   = {((r, s), r', s'). unat r < unat r'}")
    apply fastforce
  apply fastforce
  done

\<comment> \<open>The following method can be used to try to solve Hoare triples in the following way.
    Note that the method works best when the precondition is not schematic.
    First, if the postcondition is not a conjunction, it will try to solve the goal with the
    method given to `solves`. The goal will be left untouched if it cannot solve the goal.
    If the postcondition is a conjunction, the method will pull it apart into all the conjuncts
    using hoare_vcg_conj_lift_pre_fix. It will then attempt to solve each of these individually.\<close>
method wps_conj_solves uses wp simp wps
   = (clarsimp simp: pred_conj_def)?
     , (intro hoare_vcg_conj_lift_pre_fix
        ; (solves \<open>rule hoare_weaken_pre, (wpsimp wp: wp simp: simp | wps wps)+\<close>)?)
       | (solves \<open>rule hoare_weaken_pre, (wpsimp wp: wp simp: simp | wps wps)+\<close>)?

lemma handle_overrun_loop_body_terminates:
  "\<lbrakk>sc_at (cur_sc s) s;
    pred_map (\<lambda>cfg. \<forall>refill \<in> set (scrc_refills cfg). 0 < unat (r_amount refill))
             (sc_refill_cfgs_of s) (cur_sc s);
    pred_map (\<lambda>cfg. scrc_refills cfg \<noteq> []) (sc_refill_cfgs_of s) (cur_sc s);
    pred_map (\<lambda>cfg. refills_unat_sum (scrc_refills cfg) = unat (scrc_budget cfg))
             (sc_refill_cfgs_of s) (cur_sc s)\<rbrakk>
   \<Longrightarrow> whileLoop_terminates (\<lambda>r s. the (head_time_buffer r s)) handle_overrun_loop_body usage s"
  (is "\<lbrakk>?P1 s; ?P2 s; ?P3 s; ?P4 s\<rbrakk> \<Longrightarrow> _")
  apply (rule_tac R="{((r' :: ticks, s' :: 'a state), (r, s)). unat r' < unat r}"
              and I="\<lambda>_ s'. ?P1 s' \<and> ?P2 s' \<and> ?P3 s' \<and> ?P4 s' \<and> cur_sc s' = cur_sc s"
               in whileLoop_terminates_inv)
    apply simp
   prefer 2
   apply (fastforce simp: handle_overrun_loop_body_terminates_wf_helper)
  apply (rename_tac r s')
  apply (wps_conj_solves wp: handle_overrun_loop_body_non_zero_refills
                             handle_overrun_loop_body_refills_unat_sum_equals_budget)
   apply (wpsimp simp: handle_overrun_loop_body_def)
  apply (rename_tac sc n)
  apply (subst unat_sub)
   apply (prop_tac "sc_at (cur_sc s') s'", simp)
   apply (frule_tac usage=r and s=s' in head_time_buffer_simp)
   apply (clarsimp simp: sc_at_ppred_def obj_at_def)
  apply (clarsimp simp: obj_at_def vs_all_heap_simps)
  apply (frule_tac x="refill_hd sc" in bspec, fastforce)
  apply (prop_tac "0 < unat r")
   apply (prop_tac "sc_at (cur_sc s') s'")
    apply (clarsimp simp: obj_at_def is_sc_obj_def)
   apply (frule_tac usage=r and s=s' in head_time_buffer_simp)
   apply (clarsimp simp: sc_at_ppred_def obj_at_def)
   apply (frule_tac x="refill_hd sc" in bspec, fastforce)
   apply (fastforce simp: word_le_nat_alt)
  apply fastforce
  done

lemma handleOverrunLoop_corres:
  "usage = usage' \<Longrightarrow>
   corres (=) (\<lambda>s. sc_at (cur_sc s) s \<and> is_active_sc2 (cur_sc s) s
                   \<and> pspace_aligned s \<and> pspace_distinct s
                   \<and> valid_objs s
                   \<and> pred_map (\<lambda>cfg. scrc_refills cfg \<noteq> []) (sc_refill_cfgs_of s) (cur_sc s)
                   \<and> pred_map (\<lambda>cfg. \<forall>refill\<in>set (scrc_refills cfg). 0 < unat (r_amount refill))
                               (sc_refill_cfgs_of s) (cur_sc s)
                   \<and> pred_map (\<lambda>cfg. refills_unat_sum (scrc_refills cfg) = unat (scrc_budget cfg))
                               (sc_refill_cfgs_of s) (cur_sc s))
              (\<lambda>s'. valid_refills' (ksCurSc s') s')
              (handle_overrun_loop usage)
              (handleOverrunLoop usage')"
  apply (rule_tac Q="\<lambda>s'. sc_at' (ksCurSc s') s'" in corres_cross_add_guard)
   apply (fastforce intro: sc_at_cross simp: state_relation_def)
  apply (rule_tac Q="\<lambda>s'. is_active_sc' (ksCurSc s') s'" in corres_cross_add_guard)
   apply (fastforce intro: is_active_sc'_cross simp: state_relation_def)
  apply (clarsimp simp: handle_overrun_loop_def handleOverrunLoop_def runReaderT_def)
  apply (rule corres_whileLoop_abs; simp?)
      apply (frule_tac usage=r' in head_time_buffer_equiv; simp?)
      apply fastforce
     apply (corresKsimp corres: handleOverrunLoopBody_corres)
    apply (wps_conj_solves wp: handle_overrun_loop_body_non_zero_refills
                               handle_overrun_loop_body_refills_unat_sum_equals_budget)
   apply wps_conj_solves
  apply (fastforce intro:  handle_overrun_loop_body_terminates)
  done

lemma handle_overrun_loop_is_active_sc[wp]:
  "handle_overrun_loop usage \<lbrace>\<lambda>s. is_active_sc sc_ptr s\<rbrace>"
  apply handle_overrun_loop_simple
  done

lemma get_refills_exs_valid[wp]:
  "sc_at sc_ptr s \<Longrightarrow> \<lbrace>(=) s\<rbrace> get_refills sc_ptr \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  apply (clarsimp simp: get_refills_def)
  apply (wpsimp wp: get_sched_context_exs_valid)
   apply (erule sc_atD1)
  apply simp
  done

crunch handleOverrunLoop
  for valid_refills'[wp]: "valid_refills' scPtr"
  (wp: crunch_wps)

lemma refillBudgetCheck_corres:
  "usage = usage'
   \<Longrightarrow> corres dc ((\<lambda>s. sc_at (cur_sc s) s \<and> is_active_sc (cur_sc s) s
                       \<and> valid_objs s
                       \<and> pspace_aligned s \<and> pspace_distinct s)
                  and (\<lambda>s. \<not> round_robin (cur_sc s) s \<and> valid_refills (cur_sc s) s))
                 (\<lambda>s'. valid_refills' (ksCurSc s') s')
                 (refill_budget_check usage)
                 (refillBudgetCheck usage')"
  (is "_ \<Longrightarrow> corres _ (?P and _) _ _ _")
  apply (rule_tac Q="\<lambda>s'. sc_at' (ksCurSc s') s'" in corres_cross_add_guard)
   apply (fastforce intro: sc_at_cross simp: state_relation_def)
  apply (rule_tac Q="\<lambda>s'. is_active_sc' (ksCurSc s') s'" in corres_cross_add_guard)
   apply (fastforce intro!: is_active_sc'2_cross simp: state_relation_def)

  apply (clarsimp simp: refill_budget_check_def refillBudgetCheck_def)
  apply (rule corres_underlying_split[rotated 2, OF gets_sp getCurSc_sp])
   apply (corresKsimp corres: getCurSc_corres)
  apply (rule corres_symb_exec_r[rotated, OF scActive_sp]; (solves \<open>wpsimp simp: scActive_def\<close>)?)
  apply (rule corres_symb_exec_r[rotated, OF assert_sp]; (solves wpsimp)?)
   apply (wpsimp wp: no_fail_assert
               simp: is_active_sc'_def opt_map_red opt_pred_def obj_at_simps)
  apply (rule corres_underlying_split[rotated 2, OF is_round_robin_sp isRoundRobin_sp])
   apply (corresKsimp corres: isRoundRobin_corres)
  apply (rule corres_symb_exec_l[rotated, OF _  assert_sp]; (solves wpsimp)?)
  apply (rule_tac F="\<not>roundRobin" in corres_req)
   apply clarsimp
  apply (rule corres_symb_exec_r[rotated, OF assert_sp]; (solves wpsimp)?)

  apply (rule_tac Q="\<lambda>usage' s. ?P s
                                \<and> pred_map (\<lambda>cfg. refills_unat_sum (scrc_refills cfg)
                                                   = unat (scrc_budget cfg))
                                           (sc_refill_cfgs_of s) sc_ptr
                                \<and> pred_map (\<lambda>cfg. MIN_BUDGET \<le> scrc_budget cfg)
                                            (sc_refill_cfgs_of s) sc_ptr
                                \<and> sc_ptr = cur_sc s
                                \<and> (pred_map (\<lambda>cfg. r_time (hd (scrc_refills cfg)) < MAX_RELEASE_TIME)
                                             (sc_refill_cfgs_of s) (cur_sc s)
                                   \<longrightarrow> pred_map (\<lambda>cfg. usage' < r_amount (hd (scrc_refills cfg)))
                                                (sc_refill_cfgs_of s) (cur_sc s))
                                \<and> pred_map (\<lambda>cfg. scrc_refills cfg \<noteq> [])
                                            (sc_refill_cfgs_of s) sc_ptr"
               and Q'="\<lambda>_ s'. valid_refills' scPtr s' \<and> active_sc_at' scPtr s' \<and> scPtr = ksCurSc s'"
               in corres_underlying_split)
     apply (corresKsimp corres: handleOverrunLoop_corres)
     apply (fastforce intro: valid_refills_refills_unat_sum_equals_budget
                       simp: vs_all_heap_simps cfg_valid_refills_def round_robin_def
                             sp_valid_refills_def is_active_sc_rewrite[symmetric])
    apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> handle_overrun_loop _ \<lbrace>Q\<rbrace>" for P Q \<Rightarrow> -\<close>)
    apply (clarsimp simp: pred_conj_def)
    apply (intro hoare_vcg_conj_lift_pre_fix; (solves handle_overrun_loop_simple)?)
      apply wps_conj_solves
     apply (wpsimp wp: handle_overrun_loop_refills_unat_sum_equals_budget)
     apply (fastforce intro: valid_refills_refills_unat_sum_equals_budget
                       simp: vs_all_heap_simps cfg_valid_refills_def round_robin_def
                             sp_valid_refills_def)
    apply (clarsimp simp: handle_overrun_loop_def)
    apply (wpsimp wp: valid_whileLoop[where I="\<lambda>_ s. pred_map \<top> (scs_of s) (cur_sc s)"])
     apply (fastforce simp: head_time_buffer_true_imp_unat_buffer vs_all_heap_simps
                            word_less_nat_alt word_le_nat_alt)
    apply (clarsimp simp: vs_all_heap_simps)
   apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> handleOverrunLoop _ \<lbrace>Q\<rbrace>" for P Q \<Rightarrow> -\<close>)
   apply wpsimp
   apply (clarsimp simp: active_sc_at'_def obj_at_simps)

  apply (clarsimp simp: get_refills_def)
  apply (rule corres_underlying_split[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corresKsimp corres: get_sc_corres
                       simp: state_relation_def active_sc_at'_def obj_at_simps)
  apply (rename_tac sc sc')
  apply (rule_tac Q="\<lambda>_ s. ?P s
                           \<and> pred_map (\<lambda>cfg. refills_unat_sum (scrc_refills cfg)
                                              = unat (scrc_budget cfg))
                                       (sc_refill_cfgs_of s) scPtr
                           \<and> pred_map (\<lambda>cfg. MIN_BUDGET \<le> scrc_budget cfg)
                                       (sc_refill_cfgs_of s) scPtr
                           \<and> scPtr = cur_sc s"
              and Q'="\<lambda>_ s'. valid_refills' scPtr s' \<and> active_sc_at' scPtr s' \<and> scPtr = ksCurSc s'"
              and r'=dc
               in corres_underlying_split[rotated])
     apply (corresKsimp corres: headInsufficientLoop_corres)
     apply (fastforce simp: vs_all_heap_simps word_le_nat_alt)
    apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
       apply schedule_used_simple
       apply (clarsimp simp: obj_at_def is_sc_obj_def)
      apply schedule_used_simple
     apply (wpsimp wp: schedule_used_refills_unat_sum update_sched_context_wp
                 simp: update_refill_hd_def)
     apply (clarsimp simp: obj_at_def vs_all_heap_simps refills_unat_sum_cons
                           refills_unat_sum_append)
     apply (subst unat_sub)
      apply fastforce
     apply (clarsimp simp: word_less_nat_alt)
     apply (drule less_imp_le)
     apply (clarsimp simp: refills_unat_sum_def)
     apply (case_tac "sc_refills sc"; clarsimp simp: refills_unat_sum_cons)
    apply schedule_used_simple
   apply wpsimp

  apply (rule_tac F="refill_hd sc = refill_map (refillHd sc')" in corres_req)
   apply clarsimp
   apply (rule refill_hd_relation)
     apply fastforce
    apply (clarsimp simp: vs_all_heap_simps obj_at_def)
   apply (fastforce simp: valid_refills'_def obj_at_simps opt_map_red opt_pred_def)

  apply (clarsimp simp: maxReleaseTime_equiv)
  apply (simp add: when_def split del: if_split)
  apply (rule corres_if_split; (solves simp)?)
   apply (clarsimp simp: refill_map_def)
  apply (rule corres_symb_exec_l[rotated 2, OF get_sched_context_sp])
    apply wpsimp
    apply (clarsimp simp: obj_at_def)
   apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<exists>\<lbrace>Q\<rbrace>" for P f Q \<Rightarrow> -\<close>)
   apply (wpsimp wp: get_sched_context_exs_valid)
    apply (clarsimp simp: obj_at_def)
   apply simp
  apply (rename_tac new_sc)
  apply (rule_tac F="new_sc=sc" in corres_req)
   apply (clarsimp simp: obj_at_def)
  apply (subst update_refill_hd_comp)
  apply (clarsimp simp: bind_assoc)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF updateRefillHd_corres])
        apply simp
       apply (clarsimp simp: refill_map_def)
      apply (rule corres_split[OF updateRefillHd_corres])
          apply simp
         apply (clarsimp simp: refill_map_def)
        apply (rule scheduleUsed_corres)
         apply simp
        apply (clarsimp simp: refill_map_def sc_relation_def)
       apply wpsimp
      apply wpsimp
     apply wpsimp
    apply wpsimp
   apply (clarsimp simp: is_active_sc_rewrite)
  apply (fastforce simp: active_sc_at'_def is_active_sc'_def obj_at_simps opt_map_red)
  done

(* schedule_corres *)

crunch setReprogramTimer
  for valid_tcbs'[wp]: valid_tcbs'
  and valid_refills'[wp]: "valid_refills' scPtr"
  and ksCurSc[wp]: "\<lambda>s. P (ksCurSc s)"
  (simp: valid_refills'_def)

lemma checkDomainTime_corres:
  "corres dc (valid_tcbs and weak_valid_sched_action and active_scs_valid and pspace_aligned
              and pspace_distinct)
             (valid_tcbs' and valid_queues and valid_queues' and valid_release_queue_iff)
             check_domain_time
             checkDomainTime"
  apply (clarsimp simp: check_domain_time_def checkDomainTime_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF isCurDomainExpired_corres])
      apply (rule corres_when)
       apply simp
      apply (rule corres_split[OF setReprogramTimer_corres])
        apply (rule rescheduleRequired_corres)
       apply (wpsimp wp: hoare_drop_imps
                   simp: isCurDomainExpired_def)+
  done

crunch refill_budget_check_round_robin
  for sc_at[wp]: "sc_at sc_ptr"
  and valid_objs[wp]: valid_objs
  and pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct

lemma commitTime_corres:
  "corres dc (\<lambda>s. sc_at (cur_sc s) s \<and> valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s
                  \<and> (cur_sc_active s \<longrightarrow> valid_refills (cur_sc s) s))
             (\<lambda>s'. is_active_sc' (ksCurSc s') s' \<longrightarrow> valid_refills' (ksCurSc s') s')
             commit_time
             commitTime"
  supply if_split[split del]
  apply (rule_tac Q="\<lambda>s'. sc_at' (ksCurSc s') s'" in corres_cross_add_guard)
   apply (fastforce intro: sc_at_cross simp: state_relation_def)
  apply (clarsimp simp: commit_time_def commitTime_def liftM_def)
  apply (rule corres_underlying_split[rotated 2, OF gets_sp getCurSc_sp])
   apply (corresKsimp corres: getCurSc_corres)
  apply clarsimp
  apply (rule corres_underlying_split[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corresKsimp corres: get_sc_corres)
  apply (rule corres_symb_exec_r[rotated, OF getIdleSC_sp])
    apply wpsimp
   apply (wpsimp simp: getIdleSC_def)
  apply (rename_tac idleSCPtr)
  apply (rule corres_underlying_split[rotated, where r'=dc])
     apply (rule setConsumedTime_corres)
     apply simp
    apply wpsimp
   apply wpsimp
  apply (clarsimp simp: when_def)
  apply (rule_tac F="idleSCPtr = idle_sc_ptr" in corres_req)
   apply (clarsimp simp: state_relation_def)
  apply (rule corres_if_split; fastforce?)
   apply (fastforce simp: sc_relation_def active_sc_def)
  apply (rule corres_underlying_split[rotated 2, OF gets_sp getConsumedTime_sp])
   apply corresKsimp
  apply clarsimp
  apply (rename_tac consumed)
  apply (rule_tac Q="\<lambda>_ s. sc_at (cur_sc s) s \<and> csc = cur_sc s"
              and Q'="\<lambda>_ s'. sc_at' (ksCurSc s') s' \<and> csc = ksCurSc s'"
              and r'=dc
               in corres_underlying_split[rotated])
     apply (clarsimp simp: updateSchedContext_def)
     apply (rule corres_symb_exec_r[rotated, OF get_sc_sp'])
       apply wpsimp
      apply wpsimp
     apply (rename_tac sc')
     apply (prop_tac "(\<lambda>sc. sc\<lparr>sc_consumed := sc_consumed sc + consumed\<rparr>)
                      = sc_consumed_update (\<lambda>c. c + consumed)")
      apply force
     apply (prop_tac "scConsumed_update (\<lambda>_. scConsumed sc' + consumed) sc'
                      = scConsumed_update (\<lambda>c. c + consumed) sc'")
      apply (fastforce intro: sched_context.expand)
     apply (rule_tac P="\<lambda>t. corres dc _ _ (update_sched_context csc t) _" in subst[OF sym])
      apply assumption
     apply (rule_tac P="\<lambda>t. corres dc _ _ _ (setSchedContext csc t)" in subst[OF sym])
      apply assumption
     apply (rule corres_guard_imp)
       apply (rule_tac f'="\<lambda>sched_context'. (scConsumed_update (\<lambda>c. c + consumed)) sched_context'"
                    in setSchedContext_update_sched_context_no_stack_update_corres)
          apply (clarsimp simp: sc_relation_def opt_map_red opt_map_def active_sc_def)
         apply fastforce
        apply (fastforce simp: obj_at_simps)
       apply (wpsimp simp: isRoundRobin_def | wps)+
  apply (clarsimp simp: ifM_def split: if_split)
  apply (rule corres_underlying_split[rotated 2, OF is_round_robin_sp isRoundRobin_sp])
   apply (corresKsimp corres: isRoundRobin_corres)
  apply (corresKsimp corres: refillBudgetCheckRoundRobin_corres refillBudgetCheck_corres)
  apply (fastforce simp: obj_at_def vs_all_heap_simps is_sc_obj_def obj_at_simps sc_relation_def
                         is_active_sc'_def opt_map_red opt_pred_def active_sc_def)
  done

crunch ifCondRefillUnblockCheck
  for valid_objs'[wp]: valid_objs'
  (simp: crunch_simps)

lemma switchSchedContext_corres:
  "corres dc (\<lambda>s. valid_state s \<and> cur_tcb s \<and> sc_at (cur_sc s) s  \<and> active_scs_valid s
                  \<and> current_time_bounded s \<and> active_sc_tcb_at (cur_thread s) s)
             valid_objs'
             switch_sched_context
             switchSchedContext"
  apply (clarsimp simp: valid_state_def)
  apply add_cur_tcb'
  apply (clarsimp simp: switch_sched_context_def switchSchedContext_def)
  apply (rule corres_underlying_split[rotated 2, OF gets_sp getCurSc_sp])
   apply (corresKsimp corres: getCurSc_corres)
  apply (clarsimp, rename_tac curScPtr)
  apply (rule corres_underlying_split[rotated 2, OF gets_sp getCurThread_sp])
   apply corresKsimp
  apply (clarsimp, rename_tac ct)
  apply (rule corres_underlying_split[rotated 2, OF gsc_sp threadGet_sp, where r'="(=)"])
   apply (rule corres_guard_imp)
     apply (rule get_tcb_obj_ref_corres)
     apply (fastforce simp: tcb_relation_def)
    apply (fastforce simp: cur_tcb_def)
   apply (fastforce simp: cur_tcb'_def)
  apply (clarsimp, rename_tac ctScOpt)
  apply (rule corres_symb_exec_l[rotated, OF _ assert_opt_sp])
    apply wpsimp
    apply (fastforce simp: obj_at_def pred_tcb_at_def vs_all_heap_simps)
   apply wpsimp
   apply (fastforce simp: obj_at_def pred_tcb_at_def vs_all_heap_simps)
  apply (rename_tac scp)
  apply (rule corres_symb_exec_l[rotated, OF _ get_sched_context_sp])
    apply (rule get_sched_context_exs_valid)
    apply (clarsimp simp: sc_at_pred_n_def obj_at_def is_sc_obj_def)
    apply (rename_tac ko n, case_tac ko; clarsimp)
   apply wpsimp
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def is_sc_obj_def)
  apply (rename_tac ko n, case_tac ko; clarsimp)
  apply (rule_tac F="the ctScOpt = scp" in corres_req, simp)
  apply (rule_tac Q="\<lambda>_ s. sc_at (cur_sc s) s \<and> valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s
                           \<and> (cur_sc_active s \<longrightarrow> valid_refills (cur_sc s) s)"
              and Q'="\<lambda>_. valid_objs'"
              and r'=dc
               in corres_underlying_split;
         (solves wpsimp)?)
    apply (clarsimp simp: when_def)
    apply (rule corres_split_skip; (solves \<open>wpsimp wp: hoare_vcg_ex_lift\<close>)?)
     apply (corresKsimp corres: setReprogramTimer_corres)
    apply (corresKsimp corres: ifCondRefillUnblockCheck_corres)
    apply (fastforce intro: valid_objs'_valid_refills' sc_at_cross is_active_sc'2_cross
                            valid_sched_context_size_objsI
                      simp: obj_at_def pred_tcb_at_def vs_all_heap_simps is_sc_obj_def opt_map_red
                            opt_pred_def)
   apply (rule corres_split_skip; (solves wpsimp)?)
    apply (corresKsimp corres: getReprogramTimer_corres)
   apply (rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and r'=dc in corres_underlying_split; (solves wpsimp)?)
    apply (corresKsimp corres: commitTime_corres)
    apply (fastforce intro!: valid_objs'_valid_refills' sc_at_cross
                       simp: state_relation_def)
   apply (corresKsimp corres: setCurSc_corres)
  apply (wpsimp wp: hoare_vcg_imp_lift' | wps)+
  apply (fastforce intro: valid_sched_context_size_objsI active_scs_validE
                    simp: obj_at_def is_sc_obj_def)
  done

lemma commit_time_active_sc_tcb_at[wp]:
  "commit_time \<lbrace>active_sc_tcb_at t\<rbrace>"
  by (wpsimp simp: commit_time_def)

crunch switch_sched_context
  for active_sc_tcb_at[wp]: "active_sc_tcb_at t"
  and not_in_release_q[wp]: "\<lambda>s. t \<notin> set (release_queue s)"
  and pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  (wp: crunch_wps simp: crunch_simps)

crunch schedule_choose_new_thread
  for sc_at[wp]: "sc_at sc_ptr"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps)

lemma scAndTimer_corres:
  "corres dc (\<lambda>s. valid_state s \<and> cur_tcb s \<and> sc_at (cur_sc s) s
                  \<and> active_scs_valid s \<and> valid_release_q s
                  \<and> current_time_bounded s \<and> active_sc_tcb_at (cur_thread s) s)
             invs'
             sc_and_timer
             scAndTimer"
  apply (clarsimp simp: sc_and_timer_def scAndTimer_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF switchSchedContext_corres])
      apply (rule corres_split[OF getReprogramTimer_corres])
        apply (clarsimp simp: when_def)
        apply (rule corres_split[OF setNextInterrupt_corres])
          apply (rule setReprogramTimer_corres)
         apply (wpsimp wp: hoare_vcg_ball_lift2| wps)+
     apply (rule_tac Q="\<lambda>_.invs" in hoare_post_imp, fastforce)
     apply wpsimp+
    apply (rule_tac Q="\<lambda>_. invs'" in hoare_post_imp, fastforce)
    apply (wpsimp wp: switchSchedContext_invs')
   apply (clarsimp simp: valid_state_def valid_release_q_def)
  apply fastforce
  done

lemma tcb_sched_action_valid_state[wp]:
  "tcb_sched_action action thread \<lbrace>valid_state\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def valid_state_def
               wp: hoare_drop_imps hoare_vcg_all_lift)

crunch setQueue, addToBitmap
  for isSchedulable_bool[wp]: "isSchedulable_bool tcbPtr"
  (simp: bitmap_fun_defs isSchedulable_bool_def isScActive_def)

lemma tcbSchedEnqueue_isSchedulable_bool[wp]:
  "tcbSchedEnqueue tcbPtr \<lbrace>isSchedulable_bool tcbPtr'\<rbrace>"
  apply (clarsimp simp: tcbSchedEnqueue_def unless_def)
  apply (rule bind_wp_fwd_skip, wpsimp)+
  apply (rule hoare_when_cases, simp)
  apply (rule bind_wp_fwd_skip, wpsimp)+
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: obj_at_simps isSchedulable_bool_def pred_map_simps opt_map_def
                         isScActive_def
                  split: option.splits)
  done

lemma schedule_switch_thread_branch_sc_at_cur_sc:
  "\<lbrace>valid_objs and cur_sc_tcb\<rbrace>
   schedule_switch_thread_branch candidate ct ct_schdlble
   \<lbrace>\<lambda>_ s. sc_at (cur_sc s) s\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule_tac f=cur_sc in hoare_lift_Pf2)
    apply (wpsimp simp: schedule_switch_thread_fastfail_def wp: hoare_drop_imps)+
  apply (fastforce intro: cur_sc_tcb_sc_at_cur_sc)
  done

lemma schedule_switch_thread_branch_valid_state_and_cur_tcb:
  "\<lbrace>\<lambda>s. invs s \<and> scheduler_action s = switch_thread candidate\<rbrace>
   schedule_switch_thread_branch candidate ct ct_schdlble
   \<lbrace>\<lambda>_ s. valid_state s \<and> cur_tcb s\<rbrace>"
  apply (wpsimp simp: schedule_switch_thread_fastfail_def set_scheduler_action_def
                  wp: switch_to_thread_invs thread_get_inv hoare_drop_imps)
  done

lemma schedule_corres:
  "corres dc (invs and valid_sched and current_time_bounded and ct_ready_if_schedulable
              and (\<lambda>s. schact_is_rct s \<longrightarrow> cur_sc_active s))
             invs'
             (Schedule_A.schedule)
             schedule"
  apply add_sch_act_wf
  apply add_cur_tcb'
  apply (clarsimp simp: Schedule_A.schedule_def schedule_def sch_act_wf_asrt_def cur_tcb'_asrt_def)
  apply (rule corres_stateAssert_add_assertion[rotated], simp)+
  apply (rule corres_split_skip)
     apply (wpsimp wp: awaken_valid_sched hoare_vcg_imp_lift')
     apply fastforce
    apply (wpsimp wp: awaken_invs')
   apply (corresKsimp corres: awaken_corres)
   apply (fastforce intro: weak_sch_act_wf_at_cross
                     simp: invs_def valid_state_def)
  apply (rule corres_split_skip)
     apply (wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)
    apply wpsimp
   apply (corresKsimp corres: checkDomainTime_corres)
   apply (fastforce intro: weak_sch_act_wf_at_cross
                     simp: invs_def valid_state_def)
  apply (rule corres_underlying_split[rotated 2, OF gets_sp getCurThread_sp])
   apply corresKsimp
  apply (rule corres_underlying_split[rotated 2, OF is_schedulable_sp' isSchedulable_sp])
   apply (corresKsimp corres: isSchedulable_corres)
   apply (fastforce intro: weak_sch_act_wf_at_cross
                     simp: invs_def valid_state_def state_relation_def cur_tcb_def)
  apply (rule corres_underlying_split[rotated 2, OF gets_sp getSchedulerAction_sp])
   apply (corresKsimp corres: getSchedulerAction_corres)

  apply (case_tac "action = resume_cur_thread"; clarsimp)
   apply (corresKsimp corres: scAndTimer_corres)
   subgoal by (fastforce intro: valid_sched_context_size_objsI
                          dest: schact_is_rct_ct_active_sc
                          simp: invs_def cur_sc_tcb_def sc_at_pred_n_def obj_at_def is_sc_obj_def
                                valid_state_def valid_sched_def)

  apply (case_tac "action = choose_new_thread")
   apply (clarsimp simp: bind_assoc)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF corres_when])
         apply simp
        apply (rule tcbSchedEnqueue_corres)
       apply (rule corres_split[OF scheduleChooseNewThread_corres])
         apply (rule scAndTimer_corres)
        apply (subst conj_assoc[symmetric])
        apply ((wpsimp wp: schedule_choose_new_thread_valid_state_cur_tcb
                           schedule_choose_new_thread_active_sc_tcb_at_cur_thread
               | rule_tac f=cur_sc in hoare_lift_Pf2
               | rule_tac f=cur_thread in hoare_lift_Pf2)+)[1]
       apply (wpsimp wp: scheduleChooseNewThread_invs')
      apply (wpsimp | wps)+
    subgoal by (fastforce intro!: cur_sc_tcb_sc_at_cur_sc valid_sched_context_size_objsI
                            simp: schedulable_def2 pred_tcb_at_def obj_at_def get_tcb_def
                                  invs_def cur_tcb_def is_tcb_def ct_ready_if_schedulable_def
                                  vs_all_heap_simps valid_sched_def)
   apply (fastforce simp: invs'_def isSchedulable_bool_def st_tcb_at'_def pred_map_simps
                          obj_at_simps cur_tcb'_def
                   elim!: opt_mapE)

  apply (case_tac action; clarsimp)
  apply (rule corres_underlying_split[OF _ scAndTimer_corres, where r'=dc])

    apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q  \<Rightarrow> -\<close>)
    apply (subst bind_dummy_ret_val)+
    apply (subst conj_assoc[symmetric])
    apply (rule hoare_vcg_conj_lift_pre_fix)
     apply (wpsimp wp: schedule_switch_thread_branch_valid_state_and_cur_tcb)
    apply (intro hoare_vcg_conj_lift_pre_fix;
           (solves \<open>wpsimp simp: schedule_switch_thread_fastfail_def
                             wp: thread_get_inv hoare_drop_imps\<close>)?)
     apply (wpsimp wp: schedule_switch_thread_branch_sc_at_cur_sc)
     apply fastforce
    apply (wpsimp wp: schedule_switch_thread_branch_active_sc_tcb_at_cur_thread)
    apply (fastforce simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                           vs_all_heap_simps)

   apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q  \<Rightarrow> -\<close>)
   apply (rename_tac target)
   apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> curThread = ksCurThread s \<and> st_tcb_at' runnable' target s"
                in bind_wp_fwd)
    apply wpsimp
    apply (clarsimp simp: invs'_def isSchedulable_bool_def st_tcb_at'_def pred_map_simps
                          obj_at_simps cur_tcb'_def sch_act_wf_cases
                   elim!: opt_mapE
                   split: scheduler_action.splits)
   apply (rule bind_wp_fwd_skip, solves wpsimp)+
   apply (wpsimp wp: scheduleChooseNewThread_invs' ksReadyQueuesL1Bitmap_return_wp
               simp: isHighestPrio_def scheduleSwitchThreadFastfail_def)

  apply (rename_tac candidate)
  apply (rule corres_split_skip[where r'="(=)"])
     apply wpsimp
     apply (clarsimp simp: schedulable_def2 pred_tcb_at_def obj_at_def valid_sched_def
                           ct_ready_if_schedulable_def vs_all_heap_simps)
    apply wpsimp
    apply (clarsimp simp: invs'_def isSchedulable_bool_def st_tcb_at'_def pred_map_simps
                          obj_at_simps vs_all_heap_simps cur_tcb'_def
                   elim!: opt_mapE)
   apply (corresKsimp corres: tcbSchedEnqueue_corres)
   apply (fastforce dest: invs_cur
                    simp: cur_tcb_def)

  apply (rule corres_underlying_split[rotated 2, OF gets_sp getIdleThread_sp])
   apply corresKsimp
  apply (rule corres_underlying_split[rotated 2, OF thread_get_sp threadGet_sp, where r'="(=)"])
   apply (rule corres_guard_imp)
     apply (rule threadGet_corres)
     apply (clarsimp simp: tcb_relation_def)
    apply (fastforce simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                           vs_all_heap_simps obj_at_def is_tcb_def)
   apply (clarsimp simp: sch_act_wf_cases split: scheduler_action.splits)

  apply (rule_tac Q="\<lambda>_ s. invs s \<and> valid_ready_qs s \<and> ready_or_release s
                           \<and> pred_map runnable (tcb_sts_of s) candidate
                           \<and> released_sc_tcb_at candidate s \<and> not_in_release_q candidate s"
              and Q'="\<lambda>_ s. invs' s \<and> cur_tcb' s \<and> curThread = ksCurThread s
                            \<and> st_tcb_at' runnable' candidate s"
              and r'="(=)"
               in corres_underlying_split)
     apply clarsimp
     apply (rule corres_guard_imp)
       apply (rule threadGet_corres)
       apply (clarsimp simp: tcb_relation_def)
      apply clarsimp
     apply (clarsimp simp: cur_tcb'_def)

    apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q  \<Rightarrow> -\<close>)
    apply (wpsimp wp: thread_get_wp)
    apply (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                          in_queue_2_def)

   apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q  \<Rightarrow> -\<close>)
   apply (wpsimp wp: threadGet_wp)
   apply (clarsimp simp: cur_tcb'_def obj_at_simps sch_act_wf_cases
                  split: scheduler_action.splits)

  apply (rule corres_underlying_split[rotated 2, OF schedule_switch_thread_fastfail_inv
                                          scheduleSwitchThreadFastfail_inv])
   apply (corresKsimp corres: scheduleSwitchThreadFastfail_corres)
   apply (fastforce dest: invs_cur
                    simp: cur_tcb_def obj_at_def is_tcb_def state_relation_def cur_tcb'_def)
  apply (rule corres_underlying_split[rotated 2, OF gets_sp curDomain_sp])
   apply (corresKsimp corres: curDomain_corres)
  apply (clarsimp simp: isHighestPrio_def' split del: if_split)

  apply (rule corres_underlying_split[rotated 2, OF gets_sp gets_sp, where r'="(=)"])
   apply (corresKsimp corres: isHighestPrio_corres)
   apply (clarsimp simp: is_highest_prio_def)
   apply (subst bitmapL1_zero_ksReadyQueues)
     apply (fastforce dest: invs_queues simp: valid_queues_def)
    apply (fastforce dest: invs_queues simp: valid_queues_def)
   apply (rule disj_cong)
    apply (fastforce simp: ready_queues_relation_def dest!: state_relationD)
   apply clarsimp
   apply (subst lookupBitmapPriority_Max_eqI)
      apply (fastforce dest: invs_queues simp: valid_queues_def)
     apply (fastforce dest: invs_queues simp: valid_queues_def)
    apply (subst bitmapL1_zero_ksReadyQueues)
      apply (fastforce dest: invs_queues simp: valid_queues_def)
     apply (fastforce dest: invs_queues simp: valid_queues_def)
    apply (fastforce simp: ready_queues_relation_def dest!: state_relationD)
   apply (clarsimp simp: ready_queues_relation_def dest!: state_relationD)

  apply (rule corres_if_split; (solves simp)?)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF tcbSchedEnqueue_corres])
       apply clarsimp
       apply (rule corres_split[OF setSchedulerAction_corres])
          apply (clarsimp simp: sched_act_relation_def)
         apply (rule scheduleChooseNewThread_corres)
        apply wpsimp+
    apply (fastforce simp: obj_at_def vs_all_heap_simps is_tcb_def pred_tcb_at_def)
   apply fastforce

  apply (rule corres_if_split; (solves simp)?)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF tcbSchedAppend_corres])
       apply clarsimp
       apply (rule corres_split[OF setSchedulerAction_corres])
          apply (clarsimp simp: sched_act_relation_def)
         apply (rule scheduleChooseNewThread_corres)
        apply wpsimp+
    apply (fastforce simp: obj_at_def vs_all_heap_simps is_tcb_def pred_tcb_at_def)
   apply fastforce

  apply (rule corres_guard_imp)
    apply (rule corres_split[OF switchToThread_corres])
      apply clarsimp
      apply (rule setSchedulerAction_corres)
      apply (clarsimp simp: sched_act_relation_def)
     apply wpsimp
    apply wpsimp
   apply (clarsimp simp: pred_conj_def)
   apply (fastforce simp: obj_at_def vs_all_heap_simps pred_tcb_at_def)
  apply fastforce
  done

end

lemma schedContextDonate_valid_queues[wp]:
  "\<lbrace>valid_queues and valid_objs'\<rbrace> schedContextDonate scPtr tcbPtr \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  (is "valid ?pre _ _")
  apply (clarsimp simp: schedContextDonate_def)
  apply (rule bind_wp[OF _ get_sc_sp'])
  apply (rule_tac Q'="\<lambda>_. ?pre" in bind_wp_fwd)
   apply (rule hoare_when_cases, clarsimp)
   apply (rule_tac Q'="\<lambda>_. ?pre" in bind_wp_fwd)
    apply (wpsimp wp: tcbSchedDequeue_valid_queues)
    apply (fastforce intro: valid_objs'_maxDomain valid_objs'_maxPriority)
   apply (rule bind_wp_fwd_skip)
    apply (wpsimp wp: tcbReleaseRemove_valid_queues)
   apply (rule bind_wp_fwd_skip)
    apply (wpsimp wp: threadSet_valid_queues_new threadSet_valid_objs')
    apply (clarsimp simp: obj_at'_def inQ_def valid_tcb'_def tcb_cte_cases_def)
   apply (wpsimp wp: rescheduleRequired_valid_queues)
   apply fastforce
  apply (wpsimp wp: threadSet_valid_queues_new hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (clarsimp simp: obj_at'_def inQ_def)
  done

lemma schedContextDonate_valid_queues'[wp]:
  "schedContextDonate sc t \<lbrace>valid_queues'\<rbrace>"
  apply (clarsimp simp: schedContextDonate_def)
  apply (rule bind_wp_fwd_skip, solves wpsimp)
  apply (rule bind_wp_fwd_skip)
   apply (rule hoare_when_cases, simp)
   apply ((rule bind_wp_fwd_skip
           , wpsimp wp: threadSet_valid_queues' hoare_vcg_imp_lift' simp: inQ_def)
          | wpsimp wp: threadSet_valid_queues' hoare_vcg_imp_lift' simp: inQ_def)+
  done

crunch tcbSchedDequeue
  for ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"

crunch schedContextDonate
  for vrq[wp]: valid_release_queue
  and vrq'[wp]: valid_release_queue'
  (wp: threadSet_vrq_inv threadSet_vrq'_inv simp: crunch_simps)

crunch schedContextDonate
  for ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' ptr"
  (wp: threadSet_cap_to simp: tcb_cte_cases_def)

crunch schedContextDonate
  for valid_irq_handlers'[wp]: "\<lambda>s. valid_irq_handlers' s"
  and valid_mdb'[wp]: valid_mdb'
  (ignore: threadSet
     simp: comp_def valid_mdb'_def crunch_simps
       wp: valid_irq_handlers_lift'' threadSet_ctes_of)

crunch schedContextDonate
  for sch_act_sane[wp]: sch_act_sane
  and sch_act_simple[wp]: sch_act_simple
  and sch_act_not[wp]: "sch_act_not t"
  (wp: crunch_wps simp: crunch_simps rule: sch_act_sane_lift)

crunch schedContextDonate
  for no_0_obj'[wp]: no_0_obj'
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and if_unsafe_then_cap'[wp]: "if_unsafe_then_cap'"
  and valid_global_refs'[wp]: "valid_global_refs'"
  and valid_arch_state'[wp]: "valid_arch_state'"
  and valid_irq_node'[wp]: "\<lambda>s. valid_irq_node' (irq_node' s) s"
  and valid_irq_states'[wp]: "\<lambda>s. valid_irq_states' s"
  and valid_machine_state'[wp]: "\<lambda>s. valid_machine_state' s"
  and ct_not_inQ[wp]: "ct_not_inQ"
  and ct_idle_or_in_cur_domain'[wp]: "ct_idle_or_in_cur_domain'"
  and valid_pde_mappings'[wp]: "\<lambda>s. valid_pde_mappings' s"
  and pspace_domain_valid[wp]: "\<lambda>s. pspace_domain_valid s"
  and irqs_masked'[wp]: "\<lambda>s. irqs_masked' s"
  and cur_tcb'[wp]: "cur_tcb'"
  and urz[wp]: untyped_ranges_zero'
  and valid_dom_schedule'[wp]: valid_dom_schedule'
  and reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and valid_replies' [wp]: valid_replies'
  and pspace_bounded'[wp]: "pspace_bounded'"
  (simp: comp_def tcb_cte_cases_def crunch_simps
     wp: threadSet_not_inQ hoare_vcg_imp_lift' valid_irq_node_lift
         setQueue_cur threadSet_ifunsafe'T threadSet_cur crunch_wps
         cur_tcb_lift valid_dom_schedule'_lift valid_replies'_lift)

lemma schedContextDonate_valid_pspace':
  "\<lbrace>valid_pspace' and tcb_at' tcbPtr\<rbrace> schedContextDonate scPtr tcbPtr \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  by (wpsimp wp: schedContextDonate_valid_objs' simp: valid_pspace'_def)

lemma schedContextDonate_if_live_then_nonz_cap':
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> valid_objs' s \<and>
        ex_nonz_cap_to' tcbPtr s \<and> ex_nonz_cap_to' scPtr s\<rbrace>
   schedContextDonate scPtr tcbPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding schedContextDonate_def
  by (wpsimp wp: threadSet_iflive'T setSchedContext_iflive' hoare_vcg_all_lift threadSet_cap_to'
           simp: conj_ac cong: conj_cong | wp hoare_drop_imps | fastforce simp: tcb_cte_cases_def)+

(* `obj_at' (\<lambda>x. scTCB x \<noteq> Some idle_thread_ptr) scPtr s` is
   needed because sometimes sym_refs doesn't hold in its entirety here. *)
lemma schedContextDonate_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> bound_sc_tcb_at' ((=) None) tcbPtr s \<and>
        ex_nonz_cap_to' scPtr s \<and> ex_nonz_cap_to' tcbPtr s\<rbrace>
   schedContextDonate scPtr tcbPtr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp only: invs'_def)
  apply (rule_tac E="\<lambda>s. sc_at' scPtr s" in hoare_strengthen_pre_via_assert_backward)
   apply (simp only: schedContextDonate_def)
   apply (rule bind_wp[OF _ get_sc_sp'])
   apply (rule_tac hoare_weaken_pre[OF hoare_pre_cont])
   apply (clarsimp simp: obj_at'_def)
  apply (wp schedContextDonate_valid_pspace'
            schedContextDonate_valid_queues schedContextDonate_valid_queues'
            schedContextDonate_if_live_then_nonz_cap')
  apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_sc)
  apply (auto dest!: global'_sc_no_ex_cap
              simp: ko_wp_at'_def obj_at'_def projectKO_eq projectKO_tcb
                    pred_tcb_at'_def)
  done

lemma tcbSchedDequeue_notksQ:
  "tcbSchedDequeue t \<lbrace>\<lambda>s. t' \<notin> set(ksReadyQueues s p)\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp hoare_when_weak_wp)
     apply (rule_tac Q="\<lambda>_ s. t' \<notin> set(ksReadyQueues s p)" in hoare_post_imp)
      apply wpsimp+
  done

lemma tcbSchedDequeue_nonq:
  "\<lbrace>\<lambda>s. if t=t' then valid_queues s else t' \<notin> set (ksReadyQueues s p)\<rbrace>
   tcbSchedDequeue t
   \<lbrace>\<lambda>_ s. t' \<notin> set (ksReadyQueues s p)\<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (wpsimp wp: threadGet_wp)
  apply (case_tac p)
  apply (fastforce simp: valid_queues_def valid_queues_no_bitmap_def obj_at'_def inQ_def
                  split: if_splits)
  done

crunch tcbReleaseRemove
  for not_queued[wp]: "\<lambda>s. t' \<notin> set (ksReadyQueues s p)"
  (wp: crunch_wps simp: crunch_simps)

lemma reprogram_timer_corres:
   "corres dc \<top> \<top>
      (modify (reprogram_timer_update (\<lambda>_. True)))
      (setReprogramTimer True)"
  unfolding setReprogramTimer_def
  by (rule corres_modify) (simp add: state_relation_def swp_def)

lemma release_queue_corres:
  "corres (=) \<top> \<top> (gets release_queue) getReleaseQueue"
  by (simp add: getReleaseQueue_def state_relation_def release_queue_relation_def)

lemma tcbReleaseRemove_corres:
  "t = t' \<Longrightarrow>
   corres dc (pspace_aligned and pspace_distinct and tcb_at t) \<top>
             (tcb_release_remove t) (tcbReleaseRemove t')"
  unfolding tcb_release_remove_def tcbReleaseRemove_def tcb_sched_dequeue_def setReleaseQueue_def
  apply clarsimp
  apply (rule stronger_corres_guard_imp)
    apply (rule_tac r'="(=)" in corres_split)
       apply (rule release_queue_corres)
      apply (rule corres_split)
         apply (rule corres_when)
          apply clarsimp
         apply (rule reprogram_timer_corres)
        apply (rule corres_add_noop_lhs2)
        apply (rule corres_split)
           apply (rule corres_modify)
           apply (auto simp: release_queue_relation_def state_relation_def swp_def)[1]
          apply (rule threadSet_corres_noop; clarsimp simp: tcb_relation_def)
         apply wp
        apply wp
       apply clarsimp
       apply wp
      apply (rule when_wp)
      apply clarsimp
      apply wp
     apply wp
    apply clarsimp
    apply wpsimp
   apply simp
   apply metis
  apply (fastforce simp: state_relation_def tcb_at_cross)
  done

lemma threadSet_valid_queues_no_state:
  "\<lbrace>valid_queues and (\<lambda>s. \<forall>p. t \<notin> set (ksReadyQueues s p))\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: threadSet_def)
  apply wp
   apply (simp add: valid_queues_def valid_queues_no_bitmap_def' pred_tcb_at'_def)
   apply (wp hoare_Ball_helper
             hoare_vcg_all_lift
             setObject_tcb_strongest)[1]
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: valid_queues_def valid_queues_no_bitmap_def' pred_tcb_at'_def)
  apply (clarsimp simp: obj_at'_def)
  done

lemma threadSet_valid_queues'_no_state:
  "(\<And>tcb. tcbQueued tcb = tcbQueued (f tcb)) \<Longrightarrow>
   \<lbrace>valid_queues' and (\<lambda>s. \<forall>p. t \<notin> set (ksReadyQueues s p))\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  apply (simp add: valid_queues'_def threadSet_def obj_at'_real_def
                split del: if_split)
  apply (simp only: imp_conv_disj)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
     apply (wp setObject_ko_wp_at | simp add: objBits_simps')+
    apply (wp getObject_tcb_wp updateObject_default_inv
               | simp split del: if_split)+
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs
                        objBits_simps addToQs_def
             split del: if_split cong: if_cong)
  apply (fastforce simp: projectKOs inQ_def split: if_split_asm)
  done

lemma setQueue_valid_tcbs'[wp]:
  "setQueue qdom prio q \<lbrace>valid_tcbs'\<rbrace>"
  unfolding valid_tcbs'_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
  done

lemma removeFromBitmap_valid_tcbs'[wp]:
  "removeFromBitmap tdom prio \<lbrace>valid_tcbs'\<rbrace>"
  apply (wpsimp simp: valid_tcbs'_def bitmap_fun_defs)
  done

lemma tcbSchedDequeue_valid_tcbs'[wp]:
  "tcbSchedDequeue tcbPtr \<lbrace>valid_tcbs'\<rbrace>"
  apply (clarsimp simp: tcbSchedDequeue_def)
  apply (rule bind_wp_fwd_skip, wpsimp)
  apply (clarsimp simp: when_def)
  apply (rule bind_wp_fwd_skip, wpsimp)+
  apply (wpsimp wp: threadSet_valid_tcbs')
  done

lemma schedContextDonate_corres_helper:
  "(case rv' of SwitchToThread x \<Rightarrow> when (x = t \<or> t = cur) rescheduleRequired
                             | _ \<Rightarrow> when (t = cur) rescheduleRequired) =
   (when (t = cur \<or> (case rv' of SwitchToThread x \<Rightarrow> t = x | _ \<Rightarrow> False)) rescheduleRequired)"
  by (case_tac rv'; clarsimp simp: when_def)

crunch tcbReleaseRemove
  for valid_tcbs'[wp]: valid_tcbs'
  (wp: crunch_wps)

lemma schedContextDonate_corres:
  "corres dc (sc_at scp and tcb_at thread and weak_valid_sched_action and pspace_aligned and
              pspace_distinct and valid_objs and active_scs_valid)
             (valid_objs' and valid_queues and valid_queues' and
              valid_release_queue and valid_release_queue')
             (sched_context_donate scp thread)
             (schedContextDonate scp thread)"
  apply (simp add: test_reschedule_def get_sc_obj_ref_def set_tcb_obj_ref_thread_set
                   schedContextDonate_def sched_context_donate_def schedContextDonate_corres_helper)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split [OF get_sc_corres])
      apply (rule corres_split [OF corres_when2])
          apply (clarsimp simp: sc_relation_def)
         apply (rule corres_assert_opt_assume_l)
         apply (rule corres_split_nor)
            apply (rule_tac x="the (sc_tcb sc)" and x'="the (scTCB sca)" in lift_args_corres)
             apply (rule tcbSchedDequeue_corres)
            apply (clarsimp simp: sc_relation_def)
           apply (rule corres_split_nor)
              apply (rule tcbReleaseRemove_corres)
              apply (clarsimp simp: sc_relation_def)
             apply (rule corres_split_nor)
                apply (rule_tac x="the (sc_tcb sc)" and x'="the (scTCB sca)" in lift_args_corres)
                 apply (rule threadset_corresT)
                   apply (clarsimp simp: tcb_relation_def)
                  apply (clarsimp simp: tcb_cap_cases_def)
                 apply (clarsimp simp: tcb_cte_cases_def)
                apply (clarsimp simp: sc_relation_def)
               apply (rule corres_split_eqr)
                  apply (rule getCurThread_corres)
                 apply (rule_tac r'=sched_act_relation in corres_split)
                    apply (rule getSchedulerAction_corres)
                   apply (rule corres_when)
                    apply (case_tac rv; clarsimp simp: sched_act_relation_def sc_relation_def)
                   apply (rule rescheduleRequired_corres_weak)
                  apply wpsimp
                 apply wpsimp
                apply wpsimp
               apply wpsimp
              apply (wpsimp wp: hoare_drop_imps)
             apply (wpsimp wp: hoare_drop_imps
                               threadSet_valid_release_queue threadSet_valid_release_queue'
                               threadSet_valid_queues_no_state threadSet_valid_queues'_no_state)
            apply (wpsimp | strengthen weak_valid_sched_action_strg)+
           apply (rule_tac Q="\<lambda>_. tcb_at' (the (scTCB sca)) and valid_tcbs' and
                                  valid_queues and valid_queues' and
                                  valid_release_queue and valid_release_queue' and
                                  (\<lambda>s. \<forall>d p. the (scTCB sca) \<notin> set (ksReadyQueues s (d, p)))"
                        in hoare_strengthen_post[rotated])
            apply (clarsimp simp: valid_release_queue'_def obj_at'_def)
           apply (wpsimp wp: tcbReleaseRemove_valid_queues hoare_vcg_all_lift)
          apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
         apply (wpsimp wp: tcbSchedDequeue_valid_queues hoare_vcg_all_lift tcbSchedDequeue_nonq)
        apply (rule corres_split
                   [OF update_sc_no_reply_stack_update_ko_at'_corres
                         [where f'="scTCB_update (\<lambda>_. Some thread)"]
                       threadset_corresT])
                apply (clarsimp simp: sc_relation_def)
               apply clarsimp
              apply (clarsimp simp: objBits_def objBitsKO_def)
             apply clarsimp
            apply (clarsimp simp: tcb_relation_def)
           apply (clarsimp simp: tcb_cap_cases_def)
          apply (clarsimp simp: tcb_cte_cases_def)
         apply wpsimp
        apply wpsimp
       apply (wpsimp wp: hoare_drop_imp)+
   apply (frule (1) valid_objs_ko_at)
   apply (fastforce simp: valid_obj_def valid_sched_context_def valid_bound_obj_def obj_at_def)
  apply (prop_tac "sc_at' scp s' \<and> tcb_at' thread s'")
   apply (fastforce elim: sc_at_cross tcb_at_cross simp: state_relation_def)
  apply clarsimp
  apply (frule valid_objs'_valid_tcbs')
  apply (rule valid_objsE', assumption)
   apply (fastforce simp: obj_at'_def projectKO_eq projectKO_sc)
  apply (clarsimp simp: valid_obj'_def valid_sched_context'_def obj_at'_def projectKOs)
  apply (frule valid_objs'_valid_tcbs')
  apply (fastforce simp: valid_obj'_def valid_tcb'_def)
  done

end
