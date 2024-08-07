(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Schedule_R
imports SchedContext_R InterruptAcc_R
begin

crunch scReleased, getReprogramTimer, getCurTime, getRefills, getReleaseQueue, getRefillSufficient,
         refillReady, isRoundRobin
  for inv[wp]: P

context begin interpretation Arch . (*FIXME: arch-split*)

declare hoare_weak_lift_imp[wp_split del]

(* Levity: added (20090713 10:04:12) *)
declare sts_rel_idle [simp]

crunch refillHeadOverlappingLoop, headInsufficientLoop, setRefillHd
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n T p s)"
  (wp: crunch_wps)

crunch tcbReleaseDequeue
  for sc_at'_n[wp]: "\<lambda>s. Q (sc_at'_n n p s)"
  (simp: crunch_simps wp: crunch_wps)

crunch refillUnblockCheck, refillBudgetCheck, ifCondRefillUnblockCheck, refillBudgetCheckRoundRobin
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. Q (sc_at'_n n p s)"
  and pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and pspace_bounded'[wp]: pspace_bounded'
  and pspace_canonical'[wp]: pspace_canonical'
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
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksCurdomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and untyped_ranges_zero'[wp]: untyped_ranges_zero'
  and cur_tcb'[wp]: cur_tcb'
  and ct_not_inQ[wp]: ct_not_inQ
  and valid_dom_schedule'[wp]: valid_dom_schedule'
  and ksCurSc[wp]: "\<lambda>s. P (ksCurSc s)"
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  (wp: crunch_wps hoare_vcg_all_lift valid_dom_schedule'_lift simp: crunch_simps refillSingle_def)

crunch commitTime, refillNew, refillUpdate
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps simp: crunch_simps)

end

global_interpretation refillPopHead: typ_at_all_props' "refillPopHead scPtr"
  by typ_at_props'

global_interpretation updateRefillTl: typ_at_all_props' "updateRefillTl scPtr f"
  by typ_at_props'

global_interpretation chargeEntireHeadRefill: typ_at_all_props' "chargeEntireHeadRefill scPtr usage"
  by typ_at_props'

global_interpretation handleOverrun: typ_at_all_props' "handleOverrun scPtr usage"
  by typ_at_props'

global_interpretation scheduleUsed: typ_at_all_props' "scheduleUsed scPtr new"
  by typ_at_props'

global_interpretation updateRefillHd: typ_at_all_props' "updateRefillHd scPtr f"
  by typ_at_props'

global_interpretation mergeOverlappingRefills: typ_at_all_props' "mergeOverlappingRefills scPtr"
  by typ_at_props'

global_interpretation setRefillHd: typ_at_all_props' "setRefillHd scPtr v"
  by typ_at_props'

global_interpretation mergeNonoverlappingHeadRefill: typ_at_all_props' "mergeNonoverlappingHeadRefill scPtr"
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

context begin interpretation Arch . (*FIXME: arch-split*)

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

crunch set_vm_root
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  (simp: crunch_simps)

lemma arch_switchToThread_corres:
  "corres dc (valid_arch_state and valid_objs and pspace_aligned and pspace_distinct
                and valid_vspace_objs and st_tcb_at runnable t)
             (no_0_obj')
             (arch_switch_to_thread t) (Arch.switchToThread t)"
  apply (simp add: arch_switch_to_thread_def RISCV64_H.switchToThread_def)
  apply (rule corres_guard_imp)
    apply (rule setVMRoot_corres[OF refl])
   apply (clarsimp simp: st_tcb_at_tcb_at valid_arch_state_asid_table
                         valid_arch_state_global_arch_objs)
  apply simp
  done

lemma schedule_choose_new_thread_sched_act_rct[wp]:
  "\<lbrace>\<top>\<rbrace> schedule_choose_new_thread \<lbrace>\<lambda>rs s. scheduler_action s = resume_cur_thread\<rbrace>"
  unfolding schedule_choose_new_thread_def
  by wp

\<comment> \<open>This proof shares many similarities with the proof of @{thm tcbSchedEnqueue_corres}\<close>
lemma tcbSchedAppend_corres:
  "tcb_ptr = tcbPtr \<Longrightarrow>
   corres dc
     (st_tcb_at runnable tcb_ptr and in_correct_ready_q and ready_qs_distinct
      and not_in_release_q tcb_ptr and ready_or_release and pspace_aligned and pspace_distinct)
     (sym_heap_sched_pointers and valid_sched_pointers and valid_tcbs')
     (tcb_sched_action tcb_sched_append tcb_ptr) (tcbSchedAppend tcbPtr)"
  supply if_split[split del]
  apply (rule_tac Q'="st_tcb_at' runnable' tcbPtr" in corres_cross_add_guard)
   apply (fastforce intro!: st_tcb_at_runnable_cross simp: vs_all_heap_simps obj_at_def is_tcb_def)
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest: pspace_distinct_cross)
  apply (clarsimp simp: tcb_sched_action_def tcb_sched_append_def get_tcb_queue_def
                        tcbSchedAppend_def getQueue_def unless_def when_def)
  apply (rule corres_symb_exec_l[OF _ _ thread_get_sp]; (solves wpsimp)?)
  apply (rename_tac domain)
  apply (rule corres_symb_exec_l[OF _ _ thread_get_sp]; (solves wpsimp)?)
  apply (rename_tac priority)
  apply (rule corres_symb_exec_l[OF _ _ gets_sp]; (solves wpsimp)?)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (fastforce intro: ready_or_release_cross)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (fastforce dest: state_relation_release_queue_relation in_release_q_tcbInReleaseQueue_eq)
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro: ksReadyQueues_asrt_cross)
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro: ksReleaseQueue_asrt_cross)
  apply (rule corres_symb_exec_r[OF _ isRunnable_sp]; wpsimp?)
  apply (rule corres_symb_exec_r[OF _ assert_sp, rotated]; (solves wpsimp)?)
   apply wpsimp
   apply (fastforce simp: st_tcb_at'_def runnable_eq_active' obj_at'_def)
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; (solves wpsimp)?)
  apply (subst if_distrib[where f="set_tcb_queue domain prio" for domain prio])
  apply (rule corres_if_strong')
    apply (rule arg_cong_Not)
    apply (fastforce dest!: state_relation_ready_queues_relation
                            in_ready_q_tcbQueued_eq[where t=tcbPtr]
                      simp: obj_at'_def opt_pred_def opt_map_def in_correct_ready_q_def
                            vs_all_heap_simps obj_at_def in_ready_q_def)
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
  apply (rule corres_split_skip)
     apply wpsimp
    apply (wpsimp wp: hoare_vcg_if_lift hoare_vcg_ex_lift)
   apply (corres corres: addToBitmap_if_null_noop_corres)

  apply (rule_tac F="tdom = domain \<and> prio = priority" in corres_req)
   apply (fastforce dest: pspace_relation_tcb_domain_priority state_relation_pspace_relation
                    simp: obj_at_def obj_at'_def)
  apply clarsimp

  apply (rule corres_from_valid_det)
    apply (fastforce intro: det_wp_modify det_wp_pre simp: set_tcb_queue_def)
   apply (wpsimp simp: tcbQueueAppend_def wp: hoare_vcg_imp_lift' hoare_vcg_if_lift2)
   apply (clarsimp simp: ex_abs_def split: if_splits)
   apply (frule state_relation_ready_queues_relation)
   apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
   apply (drule_tac x="tcbDomain tcb" in spec)
   apply (drule_tac x="tcbPriority tcb" in spec)
   subgoal by (auto dest!: obj_at'_tcbQueueEnd_ksReadyQueues simp: obj_at'_def)

  apply (rename_tac s rv t)
  apply (clarsimp simp: state_relation_def)
  apply (intro hoare_vcg_conj_lift_pre_fix;
         (solves \<open>frule singleton_eqD, frule set_tcb_queue_projs_inv, wpsimp simp: swp_def\<close>)?)

   apply (find_goal \<open>match conclusion in "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_. release_queue_relation t\<rbrace>" for t \<Rightarrow> \<open>-\<close>\<close>)
   apply (frule_tac d=domain and p=priority in ready_or_release_disjoint)
   apply (drule set_tcb_queue_projs_inv)
   apply (wpsimp wp: tcbQueueAppend_list_queue_relation_other hoare_vcg_ex_lift
                     threadSet_sched_pointers
               simp: release_queue_relation_def
          | wps)+
   apply (rule_tac x="ready_queues s (tcbDomain tcba) (tcbPriority tcb)" in exI)
   apply (auto simp: ready_queues_relation_def ready_queue_relation_def Let_def)[1]

  \<comment> \<open>ready_queues_relation\<close>
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
  apply (intro hoare_allI)
  apply (drule singleton_eqD)
  apply (drule set_tcb_queue_new_state)
  apply (intro hoare_vcg_conj_lift_pre_fix)

     apply (find_goal \<open>match conclusion in "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_ s. maxDomain < d \<longrightarrow> _\<rbrace>" for d \<Rightarrow> \<open>-\<close>\<close>)
     apply (wpsimp wp: threadSet_wp getTCB_wp simp: setQueue_def tcbQueueAppend_def)
     apply (frule valid_tcbs'_maxDomain[where t=tcbPtr])
      apply fastforce
     subgoal by (force simp: obj_at'_def tcbQueueEmpty_def split: if_split)

    apply (find_goal \<open>match conclusion in "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_ s. maxPriority < d \<longrightarrow> _\<rbrace>" for d \<Rightarrow> \<open>-\<close>\<close>)
    apply (wpsimp wp: threadSet_wp getTCB_wp simp: setQueue_def tcbQueueAppend_def)
    apply (frule valid_tcbs'_maxPriority[where t=tcbPtr])
     apply fastforce
    subgoal by (force simp: obj_at'_def tcbQueueEmpty_def split: if_split)

   apply (find_goal \<open>match conclusion in "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_ s. list_queue_relation _ _ _ _ \<rbrace>" \<Rightarrow> \<open>-\<close>\<close>)
   apply (clarsimp simp: obj_at_def)
   apply (case_tac "d \<noteq> tcb_domain tcb \<or> p \<noteq> tcb_priority tcb")
    apply (wpsimp wp: tcbQueueAppend_list_queue_relation_other setQueue_ksReadyQueues_other
                      threadSet_sched_pointers hoare_vcg_ex_lift
           | wps)+
    apply (intro conjI)
      subgoal by fastforce
     apply (rule_tac x="ready_queues s (tcb_domain tcb) (tcb_priority tcb)" in exI)
     apply (auto dest!: in_correct_ready_qD simp: ready_queues_disjoint
                 split: if_splits)[1]
    apply fastforce
   apply ((wpsimp wp: tcbQueueAppend_list_queue_relation threadSet_sched_pointers | wps)+)[1]
   apply (fastforce dest!: valid_sched_pointersD[where t=tcbPtr]
                     simp: in_opt_pred opt_map_red obj_at'_def)

  apply (rule hoare_allI, rename_tac t')
  apply (case_tac "d \<noteq> domain \<or> p \<noteq> priority")
   apply (wpsimp wp: tcbQueued_update_inQ_other hoare_vcg_disj_lift
               simp: opt_pred_disj[simplified pred_disj_def, symmetric] simp_del: disj_not1)
   apply (clarsimp simp: opt_map_def opt_pred_def obj_at'_def split: option.splits if_splits)
  apply (case_tac "t' = tcbPtr")
   apply (wpsimp wp: tcbQueued_True_makes_inQ)
   apply (clarsimp simp: opt_pred_def opt_map_def obj_at'_def)
  apply (wpsimp wp: threadSet_opt_pred_other)
  done

lemma tcbQueueAppend_valid_objs'[wp]:
  "\<lbrace>\<lambda>s. valid_objs' s \<and> tcb_at' tcbPtr s \<and> (\<forall>end. tcbQueueEnd queue = Some end \<longrightarrow> tcb_at' end s)\<rbrace>
   tcbQueueAppend queue tcbPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding tcbQueueAppend_def
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')
  apply (clarsimp simp: tcbQueueEmpty_def valid_bound_tcb'_def split: option.splits)
  done

lemma tcbQueueInsert_valid_objs'[wp]:
  "\<lbrace>valid_objs' and tcb_at' tcbPtr\<rbrace> tcbQueueInsert tcbPtr afterPtr \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding tcbQueueInsert_def
  apply (wpsimp wp: getTCB_wp hoare_vcg_if_lift2 hoare_vcg_imp_lift')
  apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
  apply (clarsimp simp: valid_tcb'_def)
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
  apply (force dest!: obj_at'_tcbQueueEnd_ksReadyQueues simp: tcbQueueEmpty_def)
  done

crunch tcbSchedEnqueue, tcbSchedAppend, tcbSchedDequeue
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
  (wp: threadSet_pred_tcb_no_state simp: unless_def tcb_to_itcb'_def)

(* FIXME move *)
lemmas obj_at'_conjI = obj_at_conj'

crunch tcbSchedAppend, tcbSchedDequeue, tcbSchedEnqueue
  for tcb_at'[wp]: "tcb_at' t"
  and cap_to'[wp]: "ex_nonz_cap_to' p"
  and ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"
  and tcbInReleaseQueue[wp]: "\<lambda>s. P (tcbInReleaseQueue |< tcbs_of' s)"
  and ifunsafe'[wp]: if_unsafe_then_cap'
  (wp: crunch_wps simp: crunch_simps)

lemma tcbSchedAppend_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedAppend tcbPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding tcbSchedAppend_def
  apply (wpsimp wp: tcbQueueAppend_if_live_then_nonz_cap' threadGet_wp
                    threadSet_sched_pointers hoare_vcg_all_lift hoare_vcg_imp_lift'
              simp: bitmap_fun_defs)
  apply (frule_tac p=tcbPtr in if_live_then_nonz_capE')
   apply (fastforce simp: ko_wp_at'_def st_tcb_at'_def obj_at'_def runnable_eq_active')
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
  apply (intro conjI impI allI)
   apply (erule if_live_then_nonz_capE')
   apply (drule_tac x="tcbDomain tcb" in spec)
   apply (drule_tac x="tcbPriority tcb" in spec)
   apply clarsimp
   apply (frule (3) obj_at'_tcbQueueEnd_ksReadyQueues)
   apply (frule tcbQueueHead_iff_tcbQueueEnd)
   apply (clarsimp simp: ko_wp_at'_def inQ_def obj_at'_def tcbQueueEmpty_def)
  apply fastforce
  done

lemma tcbSchedDequeue_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and valid_objs' and sym_heap_sched_pointers\<rbrace>
   tcbSchedDequeue tcbPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wpsimp wp: tcbQueueRemove_if_live_then_nonz_cap' threadGet_wp threadSet_valid_objs')
  apply (fastforce elim: if_live_then_nonz_capE' simp: obj_at'_def ko_wp_at'_def)
  done

lemma tcbSchedEnqueue_vms'[wp]:
  "tcbSchedEnqueue t \<lbrace>valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift tcbSchedEnqueue_ksMachine)
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
  including no_pre
  apply (wp hoare_weak_lift_imp hoare_vcg_disj_lift)
  apply simp+
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

lemma tcbQueueInsert_valid_mdb':
  "\<lbrace>valid_mdb' and tcb_at' tcbPtr and valid_tcbs'\<rbrace> tcbQueueInsert tcbPtr afterPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding tcbQueueInsert_def
  apply (wpsimp wp: getTCB_wp)
  apply (frule (1) ko_at'_valid_tcbs'_valid_tcb')
  apply (clarsimp simp: valid_tcb'_def valid_bound_tcb'_def)
  done

lemma tcbInReleaseQueue_update_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and tcb_at' tcbPtr\<rbrace> threadSet (tcbInReleaseQueue_update f) tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (wpsimp wp: threadSet_mdb')
  apply (fastforce simp: obj_at'_def valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

lemma tcbQueued_update_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and tcb_at' tcbPtr\<rbrace> threadSet (tcbQueued_update f) tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (wpsimp wp: threadSet_mdb')
  apply (fastforce simp: obj_at'_def valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

lemma tcbSchedEnqueue_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and valid_tcbs' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedEnqueue tcbPtr
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (clarsimp simp: tcbSchedEnqueue_def setQueue_def)
  apply (wpsimp wp: tcbQueuePrepend_valid_mdb' threadGet_wp simp: bitmap_fun_defs)
  apply normalise_obj_at'
  apply (fastforce dest!: obj_at'_tcbQueueHead_ksReadyQueues
                    simp: ready_queue_relation_def ksReadyQueues_asrt_def)
  done

lemma tcbSchedEnqueue_invs'[wp]:
  "tcbSchedEnqueue t \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_pspace'_def valid_dom_schedule'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
                    untyped_ranges_zero_lift valid_replies'_lift
              simp: cteCaps_of_def o_def)
  done

lemma tcbSchedAppend_vms'[wp]:
  "tcbSchedAppend t \<lbrace>valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

crunch tcbSchedDequeue, tcbSchedAppend
  for arch'[wp]: "\<lambda>s. P (ksArchState s)"

lemma tcbSchedAppend_valid_bitmapQ[wp]:
  "\<lbrace>valid_bitmaps\<rbrace> tcbSchedAppend tcbPtr \<lbrace>\<lambda>_. valid_bitmapQ\<rbrace>"
  supply if_split[split del]
  unfolding tcbSchedAppend_def
  apply (wpsimp simp: tcbQueueAppend_def
                  wp: setQueue_valid_bitmapQ' addToBitmap_valid_bitmapQ_except addToBitmap_bitmapQ
                      threadGet_wp hoare_vcg_if_lift2 threadSet_bitmapQ)
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
  apply (fastforce dest: obj_at'_tcbQueueEnd_ksReadyQueues
                   simp: ready_queue_relation_def ksReadyQueues_asrt_def)
  done

lemma tcbSchedAppend_valid_bitmaps[wp]:
  "tcbSchedAppend tcbPtr \<lbrace>valid_bitmaps\<rbrace>"
  unfolding valid_bitmaps_def
  apply wpsimp
  apply (clarsimp simp: valid_bitmaps_def)
  done

lemma tcbSchedAppend_invs'[wp]:
  "tcbSchedAppend t \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_pspace'_def valid_dom_schedule'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
                    untyped_ranges_zero_lift valid_replies'_lift
              simp: cteCaps_of_def o_def)
  done

lemma tcb_at'_has_tcbDomain:
 "tcb_at' t s \<Longrightarrow> \<exists>p. obj_at' (\<lambda>tcb. tcbDomain tcb = p) t s"
 by (clarsimp simp add: obj_at'_def)

lemma tcbSchedDequeue_vms'[wp]:
  "tcbSchedDequeue t \<lbrace>valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

lemma tcbSchedDequeue_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and valid_objs'\<rbrace> tcbSchedDequeue tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding tcbSchedDequeue_def
  by (wpsimp simp: bitmap_fun_defs setQueue_def wp: tcbQueueRemove_valid_mdb' threadGet_wp)

lemma tcbSchedDequeue_invs'[wp]:
  "tcbSchedDequeue t \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_pspace'_def valid_dom_schedule'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
                    untyped_ranges_zero_lift valid_replies'_lift
              simp: cteCaps_of_def o_def)
  done

defs idleThreadNotQueued_def:
  "idleThreadNotQueued s \<equiv> obj_at' (Not \<circ> tcbQueued) (ksIdleThread s) s"

lemma idle_thread_not_queued:
  "\<lbrakk>valid_idle s; valid_ready_qs s\<rbrakk> \<Longrightarrow> not_queued (idle_thread s) s"
  apply (clarsimp simp: valid_ready_qs_def vs_all_heap_simps in_ready_q_def)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (drule_tac x="idle_thread s" in bspec)
   apply fastforce
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def vs_all_heap_simps)
  done

lemma valid_idle_tcb_at:
  "valid_idle s \<Longrightarrow> tcb_at (idle_thread s) s"
  by (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def is_tcb_def)

lemma setCurThread_corres:
  "corres dc (pspace_aligned and pspace_distinct and valid_idle and valid_ready_qs) \<top>
             (modify (cur_thread_update (\<lambda>_. t))) (setCurThread t)"
  apply (clarsimp simp: setCurThread_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (clarsimp simp: idleThreadNotQueued_def)
   apply (frule (1) idle_thread_not_queued)
   apply (frule state_relation_ready_queues_relation)
   apply (frule state_relation_pspace_relation)
   apply (frule state_relation_idle_thread)
   apply (frule valid_idle_tcb_at)
   apply (frule (3) tcb_at_cross)
   apply (fastforce dest!: in_ready_q_tcbQueued_eq[THEN arg_cong_Not, THEN iffD1]
                     simp: obj_at'_def opt_pred_def opt_map_def)
  apply (rule corres_modify)
  apply (simp add: state_relation_def swp_def)
  done

lemma arch_switch_thread_tcb_at' [wp]: "\<lbrace>tcb_at' t\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  by (unfold RISCV64_H.switchToThread_def, wp)

crunch "switchToThread"
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"

crunch setVMRoot
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t'"
  (simp: crunch_simps wp: crunch_wps)

lemma Arch_switchToThread_pred_tcb'[wp]:
  "Arch.switchToThread t \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
proof -
  have pos: "\<And>P t t'. Arch.switchToThread t \<lbrace>pred_tcb_at' proj P t'\<rbrace>"
    by (wpsimp wp: setVMRoot_obj_at simp: RISCV64_H.switchToThread_def)
  show ?thesis
    apply (rule P_bool_lift [OF pos])
    by (rule lift_neg_pred_tcb_at' [OF ArchThreadDecls_H_RISCV64_H_switchToThread_typ_at' pos])
qed

crunch storeWordUser, setVMRoot, asUser, storeWordUser, Arch.switchToThread
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  and tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
  and tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
  and sym_heap_sched_poinetsr[wp]: sym_heap_sched_pointers
  and valid_objs'[wp]: valid_objs'
  (wp: crunch_wps sym_heap_sched_pointers_lift simp: crunch_simps)

lemma ready_qs_distinct_lift:
  assumes r: "\<And>P. f \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace>"
  shows "f \<lbrace>ready_qs_distinct\<rbrace>"
  unfolding ready_qs_distinct_def
  apply (rule hoare_pre)
   apply (wps assms | wpsimp)+
  done

lemma valid_ready_qs_in_correct_ready_q[elim!]:
  "valid_ready_qs s \<Longrightarrow> in_correct_ready_q s"
  by (simp add: valid_ready_qs_def in_correct_ready_q_def)

lemma valid_ready_qs_ready_qs_distinct[elim!]:
  "valid_ready_qs s \<Longrightarrow> ready_qs_distinct s"
  by (simp add: valid_ready_qs_def ready_qs_distinct_def)

crunch arch_switch_to_thread, arch_switch_to_idle_thread
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  and in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  and valid_idle[wp]: valid_idle
  (rule: in_correct_ready_q_lift ready_qs_distinct_lift)

lemma switchToThread_corres:
  "corres dc
     (valid_arch_state and valid_objs and valid_idle
      and valid_vspace_objs and pspace_aligned and pspace_distinct and valid_ready_qs
      and valid_vs_lookup and valid_global_objs
      and unique_table_refs and st_tcb_at runnable t and ready_or_release)
     (no_0_obj' and sym_heap_sched_pointers and valid_objs')
     (switch_to_thread t) (switchToThread t)"
  (is "corres _ ?PA ?PH _ _")
proof -
  have mainpart: "corres dc (?PA) (?PH)
     (do y \<leftarrow> arch_switch_to_thread t;
         y \<leftarrow> (tcb_sched_action tcb_sched_dequeue t);
         modify (cur_thread_update (\<lambda>_. t))
      od)
     (do y \<leftarrow> Arch.switchToThread t;
         y \<leftarrow> tcbSchedDequeue t;
         setCurThread t
      od)"
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF arch_switchToThread_corres])
        apply (rule corres_split[OF tcbSchedDequeue_corres setCurThread_corres])
         apply (wpsimp wp: tcb_sched_dequeue_valid_ready_qs | clarsimp simp: st_tcb_at_tcb_at)+
     apply fastforce
    apply fastforce
    done

  show ?thesis
    apply -
    apply (rule_tac Q'="st_tcb_at' runnable' t" in corres_cross_add_guard)
     apply (fastforce intro!: st_tcb_at_runnable_cross)
    apply (simp add: switch_to_thread_def Thread_H.switchToThread_def)
    apply add_ready_qs_runnable
    apply (rule corres_symb_exec_l[OF _ _ get_sp])
      apply (rule corres_symb_exec_r[OF _ isRunnable_sp])
        apply (rule corres_symb_exec_r[OF _ assert_sp])
          apply (rule corres_stateAssert_add_assertion[rotated])
           apply (fastforce intro: ksReadyQueues_asrt_cross)
          apply (rule corres_stateAssert_add_assertion)
           apply (intro corres_symb_exec_l[OF _ _ assert_sp])
             apply (rule corres_guard_imp[OF mainpart])
              apply (wpsimp
                     | fastforce simp: st_tcb_at'_def obj_at'_def runnable_eq_active'
                                 dest: st_tcb_at_tcb_at [THEN get_tcb_at])+
    done
qed

lemma arch_switchToIdleThread_corres:
  "corres dc
     (valid_arch_state and valid_objs and pspace_aligned and pspace_distinct
      and valid_vspace_objs and valid_idle)
     no_0_obj'
     arch_switch_to_idle_thread Arch.switchToIdleThread"
  apply (simp add: arch_switch_to_idle_thread_def RISCV64_H.switchToIdleThread_def)
  apply add_valid_idle'
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (clarsimp simp: valid_idle'_asrt_def)
  apply (corresKsimp corres: getIdleThread_corres setVMRoot_corres)
  apply (clarsimp simp: valid_idle_def valid_idle'_def pred_tcb_at_def obj_at_def is_tcb
                        valid_arch_state_asid_table valid_arch_state_global_arch_objs)
  done

lemma ready_qs_runnable_ksMachineState_update[simp]:
  "ready_qs_runnable (ksMachineState_update f s) = ready_qs_runnable s"
  by (clarsimp simp: ready_qs_runnable_def)

crunch setVMRoot
  for ready_qs_runnable[wp]: ready_qs_runnable
  (simp: crunch_simps wp: crunch_wps)

lemma switchToIdleThread_corres:
  "corres dc (invs and valid_ready_qs) invs' switch_to_idle_thread switchToIdleThread"
  apply add_ready_qs_runnable
  apply add_valid_idle'
  apply (simp add: switch_to_idle_thread_def Thread_H.switchToIdleThread_def)
  apply (rule corres_stateAssert_ignore)
   apply clarsimp
  apply (rule corres_stateAssert_ignore)
   apply (clarsimp simp: valid_idle'_asrt_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getIdleThread_corres])
      apply (rule corres_split[OF arch_switchToIdleThread_corres])
        apply clarsimp
        apply (rule setCurThread_corres)
       apply (wpsimp simp: switchToIdleThread_def)+
   apply fastforce
  apply fastforce
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
  "setCurThread t \<lbrace>invs'\<rbrace>"
  apply (simp add: setCurThread_def)
  apply wp
  apply (clarsimp simp add: invs'_def cur_tcb'_def sch_act_wf ct_in_state'_def
                            state_refs_of'_def ps_clear_def valid_irq_node'_def
                            valid_bitmaps_def bitmapQ_defs valid_dom_schedule'_def
                      cong: option.case_cong)
  done

crunch Arch.switchToThread
  for pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and pspace_bounded'[wp]: pspace_bounded'
  (simp: crunch_simps wp: crunch_wps)

lemma Arch_switchToThread_invs[wp]:
  "Arch.switchToThread t \<lbrace>invs'\<rbrace>"
  apply (simp add: RISCV64_H.switchToThread_def)
  apply (wp; auto)
  done

crunch "Arch.switchToThread"
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  (simp: crunch_simps wp: crunch_wps)

lemma Arch_swichToThread_tcbDomain_triv[wp]:
  "\<lbrace> obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t' \<rbrace> Arch.switchToThread t \<lbrace> \<lambda>_. obj_at'  (\<lambda>tcb. P (tcbDomain tcb)) t' \<rbrace>"
  apply (clarsimp simp: RISCV64_H.switchToThread_def storeWordUser_def)
  apply (wp hoare_drop_imp | simp)+
  done

lemma Arch_swichToThread_tcbPriority_triv[wp]:
  "\<lbrace> obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t' \<rbrace> Arch.switchToThread t \<lbrace> \<lambda>_. obj_at'  (\<lambda>tcb. P (tcbPriority tcb)) t' \<rbrace>"
  apply (clarsimp simp: RISCV64_H.switchToThread_def storeWordUser_def)
  apply (wp hoare_drop_imp | simp)+
  done

lemma Arch_switchToThread_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>_. tcb_in_cur_domain' t' \<rbrace>"
  apply (rule tcb_in_cur_domain'_lift)
   apply wp+
  done

lemma tcbSchedDequeue_not_tcbQueued:
  "\<lbrace>\<top>\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. \<not> tcbQueued tcb) t\<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (wpsimp wp: hoare_vcg_if_lift2 threadGet_wp)
  by (clarsimp simp: obj_at'_def)

lemma asUser_tcbState_inv[wp]:
  "asUser t m \<lbrace>obj_at' (P \<circ> tcbState) t\<rbrace>"
  apply (simp add: asUser_def tcb_in_cur_domain'_def threadGet_def)
  apply (wp threadSet_obj_at'_strongish getObject_tcb_wp | wpc | simp | clarsimp simp: obj_at'_def)+
  done

lemma Arch_switchToThread_obj_at[wp]:
  "Arch.switchToThread t \<lbrace>obj_at' (P \<circ> tcbState) t\<rbrace>"
  by (wpsimp simp: RISCV64_H.switchToThread_def)

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

lemma asUser_valid_irq_node'[wp]:
  "\<lbrace>\<lambda>s. valid_irq_node' (irq_node' s) s\<rbrace> asUser t (setRegister f r)
          \<lbrace>\<lambda>_ s. valid_irq_node' (irq_node' s) s\<rbrace>"
  apply (rule_tac valid_irq_node_lift)
   apply (simp add: asUser_def)
   apply (wpsimp wp: crunch_wps)+
  done

crunch asUser
  for irq_masked'_helper: "\<lambda>s. P (intStateIRQTable (ksInterruptState s))"
(wp: crunch_wps simp: crunch_simps)

lemma asUser_irq_masked'[wp]:
  "\<lbrace>irqs_masked'\<rbrace> asUser t (setRegister f r)
          \<lbrace>\<lambda>_ . irqs_masked'\<rbrace>"
  apply (rule irqs_masked_lift)
  apply (rule asUser_irq_masked'_helper)
  done

lemma asUser_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> asUser t (setRegister f r)
          \<lbrace>\<lambda>_ . ct_not_inQ\<rbrace>"
  apply (clarsimp simp: submonad_asUser.fn_is_sm submonad_fn_def)
  apply (rule bind_wp)+
     prefer 4
     apply (rule stateAssert_sp)
    prefer 3
    apply (rule gets_inv)
   defer
   apply (rule select_f_inv)
  apply (case_tac rv; simp)
  apply (clarsimp simp: asUser_replace_def obj_at'_def fun_upd_def
                  split: option.split kernel_object.split)
  apply wp
  apply (clarsimp simp: ct_not_inQ_def obj_at'_def objBitsKO_def ps_clear_def dom_def)
  apply (rule conjI; clarsimp; blast)
  done

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

lemma asUser_utr[wp]:
  "\<lbrace>untyped_ranges_zero'\<rbrace> asUser f t \<lbrace>\<lambda>_. untyped_ranges_zero'\<rbrace>"
  apply (simp add: cteCaps_of_def)
  apply (rule hoare_pre, wp untyped_ranges_zero_lift)
  apply (simp add: o_def)
  done

lemma switchToThread_invs'_helper:
  "do y \<leftarrow> RISCV64_H.switchToThread t;
      y \<leftarrow> tcbSchedDequeue t;
      setCurThread t
   od
   \<lbrace>invs'\<rbrace>"
  by (wp setCurThread_invs' Arch_switchToThread_pred_tcb')

lemma switchToThread_invs'[wp]:
  "switchToThread t \<lbrace>invs'\<rbrace>"
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
  (simp: crunch_simps wp: crunch_wps)

crunch switchToThread
  for cap_to'[wp]: "ex_nonz_cap_to' p"
  (simp: crunch_simps)

lemma no_longer_inQ[simp]:
  "\<not> inQ d p (tcbQueued_update (\<lambda>x. False) tcb)"
  by (simp add: inQ_def)

lemma iflive_inQ_nonz_cap_strg:
  "if_live_then_nonz_cap' s \<and> obj_at' (inQ d prio) t s
          \<longrightarrow> ex_nonz_cap_to' t s"
  by (clarsimp simp: obj_at'_real_def inQ_def
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
   \<Longrightarrow> (ksReadyQueuesL1Bitmap s d = 0) = (\<forall>p. tcbQueueEmpty (ksReadyQueues s (d,p)))"
  apply (cases "ksReadyQueuesL1Bitmap s d = 0")
   apply (force simp add: bitmapQ_def valid_bitmapQ_def tcbQueueEmpty_def)
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
    apply (simp add: word_size wordRadix_def')
    apply (drule (1) bitmapQ_no_L1_orphansD[where d=d and i="word_log2 _"])
    apply (simp add: l2BitmapSize_def')
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
                    simp: wordBits_def numPriorities_def word_size wordRadix_def' l2BitmapSize_def')
  apply (erule word_log2_highest)
  done

lemma bitmapQ_ksReadyQueuesI:
  "\<lbrakk> bitmapQ d p s ; valid_bitmapQ s \<rbrakk> \<Longrightarrow> \<not> tcbQueueEmpty (ksReadyQueues s (d, p))"
  unfolding valid_bitmapQ_def by simp

lemma getReadyQueuesL2Bitmap_inv[wp]:
  "\<lbrace> P \<rbrace> getReadyQueuesL2Bitmap d i \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding getReadyQueuesL2Bitmap_def by wp

lemma switchToThread_lookupBitmapPriority_wp:
  "\<lbrace>invs' and tcb_at' t\<rbrace>
   ThreadDecls_H.switchToThread t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp switchToThread_invs'_helper)
  apply (fastforce simp: st_tcb_at'_def obj_at_simps invs'_def ready_qs_runnable_def)
  done

lemma switchToIdleThread_invs':
  "switchToIdleThread \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: Thread_H.switchToIdleThread_def RISCV64_H.switchToIdleThread_def)
  apply (wpsimp wp: setCurThread_invs')
  done

crunch "Arch.switchToIdleThread"
  for obj_at'[wp]: "\<lambda>s. obj_at' P t s"


declare hoare_weak_lift_imp_conj[wp_split del]

lemma setCurThread_const:
  "\<lbrace>\<lambda>_. P t \<rbrace> setCurThread t \<lbrace>\<lambda>_ s. P (ksCurThread s) \<rbrace>"
  by (simp add: setCurThread_def | wp)+



crunch switchToIdleThread
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"
crunch switchToThread
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"

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
  "corres dc
     (valid_arch_state and valid_objs and valid_vspace_objs and pspace_aligned and pspace_distinct
      and valid_vs_lookup and valid_global_objs and unique_table_refs
      and schedulable t and valid_ready_qs and ready_or_release and valid_idle)
     (no_0_obj' and sym_heap_sched_pointers and valid_objs')
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

lemma enumPrio_word_div:
  fixes v :: "8 word"
  assumes vlt: "unat v \<le> unat maxPriority"
  shows "\<exists>xs ys. enumPrio = xs @ [v] @ ys \<and> (\<forall>x\<in>set xs. x < v) \<and> (\<forall>y\<in>set ys. v < y)"
  apply (subst upto_enum_word)
  apply (subst upt_add_eq_append'[where j="unat v"])
    apply simp
   apply (rule le_SucI)
   apply (rule vlt)
  apply (simp only: upt_conv_Cons vlt[simplified less_Suc_eq_le[symmetric]])
  apply (intro exI conjI)
    apply fastforce
   apply clarsimp
   apply (drule of_nat_mono_maybe[rotated, where 'a="8"])
    apply (fastforce simp: vlt)
   apply simp
  apply (clarsimp simp: Suc_le_eq)
  apply (erule disjE)
   apply (drule of_nat_mono_maybe[rotated, where 'a="8"])
    apply (simp add: maxPriority_def numPriorities_def)
   apply (clarsimp simp: unat_of_nat_eq)
  apply (erule conjE)
  apply (drule_tac y="unat v" and x="x" in of_nat_mono_maybe[rotated, where 'a="8"])
   apply (simp add: maxPriority_def numPriorities_def)+
  done

lemma curDomain_corres: "corres (=) \<top> \<top> (gets cur_domain) (curDomain)"
  by (simp add: curDomain_def state_relation_def)

lemma curDomain_corres':
  "corres (=) \<top> (\<lambda>s. ksCurDomain s \<le> maxDomain)
    (gets cur_domain) (if 1 < numDomains then curDomain else return 0)"
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
  using bitmapQ_from_bitmap_lookup bitmapQ_ksReadyQueuesI
  apply blast
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
    apply (clarsimp simp: opt_map_def)
    apply (clarsimp simp: tcb_relation_cut_def tcb_relation_def thread_state_relation_def)
    apply (case_tac "tcb_state b"; simp add: runnable_def)
   apply clarsimp
  apply clarsimp
  done

lemma tcbInReleaseQueue_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and tcb_at t and not_in_release_q t)
             (\<lambda>s'. pred_map (\<lambda>tcb. \<not> tcbInReleaseQueue tcb) (tcbs_of' s') t)"
  apply (clarsimp simp: cross_rel_def)
  apply (clarsimp simp: pred_map_def cross_rel_def obj_at'_def obj_at_def is_tcb)
  apply (frule state_relation_pspace_relation)
  apply (frule (2) tcb_at_cross)
   apply (fastforce simp: obj_at_def is_tcb)
  apply normalise_obj_at'
  apply (rename_tac tcb')
  apply (rule_tac x=tcb' in exI)
  apply (rule conjI)
   apply (clarsimp simp: opt_map_def obj_at'_def)
  apply (drule state_relation_release_queue_relation)
  apply (clarsimp simp: release_queue_relation_def list_queue_relation_def)
  apply (force simp: not_in_release_q_def opt_pred_def opt_map_def obj_at'_def)
  done

lemma isScActive_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and valid_objs and active_sc_tcb_at t)
             (\<lambda>s'. pred_map ((\<lambda>scPtr. isScActive scPtr s')) (tcbSCs_of s') t)"
  supply projectKOs[simp del]
  apply (rule cross_rel_imp[OF tcb_at'_cross_rel[where t=t]])
   apply (clarsimp simp: cross_rel_def)
   apply (subgoal_tac "pspace_relation (kheap s) (ksPSpace s')")
    apply (clarsimp simp: pred_map_def obj_at'_real_def ko_wp_at'_def vs_all_heap_simps)
    apply (subgoal_tac "sc_at' ref' s'")
     apply (clarsimp simp: vs_all_heap_simps pspace_relation_def)
     apply (drule_tac x=t in bspec, clarsimp)
     apply (clarsimp simp: other_obj_relation_def split: option.splits)
     apply (rename_tac s s' scp ko' tcb sc n x)
     apply (case_tac "ko'"; simp add: tcb_relation_cut_def)
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
      apply fastforce
     apply clarsimp
    apply (erule (2) sc_at_cross)
    apply (clarsimp simp: obj_at_def is_sc_obj_def)
    apply (rule_tac sc=ya in  valid_objs_valid_sched_context_size, assumption)
    apply fastforce
   apply clarsimp
  apply (clarsimp simp: obj_at_kh_kheap_simps pred_map_def vs_all_heap_simps is_tcb)
  done

lemma isSchedulable_bool_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and valid_objs and schedulable t)
             (isSchedulable_bool t)"
  apply (rule cross_rel_imp[OF isScActive_cross_rel[where t=t]])
   apply (rule cross_rel_imp[OF tcbInReleaseQueue_cross_rel[where t=t]])
    apply (rule cross_rel_imp[OF runnable_cross_rel[where t=t]])
     apply (clarsimp simp: isSchedulable_bool_def pred_map_conj[simplified pred_conj_def])
    apply (clarsimp simp: schedulable_def2)+
  done

lemmas tcb_at'_example = corres_cross[where Q' = "tcb_at' t" for t, OF tcb_at'_cross_rel]

(* FIXME RT: move to AInvs? *)
lemma no_fail_is_schedulable:
  "no_fail (tcb_at t and valid_tcbs) (is_schedulable t)"
  unfolding is_schedulable_def
  apply wpsimp
  apply (intro conjI impI allI)
    apply (clarsimp simp: obj_at_def get_tcb_def is_tcb_def
                   split: option.splits Structures_A.kernel_object.splits)
   apply (clarsimp simp: obj_at_def get_tcb_def is_tcb_def
                  split: option.splits Structures_A.kernel_object.splits)
  apply (clarsimp simp: obj_at_def get_tcb_def is_tcb_def Option.is_none_def
                 split: option.splits Structures_A.kernel_object.splits)
  apply (rename_tac sc_ptr)
  apply (prop_tac "sc_at sc_ptr s")
   subgoal
     by (fastforce simp: valid_tcbs_def obj_at_def valid_tcb_def valid_bound_obj_def
                  split: option.splits)
  apply (clarsimp simp: obj_at_def is_sc_obj_def)
  apply (rename_tac ko n, case_tac ko; clarsimp)
  done

lemma schedulable_imp_tcb_at:
  "schedulable t s \<Longrightarrow> tcb_at t s"
  by (clarsimp simp: schedulable_def get_tcb_def obj_at_def is_tcb_def
              split: option.splits Structures_A.kernel_object.splits)

lemma guarded_switch_to_chooseThread_fragment_corres:
  "corres dc
     (P and schedulable t and invs and valid_ready_qs and ready_or_release)
     (P' and invs')
     (guarded_switch_to t) (ThreadDecls_H.switchToThread t)"
  apply (rule corres_cross[where Q' = "isSchedulable_bool t", OF isSchedulable_bool_cross_rel],
         fastforce)
  apply (clarsimp simp: guarded_switch_to_def)
  apply (rule corres_symb_exec_l[rotated, OF _ thread_get_sp])
    apply (rule thread_get_exs_valid)
    apply (fastforce intro: schedulable_imp_tcb_at)
   apply wpsimp
   apply (fastforce intro: schedulable_imp_tcb_at)
  apply (rule corres_symb_exec_l[rotated, OF _ assert_opt_sp])
    apply wpsimp
    apply (clarsimp simp: schedulable_def get_tcb_def obj_at_def is_tcb_def
                   split: option.splits Structures_A.kernel_object.splits)
   apply wpsimp
   apply (clarsimp simp: schedulable_def get_tcb_def obj_at_def is_tcb_def
                  split: option.splits Structures_A.kernel_object.splits)
  apply (rule corres_symb_exec_l[rotated, OF _ is_schedulable_sp'])
    apply wpsimp
     apply (clarsimp simp: schedulable_def get_tcb_def vs_all_heap_simps is_sc_active_def
                    split: option.splits Structures_A.kernel_object.splits)
    apply wpsimp
   apply (wpsimp wp: no_fail_is_schedulable)
   apply (fastforce intro: schedulable_imp_tcb_at)
  apply (rule corres_symb_exec_l[rotated, OF _ assert_sp]; wpsimp)
  apply (rule corres_guard_imp)
    apply (rule switchToThread_corres)
   apply (wpsimp wp: is_schedulable_wp)
   apply (fastforce simp: schedulable_def2)
  apply fastforce
  done

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
   \<Longrightarrow> the (tcbQueueHead (ksReadyQueues s' (ksCurDomain s', lookupBitmapPriority (ksCurDomain s') s')))
       = hd (max_non_empty_queue (ready_queues s (cur_domain s)))"
  apply (clarsimp simp: max_non_empty_queue_def valid_bitmaps_def lookupBitmapPriority_Max_eqI)
  apply (frule curdomain_relation)
  apply (drule state_relation_ready_queues_relation)
  apply (simp add: Max_prio_helper)
  apply (frule (2) bitmapL1_zero_ksReadyQueues[THEN arg_cong_Not, THEN iffD1])
  apply clarsimp
  apply (cut_tac P="\<lambda>x. \<not> tcbQueueEmpty (ksReadyQueues s' (ksCurDomain s', x))"
              in setcomp_Max_has_prop)
   apply fastforce
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def
                        list_queue_relation_def tcbQueueEmpty_def)
  apply (drule_tac x="ksCurDomain s'" in spec)
  apply (drule_tac x="Max {prio. \<not> tcbQueueEmpty (ksReadyQueues s' (ksCurDomain s', prio))}"
                in spec)
  using heap_path_head tcbQueueEmpty_def
  by fastforce

lemma ksReadyQueuesL1Bitmap_return_wp:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s d) s \<rbrace> getReadyQueuesL1Bitmap d \<lbrace>\<lambda>rv s. P rv s\<rbrace>"
  unfolding getReadyQueuesL1Bitmap_def
  by wp

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
   apply (fastforce intro: ksReadyQueues_asrt_cross)
  apply (simp only: return_bind Let_def K_bind_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (clarsimp simp: ready_qs_runnable_def)
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
                       P'="\<lambda>s. ?PREH s \<and>
                               l1 = ksReadyQueuesL1Bitmap s (ksCurDomain s) \<and>
                               l1 \<noteq> 0 \<and>
                               queue = ksReadyQueues s (ksCurDomain s,
                                         lookupBitmapPriority (ksCurDomain s) s)" and
                       F="the (tcbQueueHead queue) = hd (max_non_empty_queue queues)" in corres_req)
               apply (fastforce simp: bitmap_lookup_queue_is_max_non_empty invs'_def)
              apply clarsimp
              apply (rule corres_guard_imp)
                apply (rule_tac P=\<top> and P'=\<top> in guarded_switch_to_chooseThread_fragment_corres)
               apply (wpsimp simp: getQueue_def getReadyQueuesL2Bitmap_def)+
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
                      and P'="\<lambda>s. valid_bitmaps s
                                  \<and> l1 = ksReadyQueuesL1Bitmap s d
                                  \<and> l1 \<noteq> 0 \<and> hprio = lookupBitmapPriority d s"
                      and F="hprio = Max {prio. q prio \<noteq> []}" in corres_req)
           apply (elim conjE)
           apply (clarsimp simp: valid_bitmaps_def)
           apply (subst lookupBitmapPriority_Max_eqI; blast?)
           apply (fastforce dest: state_relation_ready_queues_relation Max_prio_helper[where d=d]
                            simp: tcbQueueEmpty_def)
          apply fastforce
         apply (wpsimp simp: if_apply_def2 wp: hoare_drop_imps ksReadyQueuesL1Bitmap_return_wp)+
  done

crunch set_scheduler_action
  for valid_idle_etcb[wp]: valid_idle_etcb

crunch isHighestPrio
  for inv[wp]: P
crunch curDomain
  for inv[wp]: P
crunch scheduleSwitchThreadFastfail
  for inv[wp]: P

lemma setSchedulerAction_invs': (* not in wp set, clobbered by ssa_wp *)
  "\<lbrace>\<lambda>s. invs' s \<rbrace> setSchedulerAction ChooseNewThread \<lbrace>\<lambda>_. invs' \<rbrace>"
  by (wpsimp simp: invs'_def valid_irq_node'_def valid_bitmaps_def  valid_dom_schedule'_def)

lemma scheduleChooseNewThread_corres:
  "corres dc
     (\<lambda>s. invs s \<and> valid_ready_qs s \<and> ready_or_release s \<and> scheduler_action s = choose_new_thread)
     (\<lambda>s. invs' s \<and> ksSchedulerAction s = ChooseNewThread)
     schedule_choose_new_thread scheduleChooseNewThread"
  apply (clarsimp simp: schedule_choose_new_thread_def scheduleChooseNewThread_def)
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro: ksReadyQueues_asrt_cross)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getDomainTime_corres], clarsimp)
      apply (rule corres_split[OF scheduleChooseNewThread_fragment_corres, simplified bind_assoc])
        apply (rule setSchedulerAction_corres)
        apply wpsimp+
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

lemma switchToThread_ct_not_queued_2:
  "\<lbrace>invs' and tcb_at' t\<rbrace> switchToThread t \<lbrace>\<lambda>rv s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>"
  (is "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_. ?POST\<rbrace>")
  apply (simp add: Thread_H.switchToThread_def)
  apply wp
    apply (simp add: RISCV64_H.switchToThread_def setCurThread_def)
    apply (wp tcbSchedDequeue_not_tcbQueued hoare_drop_imp | simp )+
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

lemma switchToIdleThread_activatable_2[wp]:
  "\<lbrace>invs'\<rbrace> switchToIdleThread \<lbrace>\<lambda>_. ct_in_state' activatable'\<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def
                   RISCV64_H.switchToIdleThread_def)
  apply (wp setCurThread_ct_in_state)
  apply (clarsimp simp: invs'_def valid_idle'_def valid_idle'_asrt_def
                        pred_tcb_at'_def obj_at'_def idle_tcb'_def)
  done

lemma chooseThread_invs'':
  "chooseThread \<lbrace>invs'\<rbrace>"
  unfolding chooseThread_def Let_def
  apply (simp only: return_bind, simp split del: if_split)
  apply (intro bind_wp[OF _ stateAssert_sp])
  apply (rule bind_wp[where Q'="\<lambda>rv s. invs' s \<and> rv = ksCurDomain s \<and> ready_qs_runnable s"])
   apply (rule_tac Q'="\<lambda>rv s. invs' s \<and> curdom = ksCurDomain s \<and>
                             rv = ksReadyQueuesL1Bitmap s curdom \<and> ready_qs_runnable s"
                in bind_wp)
    apply (rename_tac l1)
    apply (case_tac "l1 = 0")
     (* switch to idle thread *)
     apply (wpsimp wp: switchToIdleThread_invs')
    apply (wpsimp wp: curDomain_or_return_0[simplified] ksReadyQueuesL1Bitmap_return_wp)+
  done

lemma scheduleChooseNewThread_invs':
  "scheduleChooseNewThread \<lbrace>invs'\<rbrace>"
  unfolding scheduleChooseNewThread_def
  apply (wpsimp wp: ssa_invs' chooseThread_invs'' chooseThread_invs'' nextDomain_invs')
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
  apply (wpsimp wp: dmo_invs' RISCV64.setDeadline_irq_masks threadGet_wp getReleaseQueue_wp)
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  by (auto simp: in_monad setDeadline_def machine_op_lift_underlying_memory_invar)

lemma setCurSc_invs'[wp]:
  "setCurSc v \<lbrace>invs'\<rbrace>"
  unfolding setCurSc_def
  apply wpsimp
  apply (clarsimp simp: invs'_def valid_machine_state'_def
                        valid_bitmaps_def valid_bitmapQ_def bitmapQ_def
                        bitmapQ_no_L2_orphans_def bitmapQ_no_L1_orphans_def valid_irq_node'_def
                        valid_dom_schedule'_def)
  done

lemma setConsumedTime_invs'[wp]:
  "setConsumedTime v \<lbrace>invs'\<rbrace>"
  unfolding setConsumedTime_def
  apply wpsimp
  apply (clarsimp simp: invs'_def valid_machine_state'_def
                        valid_bitmaps_def valid_bitmapQ_def bitmapQ_def
                        bitmapQ_no_L2_orphans_def bitmapQ_no_L1_orphans_def valid_irq_node'_def
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

lemma valid_sched_context'_scRefills_update:
  "length (scRefills (scRefills_update f sc)) = length (scRefills sc)
   \<Longrightarrow> valid_sched_context' (scRefills_update f sc) s = valid_sched_context' sc s"
  by (clarsimp simp: valid_obj'_def valid_sched_context'_def objBits_simps refillSize_def)

lemma updateRefillIndex_valid_objs'[wp]:
  "\<lbrace>valid_objs' and sc_at' scPtr\<rbrace>
   updateRefillIndex scPtr f next
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding updateRefillIndex_def
  apply wpsimp
  apply (clarsimp simp: in_omonad obj_at'_def valid_objs'_def valid_obj'_def
                        valid_sched_context_size'_def sc_size_bounds_def objBits_simps
                        valid_sched_context'_scRefills_update)
  done

lemma refillAddTail_valid_objs'[wp]:
  "refillAddTail scPtr t \<lbrace>valid_objs'\<rbrace>"
  apply (simp add: refillAddTail_def)
  apply (wpsimp wp: set_sc_valid_objs' getRefillNext_wp getRefillSize_wp hoare_vcg_all_lift
              simp: updateSchedContext_def)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc', clarsimp)
  apply (clarsimp simp: valid_obj'_def obj_at'_def in_omonad)
  apply (fastforce simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps
                         refillSize_def refillNext_def
                  split: if_splits)
  done

lemma updateRefillIndex_invs'[wp]:
  "\<lbrace>invs' and sc_at' scPtr\<rbrace>
   updateRefillIndex scPtr f next
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding updateRefillIndex_def
  apply (wpsimp wp: updateSchedContext_invs')
  apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                   elim: live_sc'_ko_ex_nonz_cap_to'
                   simp: valid_sched_context'_scRefills_update)
  done

lemma refillAddTail_invs'[wp]:
  "refillAddTail scPtr t \<lbrace>invs'\<rbrace>"
  apply (simp add: refillAddTail_def)
  apply (wpsimp wp: getRefillNext_wp getRefillSize_wp updateSchedContext_invs')
  apply (frule (1) invs'_ko_at_valid_sched_context', clarsimp)
  apply (drule ko_at'_inj, assumption, clarsimp)
  apply (fastforce elim: live_sc'_ko_ex_nonz_cap_to'
                   simp: in_omonad obj_at'_def valid_sched_context'_def refillSize_def
                         valid_sched_context_size'_def sc_size_bounds_def objBits_simps
                         refillNext_def)
  done

lemma refillBudgetCheckRoundRobin_invs'[wp]:
  "\<lbrace>invs' and (\<lambda>s. active_sc_at' (ksCurSc s) s)\<rbrace>
   refillBudgetCheckRoundRobin consumed
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  supply if_split [split del]
  apply (simp add: refillBudgetCheckRoundRobin_def updateRefillTl_def updateRefillHd_def)
  apply (wpsimp simp:  wp: updateSchedContext_refills_invs')
    apply (rule_tac Q'="\<lambda>_. invs' and active_sc_at' scPtr" in hoare_strengthen_post[rotated])
     apply clarsimp
     apply (frule (1) invs'_ko_at_valid_sched_context', clarsimp)
     apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def
                           ko_wp_at'_def valid_sched_context_size'_def objBits_def objBitsKO_def
                           refillSize_def
                    split: if_splits)
    apply (wpsimp wp: updateSchedContext_refills_invs' getCurTime_wp updateSchedContext_active_sc_at')
   apply wpsimp
  apply clarsimp
  apply (frule invs'_ko_at_valid_sched_context', simp, clarsimp)
  apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def ko_wp_at'_def
                        valid_sched_context_size'_def objBits_def objBitsKO_def refillSize_def
                 split: if_splits)
  done

lemma updateRefillTl_valid_objs'[wp]:
  "updateRefillTl scPtr f \<lbrace>valid_objs'\<rbrace>"
  apply (clarsimp simp: updateRefillTl_def updateSchedContext_def)
  apply (wpsimp wp: set_sc_valid_objs')
  apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                   simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps
                         refillSize_def)
  done

crunch scheduleUsed
  for valid_objs'[wp]: valid_objs'

lemma updateRefillTl_invs'[wp]:
  "updateRefillTl scPtr f \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: updateRefillTl_def)
  apply (wpsimp wp: updateSchedContext_invs')
  apply (intro conjI)
   apply (fastforce dest: invs_iflive'
                    elim: if_live_then_nonz_capE'
                    simp: valid_idle'_def obj_at'_def ko_wp_at'_def live_sc'_def)
  apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                   simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps
                         refillSize_def)
  done

lemma updateRefillIndex_if_live_then_nonz_cap'[wp]:
  "updateRefillIndex scPtr f index \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: updateRefillIndex_def updateSchedContext_def)
  apply (wpsimp wp: setSchedContext_iflive')
  apply (fastforce elim: if_live_then_nonz_capE'
                   simp: valid_idle'_def obj_at'_def ko_wp_at'_def live_sc'_def)
  done

lemma updateRefillTl_if_live_then_nonz_cap'[wp]:
  "updateRefillTl scPtr f \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: updateRefillTl_def updateSchedContext_def)
  apply (wpsimp wp: setSchedContext_iflive')
  apply (fastforce elim: if_live_then_nonz_capE'
                   simp: valid_idle'_def obj_at'_def ko_wp_at'_def live_sc'_def)
  done

lemma refillAddTail_if_live_then_nonz_cap'[wp]:
  "refillAddTail scPtr new \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: refillAddTail_def updateSchedContext_def)
  apply (wpsimp wp: setSchedContext_iflive' getRefillNext_wp getRefillSize_wp)
  apply (fastforce elim: if_live_then_nonz_capE'
                   simp: valid_idle'_def obj_at'_def ko_wp_at'_def live_sc'_def)
  done

lemma scheduleUsed_if_live_then_nonz_cap'[wp]:
  "scheduleUsed scPtr refill \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  unfolding scheduleUsed_def
  by (wpsimp simp: scheduleUsed_def
               wp: updateSchedContext_wp getRefillSize_wp getRefillNext_wp getRefillFull_wp getRefillTail_wp)

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
  (wp: updateSchedContext_valid_idle' getRefillSize_wp)

lemma scheduleUsed_invs'[wp]:
  "scheduleUsed scPtr refill \<lbrace>invs'\<rbrace>"
  apply (simp add: scheduleUsed_def)
  apply (wpsimp wp: getRefillFull_wp)
  done

lemma refillPopHead_valid_objs'[wp]:
  "refillPopHead scPtr \<lbrace>valid_objs'\<rbrace>"
  apply (clarsimp simp: refillPopHead_def updateSchedContext_def getRefillNext_def)
  apply (wpsimp wp: set_sc_valid_objs')
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply (clarsimp simp: readRefillNext_def readSchedContext_def)
  apply (fastforce simp: obj_at'_def scBits_simps refillNext_def refillSize_def
                         valid_sched_context'_def valid_sched_context_size'_def objBits_simps'
                  dest!: readObject_misc_ko_at')
  done

lemma refillPopHead_invs'[wp]:
  "refillPopHead scPtr \<lbrace>invs'\<rbrace>"
  supply if_split[split del]
  apply (simp add: refillPopHead_def)
  apply (wpsimp wp: updateSchedContext_invs' getRefillNext_wp)
  apply normalise_obj_at'
  apply (rule conjI)
   apply (fastforce intro!: if_live_then_nonz_capE'
                      simp: ko_wp_at'_def obj_at'_def live_sc'_def)
  by (fastforce dest!: invs'_ko_at_valid_sched_context'
                 simp: valid_sched_context'_def valid_sched_context_size'_def obj_at_simps
                       refillSize_def refillNext_def
                split: if_split)

lemma refillPopHead_active_sc_at'[wp]:
  "refillPopHead scPtr \<lbrace>active_sc_at' scPtr'\<rbrace>"
  apply (simp add: refillPopHead_def)
  apply (wpsimp wp: updateSchedContext_active_sc_at' getRefillNext_wp)
  done

lemma refillAddTail_active_sc_at'[wp]:
  "refillAddTail scPtr refill \<lbrace>active_sc_at' scPtr'\<rbrace>"
  apply (simp add: refillAddTail_def getRefillSize_def updateRefillIndex_def)
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
                        valid_sched_context_size'_def objBits_def objBitsKO_def refillSize_def
                 split: if_splits)
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
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n T p s)"
  and active_sc_at'[wp]: "active_sc_at' scPtr"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

lemma updateRefillHd_valid_objs'[wp]:
  "updateRefillHd scPtr f \<lbrace>valid_objs'\<rbrace>"
  unfolding updateRefillHd_def updateSchedContext_def
  apply wpsimp
  by (fastforce dest: sc_ko_at_valid_objs_valid_sc' simp: valid_sched_context'_def refillSize_def)

lemma mergeOverlappingRefills_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> ((\<lambda>sc. 1 < refillSize sc) |< scs_of' s) scPtr\<rbrace>
   mergeOverlappingRefills scPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding mergeOverlappingRefills_def
  by (wpsimp wp: updateRefillHd_valid_objs')

lemma no_ofail_readRefillNext[wp]:
  "no_ofail (active_sc_at' scPtr) (readRefillNext scPtr index)"
  unfolding readRefillNext_def readSchedContext_def ohaskell_state_assert_def
  by (wpsimp wp_del: ovalid_readObject simp: active_sc_at'_def)

lemmas no_fail_getRefillNext[wp] =
  no_ofail_gets_the[OF no_ofail_readRefillNext, simplified getRefillNext_def[symmetric]]

lemma no_ofail_readRefillIndex[wp]:
  "no_ofail (sc_at' scp) (readRefillIndex scp idx)"
  unfolding readRefillIndex_def
  by (wpsimp wp: no_ofail_readSchedContext)

lemma no_ofail_readRefillSingle[wp]:
  "no_ofail (sc_at' scp) (readRefillSingle scp)"
  unfolding readRefillSingle_def
  by (wpsimp wp: no_ofail_readSchedContext)

lemma readRefillSingle_wp[wp]:
  "\<lblot>\<lambda>s. \<forall>sc. ko_at' (sc :: sched_context) scp s \<longrightarrow> Q (scRefillHead sc = scRefillTail sc) s\<rblot>
   readRefillSingle scp
   \<lblot>Q\<rblot>"
  unfolding readRefillSingle_def readSchedContext_def
  by (wpsimp wp: set_sc'.readObject_wp)

lemma readRefillNext_wp[wp]:
  "\<lblot>\<lambda>s. \<forall>sc. ko_at' (sc :: sched_context) scp s \<longrightarrow> Q (refillNext sc idx) s\<rblot>
   readRefillNext scp idx
   \<lblot>Q\<rblot>"
  unfolding readRefillNext_def readSchedContext_def
  by (wpsimp wp: set_sc'.readObject_wp)

lemma no_ofail_refillHeadOverlapping:
  "no_ofail (active_sc_at' scp) (refillHeadOverlapping scp)"
  unfolding refillHeadOverlapping_def
  apply (wpsimp wp: no_ofail_readSchedContext simp: active_sc_at'_def)
  by (clarsimp simp: obj_at'_def)

lemma readRefillIndex_wp[wp]:
  "\<lblot>\<lambda>s. \<forall>sc. ko_at' (sc :: sched_context) scp s \<longrightarrow> Q (refillIndex idx sc) s\<rblot>
   readRefillIndex scp idx
   \<lblot>Q\<rblot>"
  unfolding readRefillIndex_def readSchedContext_def
  by (wpsimp wp: set_sc'.readObject_wp)

lemma refillHeadOverlapping_refillSize:
  "\<lblot>valid_refills' scPtr\<rblot>
   refillHeadOverlapping scPtr
   \<lblot>\<lambda>rv s. rv \<longrightarrow> ((\<lambda>sc. 1 < refillSize sc) |< scs_of' s) scPtr\<rblot>"
  unfolding refillHeadOverlapping_def readSchedContext_def
  apply (wpsimp wp: ovalid_if_split set_sc'.readObject_wp)
  apply (clarsimp simp: obj_at'_def opt_map_red opt_pred_def refillSize_def valid_refills'_def)
  done

lemma refillHeadOverlappingLoop_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> active_sc_at' scPtr s\<rbrace>
   refillHeadOverlappingLoop scPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  (is "\<lbrace>?pre\<rbrace>_ \<lbrace>_\<rbrace>")
  apply (clarsimp simp: refillHeadOverlappingLoop_def runReaderT_def)
  apply (wpsimp wp: valid_whileLoop[where I="\<lambda>_. ?pre"] mergeOverlappingRefills_valid_objs')
    apply (frule no_ofailD[OF no_ofail_refillHeadOverlapping])
    apply (fastforce dest: use_ovalid[OF refillHeadOverlapping_refillSize]
                    intro: valid_objs'_valid_refills'
                     simp: active_sc_at'_rewrite)
   apply (fastforce simp: active_sc_at'_def)
  apply fastforce
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
  apply (clarsimp simp: active_sc_at'_def obj_at'_def)
  done

lemma refillUnblockCheck_valid_mdb'[wp]:
  "refillUnblockCheck scPtr \<lbrace>valid_mdb'\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def valid_mdb'_def)
  apply (wpsimp wp: scActive_wp)
  done

crunch refillUnblockCheck
  for valid_machine_state'[wp]: valid_machine_state'
  (simp: crunch_simps wp: crunch_wps)

lemma refillUnblockCheck_list_refs_of_replies'[wp]:
  "refillUnblockCheck scPtr \<lbrace>\<lambda>s. P (list_refs_of_replies' s)\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def valid_mdb'_def refillHeadOverlappingLoop_def
                        mergeOverlappingRefills_def updateRefillHd_def refillPopHead_def updateSchedContext_def
                        setReprogramTimer_def refillReady_def isRoundRobin_def)
  apply (wpsimp wp: whileLoop_valid_inv hoare_drop_imps scActive_wp getRefillNext_wp
              simp: o_def)
  done

lemma refillPopHead_if_live_then_nonz_cap'[wp]:
  "refillPopHead scPtr \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: refillPopHead_def updateSchedContext_def getRefillNext_def)
  apply wpsimp
  apply (fastforce intro: if_live_then_nonz_capE'
                    simp: ko_wp_at'_def obj_at'_real_def live_sc'_def)
  done

lemma updateRefillHd_if_live_then_nonz_cap'[wp]:
  "updateRefillHd scPtr f \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: updateRefillHd_def updateSchedContext_def)
  apply wpsimp
  apply (fastforce intro: if_live_then_nonz_capE'
                    simp: ko_wp_at'_def obj_at'_real_def live_sc'_def)
  done

crunch refillHeadOverlappingLoop, headInsufficientLoop
  for if_live_then_nonz_cap'[wp]: if_live_then_nonz_cap'
  (wp: crunch_wps)

lemma setRefillHd_if_live_then_nonz_cap'[wp]:
  "setRefillHd scPtr f \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (wpsimp simp: setRefillHd_def)
  done

crunch handleOverrun, refillUnblockCheck
  for if_live_then_nonz_cap'[wp]: if_live_then_nonz_cap'
  (wp: crunch_wps)

crunch refillHeadOverlappingLoop, headInsufficientLoop, handleOverrun
  for valid_idle'[wp]: valid_idle'
  (wp: crunch_wps)

crunch refillUnblockCheck, refillBudgetCheck
  for reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and pred_tcb_at'[wp]: "pred_tcb_at' proj P p"
  and valid_replies'[wp]: valid_replies'
  and sched_projs[wp]: "\<lambda>s. P (tcbSchedPrevs_of s) (tcbSchedNexts_of s)"
  and tcbs_of'[wp]: "\<lambda>s. P (tcbs_of' s)"
  and ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksReadyQueuesL1Bitmap[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and ksReadyQueuesL2Bitmap[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (wp: crunch_wps hoare_vcg_all_lift valid_replies'_lift hoare_vcg_if_lift2)

lemma refillUnblockCheck_invs':
  "refillUnblockCheck scPtr \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: invs'_def valid_pspace'_def pred_conj_def)
  by (wpsimp wp: sym_heap_sched_pointers_lift valid_bitmaps_lift)

crunch ifCondRefillUnblockCheck
  for invs'[wp]: invs'
  (wp: hoare_vcg_if_lift2 crunch_wps simp: crunch_simps)

lemma getRefillSize_sp:
  "\<lbrace>P\<rbrace> getRefillSize scPtr \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. ko_at' sc scPtr s \<and> rv = refillSize sc)\<rbrace>"
  apply (wpsimp wp: getRefillSize_wp)
  apply (clarsimp simp: obj_at'_def)
  done

crunch headInsufficientLoop, handleOverrun, refillBudgetCheck
  for valid_objs'[wp]: valid_objs'
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

lemma refillBudgetCheck_valid_mdb'[wp]:
  "refillBudgetCheck usage \<lbrace>valid_mdb'\<rbrace>"
  apply (clarsimp simp: handleOverrun_def valid_mdb'_def)
  apply (wpsimp wp: scActive_wp)
  done

crunch updateRefillHd, updateRefillTl
  for list_refs_of_replies'[wp]: "\<lambda>s. P (list_refs_of_replies' s)"
  and valid_machine_state'[wp]: valid_machine_state'
  (simp: o_def updateSchedContext_def updateRefillIndex_def)

lemma refillAddTail_list_refs_of_replies'[wp]:
  "refillAddTail scPtr new \<lbrace>\<lambda>s. P (list_refs_of_replies' s)\<rbrace>"
  by (wpsimp wp: hoare_drop_imps getRefillNext_wp getRefillSize_wp
           simp: o_def updateSchedContext_def refillAddTail_def updateRefillIndex_def)

crunch refillBudgetCheck
  for list_refs_of_replies'[wp]: "\<lambda>s. P (list_refs_of_replies' s)"
  and valid_machine_state'[wp]: valid_machine_state'
  (wp: crunch_wps hoare_vcg_all_lift hoare_vcg_if_lift2)

crunch refillBudgetCheck
  for if_live_then_nonz_cap'[wp]: if_live_then_nonz_cap'
  (simp: crunch_simps wp: crunch_wps hoare_vcg_all_lift)

lemma refillBudgetCheck_invs'[wp]:
  "refillBudgetCheck usage \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: invs'_def valid_pspace'_def pred_conj_def)
  apply (wpsimp wp: refillBudgetCheck_valid_objs' valid_bitmaps_lift)
  done

lemma commitTime_invs':
  "commitTime \<lbrace>invs'\<rbrace>"
  apply (simp add: commitTime_def)
  apply wpsimp
       apply (wpsimp wp: updateSchedContext_invs'_indep)
      apply (clarsimp simp: valid_sched_context'_def valid_sched_context_size'_def objBits_def sc_size_bounds_def objBitsKO_def live_sc'_def)
      apply (rule_tac Q'="\<lambda>_. invs'" in hoare_strengthen_post)
       apply (wpsimp wp: isRoundRobin_wp)
      apply (wpsimp wp: getConsumedTime_wp getCurSc_wp)+
  by (clarsimp simp: active_sc_at'_def obj_at'_real_def ko_wp_at'_def)

lemma switchSchedContext_invs':
  "switchSchedContext \<lbrace>invs'\<rbrace>"
  apply (simp add: switchSchedContext_def)
  apply (wpsimp wp: commitTime_invs' getReprogramTimer_wp refillUnblockCheck_invs' threadGet_wp
              simp: getCurSc_def)
  done

lemma isSchedulable_bool_runnableE:
  "isSchedulable_bool t s \<Longrightarrow> tcb_at' t s \<Longrightarrow> st_tcb_at' runnable' t s"
  unfolding isSchedulable_bool_def
  by (clarsimp simp: pred_tcb_at'_def obj_at'_def pred_map_def
              elim!: opt_mapE)

lemma rescheduleRequired_invs'[wp]:
  "rescheduleRequired \<lbrace>invs'\<rbrace>"
  unfolding rescheduleRequired_def
  apply (wpsimp wp: ssa_invs' isSchedulable_wp)
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

crunch possibleSwitchTo
  for valid_sched_pointers[wp]: valid_sched_pointers
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  (wp: crunch_wps simp: crunch_simps)

crunch possibleSwitchTo
  for valid_tcbs'[wp]: valid_tcbs'
  and cap_to'[wp]: "ex_nonz_cap_to' p"
  and ifunsafe'[wp]: "if_unsafe_then_cap'"
  and global_refs'[wp]: valid_global_refs'
  and valid_machine_state'[wp]: valid_machine_state'
  and cur[wp]: cur_tcb'
  and refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  and replies_of'[wp]: "\<lambda>s. P (replies_of' s)"
  and idle'[wp]: "valid_idle'"
  and valid_arch'[wp]: valid_arch_state'
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and irq_states' [wp]: valid_irq_states'
  and pspace_domain_valid[wp]: "pspace_domain_valid"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and ksArchState[wp]: "\<lambda>s. P (ksArchState s)"
  and ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and valid_irq_handlers'[wp]: valid_irq_handlers'
  and tcbInReleaseQueue[wp]: "\<lambda>s. P (tcbInReleaseQueue |< tcbs_of' s)"
  and valid_objs'[wp]: valid_objs'
  and pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and pspace_bounded'[wp]: pspace_bounded'
  (wp: crunch_wps cur_tcb_lift valid_irq_handlers_lift'' simp: crunch_simps)

lemmas possibleSwitchTo_typ_ats[wp] = typ_at_lifts[OF possibleSwitchTo_typ_at']

crunch possibleSwitchTo
  for if_live_then_nonz_cap'[wp]: if_live_then_nonz_cap'
  (wp: crunch_wps simp: crunch_simps)

lemma possibleSwitchTo_utr[wp]:
  "possibleSwitchTo t \<lbrace>untyped_ranges_zero'\<rbrace>"
  by (wpsimp simp: cteCaps_of_def o_def wp: untyped_ranges_zero_lift)

crunch possibleSwitchTo
  for invs'[wp]: invs'

lemma possibleSwitchTo_sch_act_not_other:
  "\<lbrace>\<lambda>s. sch_act_not t' s \<and> t' \<noteq> t\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>_. sch_act_not t'\<rbrace>"
  apply (clarsimp simp: possibleSwitchTo_def)
  apply (wpsimp wp: threadGet_wp inReleaseQueue_wp)
  done

crunch setReprogramTimer, possibleSwitchTo
  for ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"
  (wp: crunch_wps simp: crunch_simps)

lemma getReleaseQueue_sp:
  "\<lbrace>Q\<rbrace> getReleaseQueue \<lbrace>\<lambda>r. (\<lambda>s. r = ksReleaseQueue s) and Q\<rbrace>"
  unfolding getReleaseQueue_def
  by wpsimp

lemma releaseQNonEmptyAndReady_implies_releaseQNonEmpty:
  "releaseQNonEmptyAndReady s = Some True \<Longrightarrow> tcbQueueHead (ksReleaseQueue s) \<noteq> None"
  by (clarsimp simp: releaseQNonEmptyAndReady_def readReleaseQueue_def obind_def omonad_defs
              split: if_splits)

crunch awaken
  for invs'[wp]: invs'
  (wp: crunch_wps)

crunch tcbReleaseRemove
  for valid_replies' [wp]: valid_replies'
  (wp: crunch_wps threadSet_pred_tcb_no_state valid_replies'_lift)

crunch awaken
  for cur_tcb'[wp]: cur_tcb'
  (wp: crunch_wps threadSet_cur)

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
   apply (rule_tac P'="invs' and cur_tcb'" in hoare_weaken_pre)
    apply (rule bind_wp_fwd_skip, wpsimp)
    apply (rule_tac bind_wp[OF _ getCurThread_sp])
    apply (rule_tac bind_wp[OF _ isSchedulable_sp])
    apply (rule_tac bind_wp[OF _ getSchedulerAction_sp])
    apply (rule bind_wp)
     apply (wpsimp wp: switchSchedContext_invs' hoare_drop_imp)
    apply (wpsimp wp: scheduleChooseNewThread_invs' isSchedulable_wp setSchedulerAction_invs'
                      ssa_invs' hoare_vcg_disj_lift)
           apply (wpsimp simp: isHighestPrio_def')
          apply (wpsimp wp: curDomain_wp)
         apply (wpsimp simp: scheduleSwitchThreadFastfail_def)
        apply (rename_tac tPtr x idleThread targetPrio)
        apply (rule_tac Q'="\<lambda>_. invs'" in hoare_strengthen_post[rotated])
         apply (prop_tac "st_tcb_at' runnable' tPtr s \<Longrightarrow> obj_at' (\<lambda>a. activatable' (tcbState a)) tPtr s")
          apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
         apply fastforce
        apply (wpsimp wp: threadGet_wp hoare_drop_imp hoare_vcg_ex_lift)
       apply (rename_tac tPtr x idleThread)
       apply (rule_tac Q'="\<lambda>_. invs'"
                    in hoare_strengthen_post[rotated])
        apply (subst obj_at_ko_at'_eq[symmetric], simp)
       apply (wpsimp wp: threadGet_wp hoare_drop_imp hoare_vcg_ex_lift)
      apply (rename_tac tPtr x)
      apply (rule_tac Q'="\<lambda>_. invs'" in hoare_strengthen_post[rotated])
       apply (subst obj_at_ko_at'_eq[symmetric], simp)
      apply (wpsimp wp: isSchedulable_wp)
     apply (wpsimp wp: tcbSchedEnqueue_invs')
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
  apply (simp add: Thread_H.switchToThread_def RISCV64_H.switchToThread_def storeWordUser_def)
  apply (wp setCurThread_nosch hoare_drop_imp |simp)+
  done

lemma stit_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
    switchToIdleThread
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def
                   RISCV64_H.switchToIdleThread_def  storeWordUser_def)
  apply (wp setCurThread_nosch | simp add: getIdleThread_def)+
  done

lemma chooseThread_nosch:
  "chooseThread \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>"
  unfolding chooseThread_def
  by (wpsimp wp: stt_nosch isSchedulable_wp simp: bitmap_fun_defs)

crunch switchSchedContext, setNextInterrupt
  for ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

lemma schedule_sch:
  "\<lbrace>\<top>\<rbrace> schedule \<lbrace>\<lambda>rv s. ksSchedulerAction s = ResumeCurrentThread\<rbrace>"
  unfolding schedule_def scAndTimer_def
  by (wpsimp wp: setSchedulerAction_direct isSchedulable_wp
           simp: getReprogramTimer_def scheduleChooseNewThread_def
      | wp (once) hoare_drop_imp)+

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
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  apply (simp add: rescheduleRequired_def sch_act_sane_def
                   setSchedulerAction_def)
  by (wp isSchedulable_wp | wpc | clarsimp)+

crunch setThreadState, setBoundNotification
 for sch_act_sane[wp]: "sch_act_sane"
  (simp: crunch_simps wp: crunch_wps)

lemma weak_sch_act_wf_cross:
  assumes sr: "(s,s') \<in> state_relation"
  assumes aligned: "pspace_aligned s"
  assumes distinct: "pspace_distinct s"
  assumes t: "weak_valid_sched_action s"
  shows "weak_sch_act_wf (ksSchedulerAction s') s'"
  using assms
  apply (clarsimp simp: weak_valid_sched_action_def weak_sch_act_wf_def)
  apply (frule state_relation_sched_act_relation)
  apply (rename_tac t)
  apply (drule_tac x=t in spec)
  apply (prop_tac "scheduler_action s = switch_thread t")
   subgoal
     by (metis sched_act_relation.simps Structures_A.scheduler_action.exhaust
               scheduler_action.simps)
  apply (auto simp: obj_at_def is_tcb_def vs_all_heap_simps intro: tcb_at_cross)
  done

lemma tcb_sched_enqueue_in_correct_ready_q[wp]:
  "tcb_sched_action tcb_sched_enqueue t \<lbrace>in_correct_ready_q\<rbrace> "
  unfolding tcb_sched_action_def set_tcb_queue_def
  apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: in_correct_ready_q_def obj_at_def vs_all_heap_simps tcb_sched_enqueue_def)
  done

lemma tcb_sched_append_in_correct_ready_q[wp]:
  "tcb_sched_action tcb_sched_append t \<lbrace>in_correct_ready_q\<rbrace> "
  unfolding tcb_sched_action_def set_tcb_queue_def
  apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: in_correct_ready_q_def obj_at_def vs_all_heap_simps tcb_sched_append_def)
  done

lemma tcb_sched_enqueue_ready_qs_distinct[wp]:
  "tcb_sched_action tcb_sched_enqueue t \<lbrace>ready_qs_distinct\<rbrace> "
  unfolding tcb_sched_action_def set_tcb_queue_def
  apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: ready_qs_distinct_def)
  done

lemma tcb_sched_append_ready_qs_distinct[wp]:
  "tcb_sched_action tcb_sched_append t \<lbrace>ready_qs_distinct\<rbrace> "
  unfolding tcb_sched_action_def set_tcb_queue_def
  apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: ready_qs_distinct_def)
  done

crunch set_scheduler_action
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  (wp: crunch_wps simp: in_correct_ready_q_def ready_qs_distinct_def)

crunch reschedule_required
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  (ignore: tcb_sched_action wp: crunch_wps)

lemma possibleSwitchTo_corres:
  "t = t' \<Longrightarrow>
   corres dc
    (valid_sched_action and st_tcb_at runnable t
     and pspace_aligned and pspace_distinct and valid_tcbs
     and active_scs_valid and in_correct_ready_q and ready_or_release and ready_qs_distinct)
    (sym_heap_sched_pointers and valid_sched_pointers and valid_tcbs'
     and pspace_aligned' and pspace_distinct' and pspace_bounded')
      (possible_switch_to t)
      (possibleSwitchTo t')"
  supply dc_simp [simp del]
  apply (rule corres_cross_add_guard[where Q'="tcb_at' t"])
   apply (fastforce intro: tcb_at_cross)
  apply (simp add: possible_switch_to_def possibleSwitchTo_def cong: if_cong)
  apply (rule corres_guard_imp)
    apply (simp add: get_tcb_obj_ref_def)
    apply (rule_tac r'="(=)" in  corres_split[OF threadGet_corres])
       apply (clarsimp simp: tcb_relation_def)
      apply (rule corres_split[OF inReleaseQueue_corres])
        apply (rule corres_when[rotated])
         apply (rule corres_split[OF curDomain_corres], simp)
           apply (rule corres_split[OF threadGet_corres[where r="(=)"]])
              apply (clarsimp simp: tcb_relation_def)
             apply (rule corres_split[OF getSchedulerAction_corres])
               apply (rule corres_if, simp)
                apply (rule tcbSchedEnqueue_corres, simp)
               apply (rule corres_if, simp)
                 apply (case_tac rva; simp)
                apply (rule corres_split[OF rescheduleRequired_corres])
                  apply (rule tcbSchedEnqueue_corres)
                 apply (wpsimp)+
               apply (rule setSchedulerAction_corres, simp)
              apply (wpsimp simp: if_apply_def2 valid_sched_action_def
                              wp: thread_get_wp threadGet_wp inReleaseQueue_wp)+
   apply (clarsimp simp: st_tcb_at_def obj_at_def is_tcb_def)
  apply (clarsimp simp: obj_at'_def)
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
   by (auto simp: vs_all_heap_simps other_obj_relation_def tcb_relation_def tcb_relation_cut_def
                  cur_tcb'_def pred_tcb_at'_def obj_at'_def
           split: kernel_object.splits)

lemma setReprogramTimer_corres[corres]:
  "corres dc \<top> \<top> (modify (reprogram_timer_update (\<lambda>_. b))) (setReprogramTimer b)"
  apply (unfold setReprogramTimer_def)
  apply (rule corres_modify)
  apply (simp add: state_relation_def swp_def)
  done

lemma getReleaseQueue_corres:
  "corres (\<lambda>ls q. (ls = [] \<longleftrightarrow> tcbQueueEmpty q) \<and> (ls \<noteq> [] \<longrightarrow> tcbQueueHead q = Some (hd ls))
                  \<and> queue_end_valid ls q)
     \<top> \<top> (gets release_queue) getReleaseQueue"
  apply (clarsimp simp: getReleaseQueue_def)
  apply (drule state_relation_release_queue_relation)
  apply (fastforce dest!: heap_path_head
                    simp: release_queue_relation_def list_queue_relation_def tcbQueueEmpty_def)
  done

lemma scActive_inv:
  "scActive scPtr \<lbrace>P\<rbrace>"
  by wpsimp

lemma gets_the_releaseQNonEmptyAndReady_corres:
  "corres (=)
     (valid_release_q and active_scs_valid and valid_objs and pspace_aligned and pspace_distinct)
     (valid_objs' and pspace_bounded')
     (gets_the (read_release_q_non_empty_and_ready)) (gets_the (releaseQNonEmptyAndReady))"
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest: pspace_distinct_cross)
  apply (simp add: read_release_q_non_empty_and_ready_def releaseQNonEmptyAndReady_def
                   gets_the_ogets readReleaseQueue_def gets_the_if_distrib
             flip: getReleaseQueue_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF getReleaseQueue_corres])
      apply (rule corres_if_strong[where R=\<top> and R'=\<top> and P=\<top> and P'=\<top>])
        apply (fastforce simp: tcbQueueEmpty_def)
       apply clarsimp
      apply (simp add: read_tcb_refill_ready_def read_tcb_obj_ref_def gets_the_thread_read
                       gets_the_assert_opt gets_the_ohaskell_assert
                 flip: threadGet_def get_sc_refill_ready_def refillReady_def)
      apply (rule_tac r'="(=)" in corres_split[OF threadGet_corres])
         apply (clarsimp simp: tcb_relation_def)
        apply (rule corres_assert_opt_l)
        apply (rule corres_assert_gen_asm2)
        apply (simp flip: scActive_def)
        apply (rule corres_symb_exec_r'[where Q'=\<top>])
           apply (rule corres_assert_gen_asm2)
           apply (rule refillReady_corres)
           apply fastforce
          apply wpsimp
         apply (rule scActive_inv)
         apply clarsimp
        apply wpsimp
       apply (wpsimp wp: thread_get_wp)
      apply (rule_tac Q'="\<lambda>rv s. \<exists>scPtr. rv = Some scPtr \<and> active_sc_at' scPtr s \<and> valid_objs' s"
                   in hoare_post_imp)
       apply (fastforce intro: valid_objs'_valid_refills'
                         simp: active_sc_at'_def is_active_sc'_def obj_at'_def
                               opt_pred_def opt_map_def)
      apply clarsimp
      apply (drule Some_to_the)
      apply (wpsimp wp: hoare_vcg_ex_lift threadGet_wp)
     apply wpsimp
    apply wpsimp
   apply (clarsimp simp: valid_release_q_def)
   apply (drule_tac x="hd (release_queue s)" in bspec)
    apply fastforce
   apply (fastforce elim!: valid_objs_valid_sched_context_size active_scs_validE[rotated]
                   intro!: valid_refills_nonempty_refills
                     simp: vs_all_heap_simps obj_at_def is_tcb_def is_sc_obj_def)
  apply (clarsimp split: if_splits)
  apply (rename_tac head)
  apply (frule (4) release_queue_active_sc_tcb_at_cross)
  apply (frule state_relation_release_queue_relation)
  apply (drule_tac x=head in spec)
  apply (clarsimp simp: release_queue_relation_def)
  apply (frule (3) obj_at'_tcbQueueHead_ksReleaseQueue)
  apply (clarsimp simp: tcbQueueEmpty_def)
  apply normalise_obj_at'
  apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
  by (fastforce simp: active_sc_tcb_at'_def opt_pred_def opt_map_def
                      obj_at'_def active_sc_at'_def  valid_bound_obj'_def valid_tcb'_def
               split: option.splits)

lemma release_queue_length_well_founded:
  "wf {((r :: unit, s :: 'a state), (r', s')). length (release_queue s) < length (release_queue s')}"
  apply (insert wf_inv_image[where r="{(m, n). m < n}"
                               and f="\<lambda>(r :: unit, s :: 'a state). length (release_queue s)"])
  apply (fastforce intro: rsubst[where P=wf])
  done

lemma tcb_release_dequeue_release_queue_length_helper:
  "\<lbrace>\<lambda>s'. release_queue s' \<noteq> [] \<and> s' = s\<rbrace>
   tcb_release_dequeue
   \<lbrace>\<lambda>_ s'. length (release_queue s') < length (release_queue s)\<rbrace>"
  apply (wpsimp simp: tcb_release_dequeue_def getReleaseQueue_def setReleaseQueue_def
                      tcb_release_remove_def tcb_sched_dequeue_def)
  apply (fastforce dest: hd_in_set intro: length_filter_less)
  done

lemma tcb_release_dequeue_release_queue_length:
  "\<lbrace>\<lambda>s'. the (read_release_q_non_empty_and_ready s') \<and> s' = s\<rbrace>
   tcb_release_dequeue
   \<lbrace>\<lambda>_ s'. length (release_queue s') < length (release_queue s)\<rbrace>"
  apply (wpsimp wp: tcb_release_dequeue_release_queue_length_helper)
  apply (clarsimp simp: read_release_q_non_empty_and_ready_simp)
  done

lemma awaken_terminates:
  "whileLoop_terminates (\<lambda>_ s. (the (read_release_q_non_empty_and_ready s)))
                        (\<lambda>_. tcb_release_dequeue) r' s"
  apply (rule_tac R="{((r', s'), (r, s)). length (release_queue s') < length (release_queue s)}"
               in whileLoop_terminates_inv)
    apply simp
   apply clarsimp
   apply (rule tcb_release_dequeue_release_queue_length)
  apply (rule release_queue_length_well_founded)
  done

definition tcb_release_remove' :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "tcb_release_remove' tcb_ptr \<equiv> do
     qs \<leftarrow> gets release_queue;
     when (tcb_ptr \<in> set qs) $ do
       when (hd qs = tcb_ptr) $ modify (reprogram_timer_update (\<lambda>_. True));
       set_release_queue (tcb_queue_remove tcb_ptr qs)
     od
   od"

lemma tcb_release_remove_monadic_rewrite:
  "monadic_rewrite False True (tcb_at tcb_ptr and (\<lambda>s. distinct (release_queue s)))
     (tcb_release_remove tcb_ptr) (tcb_release_remove' tcb_ptr)"
  supply if_split[split del]
  apply (clarsimp simp: tcb_release_remove_def tcb_release_remove'_def tcb_sched_dequeue_def)
  apply (rule monadic_rewrite_bind_tail)
   apply (clarsimp simp: when_def)
   apply (rule monadic_rewrite_if_r)

    (* tcb_ptr is in the release queue *)

    (* break off the reprogramming of the timer *)
    apply (rule monadic_rewrite_bind)
      apply (rule monadic_rewrite_if_known)

     apply (rule_tac P="\<lambda>_. distinct qs" in monadic_rewrite_guard_arg_cong)
     apply (erule (1) filter_tcb_queue_remove)
    apply wpsimp

   (* tcb_ptr is not in the release queue *)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_head)
    apply (rule monadic_rewrite_if_l_False)
    apply (rule monadic_rewrite_refl)
   apply (rule monadic_rewrite_drop_return)
   apply (rule monadic_rewrite_trans)
    apply (rule_tac P="\<lambda>s. release_queue s = qs" in monadic_rewrite_guard_arg_cong)
    apply (rule filter_True)
    apply clarsimp
   apply (rule monadic_rewrite_modify_noop)
  apply wpsimp
  apply fastforce
  done

crunch setReleaseQueue
  for ready_queues_relation[wp]: "\<lambda>s'. ready_queues_relation s s'"
  (simp: ready_queues_relation_def)

lemma tcbReleaseRemove_corres:
  "tcb_ptr = tcbPtr \<Longrightarrow>
   corres dc
     (tcb_at tcb_ptr and ready_or_release and (\<lambda>s. distinct (release_queue s))
      and pspace_aligned and pspace_distinct )
     (sym_heap_sched_pointers and valid_objs')
     (tcb_release_remove tcb_ptr) (tcbReleaseRemove tcbPtr)"
  supply if_split[split del]
         heap_path_append[simp del] fun_upd_apply[simp del] list_remove_append[simp del]
  apply (rule_tac Q'="tcb_at' tcbPtr" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: tcb_at_cross)
  apply (rule monadic_rewrite_corres_l[where P=P and Q=P for P, simplified])
   apply (fastforce intro: monadic_rewrite_guard_imp[OF tcb_release_remove_monadic_rewrite])
  apply (clarsimp simp: tcb_release_remove'_def tcbReleaseRemove_def)
  apply (rule corres_symb_exec_l[OF _ _ gets_sp]; wpsimp?)
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro: ready_or_release_cross)
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro: ksReleaseQueue_asrt_cross)
  apply (rule corres_symb_exec_r[OF _ inReleaseQueue_sp]; wpsimp?)
  apply (rule corres_underlying_lift_ex2')
  apply (clarsimp simp: when_def)
  apply (rule corres_if_strong'; fastforce?)
   apply (drule state_relation_release_queue_relation)
   apply (clarsimp simp: list_queue_relation_def release_queue_relation_def)
   apply (force simp: in_queue_2_def obj_at'_def opt_pred_def opt_map_def)
  apply (rule corres_symb_exec_r[rotated, OF getReleaseQueue_sp]; wpsimp?)

  \<comment> \<open>deal with the reprogram of the timer\<close>
  apply (rule corres_split_skip[rotated 2])
     apply (rule corres_if_strong')
       apply (drule state_relation_release_queue_relation)
       apply (clarsimp simp: list_queue_relation_def release_queue_relation_def)
       apply (force dest!: heap_path_head simp: list_queue_relation_def)
      apply corres
     apply clarsimp
    apply (find_goal \<open>match conclusion in "valid _ _ _" \<Rightarrow> wpsimp\<close>)+

  \<comment> \<open>setting the release queue\<close>
  apply (rule corres_from_valid_det)
    apply (fastforce intro: det_wp_modify det_wp_pre)
   apply (wpsimp wp: tcbQueueRemove_no_fail hoare_vcg_ex_lift threadSet_sched_pointers)
   apply (fastforce dest: state_relation_release_queue_relation
                    simp: ex_abs_def release_queue_relation_def list_queue_relation_def)
  apply (clarsimp simp: state_relation_def)
  apply (frule singleton_eqD)
  apply (drule set_release_queue_new_state)
  apply (intro hoare_vcg_conj_lift_pre_fix; (solves \<open>wpsimp simp: swp_def\<close>)?)

   apply (find_goal \<open>match conclusion in "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_. ready_queues_relation t\<rbrace>" for t \<Rightarrow> \<open>-\<close>\<close>)
   apply (wpsimp wp: tcbQueueRemove_list_queue_relation_other threadSet_sched_pointers
                     hoare_vcg_all_lift threadSet_inQ
               simp: ready_queues_relation_def ready_queue_relation_def Let_def
          | wps)+
   apply (rule_tac x="release_queue s" in exI)
   apply (auto dest: ready_or_release_disjoint simp: release_queue_relation_def Let_def)[1]

  apply (clarsimp simp: release_queue_relation_def)
  apply (frule singleton_eqD)
  apply (drule set_release_queue_new_state)
  apply (intro hoare_vcg_conj_lift_pre_fix)
   apply ((wpsimp wp: tcbQueueRemove_list_queue_relation threadSet_sched_pointers | wps)+)[1]

  apply (rule hoare_allI, rename_tac t')
  apply (subst set_tcb_queue_remove)
   apply clarsimp
  apply (case_tac "t' = tcbPtr")
   apply (wpsimp wp: threadSet_wp)
  apply (wpsimp wp: threadSet_opt_pred_other)
  done

lemma tcbInReleaseQueue_update_valid_tcbs'[wp]:
  "threadSet (tcbInReleaseQueue_update f) tcbPtr \<lbrace>valid_tcbs'\<rbrace>"
  by (wpsimp wp: threadSet_valid_tcbs')

lemma tcbQueueRemove_valid_tcbs'[wp]:
  "tcbQueueRemove queue tcbPtr \<lbrace>valid_tcbs'\<rbrace>"
  unfolding tcbQueueRemove_def
  apply (wpsimp wp: getTCB_wp hoare_drop_imps hoare_case_option_wp simp: opt_tcb_at'_def)
  apply (clarsimp simp: valid_tcbs'_def valid_tcb'_def obj_at'_def opt_tcb_at'_def)
  done

crunch tcbReleaseDequeue
  for valid_tcbs'[wp]: valid_tcbs'
  and valid_sched_pointers[wp]: valid_sched_pointers
  (wp: crunch_wps simp: crunch_simps)

crunch tcb_release_remove
  for ready_qs_distinct[wp]: ready_qs_distinct
  and in_correct_ready_q[wp]: in_correct_ready_q
  (rule: in_correct_ready_q_lift simp: crunch_simps ready_qs_distinct_def)

defs tcbQueueHead_ksReleaseQueue_active_sc_tcb_at'_asrt_def:
  "tcbQueueHead_ksReleaseQueue_active_sc_tcb_at'_asrt s \<equiv>
     \<forall>head. tcbQueueHead (ksReleaseQueue s) = Some head \<longrightarrow> active_sc_tcb_at' head s"

lemma tcbReleaseDequeue_corres:
  "corres dc
     (pspace_aligned and pspace_distinct and valid_sched_action
      and valid_objs and in_correct_ready_q and ready_qs_distinct
      and active_scs_valid and ready_or_release
      and valid_release_q and (\<lambda>s. release_queue s \<noteq> []))
     (valid_objs' and valid_sched_pointers and sym_heap_sched_pointers and pspace_bounded')
     tcb_release_dequeue tcbReleaseDequeue"
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest: pspace_distinct_cross)
  apply (clarsimp simp: tcb_release_dequeue_def tcbReleaseDequeue_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (fastforce intro: ksReleaseQueue_asrt_cross)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (fastforce simp: tcbInReleaseQueue_imp_active_sc_tcb_at'_asrt_def
                   dest!: release_queue_active_sc_tcb_at_cross)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF getReleaseQueue_corres])
      apply clarsimp
      apply (rename_tac rlq queue)
      apply (rule corres_symb_exec_r_conj_ex_abs_forwards)
         apply (rule corres_assert_assume_r)
         apply (rule_tac F="rlq \<noteq> []" in corres_gen_asm)
         apply simp
         apply (rule corres_split[OF tcbReleaseRemove_corres])
            apply fastforce
           apply (rule corres_add_noop_lhs2)
           apply (rule corres_add_noop_rhs2)
           apply (simp only: bind_assoc)
           apply (rule corres_split[OF possibleSwitchTo_corres])
              apply fastforce
             apply (rule corres_symb_exec_r_conj_ex_abs[where P'=\<top> and P=\<top>])
                apply (rule corres_symb_exec_r_conj_ex_abs
                             [where P'=\<top>
                                and P="valid_release_q and pspace_aligned and pspace_distinct
                                       and valid_objs"])
                   apply (rule corres_return_trivial)
                  apply wpsimp
                 apply wpsimp
                apply (wpsimp wp: no_fail_stateAssert)
                apply (clarsimp simp: ex_abs_def)
                apply (frule (4) release_queue_active_sc_tcb_at_cross)
                apply (fastforce dest!: state_relation_release_queue_relation
                                        tcbQueueHead_ksReleaseQueue
                                  simp: tcbQueueHead_ksReleaseQueue_active_sc_tcb_at'_asrt_def
                                        release_queue_relation_def tcbQueueEmpty_def)
               apply wpsimp+
             apply (wpsimp wp: no_fail_stateAssert)
             apply (fastforce intro: ksReleaseQueue_asrt_cross simp: ex_abs_def)
            apply wpsimp+
   apply (fastforce dest!: hd_in_set
                     simp: valid_release_q_def vs_all_heap_simps pred_tcb_at_def obj_at_def is_tcb_def)
  apply (fastforce dest: state_relation_release_queue_relation heap_path_head
                 intro!: st_tcb_at_runnable_cross
                   simp: valid_release_q_def vs_all_heap_simps pred_tcb_at_def obj_at_def
                         release_queue_relation_def list_queue_relation_def)
  done

crunch tcbReleaseDequeue
  for weak_sch_act_wf[wp]: "\<lambda>s'. weak_sch_act_wf (ksSchedulerAction s') s'"
  (wp: crunch_wps)

crunch tcb_release_dequeue
  for pred_tcb_at[wp]: "\<lambda>s. Q (pred_tcb_at proj P tptr s)"
  and released_sc_tcb_at[wp]: "released_sc_tcb_at t"

crunch tcb_release_dequeue
  for in_correct_ready_q[wp]: in_correct_ready_q
  (rule: in_correct_ready_q_lift ignore: tcb_sched_action)

crunch tcb_release_dequeue
  for ready_qs_distinct[wp]: ready_qs_distinct
  (rule: ready_qs_distinct_lift ignore: tcb_sched_action wp: crunch_wps)

lemma awaken_corres:
  "corres dc
     (pspace_aligned and pspace_distinct and valid_objs and valid_release_q
      and in_correct_ready_q and ready_qs_distinct
      and valid_sched_action and valid_tcbs and active_scs_valid and ready_or_release)
     (sym_heap_sched_pointers and valid_sched_pointers and valid_objs'
      and pspace_aligned' and pspace_distinct' and pspace_bounded')
     Schedule_A.awaken awaken"
  apply (clarsimp simp: awaken_def Schedule_A.awaken_def runReaderT_def)
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro: ksReleaseQueue_asrt_cross)
  apply (rule corres_stateAssert_ignore)
   apply (fastforce simp: tcbInReleaseQueue_imp_active_sc_tcb_at'_asrt_def
                   dest!: release_queue_active_sc_tcb_at_cross)
  apply (rule corres_whileLoop_abs; simp)
      apply (rule_tac f=read_release_q_non_empty_and_ready
                  and f'=releaseQNonEmptyAndReady
                   in gets_the_corres_relation[rotated])
          apply (rule gets_the_releaseQNonEmptyAndReady_corres)
         apply fastforce
        apply fastforce
       apply fastforce
      apply (clarsimp simp: no_ofail_def)
      apply (erule (1) valid_release_q_read_release_q_non_empty_and_ready_bound)
     apply (corres corres: tcbReleaseDequeue_corres)
      apply (fastforce simp: read_release_q_non_empty_and_ready_simp)
     apply fastforce
    apply (clarsimp simp: pred_conj_def)
    apply (intro hoare_vcg_conj_lift_pre_fix;
           (solves \<open>wpsimp simp: tcb_release_dequeue_def\<close>)?)
    apply (wpsimp wp: tcb_release_dequeue_valid_sched_action)
    apply (frule valid_release_q_read_release_q_non_empty_and_ready_bound)
     apply fastforce
    apply (fastforce dest: read_release_q_non_empty_and_ready_True_simp)
   apply ((wpsimp simp: tcbReleaseDequeue_def | wpsimp wp: hoare_drop_imps)+)[1]
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
    apply (rule_tac x=tcb' in exI, simp add: tcb_relation_cut_def)
    apply (prop_tac "tcbSchedContext tcb' = Some scp", clarsimp simp: tcb_relation_def, simp)
    apply (subgoal_tac "sc_at' scp s'", clarsimp)
     apply (frule_tac x=scp in pspace_relation_absD, erule state_relation_pspace_relation)
     apply (frule (1) valid_sched_context_size_objsI, clarsimp)
     apply (subgoal_tac "z = KOSchedContext ko", clarsimp)
      apply (frule (1) sc_ko_at_valid_objs_valid_sc', clarsimp)
      apply (clarsimp simp: valid_sched_context'_def sc_relation_def active_sc_def)
     apply (case_tac z; clarsimp simp: obj_at'_def)
    apply (erule cross_relF [OF _ sc_at'_cross_rel], clarsimp simp: obj_at_def is_sc_obj)
    apply (erule (1) valid_sched_context_size_objsI)
   apply (case_tac z; clarsimp simp: obj_at'_def)
  apply (subgoal_tac "tcb_at t s")
   apply (frule cross_relF [OF _ tcb_at'_cross_rel], clarsimp, assumption)
   apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: obj_at_def vs_all_heap_simps pred_map_def is_tcb)
  done

lemma threadGet_wp':
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> (\<exists>tcb. ko_at' tcb t s \<and> P (f tcb) s)\<rbrace>
   threadGet f t
   \<lbrace>P\<rbrace>"
  apply (simp add: threadGet_getObject)
  apply (wp getObject_tcb_wp)
  done

crunch setEndpoint, setReply, setNotification
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (wp: weak_sch_act_wf_lift)

crunch restart, suspend
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (wp: crunch_wps simp: crunch_simps)

lemma setNextInterrupt_corres:
  "corres dc ((\<lambda>s. active_sc_tcb_at (cur_thread s) s)
              and (\<lambda>s. \<forall>t \<in> set (release_queue s). active_sc_tcb_at t s)
              and valid_objs and pspace_aligned and pspace_distinct)
             valid_objs'
             set_next_interrupt
             setNextInterrupt"
  unfolding setNextInterrupt_def set_next_interrupt_def
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF getCurTime_corres])
      apply (rule corres_split[OF getCurThread_corres], simp)
        apply (rule corres_split_eqr[OF get_tcb_obj_ref_corres])
           apply (clarsimp simp: tcb_relation_def)
          apply (rule corres_assert_opt_assume_l)
          apply (rule corres_split[OF get_sc_corres])
            apply (rule_tac F="sc_valid_refills' rv'" in corres_gen_asm2)
            apply (rule corres_split[OF corres_if])
                 apply clarsimp
                apply (rule corres_split[OF getDomainTime_corres])
                  apply (simp only: fun_app_def)
                  apply (rule corres_return_eq_same)
                  apply (clarsimp simp: refill_hd_relation refill_map_def)
                 apply wpsimp
                apply wpsimp
               apply (rule corres_return_eq_same)
               apply (clarsimp simp: refill_hd_relation refill_map_def)
              apply (rule corres_split [OF getReleaseQueue_corres])
                apply (rename_tac rlq queue)
                apply (rule_tac r'="(=)" in corres_split)
                   apply (rule_tac R="\<lambda>s. release_queue s = rlq"
                               and R'="\<lambda>s. ksReleaseQueue s = queue"
                                in corres_if_strong)
                     apply (drule state_relation_release_queue_relation)
                     apply (fastforce simp: release_queue_relation_def tcbQueueEmpty_def)
                   apply (rule corres_return_eq_same)
                    apply simp
                   apply (rule_tac r'="(=)" in corres_split[OF get_tcb_obj_ref_corres'])
                       apply (clarsimp simp: tcb_relation_def)
                      apply fastforce
                     apply (rule corres_assert_opt_assume_l)
                     apply simp
                     apply (rule corres_split [OF get_sc_corres])
                       apply (rule_tac F="sc_valid_refills' rqSC" in corres_gen_asm2)
                       apply (rule corres_return_eq_same)
                       apply (clarsimp simp: refill_hd_relation refill_map_def)
                      apply wpsimp
                     apply wpsimp
                    apply (wpsimp wp: get_tcb_obj_ref_wp)
                   apply (wpsimp wp: threadGet_wp')
                  apply (rule corres_machine_op)
                  apply (simp del: dc_simp, rule setDeadline_corres, simp)
                 apply (wpsimp wp: get_tcb_obj_ref_wp threadGet_wp')+
   apply (fastforce intro!: valid_sched_context_size_objsI
                      dest: list.set_sel(1)
                      simp: vs_all_heap_simps obj_at_def is_tcb_def is_sc_obj_def)
  apply (clarsimp split: if_splits)
  apply (subgoal_tac "(\<exists>tcb. ko_at' tcb (ksCurThread s') s' \<and>
                    sc_at' (the (tcbSchedContext tcb)) s' \<and>
                    (\<forall>ko. ko_at' ko (the (tcbSchedContext tcb)) s' \<longrightarrow> sc_valid_refills' ko)) \<and>
                    (tcbQueueHead (ksReleaseQueue s') \<noteq> None \<longrightarrow>
                     (\<exists>tcb. ko_at' tcb (the (tcbQueueHead (ksReleaseQueue s'))) s' \<and>
                    sc_at' (the (tcbSchedContext tcb)) s' \<and>
                    (\<forall>ko. ko_at' ko (the (tcbSchedContext tcb)) s' \<longrightarrow> sc_valid_refills' ko)))")
   apply blast
  apply (intro conjI impI)
   apply (prop_tac "ksCurThread s' = cur_thread s", clarsimp simp: state_relation_def, simp)
   apply (rule setNextInterrupt_corres_helper; simp)
  apply (clarsimp simp: state_relation_def release_queue_relation_def)
  apply (rule setNextInterrupt_corres_helper; simp?)
   apply (clarsimp simp: state_relation_def release_queue_relation_def list_queue_relation_def)+
  apply (frule heap_path_head)
   apply fastforce
  apply (drule_tac x="hd (release_queue s)" in bspec)
   apply (rule hd_in_set)
   apply fastforce
  apply fastforce
  done

(* refillUnblockCheck_corres *)

lemma isRoundRobin_corres:
  "corres (=) (sc_at sc_ptr) (sc_at' sc_ptr)
              (is_round_robin sc_ptr) (isRoundRobin sc_ptr)"
  apply (clarsimp simp: is_round_robin_def isRoundRobin_def)
  apply (corresKsimp corres: get_sc_corres
                      simp: sc_relation_def)
  done

lemma refillPopHead_refillSize:
  "\<lbrakk>sc_valid_refills' sc'; 1 < refillSize sc'\<rbrakk>
   \<Longrightarrow> refillSize (scRefillHead_update (\<lambda>_. refillNext sc' (scRefillHead sc')) sc')
       = refillSize sc' - 1"
  by (auto simp: refillSize_def refillNext_def split: if_splits)

lemma length_sc_refills_cross:
  "\<lbrakk>(s, s') \<in> state_relation; sc_at scp s; sc_at' scp s'; valid_refills' scp s'\<rbrakk>
   \<Longrightarrow> ((\<lambda>sc. P (length (sc_refills sc))) |< scs_of2 s) scp
       = ((\<lambda>sc'. P (refillSize sc')) |< scs_of' s') scp"
  apply (drule (2) state_relation_sc_relation)
  apply (clarsimp simp: obj_at_simps is_sc_obj valid_refills'_def sc_relation_def opt_map_red
                        opt_pred_def)
  done

crunch getRefillNext
  for inv[wp]: P

lemma refillPopHead_corres:
  "sc_ptr = scPtr \<Longrightarrow>
   corres (\<lambda>refill refill'. refill = refill_map refill')
     (\<lambda>s. sc_at sc_ptr s \<and> pspace_aligned s \<and> pspace_distinct s
          \<and> sc_refills_sc_at (\<lambda>refills. 1 < length refills) sc_ptr s
          \<and> valid_objs s \<and> is_active_sc sc_ptr s)
     (valid_objs' and valid_refills' sc_ptr)
     (refill_pop_head sc_ptr) (refillPopHead scPtr)"
  apply (add_active_sc_at' scPtr)
  apply (rule corres_cross[where Q' = "sc_at' sc_ptr", OF sc_at'_cross_rel], fastforce)
  apply (clarsimp simp: refill_pop_head_def refillPopHead_def)
  apply (rule corres_stateAssert_ignore, simp)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF getRefillHead_corres], simp)
      apply (rule corres_symb_exec_r'[OF _ _ hoare_eq_P[OF get_sc_inv']])
         apply (rule corres_symb_exec_r'[OF _ _ hoare_eq_P[OF getRefillNext_inv]])
            apply (rule_tac Q1=\<top>
                        and Q'1="\<lambda>sc'. sc_valid_refills' sc' \<and> 1 < refillSize sc'
                                       \<and> next = refillNext sc' (scRefillHead sc')"
                     in corres_split[OF updateSchedContext_no_stack_update_corres_Q])
                  apply (clarsimp simp: sc_relation_def refills_map_def tl_map)
                  apply (subst refillPopHead_refillSize; fastforce?)
                  apply (subst tl_wrap_slice)
                     apply (clarsimp simp: refillSize_def split: if_splits)
                    apply fastforce
                   apply fastforce
                  apply (clarsimp simp: refillNext_def wrap_slice_start_0 split: if_splits)
                 apply clarsimp
                apply (clarsimp simp: objBits_simps)
               apply (wpsimp | wpsimp wp: getRefillNext_wp)+
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
  by (fastforce dest: length_sc_refills_cross valid_objs'_valid_refills'
                simp: valid_refills'_def obj_at'_def sc_at_pred_n_def obj_at_def opt_map_def
                      opt_pred_def)

lemma refillPopHead_valid_refills'[wp]:
  "\<lbrace>\<lambda>s. valid_refills' scPtr' s
        \<and> (scPtr = scPtr' \<longrightarrow> obj_at' (\<lambda>sc'. Suc 0 < refillSize sc') scPtr s)\<rbrace>
   refillPopHead scPtr
   \<lbrace>\<lambda>_. valid_refills' scPtr'\<rbrace>"
  apply (clarsimp simp: refillPopHead_def updateSchedContext_def setSchedContext_def)
  apply (wpsimp wp: setObject_sc_wp getRefillNext_wp)
  by (fastforce simp: valid_refills'_def obj_at'_def opt_map_def opt_pred_def refillSize_def
                      refillNext_def)

lemma refillHeadOverlapping_simp:
  "\<lbrakk>active_sc_at' sc_ptr s'; valid_refills' sc_ptr s'\<rbrakk> \<Longrightarrow>
   refillHeadOverlapping sc_ptr s' =
    (scs_of' s' ||> (\<lambda>sc'. Suc 0 < refillSize sc'
                           \<and> rTime (scRefills sc' ! (if scRefillHead sc' = scRefillMax sc' - Suc 0
                                                     then 0 else Suc (scRefillHead sc')))
                             \<le> rTime (refillHd sc') + rAmount (refillHd sc'))) sc_ptr"
  unfolding refillHeadOverlapping_def
  apply (clarsimp simp: active_sc_at'_rewrite)
  apply (frule no_ofailD[OF no_ofail_readSchedContext])
  apply (clarsimp simp: obind_def omonad_defs oliftM_def obj_at'_def readRefillNext_def
                        readRefillSize_def refillIndex_def opt_map_red readSchedContext_def
                        refillSize_def valid_refills'_def in_omonad refillNext_def
                        readRefillHead_def readRefillIndex_def readRefillSingle_def
                        active_sc_at'_rewrite ostate_assert_def
                 dest!: readObject_ko_at'_sc split: option.splits if_splits)
  apply fastforce
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
  "\<lbrakk>(s, s') \<in> state_relation; sc_at sc_ptr s; active_sc_at' sc_ptr s'; valid_refills' sc_ptr s'\<rbrakk>
   \<Longrightarrow> refill_head_overlapping sc_ptr s = refillHeadOverlapping sc_ptr s'"
  apply (frule no_ofailD[OF no_ofail_refillHeadOverlapping])
  apply (clarsimp simp: active_sc_at'_rewrite)
  apply (drule (2) state_relation_sc_relation)
  apply (clarsimp simp: obj_at_simps is_sc_obj)
  apply (rename_tac b n sc sc')
  apply (case_tac b;
         clarsimp simp: refillHeadOverlapping_simp refill_head_overlapping_simp obj_at_simps
                        is_sc_obj sc_relation_def valid_refills'_def refillHd_def
                        neq_Nil_lengthI tl_drop_1 hd_drop_conv_nth refills_map_def hd_map
                        hd_wrap_slice wrap_slice_index refill_map_def opt_map_red opt_pred_def
                        active_sc_at'_rewrite
                 split: if_split_asm)
  by linarith+

crunch update_refill_hd, refill_pop_head, merge_overlapping_refills, schedule_used,
       charge_entire_head_refill
  for is_active_sc2[wp]: "is_active_sc2 scp"
  (wp: crunch_wps ignore: update_sched_context
   simp: crunch_simps update_refill_hd_rewrite update_sched_context_set_refills_rewrite)

lemma merge_overlapping_refills_scs_of2[wp]:
  "\<lbrace>\<lambda>s. P ((scs_of2 s)(scp \<mapsto> (\<lambda>sc. sc_refills_update
            (\<lambda>_. merge_refill (refill_hd sc) (hd (tl (sc_refills sc))) # tl (tl (sc_refills sc))) sc)
                          (the (scs_of2 s scp)))) \<rbrace>
   merge_overlapping_refills scp
   \<lbrace>\<lambda>_ s. P (scs_of2 s)\<rbrace>"
  unfolding merge_overlapping_refills_def
  apply (wpsimp simp: update_refill_hd_rewrite refill_pop_head_def
                  wp: get_refills_wp set_refills_wp update_sched_context_wp)
  by (clarsimp simp: is_active_sc2_def obj_at_def opt_map_red)

lemma update_refill_hd_decompose:
  "update_refill_hd sc_ptr (g o f) = do update_refill_hd sc_ptr f; update_refill_hd sc_ptr g od"
  apply (clarsimp simp: update_refill_hd_def)
  apply (subst bind_dummy_ret_val)
  apply (subst update_sched_context_decompose[symmetric])
  apply fastforce
  done

lemma merge_refill_def2:
  "update_refill_hd sc_ptr (merge_refill hd_refill)
   = do update_refill_hd sc_ptr (r_time_update (\<lambda>_. r_time hd_refill));
        update_refill_hd sc_ptr (\<lambda>hd. r_amount_update (\<lambda>_. r_amount hd + r_amount hd_refill) hd)
     od"
  unfolding merge_refill_def
  apply (subst update_refill_hd_decompose[symmetric])
  apply (fastforce intro: arg_cong2[where f = update_refill_hd])
  done

lemma updateRefillHd_valid_refills'[wp]:
  "updateRefillHd scPtr f \<lbrace>valid_refills' scPtr'\<rbrace>"
  apply (clarsimp simp: updateRefillHd_def updateSchedContext_def setSchedContext_def)
  apply (wpsimp wp: setObject_sc_wp)
  apply (fastforce simp: valid_refills'_def obj_at'_def opt_map_def opt_pred_def refillSize_def)
  done

lemma updateRefillTl_valid_refills'[wp]:
  "updateRefillTl scPtr f \<lbrace>valid_refills' scPtr'\<rbrace>"
  apply (clarsimp simp: updateRefillTl_def updateSchedContext_def setSchedContext_def)
  apply (wpsimp wp: setObject_sc_wp)
  apply (fastforce simp: valid_refills'_def obj_at'_def opt_map_def opt_pred_def refillSize_def)
  done

(* if the loop guard is true, the refill length is greater than one *)
lemma mergeOverlappingRefills_corres:
  "corres dc
     (sc_at sc_ptr and pspace_aligned and pspace_distinct
      and (\<lambda>s. ((\<lambda>sc. 1 < length (sc_refills sc)) |< scs_of2 s) sc_ptr) and valid_objs
      and is_active_sc sc_ptr)
     (valid_objs' and valid_refills' sc_ptr)
     (merge_overlapping_refills sc_ptr) (mergeOverlappingRefills sc_ptr)"
  unfolding mergeOverlappingRefills_def merge_overlapping_refills_def merge_refill_def2
  apply (rule corres_cross[where Q' = "sc_at' sc_ptr", OF sc_at'_cross_rel], fastforce)
  apply (rule_tac Q'="\<lambda>s'. ((\<lambda>sc'. 1 < refillSize sc') |< scs_of' s') sc_ptr" in corres_cross_add_guard)
   apply clarsimp
   apply (drule (2) state_relation_sc_relation)
   apply (clarsimp simp: sc_relation_def)
   apply (clarsimp simp: valid_refills'_def obj_at_simps is_sc_obj opt_map_red opt_pred_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF refillPopHead_corres], simp)
      apply (rule corres_split[OF updateRefillHd_corres], simp)
         apply (clarsimp simp: refill_map_def)+
        apply (rule updateRefillHd_corres, simp)
        apply (clarsimp simp: refill_map_def)
       apply (rule hoare_strengthen_post[where Q'="\<lambda>_. sc_at sc_ptr", rotated])
        apply (simp add: active_sc_at_equiv is_active_sc_rewrite[symmetric])
       apply (wpsimp wp: refill_pop_head_sc_active)+
   apply (clarsimp simp: obj_at_def is_sc_obj opt_map_red is_active_sc_rewrite active_sc_at_equiv
                         sc_refills_sc_at_rewrite)
  apply (fastforce simp: valid_refills'_def obj_at_simps opt_map_red opt_pred_def refillNext_def)
  done

lemma mergeOverlappingRefills_valid_refills'[wp]:
  "\<lbrace>obj_at'(\<lambda>sc. 1 < refillSize sc) scp and valid_refills' scp\<rbrace>
   mergeOverlappingRefills p
   \<lbrace>\<lambda>_. valid_refills' scp\<rbrace>"
  unfolding mergeOverlappingRefills_def
  by (wpsimp simp: updateRefillHd_def refillPopHead_def wp: updateSchedContext_wp getRefillNext_wp)

lemma no_fail_getRefillHead[wp]:
  "no_fail (active_sc_at' scPtr) (getRefillHead scPtr)"
  apply (wpsimp simp: getRefillHead_def)
  apply (erule no_ofailD[OF no_ofail_readRefillHead])
  done

lemma no_fail_refillPopHead[wp]:
  "no_fail (active_sc_at' scPtr) (refillPopHead scPtr)"
  unfolding refillPopHead_def
  apply (wpsimp wp: getRefillNext_wp no_fail_stateAssert)
  by (clarsimp simp: active_sc_at'_rewrite obj_at'_def opt_map_def opt_pred_def objBits_simps)

crunch mergeOverlappingRefills
  for (no_fail) no_fail[wp]
  (simp: opt_map_red opt_pred_def obj_at_simps)

lemma refillPopHead_length_decreasing:
  "\<lbrace>\<lambda>s'. ((\<lambda>sc. 1 < refillSize sc \<and> sc_valid_refills' sc) |< scs_of' s') scp \<and> s' = s\<rbrace>
   refillPopHead scp
   \<lbrace>\<lambda>r' s'. refillSize (the (scs_of' s' scp)) < refillSize (the (scs_of' s scp))\<rbrace>"
  unfolding refillPopHead_def
  apply (simp add: liftM_def bind_assoc refillHd_def)
  apply (wpsimp wp: updateSchedContext_wp getRefillNext_wp)
  apply (fastforce simp: obj_at'_def opt_map_red opt_pred_def refillSize_def refillNext_def
                  split: if_splits)
  done

lemma mergeOverlappingRefills_length_decreasing:
  "\<lbrace>\<lambda>s'. ((\<lambda>sc. 1 < refillSize sc \<and> sc_valid_refills' sc) |< scs_of' s') scp \<and> s' = s\<rbrace>
   mergeOverlappingRefills scp
   \<lbrace>\<lambda>r' s'. refillSize (the (scs_of' s' scp)) < refillSize (the (scs_of' s scp))\<rbrace>"
  unfolding mergeOverlappingRefills_def updateRefillHd_def
  apply (rule bind_wp[OF _ refillPopHead_length_decreasing])
  apply (wpsimp wp: refillPopHead_length_decreasing updateSchedContext_wp)
  apply (clarsimp simp: refillSize_def split: if_splits)
  done

lemma refillSize_wf:
  "wf {((r', s'), r, s). refillSize (the (scs_of' s' sc_ptr)) < refillSize (the (scs_of' s sc_ptr))}"
  apply (prop_tac "{((r', s'), r, s). refillSize (the (scs_of' s' sc_ptr))
                                             < refillSize (the (scs_of' s sc_ptr))}
                   = measure (\<lambda>(r, s). refillSize (the (scs_of' s sc_ptr)))")
   apply (clarsimp simp: measure_def inv_image_def split_def)
  apply (drule sym)
  apply (erule subst)
  apply (rule wf_measure)
  done

lemma mergeOverlappingRefills_terminates:
  "\<lbrakk>active_sc_at' sc_ptr s'; valid_objs' s'\<rbrakk>
   \<Longrightarrow> whileLoop_terminates
        (\<lambda>_ s'. the (refillHeadOverlapping sc_ptr s'))
        (\<lambda>_. mergeOverlappingRefills sc_ptr) r' s'"
  apply (rule_tac I="\<lambda>_. active_sc_at' sc_ptr and valid_objs'"
              and R="{((r', s'), (r, s)). refillSize (the (scs_of' s' sc_ptr))
                                          < refillSize (the (scs_of' s sc_ptr))}"
               in whileLoop_terminates_inv)
    apply simp
   apply (rename_tac s)
   apply (wpsimp wp: mergeOverlappingRefills_length_decreasing mergeOverlappingRefills_valid_objs')
   apply (frule_tac s=s in no_ofailD[OF no_ofail_refillHeadOverlapping])
   apply clarsimp
   apply (frule use_ovalid[OF refillHeadOverlapping_refillSize])
    apply (fastforce intro!: valid_objs'_valid_refills' simp: active_sc_at'_rewrite)
   apply (fastforce dest: valid_objs'_valid_refills'
                    simp: active_sc_at'_rewrite opt_pred_def opt_map_def valid_refills'_def
                          obj_at'_def)
  apply (rule refillSize_wf)
  done

crunch merge_overlapping_refills
  for valid_objs[wp]: valid_objs
  (wp: crunch_wps)

lemma refillHeadOverlappingLoop_corres:
  "corres dc
     (sc_at sc_ptr and pspace_aligned and pspace_distinct and valid_objs and is_active_sc sc_ptr)
     (valid_objs' and valid_refills' sc_ptr)
     (refill_head_overlapping_loop sc_ptr) (refillHeadOverlappingLoop sc_ptr)"
  unfolding refill_head_overlapping_loop_def refillHeadOverlappingLoop_def runReaderT_def
  apply (rule_tac Q'="active_sc_at' sc_ptr" in corres_cross_add_guard)
   apply (fastforce intro!: active_sc_at'_cross_valid_objs)
  apply (rule corres_whileLoop)
        apply (drule refillHeadOverlapping_corres_eq[where sc_ptr=sc_ptr];
               simp add: runReaderT_def active_sc_at'_rewrite)
       apply simp
       apply (rule corres_guard_imp
                      [where P=P and Q=P for P,
                       where
                          P'= Q and
                          Q'="Q and (\<lambda>s. ((\<lambda>sc. 1 < refillSize sc) |< scs_of' s) sc_ptr)" for Q])
         apply (rule corres_cross_add_abs_guard
                       [where Q="(\<lambda>s. ((\<lambda>sc. 1 < length (sc_refills sc)) |< scs_of2 s) sc_ptr)"])
          apply (drule state_relation_sc_relation)
            apply fastforce
           apply (clarsimp simp: active_sc_at'_rewrite)
          apply (clarsimp simp: obj_at_simps is_sc_obj valid_refills'_def sc_relation_def
                                opt_map_red opt_pred_def active_sc_at'_rewrite)
         apply (corres corres: mergeOverlappingRefills_corres)
        apply fastforce
       apply clarsimp
       apply (frule no_ofailD[OF no_ofail_refillHeadOverlapping])
       apply clarsimp
       apply (fastforce dest!: use_ovalid[OF refillHeadOverlapping_refillSize])
      apply (wpsimp simp: is_active_sc_rewrite)
     apply (wpsimp wp: mergeOverlappingRefills_valid_objs')
     apply (frule no_ofailD[OF no_ofail_refillHeadOverlapping])
     apply (fastforce dest: use_ovalid[OF refillHeadOverlapping_refillSize]
                      simp: active_sc_at'_rewrite opt_pred_def opt_map_def obj_at'_def)
     apply clarsimp
   apply wpsimp
   apply (fastforce simp: active_sc_at'_rewrite)
  apply (fastforce intro!: mergeOverlappingRefills_terminates)
  done

lemma ksReprogramTimer_update_valid_refills'[simp]:
  "valid_refills' scPtr (ksReprogramTimer_update f s) = valid_refills' scPtr s"
  by (clarsimp simp: valid_refills'_def)

lemma refillUnblockCheck_corres:
  "corres dc
     (sc_at scp and pspace_aligned and pspace_distinct
      and (\<lambda>s. ((\<lambda>sc. 0 < length (sc_refills sc)) |< scs_of2 s) scp)
      and valid_objs and is_active_sc scp)
     (valid_objs' and valid_refills' scp)
     (refill_unblock_check scp) (refillUnblockCheck scp)"
  unfolding refill_unblock_check_def refillUnblockCheck_def haskell_assert_def
  apply (rule_tac Q'="active_sc_at' scp" in corres_cross_add_guard)
   apply (fastforce intro!: active_sc_at'_cross_valid_objs)
  apply (intro corres_symb_exec_r'[OF _ scActive_sp]; (solves \<open>wpsimp simp: \<close>)?)
   apply (rule corres_assert_gen_asm_cross[where P=P' and P'=P' for P',
                                           where Q=Q' and Q'=Q' for Q', simplified])
   apply (fastforce dest!: active_sc_at'_cross_valid_objs simp: active_sc_at'_def obj_at'_def)
   apply simp
   apply (rule corres_guard_imp)
     apply (rule corres_split_eqr[OF isRoundRobin_corres])
       apply (rule corres_split_eqr[OF refillReady_corres], simp)
         apply (rule corres_when, fastforce)
         apply (rule corres_split[OF getCurTime_corres])
           apply (rule corres_split[OF updateRefillHd_corres], simp)
              apply (clarsimp simp: refill_map_def)
             apply (rule corres_split[OF setReprogramTimer_corres])
               apply (rule refillHeadOverlappingLoop_corres)
              apply (wpsimp simp: setReprogramTimer_def)+
      apply (wpsimp wp: is_round_robin_wp isRoundRobin_wp)+
    apply (clarsimp simp: obj_at_simps opt_map_red opt_pred_def is_active_sc_rewrite
                          sc_at_pred_n_def
                   split: Structures_A.kernel_object.splits)
   apply (fastforce dest!: valid_objs'_valid_refills'
                     simp: obj_at_simps opt_map_red opt_pred_def is_active_sc'_def)
  apply (wpsimp simp: active_sc_at'_rewrite)
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
                           \<and> (((\<lambda>sc. case_option (sc_active sc) \<top> act) |< scs_of2 s) scp)
                           \<and> valid_objs s) scp_opt)
     (\<lambda>s. case_option True (\<lambda>scp. case_option (valid_objs' s \<and> valid_refills' scp s)
                                              (\<lambda>_. valid_objs' s) act) scp_opt)
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

lemma refillSize_refillAddTail:
  "\<lbrakk>refillSize sc' < scRefillMax sc'; sc_valid_refills' sc'\<rbrakk> \<Longrightarrow>
   refillSize (scRefills_update
                (\<lambda>_. replaceAt (refillNext sc' (scRefillTail sc')) (scRefills sc') new')
                (scRefillTail_update (\<lambda>_. refillNext sc' (scRefillTail sc')) sc'))
   = Suc (refillSize sc')"
  by (fastforce simp: refillSize_def refillNext_def split: if_splits)

lemma getRefillNext_sp:
  "\<lbrace>P\<rbrace> getRefillNext scPtr index \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. ko_at' sc scPtr s \<and> rv = refillNext sc index)\<rbrace>"
  apply (wpsimp wp: getRefillNext_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma no_ofail_readRefillSize[wp]:
  "no_ofail (sc_at' scPtr) (readRefillSize scPtr)"
  supply ovalid_readObject[wp del]
  unfolding readRefillSize_def readSchedContext_def
  apply wpsimp
  done

lemma no_fail_getRefillSize[wp]:
  "no_fail (sc_at' scPtr) (getRefillSize scPtr)"
  apply (wpsimp simp: getRefillSize_def)
  apply (erule no_ofailD[OF no_ofail_readRefillSize])
  done

lemma refillAddTail_corres:
  "\<lbrakk>new = refill_map new'; sc_ptr = scPtr\<rbrakk> \<Longrightarrow>
   corres dc
     (is_active_sc sc_ptr and sc_at sc_ptr and pspace_aligned and pspace_distinct)
     (\<lambda>s'. ((\<lambda>sc'. refillSize sc' < scRefillMax sc' \<and> sc_valid_refills' sc') |< scs_of' s') sc_ptr)
     (refill_add_tail sc_ptr new) (refillAddTail scPtr new')"
  apply (add_active_sc_at' sc_ptr)
  apply (rule corres_cross[where Q' = "sc_at' sc_ptr", OF sc_at'_cross_rel], fastforce)
  apply (clarsimp simp: refill_add_tail_def refillAddTail_def)
  apply (rule corres_stateAssert_ignore, simp)
  apply (rule corres_symb_exec_r[OF _ getRefillSize_sp])
    apply (rule corres_symb_exec_r[OF _ get_sc_sp'], rename_tac sc)
      apply (rule corres_symb_exec_r[OF _ assert_sp])
        apply (rule corres_symb_exec_r[OF _ getRefillNext_sp], rename_tac "next")
          apply (clarsimp simp: updateRefillIndex_def)
          apply (rule corres_guard_imp)
            apply (rule monadic_rewrite_corres_r)
             apply (rule monadic_rewrite_guard_imp)
              apply (subst bind_dummy_ret_val)
              apply (rule updateSchedContext_decompose[THEN monadic_rewrite_sym])
             apply (fastforce simp: objBits_simps)
            apply (rule_tac Q'="\<lambda>sc'. refillSize sc' < scRefillMax sc' \<and> sc_valid_refills' sc'
                                      \<and> next = refillNext sc' (scRefillTail sc')"
                         in updateSchedContext_no_stack_update_corres_Q[where Q=\<top>])
               apply (clarsimp simp: obj_at_simps is_sc_obj)
               apply (clarsimp simp: sc_relation_def neq_Nil_lengthI opt_map_red refills_map_def)
               apply (subst refillSize_refillAddTail; simp)
               apply (subst wrap_slice_append; fastforce?)
               subgoal
                 by (fastforce simp: wrap_slice_updateAt_eq[symmetric] neq_Nil_lengthI
                                     nat_le_Suc_less updateAt_index refillNext_def refillSize_def)
              apply fastforce
             apply (clarsimp simp: objBits_simps)
            apply fastforce
           apply (clarsimp simp: obj_at_def is_sc_obj_def)
           apply (rename_tac ko n, case_tac ko; clarsimp)
          apply (clarsimp simp: obj_at'_def in_omonad)
         apply (wpsimp wp: getRefillNext_wp)
         apply (clarsimp simp: obj_at'_def in_omonad)
        apply wpsimp+
      apply (clarsimp simp: obj_at'_def in_omonad)
     apply (wpsimp wp: getRefillSize_wp)+
  done

lemma isRoundRobin_sp:
  "\<lbrace>P\<rbrace>
   isRoundRobin scPtr
   \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. ko_at' sc scPtr s \<and> rv = (scPeriod sc = 0))\<rbrace>"
  apply (simp add: isRoundRobin_def)
  apply (rule bind_wp_fwd)
   apply (rule get_sc_sp')
  apply (wp hoare_return_sp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma maybeAddEmptyTail_corres:
  "corres dc
     (is_active_sc2 sc_ptr and sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr
      and valid_objs and pspace_aligned and pspace_distinct)
     (sc_at' sc_ptr and valid_objs'
      and (\<lambda>s'. ((\<lambda>sc'. refillSize sc' < scRefillMax sc' \<and> sc_valid_refills' sc') |< scs_of' s') sc_ptr))
     (maybe_add_empty_tail sc_ptr) (maybeAddEmptyTail sc_ptr)"
  (is "corres _ ?abs ?conc _ _")
  supply projection_rewrites[simp]
  apply (rule corres_cross_add_abs_guard[where Q="sc_at sc_ptr"])
   apply (fastforce dest!: sc_at'_cross[OF state_relation_pspace_relation])
  apply (clarsimp simp: maybe_add_empty_tail_def maybeAddEmptyTail_def get_refills_def)
  apply (rule corres_underlying_split[rotated 2, OF is_round_robin_sp isRoundRobin_sp])
   apply (corresKsimp corres: isRoundRobin_corres)
  apply (clarsimp simp: obj_at_def is_sc_obj)
  apply (clarsimp simp: when_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getRefillHead_corres], simp)
       apply simp
      apply (rule refillAddTail_corres)
       apply (clarsimp simp: refill_map_def)
      apply simp
     apply (wpsimp wp: get_refill_head_wp)
    apply (wpsimp wp: getRefillHead_wp)
   apply (clarsimp simp: is_active_sc_rewrite[symmetric] obj_at_def is_sc_obj_def)
  apply clarsimp
  done

lemma getRefills_sp:
  "\<lbrace>P\<rbrace>
   getRefills scPtr
   \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. ko_at' sc scPtr s \<and> (rv = scRefills sc))\<rbrace>"
  apply (simp add: getRefills_def)
  apply (rule bind_wp_fwd)
   apply (rule get_sc_sp')
  apply (wp hoare_return_sp)
  apply (clarsimp simp: obj_at'_def)
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
  apply (rule_tac Q'="\<lambda>s. is_active_sc' (ksCurSc s) s" in corres_cross_add_guard)
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
  apply (clarsimp simp: is_active_sc'_def obj_at'_def opt_map_red opt_pred_def)
  done

lemma refillPopHead_is_active_sc_at'[wp]:
  "refillPopHead scPtr \<lbrace>is_active_sc' scPtr'\<rbrace>"
  apply (simp add: refillPopHead_def)
  apply (wpsimp wp: updateSchedContext_is_active_sc_at' getRefillNext_wp)
  done

lemma mergeNonoverlappingHeadRefill_corres:
  "sc_ptr = scPtr \<Longrightarrow>
   corres dc
     (pspace_aligned and pspace_distinct and sc_at sc_ptr and is_active_sc sc_ptr
      and valid_objs
      and (\<lambda>s. sc_refills_sc_at (\<lambda>refills. Suc 0 < length refills) sc_ptr s))
     (valid_objs' and valid_refills' sc_ptr)
     (merge_nonoverlapping_head_refill sc_ptr) (mergeNonoverlappingHeadRefill scPtr)"
  apply (clarsimp simp: merge_nonoverlapping_head_refill_def mergeNonoverlappingHeadRefill_def)
  apply (rule corres_cross[OF sc_at'_cross_rel[where t=scPtr]], simp)
  apply (rule_tac Q'="is_active_sc' scPtr" in corres_cross_add_guard)
   apply (fastforce dest: is_active_sc'2_cross)
  apply (rule_tac Q'="obj_at' (\<lambda>sc'. Suc 0 < refillSize sc') scPtr"
                  in corres_cross_add_guard)
   apply (fastforce dest!: length_sc_refills_cross[where P="\<lambda>l. Suc 0 < l"]
                     simp: opt_map_red opt_pred_def vs_all_heap_simps obj_at'_def
                           sc_at_ppred_def obj_at_def)
  apply (rule_tac Q="\<lambda>_. sc_at sc_ptr and is_active_sc sc_ptr"
              and Q'="\<lambda>_. valid_refills' scPtr and sc_at' scPtr"
               in corres_underlying_split;
         (solves wpsimp)?)
   apply (corres corres: refillPopHead_corres
                   simp: obj_at_def vs_all_heap_simps pred_map_simps sc_at_ppred_def)
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

lemma refill_pop_head_sched_context_at[wp]:
  "refill_pop_head sc_ptr' \<lbrace>\<lambda>s. \<exists>sc n. kheap s sc_ptr = Some (Structures_A.SchedContext sc n)\<rbrace>"
  apply (clarsimp simp: refill_pop_head_def)
  apply (wpsimp wp: update_sched_context_wp)
  done

crunch merge_nonoverlapping_head_refill
  for valid_objs[wp]: valid_objs

definition head_insufficient_loop_measure where
  "head_insufficient_loop_measure sc_ptr
     \<equiv> measure (\<lambda>(_, s). case kheap s sc_ptr of Some (Structures_A.SchedContext sc _)
                                             \<Rightarrow> length (sc_refills sc))"

lemma non_overlapping_merge_refills_terminates:
  "\<lbrakk>pred_map (\<lambda>cfg. refills_unat_sum (scrc_refills cfg) \<le> unat max_time)
             (sc_refill_cfgs_of s) sc_ptr;
    pred_map (\<lambda>cfg. unat MIN_BUDGET \<le> refills_unat_sum (scrc_refills cfg))
             (sc_refill_cfgs_of s) sc_ptr;
    sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr s\<rbrakk>
   \<Longrightarrow> whileLoop_terminates (\<lambda>_ s. the (refill_head_insufficient sc_ptr s))
                            (\<lambda>_. merge_nonoverlapping_head_refill sc_ptr) r s"
  (is "\<lbrakk>?P s; ?Q s; ?R s\<rbrakk> \<Longrightarrow> _")
  apply (rule_tac I="\<lambda>_. ?P and ?Q and ?R"
               in whileLoop_terminates_inv[where R="head_insufficient_loop_measure sc_ptr"])
    apply simp
   apply (intro hoare_vcg_conj_lift_pre_fix)
    apply (wpsimp wp: merge_nonoverlapping_head_refill_refills_unat_sum_lower_bound
                      merge_nonoverlapping_head_refill_refills_unat_sum
                      merge_nonoverlapping_head_refill_nonempty_refills)
    apply (fastforce dest: no_ofailD[OF no_ofail_head_insufficient] head_insufficient_length)
   apply (wpsimp wp: update_sched_context_wp
               simp: head_insufficient_loop_measure_def merge_nonoverlapping_head_refill_def
                     refill_pop_head_def update_refill_hd_def)
    apply (fastforce dest: no_ofailD[OF no_ofail_head_insufficient] head_insufficient_length
                     simp: vs_all_heap_simps obj_at_def sc_at_ppred_def)
  apply (clarsimp simp: head_insufficient_loop_measure_def)
  done

lemma refills_unat_sum_MIN_BUDGET_implies_non_empty_refills:
  "pred_map (\<lambda>cfg. unat MIN_BUDGET \<le> refills_unat_sum (scrc_refills cfg)) (sc_refill_cfgs_of s) sc_ptr
   \<Longrightarrow> sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr s"
  by (auto simp: vs_all_heap_simps refills_unat_sum_def MIN_BUDGET_nonzero unat_eq_zero
                 sc_at_ppred_def obj_at_def)

lemma gets_the_refillHdInsufficient_corres:
  "sc_ptr = scPtr \<Longrightarrow>
   corres (=)
     (valid_objs and pspace_aligned and pspace_distinct
      and is_active_sc sc_ptr and sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr)
     valid_objs'
     (gets_the (refill_head_insufficient sc_ptr)) (gets_the (refillHdInsufficient scPtr))"
  apply (simp add: refill_head_insufficient_def refillHdInsufficient_def
             flip: get_refill_head_def getRefillHead_def)
  apply (corres corres: getRefillHead_corres)
      apply (rule corres_return_eq_same)
      apply (clarsimp simp: refill_map_def minBudget_def MIN_BUDGET_def kernelWCETTicks_def)
     apply wpsimp+
   apply (fastforce elim!: sc_at_pred_n_sc_at)
  apply clarsimp
  done

lemma headInsufficientLoop_corres:
  "sc_ptr = scPtr \<Longrightarrow>
   corres dc
     (pspace_aligned and pspace_distinct and sc_at sc_ptr and is_active_sc sc_ptr
      and valid_objs
      and (\<lambda>s. pred_map (\<lambda>cfg. unat MIN_BUDGET \<le> refills_unat_sum (scrc_refills cfg))
                        (sc_refill_cfgs_of s) sc_ptr)
      and (\<lambda>s. pred_map (\<lambda>cfg. refills_unat_sum (scrc_refills cfg) \<le> unat max_time)
                        (sc_refill_cfgs_of s) sc_ptr)
      and (\<lambda>s. sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr s))
     (valid_objs' and valid_refills' sc_ptr)
     (head_insufficient_loop sc_ptr) (headInsufficientLoop scPtr)"
  apply (clarsimp simp: head_insufficient_loop_def headInsufficientLoop_def runReaderT_def)
  apply (rule_tac Q'="active_sc_at' scPtr" in corres_cross_add_guard)
   apply (fastforce dest: active_sc_at'_cross)
  apply (rule corres_whileLoop_abs; simp?)
      apply (rule_tac f="refill_head_insufficient scPtr"
                  and f'="refillHdInsufficient scPtr"
                   in gets_the_corres_relation[rotated])
          apply (corres corres: gets_the_refillHdInsufficient_corres)
         apply fastforce
        apply fastforce
       apply fastforce
      apply (wpsimp wp: no_ofail_head_insufficient)
     apply (corres corres: mergeNonoverlappingHeadRefill_corres)
      apply (fastforce dest!: no_ofailD[OF no_ofail_head_insufficient]
                              head_insufficient_length
                        simp: vs_all_heap_simps sc_at_ppred_def obj_at_def)
     apply fastforce
    apply (wpsimp wp: merge_nonoverlapping_head_refill_refills_unat_sum_lower_bound
                      merge_nonoverlapping_head_refill_refills_unat_sum
                      merge_nonoverlapping_head_refill_nonempty_refills)
    apply (fastforce dest!: no_ofailD[OF no_ofail_head_insufficient] head_insufficient_length
                      simp: vs_all_heap_simps sc_at_ppred_def obj_at_def)
   apply (wpsimp | strengthen valid_objs'_valid_refills' active_sc_at'_imp_is_active_sc')+
   apply (clarsimp simp: active_sc_at'_rewrite)
  apply (fastforce intro!: non_overlapping_merge_refills_terminates)
  done

lemma getRefillFull_corres:
  "sc_ptr = scPtr \<Longrightarrow>
   corres (=) (sc_at sc_ptr and pspace_aligned and pspace_distinct) (valid_refills' scPtr)
     (refill_full sc_ptr) (getRefillFull scPtr)"
  apply (rule_tac Q'="sc_at' scPtr" in corres_cross_add_guard)
   apply (fastforce intro: sc_at_cross)
  apply (clarsimp simp: refill_full_def getRefillFull_def readRefillFull_def
                        readSchedContext_def getObject_def[symmetric] getSchedContext_def[symmetric]
                        getRefillSize_def[symmetric])
  apply (rule corres_underlying_split[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corres corres: get_sc_corres)
  apply (rule corres_symb_exec_r[OF _ getRefillSize_sp, rotated])
    apply (wpsimp wp: getRefillSize_wp)
   apply wpsimp
  apply (fastforce simp: sc_relation_def obj_at_simps valid_refills'_def in_omonad)
  done

lemma getRefillFull_sp:
  "\<lbrace>P\<rbrace>
   getRefillFull scPtr
   \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. ko_at' sc scPtr s \<and> rv = (scRefillMax sc = refillSize sc))\<rbrace>"
  apply (wpsimp wp: getRefillFull_wp)
  apply (fastforce simp: obj_at'_def refillSize_def)
  done

(* FIXME RT: move to AInvs *)
lemma get_refill_tail_sp:
  "\<lbrace>P\<rbrace>
   get_refill_tail sc_ptr
   \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc n. ko_at (Structures_A.SchedContext sc n) sc_ptr s \<and> rv = refill_tl sc)\<rbrace>"
  apply (wpsimp wp: get_refill_tail_wp)
  apply (clarsimp simp: obj_at_def)
  done

lemma getRefillTail_corres:
  "sc_ptr = scPtr \<Longrightarrow>
   corres (\<lambda>rv rv'. refill_map rv' = rv)
     (valid_objs and pspace_aligned and pspace_distinct
      and is_active_sc sc_ptr and sc_at sc_ptr and sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr)
     valid_objs'
     (get_refill_tail sc_ptr) (getRefillTail scPtr)"
  apply (add_active_sc_at' scPtr)
  apply (clarsimp simp: get_refill_tail_def getRefillTail_def read_refill_tail_def
                        readRefillTail_def read_sched_context_get_sched_context readSchedContext_def
                        ohaskell_state_assert_def gets_the_ostate_assert
             simp flip: getSchedContext_def getObject_def)
  apply (rule corres_stateAssert_ignore[simplified HaskellLib_H.stateAssert_def], simp)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF get_sc_corres])
      apply (rule corres_assert_assume_l)
      apply clarsimp
      apply (rule refills_tl_equal[symmetric])
       apply simp+
     apply wpsimp+
   apply (clarsimp simp: sc_at_ppred_def obj_at_def is_sc_obj_def)
  apply clarsimp
  apply (frule (4) active_sc_at'_cross_valid_objs)
  by (fastforce dest: valid_objs'_valid_refills'
                simp: active_sc_at'_def obj_at'_def is_active_sc'_def in_omonad valid_refills'_def)

lemma scheduleUsed_corres:
  "\<lbrakk>sc_ptr = scPtr; new = refill_map new'\<rbrakk> \<Longrightarrow>
    corres dc
      (sc_at sc_ptr and is_active_sc2 sc_ptr
       and (\<lambda>s. sc_refills_sc_at (\<lambda>refills. 0 < length refills) sc_ptr s)
       and pspace_aligned and pspace_distinct and valid_objs)
      valid_objs'
      (schedule_used sc_ptr new) (scheduleUsed scPtr new')"
  apply (clarsimp simp: schedule_used_def scheduleUsed_def get_refills_def bind_assoc)
  apply (rule_tac Q'="sc_at' scPtr" in corres_cross_add_guard)
   apply (fastforce intro: sc_at_cross)
  apply (rule_tac Q'="is_active_sc' scPtr" in corres_cross_add_guard)
   apply (fastforce intro: is_active_sc'_cross)
  apply (rule corres_symb_exec_r[OF _ scActive_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[rotated, OF assert_sp]; (solves wpsimp)?)
   apply wpsimp
   apply (clarsimp simp: is_active_sc'_def in_omonad obj_at_simps)
  apply (rule corres_symb_exec_l[OF _ _ get_sched_context_sp, rotated])
    apply (wpsimp wp: get_sched_context_exs_valid)
     apply (clarsimp simp: sc_at_ppred_def obj_at_def)
    apply clarsimp
   apply wpsimp
   apply (clarsimp simp: sc_at_ppred_def obj_at_def)
  apply (rule corres_symb_exec_l[rotated, OF _ assert_sp])
    apply wpsimp
    apply (fastforce simp: sc_at_pred_n_def obj_at_def)
   apply wpsimp
   apply (fastforce simp: sc_at_pred_n_def obj_at_def)
  apply (rule corres_underlying_split[rotated 2, OF get_refill_tail_sp getRefillTail_sp])
   apply (corres corres: getRefillTail_corres simp: is_active_sc_rewrite)
  apply (rename_tac tail tail')
  apply (rule corres_if_split; (solves simp)?)
    apply (fastforce simp: can_merge_refill_def refill_map_def
                     dest: refill_hd_relation refills_tl_equal)
   apply (corres corres: updateRefillTl_corres simp: refill_map_def)
   apply (fastforce intro!: valid_objs'_valid_refills')
  apply (rule corres_underlying_split[rotated 2, OF refill_full_sp getRefillFull_sp])
   apply (corres corres: getRefillFull_corres)
   apply (fastforce intro!: valid_objs'_valid_refills')
  apply (rule corres_if_split; (solves simp)?)
   apply (corres corres: refillAddTail_corres)
    apply (fastforce simp: is_active_sc_rewrite)
   apply (fastforce dest!: valid_objs'_valid_refills'
                     simp: obj_at_simps opt_map_red opt_pred_def valid_refills'_def)
  apply (corres corres: updateRefillTl_corres simp: refill_map_def)
  apply (fastforce intro!: valid_objs'_valid_refills')
  done

lemma readRefillSingle_sp:
  "\<lblot>Q\<rblot>
   readRefillSingle scp
   \<lblot>\<lambda>rv s. Q s \<and> (\<exists>sc. ko_at' sc scp s \<and> (rv = (scRefillHead sc = scRefillTail sc)))\<rblot>"
  apply wpsimp
  by (simp add: obj_at'_def)

lemmas readRefillSingle_SomeD = use_ovalid[OF readRefillSingle_sp, where P=\<top>, simplified]

lemma refillSingle_sp:
  "\<lbrace>P\<rbrace>
   refillSingle scp
   \<lbrace>\<lambda>rv s. P s \<and> (\<forall>ko. ko_at' ko scp s \<longrightarrow> rv = (scRefillHead ko = scRefillTail ko))\<rbrace>"
  unfolding refillSingle_def
  apply wpsimp
  apply (fastforce dest: readRefillSingle_SomeD simp: obj_at'_def)
  done

lemma chargeEntireHeadRefill_corres:
  "\<lbrakk>sc_ptr = scPtr; r = r'\<rbrakk> \<Longrightarrow>
   corres (=)
     (sc_at sc_ptr and is_active_sc2 sc_ptr
      and pspace_aligned and pspace_distinct and valid_objs
      and sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr)
     valid_objs'
     (charge_entire_head_refill sc_ptr r) (chargeEntireHeadRefill scPtr r')"
  apply (rule_tac Q'="\<lambda>s'. sc_at' scPtr s'" in corres_cross_add_guard)
   apply (rule sc_at_cross, fastforce+)
  apply (rule_tac Q'="\<lambda>s'. is_active_sc' scPtr s'" in corres_cross_add_guard)
   apply (fastforce intro: is_active_sc'_cross simp: state_relation_def)
  apply (clarsimp simp: charge_entire_head_refill_def chargeEntireHeadRefill_def)
  apply (rule corres_underlying_split[rotated 2, OF get_refill_head_sp getRefillHead_sp])
   apply (corres corres: getRefillHead_corres simp: is_active_sc_rewrite)
  apply (rule corres_underlying_split[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corres corres: get_sc_corres)
  apply (rename_tac sc')
  apply (rule corres_underlying_split[rotated 2, OF refill_single_sp refillSingle_sp])
   apply (corresKsimp corres: refillSingle_corres)
   apply (fastforce dest!: valid_objs'_valid_refills'
                     simp: obj_at_simps valid_refills'_def opt_map_red opt_pred_def)
  apply (rule corres_underlying_split[rotated, where r'=dc])
     apply (rule corres_return_eq_same)
     apply (clarsimp simp: refill_map_def)
    apply wpsimp
   apply wpsimp
  apply (rule corres_if_split; simp?)
   apply (corres corres: updateRefillHd_corres)
   apply (fastforce simp: refill_map_def sc_relation_def)
  apply fastforce
   apply (fastforce dest!: valid_objs'_valid_refills'
                     simp: obj_at_simps valid_refills'_def opt_map_red opt_pred_def)
  apply (rule_tac F="1 < refillSize sc'" in corres_req)
   apply (frule_tac scp="scPtr" and P="\<lambda>l. 1 < l" in length_sc_refills_cross)
      apply (clarsimp simp: state_relation_def)
     apply simp
    apply (fastforce dest!: valid_objs'_valid_refills')
   apply (clarsimp simp: opt_map_red opt_pred_def obj_at'_def Suc_lessI obj_at_def sc_at_ppred_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF refillPopHead_corres], simp)
      apply (rule scheduleUsed_corres)
       apply simp
      apply (clarsimp simp: refill_map_def sc_relation_def)
     apply (wpsimp wp: refill_pop_head_nonempty_refills)
    apply wpsimp
   apply (clarsimp simp: is_active_sc2_def sc_at_ppred_def obj_at_def active_sc_def
                         vs_all_heap_simps Suc_lessI in_omonad)
  apply (fastforce dest!: valid_objs'_valid_refills')
  done

lemma updateRefillIndex_is_active_sc'[wp]:
  "updateRefillIndex scPtr f index \<lbrace>is_active_sc' scPtr'\<rbrace>"
  unfolding updateRefillIndex_def
  apply (wpsimp wp: updateSchedContext_wp)
  apply (clarsimp simp: is_active_sc'_def in_omonad opt_map_def)
  done

lemma scheduleUsed_is_active_sc'[wp]:
  "scheduleUsed scPtr new \<lbrace>is_active_sc' scPtr'\<rbrace>"
  apply (clarsimp simp: scheduleUsed_def)
  apply (wpsimp simp: refillAddTail_def updateRefillTl_def
                  wp: updateSchedContext_wp getRefillFull_wp getRefillNext_wp getRefillSize_wp)
  apply (clarsimp simp: obj_at_simps is_active_sc'_def opt_map_def opt_pred_def)
  done

lemma chargeEntireHeadRefill_is_active_sc'[wp]:
  "chargeEntireHeadRefill scPtr usage \<lbrace>is_active_sc' sc_ptr\<rbrace>"
  apply (clarsimp simp: chargeEntireHeadRefill_def)
  apply (wpsimp simp: updateRefillHd_def refillSingle_def
                  wp: updateSchedContext_wp)
  apply (clarsimp simp: obj_at_simps is_active_sc'_def opt_map_def opt_pred_def)
  done

lemma refillAddTail_valid_refills'[wp]:
  "refillAddTail scPtr refill \<lbrace>valid_refills' ptr\<rbrace>"
  apply (clarsimp simp: refillAddTail_def updateRefillIndex_def)
  apply (wpsimp wp: updateSchedContext_wp getRefillNext_wp getRefillSize_wp)
  apply (fastforce simp: valid_refills'_def obj_at_simps opt_map_red opt_pred_def refillNext_def
                         refillSize_def)
  done

lemma scheduleUsed_valid_refills'[wp]:
  "scheduleUsed ptr new \<lbrace>valid_refills' scPtr\<rbrace>"
  apply (clarsimp simp: scheduleUsed_def)
  apply (wpsimp wp: getRefillFull_wp)
  done

crunch charge_entire_head_refill
  for valid_objs[wp]: valid_objs

crunch chargeEntireHeadRefill
  for valid_objs'[wp]: valid_objs'
  (wp: crunch_wps simp: refillSingle_def)

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

lemma charge_entire_head_refill_terminates:
  "\<lbrakk>sc_at sc_ptr s;
    pred_map (\<lambda>cfg. \<forall>refill \<in> set (scrc_refills cfg). 0 < unat (r_amount refill))
             (sc_refill_cfgs_of s) sc_ptr;
    sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr s;
    pred_map (\<lambda>cfg. refills_unat_sum (scrc_refills cfg) = unat (scrc_budget cfg))
             (sc_refill_cfgs_of s) sc_ptr\<rbrakk>
   \<Longrightarrow> whileLoop_terminates (\<lambda>r s. the (head_refill_overrun sc_ptr r s))
                            (charge_entire_head_refill sc_ptr) usage s"
  (is "\<lbrakk>?P1 s; ?P2 s; ?P3 s; ?P4 s\<rbrakk> \<Longrightarrow> _")
  apply (rule_tac R="{((r' :: ticks, s' :: 'a state), (r, s)). unat r' < unat r}"
              and I="\<lambda>_. ?P1 and ?P2 and ?P3 and ?P4"
               in whileLoop_terminates_inv)
    apply simp
   prefer 2
   apply (prop_tac "{((r', s'), r, s). unat r' < unat r} = measure (\<lambda>(r, s). unat r)")
    apply (clarsimp simp: measure_def inv_image_def split_def)
   apply (fastforce dest: sym elim: subst)
  apply (rename_tac r s')
  apply (wps_conj_solves wp: charge_entire_head_refill_non_zero_refills
                             charge_entire_head_refill_refills_unat_sum_equals_budget)
  apply (wpsimp simp: charge_entire_head_refill_def)
  apply (rename_tac sc n)
  apply (frule_tac usage=r and s=s' in head_refill_overrun_true_imp_buffer)
  apply (clarsimp simp: vs_all_heap_simps)
  apply (subst unat_sub)
   apply clarsimp
  apply (drule_tac x="refill_hd sc" in bspec)
   apply (fastforce simp: obj_at_def sc_at_ppred_def)
  apply (fastforce simp: word_le_nat_alt)
  done

lemma gets_the_headRefillOverrun_corres:
  "\<lbrakk>sc_ptr = scPtr; usage = usage'\<rbrakk> \<Longrightarrow>
   corres (=)
     (valid_objs and pspace_aligned and pspace_distinct
      and is_active_sc sc_ptr and sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr)
     valid_objs'
     (gets_the (head_refill_overrun sc_ptr usage)) (gets_the (headRefillOverrun scPtr usage'))"
  apply (simp add: head_refill_overrun_def headRefillOverrun_def
             flip: get_refill_head_def getRefillHead_def)
  apply (corres corres: getRefillHead_corres)
      apply (rule corres_return_eq_same)
      apply (clarsimp simp: refill_map_def maxReleaseTime_equiv)
     apply wpsimp+
   apply (fastforce elim!: sc_at_pred_n_sc_at)
  apply clarsimp
  done

lemma handleOverrun_corres:
  "\<lbrakk>sc_ptr = scPtr; usage = usage'\<rbrakk> \<Longrightarrow>
   corres (=)
     (sc_at sc_ptr and is_active_sc2 sc_ptr
      and pspace_aligned and pspace_distinct
      and valid_objs
      and sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr
      and (\<lambda>s. pred_map (\<lambda>cfg. \<forall>refill\<in>set (scrc_refills cfg). 0 < unat (r_amount refill))
                        (sc_refill_cfgs_of s) sc_ptr)
      and (\<lambda>s. pred_map (\<lambda>cfg. refills_unat_sum (scrc_refills cfg) = unat (scrc_budget cfg))
                        (sc_refill_cfgs_of s) sc_ptr))
     valid_objs'
     (handle_overrun sc_ptr usage) (handleOverrun scPtr usage')"
  apply (rule_tac Q'="\<lambda>s'. sc_at' scPtr s'" in corres_cross_add_guard)
   apply (rule sc_at_cross, fastforce+)
  apply (rule_tac Q'="\<lambda>s'. is_active_sc' scPtr s'" in corres_cross_add_guard)
   apply (fastforce intro: is_active_sc'_cross simp: state_relation_def)
  apply (clarsimp simp: handle_overrun_def handleOverrun_def runReaderT_def)
  apply (rule corres_whileLoop_abs; simp?)
      apply (rule_tac f="head_refill_overrun scPtr r'"
                  and f'="headRefillOverrun scPtr r'" and sr=state_relation
                   in gets_the_corres_relation[rotated])
          apply (corres corres: gets_the_headRefillOverrun_corres)
         apply (fastforce simp: is_active_sc_rewrite)
        apply fastforce
       apply fastforce
      apply (wpsimp wp: no_ofail_head_refill_overrun)
     apply (corres corres: chargeEntireHeadRefill_corres)
    apply (wpsimp wp: charge_entire_head_refill_non_zero_refills
                      charge_entire_head_refill_refills_unat_sum_equals_budget)
   apply wpsimp
  apply (fastforce intro: charge_entire_head_refill_terminates)
  done

lemma get_refills_exs_valid[wp]:
  "sc_at sc_ptr s \<Longrightarrow> \<lbrace>(=) s\<rbrace> get_refills sc_ptr \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  apply (clarsimp simp: get_refills_def)
  apply (wpsimp wp: get_sched_context_exs_valid)
   apply (erule sc_atD1)
  apply simp
  done

lemma update_refill_hd_nonempty_refills[wp]:
  "update_refill_hd sc_ptr f \<lbrace>\<lambda>s. sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr' s\<rbrace>"
  unfolding update_refill_hd_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
  done

lemma refillBudgetCheck_corres:
  "usage = usage' \<Longrightarrow>
   corres dc
     ((\<lambda>s. sc_at (cur_sc s) s \<and> is_active_sc (cur_sc s) s
           \<and> valid_objs s
           \<and> pspace_aligned s \<and> pspace_distinct s)
      and (\<lambda>s. \<not> round_robin (cur_sc s) s \<and> valid_refills (cur_sc s) s))
     valid_objs'
     (refill_budget_check usage) (refillBudgetCheck usage')"
  (is "_ \<Longrightarrow> corres _ (?P and _) _ _ _")
  apply (rule_tac Q'="\<lambda>s'. sc_at' (ksCurSc s') s'" in corres_cross_add_guard)
   apply (rule sc_at_cross, (fastforce simp: state_relation_def)+)
  apply (rule_tac Q'="\<lambda>s'. is_active_sc' (ksCurSc s') s'" in corres_cross_add_guard)
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
                                \<and> cur_sc s = sc_ptr
                                \<and> (pred_map (\<lambda>cfg. r_time (hd (scrc_refills cfg)) < MAX_RELEASE_TIME)
                                             (sc_refill_cfgs_of s) sc_ptr
                                   \<longrightarrow> pred_map (\<lambda>cfg. usage' < r_amount (hd (scrc_refills cfg)))
                                                (sc_refill_cfgs_of s) sc_ptr)
                                \<and> sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr s"
               and Q'="\<lambda>_ s'. valid_objs' s' \<and> active_sc_at' scPtr s'
                              \<and> scPtr = ksCurSc s'"
               in corres_underlying_split)
     apply (corres corres: handleOverrun_corres)
      apply (fastforce intro: valid_refills_refills_unat_sum_equals_budget
                        simp: vs_all_heap_simps cfg_valid_refills_def round_robin_def
                              sp_valid_refills_def is_active_sc_rewrite[symmetric]
                              sc_at_ppred_def obj_at_def)
     apply fastforce
    apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> handle_overrun _ usage' \<lbrace>Q\<rbrace>" for P Q \<Rightarrow> -\<close>)
    apply (clarsimp simp: pred_conj_def)
    apply (intro hoare_vcg_conj_lift_pre_fix; (solves handle_overrun_simple)?)
       apply wps_conj_solves
      apply (wpsimp wp: handle_overrun_refills_unat_sum_equals_budget)
      apply (fastforce intro: valid_refills_refills_unat_sum_equals_budget
                        simp: vs_all_heap_simps cfg_valid_refills_def round_robin_def
                              sp_valid_refills_def sc_at_ppred_def obj_at_def)
     apply (clarsimp simp: handle_overrun_def)
     apply (rule hoare_weaken_pre)
      apply (rule_tac I="\<lambda>_ s. sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) scPtr s"
                   in valid_whileLoop)
        apply assumption
       apply (wpsimp wp: charge_entire_head_refill_nonzero_refills)
      apply (frule_tac usage=r and sc_ptr=scPtr in head_refill_overrun_true_imp_unat_buffer)
      apply (fastforce simp: head_refill_overrun_true_imp_unat_buffer vs_all_heap_simps
                             word_less_nat_alt word_le_nat_alt)
     apply (fastforce simp: vs_all_heap_simps valid_refills_def round_robin_def
                            sc_at_ppred_def obj_at_def)
    apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> handleOverrun _ usage' \<lbrace>Q\<rbrace>" for P Q \<Rightarrow> -\<close>)
    apply (wpsimp wp: handleOverrun_valid_objs')
    apply (clarsimp simp: active_sc_at'_def obj_at_simps)
   apply (wpsimp wp: handle_overrun_nonzero_refills)
    apply (fastforce simp: vs_all_heap_simps valid_refills_def round_robin_def
                           sc_at_ppred_def obj_at_def)

  apply (rule corres_underlying_split[rotated 2, OF get_refill_head_sp getRefillHead_sp])
   apply (corresKsimp corres: getRefillHead_corres
                        simp: state_relation_def active_sc_at'_def)
  apply (rename_tac head head')
  apply (rule_tac Q="\<lambda>_ s. ?P s
                           \<and> pred_map (\<lambda>cfg. refills_unat_sum (scrc_refills cfg)
                                              = unat (scrc_budget cfg))
                                       (sc_refill_cfgs_of s) scPtr
                           \<and> pred_map (\<lambda>cfg. MIN_BUDGET \<le> scrc_budget cfg)
                                       (sc_refill_cfgs_of s) scPtr
                           \<and> scPtr = cur_sc s"
              and Q'="\<lambda>_ s'. valid_objs' s' \<and> active_sc_at' scPtr s' \<and> scPtr = ksCurSc s'"
              and r'=dc
               in corres_underlying_split[rotated])
     apply (corresKsimp corres: headInsufficientLoop_corres)
     using MIN_BUDGET_pos
     apply (fastforce intro!: valid_objs'_valid_refills'
                        simp: vs_all_heap_simps word_le_nat_alt sc_at_pred_n_def obj_at_def
                              refills_unat_sum_def unat_eq_0 active_sc_at'_def obj_at'_def
                              is_active_sc'_def in_omonad)
    apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
       apply ((wpsimp | wps)+)[1]
      apply ((wpsimp | wps)+)[1]
     apply (wpsimp wp: schedule_used_refills_unat_sum update_sched_context_wp
                 simp: update_refill_hd_def)
     apply (clarsimp simp: obj_at_def vs_all_heap_simps refills_unat_sum_cons
                           refills_unat_sum_append sc_at_ppred_def)
     apply (subst unat_sub)
      apply fastforce
     apply (clarsimp simp: word_less_nat_alt)
     apply (drule less_imp_le)
     apply (clarsimp simp: refills_unat_sum_def)
     apply (case_tac "sc_refills sc"; clarsimp simp: refills_unat_sum_cons)
    apply schedule_used_simple
   apply (wpsimp wp: updateRefillHd_valid_objs')
  apply (clarsimp simp: maxReleaseTime_equiv)
  apply (simp add: when_def split del: if_split)
  apply (rule corres_if_split; (solves simp)?)
   apply (clarsimp simp: refill_map_def)
  apply (rule corres_underlying_split[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corres corres: get_sc_corres)
   apply (clarsimp simp: active_sc_at'_def)
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
      apply (wpsimp wp: updateRefillHd_valid_objs')
     apply wpsimp
    apply (wpsimp wp: updateRefillHd_valid_objs')
   apply (clarsimp simp: vs_all_heap_simps is_active_sc2_def in_omonad active_sc_def)
  apply (fastforce dest: valid_objs'_valid_refills' simp: active_sc_at'_rewrite)
  done

(* schedule_corres *)

crunch setReprogramTimer
  for valid_tcbs'[wp]: valid_tcbs'
  and valid_refills'[wp]: "valid_refills' scPtr"
  (simp: valid_refills'_def)

lemma in_correct_ready_q_reprogram_timer_update[simp]:
  "in_correct_ready_q (reprogram_timer_update f s) = in_correct_ready_q s"
  by (clarsimp simp: in_correct_ready_q_def)

lemma ready_qs_distinct_reprogram_timer_update[simp]:
  "ready_qs_distinct (reprogram_timer_update f s) = ready_qs_distinct s"
  by (clarsimp simp: ready_qs_distinct_def)

lemma checkDomainTime_corres:
  "corres dc
     (valid_tcbs and weak_valid_sched_action and active_scs_valid
      and valid_ready_qs and ready_or_release and pspace_aligned and pspace_distinct
      and in_correct_ready_q and ready_qs_distinct)
     (valid_tcbs' and sym_heap_sched_pointers and valid_sched_pointers
      and pspace_aligned' and pspace_distinct' and pspace_bounded')
     check_domain_time checkDomainTime"
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
             (\<lambda>s'. valid_objs' s'
                   \<and> (is_active_sc' (ksCurSc s') s' \<longrightarrow> valid_refills' (ksCurSc s') s'))
             commit_time
             commitTime"
  supply if_split[split del]
  apply (rule_tac Q'="\<lambda>s'. sc_at' (ksCurSc s') s'" in corres_cross_add_guard)
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
  apply (fastforce simp: vs_all_heap_simps is_sc_obj_def obj_at_simps sc_relation_def
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
     apply (rule_tac Q'="\<lambda>_.invs" in hoare_post_imp, fastforce)
     apply wpsimp+
    apply (rule_tac Q'="\<lambda>_. invs'" in hoare_post_imp, fastforce)
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

lemma threadSet_isSchedulable_bool_fields_inv:
  "\<lbrakk>\<And>tcb. tcbState (f tcb) = tcbState tcb; \<And>tcb. tcbSchedContext (f tcb) = tcbSchedContext tcb;
    \<And>tcb. tcbInReleaseQueue (f tcb) = tcbInReleaseQueue tcb\<rbrakk>
   \<Longrightarrow> threadSet f tcbPtr \<lbrace>\<lambda>s. P (isSchedulable_bool tcbPtr' s)\<rbrace>"
  unfolding isSchedulable_bool_def threadSet_def
  apply (wpsimp wp: setObject_tcb_wp getTCB_wp)
  apply (erule rsubst[where P=P])
  apply (wpsimp wp: setObject_tcb_wp simp: pred_map_def obj_at'_def opt_map_def)
  apply (fastforce simp: pred_map_def isScActive_def elim!: opt_mapE split: if_splits)
  done

lemma tcbQueued_update_isSchedulable_bool[wp]:
  "threadSet (tcbQueued_update f) tcbPtr \<lbrace>isSchedulable_bool tcbPtr'\<rbrace>"
  by (fastforce intro: threadSet_isSchedulable_bool_fields_inv)

lemma tcbSchedPrev_update_isSchedulable_bool[wp]:
  "threadSet (tcbSchedPrev_update f) tcbPtr \<lbrace>isSchedulable_bool tcbPtr'\<rbrace>"
  by (fastforce intro: threadSet_isSchedulable_bool_fields_inv)

lemma tcbSchedNext_update_isSchedulable_bool[wp]:
  "threadSet (tcbSchedNext_update f) tcbPtr \<lbrace>isSchedulable_bool tcbPtr'\<rbrace>"
  by (fastforce intro: threadSet_isSchedulable_bool_fields_inv)

lemma tcbSchedEnqueue_isSchedulable_bool[wp]:
  "tcbSchedEnqueue tcbPtr \<lbrace>isSchedulable_bool tcbPtr'\<rbrace>"
  supply if_split[split del]
  apply (clarsimp simp: tcbSchedEnqueue_def tcbQueuePrepend_def unless_def)
  apply (wpsimp wp: threadSet_isSchedulable_bool hoare_vcg_if_lift2 hoare_drop_imps)
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

(* FIXME RT: move to Corres_UL.thy *)
lemma corres_underlying_return_stateAssert:
  assumes "\<And>s s'. \<lbrakk> (s,s') \<in> rf_sr; P s; P' s'\<rbrakk> \<Longrightarrow> Q' s'"
  shows "corres_underlying rf_sr nf nf' dc P P' (return ()) (stateAssert Q' [])"
  by (auto simp: stateAssert_def get_def Nondet_Monad.bind_def corres_underlying_def
                 assert_def return_def fail_def assms)

lemma schedule_corres:
  "corres dc (invs and valid_sched and current_time_bounded and ct_ready_if_schedulable
              and (\<lambda>s. schact_is_rct s \<longrightarrow> cur_sc_active s))
             invs'
             (Schedule_A.schedule)
             schedule"
  supply bind_return[simp del]
  apply (rule corres_bind_return)
  apply (clarsimp simp: schedule_def)
  apply (subst bind_assoc[symmetric])+
  apply (rule_tac r'=dc and Q'="\<top>\<top>" and Q="\<lambda>_. invs and ct_in_state activatable"
               in corres_underlying_split)
     defer
     apply clarsimp
     apply (rule corres_underlying_return_stateAssert)
     apply (fastforce intro!: st_tcb_at_activatable_cross
                        simp: ct_activatable'_asrt_def ct_in_state_def ct_in_state'_def
                              state_relation_def)
    apply (wpsimp wp: schedule_invs' schedule_ct_activateable)
   apply wpsimp
  apply (subst bind_assoc)+
  apply add_cur_tcb'
  apply (clarsimp simp: Schedule_A.schedule_def schedule_def sch_act_wf_asrt_def cur_tcb'_asrt_def)
  apply (rule corres_stateAssert_ignore, simp)+
   apply (fastforce elim!: sch_act_wf_cross)
  apply (rule corres_stateAssert_add_assertion[rotated], simp)+
  apply (rule corres_split_skip)
     apply (wpsimp wp: awaken_valid_sched hoare_vcg_imp_lift')
     apply fastforce
    apply (wpsimp wp: awaken_invs')
   apply (corresKsimp corres: awaken_corres)
   apply (fastforce dest: valid_sched_valid_ready_qs simp: invs_def valid_state_def)
  apply (rule corres_split_skip)
     apply (wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)
    apply wpsimp
   apply (corresKsimp corres: checkDomainTime_corres)
   apply (fastforce dest: valid_sched_valid_ready_qs simp: invs_def valid_state_def)
  apply (rule corres_underlying_split[rotated 2, OF gets_sp getCurThread_sp])
   apply corresKsimp
  apply clarsimp
  apply (rename_tac curThread)
  apply (rule corres_underlying_split[rotated 2, OF is_schedulable_sp' isSchedulable_sp])
   apply (corresKsimp corres: isSchedulable_corres)
   apply (fastforce simp: invs_def valid_state_def state_relation_def cur_tcb_def)
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
        apply (rule tcbSchedEnqueue_corres, simp)
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
   apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> curThread = ksCurThread s"
                in bind_wp_fwd)
    apply wpsimp
    apply (clarsimp simp: invs'_def isSchedulable_bool_def st_tcb_at'_def pred_map_simps
                          obj_at_simps cur_tcb'_def sch_act_wf_cases
                   split: scheduler_action.splits
                   elim!: opt_mapE)
   apply (rule bind_wp_fwd_skip, solves wpsimp)+
   apply (rule_tac Q'="\<lambda>_. invs'" in hoare_post_imp)
    apply (clarsimp simp: invs'_def)
   apply (wpsimp wp: scheduleChooseNewThread_invs' ksReadyQueuesL1Bitmap_return_wp
               simp: isHighestPrio_def scheduleSwitchThreadFastfail_def)
   apply (clarsimp simp: invs'_def)

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
   apply (intro conjI impI allI; fastforce?)
       apply (clarsimp simp: valid_sched_def)
      apply (clarsimp simp: valid_sched_def)
     apply (clarsimp simp: cur_tcb_def schedulable_def2 not_in_release_q_def)
    apply (clarsimp simp: cur_tcb_def schedulable_def2 not_in_release_q_def)
   apply (fastforce intro!: valid_sched_ready_or_release)
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
              and Q'="\<lambda>_ s. invs' s \<and> cur_tcb' s \<and> curThread = ksCurThread s"
              and r'="(=)"
               in corres_underlying_split)
     apply clarsimp
     apply (rule corres_guard_imp)
       apply (rule threadGet_corres)
       apply (clarsimp simp: tcb_relation_def)
      apply clarsimp
      apply (fastforce simp: cur_tcb'_def)
     apply simp

    apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q  \<Rightarrow> -\<close>)
    apply (wpsimp wp: thread_get_wp)
    apply (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                          in_queue_2_def)

   apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q  \<Rightarrow> -\<close>)
   apply (wpsimp wp: threadGet_wp)

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
     apply (fastforce dest: invs_valid_bitmaps simp: valid_bitmaps_def)
    apply (fastforce dest: invs_valid_bitmaps simp: valid_bitmaps_def)
   apply (rule disj_cong)
    apply (frule state_relation_ready_queues_relation)
    apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def
                          list_queue_relation_def tcbQueueEmpty_def)
    apply (drule_tac x="ksCurDomain s'" in spec)
    apply fastforce
   apply clarsimp
   apply (subst lookupBitmapPriority_Max_eqI)
      apply (fastforce dest: invs_valid_bitmaps simp: valid_bitmaps_def)
     apply (fastforce dest: invs_valid_bitmaps simp: valid_bitmaps_def)
    apply (subst bitmapL1_zero_ksReadyQueues)
      apply (fastforce dest: invs_valid_bitmaps simp: valid_bitmaps_def)
     apply (fastforce dest: invs_valid_bitmaps simp: valid_bitmaps_def)
    apply (fastforce simp: ready_queues_relation_def dest!: state_relationD)
   apply (subst Max_prio_helper)
    apply fastforce
   apply fastforce

  apply (rule corres_if_split; (solves simp)?)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF tcbSchedEnqueue_corres], simp)
       apply clarsimp
       apply (rule corres_split[OF setSchedulerAction_corres])
          apply (clarsimp simp: sched_act_relation_def)
         apply (rule scheduleChooseNewThread_corres)
        apply wpsimp+
    apply (fastforce simp: obj_at_def vs_all_heap_simps is_tcb_def pred_tcb_at_def)
   apply fastforce

  apply (rule corres_if_split; (solves simp)?)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF tcbSchedAppend_corres], simp)
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

crunch removeFromBitmap
  for valid_tcbs'[wp]: valid_tcbs'

lemma tcbSchedDequeue_valid_tcbs'[wp]:
  "tcbSchedDequeue t \<lbrace>valid_tcbs'\<rbrace>"
  unfolding tcbSchedDequeue_def setQueue_def
  by (wpsimp wp: threadSet_valid_tcbs' threadGet_wp hoare_vcg_if_lift2)

crunch schedContextDonate
  for ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' ptr"
  (wp: threadSet_cap_to crunch_wps simp: tcb_cte_cases_def cteSizeBits_def)

crunch schedContextDonate
  for valid_irq_handlers'[wp]: "\<lambda>s. valid_irq_handlers' s"
  and valid_mdb'[wp]: valid_mdb'
  (ignore: threadSet
     simp: comp_def valid_mdb'_def crunch_simps
       wp: valid_irq_handlers_lift'' threadSet_ctes_of)

crunch schedContextDonate
  for sch_act_sane[wp]: sch_act_sane
  and sch_act_not[wp]: "sch_act_not t"
  (wp: crunch_wps simp: crunch_simps rule: sch_act_sane_lift)

lemma schedContextDonate_utr[wp]:
  "schedContextDonate scPtr tcbPtr \<lbrace>untyped_ranges_zero'\<rbrace>"
  by (wpsimp simp: cteCaps_of_def o_def wp: untyped_ranges_zero_lift)

crunch schedContextDonate
  for no_0_obj'[wp]: no_0_obj'
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and if_unsafe_then_cap'[wp]: "if_unsafe_then_cap'"
  and valid_global_refs'[wp]: "valid_global_refs'"
  and valid_arch_state'[wp]: "valid_arch_state'"
  and valid_irq_node'[wp]: "\<lambda>s. valid_irq_node' (irq_node' s) s"
  and valid_irq_states'[wp]: "\<lambda>s. valid_irq_states' s"
  and valid_machine_state'[wp]: "\<lambda>s. valid_machine_state' s"
  and pspace_domain_valid[wp]: "\<lambda>s. pspace_domain_valid s"
  and cur_tcb'[wp]: "cur_tcb'"
  and valid_dom_schedule'[wp]: valid_dom_schedule'
  and reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and valid_replies' [wp]: valid_replies'
  and pspace_bounded'[wp]: "pspace_bounded'"
  and pspace_canonical'[wp]: pspace_canonical'
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  and irqs_masked'[wp]: irqs_masked'
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  (simp: comp_def tcb_cte_cases_def crunch_simps cteSizeBits_def
     wp: threadSet_not_inQ hoare_vcg_imp_lift' valid_irq_node_lift
         threadSet_ifunsafe'T threadSet_cur crunch_wps
         cur_tcb_lift valid_dom_schedule'_lift valid_replies'_lift irqs_masked_lift)

lemma schedContextDonate_valid_pspace':
  "\<lbrace>valid_pspace' and tcb_at' tcbPtr and sym_heap_sched_pointers and valid_sched_pointers\<rbrace>
   schedContextDonate scPtr tcbPtr
   \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  by (wpsimp wp: schedContextDonate_valid_objs' simp: valid_pspace'_def)

crunch setQueue, setSchedContext
  for valid_sched_pointers[wp]: valid_sched_pointers
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  (wp: threadSet_sched_pointers)

lemma schedContextDonate_if_live_then_nonz_cap':
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> valid_objs' s \<and> sym_heap_sched_pointers s
        \<and> ex_nonz_cap_to' tcbPtr s \<and> ex_nonz_cap_to' scPtr s
        \<and> valid_sched_pointers s
        \<and> pspace_aligned' s \<and> pspace_distinct' s \<and>  pspace_bounded' s\<rbrace>
   schedContextDonate scPtr tcbPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding schedContextDonate_def updateSchedContext_def
  by (wpsimp wp: threadSet_iflive'T setSchedContext_iflive' hoare_vcg_all_lift threadSet_cap_to'
           simp: conj_ac cong: conj_cong
      | wp hoare_drop_imps
      | fastforce simp: tcb_cte_cases_def cteSizeBits_def)+

crunch schedContextDonate
  for sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_sched_pointers[wp]: valid_sched_pointers
  and valid_bitmaps[wp]: valid_bitmaps
  (wp: crunch_wps threadSet_sched_pointers threadSet_valid_sched_pointers hoare_vcg_all_lift
   simp: crunch_simps)

lemma schedContextDonate_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> bound_sc_tcb_at' ((=) None) tcbPtr s \<and>
        ex_nonz_cap_to' scPtr s \<and> ex_nonz_cap_to' tcbPtr s\<rbrace>
   schedContextDonate scPtr tcbPtr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_pspace'_def valid_dom_schedule'_def)
  apply (wpsimp wp: schedContextDonate_valid_objs' schedContextDonate_if_live_then_nonz_cap')
  done

lemma setQueue_valid_tcbs'[wp]:
  "setQueue qdom prio q \<lbrace>valid_tcbs'\<rbrace>"
  unfolding valid_tcbs'_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')

lemma schedContextDonate_corres_helper:
  "(case rv' of SwitchToThread x \<Rightarrow> when (x = t \<or> t = cur) rescheduleRequired
                             | _ \<Rightarrow> when (t = cur) rescheduleRequired) =
   (when (t = cur \<or> (case rv' of SwitchToThread x \<Rightarrow> t = x | _ \<Rightarrow> False)) rescheduleRequired)"
  by (case_tac rv'; clarsimp simp: when_def)

crunch tcbReleaseRemove
  for valid_tcbs'[wp]: valid_tcbs'
  (wp: crunch_wps)

lemma thread_set_not_in_valid_ready_qs:
  "\<lbrace>valid_ready_qs and not_queued tcb_ptr\<rbrace> thread_set f tcb_ptr \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  apply (clarsimp simp: valid_ready_qs_def vs_all_heap_simps not_queued_def get_tcb_def
                 split: option.splits)
  by (metis Structures_A.kernel_object.case(5) option.sel option.simps(3))

lemma thread_set_in_correct_ready_q:
  "\<lbrakk>\<And>tcb. tcb_domain (f tcb) = tcb_domain tcb; \<And>tcb. tcb_priority (f tcb) = tcb_priority tcb\<rbrakk>
   \<Longrightarrow> thread_set f tptr \<lbrace>in_correct_ready_q\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps etcbs_of_tcbs_def
                        in_correct_ready_q_def)
  apply (fastforce simp: pred_map_def map_project_def opt_map_def tcbs_of_kh_def
                  split: option.splits)
  done

lemma tcb_sched_dequeue_in_correct_ready_q[wp]:
  "tcb_sched_action tcb_sched_dequeue t \<lbrace>in_correct_ready_q\<rbrace> "
  unfolding tcb_sched_action_def set_tcb_queue_def
  apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: in_correct_ready_q_def tcb_sched_dequeue_def)
  done

lemma tcb_sched_dequeue_ready_qs_distinct[wp]:
  "tcb_sched_action tcb_sched_dequeue t \<lbrace>ready_qs_distinct\<rbrace> "
  unfolding tcb_sched_action_def set_tcb_queue_def
  apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: ready_qs_distinct_def tcb_sched_dequeue_def)
  done

lemma thread_set_ready_qs_distinct[wp]:
  "thread_set f tcb_ptr \<lbrace>ready_qs_distinct\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  by (clarsimp simp: ready_qs_distinct_def)

lemma schedContextDonate_corres:
  "corres dc
     (sc_at scp and tcb_at thread and weak_valid_sched_action and pspace_aligned
      and pspace_distinct and valid_objs and active_scs_valid
      and in_correct_ready_q and ready_qs_distinct and ready_or_release
      and (\<lambda>s. distinct (release_queue s)))
     (valid_objs' and sym_heap_sched_pointers
      and valid_sched_pointers and pspace_aligned' and pspace_distinct')
     (sched_context_donate scp thread) (schedContextDonate scp thread)"
  apply (simp add: test_reschedule_def get_sc_obj_ref_def set_tcb_obj_ref_thread_set
                   schedContextDonate_def sched_context_donate_def schedContextDonate_corres_helper)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split [OF get_sc_corres])
      apply (rule corres_split [OF corres_when2])
          apply (clarsimp simp: sc_relation_def)
         apply (rule corres_assert_opt_assume_l)
         apply (rule corres_split_nor)
            apply (rule_tac x="the (sc_tcb sc)" and x'="the (scTCB sca)" in lift_args_corres)
             apply (rule tcbSchedDequeue_corres, simp)
            apply (clarsimp simp: sc_relation_def)
           apply (rule corres_split_nor)
              apply (rule tcbReleaseRemove_corres)
              apply (clarsimp simp: sc_relation_def)
             apply (rule corres_split_nor)
                apply (rule_tac x="the (sc_tcb sc)" and x'="the (scTCB sca)" in lift_args_corres)
                 apply (rule threadset_corresT)
                       apply (clarsimp simp: tcb_relation_def)
                      apply (clarsimp simp: tcb_cap_cases_def)
                     apply (fastforce simp: tcb_cte_cases_def objBits_simps')
                    apply fastforce
                   apply fastforce
                  apply (fastforce simp: inQ_def)
                 apply fastforce
                apply (clarsimp simp: sc_relation_def)
               apply (rule corres_split_eqr)
                  apply (rule getCurThread_corres)
                 apply (rule_tac r'=sched_act_relation in corres_split)
                    apply (rule getSchedulerAction_corres)
                   apply (rule corres_when)
                    apply (case_tac rv; fastforce simp: sched_act_relation_def sc_relation_def)
                   apply (rule rescheduleRequired_corres_weak)
                  apply wpsimp
                 apply wpsimp
                apply wpsimp
               apply wpsimp
              apply ((wpsimp wp: hoare_drop_imps thread_set_not_in_valid_ready_qs
                                 thread_set_in_correct_ready_q
                      | drule Some_to_the)+)[1]
             apply (wpsimp wp: hoare_drop_imps threadSet_sched_pointers threadSet_valid_sched_pointers)
            apply ((wpsimp | strengthen weak_valid_sched_action_strg | drule Some_to_the)+)[1]
           apply (rule_tac Q'="\<lambda>_. valid_tcbs' and sym_heap_sched_pointers and valid_sched_pointers
                                  and pspace_aligned' and pspace_distinct'"
                        in hoare_strengthen_post[rotated])
            apply clarsimp
           apply (wpsimp wp: hoare_vcg_all_lift)
          apply (wpsimp wp: tcb_sched_dequeue_valid_ready_qs tcb_dequeue_not_queued
                            hoare_vcg_all_lift hoare_vcg_imp_lift')
         apply (wpsimp wp: hoare_vcg_all_lift)
        apply (rule corres_split
                   [OF updateSchedContext_no_stack_update_corres
                         [where f'="scTCB_update (\<lambda>_. Some thread)"]])
              apply (clarsimp simp: sc_relation_def refillSize_def)
             apply clarsimp
            apply (clarsimp simp: objBits_def objBitsKO_def)
           apply clarsimp
          apply (rule threadset_corresT)
                apply (clarsimp simp: tcb_relation_def)
               apply (fastforce simp: tcb_cap_cases_def objBits_simps')
              apply (fastforce simp: tcb_cte_cases_def objBits_simps')
             apply wpsimp
            apply wpsimp
           apply (fastforce simp: inQ_def)
          apply fastforce
         apply (wpsimp wp: hoare_drop_imp)+
   apply (frule (1) valid_objs_ko_at)
   apply (fastforce simp: valid_obj_def valid_sched_context_def valid_bound_obj_def obj_at_def)
  apply (fastforce elim: sc_at_cross tcb_at_cross simp: state_relation_def)
  done

end
