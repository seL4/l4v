(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Schedule_C
imports Tcb_C Retype_C
begin

(*FIXME: arch_split: move up?*)
context Arch begin
context begin global_naming global
requalify_facts
  Thread_H.switchToIdleThread_def
  Thread_H.switchToThread_def
end
end

context kernel_m begin

lemma Arch_switchToIdleThread_ccorres:
  "ccorres dc xfdc invs' UNIV []
     Arch.switchToIdleThread (Call Arch_switchToIdleThread_'proc)"
  apply (cinit simp: RISCV64_H.switchToIdleThread_def)
   apply (rule ccorres_stateAssert)
   apply (rule ccorres_pre_getIdleThread)
   apply (rule ccorres_symb_exec_r)
     apply (ctac (no_vcg) add: setVMRoot_ccorres)
    apply vcg
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply (clarsimp simp: valid_pspace'_def valid_idle'_asrt_def valid_idle'_tcb_at'_ksIdleThread)
  done

lemma switchToIdleThread_ccorres:
  "ccorres dc xfdc invs' UNIV hs
     switchToIdleThread (Call switchToIdleThread_'proc)"
  apply cinit
   apply (rule ccorres_stateAssert)+
   apply (rule ccorres_symb_exec_l)
      apply (ctac (no_vcg) add: Arch_switchToIdleThread_ccorres)
       apply (simp add: setCurThread_def)
       apply (rule ccorres_stateAssert)
       apply (rule_tac P="\<lambda>s. thread = ksIdleThread s" and P'=UNIV in ccorres_from_vcg)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: simpler_modify_def)
       apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                             carch_state_relation_def cmachine_state_relation_def)
      apply (wpsimp simp: RISCV64_H.switchToIdleThread_def wp: hoare_drop_imps)+
  done

lemma Arch_switchToThread_ccorres:
  "ccorres dc xfdc
           (invs' and tcb_at' t)
           (UNIV \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           []
           (Arch.switchToThread t) (Call Arch_switchToThread_'proc)"
  apply (cinit lift: tcb_')
   apply (unfold RISCV64_H.switchToThread_def)[1]
   apply (ctac (no_vcg) add: setVMRoot_ccorres)
  apply (simp (no_asm) del: Collect_const)
  apply clarsimp
  done

lemma tcbQueued_False_ready_qs_runnable:
  "threadSet (tcbQueued_update (\<lambda>_. False)) tcbPtr \<lbrace>ready_qs_runnable\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  by (clarsimp simp: ready_qs_runnable_def pred_tcb_at'_def obj_at'_def ps_clear_upd
              split: if_splits)

lemma tcbSchedNext_update_ready_qs_runnable[wp]:
  "threadSet (tcbSchedNext_update f) tcbPtr \<lbrace>ready_qs_runnable\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  by (fastforce simp: ready_qs_runnable_def pred_tcb_at'_def obj_at'_def ps_clear_upd
               split: if_splits)

lemma tcbSchedPrev_update_ready_qs_runnable[wp]:
  "threadSet (tcbSchedPrev_update f) tcbPtr \<lbrace>ready_qs_runnable\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  by (fastforce simp: ready_qs_runnable_def pred_tcb_at'_def obj_at'_def ps_clear_upd
               split: if_splits)

crunch removeFromBitmap, setQueue
  for ready_qs_runnable[wp]: ready_qs_runnable
  (simp: bitmap_fun_defs crunch_simps ready_qs_runnable_def)

lemma tcbSchedDequeue_ready_qs_runnable[wp]:
  "tcbSchedDequeue tcbPtr \<lbrace>ready_qs_runnable\<rbrace>"
  unfolding tcbSchedDequeue_def tcbQueueRemove_def
  apply (clarsimp simp: ready_qs_runnable_def)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_ball_lift2 threadGet_wp
                    tcbQueued_False_ready_qs_runnable getTCB_wp)
  apply (fastforce simp: obj_at_simps split: if_splits)
  done

lemma threadGet_exs_valid[wp]:
  "tcb_at' t s \<Longrightarrow> \<lbrace>(=) s\<rbrace> threadGet f t \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  unfolding threadGet_def liftM_def
  apply (wpsimp wp: exs_getObject)
  apply (fastforce intro: no_ofailD[OF no_ofail_threadRead_tcb_at'])
  done

lemma isRunnable_exs_valid[wp]:
  "tcb_at' t s \<Longrightarrow> \<lbrace>(=) s\<rbrace> isRunnable t \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  unfolding isRunnable_def getThreadState_def
  by (wpsimp wp: exs_getObject)

(* FIXME: move *)
lemma switchToThread_ccorres:
  "ccorres dc xfdc
           (invs' and tcb_at' t)
           (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           hs
           (switchToThread t)
           (Call switchToThread_'proc)"
  apply (clarsimp simp: switchToThread_def)
  apply (rule ccorres_symb_exec_l'[OF _ _ isRunnable_sp]; wpsimp)
  apply (cinit' lift: thread_')
   apply (rule ccorres_assert2)
   apply (rule ccorres_stateAssert)+
   apply (ctac (no_vcg) add: Arch_switchToThread_ccorres)
    apply (ctac (no_vcg) add: tcbSchedDequeue_ccorres)
     apply (simp add: setCurThread_def)
     apply (rule ccorres_stateAssert)
     apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
     apply clarsimp
     apply (rule conseqPre, vcg)
     apply (clarsimp simp: simpler_modify_def rf_sr_def cstate_relation_def Let_def assert_def
                           carch_state_relation_def cmachine_state_relation_def)
    apply (wpsimp wp: hoare_vcg_all_lift)+
  apply (fastforce simp: ready_qs_runnable_def)
  done

lemma activateThread_ccorres:
  "ccorres dc xfdc
           (ct_in_state' activatable' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and valid_objs')
           UNIV []
           activateThread
           (Call activateThread_'proc)"
  apply (cinit)
sorry (* FIXME RT: activeThread_ccorres
   apply (rule ccorres_pre_getCurThread)
   apply (ctac add: get_tsType_ccorres [where f="\<lambda>s. ksCurThread_' (globals s)"])
     apply (rule_tac P="activatable' rv" in ccorres_gen_asm)
     apply (wpc)
            apply (rule_tac P=\<top> and P'=UNIV in ccorres_inst, simp)
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_inst, simp)
          apply (rule_tac P=\<top> and P'=UNIV in ccorres_inst, simp)
         apply simp
         apply (rule ccorres_cond_true)
         apply (rule ccorres_return_Skip)
        apply (rule_tac P=\<top> and P'=UNIV in ccorres_inst, simp)
       apply (simp add: ThreadState_defs del: Collect_const)
       apply (rule ccorres_cond_false)
       apply (rule ccorres_cond_false)
       apply (rule ccorres_cond_true)
       apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: activateIdleThread_def return_def)
      apply (rule_tac P=\<top> and P'=UNIV in ccorres_inst, simp)
     apply (simp add: ThreadState_defs del: Collect_const)
     apply (rule ccorres_cond_false)
     apply (rule ccorres_cond_true)
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply (ctac)
       apply (ctac add: setNextPC_ccorres)
         apply ctac
        apply (wp | simp add: valid_tcb_state'_def)+
       apply vcg
      apply wp
     apply vcg
    apply (wp gts_wp')
   apply vcg
  apply (clarsimp simp: ct_in_state'_def)
  apply (rule conjI, clarsimp)
  apply (clarsimp simp: st_tcb_at'_def)
  apply (rule conjI, clarsimp simp: obj_at'_def)
  apply clarsimp
  apply (drule (1) obj_at_cslift_tcb)
  apply (subgoal_tac "ksCurThread_' (globals s') = tcb_ptr_to_ctcb_ptr (ksCurThread s)")
   prefer 2
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (clarsimp simp: typ_heap_simps ThreadState_defs mask_def)
  done *)

lemma ceqv_Guard_UNIV_Skip:
  "ceqv Gamma xf v s s' (a ;; Guard F UNIV Skip) a"
  apply (rule ceqvI)
  apply (safe elim!: exec_Normal_elim_cases)
   apply (case_tac s'a, auto intro: exec.intros elim!: exec_Normal_elim_cases)[1]
  apply (cases s', auto intro: exec.intros)
  done

lemma ceqv_tail_Guard_onto_Skip:
  "ceqv Gamma xf v s s'
      (a ;; Guard F G b) ((a ;; Guard F G Skip) ;; b)"
  apply (rule ceqvI)
  apply (safe elim!: exec_Normal_elim_cases)
   apply (case_tac s'a, auto intro: exec.intros elim!: exec_Normal_elim_cases)[1]
  apply (case_tac s'aa, auto intro: exec.intros elim!: exec_Normal_elim_cases)[1]
  done

lemma ceqv_remove_tail_Guard_Skip:
  "\<lbrakk> \<And>s. s \<in> G \<rbrakk> \<Longrightarrow> ceqv Gamma xf v s s' (a ;; Guard F G Skip) a"
  apply (rule ceqvI)
  apply (safe elim!: exec_Normal_elim_cases)
   apply (case_tac s'a, auto intro: exec.intros elim!: exec_Normal_elim_cases)[1]
  apply (case_tac s', auto intro: exec.intros elim!: exec_Normal_elim_cases)[1]
  done

lemmas ccorres_remove_tail_Guard_Skip
    = ccorres_abstract[where xf'="\<lambda>_. ()", OF ceqv_remove_tail_Guard_Skip]

lemmas word_log2_max_word_word_size = word_log2_max[where 'a=machine_word_len, simplified word_size, simplified]

lemma ccorres_pre_getQueue:
  assumes cc: "\<And>queue. ccorres r xf (P queue) (P' queue) hs (f queue) c"
  shows   "ccorres r xf (\<lambda>s. P (ksReadyQueues s (d, p)) s \<and> d \<le> maxDomain \<and> p \<le> maxPriority)
                        {s'. \<forall>queue. (let cqueue = index (ksReadyQueues_' (globals s'))
                                                         (cready_queues_index_to_C d p) in
                                      ctcb_queue_relation queue cqueue) \<longrightarrow> s' \<in> P' queue}
           hs (getQueue d p >>= (\<lambda>queue. f queue)) c"
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_symb_exec_l2)
     defer
     defer
     apply (rule gq_sp)
    defer
    apply (rule ccorres_guard_imp)
    apply (rule cc)
     apply clarsimp
     apply assumption
    apply assumption
   apply (clarsimp simp: getQueue_def gets_exs_valid)
  apply clarsimp
  apply (drule spec, erule mp)
  apply (erule rf_sr_ctcb_queue_relation)
   apply (simp add: maxDom_to_H maxPrio_to_H)+
  done

lemma lookupBitmapPriority_le_maxPriority:
  "\<lbrakk> ksReadyQueuesL1Bitmap s d \<noteq> 0 ;
     \<forall>d p. d > maxDomain \<or> p > maxPriority \<longrightarrow> tcbQueueEmpty (ksReadyQueues s (d, p));
     valid_bitmaps s \<rbrakk>
   \<Longrightarrow> lookupBitmapPriority d s \<le> maxPriority"
  apply (clarsimp simp: valid_bitmaps_def)
  by (fastforce dest!: bitmapQ_from_bitmap_lookup bitmapQ_ksReadyQueuesI intro: ccontr)

lemma chooseThread_ccorres:
  "ccorres dc xfdc invs' UNIV [] chooseThread (Call chooseThread_'proc)"
proof -

  note prio_and_dom_limit_helpers [simp]
  note ksReadyQueuesL2Bitmap_nonzeroI [simp]
  note Collect_const_mem [simp]
  note invs_ksCurDomain_maxDomain'[intro]
  (* when numDomains = 1, array bounds checks would become _ = 0 rather than _ < 1, changing the
     shape of the proof compared to when numDomains > 1 *)
  include no_less_1_simps

  show ?thesis
    supply if_split[split del]
    apply (cinit)
    apply (rule ccorres_stateAssert)+
     apply (simp add: numDomains_sge_1_simp)
     apply (rule_tac xf'=dom_' and r'="\<lambda>rv rv'. rv' = ucast rv" in ccorres_split_nothrow_novcg)
         apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
         apply clarsimp
         apply (rule conseqPre, vcg)
         apply (rule Collect_mono)
         apply (clarsimp split: prod.split)
         apply (clarsimp simp: curDomain_def simpler_gets_def return_def rf_sr_ksCurDomain)
        apply ceqv
       apply clarsimp
       apply (rename_tac curdom)
       apply (rule_tac P="curdom \<le> maxDomain" in ccorres_cross_over_guard_no_st)
       apply (rule ccorres_Guard)
       apply (rule ccorres_pre_getReadyQueuesL1Bitmap)
       apply (rename_tac l1)
       apply (rule_tac R="\<lambda>s. l1 = ksReadyQueuesL1Bitmap s curdom \<and> curdom \<le> maxDomain"
                in ccorres_cond)
         subgoal by (fastforce dest!: rf_sr_cbitmap_L1_relation simp: cbitmap_L1_relation_def)
        prefer 2 \<comment> \<open>switchToIdleThread\<close>
        apply (ctac(no_vcg) add: switchToIdleThread_ccorres)
       apply clarsimp
       apply (rule ccorres_rhs_assoc)+
       apply (rule ccorres_split_nothrow_novcg)
           apply (rule_tac xf'=prio_' in ccorres_call)
              apply (rule getHighestPrio_ccorres[simplified getHighestPrio_def'])
             apply simp+
          apply ceqv
         apply clarsimp
         apply (rename_tac prio)
         apply (rule_tac P="curdom \<le> maxDomain" in ccorres_cross_over_guard_no_st)
         apply (rule_tac P="prio \<le> maxPriority" in ccorres_cross_over_guard_no_st)
         apply (rule ccorres_pre_getQueue)
         apply (rule_tac P="\<not> tcbQueueEmpty queue" in ccorres_cross_over_guard_no_st)
         apply (rule ccorres_symb_exec_r)
           apply (rule ccorres_Guard_Seq)+
           apply (rule ccorres_symb_exec_r)
             apply (rule ccorres_call[OF switchToThread_ccorres]; simp)
            apply vcg
           apply (rule conseqPre, vcg)
           apply clarsimp
          apply clarsimp
          apply (rule conseqPre, vcg)
          apply (rule Collect_mono)
          apply clarsimp
          apply assumption
         apply (rule conseqPre, vcg)
         apply clarsimp
        apply (wpsimp wp: isSchedulable_wp)+
       apply (clarsimp simp: Let_def guard_is_UNIV_def ctcb_queue_relation_def
                             option_to_ctcb_ptr_def cready_queues_index_to_C_def numPriorities_def
                             le_maxDomain_eq_less_numDomains unat_trans_ucast_helper queue_in_range
                             tcbQueueEmpty_def)
      apply (clarsimp simp: maxDom_to_H maxPrio_to_H)
      apply wpsimp
     apply (clarsimp simp: guard_is_UNIV_def le_maxDomain_eq_less_numDomains word_less_nat_alt
                           numDomains_less_numeric_explicit)
    apply clarsimp
    apply (frule invs_ksCurDomain_maxDomain')
    apply (frule invs_valid_bitmaps)
    apply (frule invs_pspace_aligned')
    apply (frule invs_pspace_distinct')
    apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def valid_bitmaps_def)
    apply (drule_tac x="ksCurDomain s" in spec)
    apply (drule_tac x="lookupBitmapPriority (ksCurDomain s) s" in spec)
    apply (clarsimp simp: tcbQueueEmpty_def cong: conj_cong)
    apply (frule (3) obj_at'_tcbQueueHead_ksReadyQueues)
    apply (rule conjI)
     subgoal
       by (fastforce dest: bitmapQ_from_bitmap_lookup
                     simp: valid_bitmapQ_bitmapQ_simp tcbQueueEmpty_def)
    apply (clarsimp simp: not_less le_maxDomain_eq_less_numDomains)
    apply (prop_tac "ksCurDomain s = 0")
     using unsigned_eq_0_iff apply force
    by (fastforce dest: bitmapQ_from_bitmap_lookup
                  simp: valid_bitmapQ_bitmapQ_simp tcbQueueEmpty_def)
qed

lemma ksDomSched_length_relation[simp]:
  "\<lbrakk>cstate_relation s s'\<rbrakk> \<Longrightarrow> length (kernel_state.ksDomSchedule s) = unat (ksDomScheduleLength)"
  apply (auto simp: cstate_relation_def cdom_schedule_relation_def Let_def ksDomScheduleLength_def)
  done

lemma ksDomSched_length_dom_relation[simp]:
  "\<lbrakk>cdom_schedule_relation (kernel_state.ksDomSchedule s) ksDomSchedule\<rbrakk>
   \<Longrightarrow> length (kernel_state.ksDomSchedule s) = unat (ksDomScheduleLength)"
  apply (auto simp: cstate_relation_def cdom_schedule_relation_def Let_def ksDomScheduleLength_def)
  done

(* FIXME RT: move to Lib *)
lemma mult_non_zero_less_eq:
  fixes a b c :: nat
  assumes "a * b \<le> c"
      and "0 < b"
  shows "a \<le> c"
  using assms
  by (metis le_0_eq le_eq_less_or_eq less_irrefl_nat multi_lessD nat_le_linear)

lemma domain_time_overflow_condition_helper:
  "\<lbrakk>cdom_schedule_relation (kernel_state.ksDomSchedule s) ksDomSchedule; valid_domain_list' s\<rbrakk>
   \<Longrightarrow> \<forall>n<length(kernel_state.ksDomSchedule s).
        unat (dschedule_C.length_C (ksDomSchedule.[n]) * \<mu>s_in_ms) * unat ticks_per_timer_unit
        \<le> unat max_time"
  apply (clarsimp simp: valid_domain_list'_def)
  apply (drule_tac x="(kernel_state.ksDomSchedule s) ! n" in bspec)
   apply fastforce
  apply clarsimp
  apply (rename_tac n d time)
  apply (prop_tac "dschedule_C.length_C (ksDomSchedule.[n]) = time")
   apply (frule ksDomSched_length_dom_relation)
   apply (simp add: ksDomScheduleLength_def sdiv_word_def sdiv_int_def)
   apply (clarsimp simp: cdom_schedule_relation_def dom_schedule_entry_relation_def
               simp del: ksDomSched_length_dom_relation)
   apply (drule_tac x=n in spec)
   apply clarsimp
  apply (subst unat_mult_lem')
   apply (rule_tac b="unat ticks_per_timer_unit" in mult_non_zero_less_eq)
    apply simp
   apply (fastforce simp: ticks_per_timer_unit_non_zero neq_0_unat)
  apply simp
  done

lemma nextDomain_ccorres:
  "ccorres dc xfdc (invs' and valid_domain_list') UNIV [] nextDomain (Call nextDomain_'proc)"
  supply ksDomSched_length_dom_relation[simp del]
  apply cinit
   apply (simp add: ksDomScheduleLength_def sdiv_word_def sdiv_int_def)
   apply (rule_tac P="invs' and valid_domain_list'" and P'=UNIV in ccorres_from_vcg)
   apply (rule allI, rule conseqPre, vcg)
   apply (simp add: rf_sr_def cstate_relation_def carch_state_relation_def
                    cmachine_state_relation_def)
   apply (clarsimp simp: simpler_modify_def Let_def)
   apply (rename_tac s s')
   apply (rule conjI)
    apply clarsimp
    apply (prop_tac "ksDomScheduleIdx s = unat (ksDomScheduleLength - 1)")
     apply (simp add: ksDomScheduleLength_def)
     apply (frule invs'_ksDomScheduleIdx)
     apply (simp add: invs'_ksDomSchedule newKernelState_def)
     apply (simp only: Abs_fnat_hom_1 Abs_fnat_hom_add)
     apply (drule unat_le_helper)
     apply (clarsimp simp: cdom_schedule_relation_def)
    apply (rule conjI)
     apply (fastforce dest!: domain_time_overflow_condition_helper
                       simp: \<mu>s_in_ms_def valid_domain_list'_def)
    apply (fastforce simp: usInMs_def cdom_schedule_relation_def dom_schedule_entry_relation_def
                           dschDomain_def dschLength_def ksDomScheduleLength_def)
   apply (simp only: Abs_fnat_hom_1 Abs_fnat_hom_add word_not_le)
   apply clarsimp
   apply (subst (asm) of_nat_Suc[symmetric])
   apply (drule iffD1[OF of_nat_mono_maybe'[where x=3, simplified, symmetric], rotated 2])
     apply simp
    apply (frule invs'_ksDomScheduleIdx)
    apply (simp add: invs'_ksDomSchedule cdom_schedule_relation_def)
   apply (clarsimp simp: ksDomScheduleLength_def)
   apply (subst of_nat_Suc[symmetric])+
   apply (subst unat_of_nat64, simp add: word_bits_def)+
   apply (frule (1) domain_time_overflow_condition_helper)
   apply (clarsimp simp: cdom_schedule_relation_def dom_schedule_entry_relation_def
                         dschDomain_def dschLength_def \<mu>s_in_ms_def usInMs_def)
  apply simp
  done

(* FIXME RT: move *)
crunch nextDomain
  for valid_idle'[wp]: valid_idle'
  and ready_or_release'[wp]: ready_or_release'
  and ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksReadyQueues_asrt[wp]: ksReadyQueues_asrt
  (simp: crunch_simps ready_or_release'_def ksReadyQueues_asrt_def)

lemma scheduleChooseNewThread_ccorres:
  "ccorres dc xfdc
     (\<lambda>s. invs' s \<and> valid_idle' s
          \<and> ksSchedulerAction s = ChooseNewThread \<and> ready_or_release' s
          \<and> valid_domain_list' s
          \<and> (\<forall>d p. d > maxDomain \<or> p > maxPriority \<longrightarrow> tcbQueueHead (ksReadyQueues s (d, p)) = None)
          \<and> ksReadyQueues_asrt s)
     UNIV hs
     (do domainTime \<leftarrow> getDomainTime;
         y \<leftarrow> when (domainTime = 0) nextDomain;
         chooseThread
      od)
     (Call scheduleChooseNewThread_'proc)"
  apply (cinit')
   apply (rule ccorres_pre_getDomainTime)
   apply (rule ccorres_split_nothrow)
       apply (rule_tac R="\<lambda>s. ksDomainTime s = domainTime" in ccorres_when)
        apply (fastforce simp: rf_sr_ksDomainTime)
       apply (rule_tac xf'=xfdc in ccorres_call[OF nextDomain_ccorres] ; simp)
      apply ceqv
     apply (ctac (no_vcg) add: chooseThread_ccorres)
    apply (wpsimp wp: nextDomain_invs' hoare_vcg_all_lift hoare_vcg_imp_lift')
   apply clarsimp
   apply (vcg exspec=nextDomain_modifies)
  apply (clarsimp simp: if_apply_def2)
  done

lemma isHighestPrio_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
           (\<lambda>s. d \<le> maxDomain \<and> bitmapQ_no_L1_orphans s)
           (UNIV \<inter> \<lbrace>\<acute>dom = ucast d\<rbrace> \<inter> \<lbrace>\<acute>prio = ucast p\<rbrace>) hs
           (isHighestPrio d p)
           (Call isHighestPrio_'proc)"
  supply Collect_const [simp del]
  supply prio_and_dom_limit_helpers[simp]
  supply Collect_const_mem [simp]
  (* FIXME: these should likely be in simpset for CRefine, or even in general *)
  supply from_bool_eq_if[simp] from_bool_eq_if'[simp] from_bool_0[simp]
          ccorres_IF_True[simp] if_cong[cong]
  (* when numDomains = 1, array bounds checks would become _ = 0 rather than _ < 1, changing the
     shape of the proof compared to when numDomains > 1 *)
  including no_less_1_simps
  apply (cinit lift: dom_' prio_')
   apply clarsimp
   apply (rule ccorres_move_const_guard)
   apply (rule ccorres_pre_getReadyQueuesL1Bitmap, rename_tac l1)
   apply (rule ccorres_rhs_assoc2)
   apply (rule ccorres_cond_seq2[THEN iffD1])
   apply ccorres_rewrite
   apply (rule_tac xf'=ret__int_' and val="from_bool (l1 = 0)"
             and R="\<lambda>s. l1 = ksReadyQueuesL1Bitmap s d \<and> d \<le> maxDomain" and R'=UNIV
             in ccorres_symb_exec_r_known_rv)
      apply vcg
      apply clarsimp
      apply (fastforce simp: rf_sr_ksReadyQueuesL1Bitmap_simp)
     apply ceqv
    apply clarsimp
    apply (rule ccorres_cond[where R=\<top>], blast)
     apply (rule_tac P="l1 = 0" in ccorres_gen_asm, clarsimp)
     apply (rule ccorres_return_C; clarsimp)
    apply (rule ccorres_rhs_assoc)+
    apply (ctac add: getHighestPrio_ccorres[simplified])
      apply (rename_tac hprio hprio')
      apply csymbr
      apply (rule ccorres_return_C, simp, simp, simp)
     apply (rule wp_post_taut)
    apply (vcg exspec=getHighestPrio_modifies)+
  apply (clarsimp simp: word_le_nat_alt maxDomain_le_unat_ucast_explicit
                  split: if_splits)
  done

lemma refill_size_length_scRefills_helper:
  "\<lbrakk>valid_sched_context' sc s; valid_sched_context_size' sc\<rbrakk>
   \<Longrightarrow> Suc (2 * length (scRefills sc)) < 2 ^ word_bits"
  apply (fastforce dest: length_scRefills_bounded
                   simp: refillSizeBytes_def word_bits_def)
  done

crunch getSchedContext
 for (empty_fail) empty_fail[wp]

lemma refill_size_ccorres:
  "ccorres (\<lambda>rv rv'. rv = unat rv') ret__unsigned_long_'
     (sc_at' scPtr and valid_objs' and valid_refills' scPtr) \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (getRefillSize scPtr) (Call refill_size_'proc)"
  supply len_bit0[simp del]
  apply (cinit lift: sc_', rename_tac sc)
   apply (clarsimp simp: readRefillSize_def readSchedContext_def getObject_def[symmetric]
                         getSchedContext_def[symmetric] refillSize_def)
   apply (rule ccorres_symb_exec_l, rename_tac sc)
      apply (rule ccorres_move_c_guard_sc)+
      apply (rule ccorres_cond_seq)
      apply ccorres_rewrite
      apply (simp add: if_distrib[where f=return])
      apply (rule_tac R="ko_at' sc scPtr and valid_objs' and K (sc_valid_refills' sc)"
                   in ccorres_cond)
        apply (fastforce dest: obj_at_cslift_sc
                         simp: csched_context_relation_def typ_heap_simps word_le_nat_alt)
       apply (ctac add: ccorres_return_C)
      apply (ctac add: ccorres_return_C)
     apply wpsimp
    apply wpsimp
   apply wpsimp
  apply (rule conjI)
   apply (fastforce simp: obj_at_simps valid_refills'_def in_omonad)
  apply clarsimp
  apply (rename_tac sc abs_state)
  apply (drule_tac s=abs_state in obj_at_cslift_sc)
   apply fastforce
  apply normalise_obj_at'
  apply (clarsimp simp: csched_context_relation_def typ_heap_simps')
  apply (elim impE)
   apply (subst unat_add_lem')+
     apply (fastforce simp: less_trans_Suc)
    apply (subst unat_sub)
     apply (clarsimp simp: word_le_nat_alt)
    apply (frule_tac k=sc in sc_ko_at_valid_objs_valid_sc')
     apply assumption
    apply (fastforce dest: refill_size_length_scRefills_helper simp: word_bits_len_of)
   apply (fastforce simp: less_trans_Suc unat_add_lem' unat_sub word_le_nat_alt)
  apply (subst unat_add_lem'')
   apply (subst unat_sub)
    apply (clarsimp simp: word_le_nat_alt)
   apply (rule_tac y="unat (scRefillMax_C ko')" in order_trans; fastforce)
  apply (fastforce simp: unat_sub word_le_nat_alt)
  done

lemma refill_full_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     (sc_at' scPtr and valid_objs' and valid_refills' scPtr) \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (getRefillFull scPtr) (Call refill_full_'proc)"
  apply (cinit simp: readRefillFull_def readSchedContext_def getObject_def[symmetric]
                     getSchedContext_def[symmetric] getRefillSize_def[symmetric])
   apply (rule ccorres_pre_getObject_sc)
   apply (ctac add: refill_size_ccorres)
     apply (ctac add: ccorres_return_C)
    apply (wpsimp wp: getRefillSize_wp)
   apply (vcg exspec=refill_size_modifies)
  apply (fastforce simp: csched_context_relation_def typ_heap_simps split: if_splits)
  done

(* FIXME RT: move to Refine *)
lemma length_scRefills_bounded:
  "\<lbrakk>valid_sched_context' sc s; valid_sched_context_size' sc\<rbrakk>
   \<Longrightarrow> length (scRefills sc) < 2 ^ word_bits"
  apply (clarsimp simp: valid_sched_context_size'_def sc_size_bounds_def objBits_simps
                        valid_sched_context'_def)
  apply (insert schedContextStructSize_minSchedContextBits)
  apply (prop_tac "schedContextStructSize \<le> 2 ^ (minSchedContextBits + scSize sc)")
   apply (fastforce intro: order_trans)
  apply (frule_tac n="minSchedContextBits + scSize sc" in refillAbsoluteMax'_leq)
  apply (rule_tac y="2 ^ (minSchedContextBits + scSize sc)" in le_less_trans)
   apply (clarsimp simp: refillSizeBytes_def)
  apply simp
  apply (clarsimp simp: word_bits_def untypedBits_defs)
  done

lemma sc_released_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     (active_sc_at' scPtr and valid_objs') \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (scReleased scPtr) (Call sc_released_'proc)"
  apply (cinit simp: readScReleased_def scActive_def[symmetric] gets_the_if_distrib)
   apply (ctac add: sc_active_ccorres)
     apply (rule ccorres_cond[where R=\<top>])
       apply (clarsimp simp: to_bool_def)
      apply (simp flip: refillReady_def)
      apply (rule ccorres_add_return2)
      apply (ctac add: refill_ready_ccorres)
        apply (fastforce intro: ccorres_return_C)
       apply wpsimp
      apply vcg
     apply (fastforce intro: ccorres_return_C)
    apply wpsimp
   apply vcg
  apply clarsimp
  done

lemma switchSchedContext_ccorres:
  "ccorres dc xfdc \<top> UNIV [] switchSchedContext (Call switchSchedContext_'proc)"
sorry (* FIXME RT: switchSchedContext_ccorres *)

lemma refill_budget_check_ccorres:
  "ccorres dc xfdc
     \<top> \<lbrace>\<acute>usage = usage\<rbrace> []
     (refillBudgetCheck usage) (Call refill_budget_check_'proc)"
sorry (* FIXME RT: refill_budget_check_ccorres *)

lemma checkDomainTime_ccorres:
  "ccorres dc xfdc \<top> UNIV [] checkDomainTime (Call checkDomainTime_'proc)"
sorry (* FIXME RT: checkDomainTime_ccorres *)

lemma commitTime_ccorres:
  "ccorres dc xfdc \<top> UNIV [] commitTime (Call commitTime_'proc)"
sorry (* FIXME RT: commitTime_ccorres *)

lemma schedule_ccorres:
  "ccorres dc xfdc invs' UNIV [] schedule (Call schedule_'proc)"
sorry (* FIXME RT: schedule_ccorres
  supply Collect_const [simp del]
  supply prio_and_dom_limit_helpers[simp]
  supply Collect_const_mem [simp]
  (* FIXME: these should likely be in simpset for CRefine, or even in general *)
  supply from_bool_eq_if[simp] from_bool_eq_if'[simp] from_bool_0[simp]
         ccorres_IF_True[simp] if_cong[cong]
  apply (cinit)
   apply (rule ccorres_pre_getCurThread)
   apply (rule ccorres_pre_getSchedulerAction)
   apply wpc
     (* toplevel case: action is resume current thread *)
     apply (rule ccorres_cond_false_seq)
     apply simp
     apply (rule_tac P=\<top> and P'="{s. ksSchedulerAction_' (globals s) = NULL }" in ccorres_from_vcg)
     apply (clarsimp simp: return_def split: prod.splits)
     apply (rule conseqPre, vcg, clarsimp)
    (* toplevel case: action is choose new thread *)
    apply (rule ccorres_cond_true_seq)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    (* ct runnable? *)
    apply (ctac add: isRunnable_ccorres, rename_tac runnable)
      apply (clarsimp simp: to_bool_def)
      apply (rule ccorres_split_nothrow_dc)
         (* enqueue if runnable *)
         apply (simp add: when_def)
         apply (rule ccorres_cond[where R=\<top>], clarsimp)
         apply csymbr
         apply (ctac add: tcbSchedEnqueue_ccorres)
         apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
         apply (clarsimp, rule conseqPre, vcg)
         apply (clarsimp simp: return_def)
        apply (rule ccorres_cond_true_seq)
        (* isolate haskell part before setting thread action *)
        apply (simp add: scheduleChooseNewThread_def)
        apply (rule ccorres_lhs_assoc)+
        apply (rule ccorres_split_nothrow_dc)
           apply (simp add: bind_assoc)
           apply (ctac add: scheduleChooseNewThread_ccorres)
          apply (ctac(no_simp) add: ccorres_setSchedulerAction)
          apply (wpsimp simp: cscheduler_action_relation_def
                 | vcg exspec=scheduleChooseNewThread_modifies exspec=tcbSchedEnqueue_modifies)+
   (* toplevel case: action is switch to candidate *)
   apply (rename_tac candidate)
   apply (rule_tac P="\<lambda>s. ksSchedulerAction s = SwitchToThread candidate \<and> invs' s" in ccorres_cross_over_guard)
   apply (rule ccorres_cond_true_seq)
   apply (rule ccorres_rhs_assoc)+
   apply csymbr
   (* ct runnable? *)
   apply (ctac add: isRunnable_ccorres, rename_tac runnable runnable')
     apply (clarsimp simp: to_bool_def)
     apply (rule ccorres_split_nothrow_dc)
        (* enqueue if runnable *)
        apply (simp add: when_def)
        apply (rule ccorres_cond[where R=\<top>], clarsimp)
        apply csymbr
        apply (ctac add: tcbSchedEnqueue_ccorres)
        apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
        apply (clarsimp, rule conseqPre, vcg)
        apply (clarsimp simp: return_def)
       apply (rule ccorres_cond_false_seq)

       apply (rule_tac xf'=was_runnable_' in ccorres_abstract, ceqv)
       apply (rename_tac was_runnable')
       apply (rule_tac P="was_runnable' = runnable'" in ccorres_gen_asm2, clarsimp)
       apply (rule ccorres_symb_exec_l3[OF _ git_wp _ empty_fail_getIdleThread], rename_tac it)
        apply (rule ccorres_pre_threadGet, rename_tac targetPrio)
        apply (rule ccorres_pre_threadGet, rename_tac curPrio)
        apply (rule ccorres_rhs_assoc)+
        apply (rule_tac xf'=candidate_' and val="tcb_ptr_to_ctcb_ptr candidate"
                 and R="\<lambda>s. ksSchedulerAction s = SwitchToThread candidate" and R'=UNIV
                 in ccorres_symb_exec_r_known_rv)
           apply (rule conseqPre, vcg, clarsimp)
           apply (fastforce dest!: rf_sr_cscheduler_relation simp: cscheduler_action_relation_def)
          apply ceqv
         (* split off fastfail calculation *)
         apply (rule ccorres_rhs_assoc2)
         apply (rule ccorres_rhs_assoc2)
         apply (rule_tac r'="\<lambda>rv rv'. rv = to_bool rv'" and xf'=fastfail_' in ccorres_split_nothrow)
             apply (clarsimp simp: scheduleSwitchThreadFastfail_def)
             apply (rule ccorres_cond_seq2[THEN iffD1])
             apply (rule_tac xf'=ret__int_' and val="from_bool (curThread = it)"
                      and R="\<lambda>s. it = ksIdleThread s \<and> curThread = ksCurThread s" and R'=UNIV
                      in ccorres_symb_exec_r_known_rv)
                apply (rule conseqPre, vcg, fastforce simp: rf_sr_ksCurThread rf_sr_ksIdleThread)
               apply ceqv
              apply clarsimp
              apply (rule ccorres_cond2'[where R=\<top>], fastforce)
               apply clarsimp
               apply (rule ccorres_return[where R'=UNIV], clarsimp, vcg)
              apply (rule_tac P="\<lambda>s. obj_at' (\<lambda>tcb. tcbPriority tcb = curPrio) curThread s
                                     \<and> curThread = ksCurThread s
                                     \<and> obj_at' (\<lambda>tcb. tcbPriority tcb = targetPrio) candidate s"
                       and P'=UNIV in ccorres_from_vcg)
              apply clarsimp
              apply (rule conseqPre, vcg)
              apply (clarsimp simp: return_def cur_tcb'_def rf_sr_ksCurThread)
              apply (drule (1) obj_at_cslift_tcb)+
              apply (clarsimp simp: typ_heap_simps ctcb_relation_def split: if_split)
              apply unat_arith
              apply clarsimp
             apply vcg
            apply ceqv
           (* fastfail calculation complete *)
           apply (rename_tac fastfail fastfail')
           apply (rule ccorres_pre_curDomain)
           (* rest of the calculation: fastfail \<and> \<not> highest *)
           apply (rule ccorres_rhs_assoc2)
           apply (rule_tac r'="\<lambda>hprio rv'. to_bool rv' = (fastfail \<and> \<not>hprio)" and xf'=ret__int_'
                    in ccorres_split_nothrow)
               apply (csymbr)
               apply (clarsimp simp: to_bool_def)
               apply (rule ccorres_Cond_rhs ; clarsimp)
                apply (rule ccorres_move_c_guard_tcb)
                apply (rule ccorres_add_return2)
                apply (ctac add: isHighestPrio_ccorres, clarsimp)
                  apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
                  apply (rule ccorres_return)
                  apply (rule conseqPre, vcg)
                  apply (clarsimp simp: to_bool_def)
                 apply (rule wp_post_taut)
                apply (vcg exspec=isHighestPrio_modifies)
               apply (rule_tac P=\<top> and P'="{s. ret__int_' s = 0}" in ccorres_from_vcg)
               apply clarsimp
               apply (rule conseqPre, vcg)
               apply (fastforce simp: isHighestPrio_def' gets_def return_def get_def
                                       Nondet_Monad.bind_def
                                split: prod.split)
              apply ceqv
             apply (clarsimp simp: to_bool_def)
             (* done with calculation of main acceptance criterion for candidate *)
             apply (rule ccorres_cond_seq)
             apply (rule ccorres_cond[where R=\<top>], blast)
              (* candidate is not the best one, enqueue and choose new thread *)
              apply (rule ccorres_rhs_assoc)+
              apply (ctac add: tcbSchedEnqueue_ccorres)
                apply clarsimp
                apply (ctac(no_simp) add: ccorres_setSchedulerAction)
                   apply (clarsimp simp: cscheduler_action_relation_def)
                  (* isolate haskell part before setting thread action *)
                  apply (simp add: scheduleChooseNewThread_def)
                  apply (rule ccorres_lhs_assoc)+
                  apply (rule ccorres_split_nothrow_dc)
                     apply (simp add: bind_assoc)
                     apply (ctac add: scheduleChooseNewThread_ccorres)
                    apply (ctac(no_simp) add: ccorres_setSchedulerAction)
                    apply (wpsimp simp: cscheduler_action_relation_def)+
                  apply (vcg exspec=scheduleChooseNewThread_modifies)
                 apply (wp add: setSchedulerAction_invs' setSchedulerAction_direct del: ssa_wp)
                apply (clarsimp | vcg exspec=tcbSchedEnqueue_modifies | wp wp_post_taut)+
             (* secondary check, when on equal prio and ct was running, prefer ct *)
             apply (rule ccorres_rhs_assoc)
             apply (rule_tac xf'=ret__int_' and val="from_bool (runnable' \<noteq> 0 \<and> curPrio = targetPrio)"
                      and R="\<lambda>s. curThread = ksCurThread s
                                 \<and> obj_at' (\<lambda>tcb. tcbPriority tcb = curPrio) (ksCurThread s) s
                                 \<and> obj_at' (\<lambda>tcb. tcbPriority tcb = targetPrio) candidate s"
                      and R'=UNIV
                      in ccorres_symb_exec_r_known_rv)
                apply clarsimp
                apply (rule conseqPre, vcg)
                apply (clarsimp simp: cur_tcb'_def rf_sr_ksCurThread)

                apply (drule (1) obj_at_cslift_tcb)+
                apply (clarsimp simp: typ_heap_simps ctcb_relation_def split: if_split)
                apply (solves \<open>unat_arith, rule iffI; simp\<close>)
               apply ceqv
              apply clarsimp
              apply (rule ccorres_cond_seq)
              apply (rule ccorres_cond[where R=\<top>], blast)
               (* candidate does not beat running ct, append and choose new thread *)
               apply (rule ccorres_rhs_assoc)+
               apply (ctac add: tcbSchedAppend_ccorres)
                 apply clarsimp
                 apply (ctac(no_simp) add: ccorres_setSchedulerAction)
                    apply (clarsimp simp: cscheduler_action_relation_def)
                   (* isolate haskell part before setting thread action *)
                   apply (simp add: scheduleChooseNewThread_def)
                   apply (rule ccorres_lhs_assoc)+
                   apply (rule ccorres_split_nothrow_dc)
                      apply (simp add: bind_assoc)
                      apply (ctac add: scheduleChooseNewThread_ccorres)
                     apply (ctac(no_simp) add: ccorres_setSchedulerAction)
                     apply (wpsimp simp: cscheduler_action_relation_def)+
                   apply (vcg exspec=scheduleChooseNewThread_modifies)
                  apply (wp add: setSchedulerAction_invs' setSchedulerAction_direct del: ssa_wp)
                 apply (clarsimp | vcg exspec=tcbSchedAppend_modifies | wp wp_post_taut)+
              (* candidate is best, switch to it *)
              apply (ctac add: switchToThread_ccorres)
                apply clarsimp
                apply (ctac(no_simp) add: ccorres_setSchedulerAction)
                apply (clarsimp simp: cscheduler_action_relation_def)
               apply (wpsimp wp: wp_post_taut)
              apply (vcg exspec=switchToThread_modifies)
             apply clarsimp
             apply vcg
            apply clarsimp
            apply (strengthen invs'_invs_no_cicd')
            apply (wp | wp (once) hoare_drop_imp)+
           apply clarsimp
           apply (vcg exspec=isHighestPrio_modifies)
          apply clarsimp
          apply (wp (once) hoare_drop_imps)
           apply wp
          apply (strengthen strenghten_False_imp[where P="a = ResumeCurrentThread" for a])
          apply (clarsimp simp: conj_ac invs_valid_objs' cong: conj_cong)
          apply wp
         apply (clarsimp, vcg exspec=tcbSchedEnqueue_modifies)
        apply (clarsimp, vcg exspec=tcbSchedEnqueue_modifies)
       apply clarsimp
       apply (strengthen ko_at'_obj_at'_field)
       apply (clarsimp cong: imp_cong simp: ko_at'_obj_at'_field)
       apply wp
      apply clarsimp
      (* when runnable tcbSchedEnqueue curThread *)
      apply (rule_tac Q="\<lambda>rv s. invs' s \<and> ksCurThread s = curThread
                                \<and> ksSchedulerAction s = SwitchToThread candidate" in hoare_post_imp)
       apply (clarsimp simp: invs'_bitmapQ_no_L1_orphans invs_ksCurDomain_maxDomain')
       apply (fastforce dest: invs_sch_act_wf')

      apply wpsimp+
     apply (vcg exspec=tcbSchedEnqueue_modifies)
    apply wp
   apply vcg

  apply (clarsimp simp: tcb_at_invs' rf_sr_ksCurThread if_apply_def2 invs_valid_objs')
  apply (frule invs_sch_act_wf')
  apply (frule tcb_at_invs')
  apply (frule invs_pspace_aligned')
  apply (frule invs_pspace_distinct')
  apply (rule conjI)
   apply (clarsimp dest!: rf_sr_cscheduler_relation simp: cscheduler_action_relation_def)
  apply (rule conjI; clarsimp)
   apply (frule (1) obj_at_cslift_tcb)
   apply (clarsimp simp: cscheduler_action_relation_def typ_heap_simps
                  split: scheduler_action.splits)
  apply (frule (1) obj_at_cslift_tcb)
  apply (clarsimp dest!: rf_sr_cscheduler_relation invs_sch_act_wf'
                  simp: cscheduler_action_relation_def)
  apply (intro conjI impI allI; clarsimp simp: typ_heap_simps ctcb_relation_def)
     apply (fastforce simp: tcb_at_not_NULL tcb_at_1 dest: pred_tcb_at')+
  done *)

(* FIXME: move *)
lemma map_to_tcbs_upd:
  "map_to_tcbs ((ksPSpace s)(t \<mapsto> KOTCB tcb')) = (map_to_tcbs (ksPSpace s))(t \<mapsto> tcb')"
  apply (rule ext)
  apply (clarsimp simp: map_comp_def projectKOs split: option.splits if_splits)
  done

(* FIXME: move *)
lemma cep_relations_drop_fun_upd:
  "\<lbrakk> f x = Some v; tcbEPNext_C v' = tcbEPNext_C v; tcbEPPrev_C v' = tcbEPPrev_C v \<rbrakk>
      \<Longrightarrow> cendpoint_relation (f (x \<mapsto> v')) = cendpoint_relation f"
  "\<lbrakk> f x = Some v; tcbEPNext_C v' = tcbEPNext_C v; tcbEPPrev_C v' = tcbEPPrev_C v \<rbrakk>
      \<Longrightarrow> cnotification_relation (f (x \<mapsto> v')) = cnotification_relation f"
  by (intro ext cendpoint_relation_upd_tcb_no_queues[where thread=x]
                cnotification_relation_upd_tcb_no_queues[where thread=x]
          | simp split: if_split)+

end

end
