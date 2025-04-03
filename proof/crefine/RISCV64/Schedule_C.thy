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

(*FIXME: arch-split: move up?*)
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
  apply (clarsimp simp: isRunnable_def readRunnable_def simp flip: threadGet_def)
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
        apply (wpsimp wp: getSchedulable_wp)+
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
     (\<lambda>s. invs' s \<and> valid_idle' s \<and> ksSchedulerAction s = ChooseNewThread \<and> valid_domain_list' s)
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

crunch getSchedContext, isRoundRobin
 for (empty_fail) empty_fail[wp]

lemma refill_size_ccorres:
  "ccorres (\<lambda>rv rv'. rv = unat rv') ret__unsigned_long_'
     (sc_at' scPtr and valid_objs' and valid_refills' scPtr) \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> hs
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

lemma head_refill_overrun_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     (active_sc_at' scPtr and valid_objs' and no_0_obj')
     (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace> \<inter> \<lbrace>usage = \<acute>usage\<rbrace>) []
     (gets_the (headRefillOverrun scPtr usage))
     (Call head_refill_overrun_'proc)"
  supply sched_context_C_size[simp del] refill_C_size[simp del]
         Collect_const [simp del]
  apply (clarsimp simp: headRefillOverrun_def getRefillHead_def[symmetric])
  apply (cinit' lift: sc_' usage_' simp: max_minus_one_word64)
   apply (rule_tac xf'="\<lambda>s. h_val (hrs_mem (t_hrs_' (globals s))) (ret__ptr_to_struct_refill_C_' s)"
                in ccorres_split_nothrow)
       apply (rule ccorres_call)
          apply (rule refill_head_ccorres, clarsimp+)
      apply ceqv
     apply (rename_tac head head')
     apply (rule ccorres_Guard_Seq)
     apply csymbr
     apply csymbr
     apply (rule_tac P="rAmount head \<le> usage" in ccorres_cases)
      apply (rule ccorres_cond_seq)
      apply (rule ccorres_cond_true)
      apply (rule ccorres_rhs_assoc)
      apply (rule_tac val="usToTicks maxPeriodUs"
                  and xf'=ret__unsigned_longlong_'
                   in ccorres_symb_exec_r_known_rv[where R=\<top> and R'=UNIV])
         apply (rule conseqPre, vcg)
         apply (clarsimp simp: maxPeriodUs_def timer_defs unat_max_word)
        apply ceqv
       apply csymbr
       apply (fastforce intro: ccorres_return_C)
      apply vcg
     apply (rule ccorres_cond_seq)
     apply (rule ccorres_cond_false)
     apply ccorres_rewrite
     apply (fastforce intro: ccorres_return_C)
    apply wpsimp
   apply vcg
  apply (clarsimp simp: active_sc_at'_rewrite)
  apply (normalise_obj_at', rename_tac sc)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply clarsimp
  apply (frule (1) length_scRefills_bounded)
  apply (frule (1) obj_at_cslift_sc)
  apply (frule rf_sr_refill_buffer_relation)
  apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
    apply (fastforce simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                           opt_map_def opt_pred_def)
   apply fastforce
  apply (frule_tac n=0 in h_t_valid_refill; fastforce?)
    apply (fastforce simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                           opt_map_def opt_pred_def)
   apply fastforce
  apply (clarsimp simp: typ_heap_simps csched_context_relation_def crefill_relation_def
                        sc_ptr_to_crefill_ptr_def maxReleaseTime_def timer_defs unat_max_word
                        maxBound_word
                 split: if_splits)
  done

lemma refillPopHead_scPeriod[wp]:
  "refillPopHead scPtr' \<lbrace>obj_at' (\<lambda>sc. P (scPeriod sc)) scPtr\<rbrace>"
  unfolding refillPopHead_def
  apply (wpsimp wp: updateSchedContext_wp getRefillNext_wp)
  by (clarsimp simp: obj_at'_def opt_map_def objBits_simps ps_clear_upd split: if_splits)

crunch getRefillSize
  for (empty_fail) empty_fail[wp]

lemma getRefillSize_exs_valid[wp]:
  "\<lbrace>(=) s\<rbrace> getRefillSize scPtr \<lbrace>\<lambda>r. (=) s\<rbrace>"
  by (wpsimp simp: getRefillSize_def)

lemma refill_add_tail_ccorres:
  "ccorres dc xfdc
     invs'
     (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace> \<inter> {s'. crefill_relation new (refill_' s')}) []
     (refillAddTail scPtr new) (Call refill_add_tail_'proc)"
  supply sched_context_C_size[simp del] refill_C_size[simp del] len_bit0[simp del]

  unfolding refillAddTail_def K_bind_apply haskell_assert_def
  apply (rule ccorres_symb_exec_l'[rotated, OF _ stateAssert_sp]; (solves wpsimp)?)
  apply (rule ccorres_symb_exec_l'[rotated, OF _ getRefillSize_sp]; (solves wpsimp)?)
  apply (rule ccorres_symb_exec_l'[rotated, OF _ get_sc_sp']; (solves wpsimp)?)
  apply (rule ccorres_symb_exec_l'[rotated, OF _ assert_sp]; (solves wpsimp)?)

  apply (cinit' lift: sc_' refill_' simp: updateRefillIndex_def)
   apply (rule ccorres_move_c_guard_sc)
   apply (ctac add: refill_next_ccorres)
     apply (rule ccorres_move_c_guard_sc)
     apply clarsimp
     apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
         apply (rule_tac P=\<top> in updateSchedContext_ccorres_lemma2)
           apply vcg
          apply fastforce
         apply clarsimp
         apply (rule_tac sc'="scRefillTail_C_update (\<lambda>_. new_tail) sc'"
                      in rf_sr_sc_update_no_refill_buffer_update2;
                fastforce?)
           apply (clarsimp simp: typ_heap_simps')
          apply (clarsimp simp: csched_context_relation_def)
         apply (fastforce intro: refill_buffer_relation_sc_no_refills_update)
        apply ceqv
       apply (rule_tac P="\<lambda>sc. scRefillTail sc = unat new_tail"
                   and P'="active_sc_at' scPtr and invs'"
                    in updateSchedContext_ccorres_lemma3)
         apply vcg
        apply fastforce
       apply normalise_obj_at'
       apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
       apply (intro conjI)
          apply (fastforce dest: sc_at_h_t_valid[rotated])
         apply (rule disjCI2)
         apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
          apply (fastforce intro: sc_at_array_assertion'
                            simp: valid_sched_context'_def MIN_REFILLS_def)
         apply (clarsimp simp: typ_heap_simps valid_sched_context'_def obj_at_simps
                               active_sc_at'_def csched_context_relation_def)
        apply (frule rf_sr_refill_buffer_relation)
        apply (frule_tac n="scRefillTail sc" in h_t_valid_refill; fastforce?)
          apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_def)
         apply fastforce
        apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps csched_context_relation_def)
       apply (clarsimp simp: ret__ptr_to_struct_refill_C_'_update_rf_sr_helper
                       cong: StateSpace.state.fold_congs)
       apply (rule_tac old_sc=sc and n="scRefillTail sc" and refill=new and refill'=refill
                    in rf_sr_refill_update2;
              fastforce?)
          apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_def)
         apply (fastforce simp: sched_context.expand)
        apply (clarsimp simp: typ_heap_simps sc_ptr_to_crefill_ptr_def csched_context_relation_def)
       apply (clarsimp simp: csched_context_relation_def)
      apply ((rule hoare_vcg_conj_lift
              | wpsimp wp: updateSchedContext_active_sc_at' updateSchedContext_refills_invs'
              | wpsimp wp: updateSchedContext_wp)+)[1]
     apply vcg
    apply (wpsimp wp: getRefillNext_wp)
   apply vcg
  apply normalise_obj_at'
  apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
  apply (elim conjE)
  apply (frule (1) length_scRefills_bounded)
  apply (intro conjI)
       apply fastforce
      apply (clarsimp simp: valid_sched_context'_def word_bits_len_of refillSizeBytes_def)
     apply (fastforce simp: obj_at'_def objBits_simps opt_map_def ps_clear_def)
    apply (fastforce simp: valid_sched_context'_def refillNext_def refillSize_def split: if_splits)
   apply (clarsimp simp: valid_sched_context_size'_def)
  apply (fastforce dest: obj_at_cslift_sc simp: csched_context_relation_def typ_heap_simps)
  done

lemma schedule_used_ccorres:
  "ccorres dc xfdc
     (active_sc_at' scPtr and invs')
     (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace> \<inter> \<lbrace>crefill_relation new \<acute>new\<rbrace>) hs
     (scheduleUsed scPtr new) (Call schedule_used_'proc)"
  (is "ccorres _ _ ?abs _ _ _ _")
  supply sched_context_C_size[simp del] refill_C_size[simp del]
  unfolding scheduleUsed_def haskell_assert_def
  apply (rule ccorres_symb_exec_l'[OF _ _ scActive_sp]; (solves wpsimp)?)
  apply (rule ccorres_symb_exec_l'[OF _ _ assert_sp]; (solves wpsimp)?)
  apply (cinit' lift: sc_' new_')
   apply (rule_tac xf'="\<lambda>s. h_val (hrs_mem (t_hrs_' (globals s))) (ret__ptr_to_struct_refill_C_' s)"
                in ccorres_split_nothrow_call)
          apply (fastforce intro: refill_tail_ccorres, fastforce+)
      apply ceqv
     apply (rule ccorres_Guard_Seq)
     apply csymbr
     apply (rule ccorres_cond[where R=\<top>])
       apply (clarsimp simp: crefill_relation_def)
      apply (clarsimp simp: setRefillTl_def updateRefillTl_def)
      apply (rule updateSchedContext_ccorres_lemma3[
                    where P="\<lambda>sc. scRefillTail sc < length (scRefills sc)" and P'="?abs"])
        apply vcg
       apply fastforce
      apply clarsimp
      apply (rename_tac sc sc')
      apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
      apply (frule rf_sr_refill_buffer_relation)
      apply (frule_tac n="scRefillTail sc" in h_t_valid_refill, fastforce+)
      apply (intro conjI)
         apply (clarsimp simp: typ_heap_simps)
        apply (rule disjCI2)
        apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
         apply (fastforce intro: sc_at_array_assertion')
        apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
       apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps csched_context_relation_def)
      apply (clarsimp simp: crefill_relation_def csched_context_relation_def)
      apply (frule rf_sr_refill_buffer_relation)
      apply (frule h_t_valid_clift_Some_iff[THEN iffD1])
      apply (clarsimp cong: StateSpace.state.fold_congs)
      apply (rule_tac old_sc=sc and n="scRefillTail sc"
                      and fa="rAmount_update (\<lambda>_. rAmount rv + rAmount new)"
                       in rf_sr_refill_update2; fastforce?)
         apply (fastforce simp: sched_context.expand)
        apply (clarsimp simp: typ_heap_simps)
        apply (fastforce simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def crefill_relation_def)
       apply (fastforce simp: csched_context_relation_def)
      apply (fastforce dest: crefill_relationD
                       simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def crefill_relation_def)
     apply (ctac add: refill_full_ccorres)
       apply (rule ccorres_cond[where R=\<top>])
         apply(clarsimp simp: to_bool_def)
        apply (ctac add: refill_add_tail_ccorres)
       apply (rule ccorres_rhs_assoc)
       apply (rule ccorres_split_nothrow)
           apply (clarsimp simp: setRefillTl_def updateRefillTl_def)
           apply (rule updateSchedContext_ccorres_lemma3
                        [where P="\<lambda>sc. scRefillTail sc < length (scRefills sc)" and P'="?abs"])
             apply vcg
            apply fastforce
           apply clarsimp
           apply (rename_tac sc sc')
           apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
           apply (frule rf_sr_refill_buffer_relation)
           apply (frule_tac n="scRefillTail sc" in h_t_valid_refill, fastforce+)
           apply (intro conjI)
              apply (clarsimp simp: typ_heap_simps)
             apply (rule disjCI2)
             apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
              apply (fastforce intro: sc_at_array_assertion')
             apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
            apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps csched_context_relation_def)
           apply (clarsimp simp: crefill_relation_def csched_context_relation_def)
           apply (frule rf_sr_refill_buffer_relation)
           apply (frule h_t_valid_clift_Some_iff[THEN iffD1])
           apply (clarsimp cong: StateSpace.state.fold_congs)
           apply (rule_tac old_sc=sc and n="scRefillTail sc"
                           and fa="rTime_update (\<lambda>_. rTime new - rAmount rv)"
                            in rf_sr_refill_update2; fastforce?)
              apply (fastforce simp: sched_context.expand)
             apply (clarsimp simp: typ_heap_simps)
             apply (fastforce simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def crefill_relation_def)
            apply (fastforce simp: csched_context_relation_def)
           apply (fastforce dest: crefill_relationD
                            simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def crefill_relation_def)
          apply ceqv
         apply (clarsimp simp: setRefillTl_def updateRefillTl_def)
         apply (rule updateSchedContext_ccorres_lemma3
                      [where P="\<lambda>sc. scRefillTail sc < length (scRefills sc)" and P'="?abs"])
           apply vcg
          apply fastforce
         apply clarsimp
         apply (rename_tac sc sc')
         apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
         apply (frule rf_sr_refill_buffer_relation)
         apply (frule_tac n="scRefillTail sc" in h_t_valid_refill, fastforce+)
         apply (intro conjI)
            apply (clarsimp simp: typ_heap_simps)
           apply (rule disjCI2)
           apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
            apply (fastforce intro: sc_at_array_assertion')
           apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
          apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps csched_context_relation_def)
         apply (clarsimp simp: crefill_relation_def csched_context_relation_def)
         apply (frule rf_sr_refill_buffer_relation)
         apply (frule h_t_valid_clift_Some_iff[THEN iffD1])
         apply (clarsimp cong: StateSpace.state.fold_congs)
         apply (rule_tac old_sc=sc and n="scRefillTail sc"
                         and fa="rAmount_update (\<lambda>_. rAmount rv + rAmount new)"
                          in rf_sr_refill_update2; fastforce?)
            apply (fastforce simp: sched_context.expand)
           apply (clarsimp simp: typ_heap_simps)
           apply (fastforce simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def crefill_relation_def)
          apply (fastforce simp: csched_context_relation_def)
         apply (fastforce dest: crefill_relationD
                          simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def crefill_relation_def)
        apply (rule_tac Q'="\<lambda>_. ?abs and active_sc_at' scPtr" in hoare_post_imp)
         apply (clarsimp simp: active_sc_at'_def)
         apply normalise_obj_at'
         apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
         apply (clarsimp simp: valid_sched_context'_def)
        apply (wpsimp wp: updateRefillHd_valid_objs')
       apply vcg
      apply (wpsimp wp: getRefillFull_wp)
     apply vcg
    apply (wpsimp wp: getRefillTail_wp)
   apply vcg
  apply (normalise_obj_at', rename_tac sc)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
  apply clarsimp
  apply (frule (1) length_scRefills_bounded)
  apply (frule (1) obj_at_cslift_sc)
  apply (frule rf_sr_refill_buffer_relation)
  apply (frule_tac n="scRefillTail sc" in h_t_valid_refill; fastforce?)
    apply (clarsimp simp: valid_sched_context'_def)
   apply fastforce
  apply (fastforce simp: crefill_relation_def typ_heap_simps csched_context_relation_def
                         sc_ptr_to_crefill_ptr_def valid_sched_context'_def active_sc_at'_rewrite
                  intro: valid_objs'_valid_refills')
  done

lemma charge_entire_head_refill_ccorres:
  "ccorres (=) ret__unsigned_longlong_'
     (active_sc_at' scPtr and invs')
     (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace> \<inter> \<lbrace>\<acute>usage = usage\<rbrace>) []
     (chargeEntireHeadRefill scPtr usage) (Call charge_entire_head_refill_'proc)"
  (is "ccorres _ _ ?abs _ _ _ _")
  supply sched_context_C_size[simp del] refill_C_size[simp del]
         Collect_const [simp del]
  apply (cinit lift: sc_' usage_')
   apply (rule_tac xf'="\<lambda>s. h_val (hrs_mem (t_hrs_' (globals s))) (ret__ptr_to_struct_refill_C_' s)"
                in ccorres_split_nothrow)
       apply (rule ccorres_call)
          apply (rule refill_head_ccorres)
         apply clarsimp
        apply clarsimp
       apply clarsimp
      apply ceqv
     apply (rename_tac head head')
     apply (rule ccorres_Guard_Seq)
     apply csymbr
     apply (rule ccorres_pre_getObject_sc, rename_tac abs_sc)
     apply (ctac add: refill_single_ccorres)
       apply (clarsimp simp: if_to_top_of_bind)
       apply (rule ccorres_cond_seq)
       apply (rule ccorres_cond[where R=\<top>])
         apply (fastforce simp: to_bool_def)
        apply (rule ccorres_split_nothrow)
            apply (clarsimp simp: setRefillHd_def updateRefillHd_def)
            apply (rule_tac P="\<lambda>sc. scRefillHead sc < length (scRefills sc)
                                    \<and> scPeriod sc = scPeriod abs_sc"
                         in updateSchedContext_ccorres_lemma3[where P'="?abs"])
              apply vcg
             apply fastforce
            apply clarsimp
            apply (rename_tac sc sc')
            apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
            apply (frule rf_sr_refill_buffer_relation)
            apply (frule_tac n="scRefillHead sc" in h_t_valid_refill, fastforce+)
            apply (intro conjI)
                apply (clarsimp simp: typ_heap_simps)
               apply (rule disjCI2)
               apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
                apply (fastforce intro: sc_at_array_assertion')
               apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
              apply (clarsimp simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def csched_context_relation_def)
             apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
            apply normalise_obj_at'
            apply (clarsimp simp: crefill_relation_def csched_context_relation_def)
            apply (frule rf_sr_refill_buffer_relation)
            apply (frule h_t_valid_clift_Some_iff[THEN iffD1])
            apply (clarsimp cong: StateSpace.state.fold_congs)
            apply (rule_tac old_sc=sc and n="scRefillHead sc"
                            and fa="rTime_update (\<lambda>_. rTime head + scPeriod sc)"
                             in rf_sr_refill_update2; fastforce?)
               apply (fastforce simp: sched_context.expand)
              apply (clarsimp simp: typ_heap_simps)
              apply (fastforce simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def crefill_relation_def)
             apply (fastforce simp: csched_context_relation_def)
            apply normalise_obj_at'
            apply (fastforce dest: crefill_relationD
                             simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def crefill_relation_def)
           apply ceqv
          apply (fastforce intro: ccorres_return_C)
         apply wpsimp
        apply vcg
       apply (clarsimp simp: bind_assoc)
       apply (rule ccorres_rhs_assoc)+
       apply (ctac add: refill_pop_head_ccorres)
         apply (rule ccorres_move_c_guard_sc)
         apply (rule_tac val="refill_C (rTime rv + scPeriod abs_sc) (rAmount rv)"
                     and xf'=old_head_'
                     and R="obj_at' (\<lambda>sc. scPeriod sc = scPeriod abs_sc) scPtr"
                      in ccorres_symb_exec_r_known_rv[where R'=UNIV])
            apply (rule conseqPre, vcg)
            apply normalise_obj_at'
            apply (frule (1) obj_at_cslift_sc)
            apply (clarsimp simp: crefill_relation_def typ_heap_simps csched_context_relation_def)
            apply (metis rTime_C_update.simps refill_C_idupdates(1))
           apply ceqv
          apply (ctac add: schedule_used_ccorres)
            apply (fastforce intro: ccorres_return_C)
           apply wpsimp
          apply (vcg exspec=schedule_used_modifies)
         apply vcg
        apply wpsimp
       apply (vcg exspec=refill_pop_head_modifies)
      apply (wpsimp simp: refillSingle_def)
     apply (vcg exspec=refill_single_modifies)
    apply wpsimp
   apply vcg
  apply (clarsimp simp: active_sc_at'_rewrite)
  apply (normalise_obj_at', rename_tac sc)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
  apply clarsimp
  apply (frule (1) length_scRefills_bounded)
  apply (frule (1) obj_at_cslift_sc)
  apply (frule rf_sr_refill_buffer_relation)
  apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
    apply (fastforce simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                           opt_map_def opt_pred_def)
   apply fastforce
  apply (frule_tac n=0 in h_t_valid_refill; fastforce?)
    apply (fastforce simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                           opt_map_def opt_pred_def)
   apply fastforce
  apply (auto simp: typ_heap_simps csched_context_relation_def crefill_relation_def
                    sc_ptr_to_crefill_ptr_def is_active_sc'_def obj_at'_def opt_pred_def opt_map_def
                    valid_sched_context'_def)
  done

lemma no_ofail_headRefillOverrun[wp]:
  "no_ofail (valid_objs' and active_sc_at' scPtr) (headRefillOverrun scPtr usage)"
  unfolding headRefillOverrun_def
  by wpsimp

lemma no_ofail_readRefillFull[wp]:
  "no_ofail (sc_at' scPtr) (readRefillFull scPtr)"
  unfolding readRefillFull_def
  by (wpsimp wp: no_ofail_readSchedContext)

lemmas no_fail_getRefillFull[wp] =
  no_ofail_gets_the[OF no_ofail_readRefillFull, simplified getRefillFull_def[symmetric]]

lemma no_ofail_readRefillTail[wp]:
  "no_ofail (valid_objs' and active_sc_at' scPtr) (readRefillTail scPtr)"
  unfolding readRefillTail_def ohaskell_state_assert_def
  by (wpsimp wp: no_ofail_readSchedContext simp: active_sc_at'_rewrite)

lemmas no_fail_getRefillTail[wp] =
  no_ofail_gets_the[OF no_ofail_readRefillTail, simplified getRefillTail_def[symmetric]]

lemma readRefillSingle_wp[wp]:
  "\<lblot>\<lambda>s. \<forall>sc. scs_of' s scPtr = Some sc \<longrightarrow> Q (scRefillHead sc = scRefillTail sc) s\<rblot>
   readRefillSingle scPtr
   \<lblot>Q\<rblot>"
  unfolding readRefillTail_def readSchedContext_def
  apply (wpsimp wp: set_sc'.readObject_wp)
  apply (clarsimp simp: opt_map_def obj_at'_def)
  done

lemmas refillSingle_wp[wp] =
  ovalid_gets_the[OF readRefillSingle_wp, simplified refillSingle_def[symmetric]]

lemmas no_fail_refillSingle[wp] =
  no_ofail_gets_the[OF no_ofail_readRefillSingle, simplified refillSingle_def[symmetric]]

lemma no_fail_updateRefillTl[wp]:
  "no_fail (sc_at' scPtr) (updateRefillTl scPtr f)"
  unfolding updateRefillTl_def
  apply wpsimp
  by (clarsimp simp: opt_pred_def opt_map_def obj_at'_def objBits_simps)

lemma no_fail_updateRefillIndex[wp]:
  "no_fail (sc_at' scPtr) (updateRefillIndex scPtr f idx)"
  unfolding updateRefillIndex_def
  apply wpsimp
  by (clarsimp simp: opt_pred_def opt_map_def obj_at'_def objBits_simps)

lemma no_fail_chargeEntireHeadRefill:
  "no_fail (active_sc_at' scPtr and valid_objs') (chargeEntireHeadRefill scPtr usage)"
  unfolding chargeEntireHeadRefill_def scheduleUsed_def refillAddTail_def
  apply (wpsimp wp: getRefillNext_wp getRefillSize_wp getRefillFull_wp no_fail_stateAssert)
          apply (rule_tac Q'="\<lambda>_. active_sc_at' scPtr and valid_objs'" in hoare_post_imp)
           apply (clarsimp simp: active_sc_at'_rewrite)
           apply normalise_obj_at'
           apply (frule (1) sc_ko_at_valid_objs_valid_sc')
           apply (clarsimp simp: opt_pred_def opt_map_def obj_at'_def objBits_simps
                                 valid_sched_context'_def is_active_sc'_def active_sc_at'_rewrite
                          split: if_splits)
          apply wpsimp+
  apply (clarsimp simp: active_sc_at'_rewrite split: if_splits)
  done

crunch chargeEntireHeadRefill
  for invs'[wp]: invs'
  (wp: crunch_wps)

lemma handle_overrun_ccorres:
  "ccorres (=) ret__unsigned_longlong_'
     (active_sc_at' scPtr and invs') (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace> \<inter> \<lbrace>\<acute>usage = usage\<rbrace>) hs
     (handleOverrun scPtr usage) (Call handle_overrun_'proc)"
  supply sched_context_C_size[simp del] refill_C_size[simp del]
         Collect_const [simp del]
  apply (cinit lift: sc_' usage_' simp: runReaderT_def whileAnno_def)
   apply (rule ccorres_symb_exec_r)
     apply (rule ccorres_add_return2)
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_split_nothrow_novcg)
         apply (rule_tac rrel="(=)" and xf="current_usage_'"
                     and G="\<lambda>_. active_sc_at' scPtr and invs'"
                      in ccorres_While'[where G'=UNIV])
              apply (rule ccorres_guard_imp)
                apply (ctac add: charge_entire_head_refill_ccorres)
               apply fastforce
              apply fastforce
             apply (rule ccorres_guard_imp)
               apply (ctac add: head_refill_overrun_ccorres)
              apply fastforce
             apply fastforce
            apply wpsimp
           apply wpsimp
          apply (rule conseqPre)
           apply clarsimp
           apply (rule_tac s=s and xf=current_usage_' in ccorres_to_vcg_Normal)
            apply (fastforce intro: ccorres_call[OF charge_entire_head_refill_ccorres])
           apply (wpsimp wp: no_fail_chargeEntireHeadRefill)
          apply fastforce
         apply (rule conseqPre, vcg)
         apply (clarsimp simp: active_sc_at'_rewrite)
         apply normalise_obj_at'
         apply (rename_tac sc)
         apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
         apply (frule rf_sr_refill_buffer_relation)
         apply (frule_tac n="scRefillHead sc" in h_t_valid_refill, fastforce+)
           apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                                 opt_pred_def opt_map_def
                          split: option.splits)
          apply fastforce
         apply (frule (1) obj_at_cslift_sc)
         apply (intro conjI)
            apply (clarsimp simp: typ_heap_simps)
           apply (rule disjCI2)
           apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
            apply (fastforce intro: sc_at_array_assertion'
                              simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                                    opt_pred_def opt_map_def
                             split: option.splits)
           apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                                 opt_pred_def opt_map_def typ_heap_simps csched_context_relation_def)
          apply (clarsimp simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def csched_context_relation_def)
         apply (clarsimp simp: timer_defs unat_max_word)
        apply ceqv
       apply (fastforce intro: ccorres_return_C')
      apply wpsimp
     apply (clarsimp simp: guard_is_UNIV_def)
    apply vcg
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply fastforce
  done

lemma head_refill_insufficient_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     (active_sc_at' scPtr and valid_objs' and no_0_obj')
     \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (gets_the (refillHdInsufficient scPtr ))
     (Call head_refill_insufficient_'proc)"
  supply sched_context_C_size[simp del] refill_C_size[simp del]
         Collect_const [simp del]
  unfolding refillHdInsufficient_def
  apply (cinit' lift: sc_' simp: getRefillHead_def[symmetric])
   apply (rule_tac xf'="\<lambda>s. h_val (hrs_mem (t_hrs_' (globals s))) (ret__ptr_to_struct_refill_C_' s)"
                in ccorres_split_nothrow)
       apply (fastforce intro: ccorres_call[OF refill_head_ccorres])
      apply ceqv
     apply csymbr
     apply (rule ccorres_Guard)
     apply (fastforce intro: ccorres_return_C)
    apply wpsimp
   apply vcg
  apply (clarsimp simp: active_sc_at'_rewrite)
  apply (normalise_obj_at', rename_tac sc)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply clarsimp
  apply (frule (1) length_scRefills_bounded)
  apply (frule (1) obj_at_cslift_sc)
  apply (frule rf_sr_refill_buffer_relation)
  apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
    apply (fastforce simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                           opt_map_def opt_pred_def)
   apply fastforce
  apply (frule_tac n="0" in h_t_valid_refill; fastforce?)
    apply (fastforce simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                           opt_map_def opt_pred_def)
   apply fastforce
 apply (clarsimp simp: to_bool_def typ_heap_simps crefill_relation_def minBudget_def
                       h_val_field_from_bytes' sc_ptr_to_crefill_ptr_def
                       csched_context_relation_def
                split: if_splits)
  done

lemma merge_nonoverlapping_head_refill_ccorres:
  "ccorres dc xfdc
     (active_sc_at' scPtr and valid_objs' and no_0_obj'
      and pspace_aligned' and pspace_distinct' and pspace_bounded')
     \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> hs
     (mergeNonoverlappingHeadRefill scPtr)  (Call merge_nonoverlapping_head_refill_'proc)"
  (is "ccorres _ _ ?abs _ _ _ _")
  supply sched_context_C_size[simp del] refill_C_size[simp del]
  apply (cinit lift: sc_')
   apply (ctac add: refill_pop_head_ccorres)
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_split_nothrow)
         apply (clarsimp simp: setRefillHd_def updateRefillHd_def)
         apply (rule updateSchedContext_ccorres_lemma3[
                       where P="\<lambda>sc. scRefillHead sc < length (scRefills sc)" and P'="?abs"])
           apply vcg
          apply fastforce
         apply clarsimp
         apply (rename_tac sc sc')
         apply (frule (1) sc_ko_at_valid_objs_valid_sc')
         apply (frule rf_sr_refill_buffer_relation)
         apply (frule_tac n="scRefillHead sc" in h_t_valid_refill, fastforce+)
         apply (intro conjI)
              apply (clarsimp simp: typ_heap_simps)
             apply (rule disjCI2)
             apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
              apply (fastforce intro: sc_at_array_assertion')
             apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
            apply (clarsimp simp: typ_heap_simps)
           apply (rule disjCI2)
           apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
            apply (fastforce intro: sc_at_array_assertion')
           apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
          apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps csched_context_relation_def)
         apply (clarsimp simp: crefill_relation_def csched_context_relation_def)
         apply (frule rf_sr_refill_buffer_relation)
         apply (frule h_t_valid_clift_Some_iff[THEN iffD1])
         apply (clarsimp cong: StateSpace.state.fold_congs)
         apply (rule_tac old_sc=sc and n="scRefillHead sc"
                         and fa="\<lambda>head. rAmount_update (\<lambda>_. rAmount head + rAmount rv) head"
                          in rf_sr_refill_update2; fastforce?)
            apply (fastforce simp: sched_context.expand)
           apply (clarsimp simp: typ_heap_simps)
           apply (fastforce simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def crefill_relation_def)
          apply (fastforce simp: csched_context_relation_def)
         apply (fastforce dest: crefill_relationD
                          simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def crefill_relation_def)
        apply ceqv
       apply (clarsimp simp: setRefillHd_def updateRefillHd_def)
       apply (rule updateSchedContext_ccorres_lemma3[
                     where P="\<lambda>sc. scRefillHead sc < length (scRefills sc)" and P'="?abs"])
         apply vcg
        apply fastforce
       apply clarsimp
       apply (rename_tac sc sc')
       apply (frule (1) sc_ko_at_valid_objs_valid_sc')
       apply (frule rf_sr_refill_buffer_relation)
       apply (frule_tac n="scRefillHead sc" in h_t_valid_refill, fastforce+)
       apply (intro conjI)
            apply (clarsimp simp: typ_heap_simps)
           apply (rule disjCI2)
           apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
            apply (fastforce intro: sc_at_array_assertion')
           apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
          apply (clarsimp simp: typ_heap_simps)
         apply (rule disjCI2)
         apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
          apply (fastforce intro: sc_at_array_assertion')
         apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
        apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps csched_context_relation_def)
       apply (clarsimp simp: crefill_relation_def csched_context_relation_def)
       apply (frule rf_sr_refill_buffer_relation)
       apply (frule h_t_valid_clift_Some_iff[THEN iffD1])
       apply (clarsimp cong: StateSpace.state.fold_congs)
       apply (rule_tac old_sc=sc and n="scRefillHead sc"
                       and fa="\<lambda>head. rTime_update (\<lambda>_. rTime head - rAmount rv) head"
                        in rf_sr_refill_update2; fastforce?)
          apply (fastforce simp: sched_context.expand)
         apply (clarsimp simp: typ_heap_simps)
         apply (fastforce simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def crefill_relation_def)
        apply (fastforce simp: csched_context_relation_def)
       apply (fastforce dest: crefill_relationD
                        simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def crefill_relation_def)
      apply (rule_tac Q'="\<lambda>_. ?abs and active_sc_at' scPtr" in hoare_post_imp)
       apply (clarsimp simp: active_sc_at'_def)
       apply normalise_obj_at'
       apply (frule (1) sc_ko_at_valid_objs_valid_sc')
       apply (clarsimp simp: valid_sched_context'_def)
      apply (wpsimp wp: updateRefillHd_valid_objs')
     apply vcg
    apply (rule_tac Q'="\<lambda>_. ?abs and active_sc_at' scPtr" in hoare_post_imp)
     apply (clarsimp simp: active_sc_at'_def)
     apply normalise_obj_at'
     apply (frule (1) sc_ko_at_valid_objs_valid_sc')
     apply (clarsimp simp: valid_sched_context'_def)
    apply (wpsimp wp: updateRefillHd_valid_objs')
   apply vcg
  apply clarsimp
  done

lemma no_ofail_refillHdInsufficient[wp]:
  "no_ofail (valid_objs' and active_sc_at' scPtr) (refillHdInsufficient scPtr)"
  unfolding refillHdInsufficient_def
  by wpsimp

crunch mergeNonoverlappingHeadRefill
  for invs'[wp]: invs'
  (wp: crunch_wps)

lemma handleOverrun_invs'[wp]:
  "\<lbrace>invs' and active_sc_at' scPtr\<rbrace> handleOverrun scPtr usage \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding handleOverrun_def
  by (wpsimp wp: valid_whileLoop[where I="\<lambda>_. invs' and active_sc_at' scPtr"]; fastforce?)

crunch mergeNonoverlappingHeadRefill
  for (no_fail) no_fail[wp]

lemma refill_budget_check_ccorres:
  "ccorres dc xfdc
     invs' \<lbrace>\<acute>usage = usage\<rbrace> hs
     (refillBudgetCheck usage) (Call refill_budget_check_'proc)"
  supply sched_context_C_size[simp del] refill_C_size[simp del]
         Collect_const [simp del]
  unfolding refillBudgetCheck_def haskell_assert_def K_bind_def
  apply (rule ccorres_symb_exec_l'[rotated, OF _ getCurSc_sp]; (solves wpsimp)?)
  apply (rule ccorres_symb_exec_l'[rotated, OF _ scActive_sp]; (solves wpsimp)?)
  apply (rule ccorres_symb_exec_l'[rotated, OF _ assert_sp]; (solves wpsimp)?)
  apply (rule ccorres_symb_exec_l'[rotated, OF _ isRoundRobin_sp]; (solves wpsimp)?)
  apply (rule ccorres_symb_exec_l'[rotated, OF _ assert_sp]; (solves wpsimp)?)
  apply (cinit' simp: max_minus_one_word64 runReaderT_def whileAnno_def)
   apply (rule_tac xf'=sc_'
               and val="Ptr scPtr"
               and R="\<lambda>s. scPtr = ksCurSc s"
                in ccorres_symb_exec_r_known_rv[where R'=UNIV])
      apply (rule conseqPre, vcg)
      apply (clarsimp simp: cstate_relation_def rf_sr_def Let_def)
     apply ceqv
    apply (ctac (no_vcg) add: handle_overrun_ccorres)
     apply (rule ccorres_rhs_assoc2)
     apply (rule_tac r'=crefill_relation and xf'="head_'" in ccorres_split_nothrow_novcg)
         apply (rule_tac P="active_sc_at' scPtr and invs'" and P'=UNIV in ccorres_from_vcg)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: active_sc_at'_rewrite)
         apply normalise_obj_at'
         apply (rename_tac sc)
         apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
         apply (frule rf_sr_refill_buffer_relation)
         apply (frule_tac n="scRefillHead sc" in h_t_valid_refill, fastforce+)
           apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                                 opt_pred_def opt_map_def
                          split: option.splits)
          apply fastforce
         apply (frule (1) obj_at_cslift_sc)
         apply (intro conjI)
            apply (clarsimp simp: typ_heap_simps)
           apply (rule disjCI2)
           apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
            apply (rule sc_at_array_assertion')
              apply fastforce
             apply fastforce
            apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                                 opt_pred_def opt_map_def)
           apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                                 opt_pred_def opt_map_def typ_heap_simps csched_context_relation_def)
          apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps csched_context_relation_def)
         apply (rename_tac s s' sc)
         apply (clarsimp simp: getRefillHead_def readRefillHead_def readRefillIndex_def
                               refillIndex_def readSchedContext_def getObject_def[symmetric]
                               bind_def return_def ohaskell_state_assert_def gets_the_ostate_assert
                               state_assert_def get_def assert_def fail_def
                        split: if_splits)
         apply (intro conjI impI)
           apply (rule_tac x="(sc, s)" in bexI[rotated])
            apply (fastforce intro: getObject_eq)
           apply (drule refill_buffer_relation_crefill_relation)
           apply (clarsimp simp: Let_def)
           apply (drule_tac x=scPtr in spec)
           apply (clarsimp simp: dyn_array_list_rel_pointwise obj_at'_def)
           apply (drule_tac x="scRefillHead sc" in spec)
           apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def opt_pred_def opt_map_def
                                 typ_heap_simps csched_context_relation_def refillHd_def
                                 sc_ptr_to_crefill_ptr_def)
          apply fastforce
         apply (clarsimp simp: active_sc_at'_rewrite)
        apply ceqv
       apply csymbr
       apply clarsimp
       apply (rename_tac head head')
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_split_nothrow_novcg[where r'=dc and xf'=xfdc])
           apply (rule_tac P="0 < usage" in ccorres_cases)
            apply clarsimp
            apply ccorres_rewrite
            apply (rule ccorres_rhs_assoc)
            apply (rule_tac val="usToTicks maxPeriodUs"
                        and xf'=ret__unsigned_longlong_'
                         in ccorres_symb_exec_r_known_rv[where R=\<top> and R'=UNIV])
               apply (rule conseqPre, vcg)
               apply (clarsimp simp: maxPeriodUs_def timer_defs unat_max_word)
              apply ceqv
             apply (rule_tac val="from_bool (rTime head < maxReleaseTime)"
                         and xf'=ret__int_'
                          in ccorres_symb_exec_r_known_rv[where R=\<top> and R'=UNIV])
                apply (rule conseqPre, vcg)
                apply (clarsimp simp: crefill_relation_def maxReleaseTime_def maxBound_word
                               split: if_splits)
               apply ceqv
              apply (clarsimp simp: when_def)
              apply (rule ccorres_cond[where R=\<top>])
                apply fastforce
               apply (rule ccorres_pre_getObject_sc, rename_tac sc)
               apply (rule ccorres_rhs_assoc)+
               apply (rule ccorres_move_c_guard_sc)
               apply (rule_tac val="refill_C (rTime head + scPeriod sc) usage"
                           and xf'=used___struct_refill_C_'
                           and R="obj_at' (\<lambda>sc'. scPeriod sc' = scPeriod sc) scPtr"
                            in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                  apply (rule conseqPre, vcg)
                  apply normalise_obj_at'
                  apply (frule (1) obj_at_cslift_sc)
                  apply (clarsimp simp: crefill_relation_def typ_heap_simps csched_context_relation_def)
                 apply ceqv
                apply (rule ccorres_rhs_assoc2)
                apply (rule ccorres_split_nothrow_novcg[where r'=dc and xf'=xfdc])
                    apply (clarsimp simp: setRefillHd_def updateRefillHd_def)
                    apply (rule_tac P'="sc_at' scPtr and invs'"
                                 in updateSchedContext_ccorres_lemma3[
                                      where P="\<lambda>sc. scRefillHead sc < length (scRefills sc)"])
                      apply vcg
                     apply fastforce
                    apply clarsimp
                    apply (rename_tac sc sc')
                    apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
                    apply (frule rf_sr_refill_buffer_relation)
                    apply (frule_tac n="scRefillHead sc" in h_t_valid_refill, fastforce+)
                    apply (intro conjI)
                       apply (clarsimp simp: typ_heap_simps)
                      apply (rule disjCI2)
                      apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
                       apply (fastforce intro: sc_at_array_assertion')
                      apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
                     apply (clarsimp simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def
                                           csched_context_relation_def)
                    apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
                    apply (clarsimp simp: crefill_relation_def csched_context_relation_def)
                    apply (frule rf_sr_refill_buffer_relation)
                    apply (frule h_t_valid_clift_Some_iff[THEN iffD1])
                    apply (clarsimp cong: StateSpace.state.fold_congs)
                    apply (rule_tac old_sc=sc and n="scRefillHead sc"
                                and fa="rAmount_update (\<lambda>_. rAmount head - usage)"
                                 in rf_sr_refill_update2; fastforce?)
                       apply (fastforce simp: sched_context.expand)
                      apply (clarsimp simp: typ_heap_simps)
                      apply (fastforce simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def)
                     apply (fastforce simp: csched_context_relation_def)
                    apply (fastforce dest: crefill_relationD
                                     simp: typ_heap_simps' crefill_relation_def)
                   apply ceqv
                  apply (rule ccorres_rhs_assoc2)
                  apply (rule ccorres_split_nothrow_novcg[where r'=dc and xf'=xfdc])
                      apply (clarsimp simp: setRefillHd_def updateRefillHd_def)
                      apply (rule_tac P'="sc_at' scPtr and invs'"
                                   in updateSchedContext_ccorres_lemma3[
                                        where P="\<lambda>sc. scRefillHead sc < length (scRefills sc)"])
                        apply vcg
                       apply fastforce
                      apply clarsimp
                      apply (rename_tac sc sc')
                      apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
                      apply (frule rf_sr_refill_buffer_relation)
                      apply (frule_tac n="scRefillHead sc" in h_t_valid_refill, fastforce+)
                      apply (intro conjI)
                         apply (clarsimp simp: typ_heap_simps)
                        apply (rule disjCI2)
                        apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
                         apply (fastforce intro: sc_at_array_assertion')
                        apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
                       apply (clarsimp simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def
                                             csched_context_relation_def)
                      apply (clarsimp simp: crefill_relation_def csched_context_relation_def)
                      apply (frule rf_sr_refill_buffer_relation)
                      apply (frule h_t_valid_clift_Some_iff[THEN iffD1])
                      apply (clarsimp cong: StateSpace.state.fold_congs)
                      apply (rule_tac old_sc=sc and n="scRefillHead sc"
                                  and fa="rTime_update (\<lambda>_. rTime head + usage)"
                                   in rf_sr_refill_update2; fastforce?)
                         apply (fastforce simp: sched_context.expand)
                        apply (clarsimp simp: typ_heap_simps)
                        apply (fastforce simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def)
                       apply (fastforce simp: csched_context_relation_def)
                      apply (fastforce dest: crefill_relationD
                                       simp: typ_heap_simps' crefill_relation_def)
                     apply ceqv
                    apply (ctac (no_vcg) add: schedule_used_ccorres)
                   apply (wpsimp wp: updateRefillHd_invs')
                  apply (clarsimp simp: guard_is_UNIV_def crefill_relation_def)
                 apply (clarsimp simp: guard_is_UNIV_def crefill_relation_def)
                 apply (rule_tac Q'="\<lambda>_. invs' and active_sc_at' scPtr" in hoare_post_imp)
                  apply (clarsimp simp: active_sc_at'_def)
                  apply normalise_obj_at'
                  apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
                  apply (clarsimp simp: valid_sched_context'_def)
                 apply (wpsimp wp: updateRefillHd_invs')
                apply (clarsimp simp: guard_is_UNIV_def crefill_relation_def)
               apply vcg
              apply (rule ccorres_return_Skip)
             apply vcg
            apply vcg
           apply clarsimp
           apply ccorres_rewrite
           apply (rule ccorres_cond_false)
           apply (rule ccorres_return_Skip)
          apply ceqv
         apply (rule ccorres_handlers_weaken)
         apply (clarsimp simp: headInsufficientLoop_def runReaderT_def)
         apply (rule_tac rrel=dc and xf=xfdc
                     and G="\<lambda>_. active_sc_at' scPtr and invs'"
                      in ccorres_While'[where G'=UNIV])
              apply (rule ccorres_guard_imp)
                apply (ctac add: merge_nonoverlapping_head_refill_ccorres)
               apply fastforce
              apply fastforce
             apply (rule ccorres_guard_imp)
               apply (ctac (no_vcg) add: head_refill_insufficient_ccorres)
              apply fastforce
             apply fastforce
            apply wpsimp
           apply wpsimp
          apply (rule conseqPre)
           apply clarsimp
           apply (rule_tac s=s and xf=xfdc in ccorres_to_vcg_Normal)
            apply (fastforce intro: ccorres_call[OF merge_nonoverlapping_head_refill_ccorres])
           apply (wpsimp wp: no_fail_mergeNonoverlappingHeadRefill)
          apply (fastforce simp: active_sc_at'_rewrite)
         apply (rule conseqPre, vcg)
         apply (clarsimp simp: active_sc_at'_rewrite)
         apply normalise_obj_at'
         apply (rename_tac sc)
         apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
         apply (frule rf_sr_refill_buffer_relation)
         apply (frule_tac n="scRefillHead sc" in h_t_valid_refill, fastforce+)
           apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                                 opt_pred_def opt_map_def
                          split: option.splits)
          apply fastforce
         apply (frule (1) obj_at_cslift_sc)
         apply (intro conjI)
           apply (clarsimp simp: typ_heap_simps)
          apply (rule disjCI2)
          apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
           apply (fastforce intro: sc_at_array_assertion'
                             simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                                   opt_pred_def opt_map_def
                            split: option.splits)
          apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                                opt_pred_def opt_map_def typ_heap_simps csched_context_relation_def)
         apply (clarsimp simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def csched_context_relation_def)
        apply (wpsimp wp: updateRefillHd_invs')
       apply (clarsimp simp: guard_is_UNIV_def)
      apply (rule_tac Q'="\<lambda>_. active_sc_at' scPtr and invs'" in hoare_post_imp)
       apply (clarsimp simp: active_sc_at'_rewrite split: if_splits)
       apply normalise_obj_at'
       apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
       apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                                 opt_pred_def opt_map_def)
      apply wpsimp
     apply (clarsimp simp: guard_is_UNIV_def timer_defs unat_max_word)
    apply (wpsimp wp: hoare_drop_imps)
   apply (vcg exspec=handle_overrun_modifies)
  apply (clarsimp simp: active_sc_at'_rewrite is_active_sc'_def obj_at'_def
                        opt_pred_def opt_map_def)
  done

lemma checkDomainTime_ccorres:
  "ccorres dc xfdc
     ((\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and valid_objs' and no_0_obj'
      and pspace_aligned' and pspace_distinct')
     UNIV hs
     checkDomainTime (Call checkDomainTime_'proc)"
  apply cinit
   apply (ctac (no_vcg) add: isCurDomainExpired_ccorres)
    apply (clarsimp simp: when_def)
    apply (rule ccorres_cond[where R=\<top>])
      apply (fastforce simp: to_bool_def)
     apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
         apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: setReprogramTimer_def rf_sr_def cstate_relation_def Let_def
                               modify_def get_def put_def bind_def carch_state_relation_def
                               cmachine_state_relation_def)
        apply ceqv
       apply (ctac add: rescheduleRequired_ccorres)
      apply wpsimp
     apply (clarsimp simp: guard_is_UNIV_def)
    apply (fastforce intro: ccorres_return_Skip)
   apply (wpsimp wp: hoare_drop_imps)
  apply (clarsimp simp: guard_is_UNIV_def)
  done

lemma rf_sr_ksIdleSC:
  "(s, s') \<in> rf_sr \<Longrightarrow> ksIdleSC_' (globals s') = Ptr (ksIdleSC s)"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)

lemma ccorres_pre_getIdleSC:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. ksIdleSC s = rv \<longrightarrow> P rv s))
                  {s. \<forall>rv. ksIdleSC_' (globals s) = Ptr rv \<longrightarrow> s \<in> P' rv }
                          hs (getIdleSC >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule getIdleSC_sp)
     apply (clarsimp simp: empty_fail_def getIdleSC_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply (clarsimp simp: rf_sr_ksIdleSC)
  done

crunch updateRefillHd, updateRefillTl, refillBudgetCheckRoundRobin, refillBudgetCheck
  for KsConsumedTime[wp]: "\<lambda>s. P (ksConsumedTime s)"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

lemma commitTime_ccorres:
  "ccorres dc xfdc invs' UNIV hs commitTime (Call commitTime_'proc)"
  (is "ccorres _ _ ?abs _ _ _ _")
  supply sched_context_C_size[simp del] refill_C_size[simp del]
         Collect_const [simp del]
  apply cinit
   apply (rule ccorres_pre_getCurSc)
   apply (ctac add: sc_active_ccorres)
     apply clarsimp
     apply (rename_tac active)
     apply (rule ccorres_pre_getIdleSC)
     apply (rule_tac xf'=xfdc and r'=dc in ccorres_split_nothrow_novcg)
         apply (clarsimp simp: when_def)
         apply (rule_tac R="\<lambda>s. idleSCPtr = ksIdleSC s \<and> scPtr = ksCurSc s" in ccorres_cond)
           apply clarsimp
           apply (frule rf_sr_ksIdleSC)
           apply (fastforce dest: rf_sr_ksCurSC simp: to_bool_def)
          apply (rule ccorres_pre_getConsumedTime, rename_tac consumed)
          apply (rule_tac xf'=xfdc and r'=dc in ccorres_split_nothrow_novcg)
              apply (rule_tac R="\<lambda>s. consumed = ksConsumedTime s" in ccorres_cond)
                apply (fastforce dest: rf_sr_ksConsumed)
               apply (clarsimp simp: ifM_def)
               apply (ctac add: isRoundRobin_ccorres)
                 apply (rule_tac R=\<top> in ccorres_cond)
                   apply (fastforce simp: to_bool_def)
                  apply (clarsimp simp: refillBudgetCheckRoundRobin_def)
                  apply (rule ccorres_pre_getCurSc, rename_tac scPtr')
                  apply (rule ccorres_rhs_assoc)
                  apply (rule ccorres_rhs_assoc)
                  apply (rule ccorres_split_nothrow_novcg[where r'=dc and xf'=xfdc])
                      apply (clarsimp simp: setRefillHd_def updateRefillHd_def)
                      apply (rule_tac P'="\<lambda>s. ?abs s \<and> active_sc_at' scPtr s \<and> scPtr = ksCurSc s
                                              \<and> scPtr = scPtr' \<and> consumed = ksConsumedTime s"
                                   in updateSchedContext_ccorres_lemma3
                                       [where P="\<lambda>sc. scRefillHead sc < length (scRefills sc)"])
                        apply vcg
                       apply fastforce
                      apply clarsimp
                      apply (rename_tac sc sc')
                      apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
                      apply (frule rf_sr_refill_buffer_relation)
                      apply (frule rf_sr_ksCurSC)
                      apply (frule_tac n="scRefillHead sc" in h_t_valid_refill, fastforce+)
                      apply (intro conjI)
                           apply (clarsimp dest!: rf_sr_ksCurSC simp: typ_heap_simps)
                          apply (rule disjCI2)
                          apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
                           apply (fastforce intro: sc_at_array_assertion')
                          apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
                         apply (clarsimp simp: typ_heap_simps)
                        apply (rule disjCI2)
                        apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
                         apply (fastforce intro: sc_at_array_assertion')
                        apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
                       apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps
                                             csched_context_relation_def)
                      apply (clarsimp simp: crefill_relation_def csched_context_relation_def)
                      apply (frule rf_sr_refill_buffer_relation)
                      apply (frule h_t_valid_clift_Some_iff[THEN iffD1])
                      apply normalise_obj_at'
                      apply (clarsimp cong: StateSpace.state.fold_congs)
                      apply (rule_tac old_sc=sc and n="scRefillHead sc"
                                  and fa="\<lambda>r. rAmount_update (\<lambda>_. rAmount r - ksConsumedTime s) r"
                                   in rf_sr_refill_update2; fastforce?)
                         apply (fastforce simp: sched_context.expand)
                        apply (clarsimp simp: typ_heap_simps)
                        apply (fastforce simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def
                                               crefill_relation_def)
                       apply (fastforce simp: csched_context_relation_def)
                      apply (fastforce dest: crefill_relationD rf_sr_ksConsumed
                                       simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def
                                             crefill_relation_def)
                     apply ceqv
                    apply (clarsimp simp: setRefillTl_def updateRefillTl_def)
                    apply (rule_tac P'="\<lambda>s. ?abs s \<and> active_sc_at' scPtr s \<and> scPtr = ksCurSc s
                                            \<and> scPtr = scPtr' \<and> consumed = ksConsumedTime s"
                                 in updateSchedContext_ccorres_lemma3
                                     [where P="\<lambda>sc. scRefillTail sc < length (scRefills sc)"])
                      apply vcg
                     apply fastforce
                    apply clarsimp
                    apply (rename_tac sc sc')
                    apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
                    apply (frule rf_sr_refill_buffer_relation)
                    apply (frule rf_sr_ksCurSC)
                    apply (frule_tac n="scRefillTail sc" in h_t_valid_refill, fastforce+)
                    apply (intro conjI)
                         apply (clarsimp dest!: rf_sr_ksCurSC simp: typ_heap_simps)
                        apply (rule disjCI2)
                        apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
                         apply (fastforce intro: sc_at_array_assertion')
                        apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
                       apply (clarsimp simp: typ_heap_simps)
                      apply (rule disjCI2)
                      apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
                       apply (fastforce intro: sc_at_array_assertion')
                      apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
                     apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps
                                           csched_context_relation_def)
                    apply (clarsimp simp: crefill_relation_def csched_context_relation_def)
                    apply (frule rf_sr_refill_buffer_relation)
                    apply (frule h_t_valid_clift_Some_iff[THEN iffD1])
                    apply normalise_obj_at'
                    apply (clarsimp cong: StateSpace.state.fold_congs)
                    apply (rule_tac old_sc=sc and n="scRefillTail sc"
                                and fa="\<lambda>r. rAmount_update (\<lambda>_. rAmount r + ksConsumedTime s) r"
                                 in rf_sr_refill_update2; fastforce?)
                       apply (fastforce simp: sched_context.expand)
                      apply (clarsimp simp: typ_heap_simps)
                      apply (fastforce simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def
                                             crefill_relation_def)
                     apply (fastforce simp: csched_context_relation_def)
                    apply (fastforce dest: crefill_relationD rf_sr_ksConsumed
                                     simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def
                                           crefill_relation_def)
                   apply (rule_tac Q'="\<lambda>_ s. ?abs s \<and> active_sc_at' scPtr s \<and> scPtr = ksCurSc s
                                             \<and> scPtr = scPtr' \<and> consumed = ksConsumedTime s"
                                in hoare_post_imp)
                    apply (clarsimp simp: active_sc_at'_def)
                    apply normalise_obj_at'
                    apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
                    apply (clarsimp simp: valid_sched_context'_def)
                   apply (wpsimp wp: updateRefillHd_invs')
                  apply (clarsimp simp: guard_is_UNIV_def)
                 apply (ctac add: refill_budget_check_ccorres)
                apply (wpsimp wp: isRoundRobin_wp)
               apply (vcg exspec=isRoundRobin_modifies)
              apply (fastforce intro: ccorres_return_Skip)
             apply ceqv
            apply (rule_tac P'="\<lambda>s. sc_at' scPtr s \<and> scPtr = ksCurSc s \<and> consumed = ksConsumedTime s"
                         in updateSchedContext_ccorres_lemma3[where P=\<top>])
              apply vcg
             apply simp
            subgoal
              by (fastforce dest: rf_sr_ksCurSC rf_sr_ksConsumed
                           intro: rf_sr_sc_update_no_refill_buffer_update2
                                  refill_buffer_relation_sc_no_refills_update
                            simp: typ_heap_simps' csched_context_relation_def option_to_ctcb_ptr_def)
           apply (wpsimp wp: isRoundRobin_wp)
          apply (clarsimp simp: guard_is_UNIV_def)
         apply (fastforce intro: ccorres_return_Skip)
        apply ceqv
       apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: setConsumedTime_def rf_sr_def cstate_relation_def Let_def
                             modify_def get_def put_def bind_def carch_state_relation_def
                             cmachine_state_relation_def)
      apply wpsimp
     apply (clarsimp simp: guard_is_UNIV_def)
    apply (wpsimp wp: scActive_wp)
   apply (vcg exspec=sc_active_modifies)
  apply clarsimp
  apply (intro conjI impI allI; clarsimp)
   apply (normalise_obj_at', rename_tac sc)
   apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
   apply (fastforce simp: valid_sched_context'_def)
  apply (fastforce simp: active_sc_at'_rewrite is_active_sc'_def opt_pred_def obj_at'_def opt_map_def)
  done

lemma rf_sr_ksReprogramTimer:
  "(s, s') \<in> rf_sr \<Longrightarrow> to_bool (ksReprogram_' (globals s')) = ksReprogramTimer s"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)

crunch commitTime, ifCondRefillUnblockCheck, setReprogramTimer
  for obj_at'_tcb[wp]: "\<lambda>s. obj_at' (P :: tcb \<Rightarrow> bool) tcbPtr s"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

crunch getReprogramTimer
  for (empty_fail) empty_fail[wp]

lemma switchSchedContext_ccorres:
  "ccorres dc xfdc invs' UNIV [] switchSchedContext (Call switchSchedContext_'proc)"
  supply Collect_const [simp del]
  apply cinit
   apply (rule ccorres_pre_getCurSc)
   apply (rule ccorres_pre_getCurThread, rename_tac ct)
   apply (rule ccorres_pre_threadGet, rename_tac ctscOpt)
   apply (rule ccorres_assert2)
   apply (clarsimp, rename_tac ctScPtr)
   apply (rule ccorres_Guard_Seq)
   apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
       apply (clarsimp simp: when_def)
       apply wpfix
       apply (rule_tac R="\<lambda>s. curScPtr = ksCurSc s \<and> ct = ksCurThread s
                              \<and> obj_at' (\<lambda>tcb. Some ctScPtr = tcbSchedContext tcb) ct s
                              \<and> valid_objs' s \<and> no_0_obj' s"
                    in ccorres_cond)
         apply normalise_obj_at'
         apply (frule rf_sr_ksCurSC)
         apply (frule rf_sr_ksCurThread)
         apply (frule (1) obj_at_cslift_tcb)
         apply (fastforce dest!: sym[where s="sched_context_Ptr ptr" for ptr]
                           simp: typ_heap_simps ctcb_relation_def option_to_ptr_def option_to_0_def
                          split: option.splits)
        apply (rule ccorres_rhs_assoc)
        apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
            apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply (clarsimp simp: setReprogramTimer_def rf_sr_def cstate_relation_def Let_def
                                  modify_def get_def put_def bind_def carch_state_relation_def
                                  cmachine_state_relation_def)
           apply ceqv
          apply (clarsimp simp: ifCondRefillUnblockCheck_def)
          apply (rule ccorres_pre_getObject_sc)
          apply (rule ccorres_pre_getCurSc)
          apply (rule ccorres_Guard_Seq)
          apply (rule_tac xf'=ret__unsigned_long_'
                      and val="from_bool (\<not> scSporadic sc)"
                      and R="\<lambda>s. curScPtr = ksCurSc s \<and> ct = ksCurThread s
                                 \<and> obj_at' (\<lambda>tcb. Some ctScPtr = tcbSchedContext tcb) ct s
                                 \<and> valid_objs' s \<and> no_0_obj' s
                                 \<and> ko_at' sc ctScPtr s"
                       in ccorres_symb_exec_r_known_rv[where R'=UNIV])
             apply (rule conseqPre, vcg)
             apply normalise_obj_at'
             apply (frule rf_sr_ksCurThread)
             apply (frule (1) obj_at_cslift_tcb)
             apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
             apply (prop_tac "sc_at' ctScPtr s")
              apply (clarsimp simp: valid_tcb'_def valid_bound_sc'_def valid_bound_obj'_def
                             split: option.splits)
             apply (frule (1) obj_at_cslift_sc)
             apply (clarsimp simp: typ_heap_simps valid_tcb'_def valid_bound_obj'_def
                                   ctcb_relation_def csched_context_relation_def to_bool_def
                            split: if_splits option.splits)
            apply ceqv
           apply (clarsimp simp: when_def)
           apply (rule ccorres_cond[where R=\<top>])
             apply fastforce
            apply (ctac add: refill_unblock_check_ccorres)
           apply (fastforce intro: ccorres_return_Skip)
          apply (vcg exspec=sc_constant_bandwidth_modifies)
         apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> ct = ksCurThread s \<and> curScPtr = ksCurSc s
                                   \<and> obj_at' (\<lambda>tcb. Some ctScPtr = tcbSchedContext tcb) ct s"
                      in hoare_post_imp)
          apply fastforce
         apply wpsimp
        apply vcg
       apply (fastforce intro: ccorres_return_Skip)
      apply ceqv
     apply (rule ccorres_symb_exec_l', rename_tac reprogram)
        apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
            apply (clarsimp simp: when_def)
            apply (rule_tac R="\<lambda>s. reprogram = ksReprogramTimer s" in ccorres_cond)
              apply (fastforce dest: rf_sr_ksReprogramTimer simp: to_bool_def)
             apply (ctac add: commitTime_ccorres)
            apply (fastforce intro: ccorres_return_Skip)
           apply ceqv
          apply clarsimp
          apply (rule_tac P="\<lambda>s. obj_at' (\<lambda>tcb. Some ctScPtr = tcbSchedContext tcb) ct s
                                 \<and> ct = ksCurThread s \<and> valid_objs' s \<and> no_0_obj' s"
                       in ccorres_from_vcg[where P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply normalise_obj_at'
          apply (frule rf_sr_ksCurSC)
          apply (frule (1) obj_at_cslift_tcb)
          apply (clarsimp simp: setCurSc_def rf_sr_def cstate_relation_def Let_def
                                modify_def get_def put_def bind_def carch_state_relation_def
                                cmachine_state_relation_def)
          subgoal
            by (clarsimp simp: typ_heap_simps ctcb_relation_def option_to_ptr_def option_to_0_def
                        split: option.splits)
         apply ((wpsimp wp: commitTime_invs' | strengthen invs_valid_objs' invs_no_0_obj')+)[1]
        apply (vcg exspec=commitTime_modifies)
       apply wpsimp
      apply wpsimp
     apply wpsimp
    apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> ct = ksCurThread s
                              \<and> obj_at' (\<lambda>tcb. Some ctScPtr = tcbSchedContext tcb) ct s"
                 in hoare_post_imp)
     apply (fastforce split: if_splits)
    apply wpsimp
   apply (vcg exspec=refill_unblock_check_modifies)
  apply (fastforce simp: typ_heap_simps ctcb_relation_def obj_at'_def )
  done

lemma ccorres_pre_getReleaseQueue:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows
    "ccorres r xf
       (\<lambda>s. \<forall>rv. ksReleaseQueue s = rv \<longrightarrow> P rv s)
       {s'. \<forall>rv s. (s, s') \<in> rf_sr \<and> ksReleaseQueue s = rv \<and> P rv s
                    \<and> ctcb_queue_relation rv (ksReleaseQueue_' (globals s'))
                   \<longrightarrow> s' \<in> P' rv} hs
       (getReleaseQueue >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule getReleaseQueue_sp)
     apply wpsimp
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  by fast

lemma scActive_exs_valid[wp]:
  "sc_at' scPtr s \<Longrightarrow> \<lbrace>(=) s\<rbrace> scActive scPtr \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  unfolding scActive_def
  apply wpsimp
  by (fastforce dest: no_ofailD[OF no_ofail_readScActive])

lemma release_q_non_empty_and_ready_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     (valid_objs' and no_0_obj' and pspace_aligned' and pspace_distinct'
      and (\<lambda>s. \<forall>head. tcbQueueHead (ksReleaseQueue s) = Some head \<longrightarrow> active_sc_tcb_at' head s))
     UNIV []
     (gets_the releaseQNonEmptyAndReady)
     (Call release_q_non_empty_and_ready_'proc)"
  apply cinit'
   apply (simp add: releaseQNonEmptyAndReady_def gets_the_if_distrib readReleaseQueue_def
                    gets_the_ogets
              flip: getReleaseQueue_def)
   apply (rule ccorres_pre_getReleaseQueue)
   apply (rename_tac releaseQueue)
   apply (rule_tac xf'=ret__int_'
               and val="from_bool (tcbQueueHead releaseQueue \<noteq> None)"
               and R="\<lambda>s. ksReleaseQueue s = releaseQueue
                          \<and> (\<forall>head. tcbQueueHead (ksReleaseQueue s) = Some head \<longrightarrow> tcb_at' head s)"
               and R'=UNIV
                in ccorres_symb_exec_r_known_rv)
      apply (rule conseqPre, vcg)
      apply (fastforce dest: tcb_at_not_NULL rf_sr_ctcb_queue_relation_release_queue
                       simp: ctcb_queue_relation_def option_to_ctcb_ptr_def
                      split: option.splits)
     apply ceqv
    apply (subst if_swap)
    apply (rule ccorres_cond_seq)
    apply ccorres_rewrite
    apply (rule_tac Q="\<lambda>s. ksReleaseQueue s = releaseQueue" in ccorres_cond_both'[where Q'=\<top>])
      apply fastforce
     apply (rule ccorres_rhs_assoc)+
     apply (clarsimp simp: gets_the_obind)
     apply (rule ccorres_Guard_Seq)
     apply (simp flip: threadGet_def refillReady_def)
     apply (drule Some_to_the)
     apply clarsimp
     apply (rule ccorres_pre_threadGet)
     apply (simp add: gets_the_ohaskell_assert)
     apply (rule ccorres_assert2)
     apply (simp flip: scActive_def)
     apply (rule ccorres_symb_exec_l')
        apply (rule ccorres_assert2_abs)
        apply (rule ccorres_add_return2)
        apply (ctac add: refill_ready_ccorres)
          apply csymbr
          apply (fastforce intro: ccorres_return_C')
         apply wpsimp
        apply (vcg exspec=refill_ready_modifies)
       apply wpsimp+
    apply (fastforce intro: ccorres_return_C)
   apply vcg
  apply (rule conjI)
   apply (fastforce intro!: aligned'_distinct'_obj_at'I
                      simp: active_sc_tcb_at'_def active_sc_at'_def obj_at'_def
                            opt_pred_def opt_map_def
                     split: option.splits)
  apply clarsimp
  apply (intro conjI)
    apply (clarsimp simp: ctcb_relation_def typ_heap_simps' option_to_ctcb_ptr_def
                          ctcb_queue_relation_def)
   apply (clarsimp simp: to_bool_def split: if_splits)
  apply (force dest: obj_at_cslift_tcb
               simp: typ_heap_simps' ctcb_queue_relation_def option_to_ctcb_ptr_def)
  done

lemma tcbReleaseDequeue_ccorres:
  "ccorres dc xfdc
     (valid_objs' and no_0_obj' and pspace_aligned' and pspace_distinct'
      and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and (\<lambda>s. ksCurDomain s \<le> maxDomain)
      and (\<lambda>s. releaseQNonEmptyAndReady s = Some True))
     UNIV []
     tcbReleaseDequeue
     (Call tcbReleaseDequeue_'proc)"
  apply cinit
   apply (rule ccorres_stateAssert)+
   apply (rule ccorres_pre_getReleaseQueue, rename_tac releaseQueue)
   apply (rule_tac P="tcbQueueHead releaseQueue \<noteq> None" in ccorres_gen_asm)
   apply (rule ccorres_symb_exec_l')
     apply (rule ccorres_assert2_abs)
     apply (rule_tac xf'=awakened_'
                 and val="option_to_ctcb_ptr (tcbQueueHead releaseQueue)"
                 and R="\<lambda>s. ksReleaseQueue s = releaseQueue"
                 and R'=UNIV
                  in ccorres_symb_exec_r_known_rv)
        apply (rule conseqPre, vcg)
        apply clarsimp
        apply (drule rf_sr_ctcb_queue_relation_release_queue)
        apply (clarsimp simp: ctcb_queue_relation_def)
       apply ceqv
      apply (ctac add: tcbReleaseRemove_ccorres)
        apply (rule ccorres_add_return2)
        apply (simp only: bind_assoc)
        apply (subst ccorres_seq_skip'[symmetric])
        apply (ctac add: possibleSwitchTo_ccorres)
          apply (rule ccorres_stateAssert)+
          apply (rule ccorres_return_Skip')
         apply wpsimp
        apply (vcg exspec=possibleSwitchTo_modifies)
       apply wpsimp
      apply (vcg exspec=tcbReleaseRemove_modifies)
     apply vcg
    apply wpsimp+
  apply (frule releaseQNonEmptyAndReady_implies_releaseQNonEmpty)
  by (fastforce dest: obj_at'_tcbQueueHead_ksReleaseQueue simp: option_to_ctcb_ptr_def)

lemma no_ofail_releaseQNonEmptyAndReady:
  "no_ofail (invs'
             and (\<lambda>s. \<forall>head. tcbQueueHead (ksReleaseQueue s) = Some head
                             \<longrightarrow> active_sc_tcb_at' head s))
            releaseQNonEmptyAndReady"
  unfolding releaseQNonEmptyAndReady_def readReleaseQueue_def
  apply (wpsimp wp: ovalid_threadRead)
  apply (clarsimp split: if_splits)
  apply (intro conjI)
   apply (fastforce intro!: aligned'_distinct'_obj_at'I
                      simp: active_sc_tcb_at'_def opt_pred_def opt_map_def obj_at_simps
                     split: option.splits)
  apply normalise_obj_at'
  apply (fastforce intro!: aligned'_distinct'_obj_at'I
                     simp: active_sc_tcb_at'_def obj_at'_def opt_pred_def opt_map_def
                           active_sc_at'_def
                    split: option.splits)
  done

lemma awaken_ccorres:
  "ccorres dc xfdc (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)) UNIV []
     awaken (Call awaken_'proc)"
  (is "ccorres _ _ ?abs _ _ _ _")
  apply (cinit simp: runReaderT_def whileAnno_def)
   apply (rule ccorres_stateAssert)+
   apply (rule ccorres_handlers_weaken)
   apply (rule_tac G="\<lambda>_. ?abs
                          and (\<lambda>s. \<forall>head. tcbQueueHead (ksReleaseQueue s) = Some head
                                          \<longrightarrow> active_sc_tcb_at' head s)"
                in ccorres_While'[where G'=UNIV])
        apply (rule ccorres_guard_imp)
          apply (ctac add: tcbReleaseDequeue_ccorres)
         apply fastforce
        apply fastforce
       apply (rule ccorres_guard_imp)
         apply (ctac add: release_q_non_empty_and_ready_ccorres)
        apply fastforce
       apply fastforce
      apply (wpsimp wp: no_ofail_releaseQNonEmptyAndReady)
     apply (clarsimp simp: pred_conj_def)
     apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
     apply (clarsimp simp: tcbReleaseDequeue_def)
     apply (wpsimp simp: tcbQueueHead_ksReleaseQueue_active_sc_tcb_at'_asrt_def)
    apply (rule conseqPre)
     apply (rule ccorres_to_vcg_Normal'[where xf=xfdc])
     apply (fastforce intro: ccorres_call[OF tcbReleaseDequeue_ccorres])
    apply fastforce
   apply clarsimp
   apply (rule conseqPre)
    apply (rule_tac xf=ret__unsigned_long_' in ccorres_to_vcg_Normal)
     apply (fastforce intro: ccorres_call[OF release_q_non_empty_and_ready_ccorres])
    apply (fastforce intro: no_ofail_gets_the no_ofail_releaseQNonEmptyAndReady)
   apply fastforce
  apply (clarsimp simp: tcbInReleaseQueue_imp_active_sc_tcb_at'_asrt_def ksReleaseQueue_asrt_def
                        list_queue_relation_def)
  apply (frule heap_path_head')
  apply (clarsimp simp: tcbQueueEmpty_def)
  apply (case_tac "ts = []"; force)
  done

lemma setNextInterrupt_ccorres:
  "ccorres dc xfdc invs' UNIV [] setNextInterrupt (Call setNextInterrupt_'proc)"
  supply sched_context_C_size[simp del] refill_C_size[simp del]
         Collect_const [simp del]
  (* when numDomains = 1, array bounds checks would become _ = 0 rather than _ < 1, changing the
     shape of the proof compared to when numDomains > 1 *)
  supply word_less_1[simp del]
  apply cinit
   apply (subst if_swap[where P="tcbQueueHead _ = _"])
   apply (rule ccorres_stateAssert)+
   apply (rule ccorres_pre_getCurTime)
   apply (rule ccorres_pre_getCurThread)
   apply (rule ccorres_pre_threadGet)
   apply (rule ccorres_assert2_abs)
   apply (rule ccorres_symb_exec_l')
      apply (rule ccorres_assert2_abs)
      apply (clarsimp, rename_tac scPtr)
      apply (rule ccorres_rhs_assoc2)
      apply wpfix
      apply (rule_tac r'=crefill_relation and xf'=ct_head_refill_' in ccorres_split_nothrow_novcg)
          apply (rule_tac P="\<lambda>s. curTh = ksCurThread s \<and> active_sc_at' scPtr s
                                 \<and> invs' s \<and> cur_tcb' s
                                 \<and> obj_at' (\<lambda>tcb. tcbSchedContext tcb = Some scPtr) curTh s"
                       in ccorres_from_vcg[where P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: active_sc_at'_rewrite)
          apply normalise_obj_at'
          apply (rename_tac sc tcb)
          apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
          apply (frule rf_sr_refill_buffer_relation)
          apply (frule_tac n="scRefillHead sc" in h_t_valid_refill, fastforce+)
            apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                                  opt_pred_def opt_map_def
                           split: option.splits)
           apply fastforce
          apply (frule rf_sr_ksCurThread)
          apply (frule tcb_ko_at_valid_objs_valid_tcb')
           apply fastforce
          apply (frule (1) obj_at_cslift_sc)
          apply (frule (1) obj_at_cslift_tcb)
          apply normalise_obj_at'
          apply (intro conjI)
              apply (clarsimp simp: typ_heap_simps)
             apply (clarsimp simp: typ_heap_simps obj_at'_def valid_tcb'_def ctcb_relation_def)
            apply (rule disjCI2)
            apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
             apply (rule sc_at_array_assertion')
               apply fastforce
              apply (clarsimp simp: typ_heap_simps' obj_at'_def valid_tcb'_def ctcb_relation_def)
              apply (metis ptr_val.simps)
             apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                                  opt_pred_def opt_map_def)
            apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def obj_at'_def
                                  opt_pred_def opt_map_def typ_heap_simps
                                  csched_context_relation_def ctcb_relation_def)
           apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps
                                 csched_context_relation_def ctcb_relation_def)
           apply (metis ptr_val.simps)
          apply normalise_obj_at'
          apply (rename_tac s s' sc sc' tcb tcb')
          apply (clarsimp simp: getRefillHead_def readRefillHead_def readRefillIndex_def
                                refillIndex_def readSchedContext_def getObject_def[symmetric]
                                bind_def return_def ohaskell_state_assert_def gets_the_ostate_assert
                                state_assert_def get_def assert_def fail_def
                         split: if_splits)
          apply (intro conjI impI)
            apply (rule_tac x="(sc, s)" in bexI[rotated])
             apply (fastforce intro: getObject_eq)
            apply (drule refill_buffer_relation_crefill_relation)
            apply (clarsimp simp: Let_def)
            apply (drule_tac x=scPtr in spec)
            apply (clarsimp simp: dyn_array_list_rel_pointwise obj_at'_def)
            apply (drule_tac x="scRefillHead sc" in spec)
            apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def opt_pred_def opt_map_def
                                  typ_heap_simps csched_context_relation_def refillHd_def
                                  sc_ptr_to_crefill_ptr_def ctcb_relation_def)
            apply (metis h_val_clift' ptr_val.simps)
           apply fastforce
          apply (clarsimp simp: active_sc_at'_rewrite)
         apply ceqv
        apply (rename_tac ct_head_refill ct_head_refill')
        apply (rule_tac xf'=next_interrupt_'
                    and val="curTm + rAmount ct_head_refill"
                    and R="\<lambda>s. curTm = ksCurTime s"
                     in ccorres_symb_exec_r_known_rv[where R'=UNIV])
           apply (rule conseqPre, vcg)
           apply clarsimp
           apply (frule rf_sr_ksCurTime)
           apply (clarsimp simp: crefill_relation_def)
          apply ceqv
         apply (rule_tac xf'=next_interrupt_' and r'="(=)" in ccorres_split_nothrow)
             apply (rule ccorres_cond[where R=\<top>])
               apply (simp add: numDomains_sge_1_simp)
              apply (rule ccorres_pre_getDomainTime, rename_tac domainTm)
              apply (rule_tac P="\<lambda>s. domainTm = ksDomainTime s \<and> curTm = ksCurTime s"
                          and P'="\<lbrace>\<acute>next_interrupt = curTm + rAmount ct_head_refill\<rbrace>"
                           in ccorres_from_vcg)
              apply clarsimp
              apply (rule conseqPre, vcg)
              apply (clarsimp simp: return_def min_def)
              apply (frule rf_sr_ksDomainTime)
              apply (fastforce simp:  rf_sr_def cstate_relation_def Let_def split: if_splits)
             apply (rule ccorres_return_Skip')
            apply ceqv
           apply (rule ccorres_pre_getReleaseQueue, rename_tac rq)
           apply (rule_tac xf'=rlq_head_' and val="option_to_ctcb_ptr (tcbQueueHead rq)"
                     and R="\<lambda>s. ksReleaseQueue s = rq"
                     in ccorres_symb_exec_r_known_rv[where R'=UNIV])
              apply (rule conseqPre, vcg)
              apply clarsimp
              apply (frule rf_sr_ctcb_queue_relation_release_queue)
              apply (clarsimp simp: ctcb_queue_relation_def)
             apply ceqv
            apply (rule_tac xf'=next_interrupt_' and r'="(=)" in ccorres_split_nothrow)
                apply (rule_tac Q="\<lambda>s. rq = ksReleaseQueue s \<and> ksReleaseQueue_asrt s
                                       \<and> pspace_aligned' s \<and> pspace_distinct' s \<and> no_0_obj' s"
                             in ccorres_cond_both'[where Q'="\<top>"])
                  apply clarsimp
                  apply (frule rf_sr_ctcb_queue_relation_release_queue)
                  apply (clarsimp simp: ksReleaseQueue_asrt_def)
                  apply (frule (3) obj_at'_tcbQueueHead_ksReleaseQueue)
                  apply (frule (3) obj_at'_tcbQueueEnd_ksReleaseQueue)
                  apply (frule tcbQueueHead_iff_tcbQueueEnd)
                  apply (fastforce dest: obj_at'_typ_at' tcb_at_not_NULL
                                   simp: ctcb_queue_relation_def option_to_ctcb_ptr_def tcbQueueEmpty_def)
                 apply (rule ccorres_pre_threadGet, rename_tac rqSCOpt)
                 apply (clarsimp, rename_tac rlqHeadPtr)
                 apply (rule ccorres_assert2_abs)
                 apply (clarsimp, rename_tac rqScPtr)
                 apply (rule ccorres_symb_exec_l', rename_tac active)
                    apply (rule ccorres_assert2_abs)
                    apply (rule_tac r'=crefill_relation and xf'=rlq_head_refill_'
                                 in ccorres_split_nothrow_novcg)
                        apply clarsimp
                        apply wpfix
                        apply (rule_tac P="\<lambda>s. rq = ksReleaseQueue s \<and> tcbQueueHead rq \<noteq> None
                                               \<and> active_sc_at' rqScPtr s \<and> invs' s
                                               \<and> obj_at' (\<lambda>tcb. tcbSchedContext tcb = Some rqScPtr)
                                                          (the (tcbQueueHead rq)) s"
                                     in ccorres_from_vcg[where P'=UNIV])
                        apply (rule allI, rule conseqPre, vcg)
                        apply (clarsimp simp: active_sc_at'_rewrite)
                        apply normalise_obj_at'
                        apply (rename_tac sc tcb)
                        apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
                        apply (frule rf_sr_refill_buffer_relation)
                        apply (frule_tac n="scRefillHead sc" in h_t_valid_refill, fastforce+)
                          apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def
                                                obj_at'_def opt_pred_def opt_map_def)
                         apply fastforce
                        apply (frule rf_sr_ctcb_queue_relation_release_queue)
                        apply (clarsimp simp: ctcb_queue_relation_def option_to_ctcb_ptr_def)
                        apply (frule tcb_ko_at_valid_objs_valid_tcb')
                         apply fastforce
                        apply (frule (1) obj_at_cslift_sc)
                        apply (frule (1) obj_at_cslift_tcb)
                        apply normalise_obj_at'
                        apply (intro conjI)
                            apply (clarsimp simp: typ_heap_simps)
                           apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
                          apply (rule disjCI2)
                          apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
                           apply (rule sc_at_array_assertion')
                             apply fastforce
                            apply (clarsimp simp: typ_heap_simps' ctcb_relation_def)
                            apply (metis ptr_val.simps)
                           apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def
                                                 obj_at'_def opt_pred_def opt_map_def)
                          apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def
                                                obj_at'_def opt_pred_def opt_map_def typ_heap_simps
                                                csched_context_relation_def ctcb_relation_def)
                         apply (clarsimp simp: sc_ptr_to_crefill_ptr_def csched_context_relation_def
                                               typ_heap_simps ctcb_relation_def)
                         apply (metis ptr_val.simps)
                        apply normalise_obj_at'
                        apply (rename_tac s s' sc sc' tcb tcb')
                        apply (clarsimp simp: getRefillHead_def readRefillHead_def
                                              readRefillIndex_def refillIndex_def readSchedContext_def
                                              getObject_def[symmetric] bind_def return_def
                                              ohaskell_state_assert_def gets_the_ostate_assert
                                              state_assert_def get_def assert_def fail_def
                                       split: if_splits)
                        apply (intro conjI impI)
                          apply (rule_tac x="(sc, s)" in bexI[rotated])
                           apply (fastforce intro: getObject_eq)
                          apply (drule refill_buffer_relation_crefill_relation)
                          apply (clarsimp simp: Let_def)
                          apply (drule_tac x=rqScPtr in spec)
                          apply (clarsimp simp: dyn_array_list_rel_pointwise obj_at'_def)
                          apply (drule_tac x="scRefillHead sc" in spec)
                          apply (clarsimp simp: valid_sched_context'_def is_active_sc'_def opt_pred_def
                                                opt_map_def csched_context_relation_def refillHd_def
                                                sc_ptr_to_crefill_ptr_def typ_heap_simps' obj_at'_def
                                                valid_tcb'_def ctcb_relation_def)
                          apply (metis h_val_clift' ptr_val.simps)
                         apply fastforce
                        apply (clarsimp simp: active_sc_at'_rewrite)
                       apply ceqv
                      apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
                      apply (rule allI, rule conseqPre, vcg)
                      apply (fastforce simp: return_def min_def crefill_relation_def split: if_splits)
                     apply wp
                    apply (clarsimp simp: guard_is_UNIV_def)
                   apply wpsimp+
                apply (rule ccorres_return_Skip')
               apply ceqv
              apply csymbr
              apply (ctac add: setDeadline_ccorres)
             apply wp
            apply vcg
           apply wpsimp
           apply vcg
          apply wpsimp
         apply vcg
        apply vcg
       apply wpsimp
      apply (simp only: guard_is_UNIV_def crefill_relation_def)
      apply fastforce
     apply wpsimp+
  apply (fastforce simp: obj_at'_def active_sc_at'_def)
  done

lemma ccorres_pre_getReprogramTimer:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. ksReprogramTimer s = rv \<longrightarrow> P rv s))
                  {s. \<forall>rv. to_bool (ksReprogram_' (globals s)) = rv \<longrightarrow> s \<in> P' rv }
                          hs (getReprogramTimer >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (simp add: getReprogramTimer_def)
      apply (rule gets_sp)
     apply (clarsimp simp: empty_fail_def getReprogramTimer_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply (clarsimp simp: rf_sr_ksReprogramTimer)
  done

lemma setSchedulerAction_valid_idle'[wp]:
  "setSchedulerAction act \<lbrace>valid_idle'\<rbrace>"
  by wpsimp

lemma setSchedulerAction_valid_domain_list'[wp]:
  "setSchedulerAction act \<lbrace>valid_domain_list'\<rbrace>"
  by wpsimp

crunch tcbSchedAppend
  for valid_idle'[wp]: valid_idle'
  (ignore: threadSet wp: threadSet_idle')

crunch checkDomainTime, awaken
  for valid_domain_list'[wp]: valid_domain_list'
  and weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (simp: crunch_simps wp: crunch_wps)

lemma schedule_ccorres:
  "ccorres dc xfdc invs' UNIV [] schedule (Call schedule_'proc)"
  supply Collect_const [simp del]
  supply prio_and_dom_limit_helpers[simp]
  supply sch_act_wf_asrt_def[simp]
  (* FIXME: these should likely be in simpset for CRefine, or even in general *)
  supply from_bool_eq_if[simp] from_bool_eq_if'[simp] from_bool_0[simp]
         ccorres_IF_True[simp] if_cong[cong]
  apply cinit
   apply (rule ccorres_stateAssert)+
   apply (ctac (no_vcg) add: awaken_ccorres)
    apply (ctac (no_vcg) add: checkDomainTime_ccorres)
     apply (rule ccorres_pre_getCurThread)
     apply (rule ccorres_pre_getSchedulerAction)
     apply (rule ccorres_rhs_assoc2)
     apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
         apply wpc
           (* toplevel case: action is resume current thread *)
           apply (rule ccorres_cond_false_seq)
           apply (rule_tac P="\<lambda>s. ksSchedulerAction s = ResumeCurrentThread"
                        in ccorres_from_vcg[where P'=UNIV])
           apply (clarsimp simp: return_def split: prod.splits)
           apply (rule conseqPre, vcg, clarsimp)
           apply (frule rf_sr_sched_action_relation)
           apply (clarsimp simp: cscheduler_action_relation_def)
          (* toplevel case: action is choose new thread *)
          apply (rule ccorres_cond_true_seq)
          apply (rule ccorres_rhs_assoc)+
          apply csymbr
          (* ct runnable? *)
          apply (ctac add: isSchedulable_ccorres, rename_tac schedulable)
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
              apply (simp add: scheduleChooseNewThread_def bind_assoc)
              apply (rule ccorres_stateAssert)
              apply (rule ccorres_lhs_assoc)+
              apply (rule ccorres_split_nothrow_dc)
                 apply (simp add: bind_assoc)
                 apply (ctac add: scheduleChooseNewThread_ccorres)
                apply (ctac (no_simp) add: ccorres_setSchedulerAction)
                apply (wpsimp simp: cscheduler_action_relation_def wp: hoare_drop_imps
                       | vcg exspec=scheduleChooseNewThread_modifies
                             exspec=tcbSchedEnqueue_modifies
                             exspec=isSchedulable_modifies)+
         (* toplevel case: action is switch to candidate *)
         apply (rename_tac candidate)
         apply (rule_tac P="\<lambda>s. ksSchedulerAction s = SwitchToThread candidate
                                \<and> invs' s \<and> cur_tcb' s \<and> weak_sch_act_wf (ksSchedulerAction s) s"
                      in ccorres_cross_over_guard)
         apply (rule ccorres_cond_true_seq)
         apply (rule ccorres_rhs_assoc)+
         apply csymbr
         (* ct runnable? *)
         apply (ctac add: isSchedulable_ccorres, rename_tac schedulable)
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
             apply (rename_tac schedulable)
             apply (rule_tac P="schedulable = schedulablea" in ccorres_gen_asm2, clarsimp)
             apply (rule ccorres_symb_exec_l3[OF _ git_wp _ empty_fail_getIdleThread], rename_tac it)
              apply (rule ccorres_pre_threadGet, rename_tac targetPrio)
              apply (rule ccorres_pre_threadGet, rename_tac curPrio)
              apply (rule ccorres_rhs_assoc)+
              apply (rule_tac xf'=candidate_' and val="tcb_ptr_to_ctcb_ptr candidate"
                           and R="\<lambda>s. ksSchedulerAction s = SwitchToThread candidate"
                            in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                 apply (rule conseqPre, vcg, clarsimp)
                 apply (fastforce dest!: rf_sr_sched_action_relation
                                   simp: cscheduler_action_relation_def)
                apply ceqv
               (* split off fastfail calculation *)
               apply (rule ccorres_rhs_assoc2)
               apply (rule ccorres_rhs_assoc2)
               apply (rule_tac r'="\<lambda>rv rv'. rv = to_bool rv'" and xf'=fastfail_'
                            in ccorres_split_nothrow)
                   apply (clarsimp simp: scheduleSwitchThreadFastfail_def)
                   apply (rule ccorres_cond_seq2[THEN iffD1])
                   apply (rule_tac xf'=ret__int_' and val="from_bool (curThread = it)"
                               and R="\<lambda>s. it = ksIdleThread s \<and> curThread = ksCurThread s"
                                in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                      apply (rule conseqPre, vcg,
                             fastforce simp: rf_sr_ksCurThread rf_sr_ksIdleThread)
                     apply ceqv
                    apply clarsimp
                    apply (rule ccorres_cond2'[where R=\<top>], fastforce)
                     apply clarsimp
                     apply (rule ccorres_return[where R'=UNIV], clarsimp, vcg)
                    apply (rule_tac P="\<lambda>s. obj_at' (\<lambda>tcb. tcbPriority tcb = curPrio) curThread s
                                           \<and> curThread = ksCurThread s
                                           \<and> obj_at' (\<lambda>tcb. tcbPriority tcb = targetPrio) candidate s"
                                 in ccorres_from_vcg[where P'=UNIV ])
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
                     apply csymbr
                     apply (clarsimp simp: to_bool_def)
                     apply (rule ccorres_Cond_rhs; clarsimp)
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
                      apply (ctac (no_simp) add: ccorres_setSchedulerAction)
                         apply (clarsimp simp: cscheduler_action_relation_def)
                        (* isolate haskell part before setting thread action *)
                        apply (simp add: scheduleChooseNewThread_def)
                        apply (rule ccorres_lhs_assoc)+
                        apply (rule ccorres_split_nothrow_dc)
                           apply (simp add: bind_assoc)
                           apply (rule ccorres_stateAssert)
                           apply (ctac add: scheduleChooseNewThread_ccorres)
                          apply (ctac (no_simp) add: ccorres_setSchedulerAction)
                          apply (wpsimp simp: cscheduler_action_relation_def)+
                        apply (vcg exspec=scheduleChooseNewThread_modifies)
                       apply (wp add: setSchedulerAction_invs' setSchedulerAction_direct hoare_drop_imp
                                 del: ssa_wp)
                      apply (clarsimp | vcg exspec=tcbSchedEnqueue_modifies | wp wp_post_taut)+
                   (* secondary check, when on equal prio and ct was running, prefer ct *)
                   apply (rule ccorres_rhs_assoc)
                   apply (rule_tac xf'=ret__int_'
                               and val="from_bool (schedulablea \<noteq> 0 \<and> curPrio = targetPrio)"
                               and R="\<lambda>s. curThread = ksCurThread s
                                          \<and> obj_at' (\<lambda>tcb. tcbPriority tcb = curPrio) curThread s
                                          \<and> obj_at' (\<lambda>tcb. tcbPriority tcb = targetPrio) candidate s"
                                in ccorres_symb_exec_r_known_rv[where R'=UNIV])
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
                            apply (rule ccorres_stateAssert)
                            apply (ctac add: scheduleChooseNewThread_ccorres)
                           apply (ctac(no_simp) add: ccorres_setSchedulerAction)
                           apply (wpsimp simp: cscheduler_action_relation_def)+
                         apply (vcg exspec=scheduleChooseNewThread_modifies)
                        apply (wp add: setSchedulerAction_invs' setSchedulerAction_direct hoare_drop_imp
                                  del: ssa_wp)
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
                  apply (wp | wp (once) hoare_drop_imp)+
                 apply clarsimp
                 apply (vcg exspec=isHighestPrio_modifies)
                apply clarsimp
                apply (wp (once) hoare_drop_imps)
                 apply wp
                apply (clarsimp simp: conj_ac invs_valid_objs' cong: conj_cong)
                apply wp
               apply (clarsimp, vcg)
              apply (clarsimp, vcg)
             apply clarsimp
             apply (strengthen ko_at'_obj_at'_field)
             apply (clarsimp cong: imp_cong simp: ko_at'_obj_at'_field)
             apply wp
            apply clarsimp
            (* when runnable tcbSchedEnqueue curThread *)
            apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> ksCurThread s = curThread
                                      \<and> ksSchedulerAction s = SwitchToThread candidate
                                      \<and> valid_idle' s \<and> valid_domain_list' s"
                         in hoare_post_imp)
             apply (fastforce simp: invs'_bitmapQ_no_L1_orphans invs_ksCurDomain_maxDomain')
            apply wpsimp+
           apply (vcg exspec=tcbSchedEnqueue_modifies)
          apply (wpsimp wp: getSchedulable_wp)
         apply vcg
        apply ceqv
       apply (clarsimp simp: scAndTimer_def)
       apply (simp add: bind_assoc)
       apply (ctac add: switchSchedContext_ccorres)
         apply (rule ccorres_pre_getReprogramTimer)
         apply (rule ccorres_seq_skip'[THEN iffD1])
         apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
             apply (clarsimp simp: when_def)
             apply (rule_tac R="\<lambda>s. ksReprogramTimer s = reprogram" in ccorres_cond)
               apply clarsimp
               apply (frule rf_sr_ksReprogramTimer)
               apply (fastforce simp: to_bool_def)
              apply (ctac add: setNextInterrupt_ccorres)
                apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
                apply (rule allI, rule conseqPre, vcg)
                apply (clarsimp simp: setReprogramTimer_def rf_sr_def cstate_relation_def Let_def
                                      modify_def get_def put_def bind_def carch_state_relation_def
                                      cmachine_state_relation_def)
               apply wpsimp
              apply (vcg exspec=setNextInterrupt_modifies)
             apply (rule ccorres_return_Skip)
            apply ceqv
           apply (rule ccorres_add_return2)
           apply (rule ccorres_stateAssert)
           apply (rule ccorres_return_Skip)
          apply wpsimp
         apply (vcg exspec=setNextInterrupt_modifies)
        apply (wpsimp wp: switchSchedContext_invs' hoare_drop_imps)
       apply (vcg exspec=switchSchedContext_modifies)
      apply ((wpsimp wp: hoare_drop_imps ssa_invs' scheduleChooseNewThread_invs'
              | fold cur_tcb'_def
              | strengthen invs'_implies)+)[1]
     apply (clarsimp simp: guard_is_UNIV_def)
    apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> valid_idle' s \<and> valid_domain_list' s
                              \<and> cur_tcb' s \<and> weak_sch_act_wf (ksSchedulerAction s) s"
                 in hoare_post_imp)
     apply (fastforce simp: cur_tcb'_def)
    apply (wpsimp wp: hoare_drop_imps ssa_invs' scheduleChooseNewThread_invs')
   apply ((wpsimp | strengthen invs'_implies)+)[1]
  apply clarsimp
  apply (rule conjI)
   apply fastforce
  apply clarsimp
  apply (rule conjI, clarsimp simp: cscheduler_action_relation_def)+
  apply clarsimp
  apply (rule conjI)
   apply (fastforce simp: clift_Some_eq_valid rf_sr_def rf_sr_ksCurThread cur_tcb'_def
                  intro!: tcb_at_h_t_valid)
  apply (rule conjI)
  subgoal
    by (safe;
        clarsimp intro!: obj_at'_weakenE dest!: tcb_at_1 pred_tcb_at'
                   simp: weak_sch_act_wf_def cscheduler_action_relation_def typ_heap_simps
                         ctcb_relation_def true_def false_def;
        fastforce split: if_splits)
  apply (fastforce simp: weak_sch_act_wf_def cscheduler_action_relation_def dest!: tcb_at_not_NULL)
  done

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
