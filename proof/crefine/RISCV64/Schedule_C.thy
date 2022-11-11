(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Schedule_C
imports Tcb_C
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
  "ccorres dc xfdc (invs' and valid_idle') UNIV []
           Arch.switchToIdleThread (Call Arch_switchToIdleThread_'proc)"
  apply (cinit simp: RISCV64_H.switchToIdleThread_def)
   apply (rule ccorres_pre_getIdleThread)
   apply (rule ccorres_symb_exec_r)
     apply (ctac (no_vcg) add: setVMRoot_ccorres)
    apply vcg
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply (clarsimp simp: valid_pspace'_def valid_idle'_tcb_at'_ksIdleThread)
  done

lemma switchToIdleThread_ccorres:
  "ccorres dc xfdc (invs' and valid_idle') UNIV hs
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

lemma tcbSchedDequeue_ready_qs_runnable[wp]:
  "tcbSchedDequeue tcbPtr \<lbrace>ready_qs_runnable\<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (clarsimp simp: ready_qs_runnable_def)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_ball_lift2 threadGet_wp)
    apply (fastforce simp: obj_at_simps split: if_splits)
   apply (wpsimp wp: threadSet_st_tcb_at2)
  by fastforce

lemma ready_qs_runnable_ksMachineState[simp]:
  "ready_qs_runnable (ksMachineState_update f s) = ready_qs_runnable s"
  by (clarsimp simp: ready_qs_runnable_def)

lemma ready_or_release'_ksMachineState[simp]:
  "ready_or_release' (ksMachineState_update f s) = ready_or_release' s"
  by (clarsimp simp: ready_or_release'_def)

crunches setVMRoot
  for ready_qs_runnable'[wp]: ready_qs_runnable
  and ready_or_release'[wp]: ready_or_release'
  (wp: crunch_wps)

lemma switchToThread_ready_qs_runnable[wp]:
  "RISCV64_H.switchToThread t \<lbrace>ready_qs_runnable\<rbrace>"
  unfolding RISCV64_H.switchToThread_def
  by wpsimp

lemma switchToThread_ready_or_release'[wp]:
  "RISCV64_H.switchToThread t \<lbrace>ready_or_release'\<rbrace>"
  unfolding RISCV64_H.switchToThread_def
  by wpsimp

(* FIXME: move *)
lemma switchToThread_ccorres:
  "ccorres dc xfdc
           (invs' and tcb_at' t and (\<lambda>s. \<forall>d p. distinct (ksReadyQueues s (d, p))) and ready_or_release')
           (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           hs
           (switchToThread t)
           (Call switchToThread_'proc)"
  apply (cinit lift: thread_')
   apply (rule ccorres_stateAssert)
   apply (ctac (no_vcg) add: Arch_switchToThread_ccorres)
    apply (ctac (no_vcg) add: tcbSchedDequeue_ccorres)
     apply (rule_tac P=ready_qs_runnable and P'=UNIV in ccorres_from_vcg)
     apply clarsimp
     apply (rule conseqPre, vcg)
     apply (clarsimp simp: setCurThread_def simpler_modify_def
                           stateAssert_def get_def bind_def return_def fail_def)
     apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                           carch_state_relation_def cmachine_state_relation_def)
    apply (wpsimp wp: hoare_vcg_all_lift)+
  apply (fastforce simp: ready_qs_runnable_def)
  done

lemma get_tsType_ccorres2:
  "ccorres (\<lambda>r r'. r' = thread_state_to_tsType r) ret__unsigned_longlong_' (tcb_at' thread)
           (UNIV \<inter> {s. f s = tcb_ptr_to_ctcb_ptr thread} \<inter>
            {s. cslift s (Ptr &(f s\<rightarrow>[''tcbState_C''])) = Some (thread_state_' s)}) []
  (getThreadState thread) (Call thread_state_get_tsType_'proc)"
  unfolding getThreadState_def
  apply (rule ccorres_from_spec_modifies [where P=\<top>, simplified])
     apply (rule thread_state_get_tsType_spec)
    apply (rule thread_state_get_tsType_modifies)
   apply simp
  apply (frule (1) obj_at_cslift_tcb)
  apply (clarsimp simp: typ_heap_simps)
  apply (rule bexI [rotated, OF threadGet_eq], assumption)
  apply simp
  apply (drule ctcb_relation_thread_state_to_tsType)
  apply simp
  done

lemma activateThread_ccorres:
  "ccorres dc xfdc
           (ct_in_state' activatable' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)
                   and valid_queues and valid_objs')
           UNIV []
           activateThread
           (Call activateThread_'proc)"
  apply (cinit)
sorry (* FIXME RT: activeThread_ccorres
   apply (rule ccorres_pre_getCurThread)
   apply (ctac add: get_tsType_ccorres2 [where f="\<lambda>s. ksCurThread_' (globals s)"])
     apply (rule_tac P="activatable' rv" in ccorres_gen_asm)
     apply (wpc)
            apply (rule_tac P=\<top> and P'=UNIV in ccorres_inst, simp)
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_inst, simp)
          apply (rule_tac P=\<top> and P'=UNIV in ccorres_inst, simp)
         apply simp
         apply (rule ccorres_cond_true)
         apply (rule ccorres_return_Skip)
        apply (rule_tac P=\<top> and P'=UNIV in ccorres_inst, simp)
       apply (simp add: "StrictC'_thread_state_defs" del: Collect_const)
       apply (rule ccorres_cond_false)
       apply (rule ccorres_cond_false)
       apply (rule ccorres_cond_true)
       apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: activateIdleThread_def return_def)
      apply (rule_tac P=\<top> and P'=UNIV in ccorres_inst, simp)
     apply (simp add: "StrictC'_thread_state_defs" del: Collect_const)
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
  apply (clarsimp simp: typ_heap_simps ThreadState_Running_def mask_def)
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

lemma switchToThread_ccorres':
  "ccorres dc xfdc
           (invs' and tcb_at' t and (\<lambda>s. \<forall>d p. distinct (ksReadyQueues s (d, p))) and ready_or_release')
           (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           hs
           (switchToThread t)
           (Call switchToThread_'proc)"
  apply (rule ccorres_guard_imp2)
      apply (ctac (no_vcg) add: switchToThread_ccorres)
     apply auto
  done

lemmas word_log2_max_word_word_size = word_log2_max[where 'a=machine_word_len, simplified word_size, simplified]

lemma chooseThread_ccorres:
  "ccorres dc xfdc
     (invs' and valid_idle' and (\<lambda>s.  \<forall>d p. distinct (ksReadyQueues s (d, p))) and ready_or_release')
     UNIV []
     chooseThread (Call chooseThread_'proc)"
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
    apply (rule ccorres_stateAssert)
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
         apply (rule_tac P="queue \<noteq> []" in ccorres_cross_over_guard_no_st)
         apply (rule ccorres_symb_exec_l)
            apply (rule ccorres_assert)
            apply (rule ccorres_symb_exec_r)
              apply (rule ccorres_Guard_Seq)+
              apply (rule ccorres_symb_exec_r)
                apply (simp only: ccorres_seq_skip)
                apply (rule ccorres_call[OF switchToThread_ccorres']; simp)
               apply vcg
              apply (rule conseqPre, vcg)
              apply clarsimp
             apply clarsimp
             apply (rule conseqPre, vcg)
             apply (rule Collect_mono)
             apply clarsimp
             apply (strengthen queue_in_range)
             apply assumption
            apply clarsimp
            apply (rule conseqPre, vcg)
            apply clarsimp
           apply (wpsimp wp: isSchedulable_wp)+
       apply (clarsimp simp: Let_def guard_is_UNIV_def)
       apply (case_tac queue, simp)
       apply (clarsimp simp: tcb_queue_relation'_def cready_queues_index_to_C_def numPriorities_def)
       apply (clarsimp simp add: maxDom_to_H maxPrio_to_H
                                 queue_in_range[where qdom=0, simplified, simplified maxPrio_to_H])
       apply (clarsimp simp: le_maxDomain_eq_less_numDomains unat_trans_ucast_helper )
      apply wpsimp
     apply (clarsimp simp: guard_is_UNIV_def le_maxDomain_eq_less_numDomains word_less_nat_alt
                           numDomains_less_numeric_explicit)
    apply clarsimp
    apply (frule invs_queues)
    apply (frule invs_ksCurDomain_maxDomain')
    apply (frule invs'_bitmapQ_no_L1_orphans)
    apply (prop_tac "\<forall>d p. \<forall>t \<in> set (ksReadyQueues s (d,p)). isSchedulable_bool t s")
     subgoal sorry (* FIXME RT: use cross lemmas or remove assert from the Haskell *)
    apply (clarsimp simp: valid_queues_def lookupBitmapPriority_le_maxPriority)
    apply (intro conjI impI)
       apply (fastforce dest: bitmapQ_from_bitmap_lookup simp: valid_bitmapQ_bitmapQ_simp)
      apply (drule (2) bitmapQ_from_bitmap_lookup)
      apply (simp add: valid_bitmapQ_bitmapQ_simp)
      apply (case_tac "ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s)", simp)
      apply (fastforce dest: cons_set_intro)
     apply (fastforce dest: bitmapQ_from_bitmap_lookup simp: valid_bitmapQ_bitmapQ_simp)
    apply (clarsimp simp: not_less le_maxDomain_eq_less_numDomains)
    apply (prop_tac "ksCurDomain s = 0")
     using unsigned_eq_0_iff apply force
    apply (drule (2) bitmapQ_from_bitmap_lookup)
    apply (simp add: valid_bitmapQ_bitmapQ_simp)
    apply (case_tac "ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s)", simp)
    apply (fastforce dest: cons_set_intro
                     simp: valid_queues_no_bitmap_def inQ_def obj_at'_def st_tcb_at'_def)
    done
qed

lemma ksDomSched_length_relation[simp]:
  "\<lbrakk>cstate_relation s s'\<rbrakk> \<Longrightarrow> length (kernel_state.ksDomSchedule s) = unat (ksDomScheduleLength)"
  apply (auto simp: cstate_relation_def cdom_schedule_relation_def Let_def ksDomScheduleLength_def)
  done

lemma ksDomSched_length_dom_relation[simp]:
  "\<lbrakk>cdom_schedule_relation (kernel_state.ksDomSchedule s) kernel_all_global_addresses.ksDomSchedule \<rbrakk> \<Longrightarrow> length (kernel_state.ksDomSchedule s) = unat (ksDomScheduleLength)"
  apply (auto simp: cstate_relation_def cdom_schedule_relation_def Let_def ksDomScheduleLength_def)
  done

lemma nextDomain_ccorres:
  "ccorres dc xfdc invs' UNIV [] nextDomain (Call nextDomain_'proc)"
sorry (* FIXME RT: nextDomain_ccorres. Involves usToTicks
  apply (cinit)
   apply (simp add: ksDomScheduleLength_def sdiv_word_def sdiv_int_def)
   apply (rule_tac P=invs' and P'=UNIV in ccorres_from_vcg)
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: simpler_modify_def Let_def
                         rf_sr_def cstate_relation_def
                         carch_state_relation_def cmachine_state_relation_def)
   apply (rule conjI)
    apply clarsimp
    apply (subgoal_tac "ksDomScheduleIdx \<sigma> = unat (ksDomScheduleLength - 1)")
     apply (fastforce simp add: cdom_schedule_relation_def dom_schedule_entry_relation_def dschDomain_def dschLength_def ksDomScheduleLength_def sdiv_word_def sdiv_int_def simp del: ksDomSched_length_dom_relation)
    apply (simp add: ksDomScheduleLength_def)
    apply (frule invs'_ksDomScheduleIdx)
    apply (simp add: invs'_ksDomSchedule newKernelState_def)
    apply (simp only: Abs_fnat_hom_1 Abs_fnat_hom_add)
    apply (drule unat_le_helper)
    apply (simp add: sdiv_int_def sdiv_word_def)
    apply (clarsimp simp: cdom_schedule_relation_def)
   apply (simp only: Abs_fnat_hom_1 Abs_fnat_hom_add word_not_le)
   apply clarsimp
   apply (subst (asm) of_nat_Suc[symmetric])
   apply (drule iffD1[OF of_nat_mono_maybe'[where x=3, simplified, symmetric], rotated 2])
     apply simp
    apply (frule invs'_ksDomScheduleIdx)
    apply (simp add: invs'_ksDomSchedule newKernelState_def)
    apply (clarsimp simp: cdom_schedule_relation_def)
   apply (clarsimp simp: ksDomScheduleLength_def)
   apply (subst of_nat_Suc[symmetric])+
   apply (subst unat_of_nat64)
    apply (simp add: word_bits_def)
   apply (subst unat_of_nat64)
    apply (simp add: word_bits_def)
   apply (fastforce simp add: cdom_schedule_relation_def dom_schedule_entry_relation_def dschDomain_def dschLength_def simp del: ksDomSched_length_dom_relation)
  apply simp
  done *)

(* FIXME RT: move *)
crunches nextDomain
  for valid_idle'[wp]: valid_idle'
  and distinct_queues[wp]: "\<lambda>s. distinct (ksReadyQueues s (d, p))"
  and ready_or_release'[wp]: ready_or_release'
  (simp: crunch_simps ready_or_release'_def)

lemma scheduleChooseNewThread_ccorres:
  "ccorres dc xfdc
     (\<lambda>s. invs' s \<and> valid_idle' s \<and> (\<forall>d p. distinct (ksReadyQueues s (d, p)))
          \<and> ksSchedulerAction s = ChooseNewThread \<and> ready_or_release' s) UNIV hs
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
    apply (wpsimp wp: nextDomain_invs' hoare_vcg_all_lift)
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

lemma isRoundRobin_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     \<top> \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> [] (isRoundRobin scPtr) (Call isRoundRobin_'proc)"
  apply cinit
   apply (rule ccorres_pre_getObject_sc)
   apply (rule ccorres_Guard)
   apply (rule ccorres_return_C)
     apply simp+
  apply (fastforce simp: rf_sr_def csched_context_relation_def typ_heap_simps
                  split: if_splits)
  done

definition refillSize :: "machine_word \<Rightarrow> (kernel_state, nat) nondet_monad" where
  "refillSize scPtr \<equiv>
     do sc \<leftarrow> getSchedContext scPtr;
        return (scRefillCount sc)
     od"

(* FIXME RT: use automation here *)
lemma refillFull_refill_size:
  "monadic_rewrite True False (sc_at' scPtr)
     (refillFull scPtr)
     (do count \<leftarrow> refillSize scPtr;
         sc \<leftarrow> getSchedContext scPtr;
         return $ count = scRefillMax sc
      od)"
  apply (clarsimp simp: refillFull_def refillSize_def)
  apply (rule monadic_rewrite_guard_imp)
   apply (rule monadic_rewrite_symb_exec_r)
      apply (rule monadic_rewrite_bind_tail)
       apply (rename_tac sc')
       apply (rule_tac Q="\<lambda>_. sc' = sc" in monadic_rewrite_guard_imp)
        apply (rule monadic_rewrite_from_simple)
        apply fastforce
       apply simp
      apply wpsimp
     apply wpsimp
    apply wpsimp+
  apply (clarsimp simp: obj_at_simps)
  done

lemma refill_size_ccorres:
  "ccorres (\<lambda>rv rv'. rv = unat rv') ret__unsigned_long_'
     (sc_at' scPtr and valid_refills' scPtr) \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (refillSize scPtr)
     (Call refill_size_'proc)"
  apply (cinit lift: sc_', rename_tac sc')
   apply (rule ccorres_pre_getObject_sc, rename_tac sc)
   apply (rule ccorres_Guard_Seq)+
   apply (rule ccorres_cond_seq)
   apply ccorres_rewrite
   apply (rule_tac R="ko_at' sc scPtr and K (sc_valid_refills' sc)"
               and P="\<lambda>s. scRefillHead sc \<le> refillTailIndex sc"
                in ccorres_cond_both)
     apply clarsimp
     apply (drule obj_at_cslift_sc)
      apply fastforce
     apply (clarsimp simp: csched_context_relation_def word_le_nat_alt typ_heap_simps)
    apply (rule ccorres_Guard)+
    apply (ctac add: ccorres_return_C)
   apply (rule ccorres_Guard)+
   apply (ctac add: ccorres_return_C)
  apply (clarsimp simp: csched_context_relation_def typ_heap_simps obj_at_simps
                        valid_refills'_def opt_map_def crefill_size_def opt_pred_def
                 split: if_splits)
  done

lemma refill_full_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     (sc_at' scPtr and valid_refills' scPtr) \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (refillFull scPtr) (Call refill_full_'proc)"
  apply (rule monadic_rewrite_ccorres_assemble[where P=P and Q=P for P,
                                               unfolded pred_conj_def, simplified, rotated])
   apply (rule monadic_rewrite_guard_imp)
    apply (rule refillFull_refill_size)
   apply fastforce
  apply cinit'
   apply (ctac (no_vcg) add: refill_size_ccorres)
    apply (rule ccorres_pre_getObject_sc)
    apply (rule ccorres_Guard)
    apply (rule ccorres_return_C)
      apply wpsimp
     apply simp
    apply simp
   apply wpsimp
  apply (fastforce dest: obj_at_cslift_sc
                   simp: csched_context_relation_def typ_heap_simps split: if_splits)
  done

lemma refill_single_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     (sc_at' scPtr) \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> [] (refillSingle scPtr) (Call refill_single_'proc)"
  apply cinit
   apply (rule ccorres_pre_getObject_sc)
   apply (rule ccorres_Guard)+
   apply (ctac add: ccorres_return_C)
  by (clarsimp simp: csched_context_relation_def typ_heap_simps
              split: if_splits)

lemma refill_capacity_ccorres:
  "ccorres (=) ret__unsigned_longlong_'
     \<top> (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace> \<inter> \<lbrace>\<acute>usage = usage\<rbrace>) []
     (refillCapacity scPtr usage) (Call refill_capacity_'proc)"
sorry (* FIXME RT: refill_capacity_ccorres *)

lemma refill_ready_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     \<top> \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (refillReady scPtr) (Call refill_ready_'proc)"
sorry (* FIXME RT: refill_ready_ccorres *)

lemma sc_active_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     \<top> \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (scActive scPtr) (Call sc_active_'proc)"
  apply cinit
   apply (rule ccorres_pre_getObject_sc)
   apply (rule ccorres_Guard)+
   apply (ctac add: ccorres_return_C)
  by (clarsimp simp: csched_context_relation_def typ_heap_simps word_less_nat_alt
              split: if_splits)

lemma scReleased_rewrite:
  "monadic_rewrite True False \<top>
     (scReleased scPtr)
     (do active \<leftarrow> scActive scPtr;
         if active
           then do ready \<leftarrow> refillReady scPtr;
                   return ready
                od
           else return False
      od)"
  apply (clarsimp simp: scReleased_def)
  apply (rule monadic_rewrite_bind_tail)
   apply (rule_tac P="active" and R=\<top> in monadic_rewrite_if_r)
    apply (rule monadic_rewrite_is_refl)
    apply fastforce
   apply (rule monadic_rewrite_symb_exec_l)
      apply wpsimp
      apply (rule monadic_rewrite_is_refl)
      apply (wpsimp simp: refillReady_def)+
  done

lemma sc_released_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     \<top> \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (scReleased scPtr) (Call sc_released_'proc)"
  apply (rule monadic_rewrite_ccorres_assemble[where P=P and Q=P for P,
                                               unfolded pred_conj_def, simplified, rotated])
   apply (rule monadic_rewrite_guard_imp)
    apply (rule scReleased_rewrite)
   apply fastforce
  apply cinit'
   apply (ctac add: sc_active_ccorres, rename_tac active)
     apply (rule ccorres_cond[where R=\<top>])
       apply (clarsimp simp: to_bool_def split: if_splits)
      apply (ctac add: refill_ready_ccorres)
        apply (rule ccorres_return_C)
          apply fastforce
         apply fastforce
        apply fastforce
       apply wpsimp
      apply vcg
     apply (rule ccorres_return_C)
       apply fastforce
      apply fastforce
     apply fastforce
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
          apply (clarsimp simp: conj_ac invs_queues invs_valid_objs' cong: conj_cong)
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

  apply (clarsimp simp: tcb_at_invs' rf_sr_ksCurThread if_apply_def2 invs_queues invs_valid_objs')
  apply (frule invs_sch_act_wf')
  apply (frule tcb_at_invs')
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
