(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Schedule_C
imports Tcb_C Detype_C
begin

instance tcb              :: no_vcpu by intro_classes auto

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
  "ccorres dc xfdc invs_no_cicd' UNIV []
           Arch.switchToIdleThread (Call Arch_switchToIdleThread_'proc)"
  apply (cinit simp: ARM_HYP_H.switchToIdleThread_def)
   apply csymbr (* config_set(CONFIG_ARM_HYPERVISOR_SUPPORT) *)
   apply ccorres_rewrite
   apply (ctac (no_vcg) add: vcpu_switch_ccorres_None)
    apply (rule ccorres_pre_getIdleThread)
    apply (ctac (no_vcg) add: setVMRoot_ccorres)
   apply (wp hoare_vcg_all_lift vcpuSwitch_invs_no_cicd' hoare_vcg_imp_lift vcpuSwitch_it')
  apply (clarsimp simp: invs_no_cicd'_def valid_pspace'_def valid_idle'_tcb_at'_ksIdleThread)
  done

lemma switchToIdleThread_ccorres:
  "ccorres dc xfdc invs_no_cicd' UNIV hs
           switchToIdleThread (Call switchToIdleThread_'proc)"
  apply (cinit)
   apply (rule ccorres_stateAssert)
   apply (rule ccorres_symb_exec_l)
      apply (ctac (no_vcg) add: Arch_switchToIdleThread_ccorres)
       apply (simp add: setCurThread_def)
       apply (rule ccorres_stateAssert)
       apply (rule_tac P="\<lambda>s. thread = ksIdleThread s" and P'=UNIV in ccorres_from_vcg)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: simpler_modify_def)
       apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                             carch_state_relation_def cmachine_state_relation_def)
      apply (wpsimp simp: ARM_HYP_H.switchToIdleThread_def wp: hoare_drop_imps)+
  done

lemma Arch_switchToThread_ccorres:
  "ccorres dc xfdc
           (all_invs_but_ct_idle_or_in_cur_domain' and tcb_at' t)
           (UNIV \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           []
           (Arch.switchToThread t) (Call Arch_switchToThread_'proc)"
  apply (cinit lift: tcb_')
   apply (unfold ARM_HYP_H.switchToThread_def)[1]
   apply csymbr (* config_set(CONFIG_ARM_HYPERVISOR_SUPPORT) *)
   apply ccorres_rewrite
   apply (rule ccorres_move_c_guard_tcb)
   apply (rule ccorres_symb_exec_l3)
      apply (rule_tac P="ko_at' rv t" in ccorres_cross_over_guard)
      apply (ctac add: vcpu_switch_ccorres) (* c *)
        apply simp
        apply (ctac (no_vcg) add: setVMRoot_ccorres)
         apply (simp (no_asm) del: Collect_const)
         apply (rule_tac A'=UNIV in ccorres_guard_imp2)
          apply (ctac add: clearExMonitor_ccorres)
         apply wpsimp+
      apply (vcg exspec=vcpu_switch_modifies)
     apply wpsimp+
    apply (rule_tac Q'="\<lambda>rv s. all_invs_but_ct_idle_or_in_cur_domain' s
                              \<and> case_option (\<lambda>_. True) (ko_wp_at' (is_vcpu' and hyp_live')) (atcbVCPUPtr (tcbArch rv)) s
                              \<and> obj_at' (\<lambda>t::tcb. True) t s" in hoare_strengthen_post[rotated])
     apply (clarsimp simp: vcpu_at_is_vcpu' elim!: ko_wp_at'_weakenE split: option.splits)
    apply (wpsimp wp: getObject_tcb_hyp_sym_refs)
   apply wp
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_pspace'_def)
  apply (frule cmap_relation_tcb, frule (1) cmap_relation_ko_atD)
  apply (clarsimp simp: typ_heap_simps ctcb_relation_def carch_tcb_relation_def)
  done

lemma invs_no_cicd'_pspace_aligned':
  "all_invs_but_ct_idle_or_in_cur_domain' s \<Longrightarrow> pspace_aligned' s"
  by (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def valid_pspace'_def)

lemma invs_no_cicd'_pspace_distinct':
  "all_invs_but_ct_idle_or_in_cur_domain' s \<Longrightarrow> pspace_distinct' s"
  by (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def valid_pspace'_def)

(* FIXME: move *)
lemma switchToThread_ccorres:
  "ccorres dc xfdc
           (all_invs_but_ct_idle_or_in_cur_domain' and tcb_at' t)
           (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           hs
           (switchToThread t)
           (Call switchToThread_'proc)"
  apply (clarsimp simp: switchToThread_def)
  apply (rule ccorres_symb_exec_l'[OF _ _ isRunnable_sp]; (solves wpsimp)?)
  apply (rule ccorres_symb_exec_l'[OF _ _ assert_sp]; (solves wpsimp)?)
  apply (rule ccorres_stateAssert_fwd)+
  apply (cinit' lift: thread_')
   apply (ctac (no_vcg) add: Arch_switchToThread_ccorres)
    apply (ctac (no_vcg) add: tcbSchedDequeue_ccorres)
     apply (simp add: setCurThread_def)
     apply (rule ccorres_stateAssert)
     apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
     apply clarsimp
     apply (rule conseqPre, vcg)
     apply (clarsimp simp: setCurThread_def simpler_modify_def rf_sr_def cstate_relation_def
                           Let_def carch_state_relation_def cmachine_state_relation_def)
    apply (wpsimp wp: Arch_switchToThread_invs_no_cicd' hoare_drop_imps
           | strengthen invs_no_cicd'_pspace_aligned' invs_no_cicd'_pspace_distinct')+
  done

lemma activateThread_ccorres:
  "ccorres dc xfdc
           (ct_in_state' activatable' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)
            and valid_objs' and pspace_aligned' and pspace_distinct')
           UNIV []
           activateThread
           (Call activateThread_'proc)"
  apply (cinit)
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
  done

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
           (all_invs_but_ct_idle_or_in_cur_domain' and tcb_at' t)
           (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           hs
           (switchToThread t)
           (Call switchToThread_'proc)"
  apply (rule ccorres_guard_imp2)
      apply (ctac (no_vcg) add: switchToThread_ccorres)
     apply auto
  done

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

lemma chooseThread_ccorres:
  "ccorres dc xfdc all_invs_but_ct_idle_or_in_cur_domain' UNIV [] chooseThread (Call chooseThread_'proc)"
proof -

  note prio_and_dom_limit_helpers [simp]
  note Collect_const_mem [simp]
  (* when numDomains = 1, array bounds checks would become _ = 0 rather than _ < 1, changing the
     shape of the proof compared to when numDomains > 1 *)
  include no_less_1_simps

  have invs_no_cicd'_max_CurDomain[intro]:
    "\<And>s. invs_no_cicd' s \<Longrightarrow> ksCurDomain s \<le> maxDomain"
    by (simp add: invs_no_cicd'_def)

  have invs_no_cicd'_valid_bitmaps:
    "\<And>s. invs_no_cicd' s \<Longrightarrow> valid_bitmaps s"
    by (simp add: invs_no_cicd'_def)

  have invs_no_cicd'_pspace_aligned':
    "\<And>s. invs_no_cicd' s \<Longrightarrow> pspace_aligned' s"
    by (simp add: invs_no_cicd'_def valid_pspace'_def)

  have invs_no_cicd'_pspace_distinct':
    "\<And>s. invs_no_cicd' s \<Longrightarrow> pspace_distinct' s"
    by (simp add: invs_no_cicd'_def valid_pspace'_def)

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
             apply assumption
            apply clarsimp
            apply (rule conseqPre, vcg)
            apply clarsimp
           apply (wp isRunnable_wp)+
       apply (clarsimp simp: Let_def guard_is_UNIV_def)
       apply (rule conjI)
        apply (clarsimp simp: le_maxDomain_eq_less_numDomains unat_trans_ucast_helper)
       apply (intro conjI impI)
        apply (clarsimp simp: cready_queues_index_to_C_def numPriorities_def ctcb_queue_relation_def
                              tcbQueueEmpty_def option_to_ctcb_ptr_def)
       apply (frule_tac qdom=curdom and prio=rv in cready_queues_index_to_C_in_range')
        apply fastforce
       apply (clarsimp simp: num_tcb_queues_val word_less_nat_alt cready_queues_index_to_C_def2)
      apply wpsimp
     apply (clarsimp simp: guard_is_UNIV_def le_maxDomain_eq_less_numDomains word_less_nat_alt
                           numDomains_less_numeric_explicit)
    apply clarsimp
    apply (frule invs_no_cicd'_max_CurDomain)
    apply (frule invs_no_cicd'_pspace_aligned')
    apply (frule invs_no_cicd'_pspace_distinct')
    apply (frule invs_no_cicd'_valid_bitmaps)
    apply (frule valid_bitmaps_bitmapQ_no_L1_orphans)
    apply (frule valid_bitmaps_valid_bitmapQ)
    apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def cong: conj_cong)
    apply (intro conjI impI)
         apply (fastforce intro: lookupBitmapPriority_le_maxPriority)
        apply (fastforce dest!: bitmapQ_from_bitmap_lookup valid_bitmapQ_bitmapQ_simp)
       apply (fastforce dest!: lookupBitmapPriority_obj_at'
                         simp: ready_queue_relation_def ksReadyQueues_asrt_def st_tcb_at'_def obj_at'_def)
      apply (fastforce dest: lookupBitmapPriority_le_maxPriority)
     apply (fastforce dest!: bitmapQ_from_bitmap_lookup valid_bitmapQ_bitmapQ_simp)
    apply (fastforce dest!: lookupBitmapPriority_obj_at'
                      simp: ready_queue_relation_def ksReadyQueues_asrt_def st_tcb_at'_def obj_at'_def)
    done
qed

lemma cdom_schedule_relationD:
  "\<lbrakk> cdom_schedule_relation asched csched; n < length asched \<rbrakk> \<Longrightarrow>
   dom_schedule_entry_relation (asched ! n) (csched.[n])"
  by (simp add: cdom_schedule_relation_def)

lemma ksDomSched_length_dom_relation[simp]:
  "cdom_schedule_relation (ksDomSchedule s) csched \<Longrightarrow>
   length (ksDomSchedule s) = unat domScheduleLength"
  by (auto simp: cdom_schedule_relation_def domScheduleLength_def)

lemma ksDomSched_length_relation[simp]:
  "(s,s') \<in> rf_sr \<Longrightarrow> length (ksDomSchedule s) = unat domScheduleLength"
  by (auto simp: rf_sr_def cstate_relation_def Let_def)

lemma rf_sr_cdom_schedule_relation:
  "(s, s') \<in> rf_sr \<Longrightarrow> cdom_schedule_relation (ksDomSchedule s) (ksDomSchedule_' (globals s'))"
  by (simp add: rf_sr_def cstate_relation_def Let_def)

lemma rf_sr_ksDomScheduleStart:
  "(s, s') \<in> rf_sr \<Longrightarrow> ksDomScheduleStart s = unat (ksDomScheduleStart_' (globals s'))"
  by (simp add: rf_sr_def cstate_relation_def Let_def)

lemma rf_sr_ksDomScheduleIdx:
  "(s, s') \<in> rf_sr \<Longrightarrow> ksDomScheduleIdx s = unat (ksDomScheduleIdx_' (globals s'))"
  by (simp add: rf_sr_def cstate_relation_def Let_def)

lemma ksDomScheduleStart_bounded:
  "\<lbrakk>invs' s; (s, s') \<in> rf_sr \<rbrakk> \<Longrightarrow> ksDomScheduleStart_' (globals s') < scast domScheduleLength"
  apply (drule invs_valid_dom_schedule')
  apply (frule ksDomSched_length_relation)
  apply (drule rf_sr_ksDomScheduleStart)
  apply (simp add: valid_dom_schedule'_def word_less_nat_alt unat_scast_domScheduleLength)
  done

lemma ksDomScheduleIdx_bounded:
  "\<lbrakk>invs' s; (s, s') \<in> rf_sr \<rbrakk> \<Longrightarrow> ksDomScheduleIdx_' (globals s') < scast domScheduleLength"
  apply (drule invs_valid_dom_schedule')
  apply (frule ksDomSched_length_relation)
  apply (drule rf_sr_ksDomScheduleIdx)
  apply (simp add: valid_dom_schedule'_def word_less_nat_alt unat_scast_domScheduleLength)
  done

lemma nextDomain_ccorres:
  "ccorres dc xfdc invs' UNIV [] nextDomain (Call nextDomain_'proc)"
  supply rf_sr_unfold = rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                        cmachine_state_relation_def dschDomain_def dschLength_def
  supply idx_unat = word_le_nat_alt word_less_nat_alt less_domScheduleLength_plus_1
                    unat_scast_domScheduleLength
  supply word_less_1[simp del] less_Suc0[simp del]
  apply cinit
   apply (rule_tac P=invs' and P'=UNIV in ccorres_from_vcg)
   apply (rule allI, rule conseqPre, vcg)
   apply (simp only: if_P_then_t_else_f_eq_f) (* reduce if-explosion first *)
   apply (simp add: if_P_then_t_else_f_eq_f cong: if_cong)
   apply (clarsimp simp: simpler_modify_def Let_def not_le)
   apply (frule (1) ksDomScheduleStart_bounded)
   apply (frule (1) ksDomScheduleIdx_bounded)
   apply (frule rf_sr_ksDomScheduleIdx)
   apply (frule rf_sr_ksDomScheduleStart)
   apply (frule rf_sr_cdom_schedule_relation)
   apply (rule conjI; clarsimp)
    (* idx + 1 \<ge> length; wrap to start *)
    apply (simp add: idx_unat)
    apply (clarsimp simp: rf_sr_unfold)
    apply (frule_tac n="ksDomScheduleStart \<sigma>" in cdom_schedule_relationD, simp)
    apply (clarsimp simp: dom_schedule_entry_relation_def mask_def domScheduleLength_def)
    apply (drule sym[where s="ucast t" for t], simp)
   (* idx + 1 < length *)
   apply (rule conjI)
    apply (simp add: domScheduleLength_def) (* array guard *)
   apply (rule conjI, clarsimp)
    (* sched ! idx + 1 = end marker; wrap to start *)
    apply (rule conjI)
     apply (simp add: domScheduleLength_def) (* array guard *)
    apply (simp add: idx_unat)
    apply (frule_tac n="Suc (ksDomScheduleIdx \<sigma>)" in cdom_schedule_relationD, simp)
    apply (clarsimp simp: dom_schedule_entry_relation_domainEndMarker)
    apply (clarsimp simp: rf_sr_unfold)
    apply (frule_tac n="ksDomScheduleStart \<sigma>" in cdom_schedule_relationD, simp)
    apply (clarsimp simp: dom_schedule_entry_relation_def mask_def)
    apply (drule sym[where s="ucast x" and t="w >> n" for x w n], simp)
   (* idx + 1 < length, no end marker; advance to idx + 1 *)
   (* In the numDomains = 1/domScheduleLength = 1 case, this case is a contradiction, because
      idx + 1 can never become < length. We carefully do not let Isabelle discover the
      contradiction until the very end where we unfold domScheduleLength_def, so that the proof
      steps also work for numDomains > 1. *)
   apply (clarsimp simp: idx_unat)
   apply (frule_tac n="Suc (ksDomScheduleIdx \<sigma>)" in cdom_schedule_relationD, simp)
   apply (clarsimp simp: dom_schedule_entry_relation_domainEndMarker)
   apply (clarsimp simp: rf_sr_unfold idx_unat)
   apply (frule_tac n="Suc (ksDomScheduleIdx \<sigma>)" in cdom_schedule_relationD, simp)
   apply (clarsimp simp: dom_schedule_entry_relation_def mask_def domScheduleLength_def)
   apply (drule sym[where s="ucast t" for t], simp)
  apply simp
  done

lemma Arch_prepareNextDomain_ccorres:
  "ccorres dc xfdc invs' UNIV [] vcpuFlush (Call Arch_prepareNextDomain_'proc)"
  apply cinit'
   apply csymbr (* config_set(CONFIG_ARM_HYPERVISOR_SUPPORT) *)
   apply ccorres_rewrite
   apply (ctac add: vcpu_flush_ccorres)
  apply simp
  done

lemma prepareNextDomain_ccorres:
  "ccorres dc xfdc invs' UNIV [] prepareNextDomain (Call prepareNextDomain_'proc)"
  apply cinit
   apply (ctac add: Arch_prepareNextDomain_ccorres)
  by clarsimp

lemma scheduleChooseNewThread_ccorres:
  "ccorres dc xfdc
     (\<lambda>s. invs' s \<and> ksSchedulerAction s = ChooseNewThread) UNIV hs
     (do domainTime \<leftarrow> getDomainTime;
         _ \<leftarrow> when (domainTime = 0) (do
             _ <- prepareNextDomain;
             nextDomain
         od);
         chooseThread
      od)
     (Call scheduleChooseNewThread_'proc)"
  apply (cinit')
   apply (rule ccorres_pre_getDomainTime)
   apply (rule ccorres_split_nothrow)
       apply (rule_tac R="\<lambda>s. ksDomainTime s = domainTime" in ccorres_when)
        apply (fastforce simp: rf_sr_ksDomainTime)
       apply (ctac (no_vcg) add: prepareNextDomain_ccorres)
        apply (rule ccorres_call[OF nextDomain_ccorres, where xf'=xfdc] ; simp)
       apply wpsimp
      apply ceqv
     apply (ctac (no_vcg) add: chooseThread_ccorres)
    apply (wpsimp wp: nextDomain_invs_no_cicd' simp: prepareNextDomain_def)
   apply clarsimp
   apply (vcg exspec=nextDomain_modifies exspec=prepareNextDomain_modifies)
  apply (clarsimp simp: if_apply_def2 invs'_invs_no_cicd')
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

lemma schedule_ccorres:
  "ccorres dc xfdc invs' UNIV [] schedule (Call schedule_'proc)"
  supply Collect_const [simp del]
  supply prio_and_dom_limit_helpers[simp]
  supply Collect_const_mem [simp]
  (* FIXME: these should likely be in simpset for CRefine, or even in general *)
  supply from_bool_eq_if[simp] from_bool_eq_if'[simp] from_bool_0[simp] if_1_0_0[simp]
         ccorres_IF_True[simp]
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
      apply (rule_tac Q'="\<lambda>rv s. invs' s \<and> ksCurThread s = curThread
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
  apply (intro conjI impI allI; clarsimp simp: typ_heap_simps ctcb_relation_def to_bool_def)
     apply (fastforce simp: tcb_at_not_NULL tcb_at_1 dest: pred_tcb_at')+
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

lemma threadSet_timeSlice_ccorres [corres]:
  "ccorres dc xfdc (tcb_at' thread) {s. thread' s = tcb_ptr_to_ctcb_ptr thread \<and> unat (v' s) = v} hs
           (threadSet (tcbTimeSlice_update (\<lambda>_. v)) thread)
           (Basic (\<lambda>s. globals_update (t_hrs_'_update (hrs_mem_update (heap_update (Ptr &(thread' s\<rightarrow>[''tcbTimeSlice_C''])::word32 ptr) (v' s)))) s))"
  apply (rule ccorres_guard_imp2)
   apply (rule threadSet_ccorres_lemma4 [where P=\<top> and P'=\<top>])
    apply vcg
   prefer 2
   apply (rule conjI, simp)
   apply assumption
  apply clarsimp
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (clarsimp simp: cmachine_state_relation_def carch_state_relation_def cpspace_relation_def)
  apply (clarsimp simp: update_tcb_map_tos typ_heap_simps')
  apply (simp add: map_to_ctes_upd_tcb_no_ctes tcb_cte_cases_def tcb_cte_cases_neqs
                   map_to_tcbs_upd)
  apply (simp add: cep_relations_drop_fun_upd cvariable_relation_upd_const
                   ko_at_projectKO_opt)
   defer
  apply (drule ko_at_projectKO_opt)
  apply (erule (2) cmap_relation_upd_relI)
    apply (simp add: ctcb_relation_def)
   apply assumption
  apply simp
  done

lemma timerTick_ccorres:
  "ccorres dc xfdc invs' UNIV [] timerTick (Call timerTick_'proc)"
  supply subst_all [simp del]
  apply (cinit)
   apply (rule ccorres_pre_getCurThread)
   apply (ctac add: get_tsType_ccorres [where f="\<lambda>s. ksCurThread_' (globals s)"])
     apply (rule ccorres_split_nothrow_novcg)
         apply wpc
                apply (simp add: ThreadState_defs, rule ccorres_cond_false, rule ccorres_return_Skip)+
             (* thread_state.Running *)
             apply simp
             apply (rule ccorres_cond_true)
             apply (rule ccorres_pre_threadGet)
             apply (rule_tac P="cur_tcb'" and P'=\<top> in ccorres_move_c_guards(8))
              apply (clarsimp simp: cur_tcb'_def)
              apply (drule (1) tcb_at_h_t_valid)
              apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
             apply (rule_tac Q="\<lambda>s. obj_at' (\<lambda>tcb. tcbTimeSlice tcb = rva) (ksCurThread s) s"
                         and Q'=\<top> in ccorres_cond_both')
               apply clarsimp
               apply (drule (1) obj_at_cslift_tcb)
               apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
               apply (clarsimp simp: typ_heap_simps)
               apply (clarsimp simp: ctcb_relation_def word_less_nat_alt)
              apply (rule_tac P="cur_tcb'" and P'=\<top> in ccorres_move_c_guards(8))
               apply (clarsimp simp: cur_tcb'_def)
               apply (fastforce simp: rf_sr_def cstate_relation_def Let_def typ_heap_simps dest: tcb_at_h_t_valid)
              apply (rule_tac P="cur_tcb'" and P'=\<top> in ccorres_move_c_guards(8))
               apply (clarsimp simp: cur_tcb'_def)
               apply (fastforce simp: rf_sr_def cstate_relation_def Let_def typ_heap_simps dest: tcb_at_h_t_valid)
              apply (ctac add: threadSet_timeSlice_ccorres)
             apply (rule ccorres_rhs_assoc)+
             apply (ctac)
               apply simp
               apply (ctac (no_vcg) add: tcbSchedAppend_ccorres)
                apply (ctac add: rescheduleRequired_ccorres)
               apply (wp weak_sch_act_wf_lift_linear
                         threadSet_pred_tcb_at_state tcbSchedAppend_valid_objs' threadSet_valid_objs' threadSet_tcbDomain_triv
                    | clarsimp simp: st_tcb_at'_def o_def split: if_splits)+
             apply (vcg exspec=tcbSchedDequeue_modifies)
        apply (simp add: ThreadState_defs, rule ccorres_cond_false, rule ccorres_return_Skip)+
        apply ceqv
       apply (clarsimp simp: decDomainTime_def numDomains_sge_1_simp)
       apply (rule ccorres_when[where R=\<top>])
        apply (solves \<open>clarsimp split: if_split\<close>)
       apply (rule ccorres_split_nothrow_novcg)
           apply (rule_tac rrel=dc and xf=xfdc and P=\<top> and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: simpler_modify_def)
           apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                 carch_state_relation_def cmachine_state_relation_def)
          apply ceqv
         apply (rule ccorres_pre_getDomainTime)
         apply (rename_tac rva rv'a rvb)
         apply (rule_tac P'="{s. ksDomainTime_' (globals s) = rvb}" in ccorres_inst, simp)
         apply (case_tac "rvb = 0")
          apply clarsimp
          apply (rule ccorres_guard_imp2)
           apply (rule ccorres_cond_true)
           apply (ctac add: rescheduleRequired_ccorres)
          apply clarsimp
          apply assumption
         apply clarsimp
         apply (rule ccorres_guard_imp2)
          apply (rule ccorres_cond_false)
          apply (rule ccorres_return_Skip)
         apply clarsimp
        apply wp
       apply (clarsimp simp: guard_is_UNIV_def)
      apply (wp hoare_vcg_conj_lift hoare_vcg_all_lift hoare_drop_imps)
       apply (wpc | wp threadSet_weak_sch_act_wf threadSet_valid_objs' rescheduleRequired_weak_sch_act_wf
                       tcbSchedAppend_valid_objs' weak_sch_act_wf_lift_linear threadSet_st_tcb_at2 threadGet_wp
                  | simp split del: if_splits)+
     apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem word_sle_def word_sless_def)
    apply (wp gts_wp')
   apply vcg
  apply (clarsimp simp: invs_weak_sch_act_wf)
  apply (fold cur_tcb'_def)
  apply (rule conjI, clarsimp)
  apply (rule conjI, clarsimp)
   apply (rule conjI)
    apply (clarsimp simp: invs'_def valid_state'_def)
    apply (auto simp: obj_at'_def inQ_def weak_sch_act_wf_def st_tcb_at'_def
                      valid_pspace'_def ct_idle_or_in_cur_domain'_def valid_tcb'_def valid_idle'_def projectKOs)[1]
   apply (rule conjI, clarsimp simp: invs'_def valid_state'_def valid_tcb'_def)+
    apply (auto simp: obj_at'_def inQ_def weak_sch_act_wf_def st_tcb_at'_def
                      valid_pspace'_def ct_idle_or_in_cur_domain'_def valid_tcb'_def valid_idle'_def projectKOs)[1]
   apply (auto simp: invs'_def valid_state'_def valid_tcb'_def tcb_cte_cases_def)[1]

  apply (frule invs_cur')
  apply (clarsimp simp: cur_tcb'_def)
  apply (drule (1) obj_at_cslift_tcb)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def typ_heap_simps' Kernel_Config.timeSlice_def)
  apply (subst unat_sub)
   apply simp
  apply (clarsimp simp: ctcb_relation_def)
  done

end

end
