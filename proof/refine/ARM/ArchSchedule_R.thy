(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchSchedule_R
imports Schedule_R
begin

context Arch begin arch_global_naming

named_theorems Schedule_R_assms

crunch tcbSchedAppend, tcbSchedDequeue, tcbSchedEnqueue
  for state_hyp_refs_of'[Schedule_R_assms, wp]: "\<lambda>s. P (state_hyp_refs_of' s)"
  (simp: unless_def crunch_simps obj_at'_def wp: getObject_tcb_wp)

lemma arch_switch_thread_tcb_at'[wp]:
  "\<lbrace>tcb_at' t\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  by (unfold ARM_H.switchToThread_def, wp typ_at_lift_tcb')

crunch setVMRoot
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t'"
  (simp: crunch_simps wp: crunch_wps)

crunch Arch.switchToThread
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"

lemma Arch_switchToThread_pred_tcb'[wp]:
  "Arch.switchToThread t \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
proof -
  have pos: "\<And>P t t'. Arch.switchToThread t \<lbrace>pred_tcb_at' proj P t'\<rbrace>"
    by (wpsimp simp: ARM_H.switchToThread_def)
  show ?thesis
    apply (rule P_bool_lift [OF pos])
    by (rule lift_neg_pred_tcb_at' [OF ArchThreadDecls_H_ARM_H_switchToThread_typ_at' pos])
qed

lemmas Arch_switchToThread_st_tcb_at'[Schedule_R_assms] =
  Arch_switchToThread_pred_tcb'[where proj=itcbState]

crunch storeWordUser, setVMRoot, asUser, storeWordUser, Arch.switchToThread, Arch.switchToIdleThread
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksIdleThread[Schedule_R_assms, wp]: "\<lambda>s. P (ksIdleThread s)"
  and sym_heap_sched_pointers[Schedule_R_assms, wp]: sym_heap_sched_pointers
  and valid_objs'[Schedule_R_assms, wp]: valid_objs'
  (wp: crunch_wps threadSet_sched_pointers getObject_tcb_wp getASID_wp
   simp: crunch_simps obj_at'_def)

crunch arch_switch_to_thread, arch_switch_to_idle_thread
  for pspace_aligned[Schedule_R_assms, wp]: pspace_aligned
  and pspace_distinct[Schedule_R_assms, wp]: pspace_distinct
  and ready_queues[Schedule_R_assms, wp]: "\<lambda>s. P (ready_queues s)"
  and ready_qs_distinct[wp]: ready_qs_distinct
  (wp: ready_qs_distinct_lift crunch_wps simp: crunch_simps)

lemma arch_switchToThread_corres:
  "corres dc (valid_arch_state and valid_objs and pspace_aligned and pspace_distinct
              and valid_asid_map and (\<lambda>s. unique_table_refs (caps_of_state s))
              and (\<lambda>s. sym_refs (state_hyp_refs_of s)) and valid_global_objs
              and valid_vs_lookup and valid_vspace_objs and tcb_at t)
             (no_0_obj')
             (arch_switch_to_thread t) (Arch.switchToThread t)"
  unfolding arch_switch_to_thread_def ARM_H.switchToThread_def
  apply (simp add: arch_switch_to_thread_def ARM_H.switchToThread_def)
  apply (rule corres_guard_imp)
    apply (rule corres_underlying_split [OF setVMRoot_corres])
      apply (rule corres_machine_op[OF corres_rel_imp])
      apply (rule corres_underlying_trivial)
       apply (simp add: ARM.clearExMonitor_def | wp)+
  done

(* use superset of arch_switchToThread_corres preconditions across the architectures as interface *)
lemma arch_switchToThread_corres_interface[Schedule_R_assms]:
  "corres dc (valid_arch_state and valid_objs and valid_asid_map and valid_arch_caps
              and pspace_aligned and pspace_distinct and valid_global_objs
              and (\<lambda>s. sym_refs (state_hyp_refs_of s))
              and valid_vspace_objs and pspace_in_kernel_window and valid_cur_fpu and tcb_at t)
             (no_0_obj')
             (arch_switch_to_thread t) (Arch.switchToThread t)"
  by (corres corres: arch_switchToThread_corres; simp add: valid_arch_caps_def)

lemma arch_switchToIdleThread_corres:
  "corres dc
          (valid_arch_state and pspace_aligned and pspace_distinct and valid_idle
           and valid_objs and valid_vspace_objs and valid_asid_map and valid_arch_caps
           and valid_global_objs)
          (no_0_obj')
          arch_switch_to_idle_thread Arch.switchToIdleThread"
  unfolding arch_switch_to_idle_thread_def switchToIdleThread_def
  apply (corres corres: setVMRoot_corres
                        getIdleThread_corres
                wp: tcb_at_idle_thread_lift tcb_at'_ksIdleThread_lift
         | simp)+
   apply (clarsimp simp: valid_idle_tcb_at valid_arch_caps_def)+
  done

(* use superset of arch_switchToIdleThread_corres preconditions across the architectures as interface *)
lemma arch_switchToIdleThread_corres_interface[Schedule_R_assms]:
  "corres dc
     (valid_arch_state and pspace_aligned and pspace_distinct and valid_asid_map and valid_idle
      and valid_arch_caps and valid_global_objs and valid_vspace_objs and valid_objs)
     (no_0_obj')
     arch_switch_to_idle_thread Arch.switchToIdleThread"
  by (rule corres_guard_imp, rule arch_switchToIdleThread_corres; simp)

lemma threadSet_timeslice_invs[Schedule_R_assms]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> threadSet (tcbTimeSlice_update b) t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (wp threadSet_invs_trivial, simp_all add: inQ_def cong: conj_cong)

lemma clearExMonitor_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp ARM.clearExMonitor \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq)
   apply (simp add: no_irq_clearExMonitor)
  apply (clarsimp simp: ARM.clearExMonitor_def machine_op_lift_def
                        in_monad select_f_def)
  done

lemma Arch_switchToThread_invs[Schedule_R_assms, wp]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (wpsimp simp: ARM_H.switchToThread_def)

crunch "Arch.switchToThread"
  for ksCurDomain[Schedule_R_assms, wp]: "\<lambda>s. P (ksCurDomain s)"
  and tcbDomain[Schedule_R_assms, wp]: "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'"
  and tcbState[Schedule_R_assms, wp]: "obj_at' (\<lambda>tcb. P (tcbState tcb)) t'"
  (simp: crunch_simps wp: crunch_wps getASID_wp)

lemma threadSet_invs_no_cicd'_trivialT:
  assumes
    "\<forall>tcb. \<forall>(getF,setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
    "\<forall>tcb. tcbState (F tcb) = tcbState tcb \<and> tcbDomain (F tcb) = tcbDomain tcb"
    "\<forall>tcb. is_aligned (tcbIPCBuffer tcb) msg_align_bits \<longrightarrow> is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits"
    "\<forall>tcb. tcbBoundNotification (F tcb) = tcbBoundNotification tcb"
    "\<forall>tcb. tcbSchedPrev (F tcb) = tcbSchedPrev tcb"
    "\<forall>tcb. tcbSchedNext (F tcb) = tcbSchedNext tcb"
    "\<forall>tcb. tcbQueued (F tcb) = tcbQueued tcb"
    "\<forall>tcb. tcbDomain tcb \<le> maxDomain \<longrightarrow> tcbDomain (F tcb) \<le> maxDomain"
    "\<forall>tcb. tcbPriority tcb \<le> maxPriority \<longrightarrow> tcbPriority (F tcb) \<le> maxPriority"
    "\<forall>tcb. tcbMCP tcb \<le> maxPriority \<longrightarrow> tcbMCP (F tcb) \<le> maxPriority"
    "\<forall>tcb. tcbFlags tcb && ~~ tcbFlagMask = 0 \<longrightarrow> tcbFlags (F tcb) && ~~ tcbFlagMask = 0"
  shows "threadSet F t \<lbrace>invs_no_cicd'\<rbrace>"
  apply (simp add: invs_no_cicd'_def valid_state'_def)
  apply (wp threadSet_valid_pspace'T
            threadSet_sch_actT_P[where P=False, simplified]
            threadSet_state_refs_of'T[where f'=id]
            threadSet_state_hyp_refs_of'
            threadSet_iflive'T
            threadSet_ifunsafe'T
            threadSet_idle'T
            threadSet_global_refsT
            irqs_masked_lift
            valid_irq_node_lift
            valid_irq_handlers_lift''
            threadSet_ctes_ofT
            threadSet_not_inQ
            threadSet_ct_idle_or_in_cur_domain'
            threadSet_valid_dom_schedule' threadSet_sched_pointers threadSet_valid_sched_pointers
            threadSet_cur
            untyped_ranges_zero_lift
         | clarsimp simp: assms cteCaps_of_def valid_arch_tcb'_def | rule refl)+
  by (auto simp: o_def)

lemmas threadSet_invs_no_cicd'_trivial =
    threadSet_invs_no_cicd'_trivialT [OF all_tcbI all_tcbI all_tcbI all_tcbI, OF ball_tcb_cte_casesI]

lemma asUser_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> asUser t m \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps | simp)+
  apply (wp threadSet_invs_no_cicd'_trivial hoare_drop_imps | simp)+
  done

lemma clearExMonitor_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp ARM.clearExMonitor \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wp dmo_invs_no_cicd' no_irq)
   apply (simp add: no_irq_clearExMonitor)
  apply (clarsimp simp: ARM.clearExMonitor_def machine_op_lift_def
                        in_monad select_f_def)
  done


lemma Arch_switchToThread_invs_no_cicd'[Schedule_R_assms]:
  "Arch.switchToThread t \<lbrace>invs_no_cicd'\<rbrace>"
  by (wpsimp wp: setVMRoot_invs_no_cicd' simp: ARM_H.switchToThread_def)

crunch "Arch.switchToThread"
  for cap_to'[wp]: "ex_nonz_cap_to' p"
  (simp: crunch_simps wp: crunch_wps)

crunch switchToThread
  for cap_to'[wp]: "ex_nonz_cap_to' p"
  (simp: crunch_simps)

crunch "ThreadDecls_H.switchToThread"
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"

(* neater unfold, actual unfold is really ugly *)
lemma bitmapQ_lookupBitmapPriority_simp[Schedule_R_assms]:
  "\<lbrakk> ksReadyQueuesL1Bitmap s d \<noteq> 0 ; valid_bitmapQ s ; bitmapQ_no_L1_orphans s \<rbrakk> \<Longrightarrow>
   bitmapQ d (lookupBitmapPriority d s) s =
    (ksReadyQueuesL1Bitmap s d !! word_log2 (ksReadyQueuesL1Bitmap s d) \<and>
     ksReadyQueuesL2Bitmap s (d, invertL1Index (word_log2 (ksReadyQueuesL1Bitmap s d))) !!
       word_log2 (ksReadyQueuesL2Bitmap s (d, invertL1Index (word_log2 (ksReadyQueuesL1Bitmap s d)))))"
  unfolding bitmapQ_def lookupBitmapPriority_def
  supply word_log2_max_word32[simp del]
  apply (drule bit_word_log2, clarsimp)
  apply (drule (1) bitmapQ_no_L1_orphansD, clarsimp)
  apply (drule bit_word_log2, clarsimp)
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
   apply (rule word_of_nat_less)
    apply (fastforce intro: word_of_nat_less simp: wordRadix_def' unat_of_nat word_size)+
  done

lemma Arch_switchToIdleThread_invs_no_cicd'[Schedule_R_assms]:
  "Arch.switchToIdleThread \<lbrace>invs_no_cicd'\<rbrace>"
  unfolding switchToIdleThread_def
  by (wpsimp wp: setCurThread_invs_no_cicd'_idle_thread setVMRoot_invs_no_cicd')

crunch Arch.switchToIdleThread
  for obj_at'[wp]: "obj_at' P t"

lemmas Arch_switchToIdleThread_not_queued'[Schedule_R_assms] =
  ArchThreadDecls_H_ARM_H_switchToIdleThread_obj_at'[where P="Not \<circ> tcbQueued"]

lemmas Arch_switchToIdleThread_tcbState[Schedule_R_assms] =
  ArchThreadDecls_H_ARM_H_switchToIdleThread_obj_at'[where P="P \<circ> tcbState" for P]

crunch arch_switch_to_thread, handle_spurious_irq
  for valid_idle[Schedule_R_assms, wp]: valid_idle

end (* Arch *)

interpretation Schedule_R?: Schedule_R
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Schedule_R_assms)?)?)
qed

context Arch begin arch_global_naming

named_theorems Schedule_R_2_assms

lemma bitmapL1_highest_lookup[Schedule_R_2_assms]:
  "\<lbrakk> valid_bitmapQ s ; bitmapQ_no_L1_orphans s ; bitmapQ d p s \<rbrakk>
   \<Longrightarrow> p \<le> lookupBitmapPriority d s"
  apply (subgoal_tac "ksReadyQueuesL1Bitmap s d \<noteq> 0")
   prefer 2
   apply (clarsimp simp add: bitmapQ_def)
  apply (case_tac "prioToL1Index (lookupBitmapPriority d s) = prioToL1Index p")
   apply (rule prioToL1Index_le_mask, simp)
   apply (frule (2) bitmapQ_from_bitmap_lookup)
   apply (clarsimp simp: bitmapQ_lookupBitmapPriority_simp)
   apply (clarsimp simp: bitmapQ_def lookupBitmapPriority_def)
   apply (subst mask_or_not_mask[where n=wordRadix and x=p, symmetric])
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
   apply (rule word_log2_maximum)
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
  apply (erule word_log2_maximum)
  done

lemma guarded_switch_to_chooseThread_fragment_corres[Schedule_R_2_assms]:
  "corres dc
    (P and st_tcb_at runnable t and invs and valid_sched)
    (P' and invs_no_cicd')
    (guarded_switch_to t)
    (do runnable \<leftarrow> isRunnable t;
        y \<leftarrow> assert runnable;
        ThreadDecls_H.switchToThread t
     od)"
  apply (rule_tac Q'="st_tcb_at' runnable' t" in corres_cross_add_guard)
   apply (fastforce intro!: st_tcb_at_runnable_cross simp: obj_at_def is_tcb_def)
  unfolding guarded_switch_to_def isRunnable_def
  apply simp
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getThreadState_corres])
      apply (rule corres_assert_assume_l)
      apply (rule corres_assert_assume_r)
      apply (rule switchToThread_corres)
     apply (wp gts_st_tcb_at)+
   apply (clarsimp simp: st_tcb_at_tcb_at invs_def valid_state_def valid_pspace_def valid_sched_def
                          invs_valid_vs_lookup invs_unique_refs)
  apply (auto elim!: pred_tcb'_weakenE split: thread_state.splits
              simp: pred_tcb_at' runnable'_def all_invs_but_ct_idle_or_in_cur_domain'_def)
  done

lemma prepareNextDomain_corres[corres]:
  "corres dc (valid_arch_state and pspace_aligned and pspace_distinct and valid_cur_fpu)
             (pspace_aligned' and pspace_distinct' and no_0_obj')
             arch_prepare_next_domain prepareNextDomain"
  by (clarsimp simp: arch_prepare_next_domain_def prepareNextDomain_def)

crunch prepareNextDomain
  for invs'[wp]: invs'
  and nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"

crunch tcb_sched_action
  for valid_vs_lookup[Schedule_R_2_assms, wp]: valid_vs_lookup

end (* Arch *)

interpretation Schedule_R_2?: Schedule_R_2
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Schedule_R_2_assms)?)?)
qed

context Arch begin arch_global_naming

named_theorems Schedule_R_3_assms

lemma scheduleChooseNewThread_fragment_corres:
  "corres dc (invs and valid_sched and (\<lambda>s. scheduler_action s = choose_new_thread)) (invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread))
     (do _ \<leftarrow> when (domainTime = 0) (do
           _ \<leftarrow> arch_prepare_next_domain;
           next_domain
         od);
         choose_thread
      od)
     (do _ \<leftarrow> when (domainTime = 0) (do
           _ \<leftarrow> prepareNextDomain;
           nextDomain
         od);
         chooseThread
      od)"
  apply (subst bind_dummy_ret_val)+
  apply (corres corres: nextDomain_corres chooseThread_corres
                    wp: nextDomain_invs_no_cicd')
   apply (auto simp: valid_sched_def invs'_def valid_state'_def all_invs_but_ct_idle_or_in_cur_domain'_def)
  done

lemma scheduleChooseNewThread_corres[Schedule_R_3_assms]:
  "corres dc
     (\<lambda>s. invs s \<and> valid_sched s \<and> scheduler_action s = choose_new_thread)
     (\<lambda>s. invs' s \<and> ksSchedulerAction s = ChooseNewThread)
     schedule_choose_new_thread scheduleChooseNewThread"
  unfolding schedule_choose_new_thread_def scheduleChooseNewThread_def
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getDomainTime_corres], clarsimp)
      apply (rule corres_split[OF scheduleChooseNewThread_fragment_corres, simplified bind_assoc])
        apply (rule setSchedulerAction_corres)
        apply (wpsimp simp: getDomainTime_def)+
  done

lemma scheduleChooseNewThread_invs'[Schedule_R_3_assms]:
  "\<lbrace> invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread) \<rbrace>
   scheduleChooseNewThread
   \<lbrace> \<lambda>_ s. invs' s \<rbrace>"
  unfolding scheduleChooseNewThread_def prepareNextDomain_def
  apply (wpsimp wp: ssa_invs' chooseThread_invs_no_cicd' chooseThread_ct_not_queued_2
                    chooseThread_activatable_2 chooseThread_invs_no_cicd'
                    chooseThread_in_cur_domain' nextDomain_invs_no_cicd' chooseThread_ct_not_queued_2)
  apply (clarsimp simp: invs'_to_invs_no_cicd'_def)
  done

lemma stt_nosch:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
   switchToThread t
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  by (simp add: Thread_H.switchToThread_def ARM_H.switchToThread_def storeWordUser_def)
     (wpsimp wp: setCurThread_nosch hoare_drop_imp)

lemma stit_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
   switchToIdleThread
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def
                   ARM_H.switchToIdleThread_def storeWordUser_def)
  apply (wp setCurThread_nosch | simp add: getIdleThread_def)+
  done

lemma scheduleChooseNewThread_ct_activatable'[Schedule_R_3_assms, wp]:
  "\<lbrace> invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread) \<rbrace>
   scheduleChooseNewThread
   \<lbrace>\<lambda>_. ct_in_state' activatable'\<rbrace>"
  unfolding scheduleChooseNewThread_def prepareNextDomain_def
  by (wpsimp simp: ct_in_state'_def
                wp: ssa_invs' nextDomain_invs_no_cicd'
                    chooseThread_activatable_2[simplified ct_in_state'_def]
         | (rule hoare_lift_Pf[where f=ksCurThread], solves wp)
         | strengthen invs'_invs_no_cicd)+

end (* Arch *)

interpretation Schedule_R_3?: Schedule_R_3
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Schedule_R_3_assms)?)?)
qed

end
