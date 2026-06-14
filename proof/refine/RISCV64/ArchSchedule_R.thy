(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchSchedule_R
imports Schedule_R
begin

context Arch begin arch_global_naming

named_theorems Schedule_R_assms

crunch set_vm_root
  for pspace_distinct[wp]: pspace_distinct
  (simp: crunch_simps)

crunch tcbSchedAppend, tcbSchedDequeue, tcbSchedEnqueue
  for state_hyp_refs_of'[Schedule_R_assms, wp]: "\<lambda>s. P (state_hyp_refs_of' s)"
  (simp: unless_def crunch_simps obj_at'_def wp: getObject_tcb_wp)

lemma arch_switch_thread_tcb_at'[wp]:
  "\<lbrace>tcb_at' t\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  by (unfold RISCV64_H.switchToThread_def, wp)

crunch setVMRoot
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t'"
  (simp: crunch_simps wp: crunch_wps)

crunch Arch.switchToThread
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"

lemma Arch_switchToThread_pred_tcb'[wp]:
  "Arch.switchToThread t \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
proof -
  have pos: "\<And>P t t'. Arch.switchToThread t \<lbrace>pred_tcb_at' proj P t'\<rbrace>"
    by (wpsimp simp: RISCV64_H.switchToThread_def)
  show ?thesis
    apply (rule P_bool_lift [OF pos])
    by (rule lift_neg_pred_tcb_at' [OF ArchThreadDecls_H_RISCV64_H_switchToThread_typ_at' pos])
qed

lemmas Arch_switchToThread_st_tcb_at'[Schedule_R_assms] =
  Arch_switchToThread_pred_tcb'[where proj=itcbState]

crunch storeWordUser, setVMRoot, asUser, storeWordUser, Arch.switchToThread
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksIdleThread[Schedule_R_assms, wp]: "\<lambda>s. P (ksIdleThread s)"
  and tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
  and tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
  and sym_heap_sched_pointers[Schedule_R_assms, wp]: sym_heap_sched_pointers
  and valid_objs'[Schedule_R_assms, wp]: valid_objs'
  (wp: crunch_wps sym_heap_sched_pointers_lift threadSet_field_inv getObject_tcb_wp getASID_wp
   simp: crunch_simps
   ignore: threadSet)

crunch arch_switch_to_thread, arch_switch_to_idle_thread
  for pspace_aligned[Schedule_R_assms, wp]: pspace_aligned
  and pspace_distinct[Schedule_R_assms, wp]: pspace_distinct
  and in_correct_ready_q[Schedule_R_assms, wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  and valid_idle[wp]: valid_idle
  and state_refs_of[wp]: "\<lambda>s. P (state_refs_of s)"
  and ready_queues_runnable[wp]: ready_queues_runnable
  and ep_queues_blocked[wp]: ep_queues_blocked
  and ntfn_queues_blocked[wp]: ntfn_queues_blocked
  (rule: in_correct_ready_q_lift ready_qs_distinct_lift ready_queues_runnable_lift
         ep_queues_blocked_lift ntfn_queues_blocked_lift crunch_wps
   simp: crunch_simps)

lemma arch_switchToThread_corres:
  "corres dc (valid_arch_state and valid_objs and pspace_aligned and pspace_distinct
              and valid_vspace_objs and tcb_at t)
             (no_0_obj')
             (arch_switch_to_thread t) (Arch.switchToThread t)"
  apply (simp add: arch_switch_to_thread_def RISCV64_H.switchToThread_def)
  apply (rule corres_guard_imp)
    apply (rule setVMRoot_corres[OF refl])
   apply (clarsimp simp: st_tcb_at_tcb_at valid_arch_state_asid_table
                         valid_arch_state_global_arch_objs)
  apply simp
  done

(* use superset of arch_switchToThread_corres preconditions across the architectures as interface *)
lemma arch_switchToThread_corres_interface[Schedule_R_assms]:
  "corres dc (valid_arch_state and valid_objs and valid_asid_map and valid_arch_caps
              and pspace_aligned and pspace_distinct and valid_global_objs
              and (\<lambda>s. sym_refs (state_hyp_refs_of s))
              and valid_vspace_objs and pspace_in_kernel_window and valid_cur_fpu and tcb_at t)
             (no_0_obj')
             (arch_switch_to_thread t) (Arch.switchToThread t)"
  by (corres corres: arch_switchToThread_corres; simp)

lemma arch_switchToIdleThread_corres:
  "corres dc
     (valid_arch_state and valid_objs and pspace_aligned and pspace_distinct
      and valid_vspace_objs and valid_idle)
     (no_0_obj')
     arch_switch_to_idle_thread Arch.switchToIdleThread"
  unfolding arch_switch_to_idle_thread_def RISCV64_H.switchToIdleThread_def
  apply add_valid_idle'
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (clarsimp simp: valid_idle'_asrt_def)
  by (corres corres: getIdleThread_corres setVMRoot_corres)
     (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def is_tcb
                     valid_arch_state_asid_table valid_arch_state_global_arch_objs)+

(* use superset of arch_switchToIdleThread_corres preconditions across the architectures as interface *)
lemma arch_switchToIdleThread_corres_interface[Schedule_R_assms]:
  "corres dc
     (valid_arch_state and pspace_aligned and pspace_distinct and valid_asid_map and valid_idle
      and valid_arch_caps and valid_global_objs and valid_vspace_objs and valid_objs)
     (no_0_obj')
     arch_switch_to_idle_thread Arch.switchToIdleThread"
  by (rule corres_guard_imp, rule arch_switchToIdleThread_corres; simp)

lemma Arch_switchToThread_invs[Schedule_R_assms, wp]:
  "Arch.switchToThread t \<lbrace>invs'\<rbrace>"
  unfolding RISCV64_H.switchToThread_def by wpsimp

crunch "Arch.switchToThread"
  for ksCurDomain[Schedule_R_assms, wp]: "\<lambda>s. P (ksCurDomain s)"
  and tcbDomain[Schedule_R_assms, wp]: "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'"
  and tcbState[Schedule_R_assms, wp]: "obj_at' (\<lambda>tcb. P (tcbState tcb)) t'"
  (simp: crunch_simps wp: crunch_wps getASID_wp)

crunch "Arch.switchToThread"
  for cap_to'[wp]: "ex_nonz_cap_to' p"
  (simp: crunch_simps wp: crunch_wps)

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
   apply (fastforce intro: word_of_nat_less simp: wordRadix_def' unat_of_nat word_size)+
  done

crunch Arch.switchToIdleThread
  for obj_at'[wp]: "obj_at' P t"

lemmas Arch_switchToIdleThread_not_queued'[Schedule_R_assms] =
  ArchThreadDecls_H_RISCV64_H_switchToIdleThread_obj_at'[where P="Not \<circ> tcbQueued"]

lemmas Arch_switchToIdleThread_tcbState[Schedule_R_assms] =
  ArchThreadDecls_H_RISCV64_H_switchToIdleThread_obj_at'[where P="P \<circ> tcbState" for P]

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
     (P and schedulable t and invs and valid_ready_qs and ready_or_release)
     (P' and invs')
     (guarded_switch_to t) (ThreadDecls_H.switchToThread t)"
  apply (clarsimp simp: guarded_switch_to_def)
  apply (rule corres_symb_exec_l[rotated, OF _ thread_get_sp])
    apply (rule thread_get_exs_valid)
    apply (fastforce intro: schedulable_imp_tcb_at)
   apply wpsimp
   apply (fastforce intro: schedulable_imp_tcb_at)
  apply (rule corres_symb_exec_l[rotated, OF _ assert_opt_sp])
    apply wpsimp
    apply (clarsimp simp: schedulable_def opt_pred_def opt_map_def obj_at_def is_tcb_def tcbs_of_kh_def
                   split: option.splits)
   apply wpsimp
    apply (clarsimp simp: schedulable_def opt_pred_def opt_map_def obj_at_def is_tcb_def tcbs_of_kh_def
                   split: option.splits)
  apply (rule corres_symb_exec_l[rotated, OF _ gets_sp])
    apply wpsimp
   apply (clarsimp simp: schedulable_def get_tcb_def vs_all_heap_simps)
  apply (rule corres_symb_exec_l[rotated, OF _ assert_sp]; wpsimp)
  apply (rule corres_guard_imp)
    apply (rule switchToThread_corres)
   apply (fastforce dest: invs_sym_refs simp: schedulable_def2)
  apply fastforce
  done

lemma prepareNextDomain_corres[corres]:
  "corres dc (valid_arch_state and pspace_aligned and pspace_distinct)
             (pspace_aligned' and pspace_distinct' and no_0_obj')
             arch_prepare_next_domain prepareNextDomain"
  by (clarsimp simp: arch_prepare_next_domain_def prepareNextDomain_def)

crunch prepareNextDomain
  for invs'[wp]: invs'
  and nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"

end (* Arch *)

interpretation Schedule_R_2?: Schedule_R_2
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Schedule_R_2_assms)?)?)
qed

context Arch begin arch_global_naming

named_theorems Schedule_R_3_assms

lemma scheduleChooseNewThread_fragment_corres:
  "corres dc (invs and valid_ready_qs and ready_or_release
              and (\<lambda>s. scheduler_action s = choose_new_thread))
             (invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread))
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
                    wp: nextDomain_invs')
   apply (auto simp: valid_sched_def invs'_def)
  done

lemma scheduleChooseNewThread_corres[Schedule_R_3_assms]:
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

lemma scheduleChooseNewThread_invs'[Schedule_R_3_assms]:
  "scheduleChooseNewThread \<lbrace>invs'\<rbrace>"
  unfolding scheduleChooseNewThread_def prepareNextDomain_def
  apply (wpsimp wp: ssa_invs' chooseThread_invs'' chooseThread_invs'' nextDomain_invs')
  done

lemma stt_nosch:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
   switchToThread t
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  by (simp add: Thread_H.switchToThread_def RISCV64_H.switchToThread_def storeWordUser_def)
     (wpsimp wp: setCurThread_nosch hoare_drop_imp)

lemma stit_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
   switchToIdleThread
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def
                   RISCV64_H.switchToIdleThread_def storeWordUser_def)
  apply (wp setCurThread_nosch | simp add: getIdleThread_def)+
  done

end (* Arch *)

interpretation Schedule_R_3?: Schedule_R_3
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Schedule_R_3_assms)?)?)
qed

end
