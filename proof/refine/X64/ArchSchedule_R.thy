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

crunch set_vm_root
  for pspace_distinct[wp]: pspace_distinct
  (simp: crunch_simps)

lemma gets_x64KSCurFPUOwner_corres[corres]:
  "corres (=) \<top> \<top>
          (gets (x64_current_fpu_owner \<circ> arch_state)) (gets (x64KSCurFPUOwner \<circ> ksArchState))"
  by (simp add: state_relation_def arch_state_relation_def)

crunch setFPUState
  for (no_fail) no_fail[wp]

lemma saveFpuState_corres[corres]:
  "corres dc (tcb_at t and pspace_aligned and pspace_distinct and (fpu_enabled \<circ> machine_state)) \<top>
             (save_fpu_state t) (saveFpuState t)"
  unfolding save_fpu_state_def saveFpuState_def
  apply (corres corres: corres_machine_op' asUser_corres')
  by (simp add: state_relation_def)

lemma loadFpuState_corres[corres]:
  "corres dc (tcb_at t and pspace_aligned and pspace_distinct and (fpu_enabled \<circ> machine_state)) \<top>
             (load_fpu_state t) (loadFpuState t)"
  unfolding load_fpu_state_def loadFpuState_def
  apply (corres corres: corres_machine_op' asUser_corres' simp: o_def)
  by (simp add: state_relation_def)

lemma set_tcb_cur_fpu_noop:
  "corres dc (pspace_aligned and pspace_distinct and tcb_at t) \<top>
             (arch_thread_set (tcb_cur_fpu_update f) t) (return ())"
  unfolding arch_thread_set_def thread_set_def
  apply (rule corres_cross_over_guard[OF tcb_at_cross]; fastforce?)
  apply (clarsimp simp: corres_underlying_def return_def set_object_def get_object_def in_monad Bex_def
                        obj_at_def obj_at'_def is_tcb get_tcb_rev)
  apply (clarsimp simp: state_relation_def)
  apply safe
     apply (frule (2) pspace_relation_tcb_relation)
     apply (clarsimp simp: pspace_relation_update_abstract_tcb tcb_relation_def arch_tcb_relation_def)
    apply (clarsimp simp: ghost_relation_of_heap)
   apply (clarsimp simp: swp_def cte_wp_at_after_update' obj_at_def simp del: same_caps_simps)
  apply (clarsimp simp: caps_of_state_fun_upd obj_at_def simp del: same_caps_simps)
  done

lemma set_x64_current_fpu_owner_corres[corres]:
  "corres dc (pspace_aligned and pspace_distinct and valid_cur_fpu and none_top tcb_at new_owner) \<top>
             (set_x64_current_fpu_owner new_owner) (modifyArchState (x64KSCurFPUOwner_update (\<lambda>_. new_owner)))"
  unfolding set_x64_current_fpu_owner_def modifyArchState_def maybeM_def
  apply corres_pre
  apply (rule corres_underlying_gets_pre_lhs)
  apply (rule corres_add_noop_rhs)
  apply (corres_split; clarsimp?)
       apply (corres_cases; corres corres: set_tcb_cur_fpu_noop)
      apply (rule corres_add_noop_rhs2)
      apply (rule corres_split)
         apply (corres corres: corres_modify_tivial) \<comment> \<open>FIXME: typo in rule name\<close>
         apply (clarsimp simp: state_relation_def arch_state_relation_def)
        apply (corres_cases; corres corres: set_tcb_cur_fpu_noop)
       apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)+
   apply (auto simp: current_fpu_owner_Some_tcb_at)
  done

lemma enableFpu_fpu_enabled[wp]:
  "\<lbrace>\<top>\<rbrace> enableFpu \<lbrace>\<lambda>_. fpu_enabled\<rbrace>"
  by (wpsimp simp: enableFpu_def)

crunch writeFpuState, readFpuState
  for fpu_enabled[wp]: fpu_enabled

crunch load_fpu_state, save_fpu_state
  for valid_cur_fpu[wp]: valid_cur_fpu
  and fpu_enabled[wp]: "\<lambda>s. fpu_enabled (machine_state s)"
  (wp: dmo_machine_state_lift)

defs fpuOwner_asrt_def:
  "fpuOwner_asrt \<equiv> \<lambda>s'. opt_tcb_at' (x64KSCurFPUOwner (ksArchState s')) s'"

lemma fpuOwner_asrt_cross:
  "\<lbrakk>(s, s') \<in> state_relation; valid_cur_fpu s; pspace_aligned s; pspace_distinct s\<rbrakk> \<Longrightarrow> fpuOwner_asrt s'"
  by (fastforce simp: state_relation_def arch_state_relation_def fpuOwner_asrt_def
              intro!: tcb_at_cross current_fpu_owner_Some_tcb_at)

lemma switchLocalFpuOwner_corres[corres]:
  "corres dc (pspace_aligned and pspace_distinct and valid_cur_fpu and none_top tcb_at new_owner) \<top>
             (switch_local_fpu_owner new_owner) (switchLocalFpuOwner new_owner)"
  unfolding switch_local_fpu_owner_def switchLocalFpuOwner_def maybeM_def
  apply (corres corres: corres_stateAssert_r | corres_cases | clarsimp)+
         apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' dmo_machine_state_lift)+
   apply (auto simp: current_fpu_owner_Some_tcb_at fpuOwner_asrt_cross)
  done

(* FIXME FPU: when the FPU being enabled is properly configurable for the proofs then this should
              have config_HAVE_FPU as a precondition instead of being unfolded. *)
lemma lazyFpuRestore_corres[corres]:
  "corres dc (pspace_aligned and pspace_distinct and valid_cur_fpu and tcb_at t) \<top>
             (lazy_fpu_restore t) (lazyFpuRestore t)"
  unfolding lazy_fpu_restore_def lazyFpuRestore_def
  by (corres corres: threadGet_corres[where r="\<lambda>flags flags'. flags = word_to_tcb_flags flags'"]
          term_simp: tcb_relation_def Kernel_Config.config_HAVE_FPU_def
                 wp: hoare_drop_imps)

crunch set_vm_root
  for x64_current_fpu_owner[wp]: "\<lambda>s. P (x64_current_fpu_owner (arch_state s))"
  and valid_cur_fpu[wp]: valid_cur_fpu
  (simp: crunch_simps wp: crunch_wps valid_cur_fpu_lift_arch)

crunch tcbSchedAppend, tcbSchedDequeue, tcbSchedEnqueue
  for state_hyp_refs_of'[Schedule_R_assms, wp]: "\<lambda>s. P (state_hyp_refs_of' s)"
  (simp: unless_def crunch_simps obj_at'_def wp: getObject_tcb_wp)

crunch setVMRoot, lazyFpuRestore
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t'"
  (simp: crunch_simps wp: crunch_wps)

crunch Arch.switchToThread
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"

lemma Arch_switchToThread_pred_tcb'[wp]:
  "Arch.switchToThread t \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
proof -
  have pos: "\<And>P t t'. Arch.switchToThread t \<lbrace>pred_tcb_at' proj P t'\<rbrace>"
    by (wpsimp simp: X64_H.switchToThread_def)
  show ?thesis
    apply (rule P_bool_lift [OF pos])
    by (rule lift_neg_pred_tcb_at' [OF ArchThreadDecls_H_X64_H_switchToThread_typ_at' pos])
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
  "corres dc (valid_arch_state and valid_objs and valid_asid_map
              and valid_vspace_objs and pspace_aligned and pspace_distinct
              and valid_vs_lookup and valid_global_objs
              and unique_table_refs o caps_of_state
              and valid_cur_fpu and tcb_at t)
             (no_0_obj')
             (arch_switch_to_thread t) (Arch.switchToThread t)"
  unfolding arch_switch_to_thread_def X64_H.switchToThread_def
  by (corres corres: getObject_TCB_corres
             term_simp: tcb_relation_def arch_tcb_relation_def)

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
        (valid_arch_state and valid_objs and valid_asid_map and unique_table_refs \<circ> caps_of_state
         and valid_vs_lookup and valid_global_objs and pspace_aligned and pspace_distinct
         and valid_vspace_objs and valid_idle)
        (no_0_obj')
        arch_switch_to_idle_thread Arch.switchToIdleThread"
  unfolding arch_switch_to_idle_thread_def X64_H.switchToIdleThread_def
  by (corres corres: setVMRoot_corres getIdleThread_corres)
     (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def is_tcb)+

(* use superset of arch_switchToIdleThread_corres preconditions across the architectures as interface *)
lemma arch_switchToIdleThread_corres_interface[Schedule_R_assms]:
  "corres dc
     (valid_arch_state and pspace_aligned and pspace_distinct and valid_asid_map and valid_idle
      and valid_arch_caps and valid_global_objs and valid_vspace_objs and valid_objs)
     (no_0_obj')
     arch_switch_to_idle_thread Arch.switchToIdleThread"
  by (rule corres_guard_imp, rule arch_switchToIdleThread_corres; simp add: valid_arch_caps_def)

lemma threadSet_timeslice_invs[Schedule_R_assms]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> threadSet (tcbTimeSlice_update b) t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (wp threadSet_invs_trivial, simp_all add: inQ_def cong: conj_cong)

lemma armKSCurFPUOwner_invs'[wp]:
  "modifyArchState (x64KSCurFPUOwner_update f) \<lbrace>invs'\<rbrace>"
  apply (wpsimp simp: modifyArchState_def)
  by (clarsimp simp: invs'_def valid_state'_def valid_machine_state'_def
                     ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def
                     valid_arch_state'_def valid_global_refs'_def global_refs'_def
              split: option.split)

crunch loadFpuState, saveFpuState
  for invs'[wp]: invs'
  (ignore: doMachineOp)

lemma switchLocalFpuOwner_invs[wp]:
  "\<lbrace>invs' and opt_tcb_at' newOwner\<rbrace> switchLocalFpuOwner newOwner \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding switchLocalFpuOwner_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' typ_at_lifts simp: fpuOwner_asrt_def)

lemma lazyFpuRestore_invs[wp]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> lazyFpuRestore t \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding lazyFpuRestore_def
  by (wpsimp wp: threadGet_wp)

lemma Arch_switchToThread_invs[Schedule_R_assms, wp]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding X64_H.switchToThread_def by wpsimp

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

lemma armKSCurFPUOwner_invs_no_cicd'[wp]:
  "modifyArchState (x64KSCurFPUOwner_update f) \<lbrace>invs_no_cicd'\<rbrace>"
  apply (wpsimp simp: modifyArchState_def)
  by (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_machine_state'_def
                     valid_arch_state'_def valid_global_refs'_def global_refs'_def
              split: option.split)

crunch lazyFpuRestore
  for invs_no_cicd'[wp]: invs_no_cicd'
  (ignore: doMachineOp modifyArchState)

lemma Arch_switchToThread_invs_no_cicd'[Schedule_R_assms]:
  "Arch.switchToThread t \<lbrace>invs_no_cicd'\<rbrace>"
  by (wpsimp wp: setVMRoot_invs_no_cicd' simp: X64_H.switchToThread_def)

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
  ArchThreadDecls_H_X64_H_switchToIdleThread_obj_at'[where P="Not \<circ> tcbQueued"]

lemmas Arch_switchToIdleThread_tcbState[Schedule_R_assms] =
  ArchThreadDecls_H_X64_H_switchToIdleThread_obj_at'[where P="P \<circ> tcbState" for P]

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
  apply (clarsimp simp: arch_prepare_next_domain_def prepareNextDomain_def)
  by corres

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

crunch lazyFpuRestore
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"

lemma stt_nosch:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
   switchToThread t
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  by (simp add: Thread_H.switchToThread_def X64_H.switchToThread_def storeWordUser_def)
     (wpsimp wp: setCurThread_nosch hoare_drop_imp)

lemma stit_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
   switchToIdleThread
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def
                   X64_H.switchToIdleThread_def storeWordUser_def)
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
