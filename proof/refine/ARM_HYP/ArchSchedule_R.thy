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

lemma vs_refs_pages_vcpu:
  "vs_refs_pages (ArchObj (VCPU vcpu)) = {}"
  by (simp add: vs_refs_pages_def)

lemma vs_lookup_pages1_vcpu_update:
  "typ_at (AArch AVCPU) vcpuPtr s \<Longrightarrow>
   vs_lookup_pages1 (s\<lparr>kheap := (kheap s)(vcpuPtr \<mapsto> ArchObj (VCPU vcpu))\<rparr>) = vs_lookup_pages1 s"
  by (clarsimp intro!: set_eqI simp: vs_lookup_pages1_def vs_refs_pages_vcpu obj_at_def)

lemma vs_lookup_pages_vcpu_update:
  "typ_at (AArch AVCPU) vcpuPtr s \<Longrightarrow>
   vs_lookup_pages (s\<lparr>kheap := (kheap s)(vcpuPtr \<mapsto> ArchObj (VCPU vcpu))\<rparr>) = vs_lookup_pages s"
  by (clarsimp simp: vs_lookup_pages_def vs_lookup_pages1_vcpu_update)

lemma valid_vs_lookup_vcpu_update:
  "typ_at (AArch AVCPU) vcpuPtr s \<Longrightarrow>
   valid_vs_lookup (s\<lparr>kheap := (kheap s)(vcpuPtr \<mapsto> ArchObj (VCPU vcpu))\<rparr>) = valid_vs_lookup s"
  apply (clarsimp simp: valid_vs_lookup_def caps_of_state_VCPU_update)
  apply (rule all_cong1)
  apply (rule all_cong1)
  apply (rule imp_cong)
   apply (simp add: vs_lookup_pages_vcpu_update)
  apply simp
  done

lemma set_vpcu_valid_vs_lookup[wp]:
  "set_vcpu vcpuPtr vcpu \<lbrace>\<lambda>s. P (valid_vs_lookup s)\<rbrace>"
  by (wpsimp wp: set_vcpu_wp simp: valid_vs_lookup_vcpu_update)

lemma vs_lookup_pages1_current_vcpu:
  "vs_lookup_pages1 (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := Some x\<rparr>\<rparr>)
   = vs_lookup_pages1 s"
  by (clarsimp simp: vs_lookup_pages1_def)

lemma vs_lookup_pages_current_vcpu:
  "vs_lookup_pages (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := Some x\<rparr>\<rparr>)
   = vs_lookup_pages s"
  by (clarsimp simp: vs_lookup_pages_def vs_lookup_pages1_current_vcpu)

lemma valid_vs_lookup_current_vcpu:
  "valid_vs_lookup (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := Some x\<rparr>\<rparr>)
   = valid_vs_lookup s"
  apply (clarsimp simp: valid_vs_lookup_def caps_of_state_VCPU_update)
  apply (rule all_cong1)
  apply (rule all_cong1)
  apply (rule imp_cong)
   apply (simp add: vs_lookup_pages_current_vcpu)
  apply simp
  done

crunch vcpu_switch
  for valid_vs_lookup[wp]: "\<lambda>s. P (valid_vs_lookup s)"
  (simp: crunch_simps valid_vs_lookup_current_vcpu wp: crunch_wps)

(* FIXME ARM_HYP: move *)
lemma ko_vcpu_cross:
  "\<lbrakk> ko_at (ArchObj (VCPU vcpu)) p s; pspace_aligned s; pspace_distinct s; (s, s') \<in> state_relation \<rbrakk>
  \<Longrightarrow> \<exists>vcpu'. ko_at' vcpu' p s' \<and> vcpu_relation vcpu vcpu'"
  apply (frule (1) pspace_distinct_cross, fastforce simp: state_relation_def)
  apply (frule pspace_aligned_cross, fastforce simp: state_relation_def)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: state_relation_def pspace_relation_def obj_at_def)
  apply (drule bspec, fastforce)
  apply (clarsimp simp: other_aobj_relation_def
                  split: kernel_object.splits arch_kernel_object.splits)
  apply (prop_tac "ksPSpace s' p \<noteq> None")
   apply (prop_tac "p \<in> pspace_dom (kheap s)")
    apply (fastforce intro!: set_mp[OF pspace_dom_dom])
   apply fastforce
  apply (fastforce simp: obj_at'_def objBits_simps dest: pspace_alignedD pspace_distinctD')
  done

(* FIXME ARM_HYP: move *)
lemma vcpu_at_cross:
  "\<lbrakk> vcpu_at p s; pspace_aligned s; pspace_distinct s; (s, s') \<in> state_relation \<rbrakk>
   \<Longrightarrow> vcpu_at' p s'"
  apply (drule vcpu_at_ko, clarsimp)
  apply (drule (3) ko_vcpu_cross)
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def)
  done

crunch tcbSchedAppend, tcbSchedDequeue, tcbSchedEnqueue
  for state_hyp_refs_of'[Schedule_R_assms, wp]: "\<lambda>s. P (state_hyp_refs_of' s)"
  (simp: unless_def crunch_simps obj_at'_def wp: getObject_tcb_wp)

lemma vcpuSwitch_typ_at'[wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> vcpuSwitch param_a \<lbrace>\<lambda>_ s. P (typ_at' T p s) \<rbrace>"
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | assumption)+

lemma arch_switch_thread_tcb_at'[wp]:
  "\<lbrace>tcb_at' t\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  by (unfold ARM_HYP_H.switchToThread_def, wp typ_at_lift_tcb')

crunch setVMRoot, vcpuSwitch
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t'"
  (simp: crunch_simps wp: crunch_wps)

crunch Arch.switchToThread
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"

lemma Arch_switchToThread_pred_tcb'[wp]:
  "Arch.switchToThread t \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
proof -
  have pos: "\<And>P t t'. Arch.switchToThread t \<lbrace>pred_tcb_at' proj P t'\<rbrace>"
    by (wpsimp simp: ARM_HYP_H.switchToThread_def)
  show ?thesis
    apply (rule P_bool_lift [OF pos])
    by (rule lift_neg_pred_tcb_at' [OF ArchThreadDecls_H_ARM_HYP_H_switchToThread_typ_at' pos])
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
              and (\<lambda>s. sym_refs (state_hyp_refs_of s))
              and valid_vs_lookup and valid_vspace_objs and tcb_at t)
             (no_0_obj')
             (arch_switch_to_thread t) (Arch.switchToThread t)"
  unfolding arch_switch_to_thread_def ARM_HYP_H.switchToThread_def
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest: pspace_distinct_cross)
  apply (corres corres: getObject_TCB_corres vcpuSwitch_corres' setVMRoot_corres
                simp: ARM_HYP.clearExMonitor_def
                term_simp: tcb_relation_def arch_tcb_relation_def)
       apply (wpsimp wp: vcpu_switch_pred_tcb_at getObject_tcb_wp simp: tcb_at_st_tcb_at)+
   apply (clarsimp simp: valid_arch_state_def st_tcb_at_def obj_at_def)
   apply (rule conjI)
    apply clarsimp
    apply (erule (1) valid_objsE)
    apply (clarsimp simp: get_tcb_ko_at[unfolded obj_at_def])
    apply (clarsimp simp: valid_obj_def valid_tcb_def valid_arch_tcb_def obj_at_def)
   apply (rule conjI)
    apply (clarsimp simp: obj_at_def is_vcpu_def)
   apply (fastforce dest!: get_tcb_ko_atI sym_refs_VCPU_hyp_live[rotated -1] simp: obj_at_def)
  using obj_at_ko_at'
  apply blast
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

crunch vcpu_update, vgic_update, vcpu_disable, vcpu_restore, vcpu_enable
  for valid_asid_map[wp]: valid_asid_map
  (simp: crunch_simps wp: crunch_wps)

lemma arch_switchToIdleThread_corres:
  "corres dc
          (valid_arch_state and pspace_aligned and pspace_distinct and valid_idle
           and valid_objs and valid_vspace_objs and valid_asid_map and valid_arch_caps)
          (no_0_obj')
          arch_switch_to_idle_thread Arch.switchToIdleThread"
  unfolding arch_switch_to_idle_thread_def switchToIdleThread_def
  apply (corres corres: vcpuSwitch_corres[where vcpu=None, simplified] setVMRoot_corres
                        getIdleThread_corres
                wp: tcb_at_idle_thread_lift tcb_at'_ksIdleThread_lift vcpuSwitch_it'
         | simp)+
   apply (clarsimp simp: valid_idle_tcb_at)
   apply (fastforce simp: valid_arch_state_def obj_at_def is_vcpu_def valid_arch_caps_def)
  apply clarsimp
  apply (rule vcpu_at_cross; assumption?)
  apply (clarsimp simp: valid_arch_state_def is_vcpu_def obj_at_def state_relation_def
                        arch_state_relation_def)
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
  "\<lbrace>invs'\<rbrace> doMachineOp ARM_HYP.clearExMonitor \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq)
   apply (simp add: no_irq_clearExMonitor)
  apply (clarsimp simp: ARM_HYP.clearExMonitor_def machine_op_lift_def
                        in_monad select_f_def)
  done

lemma Arch_switchToThread_invs[Schedule_R_assms, wp]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (wpsimp simp: ARM_HYP_H.switchToThread_def wp: getObject_tcb_hyp_sym_refs)

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
    "\<forall>tcb. atcbVCPUPtr (tcbArch (F tcb)) = atcbVCPUPtr (tcbArch tcb)"
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
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp ARM_HYP.clearExMonitor \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wp dmo_invs_no_cicd' no_irq)
   apply (simp add: no_irq_clearExMonitor)
  apply (clarsimp simp: ARM_HYP.clearExMonitor_def machine_op_lift_def
                        in_monad select_f_def)
  done

lemma Arch_switchToThread_invs_no_cicd'[Schedule_R_assms]:
  "Arch.switchToThread t \<lbrace>invs_no_cicd'\<rbrace>"
  by (wpsimp wp: getObject_tcb_hyp_sym_refs setVMRoot_invs_no_cicd' simp: ARM_HYP_H.switchToThread_def)
     (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def)

lemma setVCPU_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> setObject p' (v::vcpu) \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  by (wp ex_nonz_cap_to_pres')

crunch
  vcpuDisable, vcpuRestore, vcpuEnable, vcpuSaveRegRange, vgicUpdateLR, vcpuSave, vcpuSwitch
  for cap_to'[wp]: "ex_nonz_cap_to' p"
  (ignore: doMachineOp wp: crunch_wps)

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
  by (wpsimp wp: setCurThread_invs_no_cicd'_idle_thread setVMRoot_invs_no_cicd' vcpuSwitch_it')

crunch Arch.switchToIdleThread
  for obj_at'[wp]: "obj_at' (P :: ('a :: no_vcpu) \<Rightarrow> bool) t"

lemmas Arch_switchToIdleThread_not_queued'[Schedule_R_assms] =
  ArchThreadDecls_H_ARM_HYP_H_switchToIdleThread_obj_at'[where P="Not \<circ> tcbQueued"]

lemmas Arch_switchToIdleThread_tcbState[Schedule_R_assms] =
  ArchThreadDecls_H_ARM_HYP_H_switchToIdleThread_obj_at'[where P="P \<circ> tcbState" for P]

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

lemma vcpuInvalidateActive_corres[corres]:
  "corres dc \<top> no_0_obj' vcpu_invalidate_active vcpuInvalidateActive"
  unfolding vcpuInvalidateActive_def vcpu_invalidate_active_def
  apply (corresKsimp  corres: vcpuDisable_corres
                    corresK: corresK_modifyT
                       simp: modifyArchState_def)
  apply (clarsimp simp: state_relation_def arch_state_relation_def)
  done

lemma vcpuFlush_corres[corres]:
  "corres dc valid_arch_state (pspace_aligned' and pspace_distinct' and no_0_obj')
     vcpu_flush vcpuFlush"
  unfolding vcpu_flush_def vcpuFlush_def
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF corres_gets_current_vcpu])
      apply clarsimp
      apply (rule corres_when, simp)
      apply (rule corres_split[OF vcpuSave_corres])
        apply (rule vcpuInvalidateActive_corres)
       apply wpsimp+
   apply (clarsimp simp: valid_arch_state_def obj_at_def is_vcpu_def)
  apply (clarsimp simp: state_relation_def arch_state_relation_def)
  apply (rule aligned_distinct_relation_vcpu_atI'; assumption?)
  apply (clarsimp simp: valid_arch_state_def obj_at_def is_vcpu_def)
  done

lemma vcpuFlush_invs'[wp]:
  "vcpuFlush \<lbrace>invs'\<rbrace>"
  unfolding vcpuFlush_def
  by wpsimp

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
  "corres dc (invs and valid_domain_list and valid_sched and
              (\<lambda>s. scheduler_action s = choose_new_thread))
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
                    wp: nextDomain_invs_no_cicd' valid_domain_list_lift)
   apply (auto simp: valid_sched_def invs'_def valid_state'_def all_invs_but_ct_idle_or_in_cur_domain'_def)
  done

lemma scheduleChooseNewThread_corres[Schedule_R_3_assms]:
  "corres dc
     (\<lambda>s. invs s \<and> valid_domain_list s \<and> valid_sched s \<and> scheduler_action s = choose_new_thread)
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
  by (simp add: Thread_H.switchToThread_def ARM_HYP_H.switchToThread_def storeWordUser_def)
     (wpsimp wp: setCurThread_nosch hoare_drop_imp)

lemma stit_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
   switchToIdleThread
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def
                   ARM_HYP_H.switchToIdleThread_def storeWordUser_def)
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
