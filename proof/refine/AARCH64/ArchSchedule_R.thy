(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchSchedule_R
imports Schedule_R
begin

context Arch begin arch_global_naming

named_theorems Schedule_R_assms

lemma vs_lookup_pages_vcpu_update:
  "typ_at (AArch AVCPU) vcpuPtr s \<Longrightarrow>
   vs_lookup_target level asid vref (s\<lparr>kheap := (kheap s)(vcpuPtr \<mapsto> ArchObj (VCPU vcpu))\<rparr>) =
   vs_lookup_target level asid vref s"
  unfolding vs_lookup_target_def vs_lookup_slot_def vs_lookup_table_def
  apply (prop_tac "asid_pools_of s vcpuPtr = None", clarsimp simp: opt_map_def obj_at_def)
  apply (prop_tac "pts_of s vcpuPtr = None", clarsimp simp: opt_map_def obj_at_def)
  apply (fastforce simp: obind_assoc intro!: obind_eqI)
  done

lemma valid_vs_lookup_vcpu_update:
  "typ_at (AArch AVCPU) vcpuPtr s \<Longrightarrow>
   valid_vs_lookup (s\<lparr>kheap := (kheap s)(vcpuPtr \<mapsto> ArchObj (VCPU vcpu))\<rparr>) = valid_vs_lookup s"
  by (clarsimp simp: valid_vs_lookup_def caps_of_state_VCPU_update vs_lookup_pages_vcpu_update)

lemma set_vpcu_valid_vs_lookup[wp]:
  "set_vcpu vcpuPtr vcpu \<lbrace>\<lambda>s. P (valid_vs_lookup s)\<rbrace>"
  by (wpsimp wp: set_vcpu_wp simp: valid_vs_lookup_vcpu_update)

lemma set_vcpu_vmid_inv[wp]:
  "set_vcpu vcpuPtr vcpu \<lbrace>\<lambda>s. P (vmid_inv s)\<rbrace>"
  unfolding vmid_inv_def
  by (wp_pre, wps, wpsimp, simp)

lemma vmid_inv_cur_vcpu[simp]:
  "vmid_inv (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := x\<rparr>\<rparr>) = vmid_inv s"
  by (simp add: vmid_inv_def)

lemma set_vcpu_valid_asid_table[wp]:
  "set_vcpu ptr vcpu \<lbrace>valid_asid_table\<rbrace>"
  apply (wpsimp wp: set_vcpu_wp)
  apply (prop_tac "asid_pools_of s ptr = None")
   apply (clarsimp simp: obj_at_def opt_map_def)
  apply simp
  done

crunch vcpu_switch
  for valid_vs_lookup[wp]: "\<lambda>s. P (valid_vs_lookup s)"
  and vmid_inv[wp]: vmid_inv
  and valid_vmid_table[wp]: valid_vmid_table
  and valid_asid_table[wp]: valid_asid_table
  and global_pt[wp]: "\<lambda>s. P (global_pt s)"
  and valid_uses[wp]: valid_uses
  (simp: crunch_simps wp: crunch_wps)

lemma vcpu_switch_valid_global_arch_objs[wp]:
  "vcpu_switch v \<lbrace>valid_global_arch_objs\<rbrace>"
  by (wp valid_global_arch_objs_lift)

crunch set_vm_root
  for pspace_distinct[wp]: pspace_distinct
  (simp: crunch_simps)

(* FIXME AARCH64: move *)
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

(* FIXME AARCH64: move *)
lemma vcpu_at_cross:
  "\<lbrakk> vcpu_at p s; pspace_aligned s; pspace_distinct s; (s, s') \<in> state_relation \<rbrakk>
   \<Longrightarrow> vcpu_at' p s'"
  apply (drule vcpu_at_ko, clarsimp)
  apply (drule (3) ko_vcpu_cross)
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def)
  done

lemma gets_armKSCurFPUOwner_corres[corres]:
  "corres (=) \<top> \<top>
          (gets (arm_current_fpu_owner \<circ> arch_state)) (gets (armKSCurFPUOwner \<circ> ksArchState))"
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
    apply (clarsimp simp: ghost_relation_of_heap pt_types_of_heap_def aobj_of_simps)
    apply (subst fun_upd_idem)
     apply (drule_tac s="pts_of a ||> pt_type" in sym)
     apply (clarsimp simp: aobj_of_simps opt_map_def)
    apply clarsimp
   apply (clarsimp simp: swp_def cte_wp_at_after_update' obj_at_def simp del: same_caps_simps)
  apply (clarsimp simp: caps_of_state_fun_upd obj_at_def simp del: same_caps_simps)
  done

lemma set_arm_current_fpu_owner_corres[corres]:
  "corres dc (pspace_aligned and pspace_distinct and valid_cur_fpu and none_top tcb_at new_owner) \<top>
             (set_arm_current_fpu_owner new_owner) (modifyArchState (armKSCurFPUOwner_update (\<lambda>_. new_owner)))"
  unfolding set_arm_current_fpu_owner_def modifyArchState_def maybeM_def
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
  "fpuOwner_asrt \<equiv> \<lambda>s'. opt_tcb_at' (armKSCurFPUOwner (ksArchState s')) s'"

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

crunch set_vm_root, vcpu_switch
  for valid_cur_fpu[wp]: valid_cur_fpu
  (simp: crunch_simps wp: crunch_wps)

crunch tcbSchedAppend, tcbSchedDequeue, tcbSchedEnqueue
  for state_hyp_refs_of'[Schedule_R_assms, wp]: "\<lambda>s. P (state_hyp_refs_of' s)"
  (simp: unless_def crunch_simps obj_at'_def wp: getObject_tcb_wp)

crunch vcpuEnable, vcpuDisable, vcpuSave, vcpuRestore, lazyFpuRestore
  for typ_at' [wp]: "\<lambda>s. P (typ_at' T p s)"
  (simp: crunch_simps
     wp: crunch_wps getObject_inv loadObject_default_inv)

lemma vcpuSwitch_typ_at'[wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> vcpuSwitch param_a \<lbrace>\<lambda>_ s. P (typ_at' T p s) \<rbrace>"
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | assumption)+

lemma arch_switch_thread_tcb_at'[wp]:
  "\<lbrace>tcb_at' t\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  by (unfold AARCH64_H.switchToThread_def, wp typ_at_lift_tcb')

lemma updateASIDPoolEntry_pred_tcb_at'[wp]:
  "updateASIDPoolEntry f asid \<lbrace>pred_tcb_at' proj P t'\<rbrace>"
  unfolding updateASIDPoolEntry_def getPoolPtr_def
  by (wpsimp wp: setASIDPool_pred_tcb_at' getASID_wp)

crunch updateASIDPoolEntry
  for tcbs_of'[wp]: "\<lambda>s. P (tcbs_of' s)"
  (wp: getASID_wp crunch_wps)

crunch setVMRoot, vcpuSwitch, lazyFpuRestore
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t'"
  (simp: crunch_simps wp: crunch_wps)

crunch Arch.switchToThread
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"

lemma Arch_switchToThread_pred_tcb'[wp]:
  "Arch.switchToThread t \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
proof -
  have pos: "\<And>P t t'. Arch.switchToThread t \<lbrace>pred_tcb_at' proj P t'\<rbrace>"
    by (wpsimp simp: AARCH64_H.switchToThread_def)
  show ?thesis
    apply (rule P_bool_lift [OF pos])
    by (rule lift_neg_pred_tcb_at' [OF ArchThreadDecls_H_AARCH64_H_switchToThread_typ_at' pos])
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
              and valid_vspace_objs and pspace_in_kernel_window and valid_cur_fpu and tcb_at t)
             (no_0_obj')
             (arch_switch_to_thread t) (Arch.switchToThread t)"
  unfolding arch_switch_to_thread_def AARCH64_H.switchToThread_def
  apply (corres corres: getObject_TCB_corres vcpuSwitch_corres
                term_simp: tcb_relation_def arch_tcb_relation_def)
       apply (wpsimp wp: vcpu_switch_pred_tcb_at getObject_tcb_wp simp: tcb_at_st_tcb_at)+
   apply (clarsimp simp: valid_arch_state_def st_tcb_at_def obj_at_def get_tcb_def)
   apply (rule conjI)
    apply clarsimp
    apply (erule (1) valid_objsE)
    apply (clarsimp simp: valid_obj_def valid_tcb_def valid_arch_tcb_def obj_at_def)
   apply (clarsimp simp: cur_vcpu_def in_omonad)
  apply normalise_obj_at'
  apply (clarsimp simp: st_tcb_at_def obj_at_def is_tcb)
  apply (frule (2) ko_tcb_cross[rotated], simp add: obj_at_def)
  apply normalise_obj_at'
  apply (rule conjI; clarsimp)
   apply (rule vcpu_at_cross; assumption?)
   apply (erule (1) valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_tcb_def valid_arch_tcb_def  tcb_relation_def
                         arch_tcb_relation_def)
  apply (rule vcpu_at_cross; assumption?)
  apply (prop_tac "cur_vcpu s", clarsimp simp: valid_arch_state_def)
  apply (clarsimp simp: state_relation_def arch_state_relation_def cur_vcpu_def in_omonad obj_at_def)
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

crunch vcpu_update, vgic_update, vcpu_disable, vcpu_restore, vcpu_enable
  for valid_asid_map[wp]: valid_asid_map
  (simp: crunch_simps wp: crunch_wps)

lemma setGlobalUserVSpace_corres[corres]:
  "corres dc valid_global_arch_objs \<top> set_global_user_vspace setGlobalUserVSpace"
  unfolding set_global_user_vspace_def setGlobalUserVSpace_def
  apply (subst o_def) (* unfold fun_comp on abstract side only to get global_pt abbrev *)
  apply corres
  done

lemma arch_switchToIdleThread_corres:
  "corres dc
          (valid_arch_state and pspace_aligned and pspace_distinct)
          (no_0_obj')
          arch_switch_to_idle_thread Arch.switchToIdleThread"
  unfolding arch_switch_to_idle_thread_def switchToIdleThread_def
  apply (corres corres: vcpuSwitch_corres)
   apply (clarsimp simp: valid_arch_state_def cur_vcpu_def in_omonad obj_at_def)
  apply clarsimp
  apply (rule vcpu_at_cross; assumption?)
  apply (clarsimp simp: valid_arch_state_def cur_vcpu_def in_omonad obj_at_def state_relation_def
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

lemma armKSCurFPUOwner_invs'[wp]:
  "modifyArchState (armKSCurFPUOwner_update f) \<lbrace>invs'\<rbrace>"
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
  unfolding AARCH64_H.switchToThread_def by (wpsimp wp: getObject_tcb_hyp_sym_refs)

crunch "Arch.switchToThread"
  for ksCurDomain[Schedule_R_assms, wp]: "\<lambda>s. P (ksCurDomain s)"
  and tcbDomain[Schedule_R_assms, wp]: "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'"
  and tcbState[Schedule_R_assms, wp]: "obj_at' (\<lambda>tcb. P (tcbState tcb)) t'"
  (simp: crunch_simps wp: crunch_wps getASID_wp)

crunch vcpuSwitch, setVMRoot
  for obj_at_tcb'[wp]: "obj_at' (\<lambda>tcb::tcb. P tcb) t"
  (wp: crunch_wps getASID_wp simp: crunch_simps)

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

lemma armKSCurFPUOwner_invs_no_cicd'[wp]:
  "modifyArchState (armKSCurFPUOwner_update f) \<lbrace>invs_no_cicd'\<rbrace>"
  apply (wpsimp simp: modifyArchState_def)
  by (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_machine_state'_def
                     valid_arch_state'_def valid_global_refs'_def global_refs'_def
              split: option.split)

crunch lazyFpuRestore
  for invs_no_cicd'[wp]: invs_no_cicd'
  (ignore: doMachineOp modifyArchState)

lemma Arch_switchToThread_invs_no_cicd'[Schedule_R_assms]:
  "Arch.switchToThread t \<lbrace>invs_no_cicd'\<rbrace>"
  by (wpsimp wp: getObject_tcb_hyp_sym_refs setVMRoot_invs_no_cicd' simp: AARCH64_H.switchToThread_def)
     (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def)

lemma setVCPU_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> setObject p' (v::vcpu) \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  by (wp ex_nonz_cap_to_pres')

crunch
  vcpuDisable, vcpuRestore, vcpuEnable, vcpuSaveRegRange, vgicUpdateLR, vcpuSave, vcpuSwitch
  for cap_to'[wp]: "ex_nonz_cap_to' p"
  (ignore: doMachineOp wp: crunch_wps)

crunch updateASIDPoolEntry
  for cap_to'[wp]: "ex_nonz_cap_to' p"
  (wp: crunch_wps ex_nonz_cap_to_pres' getASID_wp)

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
  by (wpsimp wp: setCurThread_invs_no_cicd'_idle_thread setVMRoot_invs_no_cicd' vcpuSwitch_it')

crunch Arch.switchToIdleThread
  for obj_at'[wp]: "obj_at' (P :: ('a :: no_vcpu) \<Rightarrow> bool) t"

lemmas Arch_switchToIdleThread_not_queued'[Schedule_R_assms] =
  ArchThreadDecls_H_AARCH64_H_switchToIdleThread_obj_at'[where P="Not \<circ> tcbQueued"]

lemmas Arch_switchToIdleThread_tcbState[Schedule_R_assms] =
  ArchThreadDecls_H_AARCH64_H_switchToIdleThread_obj_at'[where P="P \<circ> tcbState" for P]

lemmas [Schedule_R_assms] =
   (* part of DetSchedSchedule_AI_assms but not interfaced (AARCH64 only) *)
   arch_switch_to_thread_valid_idle

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
   apply (clarsimp simp: valid_arch_state_def obj_at_def cur_vcpu_def in_omonad)
  apply (clarsimp simp: state_relation_def arch_state_relation_def)
  apply (rule aligned_distinct_relation_vcpu_atI'; assumption?)
  apply (clarsimp simp: valid_arch_state_def obj_at_def cur_vcpu_def in_omonad)
  done

lemma vcpuFlush_invs'[wp]:
  "vcpuFlush \<lbrace>invs'\<rbrace>"
  unfolding vcpuFlush_def
  by wpsimp

crunch vcpu_flush
  for valid_cur_fpu[wp]: valid_cur_fpu

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
  by (simp add: Thread_H.switchToThread_def AARCH64_H.switchToThread_def storeWordUser_def)
     (wpsimp wp: setCurThread_nosch hoare_drop_imp)

lemma stit_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
   switchToIdleThread
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def
                   AARCH64_H.switchToIdleThread_def storeWordUser_def)
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
