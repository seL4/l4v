(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   AARCH64 VSpace refinement
*)

theory VSpace_R
imports TcbAcc_R
begin

lemma cteCaps_of_ctes_of_lift:
  "(\<And>P. \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. P (cteCaps_of s) \<rbrace> f \<lbrace>\<lambda>_ s. P (cteCaps_of s)\<rbrace>"
  unfolding cteCaps_of_def .

context begin interpretation Arch . (*FIXME: arch-split*)

definition
  "vspace_at_asid' vs asid \<equiv> \<lambda>s. \<exists>ap pool entry.
             armKSASIDTable (ksArchState s) (ucast (asid_high_bits_of (ucast asid))) = Some ap \<and>
             ko_at' (ASIDPool pool) ap s \<and>
             pool (ucast (asid_low_bits_of (ucast asid))) = Some entry \<and>
             apVSpace entry = vs \<and>
             page_table_at' VSRootPT_T vs s \<and>
             gsPTTypes (ksArchState s) vs = Some VSRootPT_T"

lemma findVSpaceForASID_vs_at_wp:
  "\<lbrace>\<lambda>s. \<forall>pm. asid \<noteq> 0 \<and> asid_wf asid \<and> vspace_at_asid' pm asid s \<longrightarrow> P pm s\<rbrace>
    findVSpaceForASID asid
   \<lbrace>P\<rbrace>,-"
  unfolding findVSpaceForASID_def
  apply (wpsimp wp: getASID_wp simp: checkPTAt_def getASIDPoolEntry_def getPoolPtr_def)
  apply (fastforce simp: asid_low_bits_of_def ucast_ucast_a is_down ucast_ucast_mask
                         asid_low_bits_def asidRange_def mask_2pm1[symmetric]
                         le_mask_asidBits_asid_wf vspace_at_asid'_def page_table_at'_def)
  done

crunch findVSpaceForASID, haskell_fail
  for inv[wp]: "P"
  (simp: const_def crunch_simps wp: loadObject_default_inv crunch_wps ignore_del: getObject)

lemma asidBits_asid_bits[simp]:
  "asidBits = asid_bits"
  by (simp add: bit_simps' asid_bits_def asidBits_def)

(* FIXME AARCH64: Added to crunch_param_rules in Crunch_Instances_NonDet as
   trans[OF liftE_bindE return_bind]; move to monad equations instead and give it the name below *)
lemma liftE_return_bindE:
  "liftE (return x) >>=E f = f x"
  by (rule Crunch.crunch_param_rules(8))

crunch getIRQState
  for inv[wp]: P

lemma dmo_invs_no_cicd_lift': (* FIXME AARCH64: move up *)
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace>"
  assumes "\<And>P p. f \<lbrace>\<lambda>s. P (underlying_memory s p)\<rbrace>"
  shows "doMachineOp f \<lbrace>all_invs_but_ct_idle_or_in_cur_domain'\<rbrace>"
  apply (wp dmo_invs_no_cicd' assms)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p" in use_valid,
         rule assms, rule refl)
  apply simp
  done

lemma dmo_invs_lift': (* FIXME AARCH64: move up *)
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace>"
  assumes "\<And>P p. f \<lbrace>\<lambda>s. P (underlying_memory s p)\<rbrace>"
  shows "doMachineOp f \<lbrace>invs'\<rbrace>"
  apply (wp dmo_invs' assms)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p" in use_valid,
         rule assms, rule refl)
  apply simp
  done

lemma dmos_invs_no_cicd'[wp]:
  "doMachineOp isb \<lbrace>invs_no_cicd'\<rbrace>"
  "doMachineOp dsb \<lbrace>invs_no_cicd'\<rbrace>"
  "\<And>w. doMachineOp (setSCTLR w) \<lbrace>invs_no_cicd'\<rbrace>"
  "\<And>w. doMachineOp (set_gic_vcpu_ctrl_hcr w) \<lbrace>invs_no_cicd'\<rbrace>"
  "\<And>w x. doMachineOp (set_gic_vcpu_ctrl_lr w x) \<lbrace>invs_no_cicd'\<rbrace>"
  "\<And>w. doMachineOp (set_gic_vcpu_ctrl_apr w) \<lbrace>invs_no_cicd'\<rbrace>"
  "\<And>w. doMachineOp (set_gic_vcpu_ctrl_vmcr w) \<lbrace>invs_no_cicd'\<rbrace>"
  "\<And>w. doMachineOp (setHCR w) \<lbrace>invs_no_cicd'\<rbrace>"
  "doMachineOp get_gic_vcpu_ctrl_hcr \<lbrace>invs_no_cicd'\<rbrace>"
  "\<And>w. doMachineOp (get_gic_vcpu_ctrl_lr w) \<lbrace>invs_no_cicd'\<rbrace>"
  "doMachineOp get_gic_vcpu_ctrl_apr \<lbrace>invs_no_cicd'\<rbrace>"
  "doMachineOp get_gic_vcpu_ctrl_vmcr \<lbrace>invs_no_cicd'\<rbrace>"
  "doMachineOp enableFpuEL01 \<lbrace>invs_no_cicd'\<rbrace>"
  "\<And>r. doMachineOp (readVCPUHardwareReg r) \<lbrace>invs_no_cicd'\<rbrace>"
  "\<And>r v. doMachineOp (writeVCPUHardwareReg r v) \<lbrace>invs_no_cicd'\<rbrace>"
  "doMachineOp check_export_arch_timer \<lbrace>invs_no_cicd'\<rbrace>"
  by (wp dmo_invs_no_cicd_lift')+

lemma dmos_invs'[wp]:
  "doMachineOp isb \<lbrace>invs'\<rbrace>"
  "doMachineOp dsb \<lbrace>invs'\<rbrace>"
  "\<And>w. doMachineOp (setSCTLR w) \<lbrace>invs'\<rbrace>"
  "\<And>w. doMachineOp (set_gic_vcpu_ctrl_hcr w) \<lbrace>invs'\<rbrace>"
  "\<And>w x. doMachineOp (set_gic_vcpu_ctrl_lr w x) \<lbrace>invs'\<rbrace>"
  "\<And>w. doMachineOp (set_gic_vcpu_ctrl_apr w) \<lbrace>invs'\<rbrace>"
  "\<And>w. doMachineOp (set_gic_vcpu_ctrl_vmcr w) \<lbrace>invs'\<rbrace>"
  "\<And>w. doMachineOp (setHCR w) \<lbrace>invs'\<rbrace>"
  "doMachineOp get_gic_vcpu_ctrl_hcr \<lbrace>invs'\<rbrace>"
  "\<And>w. doMachineOp (get_gic_vcpu_ctrl_lr w) \<lbrace>invs'\<rbrace>"
  "doMachineOp get_gic_vcpu_ctrl_apr \<lbrace>invs'\<rbrace>"
  "doMachineOp get_gic_vcpu_ctrl_vmcr \<lbrace>invs'\<rbrace>"
  "doMachineOp enableFpuEL01 \<lbrace>invs'\<rbrace>"
  "\<And>r. doMachineOp (readVCPUHardwareReg r) \<lbrace>invs'\<rbrace>"
  "\<And>r v. doMachineOp (writeVCPUHardwareReg r v) \<lbrace>invs'\<rbrace>"
  "doMachineOp check_export_arch_timer \<lbrace>invs'\<rbrace>"
  by (wp dmo_invs_lift')+

lemma valid_irq_node_lift_asm:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (irq_node' s)\<rbrace> f \<lbrace>\<lambda>rv s. P (irq_node' s)\<rbrace>"
  assumes y: "\<And>p. \<lbrace>real_cte_at' p and Q\<rbrace> f \<lbrace>\<lambda>rv. real_cte_at' p\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_irq_node' (irq_node' s) s \<and> Q s\<rbrace> f \<lbrace>\<lambda>rv s. valid_irq_node' (irq_node' s) s\<rbrace>"
  apply (simp add: valid_irq_node'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF x])
   apply (wp hoare_vcg_all_lift y)
  apply simp
  done

lemma isIRQActive_corres:
  "corres (=) \<top> \<top> (is_irq_active irqVTimerEvent) (isIRQActive irqVTimerEvent)"
  apply (clarsimp simp: isIRQActive_def getIRQState_def is_irq_active_def get_irq_state_def)
  apply (clarsimp simp: is_irq_active_def isIRQActive_def
                        get_irq_state_def irq_state_relation_def
                        getIRQState_def getInterruptState_def
                        state_relation_def interrupt_state_relation_def)
  apply (fastforce split: irq_state.splits irqstate.splits)
  done

lemma getIRQState_wp:
  "\<lbrace>\<lambda>s. P (intStateIRQTable (ksInterruptState s) irq) s \<rbrace> getIRQState irq \<lbrace>\<lambda>rv s. P rv s\<rbrace>"
  unfolding getIRQState_def getInterruptState_def
  by (wpsimp simp: comp_def)

lemma maskInterrupt_irq_states':
  "\<lbrace>valid_irq_states'
    and (\<lambda>s. \<not>b \<longrightarrow> intStateIRQTable (ksInterruptState s) irq \<noteq> irqstate.IRQInactive)\<rbrace>
   doMachineOp (maskInterrupt b irq)
   \<lbrace>\<lambda>rv. valid_irq_states'\<rbrace>"
  by (wpsimp wp: dmo_maskInterrupt)
     (auto simp add: valid_irq_states_def valid_irq_masks'_def)

crunch storeWordUser
  for ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
crunch asUser
  for ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps simp: crunch_simps)
crunch asUser
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
  (wp: crunch_wps simp: crunch_simps)

lemma maskInterrupt_invs':
  "\<lbrace>invs'
    and (\<lambda>s. \<not>b \<longrightarrow> intStateIRQTable (ksInterruptState s) irq \<noteq> irqstate.IRQInactive)\<rbrace>
   doMachineOp (maskInterrupt b irq)
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
   by (wpsimp wp: maskInterrupt_irq_states' dmo_maskInterrupt simp: invs'_def valid_state'_def)
      (auto simp: valid_irq_states_def valid_irq_masks'_def valid_machine_state'_def
                  ct_not_inQ_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)

lemma dmo_machine_op_lift_invs'[wp]:
  "doMachineOp (machine_op_lift f) \<lbrace>invs'\<rbrace>"
  by (wpsimp wp: dmo_invs' simp: machine_op_lift_def in_monad machine_rest_lift_def select_f_def)

lemma dmo'_gets_wp:
  "\<lbrace>\<lambda>s. Q (f (ksMachineState s)) s\<rbrace> doMachineOp (gets f) \<lbrace>Q\<rbrace>"
  unfolding doMachineOp_def by (wpsimp simp: in_monad)

lemma maskInterrupt_invs_no_cicd':
  "\<lbrace>invs_no_cicd'
    and (\<lambda>s. \<not>b \<longrightarrow> intStateIRQTable (ksInterruptState s) irq \<noteq> irqstate.IRQInactive)\<rbrace>
   doMachineOp (maskInterrupt b irq)
   \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  by (wpsimp wp: maskInterrupt_irq_states' dmo_maskInterrupt simp: invs_no_cicd'_def)
     (auto simp: valid_irq_states_def valid_irq_masks'_def valid_machine_state'_def
                 ct_not_inQ_def)

(* FIXME AARCH64: this is a big block of VCPU-related lemmas in an attempt to consolidate them;
                  there may be an opportunity to factor most of these out into a separate theory *)
(* setObject for VCPU invariant preservation *)

lemma setObject_vcpu_cur_domain[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_ct[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_it[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_sched[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_L1[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_L2[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_ksInt[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_ksArch[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_gs[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (gsMaxObjectSize s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_maschine_state[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_ksDomSchedule[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_ksDomScheduleIdx[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_gsUntypedZeroRanges[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (gsUntypedZeroRanges s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)


crunch vcpuEnable, vcpuSave, vcpuDisable, vcpuRestore
  for pspace_aligned'[wp]: pspace_aligned'
  (simp: crunch_simps wp: crunch_wps getObject_inv_vcpu loadObject_default_inv)

lemma vcpuSwitch_aligned'[wp]: "\<lbrace>pspace_aligned'\<rbrace> vcpuSwitch param_a \<lbrace>\<lambda>_. pspace_aligned'\<rbrace>"
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | assumption)+

crunch vcpuEnable, vcpuSave, vcpuDisable, vcpuRestore
  for pspace_distinct'[wp]: pspace_distinct'
  (simp: crunch_simps wp: crunch_wps getObject_inv_vcpu loadObject_default_inv)

lemma vcpuSwitch_distinct'[wp]: "\<lbrace>pspace_distinct'\<rbrace> vcpuSwitch param_a \<lbrace>\<lambda>_. pspace_distinct'\<rbrace>"
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | assumption)+

lemma setObject_vcpu_ctes_of[wp]:
  "\<lbrace> \<lambda>s. P (ctes_of s)\<rbrace> setObject p (t :: vcpu) \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>"
  apply (rule ctes_of_from_cte_wp_at[where Q="\<top>", simplified])
  apply (wp setObject_cte_wp_at2'[where Q="\<top>"])
    apply (clarsimp simp: updateObject_default_def in_monad projectKO_opts_defs)
   apply (rule equals0I)
   apply (clarsimp simp: updateObject_default_def in_monad)
  apply simp
  done

lemma setObject_vcpu_untyped_ranges_zero'[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>untyped_ranges_zero'\<rbrace>"
  by (rule hoare_lift_Pf[where f=cteCaps_of]; wp cteCaps_of_ctes_of_lift)

lemma setVCPU_if_live[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> (live' (injectKO vcpu) \<longrightarrow> ex_nonz_cap_to' v s)\<rbrace>
   setObject v (vcpu::vcpu) \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (wpsimp wp: setObject_iflive' [where P=\<top>]
         | simp add: objBits_simps vcpuBits_def pageBits_def)+
    apply (clarsimp simp: updateObject_default_def in_monad)
   apply (clarsimp simp: updateObject_default_def in_monad bind_def)
  apply simp
  done

lemma setVCPU_if_unsafe[wp]:
  "setObject v (vcpu::vcpu) \<lbrace>if_unsafe_then_cap'\<rbrace>"
  apply (wp setObject_ifunsafe')
     apply (clarsimp simp: updateObject_default_def in_monad)
    apply (clarsimp simp: updateObject_default_def in_monad bind_def)
   apply wp
  apply simp
  done

lemma projectKO_opt_no_vcpu[simp]:
  "projectKO_opt (KOArch (KOVCPU v)) = (None::'a::no_vcpu option)"
    by (rule ccontr) (simp add: project_koType not_vcpu[symmetric])

lemma setObject_vcpu_obj_at'_no_vcpu[wp]:
  "setObject ptr (v::vcpu) \<lbrace>\<lambda>s. P (obj_at' (P'::'a::no_vcpu \<Rightarrow> bool) t s)\<rbrace>"
  apply (wp setObject_ko_wp_at[where
        P'="\<lambda>ko. \<exists>obj. projectKO_opt ko = Some obj \<and> P' (obj::'a::no_vcpu)" for P',
        folded obj_at'_real_def])
     apply (clarsimp simp: updateObject_default_def in_monad not_vcpu[symmetric])
    apply (simp add: objBits_simps)
   apply (simp add: vcpuBits_def pageBits_def)
  apply (clarsimp split del: if_split)
  apply (erule rsubst[where P=P])
  apply normalise_obj_at'
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  done

lemmas setVCPU_pred_tcb'[wp] =
  setObject_vcpu_obj_at'_no_vcpu
      [where P'="\<lambda>ko. P (proj (tcb_to_itcb' ko))" for P proj, folded pred_tcb_at'_def]

lemma setVCPU_valid_idle'[wp]:
  "setObject v (vcpu::vcpu) \<lbrace>valid_idle'\<rbrace>"
    unfolding valid_idle'_def by (rule hoare_lift_Pf[where f=ksIdleThread]; wp)

lemma setVCPU_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setObject p (v::vcpu) \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv | simp)+

lemma setVCPU_ct_not_inQ[wp]:
  "setObject v (vcpu::vcpu) \<lbrace>ct_not_inQ\<rbrace>"
  apply (wp ct_not_inQ_lift)
   apply (rule hoare_lift_Pf[where f=ksCurThread]; wp)
  apply assumption
  done

(* TODO: move *)
lemma getObject_ko_at_vcpu [wp]:
  "\<lbrace>\<top>\<rbrace> getObject p \<lbrace>\<lambda>rv::vcpu. ko_at' rv p\<rbrace>"
  by (rule getObject_ko_at | simp add: objBits_simps vcpuBits_def pageBits_def)+

lemma corres_gets_gicvcpu_numlistregs:
  "corres (=) \<top> \<top> (gets (arm_gicvcpu_numlistregs \<circ> arch_state))
                      (gets (armKSGICVCPUNumListRegs \<circ> ksArchState))"
  by (simp add: state_relation_def arch_state_relation_def)

lemma corres_gets_current_vcpu[corres]:
  "corres (=) \<top> \<top> (gets (arm_current_vcpu \<circ> arch_state))
                      (gets (armHSCurVCPU \<circ> ksArchState))"
  by (simp add: state_relation_def arch_state_relation_def)

lemma setObject_VCPU_corres:
  "vcpu_relation vcpuObj vcpuObj'
   \<Longrightarrow>  corres dc (vcpu_at  vcpu)
                  (vcpu_at' vcpu)
                  (set_vcpu vcpu vcpuObj)
                  (setObject vcpu vcpuObj')"
  apply (simp add: set_vcpu_def)
  apply (rule corres_guard_imp)
    apply (rule setObject_other_corres [where P="\<lambda>ko::vcpu. True"], simp)
        apply (clarsimp simp: obj_at'_def)
        apply (erule map_to_ctes_upd_other, simp, simp)
       apply (simp add: a_type_def is_other_obj_relation_type_def)
      apply (simp add: objBits_simps)
     apply (simp add: objBits_simps vcpuBits_def pageBits_def)
    apply (simp add: other_obj_relation_def asid_pool_relation_def)
   apply (clarsimp simp: typ_at_to_obj_at'[symmetric] obj_at_def exs_valid_def
                         assert_def a_type_def return_def fail_def)
   apply (fastforce split: Structures_A.kernel_object.split_asm if_split_asm)
  apply (simp add: typ_at_to_obj_at_arches)
  done

lemma setObject_vcpu_cte_wp_at'[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace>
   setObject ptr (vcpu::vcpu)
   \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  apply (wp setObject_cte_wp_at2'[where Q="\<top>"])
    apply (clarsimp simp: updateObject_default_def in_monad projectKO_opts_defs)
                         apply (rule equals0I)
   apply (clarsimp simp: updateObject_default_def in_monad projectKO_opts_defs)
  apply simp
  done

crunch vcpuSave, vcpuRestore, vcpuDisable, vcpuEnable
  for ctes[wp]: "\<lambda>s. P (ctes_of s)"
  (simp: crunch_simps wp: crunch_wps getObject_inv_vcpu loadObject_default_inv)

lemma vcpuSwitch_ctes[wp]: "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> vcpuSwitch vcpu \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>"
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | assumption)+

crunch
  vgicUpdate, vgicUpdateLR, vcpuWriteReg, vcpuReadReg, vcpuRestoreRegRange, vcpuSaveRegRange,
  vcpuSave
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and no_0_obj'[wp]: no_0_obj'
  (wp: crunch_wps ignore_del: setObject)

crunch vcpuSave, vcpuRestore, vcpuDisable, vcpuEnable
  for cte_wp_at'[wp]: "\<lambda>s. P (cte_wp_at' P' p s)"
  (simp: crunch_simps wp: crunch_wps getObject_inv_vcpu loadObject_default_inv)

crunch vcpuDisable, vcpuEnable, vcpuSave, vcpuRestore
  for no_0_obj'[wp]: no_0_obj'
  (simp: crunch_simps wp: crunch_wps getObject_inv_vcpu loadObject_default_inv)

lemma vcpuSwitch_no_0_obj'[wp]: "\<lbrace>no_0_obj'\<rbrace> vcpuSwitch v \<lbrace>\<lambda>_. no_0_obj'\<rbrace>"
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | assumption)+

lemma vcpuSwitch_cte_wp_at'[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace> vcpuSwitch param_a \<lbrace>\<lambda>_ s. P (cte_wp_at' P' p s)\<rbrace> "
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | assumption)+

lemma vcpuUpdate_corres[corres]:
  "\<forall>v1 v2. vcpu_relation v1 v2 \<longrightarrow> vcpu_relation (f v1) (f' v2) \<Longrightarrow>
    corres dc (vcpu_at v) (vcpu_at' v)
           (vcpu_update v f) (vcpuUpdate v f')"
  by (corresKsimp corres: getObject_vcpu_corres setObject_VCPU_corres
                 simp: vcpu_update_def vcpuUpdate_def vcpu_relation_def)

lemma vgicUpdate_corres[corres]:
  "\<forall>vgic vgic'. vgic_map vgic = vgic' \<longrightarrow> vgic_map (f vgic) = (f' vgic')
   \<Longrightarrow> corres dc (vcpu_at v) (vcpu_at' v) (vgic_update v f) (vgicUpdate v f')"
  by (corresKsimp simp: vgic_update_def vgicUpdate_def vcpu_relation_def)

lemma vgicUpdateLR_corres[corres]:
  "corres dc (vcpu_at v) (vcpu_at' v)
          (vgic_update_lr v idx val) (vgicUpdateLR v idx val)"
  by (corresKsimp simp: vgic_update_lr_def vgicUpdateLR_def vgic_map_def)

lemma vcpuReadReg_corres[corres]:
  "corres (=) (vcpu_at v) (vcpu_at' v and no_0_obj')
          (vcpu_read_reg v r) (vcpuReadReg v r)"
  apply (simp add: vcpu_read_reg_def vcpuReadReg_def)
  apply (rule corres_guard_imp)
    apply (rule corres_assert_gen_asm2)
    apply (rule corres_underlying_split[OF getObject_vcpu_corres])
      apply (wpsimp simp: vcpu_relation_def)+
  done

lemma vcpuWriteReg_corres[corres]:
  "corres dc (vcpu_at v) (vcpu_at' v and no_0_obj')
          (vcpu_write_reg v r val) (vcpuWriteReg v r val)"
  apply (simp add: vcpu_write_reg_def vcpuWriteReg_def)
  apply (rule corres_guard_imp)
    apply (rule corres_assert_gen_asm2)
    apply (rule vcpuUpdate_corres)
    apply (fastforce simp: vcpu_relation_def)+
  done

lemma vcpuSaveReg_corres[corres]:
  "corres dc (vcpu_at v) (vcpu_at' v and no_0_obj')
          (vcpu_save_reg v r) (vcpuSaveReg v r)"
  apply (clarsimp simp: vcpu_save_reg_def vcpuSaveReg_def)
  apply (rule corres_guard_imp)
    apply (rule corres_assert_gen_asm2)
    apply (rule corres_split[OF corres_machine_op[where r="(=)"]])
       apply (rule corres_Id; simp)
      apply (rule vcpuUpdate_corres, fastforce simp: vcpu_relation_def vgic_map_def)
     apply wpsimp+
  done

lemma vcpuSaveRegRange_corres[corres]:
  "corres dc (vcpu_at v) (vcpu_at' v and no_0_obj')
          (vcpu_save_reg_range v rf rt) (vcpuSaveRegRange v rf rt)"
  apply (clarsimp simp: vcpu_save_reg_range_def vcpuSaveRegRange_def)
  apply (rule corres_mapM_x[OF _ _ _ _ subset_refl])
     apply (wpsimp wp: vcpuSaveReg_corres)+
  done

lemma vcpuRestoreReg_corres[corres]:
  "corres dc (vcpu_at v) (vcpu_at' v and no_0_obj')
          (vcpu_restore_reg v r) (vcpuRestoreReg v r)"
  apply (clarsimp simp: vcpu_restore_reg_def vcpuRestoreReg_def)
  apply (rule corres_guard_imp)
    apply (rule corres_assert_gen_asm2)
    apply (rule corres_split[OF getObject_vcpu_corres])
      apply (rule corres_machine_op)
      apply (rule corres_Id)
        apply (fastforce simp: vcpu_relation_def)
       apply (wpsimp wp: corres_Id simp: vcpu_relation_def vgic_map_def)+
  done

lemma vcpuRestoreRegRange_corres[corres]:
  "corres dc (vcpu_at v) (vcpu_at' v and no_0_obj')
          (vcpu_restore_reg_range v rf rt) (vcpuRestoreRegRange v rf rt)"
  apply (clarsimp simp: vcpu_restore_reg_range_def vcpuRestoreRegRange_def)
  apply (rule corres_mapM_x[OF _ _ _ _ subset_refl])
     apply (wpsimp wp: vcpuRestoreReg_corres)+
  done

lemma saveVirtTimer_corres[corres]:
  "corres dc (vcpu_at vcpu_ptr) (vcpu_at' vcpu_ptr and no_0_obj')
             (save_virt_timer vcpu_ptr) (saveVirtTimer vcpu_ptr)"
  unfolding save_virt_timer_def saveVirtTimer_def
  apply (rule corres_guard_imp)
    apply (rule corres_split_dc[OF vcpuSaveReg_corres], simp)
      apply (rule corres_split_dc[OF corres_machine_op], (rule corres_Id; simp))
        apply (rule corres_split_dc[OF vcpuSaveReg_corres], simp)+
              apply (rule corres_split_eqr[OF corres_machine_op], (rule corres_Id; simp))+
                  apply (fold dc_def)
                  apply (rule vcpuUpdate_corres)
                  apply (simp add: vcpu_relation_def)
                 apply wpsimp+
  done

lemma restoreVirtTimer_corres[corres]:
  "corres dc (vcpu_at vcpu_ptr) (vcpu_at' vcpu_ptr and no_0_obj')
             (restore_virt_timer vcpu_ptr) (restoreVirtTimer vcpu_ptr)"
  unfolding restore_virt_timer_def restoreVirtTimer_def IRQ_def
  apply (rule corres_guard_imp)
    apply (rule corres_split_dc[OF vcpuRestoreReg_corres], simp)+
        apply (rule corres_split_eqr[OF corres_machine_op], (rule corres_Id; simp))+
          apply (rule corres_split[OF getObject_vcpu_corres])
            apply (rule corres_split_eqr[OF vcpuReadReg_corres])
              apply (clarsimp simp: vcpu_relation_def)
              apply (rule corres_split_dc[OF vcpuWriteReg_corres])+
                apply (rule corres_split_dc[OF vcpuRestoreReg_corres], simp)+
                  apply (rule corres_split[OF getObject_vcpu_corres])
                    apply (clarsimp simp: vcpu_relation_def)
                    apply (rule corres_split_eqr[OF isIRQActive_corres])
                      apply (rule corres_split_dc[OF corres_when], simp)
                         apply (simp add: irq_vppi_event_index_def irqVPPIEventIndex_def IRQ_def)
                         apply (rule corres_machine_op, simp)
                         apply (rule corres_Id; wpsimp)
                        apply (fold dc_def)
                        apply (rule vcpuRestoreReg_corres)
                       apply (wpsimp simp: if_apply_def2 isIRQActive_def)+
  done

lemma vcpuSave_corres:
  "corres dc (vcpu_at (fst cvcpu)) (vcpu_at' (fst cvcpu) and no_0_obj')
             (vcpu_save (Some cvcpu)) (vcpuSave (Some cvcpu))"
  apply (clarsimp simp add: vcpu_save_def vcpuSave_def armvVCPUSave_def)
  apply (cases cvcpu, clarsimp, rename_tac v active)
  apply (rule corres_guard_imp)
    apply (rule corres_split_dc[OF corres_machine_op])
       apply (rule corres_Id; wpsimp)
      apply (rule corres_split[where r'=dc])
         apply (rule corres_when, simp)
         apply (rule corres_split[OF vcpuSaveReg_corres])
           apply (rule corres_split_eqr[OF corres_machine_op])
              apply (rule corres_Id; wpsimp)
             apply (rule corres_split[OF vgicUpdate_corres])
                apply (clarsimp simp: vgic_map_def)
               apply (rule saveVirtTimer_corres)
              apply wpsimp+
          apply (rule corres_split_eqr[OF corres_machine_op])
           apply (rule corres_Id; wpsimp)
          apply (rule corres_split[OF vgicUpdate_corres])
             apply (clarsimp simp: vgic_map_def)
            apply (rule corres_split_eqr[OF corres_machine_op])
               apply (rule corres_Id; wpsimp)
              apply (rule corres_split[OF vgicUpdate_corres])
                 apply (clarsimp simp: vgic_map_def)
                apply (rule corres_split_eqr)
                   apply (rule corres_trivial)
                   apply (fastforce simp add: state_relation_def arch_state_relation_def)
                  apply (simp add: mapM_discarded)
                  apply (rule corres_split[OF corres_mapM_x[OF _ _ _ _ subset_refl]])
                        apply (rule corres_split_eqr[OF corres_machine_op])
                           apply (rule corres_Id; wpsimp)
                          apply (clarsimp, fold dc_def)
                          apply (rule vgicUpdateLR_corres)
                         apply wpsimp+
                    apply (rule vcpuSaveRegRange_corres)
                    apply (wpsimp wp: mapM_x_wp_inv hoare_vcg_imp_lift'
                                simp: if_apply_def2)+
  done

lemma vcpuDisable_corres:
  "corres dc (\<lambda>s. (\<exists>v. vcpuopt = Some v) \<longrightarrow> vcpu_at  (the vcpuopt) s)
             (\<lambda>s. ((\<exists>v. vcpuopt = Some v) \<longrightarrow> vcpu_at' (the vcpuopt) s) \<and> no_0_obj' s)
             (vcpu_disable vcpuopt)
             (vcpuDisable vcpuopt)"
  apply (cases vcpuopt; clarsimp simp: vcpu_disable_def vcpuDisable_def)
   (* no current VCPU *)
   subgoal
     apply (clarsimp simp: doMachineOp_bind do_machine_op_bind empty_fail_cond)
     apply (rule corres_guard_imp)
       apply (rule corres_split_dc[OF corres_machine_op]
         | rule corres_machine_op corres_Id
         | wpsimp)+
     done
  (* have current VCPU *)
   apply (rename_tac vcpu)
   apply (clarsimp simp: doMachineOp_bind do_machine_op_bind bind_assoc IRQ_def)
   apply (rule corres_guard_imp)
     apply (rule corres_split_dc[OF corres_machine_op])
        apply (rule corres_Id; wpsimp)
       apply (rule corres_split_eqr[OF corres_machine_op])
          apply (rule corres_Id; wpsimp)
         apply (rule corres_split_dc[OF vgicUpdate_corres])
            apply (clarsimp simp: vgic_map_def)
           apply (rule corres_split_dc[OF vcpuSaveReg_corres])
             apply (rule corres_split_dc[OF vcpuSaveReg_corres])
               apply (rule corres_split_dc[OF corres_machine_op]
                           corres_split_dc[OF saveVirtTimer_corres]
                      | rule corres_machine_op corres_Id
                      | wpsimp)+
   done

lemma vcpuEnable_corres:
  "corres dc (vcpu_at  vcpu) (vcpu_at' vcpu and no_0_obj')
             (vcpu_enable vcpu) (vcpuEnable vcpu)"
  apply (simp add: vcpu_enable_def vcpuEnable_def doMachineOp_bind do_machine_op_bind bind_assoc)
  apply (rule corres_guard_imp)
    apply (rule corres_split_dc[OF vcpuRestoreReg_corres])+
      apply (rule corres_split[OF getObject_vcpu_corres], rename_tac vcpu')
        apply (case_tac vcpu')
        apply (rule corres_split_dc[OF corres_machine_op]
               | rule corres_split_dc[OF vcpuRestoreReg_corres]
               | rule corres_machine_op corres_Id restoreVirtTimer_corres
               | wpsimp simp: vcpu_relation_def vgic_map_def)+
  done

lemma vcpuRestore_corres:
  "corres dc (vcpu_at vcpu)
             (vcpu_at' vcpu and no_0_obj')
             (vcpu_restore vcpu)
             (vcpuRestore vcpu)"
  apply (simp add: vcpu_restore_def vcpuRestore_def gicVCPUMaxNumLR_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_dc[OF corres_machine_op]
           | (rule corres_machine_op corres_Id; wpsimp))+
        apply (rule corres_split[OF getObject_vcpu_corres], rename_tac vcpu')
          apply (rule corres_split[OF corres_gets_gicvcpu_numlistregs])
            apply (case_tac vcpu'
                   , clarsimp simp: comp_def vcpu_relation_def vgic_map_def mapM_x_mapM
                                    uncurry_def split_def mapM_map_simp)
            apply (simp add: doMachineOp_bind do_machine_op_bind bind_assoc empty_fail_cond)
            apply (rule corres_split_dc[OF corres_machine_op])
               apply (rule corres_Id; wpsimp)
              apply (rule corres_split_dc[OF corres_machine_op])
                 apply (rule corres_Id; wpsimp)
                apply (rule corres_split)
                   apply (rule corres_machine_op, rule corres_Id; wpsimp wp: no_fail_mapM)
                  apply (rule corres_split_dc[OF vcpuRestoreRegRange_corres])
                    apply (rule vcpuEnable_corres)
                   apply wpsimp+
  done

lemma vcpuSwitch_corres:
  assumes "vcpu' = vcpu"
  shows
  "corres dc (\<lambda>s. (vcpu \<noteq> None \<longrightarrow> vcpu_at  (the vcpu) s) \<and>
                  ((arm_current_vcpu \<circ> arch_state) s \<noteq> None
                    \<longrightarrow> vcpu_at ((fst \<circ> the \<circ> arm_current_vcpu \<circ> arch_state) s) s))
             (\<lambda>s. (vcpu' \<noteq> None \<longrightarrow> vcpu_at'  (the vcpu') s) \<and>
                  ((armHSCurVCPU \<circ> ksArchState) s \<noteq> None
                    \<longrightarrow> vcpu_at' ((fst \<circ> the \<circ> armHSCurVCPU \<circ> ksArchState) s) s) \<and>
                  no_0_obj' s)
             (vcpu_switch vcpu)
             (vcpuSwitch vcpu')"
  proof -
    have modify_current_vcpu:
      "\<And>a b. corres dc \<top> \<top> (modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := Some (a, b)\<rparr>\<rparr>))
                             (modifyArchState (armHSCurVCPU_update (\<lambda>_. Some (a, b))))"
      by (clarsimp simp add: modifyArchState_def state_relation_def arch_state_relation_def
                   intro!: corres_modify)
    have get_current_vcpu: "corres (=) \<top> \<top> (gets (arm_current_vcpu \<circ> arch_state))
                                               (gets (armHSCurVCPU \<circ> ksArchState))"
      apply clarsimp
      apply (rule_tac P = "(arm_current_vcpu (arch_state s)) = (armHSCurVCPU (ksArchState s'))"
                     in TrueE;
             simp add: state_relation_def arch_state_relation_def)
      done
    show ?thesis
      apply (simp add: vcpu_switch_def vcpuSwitch_def assms)
      apply (cases vcpu)
         apply (all \<open>simp, rule corres_underlying_split[OF  _ _ gets_sp gets_sp],
                           rule corres_guard_imp[OF get_current_vcpu TrueI TrueI],
                           rename_tac rv rv', case_tac rv ;
                           clarsimp simp add: when_def\<close>)
        apply (rule corres_machine_op[OF corres_underlying_trivial[OF no_fail_isb]] TrueI TrueI
                    vcpuDisable_corres modify_current_vcpu
                    vcpuEnable_corres
                    vcpuRestore_corres
                    vcpuSave_corres
                    hoare_TrueI conjI
                    corres_underlying_split corres_guard_imp
               | clarsimp simp add: when_def | wpsimp | assumption)+
      done
  qed

lemma aligned_distinct_relation_vcpu_atI'[elim]:
  "\<lbrakk> vcpu_at p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned' s'; pspace_distinct' s' \<rbrakk>
   \<Longrightarrow> vcpu_at' p s'"
  apply (clarsimp simp add: obj_at_def a_type_def)
  apply (simp split: Structures_A.kernel_object.split_asm
                     if_split_asm arch_kernel_obj.split_asm)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: other_obj_relation_def)
    apply (case_tac z ; simp)
    apply (rename_tac vcpu)
    apply (case_tac vcpu; simp)
  apply (clarsimp simp: vcpu_relation_def obj_at'_def typ_at'_def ko_wp_at'_def)
  apply (fastforce simp add: pspace_aligned'_def pspace_distinct'_def dom_def)
  done

lemma vcpuSwitch_corres':
  assumes "vcpu' = vcpu"
  shows
  "corres dc (\<lambda>s. (vcpu \<noteq> None \<longrightarrow> vcpu_at  (the vcpu) s) \<and>
                  ((arm_current_vcpu \<circ> arch_state) s \<noteq> None
                    \<longrightarrow> vcpu_at ((fst \<circ> the \<circ> arm_current_vcpu \<circ> arch_state) s) s))
             (pspace_aligned' and pspace_distinct' and no_0_obj')
             (vcpu_switch vcpu)
             (vcpuSwitch vcpu')"
  apply (rule stronger_corres_guard_imp,
         rule vcpuSwitch_corres[OF assms])
   apply simp
  apply (simp add: assms)
  apply (rule conjI)
   apply clarsimp
   apply (rule aligned_distinct_relation_vcpu_atI' ; clarsimp simp add: state_relation_def, assumption?)
  apply (clarsimp simp add: state_relation_def arch_state_relation_def)
  apply (rule aligned_distinct_relation_vcpu_atI'; assumption)
  done

crunch
  vgicUpdateLR, vcpuWriteReg, vcpuReadReg, vcpuRestoreRegRange, vcpuSaveRegRange, vcpuSave,
  vcpuSwitch
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (ignore: doMachineOp wp: crunch_wps)

lemma modifyArchState_hyp[wp]:
  "modifyArchState x \<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: modifyArchState_def wp: | subst doMachineOp_bind)+

abbreviation
  "live_vcpu_at_tcb p s \<equiv> \<exists>x. ko_at' x p s \<and>
    (case atcbVCPUPtr (tcbArch x) of None \<Rightarrow> \<lambda>_. True
                                   | Some x \<Rightarrow> ko_wp_at' (is_vcpu' and hyp_live') x) s"

lemma valid_case_option_post_wp':
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>\<lambda>rv. Q x\<rbrace>) \<Longrightarrow>
    \<lbrace>case ep of Some x \<Rightarrow> P x | _ \<Rightarrow> \<lambda>_. True\<rbrace>
       f \<lbrace>\<lambda>rv. case ep of Some x \<Rightarrow> Q x | _ \<Rightarrow> \<lambda>_. True\<rbrace>"
  by (cases ep, simp_all add: hoare_vcg_prop)

crunch
  vcpuDisable, vcpuRestore, vcpuEnable, vgicUpdateLR, vcpuWriteReg, vcpuReadReg,
  vcpuRestoreRegRange, vcpuSaveRegRange
  for ksQ[wp]:  "\<lambda>s. P (ksReadyQueues s)"
  (wp: crunch_wps)

lemma vcpuSave_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> vcpuSave param_a \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  supply option.case_cong_weak[cong]
  apply (wpsimp simp: vcpuSave_def modifyArchState_def armvVCPUSave_def | simp)+
  apply (rule_tac S="set gicIndices" in mapM_x_wp)
  apply wpsimp+
  done

lemma vcpuSwitch_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> vcpuSwitch param_a \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | simp)+

lemma hyp_live'_vcpu_regs[simp]:
  "hyp_live' (KOArch (KOVCPU (vcpuRegs_update f vcpu))) = hyp_live' (KOArch (KOVCPU vcpu))"
    by (simp add: hyp_live'_def arch_live'_def)

lemma hyp_live'_vcpu_vgic[simp]:
  "hyp_live' (KOArch (KOVCPU (vcpuVGIC_update f' vcpu))) = hyp_live' (KOArch (KOVCPU vcpu))"
    by (simp add: hyp_live'_def arch_live'_def)

lemma hyp_live'_vcpu_VPPIMasked[simp]:
  "hyp_live' (KOArch (KOVCPU (vcpuVPPIMasked_update f' vcpu))) = hyp_live' (KOArch (KOVCPU vcpu))"
    by (simp add: hyp_live'_def arch_live'_def)

lemma hyp_live'_vcpu_VTimer[simp]:
  "hyp_live' (KOArch (KOVCPU (vcpuVTimer_update f' vcpu))) = hyp_live' (KOArch (KOVCPU vcpu))"
    by (simp add: hyp_live'_def arch_live'_def)

lemma live'_vcpu_regs[simp]:
  "live' (KOArch (KOVCPU (vcpuRegs_update f vcpu))) = live' (KOArch (KOVCPU vcpu))"
    by (simp add: live'_def)

lemma live'_vcpu_vgic[simp]:
  "live' (KOArch (KOVCPU (vcpuVGIC_update f' vcpu))) = live' (KOArch (KOVCPU vcpu))"
    by (simp add: live'_def)

lemma live'_vcpu_VPPIMasked[simp]:
  "live' (KOArch (KOVCPU (vcpuVPPIMasked_update f' vcpu))) = live' (KOArch (KOVCPU vcpu))"
    by (simp add: live'_def)

lemma live'_vcpu_VTimer[simp]:
  "live' (KOArch (KOVCPU (vcpuVTimer_update f' vcpu))) = live' (KOArch (KOVCPU vcpu))"
    by (simp add: live'_def)

lemma setVCPU_regs_vcpu_live:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') p and ko_at' vcpu v\<rbrace>
   setObject v (vcpuRegs_update f vcpu) \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') p\<rbrace>"
  apply (wp setObject_ko_wp_at, simp)
    apply (simp add: objBits_simps)
   apply (clarsimp simp: vcpuBits_def pageBits_def)
  apply (clarsimp simp: pred_conj_def is_vcpu'_def ko_wp_at'_def obj_at'_real_def)
  done

lemma setVCPU_vgic_vcpu_live[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') p and ko_at' vcpu v\<rbrace>
   setObject v (vcpuVGIC_update f vcpu) \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') p\<rbrace>"
  apply (wp setObject_ko_wp_at, simp)
    apply (simp add: objBits_simps)
   apply (clarsimp simp: vcpuBits_def pageBits_def)
  apply (clarsimp simp: pred_conj_def is_vcpu'_def ko_wp_at'_def obj_at'_real_def)
  done

lemma setVCPU_VPPIMasked_vcpu_live[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') p and ko_at' vcpu v\<rbrace>
   setObject v (vcpuVPPIMasked_update f vcpu) \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') p\<rbrace>"
  apply (wp setObject_ko_wp_at, simp)
    apply (simp add: objBits_simps)
   apply (clarsimp simp: vcpuBits_def pageBits_def)
  apply (clarsimp simp: pred_conj_def is_vcpu'_def ko_wp_at'_def obj_at'_real_def)
  done

lemma setVCPU_VTimer_vcpu_live[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') p and ko_at' vcpu v\<rbrace>
   setObject v (vcpuVTimer_update f vcpu) \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') p\<rbrace>"
  apply (wp setObject_ko_wp_at, simp)
    apply (simp add: objBits_simps)
   apply (clarsimp simp: vcpuBits_def pageBits_def)
  apply (clarsimp simp: pred_conj_def is_vcpu'_def ko_wp_at'_def obj_at'_real_def)
  done

lemma vgicUpdate_vcpu_live[wp]:
  "vgicUpdate v f \<lbrace> ko_wp_at' (is_vcpu' and hyp_live') p \<rbrace>"
  by (wpsimp simp: vgicUpdate_def vcpuUpdate_def wp: setVCPU_vgic_vcpu_live)

lemma setVCPU_regs_vgic_vcpu_live:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') p and ko_at' vcpu v\<rbrace>
   setObject v (vcpuRegs_update f (vcpuVGIC_update f' vcpu)) \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') p\<rbrace>"
  apply (wp setObject_ko_wp_at, simp)
    apply (simp add: objBits_simps)
   apply (clarsimp simp: vcpuBits_def pageBits_def)
  apply (clarsimp simp: pred_conj_def is_vcpu'_def ko_wp_at'_def obj_at'_real_def)
  done

(* FIXME: move *)
lemma setVCPU_regs_vgic_valid_arch':
  "\<lbrace>valid_arch_state' and ko_at' vcpu v\<rbrace> setObject v (vcpuRegs_update f (vcpuVGIC_update f' vcpu)) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def option_case_all_conv)
    apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setVCPU_regs_vgic_vcpu_live
          | rule hoare_lift_Pf[where f=ksArchState])+
  apply (clarsimp simp: pred_conj_def o_def)
  done

lemma setVCPU_regs_valid_arch':
  "\<lbrace>valid_arch_state' and ko_at' vcpu v\<rbrace> setObject v (vcpuRegs_update f vcpu) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def option_case_all_conv)
    apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setVCPU_regs_vcpu_live
           | rule hoare_lift_Pf[where f=ksArchState])
  apply (clarsimp simp: pred_conj_def o_def)
  done

lemma setVCPU_vgic_valid_arch':
  "\<lbrace>valid_arch_state' and ko_at' vcpu v\<rbrace> setObject v (vcpuVGIC_update f vcpu) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def option_case_all_conv)
    apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setVCPU_vgic_vcpu_live
           | rule hoare_lift_Pf[where f=ksArchState])
  apply (clarsimp simp: pred_conj_def o_def)
  done

lemma setVCPU_VPPIMasked_valid_arch':
  "\<lbrace>valid_arch_state' and ko_at' vcpu v\<rbrace> setObject v (vcpuVPPIMasked_update f vcpu) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def option_case_all_conv)
    apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setVCPU_vgic_vcpu_live
           | rule hoare_lift_Pf[where f=ksArchState])
  apply (clarsimp simp: pred_conj_def o_def)
  done

lemma setVCPU_VTimer_valid_arch':
  "\<lbrace>valid_arch_state' and ko_at' vcpu v\<rbrace> setObject v (vcpuVTimer_update f vcpu) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def option_case_all_conv)
    apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setVCPU_vgic_vcpu_live
           | rule hoare_lift_Pf[where f=ksArchState])
  apply (clarsimp simp: pred_conj_def o_def)
  done

lemma state_refs_of'_vcpu_empty:
  "ko_at' (vcpu::vcpu) v s \<Longrightarrow> (state_refs_of' s)(v := {}) = state_refs_of' s"
    by (rule ext) (clarsimp simp: state_refs_of'_def obj_at'_def)

lemma state_hyp_refs_of'_vcpu_absorb:
  "ko_at' vcpu v s \<Longrightarrow>
   (state_hyp_refs_of' s)(v := vcpu_tcb_refs' (vcpuTCBPtr vcpu)) = state_hyp_refs_of' s"
     by (rule ext) (clarsimp simp: state_hyp_refs_of'_def obj_at'_def)

(* FIXME AARCH64: move *)
lemmas valid_arch_obj'_simps[simp] = valid_arch_obj'_def[split_simps arch_kernel_object.split]
lemmas ppn_bounded_simps[simp] = ppn_bounded_def[split_simps pte.split]

lemma setObject_vcpu_valid_objs':
  "\<lbrace>valid_objs' and K (valid_vcpu' vcpu)\<rbrace> setObject v (vcpu::vcpu) \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wp setObject_valid_objs')
   apply (clarsimp simp: in_monad updateObject_default_def valid_obj'_def)
   apply assumption
  apply simp
  done

lemma setVCPU_valid_arch':
 "\<lbrace>valid_arch_state' and (\<lambda>s. \<forall>a. armHSCurVCPU (ksArchState s) = Some (v,a) \<longrightarrow> hyp_live' (KOArch (KOVCPU vcpu))) \<rbrace>
    setObject v (vcpu::vcpu)
  \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def option_case_all_conv pred_conj_def)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' setObject_ko_wp_at
         | simp add: objBits_simps vcpuBits_def pageBits_def)+
  apply (clarsimp simp: is_vcpu'_def ko_wp_at'_def)
  done

lemma setObject_vcpu_no_tcb_update:
  "\<lbrakk> vcpuTCBPtr (f vcpu) = vcpuTCBPtr vcpu \<rbrakk>
  \<Longrightarrow> \<lbrace> valid_objs' and ko_at' (vcpu :: vcpu) p\<rbrace> setObject p (f vcpu) \<lbrace> \<lambda>_. valid_objs' \<rbrace>"
  apply (rule_tac P'="valid_objs' and (ko_at' vcpu p and valid_obj' (KOArch (KOVCPU vcpu)))" in hoare_pre_imp)
   apply (clarsimp)
   apply (simp add: valid_obj'_def)
   apply (drule (1) ko_at_valid_objs', simp)
   apply (simp add: valid_obj'_def)
  apply (rule setObject_valid_objs')
  apply (clarsimp simp add: obj_at'_def)
  apply (frule updateObject_default_result)
  apply (clarsimp simp add: valid_obj'_def valid_vcpu'_def)
  done

lemma vcpuUpdate_valid_objs'[wp]:
  "\<forall>vcpu. vcpuTCBPtr (f vcpu) = vcpuTCBPtr vcpu \<Longrightarrow>
   \<lbrace>valid_objs'\<rbrace> vcpuUpdate vr f \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wpsimp simp: vcpuUpdate_def)
  apply (rule_tac vcpu=vcpu in setObject_vcpu_no_tcb_update)
  apply wpsimp+
  done

crunch
  vgicUpdate, vcpuSaveReg, vgicUpdateLR, vcpuSaveRegRange, vcpuSave,
  vcpuDisable, vcpuEnable, vcpuRestore, vcpuSwitch
  for valid_objs'[wp]: valid_objs'
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  (wp: mapM_wp_inv simp: mapM_x_mapM)

lemma setVCPU_tcbs_of'[wp]:
  "setObject v (vcpu :: vcpu) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setVCPU_regs_r_invs_cicd':
  "\<lbrace>invs_no_cicd' and ko_at' vcpu v\<rbrace>
   setObject v (vcpuRegs_update (\<lambda>_. (vcpuRegs vcpu)(r:=rval)) vcpu) \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  unfolding valid_state'_def valid_pspace'_def valid_mdb'_def invs_no_cicd'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. vcpuRegs_update (\<lambda>_. (vcpuRegs vcpu)(r:=rval)) vcpu"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    setObject_typ_at' cur_tcb_lift valid_bitmaps_lift
                    setVCPU_regs_valid_arch' setVCPU_regs_vcpu_live
              simp: objBits_simps archObjSize_def vcpuBits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def)
  done

lemma setVCPU_vgic_invs_cicd':
  "\<lbrace>invs_no_cicd' and ko_at' vcpu v\<rbrace>
   setObject v (vcpuVGIC_update f vcpu)
   \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  unfolding valid_state'_def valid_pspace'_def valid_mdb'_def invs_no_cicd'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. (vcpuVGIC_update f vcpu)"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    setObject_typ_at' cur_tcb_lift valid_bitmaps_lift
                    setVCPU_vgic_valid_arch'
              simp: objBits_simps archObjSize_def vcpuBits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def)
  done

lemma setVCPU_VPPIMasked_invs_cicd':
  "\<lbrace>invs_no_cicd' and ko_at' vcpu v\<rbrace>
   setObject v (vcpuVPPIMasked_update f vcpu)
   \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  unfolding valid_state'_def valid_pspace'_def valid_mdb'_def invs_no_cicd'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. (vcpuVPPIMasked_update f vcpu)"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    setObject_typ_at' cur_tcb_lift valid_bitmaps_lift
                    setVCPU_VPPIMasked_valid_arch'
              simp: objBits_simps archObjSize_def vcpuBits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def)
  done

lemma setVCPU_VTimer_invs_cicd':
  "\<lbrace>invs_no_cicd' and ko_at' vcpu v\<rbrace>
   setObject v (vcpuVTimer_update f vcpu)
   \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  unfolding valid_state'_def valid_pspace'_def valid_mdb'_def invs_no_cicd'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. (vcpuVTimer_update f vcpu)"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    setObject_typ_at' cur_tcb_lift valid_bitmaps_lift
                    setVCPU_VTimer_valid_arch'
              simp: objBits_simps archObjSize_def vcpuBits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def)
  done

lemma vgicUpdate_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vgicUpdate f v \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: vgicUpdate_def vcpuUpdate_def wp: setVCPU_vgic_invs_cicd')

lemma vcpuRestoreReg_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuRestoreReg v r \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: vcpuRestoreReg_def | subst doMachineOp_bind | rule empty_fail_bind)+

lemma vcpuReadReg_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuReadReg v r \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: vcpuReadReg_def | subst doMachineOp_bind | rule empty_fail_bind)+

lemma vcpuSaveReg_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuSaveReg v r \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: vcpuSaveReg_def vcpuUpdate_def wp: setVCPU_regs_r_invs_cicd'
     | subst doMachineOp_bind | rule empty_fail_bind)+

lemma vcpuWriteReg_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuWriteReg vcpu_ptr r v \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: vcpuWriteReg_def vcpuUpdate_def wp: setVCPU_regs_r_invs_cicd'
     | subst doMachineOp_bind | rule empty_fail_bind)+

crunch vcpuRestoreRegRange, vcpuSaveRegRange, vgicUpdateLR
  for invs_no_cicd'[wp]: invs_no_cicd'
  (wp: mapM_x_wp ignore: loadObject)

lemma saveVirtTimer_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> saveVirtTimer vcpu_ptr \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: saveVirtTimer_def vcpuUpdate_def read_cntpct_def
             wp: setVCPU_VTimer_invs_cicd' dmo'_gets_wp)

lemma restoreVirtTimer_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> restoreVirtTimer vcpu_ptr \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: restoreVirtTimer_def vcpuUpdate_def read_cntpct_def if_apply_def2
                   isIRQActive_def
             wp: setVCPU_VTimer_invs_cicd' maskInterrupt_invs_no_cicd' getIRQState_wp dmo'_gets_wp)

lemma vcpuEnable_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuEnable v \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: vcpuEnable_def | subst doMachineOp_bind | rule empty_fail_bind)+

lemma dmo_maskInterrupt_True_invs_no_cicd'[wp]:
  "doMachineOp (maskInterrupt True irq) \<lbrace>invs_no_cicd'\<rbrace>"
  apply (wp dmo_maskInterrupt)
  apply (clarsimp simp: invs_no_cicd'_def valid_state'_def)
  apply (simp add: valid_irq_masks'_def valid_machine_state'_def
                   ct_not_inQ_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma vcpuDisable_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuDisable v \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  unfolding vcpuDisable_def
  by (wpsimp wp: doMachineOp_typ_ats
             simp: vcpuDisable_def doMachineOp_typ_at' split: option.splits
      | subst doMachineOp_bind | rule empty_fail_bind conjI)+

lemma vcpuRestore_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuRestore v \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  including no_pre
  apply (wpsimp simp: vcpuRestore_def uncurry_def split_def doMachineOp_mapM_x gets_wp
       | subst doMachineOp_bind | rule empty_fail_bind)+
       apply (rule_tac S="(\<lambda>i. (of_nat i, vgicLR (vcpuVGIC vcpu) i)) ` {0..<numListRegs+1}" in mapM_x_wp)
       apply wpsimp
       apply (auto simp: image_def gicVCPUMaxNumLR_def)[1]
      apply wpsimp+
  done

lemma vcpuSave_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuSave v \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: vcpuSave_def armvVCPUSave_def wp: mapM_x_wp cong: option.case_cong_weak
      | assumption)+
lemma valid_arch_state'_armHSCurVCPU_update[simp]:
  "\<lbrakk> ko_wp_at' (is_vcpu' and hyp_live') v s; valid_arch_state' s \<rbrakk> \<Longrightarrow>
   valid_arch_state' (s\<lparr>ksArchState := armHSCurVCPU_update (\<lambda>_. Some (v, b)) (ksArchState s)\<rparr>)"
  by (clarsimp simp: invs'_def valid_state'_def
                     bitmapQ_defs valid_global_refs'_def valid_arch_state'_def global_refs'_def
                     valid_irq_node'_def valid_irq_handlers'_def
                     irq_issued'_def irqs_masked'_def valid_machine_state'_def cur_tcb'_def)

lemma dmo_vcpu_hyp:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace> doMachineOp f \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: doMachineOp_def)

lemma vcpuSaveReg_hyp[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v \<rbrace> vcpuSaveReg v' r \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: vcpuSaveReg_def vcpuUpdate_def wp: setVCPU_regs_vcpu_live dmo_vcpu_hyp)

lemma vcpuWriteReg_hyp[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v \<rbrace> vcpuWriteReg v' r val \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: vcpuWriteReg_def vcpuUpdate_def wp: setVCPU_regs_vcpu_live dmo_vcpu_hyp)

crunch
  vcpuRestoreRegRange, vcpuSaveRegRange, vgicUpdateLR, vcpuReadReg
  for hyp[wp]: "ko_wp_at' (is_vcpu' and hyp_live') v"
  (wp: crunch_wps setVCPU_regs_vcpu_live dmo_vcpu_hyp)

lemma saveVirtTimer_hyp[wp]:
  "saveVirtTimer vcpu_ptr \<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: saveVirtTimer_def vcpuUpdate_def wp: dmo_vcpu_hyp vgicUpdate_vcpu_live)

lemma restoreVirtTimer_hyp[wp]:
  "restoreVirtTimer vcpu_ptr \<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: restoreVirtTimer_def vcpuUpdate_def isIRQActive_def
             wp: dmo_vcpu_hyp vgicUpdate_vcpu_live)

lemma vcpuDisable_hyp[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace> vcpuDisable (Some x) \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: vcpuDisable_def wp: dmo_vcpu_hyp vgicUpdate_vcpu_live | subst doMachineOp_bind | rule empty_fail_bind)+

lemma vcpuEnable_hyp[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace> vcpuEnable x \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: vcpuEnable_def wp: dmo_vcpu_hyp | subst doMachineOp_bind | rule empty_fail_bind)+

lemma vcpuRestore_hyp[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace> vcpuRestore x \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: vcpuRestore_def wp: dmo_vcpu_hyp | subst doMachineOp_bind | rule empty_fail_bind)+

lemma armvVCPUSave_hyp[wp]:
  "armvVCPUSave x y \<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: armvVCPUSave_def wp: dmo_vcpu_hyp)

lemma vcpuSave_hyp[wp]:
  "vcpuSave x \<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  apply (wpsimp simp: vcpuSave_def wp: dmo_vcpu_hyp mapM_x_wp'
         | subst doMachineOp_bind
         | rule empty_fail_bind)+
  apply (simp add: pred_conj_def)
  done

lemma vcpuSwitch_hyp[wp]:
  "vcpuSwitch x \<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: vcpuSwitch_def wp: dmo_vcpu_hyp)

lemma getObject_vcpu_ko_at':
  "(vcpu::vcpu, s') \<in> fst (getObject p s) \<Longrightarrow> s' = s \<and> ko_at' vcpu p s"
  apply (rule context_conjI)
   apply (drule use_valid, rule getObject_inv[where P="(=) s"]; simp add: loadObject_default_inv)
  apply (drule use_valid, rule getObject_ko_at; clarsimp simp: obj_at_simps vcpuBits_def)
  done

lemma vcpuUpdate_valid_arch_state'[wp]:
  "\<forall>vcpu. vcpuTCBPtr (f vcpu) = vcpuTCBPtr vcpu \<Longrightarrow>
   \<lbrace>valid_arch_state'\<rbrace> vcpuUpdate vr f \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  including no_pre
  apply (wpsimp simp: vcpuUpdate_def
            wp: setVCPU_valid_arch')
  by (clarsimp simp: valid_def in_monad hyp_live'_def arch_live'_def valid_arch_state'_def
                     obj_at'_real_def ko_wp_at'_def is_vcpu'_def
               dest!: getObject_vcpu_ko_at')+

crunch vcpuRestoreReg
  for valid_arch_state'[wp]: valid_arch_state'

crunch vgicUpdateLR, vcpuSave, vcpuDisable, vcpuEnable, vcpuRestore
  for valid_arch_state'[wp]: valid_arch_state'
  (wp: crunch_wps ignore: doMachineOp)

lemma vcpuSwitch_valid_arch_state'[wp]:
   "\<lbrace>valid_arch_state' and (case v of None \<Rightarrow> \<top> | Some x \<Rightarrow> ko_wp_at' (is_vcpu' and hyp_live') x)\<rbrace>
       vcpuSwitch v \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (wpsimp simp: vcpuSwitch_def modifyArchState_def
         wp: vcpuDisable_hyp[simplified pred_conj_def] vcpuSave_hyp[unfolded pred_conj_def]
             dmo_vcpu_hyp vcpuSave_valid_arch_state'
        | strengthen valid_arch_state'_armHSCurVCPU_update | simp)+
  apply (auto simp: valid_arch_state'_def pred_conj_def)
  done

lemma invs_no_cicd'_armHSCurVCPU_update[simp]:
  "ko_wp_at' (is_vcpu' and hyp_live') v s \<Longrightarrow> invs_no_cicd' s \<Longrightarrow>
     invs_no_cicd' (s\<lparr>ksArchState := armHSCurVCPU_update (\<lambda>_. Some (v, b)) (ksArchState s)\<rparr>)"
  by (clarsimp simp: invs_no_cicd'_def valid_state'_def
                     bitmapQ_defs valid_global_refs'_def valid_arch_state'_def global_refs'_def
                     valid_irq_node'_def valid_irq_handlers'_def
                     irq_issued'_def irqs_masked'_def valid_machine_state'_def cur_tcb'_def)

lemma invs'_armHSCurVCPU_update[simp]:
  "ko_wp_at' (is_vcpu' and hyp_live') v s \<Longrightarrow>
   invs' s \<Longrightarrow> invs' (s\<lparr>ksArchState := armHSCurVCPU_update (\<lambda>_. Some (v, b)) (ksArchState s)\<rparr>)"
  apply (clarsimp simp: invs'_def valid_state'_def
                        bitmapQ_defs valid_global_refs'_def valid_arch_state'_def global_refs'_def
                        valid_irq_node'_def valid_irq_handlers'_def
                        irq_issued'_def irqs_masked'_def valid_machine_state'_def cur_tcb'_def)
  done

lemma armHSCurVCPU_None_invs'[wp]:
  "modifyArchState (armHSCurVCPU_update Map.empty) \<lbrace>invs'\<rbrace>"
  apply (wpsimp simp: modifyArchState_def)
  by (clarsimp simp: invs'_def valid_state'_def valid_machine_state'_def
                        ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def
                        valid_arch_state'_def valid_global_refs'_def global_refs'_def)

lemma setVCPU_vgic_invs':
  "\<lbrace>invs' and ko_at' vcpu v\<rbrace>
   setObject v (vcpuVGIC_update f vcpu) \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. vcpuVGIC_update f vcpu"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    setObject_typ_at' cur_tcb_lift valid_bitmaps_lift
                    setVCPU_vgic_valid_arch'
              simp: objBits_simps archObjSize_def vcpuBits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def)
  done

lemma setVCPU_regs_invs':
  "\<lbrace>invs' and ko_at' vcpu v\<rbrace> setObject v (vcpuRegs_update f vcpu) \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. vcpuRegs_update f vcpu"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    setObject_typ_at' cur_tcb_lift valid_bitmaps_lift
                    setVCPU_regs_valid_arch'
              simp: objBits_simps archObjSize_def vcpuBits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def)
  done

lemma setVCPU_VPPIMasked_invs':
  "\<lbrace>invs' and ko_at' vcpu v\<rbrace> setObject v (vcpuVPPIMasked_update f vcpu) \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. vcpuVPPIMasked_update f vcpu"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    setObject_typ_at' cur_tcb_lift valid_bitmaps_lift
                    setVCPU_VPPIMasked_valid_arch'
              simp: objBits_simps archObjSize_def vcpuBits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def)
  done

lemma setVCPU_VTimer_invs':
  "\<lbrace>invs' and ko_at' vcpu v\<rbrace> setObject v (vcpuVTimer_update f vcpu) \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. vcpuVTimer_update f vcpu"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    setObject_typ_at' cur_tcb_lift valid_bitmaps_lift
                    setVCPU_VTimer_valid_arch'
              simp: objBits_simps archObjSize_def vcpuBits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def)
  done

lemma vcpuWriteReg_invs'[wp]:
  "vcpuWriteReg vcpu_ptr r v \<lbrace>invs'\<rbrace>"
  by (wpsimp simp: vcpuWriteReg_def vcpuUpdate_def wp: setVCPU_regs_invs')

lemma vcpuSaveReg_invs'[wp]:
  "vcpuSaveReg v r \<lbrace>invs'\<rbrace>"
  by (wpsimp simp: vcpuSaveReg_def vcpuUpdate_def wp: setVCPU_regs_invs')

lemma saveVirtTimer_invs'[wp]:
  "saveVirtTimer vcpu_ptr \<lbrace>invs'\<rbrace>"
  unfolding saveVirtTimer_def
  by (wpsimp wp: dmo'_gets_wp setVCPU_vgic_invs' setVCPU_regs_invs' dmo_maskInterrupt_True
                 setVCPU_VTimer_invs'
             simp: doMachineOp_bind vcpuUpdate_def read_cntpct_def check_export_arch_timer_def)

lemma vcpuDisable_invs'[wp]:
  "vcpuDisable v \<lbrace>invs'\<rbrace>"
  unfolding vcpuDisable_def isb_def setHCR_def setSCTLR_def set_gic_vcpu_ctrl_hcr_def
             getSCTLR_def get_gic_vcpu_ctrl_hcr_def dsb_def vgicUpdate_def vcpuUpdate_def
             vcpuSaveReg_def enableFpuEL01_def
  by (wpsimp wp: dmo'_gets_wp setVCPU_vgic_invs' setVCPU_regs_invs' dmo_maskInterrupt_True
                 hoare_drop_imps
             simp: doMachineOp_bind empty_fail_cond)

lemma vcpuInvalidateActive_invs'[wp]:
  "vcpuInvalidateActive \<lbrace>invs'\<rbrace>"
    unfolding vcpuInvalidateActive_def by wpsimp

crunch
  vcpuRestoreReg, vcpuRestoreRegRange, vcpuSaveReg, vcpuSaveRegRange, vgicUpdateLR, vcpuReadReg
  for invs'[wp]: invs'
  (wp: crunch_wps setVCPU_regs_invs' setVCPU_vgic_invs' simp: vcpuUpdate_def
   ignore: doMachineOp vcpuUpdate)

lemma restoreVirtTimer_invs'[wp]:
  "restoreVirtTimer vcpu_ptr \<lbrace> invs'\<rbrace>"
  unfolding restoreVirtTimer_def
  by (wpsimp wp: maskInterrupt_invs' getIRQState_wp dmo'_gets_wp dmo_machine_op_lift_invs'
             simp: IRQ_def if_apply_def2 read_cntpct_def isIRQActive_def)

lemma vcpuEnable_invs'[wp]:
  "vcpuEnable v \<lbrace> invs'\<rbrace>"
  unfolding vcpuEnable_def
  by (wpsimp | subst doMachineOp_bind | rule empty_fail_bind)+

lemma vcpuRestore_invs'[wp]:
  "\<lbrace>invs'\<rbrace> vcpuRestore v \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding vcpuRestore_def
  by (wpsimp simp: vcpuRestore_def uncurry_def split_def doMachineOp_mapM_x
                wp: mapM_x_wp[OF _ subset_refl]
     | subst doMachineOp_bind | rule empty_fail_bind)+

lemma vcpuSave_invs':
  "\<lbrace>invs'\<rbrace> vcpuSave v \<lbrace>\<lambda>_. invs'\<rbrace>"
  by (wpsimp simp: vcpuSave_def doMachineOp_mapM armvVCPUSave_def
                   get_gic_vcpu_ctrl_apr_def get_gic_vcpu_ctrl_vmcr_def
                   get_gic_vcpu_ctrl_hcr_def getSCTLR_def
             wp: dmo'_gets_wp vgicUpdate_invs' mapM_x_wp[OF _ subset_refl])

lemma vcpuSwitch_invs'[wp]:
  "\<lbrace>invs' and (case v of None \<Rightarrow> \<top> | Some x \<Rightarrow> ko_wp_at' (is_vcpu' and hyp_live') x)\<rbrace>
       vcpuSwitch v \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wpsimp simp: vcpuSwitch_def modifyArchState_def
         wp: vcpuDisable_hyp[simplified pred_conj_def] vcpuSave_hyp[unfolded pred_conj_def]
             dmo_vcpu_hyp vcpuSave_invs'
        | strengthen invs'_armHSCurVCPU_update | simp)+
  apply (auto simp: invs'_def valid_state'_def valid_arch_state'_def pred_conj_def)
  done

lemma vcpuSwitch_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd' and (case v of None \<Rightarrow> \<top> | Some x \<Rightarrow> ko_wp_at' (is_vcpu' and hyp_live') x)\<rbrace>
       vcpuSwitch v \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  apply (wpsimp simp: vcpuSwitch_def modifyArchState_def
                  wp: vcpuDisable_hyp[simplified pred_conj_def] vcpuSave_hyp[unfolded pred_conj_def]
                       gets_wp vcpuSave_invs_no_cicd' dmo_vcpu_hyp
        | strengthen invs_no_cicd'_armHSCurVCPU_update | simp)+
  apply (auto simp: invs_no_cicd'_def valid_state'_def valid_arch_state'_def pred_conj_def)
  done

crunch loadVMID
  for inv: P

lemma updateASIDPoolEntry_valid_arch_state'[wp]:
  "updateASIDPoolEntry f asid \<lbrace>valid_arch_state'\<rbrace>"
  unfolding updateASIDPoolEntry_def
  by (wpsimp wp: getObject_inv hoare_drop_imps simp: loadObject_default_def)

lemma invalidateVMIDEntry_valid_arch_state'[wp]:
  "invalidateVMIDEntry vmid \<lbrace>valid_arch_state'\<rbrace>"
  unfolding invalidateVMIDEntry_def
  by (wpsimp simp: valid_arch_state'_def ran_def cong: option.case_cong)

lemma valid_arch_state'_vmid_Some_upd:
  "\<lbrakk> valid_arch_state' s; 0 < asid \<rbrakk> \<Longrightarrow>
   valid_arch_state' (s\<lparr>ksArchState := armKSVMIDTable_update
                                       (\<lambda>_. (armKSVMIDTable (ksArchState s))(vmid \<mapsto> asid))
                                       (ksArchState s)\<rparr>)"
  by (simp add: valid_arch_state'_def ran_def cong: option.case_cong)

lemma storeVMID_valid_arch_state'[wp]:
  "\<lbrace>valid_arch_state' and K (0 < asid)\<rbrace> storeVMID asid vmid \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  unfolding storeVMID_def
  by (wpsimp simp_del: fun_upd_apply | strengthen valid_arch_state'_vmid_Some_upd)+

crunch armContextSwitch, setGlobalUserVSpace
  for valid_arch_state'[wp]: valid_arch_state'

(* FIXME AARCH64 consolidated VCPU block ends here *)

(* FIXME AARCH64: replacing getSlotCap_wp is probably going to be too much breakage, but
                   rename would be good *)
lemma getSlotCap_actual_wp:
  "\<lbrace>\<lambda>s.  \<forall>cap. cteCaps_of s p = Some cap \<longrightarrow> Q cap s\<rbrace>
   getSlotCap p \<lbrace>Q\<rbrace>"
  unfolding getSlotCap_def
  by (wpsimp wp: getCTE_cteCap_wp split: option.splits)

lemma setVMRoot_valid_arch_state'[wp]:
  "\<lbrace>valid_arch_state' and valid_objs' and live_vcpu_at_tcb p\<rbrace>
     setVMRoot p
   \<lbrace>\<lambda>rv. valid_arch_state'\<rbrace>"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def locateSlotTCB_def locateSlotBasic_def)
  apply ((wpsimp wp: hoare_vcg_ex_lift hoare_vcg_all_lift
                     getObject_tcb_wp valid_case_option_post_wp' getSlotCap_actual_wp
                 simp: if_apply_def2
          | wp hoare_drop_imps)+)
  apply (fastforce simp: cteCaps_of_def valid_cap'_def wellformed_mapdata'_def
                   dest!: ctes_of_valid_cap'')
  done

crunch setVMRoot
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
  (simp: updateObject_default_def o_def loadObject_default_def if_apply_def2
   wp: crunch_wps getObject_inv)

lemma handleVMFault_corres:
  "corres (fr \<oplus> dc) (tcb_at thread  and pspace_aligned and pspace_distinct) \<top>
          (handle_vm_fault thread fault) (handleVMFault thread fault)"
  supply if_split[split del]
  apply (rule corres_cross_over_guard[where Q="tcb_at' thread"])
   apply (fastforce simp: tcb_at_cross state_relation_def)
  apply (simp add: AARCH64_H.handleVMFault_def handle_vm_fault_def)
  apply (cases fault)
   (* ARMDataAbort *)
   apply (simp add: curVCPUActive_def)
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE, simp,
            rule corres_machine_op[where r="(=)"],
            rule corres_Id refl, rule refl, simp, simp)+
         (* only do S1 translation if current VCPU active *)
         apply (simp add: bind_liftE_distrib bindE_assoc)
         apply (rule corres_splitEE[OF corres_liftE_lift[OF corres_gets_current_vcpu]])
           apply (clarsimp simp: liftE_return_bindE bindE_assoc)
           apply (rule corres_split_eqrE[OF corres_if])
                apply fastforce
               apply (rule corres_split_eqrE, simp)
                  apply (rule corres_returnOkTT, simp)
                 apply simp
                 apply (rule corres_splitEE, simp,
                        rule corres_machine_op[where r="(=)"],
                        rule corres_Id refl, rule refl, simp, simp)+
                   apply (rule corres_returnOkTT, simp)
                  apply wpsimp+
              apply (rule corres_returnOkTT, simp)
             apply (rule corres_trivial)
             apply simp
            apply (wpsimp simp: if_apply_def2)+
  (* ARMPrefetchAbort *)
  apply (simp add: curVCPUActive_def)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE,simp)
       apply (rule asUser_corres')
       apply (rule corres_no_failI [where R="(=)"])
        apply (rule no_fail_getRestartPC)
       apply fastforce
      apply (rule corres_splitEE,simp,
             rule corres_machine_op [where r="(=)"],
             rule corres_Id refl, rule refl, simp, simp)+
        (* only do S1 translation if current VCPU active *)
        apply (simp add: bind_liftE_distrib bindE_assoc)
        apply (rule corres_splitEE[OF corres_liftE_lift[OF corres_gets_current_vcpu]])
          apply (clarsimp simp: liftE_return_bindE bindE_assoc)
          apply (rule corres_split_eqrE[OF corres_if])
               apply fastforce
              apply (rule corres_split_eqrE, simp)
                 apply (rule corres_returnOkTT, simp)
                apply simp
                apply (rule corres_splitEE, simp,
                       rule corres_machine_op[where r="(=)"],
                       rule corres_Id refl, rule refl, simp, simp)+
                  apply (rule corres_returnOkTT, simp)
                 apply wpsimp+
             apply (rule corres_returnOkTT, simp)
            apply (rule corres_trivial, simp)
           apply (wpsimp simp: if_apply_def2)+
  done

crunch findFreeVMID, loadVMID
  for no_0_obj'[wp]: no_0_obj'
  (wp: crunch_wps getObject_inv simp: o_def loadObject_default_def)

lemma mask_is_asid_low_bits_of[simp]:
  "(ucast asid :: machine_word) && mask asid_low_bits = ucast (asid_low_bits_of asid)"
  by (word_eqI_solve simp: asid_low_bits_of_def asid_low_bits_def)

declare corres_gets_asid[corres] (* FIXME AARCH64: declare at origin *)
declare getPoolPtr_corres[corres] (* FIXME AARCH64: declare at origin *)
declare getObject_ASIDPool_corres[corres] (* FIXME AARCH64: declare at origin *)

lemma getASIDPoolEntry_corres'[corres]:
  "asid' = ucast asid \<Longrightarrow>
   corres (\<lambda>r r'. r = map_option abs_asid_entry r')
          (\<lambda>s. pspace_aligned s \<and> pspace_distinct s \<and>
               (\<forall>p. pool_for_asid asid s = Some p \<longrightarrow> asid_pool_at p s) \<and> 0 < asid)
          \<top>
          (gets (entry_for_asid asid))
          (getASIDPoolEntry asid')"
  unfolding entry_for_asid_def getASIDPoolEntry_def
  apply (clarsimp simp: gets_obind_bind_eq entry_for_pool_def obind_comp_dist
                  cong: option.case_cong)
  apply (corres corres: getPoolPtr_corres | corres_cases_both)+
      apply (rule monadic_rewrite_corres_l)
       apply (monadic_rewrite_l gets_oapply_liftM_rewrite)
       apply (rule monadic_rewrite_refl)
      apply (corres simp: liftM_def asid_pool_relation_def asid_pools_at_eq corres: corres_returnTT
             | corres_cases)+
  done

lemma getASIDPoolEntry_get_the_corres[corres]:
  "asid' = ucast asid \<Longrightarrow>
   corres (\<lambda>r r'. map_option abs_asid_entry r' = Some r)
          (\<lambda>s. pspace_aligned s \<and> pspace_distinct s \<and> entry_for_asid asid s \<noteq> None \<and> 0 < asid)
          \<top>
          (gets_the (entry_for_asid asid))
          (getASIDPoolEntry asid')"
  apply (simp add: gets_the_def cong: corres_weak_cong)
  apply (rule corres_bind_return2)
  apply (corres simp: entry_for_asid_def entry_for_pool_def in_omonad obj_at_def)
  done

lemma loadVMID_corres[corres]:
  "asid' = ucast asid \<Longrightarrow>
   corres (=)
          (pspace_aligned and pspace_distinct and (\<lambda>s. vspace_for_asid asid s \<noteq> None))
          \<top>
          (load_vmid asid) (loadVMID asid')"
  unfolding load_vmid_def loadVMID_def
  apply corres
      apply (corres_cases, rule corres_inst[where P=\<top> and P'=\<top>], clarsimp)
      apply (corres_cases, rule corres_returnTT, clarsimp simp: abs_asid_entry_def)
     apply wpsimp+
   apply (clarsimp simp: vspace_for_asid_def)
  apply clarsimp
  done

lemma updateASIDPoolEntry_corres[corres]:
  assumes eq: "asid' = ucast asid"
  assumes abs: "\<And>e. map_option abs_asid_entry (f' e) = f (abs_asid_entry e)"
  shows "corres dc
                ((\<lambda>s. entry_for_asid asid s \<noteq> None \<and> 0 < asid)
                 and pspace_aligned and pspace_distinct)
                \<top>
                (update_asid_pool_entry f asid)
                (updateASIDPoolEntry f' asid')"
  unfolding update_asid_pool_entry_def updateASIDPoolEntry_def
  apply (simp add: gets_the_def bind_assoc eq)
  apply (corres simp: liftM_def
                term_simp: asid_pool_relation_def asid_low_bits_of_def
                           mask_asid_low_bits_ucast_ucast ucast_ucast_mask2
                           is_down ucast_and_mask)
             apply (rule ext)
             apply (clarsimp simp: asid_pool_relation_def asid_low_bits_of_def
                                   mask_asid_low_bits_ucast_ucast ucast_ucast_mask2
                                   is_down ucast_and_mask abs)
             apply (erule notE)
             apply word_eqI_solve
           apply wpsimp+
   apply (clarsimp simp: entry_for_asid_def entry_for_pool_def asid_pools_at_eq)
  apply simp
  done

lemma gets_armKSVMIDTable_corres[corres]:
  "corres (\<lambda>t t'. t' = map_option UCAST(16 \<rightarrow> 64) \<circ> t)
          \<top> \<top>
          (gets (arm_vmid_table \<circ> arch_state)) (gets (armKSVMIDTable \<circ> ksArchState))"
  by (simp add: state_relation_def arch_state_relation_def)

lemma storeVMID_corres[corres]:
  "\<lbrakk> asid' = ucast asid; vmid' = vmid \<rbrakk> \<Longrightarrow>
   corres dc
          (pspace_aligned and pspace_distinct and (\<lambda>s. vspace_for_asid asid s \<noteq> None))
          \<top>
          (store_vmid asid vmid) (storeVMID asid' vmid')"
  unfolding store_vmid_def storeVMID_def
  apply (corres simp: abs_asid_entry_def corres: corres_modify_tivial)
        apply (fastforce simp: state_relation_def arch_state_relation_def)
       apply wpsimp+
   apply (clarsimp simp: vspace_for_asid_def)
  apply simp
  done

lemma invalidateASID_corres[corres]:
  "asid' = ucast asid \<Longrightarrow>
   corres dc
          ((\<lambda>s. entry_for_asid asid s \<noteq> None \<and> 0 < asid) and pspace_aligned and pspace_distinct)
          \<top>
          (invalidate_asid asid) (invalidateASID asid')"
  unfolding invalidate_asid_def invalidateASID_def
  by (corres simp: abs_asid_entry_def entry_for_asid_def)

lemma gets_armKSNextVMID_corres[corres]:
  "corres (=) \<top> \<top>
          (gets (arm_next_vmid \<circ> arch_state)) (gets (armKSNextVMID \<circ> ksArchState))"
  by (simp add: state_relation_def arch_state_relation_def)

lemma take_vmid_minBound_maxBound:
  "take (length [minBound .e. maxBound :: vmid])
        ([next_vmid .e. maxBound] @ [minBound .e. next_vmid])
   = [next_vmid .e. maxBound] @ init [minBound .e. next_vmid]"
  for next_vmid :: vmid
  using leq_maxBound[where x=next_vmid]
  by (simp add: word_le_nat_alt init_def upto_enum_word minBound_word)

(* FIXME AARCH64: move to SubMonad *)
lemmas corres_machine_op_Id = corres_machine_op[OF corres_Id]
lemmas corres_machine_op_Id_eq[corres_term] = corres_machine_op_Id[where r="(=)"]
lemmas corres_machine_op_Id_dc[corres_term] = corres_machine_op_Id[where r="dc::unit \<Rightarrow> unit \<Rightarrow> bool"]

lemma invalidateVMIDEntry_corres[corres]:
  "vmid' = vmid \<Longrightarrow>
   corres dc \<top> \<top> (invalidate_vmid_entry vmid) (invalidateVMIDEntry vmid')"
  unfolding invalidate_vmid_entry_def invalidateVMIDEntry_def
  by (corres' \<open>fastforce simp: state_relation_def arch_state_relation_def\<close>
              corres: corres_modify_tivial)

lemma valid_vmid_tableD:
  "\<lbrakk> valid_vmid_table s; vmid_table s vmid = Some asid \<rbrakk> \<Longrightarrow> 0 < asid"
  apply (subgoal_tac "asid \<noteq> 0")
   apply (simp add: word_neq_0_conv)
  apply (fastforce simp: valid_vmid_table_def)
  done

lemma findFreeVMID_corres[corres]:
  "corres (=)
          (vmid_inv and valid_vmid_table and pspace_aligned and pspace_distinct)
          \<top>
          find_free_vmid findFreeVMID"
  unfolding find_free_vmid_def findFreeVMID_def
  apply (simp only: take_vmid_minBound_maxBound)
  apply corres
        apply corres_cases_both (* case find .. of *)
        (* Only None case left over *)
        apply corres
           apply (clarsimp dest!: findNoneD)
           apply (drule bspec, rule UnI1, simp, rule order_refl)
           apply clarsimp
          apply (corres corres: corres_modify_tivial  (* FIXME AARCH64: fix typo *)
                        simp: state_relation_def arch_state_relation_def maxBound_word minBound_word)
         apply wpsimp+
   apply (clarsimp dest!: findNoneD)
   apply (drule bspec, rule UnI1, simp, rule order_refl)
   apply (clarsimp simp: vmid_inv_def)
   apply (frule (1) valid_vmid_tableD)
   apply (drule (1) is_inv_SomeD)
   apply (clarsimp simp: entry_for_asid_def)
   apply (clarsimp simp: vmid_for_asid_2_def in_omonad entry_for_pool_def pool_for_asid_def
                         if_option_eq)
  apply simp
  done

lemma getVMID_corres[corres]:
  "asid' = ucast asid \<Longrightarrow>
   corres (=)
          (vmid_inv and valid_vmid_table and pspace_aligned and pspace_distinct
           and (\<lambda>s. vspace_for_asid asid s \<noteq> None))
          \<top>
          (get_vmid asid) (getVMID asid')"
  unfolding get_vmid_def getVMID_def
  by (corres wp: hoare_drop_imps simp: vspace_for_asid_def entry_for_asid_def | corres_cases_both)+

lemma armContextSwitch_corres[corres]:
  "asid' = ucast asid \<Longrightarrow>
   corres dc
          (vmid_inv and valid_vmid_table and pspace_aligned and pspace_distinct
           and (\<lambda>s. vspace_for_asid asid s \<noteq> None))
          \<top>
          (arm_context_switch pt asid) (armContextSwitch pt asid')"
  unfolding arm_context_switch_def armContextSwitch_def
  by corres

lemma setVMRoot_corres [corres]:
  assumes "t' = t"
  shows "corres dc (tcb_at t and valid_vspace_objs and valid_asid_table and
                    vmid_inv and valid_vmid_table and pspace_aligned and pspace_distinct and
                    valid_objs and valid_global_arch_objs and pspace_in_kernel_window and valid_uses)
                   (no_0_obj')
                   (set_vm_root t) (setVMRoot t')"
proof -
  have global:
    "(\<And>s. P s \<Longrightarrow> valid_global_arch_objs s) \<Longrightarrow>
     corres dc P Q set_global_user_vspace setGlobalUserVSpace" for P Q
    unfolding set_global_user_vspace_def setGlobalUserVSpace_def o_def[where g=arch_state]
    by (corresKsimp corres: corres_gets_global_pt corres_machine_op)

  show ?thesis
  unfolding set_vm_root_def setVMRoot_def catchFailure_def withoutFailure_def throw_def
  apply (rule corres_cross_over_guard[where Q="no_0_obj' and pspace_distinct' and pspace_aligned'"])
   apply (clarsimp simp add: pspace_distinct_cross pspace_aligned_cross state_relation_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="(=) \<circ> cte_map" and P=\<top> and P'=\<top>])
       apply (simp add: getThreadVSpaceRoot_def locateSlotTCB_def locateSlotBasic_def
                        tcbVTableSlot_def cte_map_def objBits_def cte_level_bits_def
                        objBitsKO_def tcb_cnode_index_def to_bl_1 assms cteSizeBits_def)
      apply (rule_tac  R="\<lambda>thread_root. valid_vspace_objs and valid_asid_table and vmid_inv and
                                        valid_vmid_table and pspace_aligned and pspace_distinct and
                                        valid_objs and valid_global_arch_objs and
                                        pspace_in_kernel_window and valid_uses and
                                        cte_wp_at ((=) thread_root) thread_root_slot and
                                        tcb_at (fst thread_root_slot) and
                                        K (snd thread_root_slot = tcb_cnode_index 1)"
                    and R'="\<lambda>thread_root. no_0_obj'"
                in corres_split[OF getSlotCap_corres])
         apply simp
        apply simp
        apply (rename_tac cap cap')
        apply (rule_tac Q="no_0_obj' and (\<lambda>_. isValidVTableRoot cap' \<or> cap' = NullCap)"
                        in corres_cross_over_guard)
         apply clarsimp
         apply (drule (1) tcb_cap_wp_at[where ref="tcb_cnode_index 1" and
                                              Q="\<lambda>cap. is_valid_vtable_root cap \<or> cap=Structures_A.NullCap"])
           apply (simp add: tcb_cap_cases_def)
          apply clarsimp
         apply (clarsimp simp: cte_wp_at_caps_of_state)
         apply (erule disjE; simp?)
         apply (clarsimp simp: is_valid_vtable_root_def
                         split: cap.splits arch_cap.splits option.splits pt_type.splits)
         apply (simp add: isValidVTableRoot_def isVTableRoot_def)
        apply (rule corres_guard_imp)
          apply (rule_tac P="valid_vspace_objs and valid_asid_table and pspace_aligned and
                             valid_vmid_table and vmid_inv and pspace_distinct and valid_objs and
                             pspace_in_kernel_window and valid_uses and
                             valid_global_arch_objs and cte_wp_at ((=) cap) thread_root_slot"
                          in corres_assert_gen_asm2)
          prefer 3
          apply assumption
         apply (case_tac cap; clarsimp simp: isCap_simps catch_throwError intro!: global)
         apply (rename_tac acap acap')
         apply (case_tac acap; clarsimp simp: isCap_simps catch_throwError intro!: global)
         apply (rename_tac pt_t m)
         apply (case_tac pt_t; clarsimp simp: isCap_simps catch_throwError intro!: global)
         apply (case_tac m; clarsimp simp: isCap_simps catch_throwError intro!: global)
         apply (rule corres_guard_imp)
           apply (rule corres_split_catch [where f=lfr and E'="\<lambda>_. \<top>"])
              apply (rule corres_split_eqrE[OF findVSpaceForASID_corres[OF refl]])
                apply (rule whenE_throwError_corres; simp add: lookup_failure_map_def)
                apply (simp add: assertE_liftE liftE_bindE)
                apply (rule corres_assert_gen_asm)
                apply simp
                apply (rule armContextSwitch_corres)
                apply (wpsimp wp: find_vspace_for_asid_wp findVSpaceForASID_inv hoare_drop_imps)+
             apply (rule global, assumption)
            apply wpsimp+
          apply (frule (1) cte_wp_at_valid_objs_valid_cap)
          apply (clarsimp simp: valid_cap_def mask_def wellformed_mapdata_def obj_at_def)
          apply (drule (3) pspace_in_kw_bounded)
          apply (clarsimp simp: kernel_window_range_def pptr_base_def AARCH64.pptrTop_def
                                AARCH64_H.pptrTop_def)
         apply (wpsimp wp: get_cap_wp simp: getThreadVSpaceRoot_def)+
   apply (auto dest!: tcb_at_cte_at_1)
  done
qed

lemma dMo_no_0_obj'[wp]:
  "doMachineOp f \<lbrace>no_0_obj'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (simp add: no_0_obj'_def)

lemma dMo_riscvKSASIDTable_inv[wp]:
  "doMachineOp f \<lbrace>\<lambda>s. P (armKSASIDTable (ksArchState s))\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (clarsimp)

lemma dMo_valid_arch_state'[wp]:
  "\<lbrace>\<lambda>s. P (valid_arch_state' s)\<rbrace> doMachineOp f \<lbrace>\<lambda>_ s. P (valid_arch_state' s)\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (clarsimp)

crunch vcpuDisable, vcpuEnable, vcpuSave, vcpuRestore, deleteASID
  for no_0_obj'[wp]: no_0_obj'
  (simp: crunch_simps wp: crunch_wps getObject_inv getObject_inv_vcpu loadObject_default_inv)

lemma asid_high_bits_of_ucast_ucast[simp]:
  "asid_high_bits_of (ucast (ucast asid :: machine_word)) = asid_high_bits_of asid"
  by (simp add: ucast_down_ucast_id is_down)

lemma invalidateTLBByASID_corres[corres]:
  "asid' = ucast asid \<Longrightarrow>
  corres dc
         (pspace_aligned and pspace_distinct and (\<lambda>s. vspace_for_asid asid s \<noteq> None))
         \<top>
         (invalidate_tlb_by_asid asid) (invalidateTLBByASID asid')"
  unfolding invalidate_tlb_by_asid_def invalidateTLBByASID_def
  apply corres
      (* when vs case .. of *)
      apply (corres_cases; (solves \<open>rule corres_inst[where P=\<top> and P'=\<top>], clarsimp\<close>)?)
      (* when-True case *)
      apply (clarsimp, corres)
     apply wpsimp+
  done

lemma invalidate_vmid_entry_entry_for_asid[wp]:
  "invalidate_vmid_entry vmid \<lbrace>\<lambda>s. P (entry_for_asid asid s)\<rbrace>"
  unfolding invalidate_vmid_entry_def
  by wpsimp

lemma invalidateASIDEntry_corres[corres]:
  "asid' = ucast asid \<Longrightarrow>
  corres dc
         (pspace_aligned and pspace_distinct and (\<lambda>s. vspace_for_asid asid s \<noteq> None))
         \<top>
         (invalidate_asid_entry asid) (invalidateASIDEntry asid')"
  unfolding invalidate_asid_entry_def invalidateASIDEntry_def
  by (corres simp: vspace_for_asid_def)

lemma deleteASID_corres [corres]:
  assumes "asid' = ucast asid" "pm' = pm"
  shows "corres dc (invs and K (asid \<noteq> 0)) no_0_obj'
                (delete_asid asid pm) (deleteASID asid' pm')"
  unfolding delete_asid_def deleteASID_def using assms
  apply simp
  apply (corres simp: liftM_def | corres_cases_both)+
         apply (simp add: mask_asid_low_bits_ucast_ucast asid_low_bits_of_def ucast_ucast_a is_down
                          asid_pool_relation_def abs_asid_entry_def split: option.splits)
        apply corres
                 apply (rule ext)
                 apply (clarsimp simp: mask_asid_low_bits_ucast_ucast asid_low_bits_of_def
                                       ucast_ucast_a is_down asid_pool_relation_def)
                 apply (erule notE)
                 apply word_eqI_solve
                apply (corres corres: getCurThread_corres)
               apply (wpsimp simp: cur_tcb_def[symmetric]
                             wp: set_asid_pool_None_vmid_inv set_asid_pool_vspace_objs_unmap_single)
              apply (wp getASID_wp)+
           apply (rename_tac p pool pool' a b)
           apply (rule_tac Q'="\<lambda>_ s. invs s \<and>
                                    (\<exists>high. asid_table s high = Some p \<and>
                                            vmid_for_asid s (asid_of high (asid_low_bits_of asid)) =
                                              None)" in hoare_strengthen_post)
            apply (wp hoare_vcg_ex_lift invalidate_asid_entry_vmid_for_asid)
           apply (fastforce simp: asid_pools_at_eq ako_asid_pools_of)
          apply (wp hoare_drop_imp hoare_vcg_all_lift)
         apply (wp invalidate_tlb_by_asid_invs hoare_vcg_ex_lift)
        apply wp
       apply (clarsimp, wp)
      apply (wp getASID_wp)
     apply wp
    apply (wp hoare_vcg_all_lift hoare_drop_imp)
   apply (fastforce simp: pool_for_asid_def vspace_for_asid_def entry_for_asid_def word_neq_0_conv
                          entry_for_pool_def in_omonad
                    intro!: pool_for_asid_ap_at)
  apply simp
  done

lemma valid_arch_state_unmap_strg':
  "valid_arch_state' s \<longrightarrow>
   valid_arch_state' (s\<lparr>ksArchState :=
                        armKSASIDTable_update (\<lambda>_. (armKSASIDTable (ksArchState s))(ptr := None))
                         (ksArchState s)\<rparr>)"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def)
  apply (auto simp: ran_def split: if_split_asm option.splits)
  done

crunch invalidateASIDEntry
  for armKSASIDTable_inv[wp]: "\<lambda>s. P (armKSASIDTable (ksArchState s))"
  (wp: getObject_inv crunch_wps simp: loadObject_default_def)

lemma is_aligned_asid_low_bits_of_zero:
  "is_aligned asid asid_low_bits \<longleftrightarrow> asid_low_bits_of asid = 0"
  apply (simp add: is_aligned_mask word_eq_iff word_size asid_bits_defs asid_bits_of_defs nth_ucast)
  apply (intro iffI allI; drule_tac x=n in spec; fastforce)
  done

lemma asid_high_bits_of_0[simp]:
  "asid_high_bits_of 0 = 0"
  by (simp add: asid_high_bits_of_def)

lemma asid_low_bits_of_0[simp]:
  "asid_low_bits_of 0 = 0"
  by (simp add: asid_low_bits_of_def)

lemma invalidate_asid_entry_asid_pool_doms[wp]:
  "invalidate_asid_entry asid \<lbrace>\<lambda>s. P (asid_pools_of s ||> dom)\<rbrace>"
  unfolding invalidate_asid_entry_def invalidate_asid_def invalidate_vmid_entry_def
  apply wpsimp
  apply (fastforce simp: opt_map_def split: option.splits elim!: rsubst[where P=P])
  done

declare getCurThread_corres[corres] (* FIXME AARCH64: declare at origin *)

lemma valid_asid_table_None_upd:
  "valid_asid_table_2 table pools \<Longrightarrow> valid_asid_table_2 (table(idx := None)) pools"
  unfolding valid_asid_table_2_def
  by (auto simp: ran_def inj_on_def)

lemma asid_low_le_mask_asidBits[simp]:
  "UCAST(asid_low_len \<rightarrow> asid_len) asid_low \<le> mask asid_low_bits"
  by (rule ucast_leq_mask, simp add: asid_low_bits_def)

lemma ucast_eq_from_zip_asid_low_bits:
  "\<lbrakk>(x, y) \<in> set (zip [0 .e. mask asid_low_bits] [0 .e. mask asid_low_bits]);
    is_aligned asid asid_low_bits\<rbrakk>
   \<Longrightarrow> ucast asid + y = ucast (asid + x)" for asid :: AARCH64_A.asid
  apply (clarsimp simp: in_set_zip upto_enum_word_nth)
  apply (subst add.commute[where a=asid])
  apply (drule nat_le_Suc_less_imp)+
  apply (simp add: ucast_add_mask_aligned[where n=asid_low_bits] mask_def word_le_nat_alt
                   asid_low_bits_def unat_of_nat_eq ucast_of_nat is_down ucast_of_nat_small)
  done

lemma deleteASIDPool_corres:
  assumes "base' = ucast base" "ptr' = ptr"
  shows "corres dc (invs and K (is_aligned base asid_low_bits) and asid_pool_at ptr)
                   (no_0_obj')
                   (delete_asid_pool base ptr) (deleteASIDPool base' ptr)"
  using assms
  apply (simp add: delete_asid_pool_def deleteASIDPool_def)
  apply (corres simp: liftM_def mapM_discarded)
          apply corres_split (* deal with mapM_x manually *)
             apply (rule_tac P="\<lambda>s. invs s \<and> pool_for_asid base s = Some ptr \<and>
                                    (asid_pools_of s ||> dom) ptr = Some (dom pool) \<and>
                                    is_aligned base asid_low_bits"
                             and P'="no_0_obj'" in corres_mapM_x')
                (* mapM_x body *)
                apply corres
                   (* "when" condition *)
                   apply (clarsimp simp: asid_pool_relation_def in_set_zip upto_enum_word_nth)
                   apply (simp add: ucast_of_nat is_down asid_low_bits_def ucast_of_nat_small)
                  apply (rule corres_gen_asm[where F="is_aligned base asid_low_bits"])
                  apply (corres term_simp: ucast_eq_from_zip_asid_low_bits mask_def)
                 apply clarsimp
                 apply (rename_tac low low' s s' entry)
                 apply (clarsimp simp: vspace_for_asid_def entry_for_asid_def pool_for_asid_def
                                       in_omonad asid_high_bits_of_add asid_low_bits_of_add
                                       mask_def entry_for_pool_def
                                 dest!: set_zip_leftD)
                 apply (rule conjI, fastforce)
                 apply (clarsimp simp flip: word_neq_0_conv mask_2pm1)
                 apply (prop_tac "valid_asid_map s", fastforce)
                 apply (prop_tac "base = 0 \<and> low = 0")
                  apply (simp add: asid_low_bits_def)
                  apply (subst (asm) word_plus_and_or_coroll, word_eqI, force)
                  apply (fastforce simp: word_or_zero)
                 apply (clarsimp simp: valid_asid_map_def entry_for_asid_def obind_None_eq
                                       pool_for_asid_def entry_for_pool_def in_omonad)
                 apply blast
                apply fastforce
               apply (wpsimp wp: invalidate_tlb_by_asid_invs)+
             apply (simp add: mask_def asid_low_bits_def)
            apply (corres' \<open>fastforce simp: asid_high_bits_of_def asid_low_bits_def up_ucast_inj_eq
                                            state_relation_def arch_state_relation_def\<close>
                           corres: corres_modify_tivial)
           (* mapM_x wp conditions *)
           apply (rename_tac table table' pool pool')
           apply (rule hoare_strengthen_post)
            apply (rule_tac I="\<lambda>s. invs s \<and> is_aligned base asid_low_bits \<and> table = asid_table s \<and>
                                   pool_for_asid base s = Some ptr \<and>
                                   (asid_pools_of s ||> dom) ptr = Some (dom pool)" and
                            V="\<lambda>xs s. \<forall>asid_low \<in> set xs.
                                         vmid_for_asid s (asid_of (asid_high_bits_of base)
                                                                  (ucast asid_low)) = None"
                            in mapM_x_inv_wp3)
            apply (wpsimp wp: invalidate_asid_entry_vmid_for_asid_add hoare_vcg_op_lift
                              invalidate_tlb_by_asid_invs)
            apply (rule conjI; clarsimp)
             apply (drule arg_cong[where f=set], drule sym[where t="set xs" for xs])
             apply fastforce
            apply (clarsimp simp: vmid_for_asid_def obind_None_eq)
            apply (rule ccontr)
            apply (clarsimp simp: entry_for_pool_def in_omonad pool_for_asid_def)
            apply (fastforce dest: dom_eq_All)
           (* mapM_x invariant implies post condition;
              some manual massaging to avoid massive duplication *)
           apply (simp (no_asm) del: fun_upd_apply)
           apply (strengthen invs_vmid_inv invs_valid_global_arch_objs invs_implies invs_valid_uses
                             invs_valid_vmid_table valid_asid_table_None_upd)
           (* can't move these into previous strengthen, otherwise will be applied too early *)
           apply (strengthen invs_arm_asid_table_unmap invs_valid_asid_table)
           apply (clarsimp simp: o_def)
           apply (rename_tac asid_low)
           apply (erule_tac x="ucast asid_low" in allE)
           apply (fastforce simp: ucast_up_ucast_id is_up)
          apply (wpsimp wp: mapM_x_wp' getASID_wp)+
   apply (fastforce simp: is_aligned_asid_low_bits_of_zero pool_for_asid_def in_omonad)
  apply (clarsimp simp: is_aligned_asid_low_bits_of_zero)
  done

crunch setVMRoot
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (simp: crunch_simps loadObject_default_def wp: crunch_wps getObject_inv)

lemmas setVMRoot_typ_ats [wp] = typ_at_lifts [OF setVMRoot_typ_at']

lemma getObject_PTE_corres'':
  assumes "p' = p"
  shows "corres pte_relation' (pte_at pt_t p and pspace_aligned and pspace_distinct) \<top>
                              (get_pte pt_t p) (getObject p')"
  using assms getObject_PTE_corres by simp

crunch unmapPageTable, unmapPage
  for aligned'[wp]: "pspace_aligned'"
  and distinct'[wp]: "pspace_distinct'"
  and ctes [wp]: "\<lambda>s. P (ctes_of s)"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (simp: crunch_simps
   wp: crunch_wps getObject_inv loadObject_default_inv)

crunch storePTE
  for no_0_obj'[wp]: no_0_obj'
  and valid_arch'[wp]: valid_arch_state'
  and cur_tcb'[wp]: cur_tcb'
  and pspace_canonical'[wp]: pspace_canonical'

lemma unmapPageTable_corres:
  assumes "asid' = ucast asid" "vptr' = vptr" "pt' = pt"
  shows "corres dc
          (invs and (\<lambda>s. vspace_for_asid asid s \<noteq> Some pt) and K (0 < asid \<and> vptr \<in> user_region))
          no_0_obj'
          (unmap_page_table asid vptr pt)
          (unmapPageTable asid' vptr' pt')"
  apply (clarsimp simp: assms unmap_page_table_def unmapPageTable_def ignoreFailure_def const_def)
  apply (corres corres: findVSpaceForASID_corres lookupPTFromLevel_corres storePTE_corres'
                        corres_returnTT
                wp: pt_lookup_from_level_wp
         | corres_cases_left)+
   apply (fastforce simp: pte_at_def dest: vspace_for_asid_vs_lookup)
  apply simp
  done

(* FIXME AARCH64: move (all arches) *)
lemma corres_split_strengthen_ftE:
  "\<lbrakk> corres (ftr \<oplus> r') P P' f j;
      \<And>rv rv'. r' rv rv' \<Longrightarrow> corres (ftr' \<oplus> r) (R rv) (R' rv') (g rv) (k rv');
      \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,-; \<lbrace>Q'\<rbrace> j \<lbrace>R'\<rbrace>,- \<rbrakk>
    \<Longrightarrow> corres (dc \<oplus> r) (P and Q) (P' and Q') (f >>=E (\<lambda>rv. g rv)) (j >>=E (\<lambda>rv'. k rv'))"
  apply (rule_tac r'=r' in corres_splitEE)
     apply (erule corres_rel_imp)
     apply (case_tac x, auto)[1]
    apply (rule corres_rel_imp, assumption)
    apply (case_tac x, auto)[1]
   apply (simp add: validE_R_def)+
  done

lemma checkMappingPPtr_corres:
  "\<lbrakk> pte_relation' pte pte'; pptr' = pptr \<rbrakk> \<Longrightarrow>
   corres (lfr \<oplus> dc) \<top> \<top>
          (whenE (AARCH64_A.is_PagePTE pte \<longrightarrow> pptr_from_pte pte \<noteq> pptr)
                 (throwError ExceptionTypes_A.InvalidRoot))
          (checkMappingPPtr pptr' pte')"
  apply (simp add: liftE_bindE checkMappingPPtr_def)
  apply (cases pte; simp add: pte_base_addr_def pptr_from_pte_def)
  apply (auto simp: whenE_def unlessE_def corres_returnOk lookup_failure_map_def)
  done

crunch checkMappingPPtr
  for inv[wp]: "P"
  (wp: crunch_wps loadObject_default_inv simp: crunch_simps)

lemmas liftE_get_pte_corres = getObject_PTE_corres[THEN corres_liftE_rel_sum[THEN iffD2]]

lemma invalidateTLBByASIDVA_corres[corres]:
  "\<lbrakk> asid' = ucast asid; vptr' = vptr \<rbrakk> \<Longrightarrow>
   corres dc
          (pspace_aligned and pspace_distinct and (\<lambda>s. vspace_for_asid asid s \<noteq> None))
          \<top>
          (invalidate_tlb_by_asid_va asid vptr) (invalidateTLBByASIDVA asid' vptr')"
  unfolding invalidate_tlb_by_asid_va_def invalidateTLBByASIDVA_def
  by (corres term_simp: wordBits_def word_bits_def word_size
      | corres_cases_left
      | rule corres_inst[where P=\<top> and P'=\<top>], clarsimp)+

crunch lookupPTSlot
  for inv: "P"

lemma unmapPage_corres[corres]:
  assumes "sz' = sz" "asid' = ucast asid" "vptr' = vptr" "pptr' = pptr"
  shows "corres dc (invs and K (valid_unmap sz (asid,vptr) \<and> vptr \<in> user_region))
                   (no_0_obj')
                   (unmap_page sz asid vptr pptr)
                   (unmapPage sz' asid' vptr' pptr')"
  apply (clarsimp simp: assms unmap_page_def unmapPage_def ignoreFailure_def const_def)
  apply (corres corres: findVSpaceForASID_corres lookupPTSlot_corres[@lift_corres_args]
                        getObject_PTE_corres' checkMappingPPtr_corres corres_returnTT
                simp: lookup_failure_map_def
                wp: hoare_drop_imp lookupPTSlot_inv
         | corres_cases_both)+
   apply (clarsimp simp: valid_unmap_def cong: conj_cong)
   apply (fastforce dest: vspace_for_asid_vs_lookup pt_lookup_slot_vs_lookup_slotI
                    intro: vs_lookup_slot_pte_at)
  apply simp
  done

definition
  "mapping_map \<equiv> \<lambda>(pte, r, level) (pte', r'). pte_relation' pte pte' \<and> r' = r"

definition
  "page_invocation_map pgi pgi' \<equiv> case pgi of
    AARCH64_A.PageMap c slot m \<Rightarrow>
      \<exists>c' m'. pgi' = PageMap c' (cte_map slot) m' \<and>
              acap_relation c c' \<and>
              mapping_map m m'
  | AARCH64_A.PageUnmap c ptr \<Rightarrow>
      \<exists>c'. pgi' = PageUnmap c' (cte_map ptr) \<and>
      acap_relation c c'
  | AARCH64_A.PageGetAddr ptr \<Rightarrow>
      pgi' = PageGetAddr ptr
  | AARCH64_A.PageFlush type vstart vend pstart vs asid \<Rightarrow>
      pgi' = PageFlush type vstart vend pstart vs (ucast asid)"

definition
  "valid_page_inv' pgi \<equiv>
  case pgi of
    PageMap cap ptr m \<Rightarrow>
      K (isPagePTE (fst m)) and
      cte_wp_at' (is_arch_update' (ArchObjectCap cap)) ptr and valid_cap' (ArchObjectCap cap)
  | PageUnmap cap ptr \<Rightarrow>
      K (isFrameCap cap) and
      cte_wp_at' (is_arch_update' (ArchObjectCap cap)) ptr and valid_cap' (ArchObjectCap cap)
  | PageGetAddr ptr \<Rightarrow> \<top>
  | PageFlush ty start end pstart space asid \<Rightarrow> \<top>"

lemma message_info_to_data_eqv:
  "wordFromMessageInfo (message_info_map mi) = message_info_to_data mi"
  apply (cases mi)
  apply (simp add: wordFromMessageInfo_def msgLengthBits_def msgExtraCapBits_def msgMaxExtraCaps_def shiftL_nat)
  done

lemma message_info_from_data_eqv:
  "message_info_map (data_to_message_info rv) = messageInfoFromWord rv"
  using shiftr_mask_eq[where 'a=64 and n=12]
  by (auto simp: data_to_message_info_def messageInfoFromWord_def Let_def not_less
                 msgLengthBits_def msgExtraCapBits_def msgMaxExtraCaps_def mask_def
                 shiftL_nat msgMaxLength_def msgLabelBits_def)

lemma setMessageInfo_corres:
 "mi' = message_info_map mi \<Longrightarrow>
  corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
            (set_message_info t mi) (setMessageInfo t mi')"
  apply (simp add: setMessageInfo_def set_message_info_def)
  apply (subgoal_tac "wordFromMessageInfo (message_info_map mi) =
                      message_info_to_data mi")
   apply (simp add: asUser_setRegister_corres msg_info_register_def
                    msgInfoRegister_def)
  apply (simp add: message_info_to_data_eqv)
  done


lemma set_mi_invs'[wp]: "\<lbrace>invs' and tcb_at' t\<rbrace> setMessageInfo t a \<lbrace>\<lambda>x. invs'\<rbrace>"
  by (simp add: setMessageInfo_def) wp

lemma set_mi_tcb' [wp]:
  "\<lbrace> tcb_at' t \<rbrace> setMessageInfo receiver msg \<lbrace>\<lambda>rv. tcb_at' t\<rbrace>"
  by (simp add: setMessageInfo_def) wp


lemma setMRs_typ_at':
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> setMRs receiver recv_buf mrs \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  by (simp add: setMRs_def zipWithM_x_mapM split_def, wp crunch_wps)

lemmas setMRs_typ_at_lifts[wp] = typ_at_lifts [OF setMRs_typ_at']

lemma set_mrs_invs'[wp]:
  "\<lbrace> invs' and tcb_at' receiver \<rbrace> setMRs receiver recv_buf mrs \<lbrace>\<lambda>rv. invs' \<rbrace>"
  apply (simp add: setMRs_def)
  apply (wp dmo_invs' no_irq_mapM no_irq_storeWord crunch_wps|
         simp add: zipWithM_x_mapM split_def)+
  done

crunch unmapPage
  for cte_at'[wp]: "cte_at' p"
  (wp: crunch_wps simp: crunch_simps)

lemma vs_lookup_slot_vspace_for_asidD:
  "\<lbrakk> vs_lookup_slot level asid vref s = Some (level, slot); level \<le> max_pt_level; valid_asid_map s \<rbrakk>
   \<Longrightarrow> vspace_for_asid asid s \<noteq> None"
  by (fastforce simp: vs_lookup_slot_def vs_lookup_table_def vspace_for_asid_def in_omonad
                      valid_asid_map_def entry_for_asid_def vspace_for_pool_def obind_None_eq
                simp flip: word_neq_0_conv
                split: if_split_asm)

lemma performPageInvocation_corres:
  assumes "page_invocation_map pgi pgi'"
  shows "corres (=) (invs and valid_page_inv pgi) (no_0_obj' and valid_page_inv' pgi')
                    (perform_page_invocation pgi) (performPageInvocation pgi')"
  apply (rule corres_cross_over_guard [where Q="no_0_obj' and valid_page_inv' pgi' and
                                                pspace_aligned' and pspace_distinct'"])
   apply (fastforce intro!: pspace_aligned_cross pspace_distinct_cross)
  using assms
  unfolding perform_page_invocation_def performPageInvocation_def page_invocation_map_def
  apply (cases pgi; clarsimp simp: valid_page_inv_def mapping_map_def)
     apply (rename_tac cap ct_slot_ref ct_slot_idx pte slot level cap' pte')
     apply (simp add: perform_pg_inv_map_def bind_assoc)
     apply (corres corres: updateCap_same_master | fastforce | corres_cases)+
                  apply (rule_tac F="arch_cap.is_FrameCap cap" in corres_gen_asm)
                  apply ((corres corres: corres_assert_opt_l simp: arch_cap.is_FrameCap_def
                          | corres_cases)+)[1]
                 apply (rule corres_return_eq_same, simp)
                apply wp
               apply wp
              apply clarsimp
              apply (wp get_pte_wp hoare_drop_imp hoare_vcg_op_lift)+
      apply (clarsimp simp: invs_valid_objs invs_distinct invs_psp_aligned)
      apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def is_cap_simps same_ref_def)
      apply (frule (3) vs_lookup_slot_pte_at)
      apply (clarsimp simp: cap_master_cap_def split: arch_cap.splits)
      apply (fastforce dest!: vs_lookup_slot_vspace_for_asidD)
     apply (clarsimp simp: valid_page_inv'_def cte_wp_at_ctes_of)
    apply (simp add: perform_pg_inv_unmap_def bind_assoc)
    apply (corres corres: corres_assert_gen_asm_l simp: liftM_def)
      apply (corres_cases_both; (solves \<open>rule corres_trivial, clarsimp simp: arch_cap.is_FrameCap_def\<close>)?)
       apply (corres corres: getSlotCap_corres)
           apply (rename_tac old_cap old_cap')
           apply (rule_tac F="is_frame_cap old_cap" in corres_gen_asm)
           apply (corres corres: updateCap_same_master
                         simp: is_frame_cap_def arch_cap.is_FrameCap_def update_map_data_def)
          apply (wp get_cap_wp)+
      apply corres_cases_both
      apply (corres simp: arch_cap.is_FrameCap_def corres: getSlotCap_corres)
          apply (rename_tac old_cap old_cap')
          apply (rule_tac F="is_frame_cap old_cap" in corres_gen_asm)
          apply (corres corres: updateCap_same_master
                        simp: is_frame_cap_def arch_cap.is_FrameCap_def update_map_data_def)
         apply (wpsimp wp: get_cap_wp hoare_vcg_op_lift)+
     apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct)
     apply (clarsimp simp: cte_wp_at_caps_of_state wellformed_pte_def
                           cap_master_cap_simps is_cap_simps update_map_data_def mdata_map_def
                           wellformed_mapdata_def valid_arch_cap_def)
    apply (clarsimp simp: valid_page_inv'_def cte_wp_at_ctes_of)
   apply (clarsimp simp: perform_pg_inv_get_addr_def fromPAddr_def)
  apply (clarsimp simp: perform_flush_def)
  apply (rename_tac type vstart vend pstart vs asid)
  apply (case_tac type;
         simp add: do_flush_def doFlush_def;
         corres simp: doMachineOp_bind do_machine_op_bind empty_fail_bind)
  done

definition
  "page_table_invocation_map pti pti' \<equiv>
  case pti of
     AARCH64_A.PageTableMap cap ptr pte pt_slot level \<Rightarrow>
       \<exists>cap' pte'. pti' = PageTableMap cap' (cte_map ptr) pte' pt_slot \<and>
                   cap_relation (Structures_A.ArchObjectCap cap) cap' \<and>
                   pte_relation' pte pte'
   | AARCH64_A.PageTableUnmap cap ptr \<Rightarrow>
       \<exists>cap'. pti' = PageTableUnmap cap' (cte_map ptr) \<and> acap_relation cap cap'"

definition
  "valid_pti' pti \<equiv>
   case pti of
     PageTableMap cap slot pte pteSlot \<Rightarrow>
       cte_wp_at' (is_arch_update' cap) slot and valid_cap' cap and K (ppn_bounded pte)
   | PageTableUnmap cap slot \<Rightarrow>
       cte_wp_at' (is_arch_update' (ArchObjectCap cap)) slot and valid_cap' (ArchObjectCap cap)
         and K (isPageTableCap cap)"

(* extend with arch rules *)
lemmas store_pte_typ_ats[wp] = store_pte_typ_ats abs_atyp_at_lifts[OF store_pte_typ_at]

lemma pte_bits_leq_pt_bits[simp, intro!]:
  "pte_bits \<le> pt_bits pt_t"
  by (simp add: bit_simps)

lemma pt_bits_le_word_len[simplified, simp, intro!]:
  "pt_bits pt_t < LENGTH(machine_word_len)"
  by (simp add: bit_simps)

lemma clear_page_table_corres:
  "corres dc (pspace_aligned and pspace_distinct and pt_at pt_t p)
             \<top>
    (mapM_x (swp (store_pte pt_t) AARCH64_A.InvalidPTE) [p , p + 2^pte_bits .e. p + mask (pt_bits pt_t)])
    (mapM_x (swp storePTE AARCH64_H.InvalidPTE) [p , p + 2^pte_bits .e. p + mask (pt_bits pt_t)])"
  apply (rule_tac F="is_aligned p (pt_bits pt_t)" in corres_req)
   apply (clarsimp simp: obj_at_def a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
   apply (drule(1) pspace_alignedD)
   apply (simp add: table_size_def pt_bits_def)
  apply (simp add: mask_def flip: p_assoc_help)
  apply (simp add: upto_enum_step_subtract[where x=p and y="p + 2^pte_bits"]
                   is_aligned_no_overflow
                   upto_enum_step_red[where us=pte_bits, simplified]
                   mapM_x_mapM liftM_def[symmetric])
  apply (rule corres_guard_imp,
         rule_tac r'=dc and S="(=)"
               and Q="\<lambda>xs s. \<forall>x \<in> set xs. pte_at pt_t x s \<and> pspace_aligned s \<and> pspace_distinct s"
               and Q'="\<lambda>_. \<top>"
                in corres_mapM_list_all2, simp_all)
      apply (rule corres_guard_imp, rule storePTE_corres)
        apply (simp add:pte_relation_def)+
     apply (wp hoare_vcg_const_Ball_lift | simp)+
   apply (simp add: list_all2_refl)
  apply (clarsimp simp: upto_enum_step_def pte_bits_def word_size_bits_def)
  apply (erule page_table_pte_atI[simplified shiftl_t2n mult.commute bit_simps, simplified])
   apply (simp add: bit_simps word_less_nat_alt word_le_nat_alt unat_of_nat)
  apply simp
  done

lemmas unmapPageTable_typ_ats[wp] = typ_at_lifts[OF unmapPageTable_typ_at']

lemma performPageTableInvocation_corres:
  "page_table_invocation_map pti pti' \<Longrightarrow>
   corres dc
          (invs and valid_pti pti) (no_0_obj' and valid_pti' pti')
          (perform_page_table_invocation pti)
          (performPageTableInvocation pti')"
  apply (rule corres_cross_over_guard [where Q="no_0_obj' and valid_pti' pti' and
                                                pspace_aligned' and pspace_distinct'"])
   apply (fastforce intro!: pspace_aligned_cross pspace_distinct_cross)
  apply (simp add: perform_page_table_invocation_def performPageTableInvocation_def
                   page_table_invocation_map_def)
  apply (cases pti)
   apply (rename_tac cap slot pte pte_slot)
   apply (clarsimp simp:  perform_pt_inv_map_def)
   apply (rule corres_name_pre)
   apply (clarsimp simp: valid_pti_def valid_pti'_def
                  split: arch_cap.splits capability.split_asm arch_capability.split_asm)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF updateCap_same_master])
        apply simp
       apply (rule corres_split[OF storePTE_corres])
          apply assumption
         apply (rule corres_machine_op, rule corres_Id; simp)
        apply wpsimp+
    apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def
                          invs_valid_objs invs_psp_aligned invs_distinct)
    apply (case_tac cap; simp add: is_cap_simps cap_master_cap_simps)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_pti'_def)
  apply (clarsimp simp: perform_pt_inv_unmap_def)
  apply (rename_tac acap a b acap')
  apply (rule_tac F="AARCH64_A.is_PageTableCap acap" in corres_req; clarsimp)
   apply (clarsimp simp: valid_pti_def)
  apply (clarsimp simp: AARCH64_A.is_PageTableCap_def split_def cong: option.case_cong)
  apply (simp add: case_option_If2 split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (rule corres_if3)
         apply (fastforce simp: acap_map_data_def mdata_map_def is_PageTableCap_def)
        apply (rule corres_split[OF unmapPageTable_corres])
             apply (clarsimp simp: mdata_map_def)
            apply (clarsimp simp: mdata_map_def)
           apply (rule refl)
          apply (simp (no_asm) add: p_assoc_help flip: mask_2pm1)
          apply (corres corres: clear_page_table_corres)
         apply wp+
       apply (rule corres_trivial, simp)
      apply (simp add: liftM_def)
      apply (rule corres_split[OF getSlotCap_corres[OF refl]])
        apply (rule_tac F="is_pt_cap x" in corres_gen_asm)
        apply (rule updateCap_same_master)
        apply (clarsimp simp: is_cap_simps update_map_data_def)
       apply (wpsimp wp: get_cap_wp mapM_x_wp' hoare_vcg_all_lift hoare_vcg_imp_lift'
                     simp: wellformed_pte_def)+
   apply (clarsimp simp: valid_pti_def valid_arch_cap_def cte_wp_at_caps_of_state
                         invs_valid_objs invs_psp_aligned invs_distinct
                         cap_master_cap_simps is_cap_simps update_map_data_def
                         wellformed_mapdata_def)
  apply (clarsimp simp: valid_pti'_def cte_wp_at_ctes_of)
  done

definition
  "asid_pool_invocation_map ap \<equiv> case ap of
  asid_pool_invocation.Assign asid p slot \<Rightarrow> Assign (ucast asid) p (cte_map slot)"

definition
  "valid_apinv' ap \<equiv>
    case ap of Assign asid p slot \<Rightarrow>
      cte_wp_at' (isArchCap isPageTableCap o cteCap) slot and K (0 < asid \<and> asid_wf asid)"

definition
  "valid_vcpuinv' vi \<equiv> case vi of
    VCPUSetTCB v t \<Rightarrow> vcpu_at' v and ex_nonz_cap_to' v and ex_nonz_cap_to' t
  | VCPUInjectIRQ v n q \<Rightarrow> \<top>
  | VCPUReadRegister v rg \<Rightarrow> \<top>
  | VCPUWriteRegister v _ _ \<Rightarrow> \<top>
  | VCPUAckVPPI v _ \<Rightarrow> \<top>"

lemma performASIDPoolInvocation_corres[corres]:
  "\<lbrakk> ap' = asid_pool_invocation_map ap \<rbrakk> \<Longrightarrow>
   corres dc
          (valid_objs and pspace_aligned and pspace_distinct and valid_arch_state and valid_apinv ap)
          (no_0_obj' and valid_apinv' ap')
          (perform_asid_pool_invocation ap)
          (performASIDPoolInvocation ap')"
  apply (clarsimp simp: perform_asid_pool_invocation_def performASIDPoolInvocation_def)
  apply (cases ap, simp add: asid_pool_invocation_map_def)
  apply (corres corres: getSlotCap_corres corres_assert_gen_asm_l updateCap_same_master
                simp: liftM_def store_asid_pool_entry_def
                term_simp: cap.is_ArchObjectCap_def arch_cap.is_PageTableCap_def
                           update_map_data_def)
          apply (fastforce simp: asid_pool_relation_def abs_asid_entry_def cap.is_ArchObjectCap_def
                                 arch_cap.is_PageTableCap_def inv_def ucast_up_inj)
         apply (wpsimp wp: set_cap_typ_at hoare_drop_imp get_cap_wp)+
   apply (clarsimp simp: valid_apinv_def cte_wp_at_caps_of_state cap_master_cap_simps is_cap_simps
                         arch_cap.is_PageTableCap_def is_vsroot_cap_def update_map_data_def in_omonad)
   apply (drule (1) caps_of_state_valid_cap)
   apply (simp add: valid_cap_def obj_at_def)
  apply (clarsimp simp: valid_apinv'_def cte_wp_at_ctes_of)
  apply (fastforce intro!: pspace_aligned_cross pspace_distinct_cross)
  done

crunch doMachineOp
  for arch[wp]: "\<lambda>s. P (ksArchState s)"
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and cur'[wp]: "\<lambda>s. P (ksCurThread s)"
  and cteCaps_of[wp]: "\<lambda>s. P (cteCaps_of s)"
  and dmo_global_refs'[wp]: "\<lambda>s. P (global_refs' s)"
  and ksPSpace[wp]: "\<lambda>s. P (ksPSpace s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"

crunch vcpuSave, vcpuDisable, vcpuEnable, vcpuRestore
  for obj_at'_no_vcpu[wp]: "\<lambda>s. P (obj_at' (P' :: ('a :: no_vcpu) \<Rightarrow> bool) t s)"
  (simp: crunch_simps wp: crunch_wps)

lemma vcpuSwitch_obj_at'_no_vcpu[wp]:
  "vcpuSwitch param_a \<lbrace>\<lambda>s. P (obj_at' (P' :: ('a :: no_vcpu) \<Rightarrow> bool) t s)\<rbrace>"
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | assumption)+

lemma dmo_setVSpaceRoot_invs'[wp]:
  "doMachineOp (setVSpaceRoot r a) \<lbrace>invs'\<rbrace>"
  by (wp dmo_invs_lift')

lemma dmo_setVSpaceRoot_irq_masks[wp]:
  "doMachineOp (setVSpaceRoot r a) \<lbrace>\<lambda>s. P (irq_masks (ksMachineState s))\<rbrace>"
  unfolding doMachineOp_def
  apply wpsimp
  apply (drule use_valid, rule setVSpaceRoot_irq_masks; assumption)
  done

lemma dmo_setVSpaceRoot_memory[wp]:
  "doMachineOp (setVSpaceRoot r a) \<lbrace>\<lambda>s. P (underlying_memory (ksMachineState s))\<rbrace>"
  unfolding doMachineOp_def
  apply wpsimp
  apply (drule use_valid, rule setVSpaceRoot_underlying_memory_inv; assumption)
  done

lemma dmo_setVSpaceRoot_invs_no_cicd'[wp]:
  "doMachineOp (setVSpaceRoot r a) \<lbrace>invs_no_cicd'\<rbrace>"
  by (wp dmo_invs_no_cicd_lift')

lemma getObject_tcb_hyp_sym_refs:
      "\<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of' s)\<rbrace> getObject p
       \<lbrace>\<lambda>rv. case atcbVCPUPtr (tcbArch rv) of None \<Rightarrow> \<lambda>_. True
             | Some x \<Rightarrow> ko_wp_at' (is_vcpu' and hyp_live') x\<rbrace>"
  apply (wpsimp wp: getObject_tcb_wp)
  apply (clarsimp simp: typ_at_tcb'[symmetric] typ_at'_def ko_wp_at'_def[of _ p]
                split: option.splits)
  apply (case_tac ko; simp)
  apply (rename_tac tcb)
  apply (rule_tac x=tcb in exI; rule conjI, clarsimp simp: obj_at'_def)
  apply (clarsimp, rule context_conjI, clarsimp simp: obj_at'_def)
  apply (drule ko_at_state_hyp_refs_ofD')
  apply (simp add: hyp_refs_of'_def sym_refs_def)
  apply (erule_tac x=p in allE, simp)
  apply (drule state_hyp_refs_of'_elemD)
  apply (clarsimp simp: hyp_refs_of_rev')
  apply (simp add: ko_wp_at'_def, erule exE,
         clarsimp simp: is_vcpu'_def hyp_live'_def arch_live'_def)
  done

lemma setASIDPool_valid_objs[wp]:
  "setObject p (ap::asidpool) \<lbrace>valid_objs'\<rbrace>"
  apply (wp setObject_valid_objs'[where P=\<top>])
   apply (clarsimp simp: updateObject_default_def in_monad valid_obj'_def)
  apply simp
  done

lemma setASIDPool_valid_mdb[wp]:
  "setObject p (ap::asidpool) \<lbrace>valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

lemma setASIDPool_nosch[wp]:
  "setObject p (ap::asidpool) \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>"
  by (wp setObject_nosch updateObject_default_inv|simp)+

lemma setASIDPool_ksQ[wp]:
  "setObject p (ap::asidpool) \<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv|simp)+

lemma setASIDPool_inQ[wp]:
  "setObject ptr (ap::asidpool) \<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def)
  apply (wpsimp wp: setObject_ko_wp_at simp: objBits_simps)
    apply (simp add: pageBits_def)
   apply simp
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def)
  done

lemma setASIDPool_qsL1[wp]:
  "setObject p (ap::asidpool) \<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv|simp)+

lemma setASIDPool_qsL2[wp]:
  "setObject p (ap::asidpool) \<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv|simp)+

lemma setASIDPool_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma setASIDPool_state_refs'[wp]:
  "setObject p (ap::asidpool) \<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def objBits_simps
                        in_magnitude_check state_refs_of'_def ps_clear_upd
                 elim!: rsubst[where P=P] del: ext intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma setASIDPool_state_hyp_refs'[wp]:
  "setObject p (ap::asidpool) \<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def objBits_simps
                        in_magnitude_check state_hyp_refs_of'_def ps_clear_upd
                 elim!: rsubst[where P=P] del: ext intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma setASIDPool_iflive[wp]:
  "setObject p (ap::asidpool) \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps)
     apply (auto simp: updateObject_default_def in_monad bit_simps live'_def hyp_live'_def
                       arch_live'_def)
  done

lemma setASIDPool_ksInt[wp]:
  "setObject p (ap::asidpool) \<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

lemma setASIDPool_ifunsafe[wp]:
  "setObject p (ap::asidpool) \<lbrace>if_unsafe_then_cap'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad)[2]
   apply wp
  apply simp
  done

lemma setASIDPool_it'[wp]:
  "setObject p (ap::asidpool) \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>"
  by (wp setObject_it updateObject_default_inv|simp)+

lemma setASIDPool_pred_tcb_at'[wp]:
  "setObject p (ap::asidpool) \<lbrace>pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma setASIDPool_idle[wp]:
  "setObject p (ap::asidpool) \<lbrace>valid_idle'\<rbrace>"
  unfolding valid_idle'_def
  by (rule hoare_lift_Pf [where f="ksIdleThread"]; wp)

lemma setASIDPool_irq_states'[wp]:
  "setObject p (ap::asidpool) \<lbrace>valid_irq_states'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=ksInterruptState, OF setObject_ksInterrupt])
    apply (simp, rule updateObject_default_inv)
   apply (rule hoare_use_eq [where f=ksMachineState, OF setObject_ksMachine])
    apply (simp, rule updateObject_default_inv)
   apply wp
  apply assumption
  done

lemma setASIDPool_vms'[wp]:
  "setObject p (ap::asidpool) \<lbrace>valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

lemma setASIDPool_ct_not_inQ[wp]:
  "setObject p (ap::asidpool) \<lbrace>ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF setObject_nosch])
   apply (simp add: updateObject_default_def | wp)+
  apply (rule hoare_weaken_pre)
   apply (wps setObject_ASID_ct)
  apply (rule obj_at_setObject2)
   apply (clarsimp simp: updateObject_default_def in_monad)+
  done

lemma setObject_asidpool_cur_domain[wp]:
  "setObject p (ap::asidpool) \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_asidpool_ksDomSchedule[wp]:
  "setObject p (ap::asidpool) \<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_asidpool_tcb_in_cur_domain'[wp]:
  "setObject p (ap::asidpool) \<lbrace>tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma setObject_asidpool_ct_idle_or_in_cur_domain'[wp]:
  "setObject p (ap::asidpool) \<lbrace>ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp hoare_vcg_disj_lift ct_idle_or_in_cur_domain'_lift)

lemma setObject_ap_ksDomScheduleIdx[wp]:
  "setObject p (ap::asidpool) \<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_ap_tcbs_of'[wp]:
  "setObject p (ap::asidpool) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setASIDPool_invs[wp]:
  "setObject p (ap::asidpool) \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wp sch_act_wf_lift valid_global_refs_lift' irqs_masked_lift
            valid_irq_node_lift
            cur_tcb_lift valid_irq_handlers_lift''
            untyped_ranges_zero_lift
            updateObject_default_inv valid_bitmaps_lift
          | simp add: cteCaps_of_def
          | rule setObject_ksPSpace_only)+
  apply (clarsimp simp: o_def)
  done

lemma doMachineOp_invalidateTranslationASID_invs'[wp]:
  "doMachineOp (invalidateTranslationASID vmid) \<lbrace>invs'\<rbrace>"
  unfolding invalidateTranslationASID_def
  by (wp dmo_machine_op_lift_invs')

lemma invs'_vmid_strg:
  "\<lbrakk> invs' s; 0 < asid \<rbrakk> \<Longrightarrow>
   invs' (s\<lparr>ksArchState := armKSVMIDTable_update
                           (\<lambda>_. (armKSVMIDTable (ksArchState s))(vmid \<mapsto> asid))
                           (ksArchState s)\<rparr>)"
  by (auto simp: invs'_def valid_state'_def valid_global_refs'_def global_refs'_def
                 valid_machine_state'_def valid_arch_state'_vmid_Some_upd)

crunch updateASIDPoolEntry
  for invs'[wp]: invs'
  (wp: getASID_wp crunch_wps)

lemma storeVMID_invs'[wp]:
  "\<lbrace>invs' and K (0 < asid)\<rbrace> storeVMID asid vmid \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding storeVMID_def
  by (wpsimp simp_del: fun_upd_apply | strengthen invs'_vmid_strg)+

lemma invs'_vmid_None_upd:
  "invs' s \<Longrightarrow>
   invs' (s\<lparr>ksArchState := armKSVMIDTable_update
                           (\<lambda>_ a. if a = vmid then None else armKSVMIDTable (ksArchState s) a)
                           (ksArchState s)\<rparr>)"
  by (clarsimp simp: invs'_def valid_state'_def valid_global_refs'_def global_refs'_def
                     valid_machine_state'_def valid_arch_state'_def ran_def
               cong: option.case_cong)

crunch getVMID, armContextSwitch, setGlobalUserVSpace
  for invs'[wp]: invs'
  (ignore: doMachineOp wp: getASID_wp crunch_wps simp: invs'_vmid_None_upd)

lemma setVMRoot_invs'[wp]:
  "setVMRoot p \<lbrace>invs'\<rbrace>"
  unfolding setVMRoot_def getThreadVSpaceRoot_def locateSlotTCB_def locateSlotBasic_def
  by (wpsimp wp: whenE_wp findVSpaceForASID_vs_at_wp hoare_vcg_ex_lift
                 hoare_vcg_all_lift getSlotCap_actual_wp
             simp: word_neq_0_conv)

lemma setASIDPool_invs_no_cicd'[wp]:
  "setObject p (ap::asidpool) \<lbrace>invs_no_cicd'\<rbrace>"
  apply (simp add: invs_no_cicd'_def valid_state'_def valid_pspace'_def)
  apply (wp sch_act_wf_lift valid_global_refs_lift' irqs_masked_lift
            valid_irq_node_lift
            cur_tcb_lift valid_irq_handlers_lift''
            untyped_ranges_zero_lift
            updateObject_default_inv valid_bitmaps_lift
          | simp add: cteCaps_of_def
          | rule setObject_ksPSpace_only)+
  apply (clarsimp simp:  o_def)
  done

lemma invalidateTranslationASID_invs_no_cicd'[wp]:
  "doMachineOp (invalidateTranslationASID asid) \<lbrace>invs_no_cicd'\<rbrace>"
  by (wp dmo_invs_no_cicd_lift')

crunch updateASIDPoolEntry
  for invs_no_cicd'[wp]: invs_no_cicd'
  (wp: getASID_wp crunch_wps)

lemma invs_no_cicd'_vmid_strg:
  "\<lbrakk> invs_no_cicd' s; 0 < asid \<rbrakk> \<Longrightarrow>
   invs_no_cicd' (s\<lparr>ksArchState := armKSVMIDTable_update
                                   (\<lambda>_. (armKSVMIDTable (ksArchState s))(vmid \<mapsto> asid))
                                   (ksArchState s)\<rparr>)"
  by (auto simp: invs_no_cicd'_def valid_state'_def valid_global_refs'_def global_refs'_def
                 valid_machine_state'_def valid_arch_state'_vmid_Some_upd)

lemma storeVMID_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd' and K (0 < asid)\<rbrace> storeVMID asid vmid \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  unfolding storeVMID_def
  by (wpsimp simp_del: fun_upd_apply | strengthen invs_no_cicd'_vmid_strg)+

lemma invs_no_cicd'_vmid_None_upd:
  "invs_no_cicd' s \<Longrightarrow>
   invs_no_cicd' (s\<lparr>ksArchState := armKSVMIDTable_update
                                  (\<lambda>_ a. if a = vmid then None else armKSVMIDTable (ksArchState s) a)
                                  (ksArchState s)\<rparr>)"
  by (clarsimp simp: invs_no_cicd'_def valid_state'_def valid_global_refs'_def global_refs'_def
                     valid_machine_state'_def valid_arch_state'_def ran_def
               cong: option.case_cong)

crunch getVMID, armContextSwitch, setGlobalUserVSpace
  for invs_no_cicd'[wp]: "invs_no_cicd'"
  (ignore: doMachineOp wp: getASID_wp crunch_wps simp: invs_no_cicd'_vmid_None_upd)

lemma setVMRoot_invs_no_cicd':
  "setVMRoot p \<lbrace>invs_no_cicd'\<rbrace>"
  unfolding setVMRoot_def getThreadVSpaceRoot_def locateSlotTCB_def locateSlotBasic_def
  by (wpsimp wp: whenE_wp findVSpaceForASID_vs_at_wp hoare_vcg_ex_lift getSlotCap_actual_wp
                 hoare_vcg_all_lift
             simp: word_neq_0_conv)

crunch setVMRoot
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps getObject_inv setObject_nosch simp: crunch_simps loadObject_default_def updateObject_default_def)

crunch deleteASIDPool
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def updateObject_default_def wp: getObject_inv mapM_wp' crunch_wps)

crunch storePTE
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps updateObject_default_def wp: setObject_idle')

crunch deleteASID
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def updateObject_default_def
   wp: getObject_inv)

crunch performPageTableInvocation
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

crunch performPageInvocation
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps simp: crunch_simps)

lemma performASIDPoolInvocation_typ_at' [wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> performASIDPoolInvocation api \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  by (wpsimp simp: performASIDPoolInvocation_def
               wp: getASID_wp hoare_vcg_imp_lift[where P'=\<bottom>, simplified])

lemmas performPageTableInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performPageTableInvocation_typ_at']

lemmas performPageInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performPageInvocation_typ_at']

lemmas performASIDPoolInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performASIDPoolInvocation_typ_at']

lemma storePTE_pred_tcb_at' [wp]:
  "storePTE p pte \<lbrace>pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: storePTE_def pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePTE_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

crunch storePTE
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (simp: updateObject_default_def ignore_del: setObject)

crunch storePTE
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
  (simp: updateObject_default_def)

lemma storePTE_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> storePTE ptr pte \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def storePTE_def)
  apply (wp setObject_ko_wp_at | simp add: objBits_simps)+
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def)
  done

crunch storePTE
  for norqL1[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  (simp: updateObject_default_def)

crunch storePTE
  for norqL2[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (simp: updateObject_default_def)

lemma storePTE_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps)
     apply (auto simp: updateObject_default_def in_monad live'_def hyp_live'_def arch_live'_def)
  done

lemma setObject_pte_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (pte::pte) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

crunch storePTE
  for ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"

lemma storePTE_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad)[2]
   apply wp
  apply simp
  done

method valid_idle'_setObject uses simp =
  simp add: valid_idle'_def, rule hoare_lift_Pf [where f="ksIdleThread"]; wpsimp?;
  (wpsimp wp: obj_at_setObject2[where P="idle_tcb'", simplified] hoare_drop_imp
        simp: simp
   | clarsimp dest!: updateObject_default_result)+


lemma storePTE_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. valid_idle'\<rbrace>" by (valid_idle'_setObject simp: storePTE_def)

crunch storePTE
  for arch'[wp]: "\<lambda>s. P (ksArchState s)"

crunch storePTE
  for cur'[wp]: "\<lambda>s. P (ksCurThread s)"

lemma storePTE_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> storePTE pte p \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (wpsimp wp: valid_irq_states_lift' dmo_lift' no_irq_storeWord setObject_ksMachine
                    updateObject_default_inv)
  done

lemma storePTE_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storePTE p pte \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: storePTE_def valid_machine_state'_def pointerInUserData_def
                   pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

crunch storePTE
  for pspace_domain_valid[wp]: "pspace_domain_valid"

lemma storePTE_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePTE p pte \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePTE_nosch])
  apply (simp add: storePTE_def)
  apply (wp_pre, wps)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)+
  done

lemma setObject_pte_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::pte) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pte_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::pte) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePTE_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> storePTE p pte \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  by (simp add: storePTE_def) wp

lemma storePTE_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePTE p pte \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  by (simp add: storePTE_def) wp

lemma storePTE_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePTE_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma storePTE_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> storePTE p pte \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)

lemma setObject_pte_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (pte::pte) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

crunch storePTE
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv)

lemma storePTE_valid_objs[wp]:
  "\<lbrace>valid_objs' and K (ppn_bounded pte)\<rbrace> storePTE p pte \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (simp add: storePTE_def doMachineOp_def split_def)
  apply (rule hoare_pre, rule setObject_valid_objs'[where P="K (ppn_bounded pte)"])
   apply (clarsimp simp: updateObject_default_def in_monad  valid_obj'_def)
  apply simp
  done

lemma storePTE_ko_wp_vcpu_at'[wp]:
  "storePTE p pde \<lbrace>\<lambda>s. P (ko_wp_at' (is_vcpu' and hyp_live') p' s)\<rbrace>"
  apply (clarsimp simp: storePTE_def)
  apply (wpsimp wp: hoare_drop_imps setObject_ko_wp_at simp: objBits_simps archObjSize_def)
   apply (auto simp: bit_simps ko_wp_at'_def obj_at'_def is_vcpu'_def)+
  done

lemma setObject_pte_tcb_of'[wp]:
  "setObject slote (pte::pte) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  by setObject_easy_cases

crunch storePTE
  for tcbs_of'[wp]: "\<lambda>s. P (tcbs_of' s)"

lemma storePTE_invs[wp]:
  "\<lbrace>invs' and K (ppn_bounded pte)\<rbrace> storePTE p pte \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_state'_def valid_pspace'_def
  by (wpsimp wp: sch_act_wf_lift valid_global_refs_lift' irqs_masked_lift valid_arch_state_lift'
                 valid_irq_node_lift cur_tcb_lift valid_irq_handlers_lift'' untyped_ranges_zero_lift
                 valid_bitmaps_lift
             simp: cteCaps_of_def o_def)

crunch unmapPageTable
  for cte_wp_at'[wp]: "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas storePTE_Invalid_invs = storePTE_invs[where pte=InvalidPTE, simplified]

crunch unmapPageTable, invalidateTLBByASIDVA
  for invs'[wp]: "invs'"
  (ignore: doMachineOp
       wp: storePTE_Invalid_invs mapM_wp' crunch_wps dmo_invs_lift'
     simp: crunch_simps if_apply_def2)

lemma perform_pti_invs [wp]:
  "\<lbrace>invs' and valid_pti' pti\<rbrace> performPageTableInvocation pti \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: performPageTableInvocation_def getSlotCap_def valid_pti'_def
                 split: page_table_invocation.splits)
  apply (intro conjI allI impI;
           wpsimp wp: arch_update_updateCap_invs getCTE_wp' mapM_x_wp'
                      hoare_vcg_all_lift hoare_vcg_imp_lift' dmo_invs_lift')
  apply (auto simp: cte_wp_at_ctes_of is_arch_update'_def isCap_simps valid_cap'_def capAligned_def)
  done

crunch unmapPage
  for cte_wp_at': "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps lookupPTSlotFromLevel_inv simp: crunch_simps)

lemmas unmapPage_typ_ats [wp] = typ_at_lifts [OF unmapPage_typ_at']

lemma unmapPage_invs' [wp]:
  "unmapPage sz asid vptr pptr \<lbrace>invs'\<rbrace>"
  unfolding unmapPage_def
  by (wpsimp wp: lookupPTSlot_inv hoare_drop_imp hoare_vcg_all_lift dmo_invs_lift')

lemma dmo_doFlush_invs'[wp]:
  "doMachineOp (doFlush flushOp vstart vend pstart) \<lbrace>invs'\<rbrace>"
  unfolding doFlush_def cleanCacheRange_RAM_def invalidateCacheRange_RAM_def branchFlushRange_def
            cleanInvalidateCacheRange_RAM_def cleanCacheRange_PoU_def invalidateCacheRange_I_def
  by (cases flushOp; wpsimp wp: dmo_machine_op_lift_invs' simp: doMachineOp_bind empty_fail_bind)

lemma isPagePTE_eq: (* FIXME AARCH64: move up *)
  "isPagePTE pte = (\<exists>base sm g xn d R. pte = PagePTE base sm g xn d R)"
  by (simp add: isPagePTE_def split: pte.splits)

lemma perform_page_invs [wp]:
  "\<lbrace>invs' and valid_page_inv' pt\<rbrace> performPageInvocation pt \<lbrace>\<lambda>_. invs'\<rbrace>"
  supply if_split[split del]
  apply (simp add: performPageInvocation_def)
  apply (cases pt)
     (* FIXME AARCH64: clean up this proof, not clear why all, fwd_all or solve_emerging don't work *)
     apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_const_imp_lift
                            arch_update_updateCap_invs unmapPage_cte_wp_at' getSlotCap_wp dmo_invs_lift'
                       simp: valid_page_inv'_def is_arch_update'_def if_apply_def2)
    apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_const_imp_lift
                           arch_update_updateCap_invs unmapPage_cte_wp_at' getSlotCap_wp dmo_invs_lift'
                      simp: valid_page_inv'_def is_arch_update'_def if_apply_def2 isPagePTE_eq)
   prefer 2
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_const_imp_lift
                          arch_update_updateCap_invs unmapPage_cte_wp_at' getSlotCap_wp
                     simp: valid_page_inv'_def is_arch_update'_def if_apply_def2)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_const_imp_lift
                         arch_update_updateCap_invs unmapPage_cte_wp_at' getSlotCap_wp dmo_invs_lift'
                    simp: valid_page_inv'_def is_arch_update'_def if_apply_def2)
  apply (clarsimp simp: cte_wp_at_ctes_of valid_page_inv'_def is_arch_update'_def isCap_simps valid_cap'_def capAligned_def
                  split: option.splits)+
  done

lemma setObject_cte_obj_at_ap':
  shows
  "\<lbrace>\<lambda>s. P' (obj_at' (P :: asidpool \<Rightarrow> bool) p s)\<rbrace>
  setObject c (cte::cte)
  \<lbrace>\<lambda>_ s. P' (obj_at' P p s)\<rbrace>"
  apply (clarsimp simp: setObject_def in_monad split_def
                        valid_def lookupAround2_char1
                        obj_at'_def ps_clear_upd
             split del: if_split)
  apply (clarsimp elim!: rsubst[where P=P'])
  apply (clarsimp simp: updateObject_cte in_monad objBits_simps
                        tcbCTableSlot_def tcbVTableSlot_def
                        typeError_def
                 split: if_split_asm
                        Structures_H.kernel_object.split_asm)
  done

lemma updateCap_ko_at_ap_inv'[wp]:
  "\<lbrace>\<lambda>s. P (ko_at' (ko::asidpool) p s )\<rbrace> updateCap a b \<lbrace>\<lambda>rv s. P ( ko_at' ko p s)\<rbrace>"
  by (wpsimp simp: updateCap_def setCTE_def wp: setObject_cte_obj_at_ap')

lemma storePTE_asid_pool_obj_at'[wp]:
  "storePTE p pte \<lbrace>\<lambda>s. P (obj_at' (P'::asidpool \<Rightarrow> bool) t s)\<rbrace>"
  apply (simp add: storePTE_def)
  apply (clarsimp simp: setObject_def in_monad split_def
                        valid_def lookupAround2_char1
                        obj_at'_def ps_clear_upd
             split del: if_split)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

lemma perform_aci_invs [wp]:
  "\<lbrace>invs' and valid_apinv' api\<rbrace> performASIDPoolInvocation api \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: performASIDPoolInvocation_def split: asidpool_invocation.splits)
  apply (wpsimp wp: arch_update_updateCap_invs getASID_wp getSlotCap_wp hoare_vcg_all_lift
            hoare_vcg_imp_lift')
  apply (clarsimp simp: valid_apinv'_def cte_wp_at_ctes_of)
  apply (case_tac cte, clarsimp)
  apply (drule ctes_of_valid_cap', fastforce)
  apply (clarsimp simp: valid_cap'_def capAligned_def is_arch_update'_def isCap_simps
                        wellformed_mapdata'_def)
  done

end

end
