(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Architecture-specific refinement for interrupt controller operations *)

theory ArchInterrupt_R
imports Interrupt_R
begin

context Arch begin arch_global_naming

named_theorems Interrupt_R_assms

lemma maxIRQ_H_ucast_toEnum_eq_irq[Interrupt_R_assms]:
  "x \<le> ucast maxIRQ \<Longrightarrow> toEnum (unat x) = (ucast x :: irq)" for x::machine_word
  by (simp add: maxIRQ_ucast_toEnum_eq_irq maxIRQ_def)

lemma arch_valid_irq_le_maxIRQ[Interrupt_R_assms]:
  "arch_valid_irq irq \<Longrightarrow> irq \<le> maxIRQ"
  by simp

lemma arch_valid_irq_valid_IRQHandlerCap[Interrupt_R_assms]:
  "arch_valid_irq irq \<Longrightarrow> valid_cap' (capability.IRQHandlerCap irq) s"
  by (simp add: valid_cap'_def capAligned_def)

primrec arch_irq_control_inv_relation ::
  "arch_irq_control_invocation \<Rightarrow> Arch.irqcontrol_invocation \<Rightarrow> bool"
  where
  "arch_irq_control_inv_relation (AARCH64_A.ARMIRQControlInvocation i ptr ptr' t) x =
     (x = AARCH64_H.IssueIRQHandler i (cte_map ptr) (cte_map ptr') t)"
| "arch_irq_control_inv_relation (AARCH64_A.IssueSGISignal irq target ptr ptr') x =
     (x = AARCH64_H.IssueSGISignal (ucast irq) (ucast target) (cte_map ptr) (cte_map ptr'))"

primrec arch_irq_control_inv_valid' :: "Arch.irqcontrol_invocation \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "arch_irq_control_inv_valid' (AARCH64_H.IssueIRQHandler irq ptr ptr' t) =
     (cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) ptr and
      cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) ptr' and
      ex_cte_cap_to' ptr and real_cte_at' ptr and
      (Not o irq_issued' irq) and K (irq \<le> maxIRQ))"
| "arch_irq_control_inv_valid' (AARCH64_H.IssueSGISignal irq target src_slot sgi_slot) =
     (cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) sgi_slot and
      cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) src_slot and
      ex_cte_cap_to' sgi_slot and real_cte_at' sgi_slot)"

lemma checkIRQ_corres[Interrupt_R_assms]:
  "corres (ser \<oplus> dc) \<top> \<top> (arch_check_irq irq) (Arch.checkIRQ irq)"
  unfolding arch_check_irq_def checkIRQ_def
  by (clarsimp simp: minIRQ_def maxIRQ_def whenE_rangeCheck_eq whenE_def returnOk_def split: if_split)

lemmas irq_const_defs = minIRQ_def

crunch arch_check_irq, checkIRQ
  for inv[Interrupt_R_assms]: "P"
  (simp: crunch_simps)

lemma arch_check_irq_valid:
  "\<lbrace>\<top>\<rbrace> arch_check_irq irq \<lbrace>\<lambda>_. (\<lambda>s. irq \<le> ucast maxIRQ)\<rbrace>, -"
  unfolding arch_check_irq_def
  by (wpsimp simp: validE_R_def not_less word_le_nat_alt maxIRQ_def wp: whenE_throwError_wp)

lemma arch_check_irq_valid'[Interrupt_R_assms]:
  "\<lbrace>\<top>\<rbrace> arch_check_irq irq \<lbrace>\<lambda>_ _. irq \<le> ucast maxIRQ\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>"
  by (wp arch_check_irq_valid)

lemma checkIRQ_irq_valid[Interrupt_R_assms]:
  "\<lbrace>\<top>\<rbrace> checkIRQ irq \<lbrace>\<lambda>_ _. arch_valid_irq (toEnum (unat irq))\<rbrace>, -"
  unfolding checkIRQ_def rangeCheck_def validE_R_def
  supply hoare_vcg_prop[wp del]
  apply (clarsimp simp: unlessE_def split del: if_split)
  apply (wpsimp simp: maxIRQ_H_ucast_toEnum_eq_irq)
  apply (fastforce simp: maxIRQ_def elim: irq_machine_le_maxIRQ_irq)
  done

lemma isSGITargetValid_eq:
  "isSGITargetValid w = sgi_target_valid w"
  unfolding isSGITargetValid_def sgi_target_valid_def
  by simp

lemma sgi_target_cast[simp]:
  "sgi_target_valid w \<Longrightarrow> ucast (ucast w :: sgi_target) = w"
  unfolding sgi_target_valid_def gicNumTargets_def
  by (simp flip: sgi_target_len_def add: ucast_ucast_le_mask mask_def sgi_target_len_val)

lemma sgi_irq_cast:
  "w \<le> word_of_nat numSGIs - 1 \<Longrightarrow> ucast (ucast w :: sgi_irq) = (w :: machine_word)"
  unfolding numSGIs_def
  by (simp flip: sgi_irq_len_def
           add: ucast_ucast_len sgi_irq_len_val word_le_nat_alt word_less_nat_alt)

lemma arch_decodeIRQControlInvocation_corres[Interrupt_R_assms]:
  "list_all2 cap_relation caps caps' \<Longrightarrow>
   corres (ser \<oplus> arch_irq_control_inv_relation)
     (invs and (\<lambda>s. \<forall>cp \<in> set caps. s \<turnstile> cp))
     (invs' and (\<lambda>s. \<forall>cp \<in> set caps'. s \<turnstile>' cp))
     (arch_decode_irq_control_invocation label args slot caps)
     (Arch.decodeIRQControlInvocation label args (cte_map slot) caps')"
  supply arch_check_irq_inv[wp del]
  apply (clarsimp simp: arch_decode_irq_control_invocation_def
                        AARCH64_H.decodeIRQControlInvocation_def Let_def)
  apply (rule conjI; clarsimp)
   prefer 2
   apply (cases caps
          ; fastforce split: arch_invocation_label.splits list.splits invocation_label.splits
                       simp: length_Suc_conv list_all2_Cons1 whenE_rangeCheck_eq liftE_bindE)
  apply (cases caps, simp split: list.split)
  apply (case_tac "\<exists>n. length args = Suc (Suc (Suc (Suc n)))",
         clarsimp simp: length_Suc_conv list_all2_Cons1 liftE_bindE)
   prefer 2 apply (fastforce split: list.split)
  \<comment>\<open>ARMIRQIssueSGISignal\<close>
  apply (rule conjI, clarsimp)
   apply (simp add: range_check_def rangeCheck_def)
   apply (corres corres: lookupSlotForCNodeOp_corres ensureEmptySlot_corres corres_returnOkTT
                 term_simp: numSGIs_def isSGITargetValid_eq sgi_irq_cast)
    apply fastforce
   apply fastforce
  \<comment>\<open>ARMIRQIssueIRQHandler\<close>
  apply (rule impI, rule conjI, clarsimp)
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE[OF checkIRQ_corres])
       apply (rule_tac F="y \<le> ucast maxIRQ" in corres_gen_asm)
       apply (clarsimp simp: maxIRQ_H_ucast_toEnum_eq_irq)
       apply (rule corres_split_eqr[OF is_irq_active_corres])
         apply (rule whenE_throwError_corres, clarsimp, clarsimp)
         apply (rule corres_splitEE)
            apply (rule lookupSlotForCNodeOp_corres; clarsimp)
           apply (rule corres_splitEE[OF ensureEmptySlot_corres], simp)
             apply (rule corres_returnOkTT)
             apply (clarsimp simp: arch_irq_control_inv_relation_def)
            apply (wpsimp wp: isIRQActive_inv checkIRQ_inv arch_check_irq_valid'
                        simp: invs_valid_objs invs_psp_aligned invs_valid_objs'
                              invs_pspace_aligned' invs_pspace_distinct'
                   | strengthen invs_valid_objs invs_psp_aligned
                   | wp (once) hoare_drop_imps arch_check_irq_inv)+
  apply (auto split: arch_invocation_label.splits invocation_label.splits)
  done

lemma arch_decode_irq_control_valid'[Interrupt_R_assms, wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> (\<forall>cap \<in> set caps. s \<turnstile>' cap)
        \<and> (\<forall>cap \<in> set caps. \<forall>r \<in> cte_refs' cap (irq_node' s). ex_cte_cap_to' r s)
        \<and> cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) slot s\<rbrace>
   Arch.decodeIRQControlInvocation label args slot caps
   \<lbrace>arch_irq_control_inv_valid'\<rbrace>,-"
  apply (clarsimp simp add: AARCH64_H.decodeIRQControlInvocation_def Let_def split_def
                            rangeCheck_def unlessE_whenE
                 split del: if_split
                      cong: if_cong list.case_cong prod.case_cong arch_invocation_label.case_cong)
  apply (rule hoare_pre)
   apply (simp add: rangeCheck_def unlessE_whenE checkIRQ_def
              cong: list.case_cong prod.case_cong
          | wp whenE_throwError_wp isIRQActive_wp ensureEmptySlot_stronger
          | wpc
          | wp (once) hoare_drop_imps)+
  apply (clarsimp, rule conjI; clarsimp)
  apply (clarsimp simp: invs_valid_objs' toEnum_unat_ucast maxIRQ_def
                        le_maxIRQ_machine_less_irqBits_val irq_machine_le_maxIRQ_irq)
  done

crunch Arch.decodeIRQControlInvocation
  for inv[Interrupt_R_assms, wp]: "P"
  (simp: crunch_simps wp: crunch_wps)

lemmas [Interrupt_R_assms] = arch_check_irq_inv

lemma irq_node_in_global_refs'[Interrupt_R_assms]:
  "Invariants_H.irq_node' s + (ucast irq << cteSizeBits) \<in> global_refs' s" for irq :: irq
  by (simp add: global_refs'_def)

lemma no_fail_deactivateInterrupt[wp, simp]:
  "config_ARM_GIC_V3 \<Longrightarrow> no_fail \<top> (deactivateInterrupt irq)"
  unfolding deactivateInterrupt_def
  by wpsimp

lemma arch_invokeIRQHandler_corres[Interrupt_R_assms]:
  "irq_handler_inv_relation i i' \<Longrightarrow>
   corres dc \<top> \<top> (arch_invoke_irq_handler i) (Arch.invokeIRQHandler i')"
  by (cases i; clarsimp simp: invokeIRQHandler_def theIRQ_def)
     (intro conjI impI; rule corres_machine_op, rule corres_Id; simp?)

lemma is_derived'_NotificationCap[Interrupt_R_assms]:
  "\<lbrakk>isNotificationCap cap; isNotificationCap cap'\<rbrakk>
   \<Longrightarrow> is_derived' ctes src cap' cap = badge_derived' cap' cap"
  by (clarsimp simp add: is_derived'_def gen_isCap_simps)

lemma doMachineOp_deactivateInterrupt[wp]:
  "\<lbrace> \<lambda>s. invs' s \<and> intStateIRQTable (ksInterruptState s) irq \<noteq> irqstate.IRQInactive \<and> config_ARM_GIC_V3 \<rbrace>
   doMachineOp (deactivateInterrupt irq)
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding deactivateInterrupt_def
  by (cases config_ARM_GIC_V3; wpsimp)

lemma IRQHandler_valid':
  "(s' \<turnstile>' IRQHandlerCap irq) = (irq \<le> maxIRQ)"
  by (simp add: valid_cap'_def capAligned_def word_bits_conv)

lemma setIRQTrigger_corres:
  "corres dc \<top> \<top> (do_machine_op (setIRQTrigger irq t)) (doMachineOp (setIRQTrigger irq t))"
  apply (rule corres_machine_op)
  apply (rule corres_guard_imp)
    apply (rule corres_rel_imp)
     apply (wp
            | rule corres_underlying_trivial
            | rule no_fail_setIRQTrigger
            | simp add: dc_def)+
  done

lemma SGISignalCap_valid[simp, intro!]:
  "valid_cap' (ArchObjectCap (SGISignalCap irq target)) s"
  by (simp add: valid_cap'_def capAligned_def word_bits_def)

lemma arch_performIRQControl_corres[Interrupt_R_assms]:
  "arch_irq_control_inv_relation ivk ivk' \<Longrightarrow> corres (dc \<oplus> dc)
          (einvs and arch_irq_control_inv_valid ivk)
          (invs' and arch_irq_control_inv_valid' ivk')
          (arch_invoke_irq_control ivk)
          (Arch.performIRQControl ivk')"
  apply (cases ivk; simp add: AARCH64_H.performIRQControl_def invoke_irq_control.cases IRQ_def)
   apply (rule corres_guard_imp)
     apply (rule corres_split_nor)
        apply (rule setIRQTrigger_corres)
       apply (rule corres_split_nor)
          apply (rule setIRQState_corres)
          apply (simp add: irq_state_relation_def)
         apply (rule cteInsert_simple_corres; simp)
        apply (wp | simp add: irq_state_relation_def IRQHandler_valid IRQHandler_valid')+
    apply (clarsimp simp: invs_def valid_state_def valid_pspace_def cte_wp_at_caps_of_state
                          is_simple_cap_def is_cap_simps arch_irq_control_inv_valid_def
                          safe_parent_for_def is_simple_cap_arch_def)
   apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def IRQHandler_valid
                         IRQHandler_valid' is_simple_cap'_def isCap_simps IRQ_def)
   apply (clarsimp simp: safe_parent_for'_def cte_wp_at_ctes_of)
   apply (case_tac ctea)
   apply (clarsimp simp: isCap_simps sameRegionAs_def3)
   apply (auto dest: valid_irq_handlers_ctes_ofD)[1]
  apply (corres corres: cteInsert_simple_corres)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def cte_wp_at_caps_of_state
                         is_simple_cap_def is_cap_simps arch_irq_control_inv_valid_def
                         safe_parent_for_def is_simple_cap_arch_def is_irq_control_descendant_def)
  apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def
                        is_simple_cap'_def isCap_simps)
  apply (clarsimp simp: safe_parent_for'_def safe_parent_for_arch'_def cte_wp_at_ctes_of)
  apply (rename_tac cte', case_tac cte', simp add: isCap_simps)
  done

lemma is_simple_cap'_IRQHandlerCap[Interrupt_R_assms]:
  "isIRQHandlerCap cap \<Longrightarrow> is_simple_cap' cap"
  by (clarsimp simp: isCap_simps is_simple_cap'_def)

lemma sameRegionAs_IRQControl_handler[Interrupt_R_assms, simp]:
  "global.sameRegionAs capability.IRQControlCap (capability.IRQHandlerCap irq)"
  by (simp add: sameRegionAs_def3 isCap_simps)

lemma dmo_setIRQTrigger_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (setIRQTrigger irq t) \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_setIRQTrigger no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (wpsimp simp: setIRQTrigger_def machine_op_lift_def machine_rest_lift_def split_def)+
  done

lemma arch_invoke_irq_control_invs'[Interrupt_R_assms, wp]:
  "\<lbrace>invs' and arch_irq_control_inv_valid' i\<rbrace> Arch.performIRQControl i \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: AARCH64_H.performIRQControl_def)
  apply (rule hoare_pre)
   apply (wpsimp wp: cteInsert_simple_invs simp: cte_wp_at_ctes_of isCap_simps IRQ_def)
  apply (clarsimp simp: cte_wp_at_ctes_of IRQHandler_valid' is_simple_cap'_def isCap_simps
                        safe_parent_for'_def safe_parent_for_arch'_def sameRegionAs_def3)
  apply (clarsimp simp: capRange_def)
  apply (rule conjI; clarsimp simp: cte_wp_at_ctes_of; case_tac ctea)
   apply (auto dest: valid_irq_handlers_ctes_ofD
               simp: invs'_def valid_state'_def IRQ_def)
  done

lemma corres_return_VGICMaintenance[corres]:
  "corres ((=) o arch_fault_map) (K (a=b)) \<top>
          (return (AARCH64_A.VGICMaintenance a)) (return (AARCH64_H.VGICMaintenance b))"
  by simp

crunch vgicUpdateLR
  for ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"

lemma virqSetEOIIRQEN_eq[simp]:
  "AARCH64_H.virqSetEOIIRQEN = AARCH64_A.virqSetEOIIRQEN"
  unfolding virqSetEOIIRQEN_def AARCH64_A.virqSetEOIIRQEN_def eoiirqenShift_def eoiirqen_shift_def
  by (simp cong: if_cong)

lemma vgic_maintenance_corres [corres]:
  "corres dc einvs
    (\<lambda>s. invs' s \<and> sch_act_not (ksCurThread s) s)
    vgic_maintenance vgicMaintenance"
proof -
  (* hoare_lift_Pf-style rules match too often, slowing down proof unless specialised *)
  note vilr = hoare_lift_Pf2[where f=cur_thread and m="vgic_update_lr v i virq" for v i virq]
  note vilr' = hoare_lift_Pf2[where f=ksCurThread and m="vgicUpdateLR v i virq" for v i virq]
  note wplr = vilr[where P="st_tcb_at active"]
              vilr[where P="ex_nonz_cap_to"]
  note wplr' = vilr'[where P="sch_act_not"]
               vilr'[where P="ex_nonz_cap_to'"]
               vilr'[where P="st_tcb_at' simple'"]
  show ?thesis
    unfolding vgic_maintenance_def vgicMaintenance_def isRunnable_def Let_def
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF corres_gets_current_vcpu], simp, rename_tac hsCurVCPU)
        (* we only care about the one case we do something: active current vcpu *)
        apply (rule_tac R="hsCurVCPU = None" in corres_cases')
         apply (rule corres_trivial, simp)
        apply (clarsimp, rename_tac vcpu_ptr active)
        apply wpfix
        apply (rule_tac R="\<not> active" in corres_cases')
         apply (rule corres_trivial, simp)
        apply clarsimp

        apply (rule corres_split_eqr[OF corres_machine_op],
               (rule corres_Id; wpsimp simp: get_gic_vcpu_ctrl_misr_def
                                             get_gic_vcpu_ctrl_eisr1_def
                                             get_gic_vcpu_ctrl_eisr0_def))+
              apply (rename_tac eisr0 eisr1 flags)
              apply (rule corres_split[OF corres_gets_gicvcpu_numlistregs])
                apply (rule corres_split[where r'="\<lambda>rv rv'. rv' = arch_fault_map rv"])
                   apply (rule corres_if[rotated -1])
                     apply (rule corres_trivial, simp)
                    apply clarsimp
                   apply (rule corres_if, simp)
                    apply (rule corres_trivial, simp)
                   supply if_split[split del]
                   apply (clarsimp simp: bind_assoc cong: if_cong)
                   apply (rule corres_split_eqr[OF corres_machine_op])
                      apply (rule corres_Id; wpsimp)
                     apply (rule corres_split_dc[OF corres_machine_op])
                        apply (rule corres_Id; wpsimp)
                       apply clarsimp
                       apply (rule corres_split_dc[OF vgicUpdateLR_corres])
                         apply (rule corres_trivial, simp)
                        apply wpsimp+
                  apply (rule corres_split_eqr[OF getCurThread_corres])
                    apply (rule corres_split[OF getThreadState_corres])
                      apply (fold dc_def)
                      apply (rule corres_when)
                       apply clarsimp
                       apply (rename_tac threadState threadState')
                       apply (case_tac threadState; simp)
                      apply (rule handleFault_corres)
                      apply clarsimp
                     apply clarsimp
                     apply (wp gts_wp)
                    apply (wp gts_wp')
                   apply (rule_tac
                            Q'="\<lambda>rv. tcb_at rv and einvs
                                    and (\<lambda>_. valid_fault (ExceptionTypes_A.fault.ArchFault rva))"
                            in hoare_post_imp)
                    apply (clarsimp cong: imp_cong conj_cong simp: not_pred_tcb runnable_eq pred_conj_def)
                    apply (strengthen st_tcb_ex_cap'[where P=active], clarsimp)
                    apply (fastforce simp: pred_tcb_at_def obj_at_def)
                   apply wp
                  apply clarsimp
                  apply (rule_tac Q'="\<lambda>rv x. tcb_at' rv x
                                            \<and> invs' x
                                            \<and> sch_act_not rv x"
                           in hoare_post_imp)
                   apply (rename_tac rv s)
                   apply clarsimp
                   apply (strengthen st_tcb_ex_cap''[where P=active'])
                   apply (strengthen invs_iflive')
                   apply (clarsimp cong: imp_cong conj_cong simp: not_pred_tcb')
                   apply (clarsimp simp: pred_tcb_at'_def)
                   apply (rule conjI, erule_tac p=rv in obj_at'_weakenE,
                          fastforce split: thread_state.splits)
                   apply (erule_tac p=rv in obj_at'_weakenE, fastforce split: thread_state.splits)
                  apply wp
                 apply (wpsimp wp: wplr wplr' hoare_vcg_all_lift
                                   hoare_vcg_imp_lift' dmo_gets_wp dmo'_gets_wp
                               simp: get_gic_vcpu_ctrl_misr_def if_apply_def2
                                     get_gic_vcpu_ctrl_eisr1_def
                                     get_gic_vcpu_ctrl_eisr0_def
                        | strengthen tcb_at_invs tcb_at_invs')+

     apply (frule invs_arch_state)
     apply (clarsimp simp: valid_arch_state_def valid_fault_def obj_at_def cur_vcpu_def in_omonad)
    apply (clarsimp simp: tcb_at_invs')
    apply (frule invs_arch_state')
    apply (clarsimp simp: valid_arch_state'_def vcpu_at_is_vcpu')
    apply (erule ko_wp_at'_weakenE, simp)
    done
qed

lemma vppiEvent_corres:
  "corres dc einvs
    (\<lambda>s. invs' s \<and> sch_act_not (ksCurThread s) s)
    (vppi_event irq) (vppiEvent irq)"
  unfolding vppi_event_def vppiEvent_def isRunnable_def
  supply [[simproc del: defined_all]]
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF corres_gets_current_vcpu])
      apply (clarsimp simp del: subst_all (* avoid destroying useful name of rv *))
      (* we only care about the one case we do something: active current vcpu *)
      apply (rule_tac R="hsCurVCPU = None" in corres_cases')
       apply (rule corres_trivial, simp)
      apply (clarsimp, rename_tac vcpu_ptr active)
      apply wpfix
      apply (rule_tac R="\<not> active" in corres_cases')
       apply (rule corres_trivial, simp)
      apply clarsimp

      apply (rule corres_split_dc[OF corres_machine_op])
         apply (rule corres_Id; wpsimp)
        apply (rule corres_split_dc[OF vcpuUpdate_corres])
           apply (fastforce simp: vcpu_relation_def irq_vppi_event_index_def
                                  irqVPPIEventIndex_def IRQ_def)
          apply (rule corres_split_eqr[OF getCurThread_corres])
            apply (rule corres_split[OF getThreadState_corres], rename_tac gts gts')
              apply (fold dc_def)
              apply (rule corres_when)
               apply (case_tac gts; fastforce)
              apply (rule handleFault_corres, simp)
             apply (wp gts_st_tcb_at hoare_vcg_imp_lift')
            apply (wp gts_st_tcb_at' hoare_vcg_imp_lift')
             (* on both sides, we check that the current thread is runnable, then have to know it
                is runnable directly afterwards, which is obvious and should not propagate further;
                clean up the postconditions of the thread_get and threadGet *)
           apply (rule_tac
                    Q'="\<lambda>rv. tcb_at rv and einvs
                            and (\<lambda>_. valid_fault (ExceptionTypes_A.fault.ArchFault
                                                    (AARCH64_A.VPPIEvent irq)))"
                    in hoare_post_imp)
            apply (clarsimp cong: imp_cong conj_cong simp: not_pred_tcb runnable_eq pred_conj_def)
            apply (strengthen st_tcb_ex_cap'[where P=active], fastforce)
           apply wp
          apply (clarsimp cong: imp_cong conj_cong simp: pred_conj_def)
          apply (rule_tac Q'="\<lambda>rv x. tcb_at' rv x
                                    \<and> invs' x
                                    \<and> sch_act_not rv x" in hoare_post_imp)
           apply (rename_tac rv s)
           apply (strengthen st_tcb_ex_cap''[where P=active'])
           apply (strengthen invs_iflive')
           apply (clarsimp cong: imp_cong conj_cong simp: not_pred_tcb')
           apply (clarsimp simp: pred_tcb_at'_def)
           apply (rule conjI, erule_tac p=rv in obj_at'_weakenE, fastforce split: thread_state.splits)
           apply (erule_tac p=rv in obj_at'_weakenE, fastforce split: thread_state.splits)
          apply wp
         apply (wpsimp wp: vcpu_update_tcb_at hoare_vcg_all_lift hoare_vcg_imp_lift'
                       cong: vcpu.fold_congs)+
         apply (strengthen tcb_at_invs)
         apply (wpsimp wp: dmo_maskInterrupt_True maskInterrupt_invs
                           setVCPU_VPPIMasked_invs' simp: vcpuUpdate_def
                | wps)+
   apply (frule invs_arch_state)
   apply (simp add: valid_arch_state_def valid_fault_def tcb_at_invs)
   apply (clarsimp simp: obj_at_def cur_vcpu_def in_omonad)
  apply clarsimp
  apply (frule invs_arch_state')
  apply (rule conjI)
   apply (clarsimp simp: valid_arch_state'_def vcpu_at_is_vcpu')
   apply (erule ko_wp_at'_weakenE, simp)
  apply (simp add: tcb_at_invs')
  done

lemma handle_reserved_irq_corres[Interrupt_R_assms, corres]:
  "corres dc einvs
     (\<lambda>s. invs' s \<and> (irq \<in> non_kernel_IRQs \<longrightarrow> sch_act_not (ksCurThread s) s))
     (handle_reserved_irq irq) (handleReservedIRQ irq)"
  apply (clarsimp simp: handle_reserved_irq_def handleReservedIRQ_def irqVPPIEventIndex_def
                        irq_vppi_event_index_def non_kernel_IRQs_def IRQ_def irqVGICMaintenance_def
                        irqVTimerEvent_def)
  apply (rule conjI; clarsimp)
   apply (rule corres_guard_imp, rule vppiEvent_corres, assumption, fastforce)
  apply (rule corres_guard_imp)
    apply (rule corres_when)
     apply (fastforce intro: vgic_maintenance_corres simp: unat_arith_simps)+
  done

lemma maskIrqSignal_corres[Interrupt_R_assms, corres]:
  "corres dc \<top> \<top> (arch_mask_irq_signal irq) (Arch.maskIrqSignal irq)"
  unfolding arch_mask_irq_signal_def maskIrqSignal_def when_def
  by (corres corres: corres_machine_op)

lemma dmo_ackInterrupt_corres[Interrupt_R_assms, corres]:
  "corres dc \<top> \<top> (do_machine_op (ackInterrupt irq)) (doMachineOp (ackInterrupt irq))"
  by (corres corres: corres_machine_op)

lemma vgicMaintenance_invs'[wp]:
  "\<lbrace>invs' and (\<lambda>s. sch_act_not (ksCurThread s) s)\<rbrace>
   vgicMaintenance
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  supply if_split[split del]
  apply (clarsimp simp: vgicMaintenance_def get_gic_vcpu_ctrl_misr_def
                        get_gic_vcpu_ctrl_eisr1_def get_gic_vcpu_ctrl_eisr0_def)
  apply (wpsimp simp: if_apply_def2 wp: hoare_vcg_const_imp_lift)
            apply (strengthen st_tcb_ex_cap''[where P=active'])
            apply (strengthen invs_iflive')
            apply (clarsimp cong: imp_cong conj_cong simp: pred_conj_def)
            apply (rule_tac Q'="\<lambda>_ s. tcb_at' (ksCurThread s) s
                                      \<and> invs' s
                                      \<and> sch_act_not (ksCurThread s) s"
                    in hoare_post_imp)
             apply (clarsimp cong: imp_cong conj_cong simp: not_pred_tcb')
             apply (clarsimp simp: st_tcb_at'_def obj_at'_def runnable'_eq)
             apply (rule conjI)
              apply (fastforce elim!: st_tcb_ex_cap'' simp: valid_state'_def valid_pspace'_def)
             apply (clarsimp simp: invs'_def valid_state'_def valid_idle'_def obj_at'_def idle_tcb'_def)
            apply wps
            apply (wpsimp simp: if_apply_def2
                          wp: hoare_vcg_const_imp_lift hoare_drop_imps dmo'_gets_wp
                   | wps)+
  apply (clarsimp cong: conj_cong imp_cong split: if_split)
  apply (strengthen st_tcb_ex_cap''[where P=active'])
  apply (strengthen invs_iflive')
  apply (clarsimp cong: conj_cong imp_cong split: if_split)
  apply (rule conjI)
   apply (clarsimp simp: st_tcb_at'_def obj_at'_def runnable'_eq)
   apply (rule conjI)
    apply (fastforce elim!: st_tcb_ex_cap'' simp: valid_state'_def valid_pspace'_def)
   apply (clarsimp simp: invs'_def valid_state'_def valid_idle'_def obj_at'_def idle_tcb'_def)
  apply clarsimp
  done

lemma vppiEvent_invs'[wp]:
  "\<lbrace>invs' and (\<lambda>s. sch_act_not (ksCurThread s) s)\<rbrace>
    vppiEvent irq \<lbrace>\<lambda>y. invs'\<rbrace>"
  supply if_split[split del]
  apply (clarsimp simp: vppiEvent_def doMachineOp_bind)
  apply (wpsimp simp: if_apply_def2 wp: hoare_vcg_const_imp_lift)
            apply (strengthen st_tcb_ex_cap''[where P=active'])
            apply (strengthen invs_iflive')
            apply (clarsimp cong: imp_cong conj_cong simp: pred_conj_def)
            apply (rule_tac Q'="\<lambda>_ s. tcb_at' (ksCurThread s) s
                                      \<and> invs' s
                                      \<and> sch_act_not (ksCurThread s) s"
                    in hoare_post_imp)
             apply (clarsimp cong: imp_cong conj_cong simp: not_pred_tcb')
             apply (clarsimp simp: st_tcb_at'_def obj_at'_def runnable'_eq)
             apply (rule conjI)
              apply (fastforce elim!: st_tcb_ex_cap'' simp: valid_state'_def valid_pspace'_def)
             apply (clarsimp simp: invs'_def valid_state'_def valid_idle'_def obj_at'_def idle_tcb'_def)
            apply wps
            apply (wpsimp simp: if_apply_def2 vcpuUpdate_def
                          wp: hoare_vcg_const_imp_lift hoare_drop_imps
                              setVCPU_VPPIMasked_invs' dmo_maskInterrupt_True
                   | wps)+
  done

crunch maskIrqSignal
  for invs'[Interrupt_R_assms]: invs'
  (wp: dmo_maskInterrupt_True ignore: doMachineOp)

lemma handleReservedIRQ_invs'[Interrupt_R_assms]:
  "\<lbrace>invs' and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> sch_act_not (ksCurThread s) s)\<rbrace>
   handleReservedIRQ irq
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  by (wpsimp simp: inQ_def handleReservedIRQ_def if_apply_def2 irqVPPIEventIndex_def
                   IRQ_def irqVTimerEvent_def irqVGICMaintenance_def unat_arith_simps
                   non_kernel_IRQs_def
             split_del: if_split)

end (* Arch *)

interpretation Interrupt_R?: Interrupt_R AARCH64.arch_irq_control_inv_valid'
                                         AARCH64.arch_irq_control_inv_relation
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Interrupt_R_assms)?)?)
qed

context Arch begin arch_global_naming

named_theorems Interrupt_R_2_assms

lemma invoke_arch_irq_handler_invs'[Interrupt_R_2_assms, wp]:
  "\<lbrace>invs' and irq_handler_inv_valid' i\<rbrace> Arch.invokeIRQHandler i \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (cases i; (wpsimp simp: AARCH64_H.invokeIRQHandler_def theIRQ_def | rule conjI)+)

end (* Arch *)

interpretation Interrupt_R_2?: Interrupt_R_2 AARCH64.arch_irq_control_inv_valid'
                                             AARCH64.arch_irq_control_inv_relation
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Interrupt_R_2_assms)?)?)
qed

end
