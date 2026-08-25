(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchEmptyFail_H
imports EmptyFail_H
begin

context Arch begin arch_global_naming

named_theorems EmptyFail_H_assms

lemma arch_deriveCap_empty_fail[EmptyFail_H_assms, intro!, wp, simp]:
  "empty_fail (Arch.deriveCap x y)"
  unfolding ARM_HYP_H.deriveCap_def
  by (cases y, auto simp: isCap_simps cong: if_cong)

lemma empty_fail_getObject_ap[intro!, wp, simp]:
  "empty_fail (getObject p :: asidpool kernel)"
  by (simp add: empty_fail_getObject)

lemma empty_fail_getObject_pte[intro!, wp, simp]:
  "empty_fail (getObject p :: pte kernel)"
  by (simp add: empty_fail_getObject)

lemma empty_fail_getObject_pde [intro!, wp, simp]:
  "empty_fail (getObject p :: pde kernel)"
  by (simp add: empty_fail_getObject)

lemma empty_fail_getObject_vcpu[intro!, wp, simp]:
  "empty_fail (getObject p :: vcpu kernel)"
  by (simp add: empty_fail_getObject)

crunch decodeARMMMUInvocation, Arch_postCapDeletion, setRegister, prepareThreadDelete
  for (empty_fail) empty_fail[EmptyFail_H_assms, intro!, wp, simp]
  (simp: Let_def ARMMMU_improve_cases
   wp: empty_fail_catch
   rule: ARM_HYP_H.postCapDeletion_def)

crunch vcpuEnable, vcpuRestore
  for (empty_fail) empty_fail[intro!, wp, simp]
  (simp: uncurry_def)

crunch
  Arch_finaliseCap, Arch.switchToThread, Arch.switchToIdleThread, prepareNextDomain, getRestartPC,
  makeArchFaultMessage
  for (empty_fail) empty_fail[EmptyFail_H_assms, intro!, wp, simp]
  (rule: ARM_HYP_H.finaliseCap_def
   ignore: get_gic_vcpu_ctrl_vmcr get_gic_vcpu_ctrl_apr)

crunch
  decodeVCPUInjectIRQ, decodeVCPUWriteReg, decodeVCPUReadReg, doFlush, decodeVCPUAckVPPI,
  decodeTransfer, checkValidIPCBuffer, Arch.decodeIRQControlInvocation, Arch.decodeInvocation,
  deleteGhost, Arch.createObject, getSanitiseRegisterInfo,
  handleArchFaultReply, prepareSetDomain, postModifyRegisters, postSetFlags,
  Arch.performIRQControl, Arch.invokeIRQHandler, Arch.performInvocation, handleSpuriousIRQ,
  maskIrqSignal, handleVMFault, checkIRQ, prepareThreadDelete, Arch.postCapDeletion
  for (empty_fail) empty_fail[EmptyFail_H_assms, intro!, wp, simp]
  (simp: Let_def)

end (* Arch *)

interpretation EmptyFail_H?: EmptyFail_H
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact EmptyFail_H_assms)?)?)
qed

context Arch begin arch_global_naming

named_theorems EmptyFail_H_2_assms

crunch
  handleReservedIRQ, handleHypervisorFault
  for (empty_fail) empty_fail[EmptyFail_H_2_assms, intro!, wp, simp]
  (simp: Let_def)

end (* Arch *)

interpretation EmptyFail_H_2?: EmptyFail_H_2
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact EmptyFail_H_2_assms)?)?)
qed

crunch callKernel
  for (empty_fail) empty_fail
  (wp: empty_fail_catch)

theorem call_kernel_serial:
  "\<lbrakk> (einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s) and (ct_running or ct_idle) and
      schact_is_rct and (\<lambda>s. 0 < domain_time s \<and> valid_domain_list s)) s;
     \<exists>s'. (s, s') \<in> state_relation \<and>
          (invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s) and (ct_running' or ct_idle') and
           (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
           (\<lambda>s. vs_valid_duplicates' (ksPSpace s))) s' \<rbrakk>
   \<Longrightarrow> fst (call_kernel event s) \<noteq> {}"
  apply (cut_tac m = "call_kernel event" in corres_underlying_serial)
    apply (rule kernel_corres)
   apply (rule callKernel_empty_fail)
  apply auto
  done

end
