(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchEmptyFail_H
imports EmptyFail_H
begin

context Arch begin arch_global_naming

clear_named_theorems Arch_assms (* accumulate assumptions for EmptyFail_H locale *)

lemma arch_deriveCap_empty_fail[Arch_assms, intro!, wp, simp]:
  "empty_fail (Arch.deriveCap x y)"
  unfolding RISCV64_H.deriveCap_def
  by (cases y, auto simp: isCap_simps cong: if_cong)

lemma empty_fail_getObject_ap[intro!, wp, simp]:
  "empty_fail (getObject p :: asidpool kernel)"
  by (simp add: empty_fail_getObject)

lemma empty_fail_getObject_pte[intro!, wp, simp]:
  "empty_fail (getObject p :: pte kernel)"
  by (simp add: empty_fail_getObject)

lemma empty_fail_lookupPTSlotFromLevel[intro!, wp, simp]:
  "empty_fail (lookupPTSlotFromLevel level pt vPtr)"
proof (induct level arbitrary: pt)
  case 0
  then show ?case by (subst lookupPTSlotFromLevel.simps, simp)
next
  case (Suc level)
  then show ?case
    by (subst lookupPTSlotFromLevel.simps) (wpsimp simp: checkPTAt_def pteAtIndex_def)
qed

lemma empty_fail_arch_cap_exhausted:
  " \<lbrakk>\<not> isFrameCap cap; \<not> isPageTableCap cap; \<not> isASIDControlCap cap; \<not> isASIDPoolCap cap\<rbrakk>
    \<Longrightarrow> empty_fail undefined"
  by (cases cap; simp add: isCap_simps)

crunch decodeRISCVMMUInvocation, Arch_postCapDeletion, setRegister, prepareThreadDelete
  for (empty_fail) empty_fail[Arch_assms, intro!, wp, simp]
  (simp: Let_def pteAtIndex_def
   wp: empty_fail_catch empty_fail_arch_cap_exhausted
   rule: RISCV64_H.postCapDeletion_def)

lemma empty_fail_lookupPTFromLevel[intro!, wp, simp]:
  "empty_fail (lookupPTFromLevel level ptPtr vPtr target)"
  by (induct level arbitrary: ptPtr; subst lookupPTFromLevel.simps; simp; wpsimp)

crunch
  Arch_finaliseCap, Arch.switchToThread, Arch.switchToIdleThread, prepareNextDomain, getRestartPC,
  makeArchFaultMessage
  for (empty_fail) empty_fail[Arch_assms, intro!, wp, simp]
  (rule: RISCV64_H.finaliseCap_def)

crunch
  decodeTransfer, checkValidIPCBuffer, Arch.decodeIRQControlInvocation, Arch.decodeInvocation,
  deleteGhost, Arch.createObject, getSanitiseRegisterInfo,
  handleArchFaultReply, prepareSetDomain, postModifyRegisters, postSetFlags,
  Arch.performIRQControl, Arch.invokeIRQHandler, Arch.performInvocation, handleSpuriousIRQ,
  maskIrqSignal, handleVMFault, checkIRQ, prepareThreadDelete, Arch.postCapDeletion
  for (empty_fail) empty_fail[Arch_assms, intro!, wp, simp]
  (simp: Let_def)

lemmas EmptyFail_H_assms = Arch_assms (* extract accumulated assumptions *)

end (* Arch *)

interpretation EmptyFail_H?: EmptyFail_H
proof goal_cases
  case 1 show ?case by (intro_locales; (unfold_locales; (fact RISCV64.EmptyFail_H_assms)?)?)
qed

context Arch begin arch_global_naming

clear_named_theorems Arch_assms (* accumulate assumptions for EmptyFail_H_2 locale *)

crunch
  handleReservedIRQ, handleHypervisorFault
  for (empty_fail) empty_fail[Arch_assms, intro!, wp, simp]
  (simp: Let_def)

lemmas EmptyFail_H_2_assms = Arch_assms (* extract accumulated assumptions *)

end (* Arch *)

interpretation EmptyFail_H_2?: EmptyFail_H_2
proof goal_cases
  case 1 show ?case by (intro_locales; (unfold_locales; (fact RISCV64.EmptyFail_H_2_assms)?)?)
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
