(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory EmptyFail_H
imports ArchRefine
begin

arch_requalify_facts (* FIXME arch-split: Machine_AI *)
  storeWord_empty_fail setRegister_empty_fail getRestartPC_empty_fail resetTimer_empty_fail
  setNextPC_empty_fail
lemmas [intro!, wp, simp] =
  storeWord_empty_fail setRegister_empty_fail getRestartPC_empty_fail resetTimer_empty_fail
  setNextPC_empty_fail

arch_requalify_facts (* FIXME arch-split: ArchEmptyFail_AI *)
  freeMemory_empty_fail clearMemory_empty_fail
lemmas [intro!, wp, simp] = freeMemory_empty_fail clearMemory_empty_fail

arch_requalify_consts (H) deleteGhost maskIrqSignal

crunch_ignore (empty_fail)
  (add: handleE' getCTE getObject updateObject ifM andM orM whileM ifM
        CSpaceDecls_H.resolveAddressBits
        doMachineOp suspend restart schedule)

lemmas forM_empty_fail[intro!, wp, simp] = empty_fail_mapM[simplified forM_def[symmetric]]
lemmas forM_x_empty_fail[intro!, wp, simp] = empty_fail_mapM_x[simplified forM_x_def[symmetric]]
lemmas forME_x_empty_fail[intro!, wp, simp] = empty_fail_mapME_x[simplified forME_x_def[symmetric]]

lemma withoutPreemption_empty_fail[intro!, wp, simp]:
  "empty_fail m \<Longrightarrow> empty_fail (withoutPreemption m)"
  by simp

lemma withoutFailure_empty_fail[intro!, wp, simp]:
  "empty_fail m \<Longrightarrow> empty_fail (withoutFailure m)"
  by simp

lemma catchFailure_empty_fail[intro!, wp, simp]:
  "\<lbrakk> empty_fail f; \<And>x. empty_fail (g x) \<rbrakk> \<Longrightarrow> empty_fail (catchFailure f g)"
  by (simp add: empty_fail_catch)

lemma emptyOnFailure_empty_fail[intro!, wp, simp]:
  "empty_fail m \<Longrightarrow> empty_fail (emptyOnFailure m)"
  by (simp add: emptyOnFailure_def empty_fail_catch)

lemma rethrowFailure_empty_fail [intro!, wp, simp]:
  "empty_fail m \<Longrightarrow> empty_fail (rethrowFailure f m)"
  by (wpsimp simp:rethrowFailure_def o_def)

lemma unifyFailure_empty_fail [intro!, wp, simp]:
  "empty_fail f \<Longrightarrow> empty_fail (unifyFailure f)"
  by (simp add: unifyFailure_def)

lemma lookupErrorOnFailure_empty_fail [intro!, wp, simp]:
  "empty_fail f \<Longrightarrow> empty_fail (lookupErrorOnFailure isSource f)"
  by (simp add: lookupErrorOnFailure_def)

lemma setObject_empty_fail [intro!, wp, simp]:
  assumes x: "(\<And>a b c. empty_fail (updateObject v a x b c))"
  shows "empty_fail (setObject x v)"
  by (wpsimp simp: setObject_def split_def wp: x)

lemma asUser_empty_fail [intro!, wp, simp]:
  "empty_fail f \<Longrightarrow> empty_fail (asUser t f)"
  unfolding asUser_def
  by (wpsimp | simp add: empty_fail_def)+

lemma capFaultOnFailure_empty_fail [intro!, wp, simp]:
  "empty_fail m \<Longrightarrow> empty_fail (capFaultOnFailure cptr rp m)"
  by (simp add: capFaultOnFailure_def)

crunch locateSlotCap
  for (empty_fail) empty_fail[intro!, wp, simp]

lemma resolveAddressBits_spec_empty_fail:
  notes spec_empty_fail_bindE'[wp_split]
  shows
  "spec_empty_fail (CSpace_H.resolveAddressBits a b c) s"
proof (induct arbitrary: s rule: resolveAddressBits.induct)
  case (1 a b c s)
  show ?case
    apply (simp add: resolveAddressBits.simps)
    apply (wp | simp | wpc | intro impI conjI | rule drop_spec_empty_fail)+
      apply (rule use_spec_empty_fail)
      apply (rule 1 | simp add: in_monad | rule drop_spec_empty_fail | force)+
    done
 qed

lemmas resolveAddressBits_empty_fail[intro!, wp, simp] =
       resolveAddressBits_spec_empty_fail[THEN use_spec_empty_fail]

declare ef_dmo'[intro!, wp, simp]

lemma empty_fail_getObject_ep [intro!, wp, simp]:
  "empty_fail (getObject p :: endpoint kernel)"
  by (simp add: empty_fail_getObject)

lemma empty_fail_getObject_reply [intro!, wp, simp]:
  "empty_fail (getObject p :: reply kernel)"
  by (simp add: empty_fail_getObject)

lemma empty_fail_getObject_sc [intro!, wp, simp]:
   "empty_fail (getObject p :: sched_context kernel)"
   by (simp add: empty_fail_getObject)

lemma getEndpoint_empty_fail [intro!, wp, simp]:
  "empty_fail (getEndpoint ep)"
  by (simp add: getEndpoint_def)

lemma constOnFailure_empty_fail[intro!, wp, simp]:
  "empty_fail m \<Longrightarrow> empty_fail (constOnFailure x m)"
  by (simp add: constOnFailure_def const_def empty_fail_catch)

crunch ensureNoChildren
  for (empty_fail) empty_fail[intro!, wp, simp]

lemma ignoreFailure_empty_fail[intro!, wp, simp]:
  "empty_fail x \<Longrightarrow> empty_fail (ignoreFailure x)"
  by (simp add: ignoreFailure_def empty_fail_catch)

crunch setExtraBadge, cteInsert
  for (empty_fail) empty_fail[intro!, wp, simp]
  (ignore: storeWord)

crunch lookupTargetSlot, ensureEmptySlot, lookupSourceSlot, lookupPivotSlot
  for (empty_fail) empty_fail[intro!, wp, simp]

lemmas finalise_spec_empty_fail_induct =
  finaliseSlot'.induct[where P="\<lambda>sl exp s. spec_empty_fail (finaliseSlot' sl exp) s"]

lemma spec_empty_fail_If:
  "\<lbrakk> P \<Longrightarrow> spec_empty_fail f s; \<not> P \<Longrightarrow> spec_empty_fail g s \<rbrakk>
   \<Longrightarrow> spec_empty_fail (if P then f else g) s"
  by (simp split: if_split)

lemma spec_empty_whenE':
  "\<lbrakk> P \<Longrightarrow> spec_empty_fail f s \<rbrakk> \<Longrightarrow> spec_empty_fail (whenE P f) s"
  by (simp add: whenE_def spec_empty_returnOk)

lemma checkCapAt_empty_fail[intro!, wp, simp]:
  "empty_fail action \<Longrightarrow> empty_fail (checkCapAt cap ptr action)"
  by (fastforce simp: checkCapAt_def)

lemma assertDerived_empty_fail[intro!, wp, simp]:
  "empty_fail f \<Longrightarrow> empty_fail (assertDerived src cap f)"
  by (fastforce simp: assertDerived_def)

lemma spec_empty_fail_unlessE':
  "\<lbrakk> \<not> P \<Longrightarrow> spec_empty_fail f s \<rbrakk> \<Longrightarrow> spec_empty_fail (unlessE P f) s"
  by (simp add:unlessE_def spec_empty_returnOk)

lemma Syscall_H_syscall_empty_fail[intro!, wp, simp]:
  "\<lbrakk>empty_fail a; \<And>x. empty_fail (b x); \<And>x. empty_fail (c x);
    \<And>x. empty_fail (d x); \<And>x. empty_fail (e x)\<rbrakk>
   \<Longrightarrow> empty_fail (syscall a b c d e)"
  apply (simp add:syscall_def)
  apply (wp | wpc | simp)+
  done

lemma catchError_empty_fail[intro!, wp, simp]:
  "\<lbrakk> empty_fail f; \<And>x. empty_fail (g x) \<rbrakk> \<Longrightarrow> empty_fail (catchError f g)"
  by fastforce

crunch setMRs, setMessageInfo
  for (empty_fail) empty_fail[wp, simp]
  (wp: empty_fail_catch simp: const_def Let_def)

locale EmptyFail_H =
  assumes arch_deriveCap_empty_fail[intro!, wp, simp]:
    "\<And>x y. empty_fail (Arch.deriveCap x y)"
  assumes Arch_postCapDeletion_empty_fail[intro!, wp, simp]:
    "\<And>c. empty_fail (Arch.postCapDeletion c)"
  assumes prepareThreadDelete_empty_fail[intro!, wp, simp]:
    "\<And>t. empty_fail (prepareThreadDelete t)"
  assumes arch_finaliseCap_empty_fail[intro!, wp, simp]:
    "\<And>x y. empty_fail (Arch.finaliseCap x y)"
  assumes arch_switchToThread_empty_fail[intro!, wp, simp]:
    "\<And>t. empty_fail (Arch.switchToThread t)"
  assumes arch_switchToIdleThread_empty_fail[intro!, wp, simp]:
    "empty_fail Arch.switchToIdleThread"
  assumes prepareNextDomain_empty_fail[intro!, wp, simp]:
    "empty_fail Arch.prepareNextDomain"
  assumes makeArchFaultMessage_empty_fail[intro!, wp, simp]:
    "\<And>af t. empty_fail (makeArchFaultMessage af t)"
  assumes maskIrqSignal_empty_fail[intro!, wp, simp]:
    "\<And>irq. empty_fail (Arch.maskIrqSignal irq)"
  assumes decodeTransfer_empty_fail[intro!, wp, simp]:
    "\<And>arg. empty_fail (decodeTransfer arg)"
  assumes checkValidIPCBuffer_empty_fail[intro!, wp, simp]:
    "\<And>vptr cap. empty_fail (checkValidIPCBuffer vptr cap)"
  assumes Arch_decodeIRQControlInvocation_empty_fail[intro!, wp, simp]:
    "\<And>label args srcSlot extraCaps.
     empty_fail (Arch.decodeIRQControlInvocation label args srcSlot extraCaps)"
  assumes Arch_decodeInvocation_empty_fail[intro!, wp, simp]:
    "\<And>label args capIndex slot cap extraCaps.
     empty_fail (Arch.decodeInvocation label args capIndex slot cap extraCaps)"
  assumes deleteGhost_empty_fail[intro!, wp, simp]:
    "\<And>ptr bits. empty_fail (Arch.deleteGhost ptr bits)"
  assumes Arch_createObject_empty_fail[intro!, wp, simp]:
    "\<And>t regionBase arg isDevice. empty_fail (Arch.createObject t regionBase arg isDevice)"
  assumes getSanitiseRegisterInfo_empty_fail[intro!, wp, simp]:
    "\<And>t. empty_fail (getSanitiseRegisterInfo t)"
  assumes handleArchFaultReply_empty_fail[intro!, wp, simp]:
    "\<And>x0 x1 x2 x3. empty_fail (handleArchFaultReply x0 x1 x2 x3)"
  assumes prepareSetDomain_empty_fail[intro!, wp, simp]:
    "\<And>t newDom. empty_fail (prepareSetDomain t newDom)"
  assumes postModifyRegisters_empty_fail[intro!, wp, simp]:
    "\<And>arg1 arg2. empty_fail (postModifyRegisters arg1 arg2)"
  assumes postSetFlags_empty_fail[intro!, wp, simp]:
    "\<And>t flags. empty_fail (postSetFlags t flags)"
  assumes Arch_performIRQControl_empty_fail[intro!, wp, simp]:
    "\<And>irq_inv. empty_fail (Arch.performIRQControl irq_inv)"
  assumes Arch_invokeIRQHandler_empty_fail[intro!, wp, simp]:
    "\<And>irq_inv. empty_fail (Arch.invokeIRQHandler irq_inv)"
  assumes Arch_performInvocation_empty_fail[intro!, wp, simp]:
    "\<And>i. empty_fail (Arch.performInvocation i)"
  assumes handleSpuriousIRQ_empty_fail[intro!, wp, simp]:
    "empty_fail handleSpuriousIRQ"
  assumes handleVMFault_empty_fail[intro!, wp, simp]:
    "\<And>t vmfault. empty_fail (handleVMFault t vmfault)"
  assumes checkIRQ_empty_fail[intro!, wp, simp]:
    "\<And>irq. empty_fail (checkIRQ irq)"
begin

lemma deriveCap_empty_fail[intro!, wp, simp]:
  "empty_fail (RetypeDecls_H.deriveCap slot y)"
  by (clarsimp simp: empty_fail_bindE deriveCap_def)

lemma transferCapsToSlots_empty_fail[intro!, wp, simp]:
  "empty_fail (transferCapsToSlots ep buffer n caps slots mi)"
  by (induct caps arbitrary: slots n mi;
      wpsimp simp: Let_def split_def split_del: if_split)

lemma decodeCNodeInvocation_empty_fail[intro!, wp, simp]:
  "empty_fail (decodeCNodeInvocation label args cap exs)"
  apply (rule_tac label=label and args=args and exs=exs in decode_cnode_cases2)
         apply (simp_all add: decodeCNodeInvocation_def
                              split_def cnode_invok_case_cleanup unlessE_whenE
                         cong: if_cong bool.case_cong list.case_cong)
  by (simp | wp | wpc | safe)+ (* slow *)

crunch SchedContextDecls_H.postpone
  for (empty_fail) "_H_empty_fail"[intro!, wp, simp]
  (simp: getSchedContext_def)

crunch
  cancelIPC, setThreadState, tcbSchedDequeue, isStopped, possibleSwitchTo, tcbSchedAppend,
  refillUnblockCheck, schedContextResume, ifCondRefillUnblockCheck
  for (empty_fail) empty_fail[intro!, wp, simp]
  (simp: Let_def wp: empty_fail_whileLoop cong: option.case_cong_weak)

crunch ThreadDecls_H.suspend
  for (empty_fail) "_H_empty_fail"[intro!, wp, simp]
  (ignore_del: ThreadDecls_H.suspend)

lemma ThreadDecls_H_restart_empty_fail[intro!, wp, simp]:
  "empty_fail (ThreadDecls_H.restart target)"
  unfolding restart_def getCurSc_def by wpsimp

crunch finaliseCap, preemptionPoint, capSwapForDelete
  for (empty_fail) empty_fail[intro!, wp, simp]
  (wp: empty_fail_catch simp: Let_def)

lemma finaliseSlot_spec_empty_fail:
  notes spec_empty_fail_bindE'[rotated, wp_split]
  shows "spec_empty_fail (finaliseSlot x b) s"
unfolding finaliseSlot_def
proof (induct rule: finalise_spec_empty_fail_induct)
  case (1 x b s)
  show ?case
  apply (subst finaliseSlot'_simps_ext)
  apply (simp only: split_def Let_def K_bind_def fun_app_def)
  apply (wp spec_empty_whenE' spec_empty_fail_If | wpc
         | rule 1[unfolded Let_def K_bind_def split_def fun_app_def,
                  simplified], (simp | intro conjI)+
         | rule drop_spec_empty_fail | simp)+
  done
qed

lemmas finaliseSlot_empty_fail[intro!, wp, simp] =
       finaliseSlot_spec_empty_fail[THEN use_spec_empty_fail]

crunch cteDelete
  for (empty_fail) empty_fail[intro!, wp, simp]

lemma cteRevoke_spec_empty_fail:
  notes spec_empty_fail_bindE'[wp_split]
  shows "spec_empty_fail (cteRevoke p) s"
proof (induct rule: cteRevoke.induct)
  case (1 p s)
  show ?case
  apply (simp add: cteRevoke.simps)
  apply (wp spec_empty_whenE' spec_empty_fail_unlessE' | rule drop_spec_empty_fail, wp)+
  apply (rule 1, auto simp add: in_monad)
  done
qed

lemmas cteRevoke_empty_fail[intro!, wp, simp] =
       cteRevoke_spec_empty_fail[THEN use_spec_empty_fail]

crunch
  chooseThread, getDomainTime, nextDomain, isHighestPrio, switchSchedContext, setNextInterrupt
  for (empty_fail) empty_fail[intro!, wp, simp]
  (wp: empty_fail_catch empty_fail_setDeadline empty_fail_whileLoop)

crunch tcbReleaseDequeue
  for (empty_fail) empty_fail[intro!, wp, simp]

lemma awaken_empty_fail[intro!, wp, simp]:
  "empty_fail awaken"
  apply (clarsimp simp: awaken_def tcbReleaseDequeue_def)
  apply (wpsimp wp: empty_fail_whileLoop)
  done

lemma ThreadDecls_H_schedule_empty_fail[intro!, wp, simp]:
  "empty_fail schedule"
  supply if_cong[cong]
  apply (simp add: schedule_def scAndTimer_def checkDomainTime_def)
  apply (clarsimp simp: scheduleChooseNewThread_def split: if_split | wp | wpc | intro conjI impI)+
  done

crunch handleFault
  for (empty_fail) empty_fail[wp, simp]

end (* EmptyFail_H *)

locale EmptyFail_H_2 = EmptyFail_H +
  assumes handleReservedIRQ_empty_fail[intro!, wp, simp]:
    "\<And>irq. empty_fail (handleReservedIRQ irq)"
  assumes handleHypervisorFault_empty_fail[intro!, wp, simp]:
    "\<And>thread fault. empty_fail (handleHypervisorFault thread fault)"

end
