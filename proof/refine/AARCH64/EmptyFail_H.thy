(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory EmptyFail_H
imports Refine
begin

crunch_ignore (empty_fail)
  (add: handleE' getCTE getObject updateObject
        CSpaceDecls_H.resolveAddressBits
        doMachineOp suspend restart schedule)

context begin interpretation Arch . (*FIXME: arch_split*)

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

lemma empty_fail_getObject_tcb [intro!, wp, simp]:
  shows "empty_fail (getObject x :: tcb kernel)"
  by (auto intro: empty_fail_getObject)

lemma getEndpoint_empty_fail [intro!, wp, simp]:
  "empty_fail (getEndpoint ep)"
  by (simp add: getEndpoint_def)

lemma constOnFailure_empty_fail[intro!, wp, simp]:
  "empty_fail m \<Longrightarrow> empty_fail (constOnFailure x m)"
  by (simp add: constOnFailure_def const_def empty_fail_catch)

lemma ArchRetypeDecls_H_deriveCap_empty_fail[intro!, wp, simp]:
  "isPageTableCap y \<or> isFrameCap y \<or> isASIDControlCap y \<or> isASIDPoolCap y \<or> isVCPUCap y
   \<Longrightarrow> empty_fail (Arch.deriveCap x y)"
  apply (simp add: AARCH64_H.deriveCap_def)
  by (auto simp: isCap_simps)

crunch ensureNoChildren
  for (empty_fail) empty_fail[intro!, wp, simp]

lemma deriveCap_empty_fail[intro!, wp, simp]:
  "empty_fail (RetypeDecls_H.deriveCap slot y)"
  apply (simp add: Retype_H.deriveCap_def)
  apply (clarsimp simp: empty_fail_bindE)
  apply (case_tac "capCap y")
      apply (simp_all add: isCap_simps)
  done

crunch setExtraBadge, cteInsert
  for (empty_fail) empty_fail[intro!, wp, simp]

lemma transferCapsToSlots_empty_fail[intro!, wp, simp]:
  "empty_fail (transferCapsToSlots ep buffer n caps slots mi)"
  apply (induct caps arbitrary: slots n mi)
   apply simp
  apply (simp add: Let_def split_def
             split del: if_split)
  apply (simp | wp | wpc | safe)+
  done

crunch lookupTargetSlot, ensureEmptySlot, lookupSourceSlot, lookupPivotSlot
  for (empty_fail) empty_fail[intro!, wp, simp]

lemma decodeCNodeInvocation_empty_fail[intro!, wp, simp]:
  "empty_fail (decodeCNodeInvocation label args cap exs)"
  apply (rule_tac label=label and args=args and exs=exs in decode_cnode_cases2)
         apply (simp_all add: decodeCNodeInvocation_def
                         split_def cnode_invok_case_cleanup unlessE_whenE
                   cong: if_cong bool.case_cong list.case_cong)
         by (simp | wp | wpc | safe)+

lemma empty_fail_getObject_ap [intro!, wp, simp]:
  "empty_fail (getObject p :: asidpool kernel)"
  by (simp add: empty_fail_getObject)

lemma empty_fail_getObject_pte [intro!, wp, simp]:
  "empty_fail (getObject p :: pte kernel)"
  by (simp add: empty_fail_getObject)

lemma empty_fail_getObject_vcpu [intro!, wp, simp]:
  "empty_fail (getObject p :: vcpu kernel)"
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

(* FIXME AARCH64 this and empty_fail_pt_type_exhausted are needed to effectively crunch decodeARMMMUInvocation,
   so should be moved much higher and then deployed to other crunches of decodeARMMMUInvocation,
   which are hand-held at present  *)
lemma empty_fail_arch_cap_exhausted:
  "\<lbrakk>\<not> isFrameCap cap; \<not> isPageTableCap cap; \<not> isASIDControlCap cap; \<not> isASIDPoolCap cap;
    \<not> isVCPUCap cap\<rbrakk>
   \<Longrightarrow> empty_fail undefined"
  by (cases cap; simp add: isCap_simps)

(* FIXME AARCH64 move somewhere high up, see empty_fail_arch_cap_exhausted *)
lemma empty_fail_pt_type_exhausted:
  "\<lbrakk> pt_t \<noteq> NormalPT_T; pt_t \<noteq> VSRootPT_T \<rbrakk>
   \<Longrightarrow> False"
  by (case_tac pt_t; simp)

crunch decodeARMMMUInvocation
  for (empty_fail) empty_fail[intro!, wp, simp]
  (simp: Let_def pteAtIndex_def
   wp: empty_fail_catch empty_fail_pt_type_exhausted empty_fail_arch_cap_exhausted)

lemma ignoreFailure_empty_fail[intro!, wp, simp]:
  "empty_fail x \<Longrightarrow> empty_fail (ignoreFailure x)"
  by (simp add: ignoreFailure_def empty_fail_catch)

crunch cancelIPC, setThreadState, tcbSchedDequeue, setupReplyMaster, isStopped, possibleSwitchTo, tcbSchedAppend
  for (empty_fail) empty_fail[intro!, wp, simp]
(simp: Let_def setNotification_def setBoundNotification_def wp: empty_fail_getObject)

crunch "ThreadDecls_H.suspend"
  for (empty_fail) "_H_empty_fail"[intro!, wp, simp]
  (ignore_del: ThreadDecls_H.suspend)

lemma ThreadDecls_H_restart_empty_fail[intro!, wp, simp]:
  "empty_fail (ThreadDecls_H.restart target)"
  by (fastforce simp: restart_def)

lemma vcpuUpdate_empty_fail[intro!, wp, simp]:
  "empty_fail (vcpuUpdate p f)"
  by (fastforce simp: vcpuUpdate_def)

crunch vcpuEnable, vcpuRestore
  for (empty_fail) empty_fail[intro!, wp, simp]
  (simp: uncurry_def)

lemma empty_fail_lookupPTFromLevel[intro!, wp, simp]:
  "empty_fail (lookupPTFromLevel level ptPtr vPtr target)"
  by (induct level arbitrary: ptPtr; subst lookupPTFromLevel.simps; simp; wpsimp)

crunch finaliseCap, preemptionPoint, capSwapForDelete
  for (empty_fail) empty_fail[intro!, wp, simp]
(wp: empty_fail_catch simp: Let_def ignore: lookupPTFromLevel)

lemmas finalise_spec_empty_fail_induct = finaliseSlot'.induct[where P=
    "\<lambda>sl exp s. spec_empty_fail (finaliseSlot' sl exp) s"]

lemma spec_empty_fail_If:
  "\<lbrakk> P \<Longrightarrow> spec_empty_fail f s; \<not> P \<Longrightarrow> spec_empty_fail g s \<rbrakk>
   \<Longrightarrow> spec_empty_fail (if P then f else g) s"
  by (simp split: if_split)

lemma spec_empty_whenE':
  "\<lbrakk> P \<Longrightarrow> spec_empty_fail f s \<rbrakk> \<Longrightarrow> spec_empty_fail (whenE P f) s"
  by (simp add: whenE_def spec_empty_returnOk)

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

lemma checkCapAt_empty_fail[intro!, wp, simp]:
  "empty_fail action \<Longrightarrow> empty_fail (checkCapAt cap ptr action)"
  by (fastforce simp: checkCapAt_def)

lemma assertDerived_empty_fail[intro!, wp, simp]:
  "empty_fail f \<Longrightarrow> empty_fail (assertDerived src cap f)"
  by (fastforce simp: assertDerived_def)

crunch cteDelete
  for (empty_fail) empty_fail[intro!, wp, simp]

lemma spec_empty_fail_unlessE':
  "\<lbrakk> \<not> P \<Longrightarrow> spec_empty_fail f s \<rbrakk> \<Longrightarrow> spec_empty_fail (unlessE P f) s"
  by (simp add:unlessE_def spec_empty_returnOk)

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

crunch
  chooseThread, getDomainTime, nextDomain, isHighestPrio
  for (empty_fail) empty_fail[intro!, wp, simp]
  (wp: empty_fail_catch)

lemma ThreadDecls_H_schedule_empty_fail[intro!, wp, simp]:
  "empty_fail schedule"
  apply (simp add: schedule_def)
  apply (clarsimp simp: scheduleChooseNewThread_def split: if_split | wp | wpc)+
  done

crunch setMRs, setMessageInfo
  for (empty_fail) empty_fail[wp, simp]
(wp: empty_fail_catch simp: const_def Let_def)

crunch decodeVCPUInjectIRQ, decodeVCPUWriteReg, decodeVCPUReadReg, doFlush,
                                decodeVCPUAckVPPI
  for (empty_fail) empty_fail
  (simp: Let_def)

crunch handleFault
  for (empty_fail) empty_fail[wp, simp]

lemma handleHypervisorFault_empty_fail[intro!, wp, simp]:
  "empty_fail (handleHypervisorFault t f)"
  by (cases f, simp add: handleHypervisorFault_def isFpuEnable_def split del: if_split)
     wpsimp

crunch callKernel
  for (empty_fail) empty_fail
  (wp: empty_fail_catch)

theorem call_kernel_serial:
  "\<lbrakk> (einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s) and (ct_running or ct_idle) and
              schact_is_rct and
              (\<lambda>s. 0 < domain_time s \<and> valid_domain_list s)) s;
       \<exists>s'. (s, s') \<in> state_relation \<and>
            (invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s) and (ct_running' or ct_idle') and
              (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)) s' \<rbrakk>
    \<Longrightarrow> fst (call_kernel event s) \<noteq> {}"
  apply (cut_tac m = "call_kernel event" in corres_underlying_serial)
    apply (rule kernel_corres)
   apply (rule callKernel_empty_fail)
  apply auto
  done

end

end
