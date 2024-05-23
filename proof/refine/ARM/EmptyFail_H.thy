(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory EmptyFail_H
imports Refine
begin

crunch_ignore (empty_fail)
  (add: handleE' getCTE getObject updateObject ifM andM orM whileM ifM
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
  apply (simp add:rethrowFailure_def o_def)
  apply (wp | simp)+
  done

lemma unifyFailure_empty_fail [intro!, wp, simp]:
  "empty_fail f \<Longrightarrow> empty_fail (unifyFailure f)"
  by (simp add: unifyFailure_def)

lemma lookupErrorOnFailure_empty_fail [intro!, wp, simp]:
  "empty_fail f \<Longrightarrow> empty_fail (lookupErrorOnFailure isSource f)"
  by (simp add: lookupErrorOnFailure_def)

lemma setObject_empty_fail [intro!, wp, simp]:
  assumes x: "(\<And>a b c. empty_fail (updateObject v a x b c))"
  shows "empty_fail (setObject x v)"
  apply (simp add: setObject_def split_def)
  apply (wp x | simp)+
  done

lemma asUser_empty_fail [intro!, wp, simp]:
  "empty_fail f \<Longrightarrow> empty_fail (asUser t f)"
  apply (simp add:asUser_def)
  apply (wp | wpc | simp | simp add: empty_fail_def)+
  done

lemma capFaultOnFailure_empty_fail [intro!, wp, simp]:
  "empty_fail m \<Longrightarrow> empty_fail (capFaultOnFailure cptr rp m)"
  apply (simp add: capFaultOnFailure_def)
  done

crunch (empty_fail) empty_fail[intro!, wp, simp]: locateSlotCap

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

lemma getEndpoint_empty_fail [intro!, wp, simp]:
  "empty_fail (getEndpoint ep)"
  by (simp add: getEndpoint_def)

lemma constOnFailure_empty_fail[intro!, wp, simp]:
  "empty_fail m \<Longrightarrow> empty_fail (constOnFailure x m)"
  by (simp add: constOnFailure_def const_def empty_fail_catch)

lemma ArchRetypeDecls_H_deriveCap_empty_fail[intro!, wp, simp]:
  "isPageTableCap y \<or> isPageDirectoryCap y \<or> isPageCap y
   \<or> isASIDControlCap y \<or> isASIDPoolCap y
   \<Longrightarrow> empty_fail (Arch.deriveCap x y)"
  apply (simp add: ARM_H.deriveCap_def)
  by auto

crunch (empty_fail) empty_fail[intro!, wp, simp]: ensureNoChildren

lemma deriveCap_empty_fail[intro!, wp, simp]:
  "empty_fail (RetypeDecls_H.deriveCap slot y)"
  apply (simp add: Retype_H.deriveCap_def)
  apply (clarsimp simp: empty_fail_bindE)
  apply (case_tac "capCap y")
      apply (simp_all add: isPageTableCap_def isPageDirectoryCap_def
                           isPageCap_def isASIDPoolCap_def isASIDControlCap_def)
  done

crunch (empty_fail) empty_fail[intro!, wp, simp]: setExtraBadge, cteInsert

lemma transferCapsToSlots_empty_fail[intro!, wp, simp]:
  "empty_fail (transferCapsToSlots ep buffer n caps slots mi)"
  apply (induct caps arbitrary: slots n mi)
   apply simp
  apply (simp add: Let_def split_def
             split del: if_split)
  apply (simp | wp | wpc | safe)+
  done

crunch (empty_fail) empty_fail[intro!, wp, simp]: lookupTargetSlot, ensureEmptySlot, lookupSourceSlot, lookupPivotSlot

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

lemma empty_fail_getObject_pde [intro!, wp, simp]:
  "empty_fail (getObject p :: pde kernel)"
  by (simp add: empty_fail_getObject)

lemma empty_fail_getObject_pte [intro!, wp, simp]:
  "empty_fail (getObject p :: pte kernel)"
  by (simp add: empty_fail_getObject)

crunch (empty_fail) empty_fail[intro!, wp, simp]: decodeARMMMUInvocation
(simp: Let_def ARMMMU_improve_cases)

lemma ignoreFailure_empty_fail[intro!, wp, simp]:
  "empty_fail x \<Longrightarrow> empty_fail (ignoreFailure x)"
  by (simp add: ignoreFailure_def empty_fail_catch)

lemma empty_fail_getObject_sc [intro!, wp, simp]:
   "empty_fail (getObject p :: sched_context kernel)"
   by (simp add: empty_fail_getObject)

crunch (empty_fail) "_H_empty_fail"[intro!, wp, simp]: "SchedContextDecls_H.postpone"
  (simp: getSchedContext_def)

context
notes option.case_cong_weak[cong]
begin
crunch (empty_fail) empty_fail[intro!, wp, simp]:
  cancelIPC, setThreadState, tcbSchedDequeue, isStopped, possibleSwitchTo, tcbSchedAppend,
  refillUnblockCheck, schedContextResume, ifCondRefillUnblockCheck
  (simp: Let_def wp: empty_fail_whileLoop)
end

crunch (empty_fail) "_H_empty_fail"[intro!, wp, simp]: "ThreadDecls_H.suspend"
  (ignore_del: ThreadDecls_H.suspend)

lemma ThreadDecls_H_restart_empty_fail[intro!, wp, simp]:
  "empty_fail (ThreadDecls_H.restart target)"
  unfolding restart_def getCurSc_def by wpsimp

crunch (empty_fail) empty_fail[intro!, wp, simp]: finaliseCap, preemptionPoint, capSwapForDelete
  (wp: empty_fail_catch simp: Let_def)

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

crunch (empty_fail) empty_fail[intro!, wp, simp]: cteDelete

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

crunch (empty_fail) empty_fail[intro!, wp, simp]:
  chooseThread, getDomainTime, nextDomain, isHighestPrio, switchSchedContext, setNextInterrupt
  (wp: empty_fail_catch empty_fail_setDeadline empty_fail_whileLoop)

crunch (empty_fail) empty_fail[intro!, wp, simp]: tcbReleaseDequeue

lemma awaken_empty_fail[intro!, wp, simp]:
  "empty_fail awaken"
  apply (clarsimp simp: awaken_def awakenBody_def)
  apply (wpsimp wp: empty_fail_whileLoop)
  done

lemma ThreadDecls_H_schedule_empty_fail[intro!, wp, simp]:
  "empty_fail schedule"
  apply (simp add: schedule_def scAndTimer_def checkDomainTime_def)
  apply (clarsimp simp: scheduleChooseNewThread_def split: if_split | wp | wpc | intro conjI impI)+
  done

lemma tcbEPFindIndex_empty_fail[intro!, wp, simp]:
  "empty_fail (tcbEPFindIndex t qs ci)"
  by (induct ci; subst tcbEPFindIndex.simps; wpsimp)

crunch (empty_fail) empty_fail: callKernel
  (wp: empty_fail_catch)

theorem call_kernel_serial:
  "\<lbrakk> (einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s) and (ct_running or ct_idle) and
                schact_is_rct and
                current_time_bounded and
                consumed_time_bounded and
                valid_machine_time and
                ct_not_in_release_q and
                cur_sc_active and
                (\<lambda>s. cur_sc_offset_ready (consumed_time s) s) and
                (\<lambda>s. cur_sc_offset_sufficient (consumed_time s) s) and
                (\<lambda>s. 0 < domain_time s \<and> valid_domain_list s)) s;
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

end
