(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Bits_R
imports Corres ArchStateRelationLemmas
begin

crunch_ignore (add:
  bind return "when" get gets fail assert put modify unless select alternative assert_opt gets_the
  returnOk throwError lift bindE liftE whenE unlessE throw_opt assertE liftM liftME sequence_x
  zipWithM_x mapM_x sequence mapM sequenceE_x sequenceE mapME mapME_x catch select_f
  handleE' handleE handle_elseE forM forM_x zipWithM filterM forME_x
  withoutFailure throw catchFailure rethrowFailure capFaultOnFailure lookupErrorOnFailure
  nullCapOnFailure nothingOnFailure without_preemption withoutPreemption preemptionPoint
  cap_fault_on_failure lookup_error_on_failure const_on_failure ignore_failure ignoreFailure
  empty_on_failure emptyOnFailure unifyFailure unify_failure throw_on_false
  storeWordVM loadWord setRegister getRegister getRestartPC
  debugPrint setNextPC maskInterrupt clearMemory throw_on_false unifyFailure ignoreFailure
  empty_on_failure emptyOnFailure clearMemoryVM null_cap_on_failure setNextPC getRestartPC
  assertDerived throw_on_false getObject setObject updateObject loadObject)

context Arch begin (*FIXME: arch-split*)

crunch_ignore (add:
  invalidateLocalTLB_ASID invalidateLocalTLB_VAASID
  cleanByVA cleanByVA_PoU invalidateByVA invalidateByVA_I invalidate_I_PoU
  cleanInvalByVA branchFlush clean_D_PoU cleanInvalidate_D_PoC cleanInvalidateL2Range
  invalidateL2Range cleanL2Range flushBTAC writeContextID isb dsb dmb
  setHardwareASID setCurrentPD)

end

context begin interpretation Arch . (*FIXME: arch-split*)

lemma withoutFailure_wp [wp]:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> withoutFailure f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> withoutFailure f \<lbrace>Q\<rbrace>,-"
  "\<lbrace>\<top>\<rbrace> withoutFailure f -,\<lbrace>E\<rbrace>"
  by (auto simp: validE_R_def validE_E_def valid_def)

lemma no_fail_typeError [simp, wp]:
  "no_fail \<bottom> (typeError xs ko)"
  by (rule no_fail_False)

lemma isCap_simps':
  "isZombie v = (\<exists>v0 v1 v2. v = Zombie v0 v1 v2)"
  "isArchObjectCap v = (\<exists>v0. v = ArchObjectCap v0)"
  "isThreadCap v = (\<exists>v0. v = ThreadCap v0)"
  "isCNodeCap v = (\<exists>v0 v1 v2 v3. v = CNodeCap v0 v1 v2 v3)"
  "isNotificationCap v = (\<exists>v0 v1 v2 v3. v = NotificationCap v0 v1 v2 v3)"
  "isEndpointCap v = (\<exists>v0 v1 v2 v3 v4 v5. v = EndpointCap v0 v1 v2 v3 v4 v5)"
  "isUntypedCap v = (\<exists>d v0 v1 f. v = UntypedCap d v0 v1 f)"
  "isReplyCap v = (\<exists>v0 v1 v2. v = ReplyCap v0 v1 v2)"
  "isIRQControlCap v = (v = IRQControlCap)"
  "isIRQHandlerCap v = (\<exists>v0. v = IRQHandlerCap v0)"
  "isNullCap v = (v = NullCap)"
  "isDomainCap v = (v = DomainCap)"
  "isPageCap w = (\<exists>d v0 v1 v2 v3. w = PageCap d v0 v1 v2 v3)"
  "isPageTableCap w = (\<exists>v0 v1. w = PageTableCap v0 v1)"
  "isPageDirectoryCap w = (\<exists>v0 v1. w = PageDirectoryCap v0 v1)"
  "isASIDControlCap w = (w = ASIDControlCap)"
  "isASIDPoolCap w = (\<exists>v0 v1. w = ASIDPoolCap v0 v1)"
  "isArchPageCap cap = (\<exists>d ref rghts sz data. cap = ArchObjectCap (PageCap d ref rghts sz data))"
  "isVCPUCap w = (\<exists>v. w = VCPUCap v)"
  "isSGISignalCap w = (\<exists>irq target. w = SGISignalCap irq target)"
  by (auto simp: isCap_defs split: capability.splits arch_capability.splits)

lemmas isCap_simps = isCap_simps' isArchSGISignalCap_def

lemma untyped_not_null [simp]:
  "\<not> isUntypedCap NullCap" by (simp add: isCap_simps)

text \<open>Miscellaneous facts about low level constructs\<close>

lemma projectKO_tcb:
  "(projectKO_opt ko = Some t) = (ko = KOTCB t)"
  by (cases ko) (auto simp: projectKO_opts_defs)

lemma tcb_of'_TCB[simp]:
  "tcb_of' (KOTCB tcb) = Some tcb"
  by (simp add: projectKO_tcb)

lemma projectKO_cte:
  "(projectKO_opt ko = Some t) = (ko = KOCTE t)"
  by (cases ko) (auto simp: projectKO_opts_defs)

lemma projectKO_ep:
  "(projectKO_opt ko = Some t) = (ko = KOEndpoint t)"
  by (cases ko) (auto simp: projectKO_opts_defs)

lemma projectKO_ntfn:
  "(projectKO_opt ko = Some t) = (ko = KONotification t)"
  by (cases ko) (auto simp: projectKO_opts_defs)

lemma projectKO_ASID:
  "(projectKO_opt ko = Some t) = (ko = KOArch (KOASIDPool t))"
  by (cases ko)
     (auto simp: projectKO_opts_defs split: arch_kernel_object.splits)

lemma projectKO_PTE:
  "(projectKO_opt ko = Some t) = (ko = KOArch (KOPTE t))"
  by (cases ko)
     (auto simp: projectKO_opts_defs split: arch_kernel_object.splits)

lemma projectKO_PDE:
  "(projectKO_opt ko = Some t) = (ko = KOArch (KOPDE t))"
  by (cases ko)
     (auto simp: projectKO_opts_defs split: arch_kernel_object.splits)

lemma projectKO_user_data:
  "(projectKO_opt ko = Some (t :: user_data)) = (ko = KOUserData)"
  by (cases ko)
     (auto simp: projectKO_opts_defs split: arch_kernel_object.splits)

lemma projectKO_user_data_device:
  "(projectKO_opt ko = Some (t :: user_data_device)) = (ko = KOUserDataDevice)"
  by (cases ko)
     (auto simp: projectKO_opts_defs split: arch_kernel_object.splits)

lemma projectKO_VCPU:
  "(projectKO_opt ko = Some t) = (ko = KOArch (KOVCPU t))"
  by (cases ko)
     (auto simp: projectKO_opts_defs split: arch_kernel_object.splits)

lemmas projectKOs =
  projectKO_ntfn projectKO_ep projectKO_cte projectKO_tcb projectKO_VCPU
  projectKO_ASID projectKO_PTE projectKO_PDE projectKO_user_data projectKO_user_data_device
  projectKO_eq projectKO_eq2

lemma capAligned_epI:
  "ep_at' p s \<Longrightarrow> capAligned (EndpointCap p a b c d e)"
  apply (clarsimp simp: obj_at'_real_def capAligned_def
                        objBits_simps word_bits_def)
  apply (drule ko_wp_at_norm)
  apply clarsimp
  apply (drule ko_wp_at_aligned)
  apply (simp add: objBits_simps' projectKOs capUntypedPtr_def isCap_simps)
  done

lemma capAligned_ntfnI:
  "ntfn_at' p s \<Longrightarrow> capAligned (NotificationCap p a b c)"
  apply (clarsimp simp: obj_at'_real_def capAligned_def
                        objBits_simps word_bits_def capUntypedPtr_def isCap_simps)
  apply (fastforce dest: ko_wp_at_norm
                  dest!: ko_wp_at_aligned simp: objBits_simps' projectKOs)
  done

lemma capAligned_tcbI:
  "tcb_at' p s \<Longrightarrow> capAligned (ThreadCap p)"
  apply (clarsimp simp: obj_at'_real_def capAligned_def
                        objBits_simps word_bits_def capUntypedPtr_def isCap_simps)
  apply (fastforce dest: ko_wp_at_norm
                  dest!: ko_wp_at_aligned simp: objBits_simps' projectKOs)
  done

lemma capAligned_reply_tcbI:
  "tcb_at' p s \<Longrightarrow> capAligned (ReplyCap p m r)"
  apply (clarsimp simp: obj_at'_real_def capAligned_def
                        objBits_simps word_bits_def capUntypedPtr_def isCap_simps)
  apply (fastforce dest: ko_wp_at_norm
                  dest!: ko_wp_at_aligned simp: objBits_simps' projectKOs)
  done

lemma ko_at_valid_objs':
  assumes ko: "ko_at' k p s"
  assumes vo: "valid_objs' s"
  assumes k: "\<And>ko. projectKO_opt ko = Some k \<Longrightarrow> injectKO k = ko"
  shows "valid_obj' (injectKO k) s" using ko vo
  by (clarsimp simp: valid_objs'_def obj_at'_def projectKOs
                     project_inject ranI)

lemma obj_at_valid_objs':
  "\<lbrakk> obj_at' P p s; valid_objs' s \<rbrakk> \<Longrightarrow>
  \<exists>k. P k \<and>
      ((\<forall>ko. projectKO_opt ko = Some k \<longrightarrow> injectKO k = ko)
       \<longrightarrow> valid_obj' (injectKO k) s)"
  apply (drule obj_at_ko_at')
  apply clarsimp
  apply (rule_tac x=ko in exI)
  apply clarsimp
  apply (erule (1) ko_at_valid_objs')
  apply simp
  done

lemma tcb_in_valid_state':
  "\<lbrakk> st_tcb_at' P t s; valid_objs' s \<rbrakk> \<Longrightarrow> \<exists>st. P st \<and> valid_tcb_state' st s"
  apply (clarsimp simp: pred_tcb_at'_def)
  apply (drule obj_at_valid_objs')
   apply fastforce
  apply (clarsimp simp: projectKOs)
  apply (fastforce simp add: valid_obj'_def valid_tcb'_def)
  done

lemma getCurThread_corres [corres]: "corres (=) \<top> \<top> (gets cur_thread) getCurThread"
  by (simp add: getCurThread_def curthread_relation)

lemma gct_wp [wp]: "\<lbrace>\<lambda>s. P (ksCurThread s) s\<rbrace> getCurThread \<lbrace>P\<rbrace>"
  by (unfold getCurThread_def, wp)

lemma getIdleThread_corres:
  "corres (=) \<top> \<top> (gets idle_thread) getIdleThread"
  by (simp add: getIdleThread_def state_relation_def)

lemma git_wp [wp]: "\<lbrace>\<lambda>s. P (ksIdleThread s) s\<rbrace> getIdleThread \<lbrace>P\<rbrace>"
  by (unfold getIdleThread_def, wp)

lemma gsa_wp [wp]: "\<lbrace>\<lambda>s. P (ksSchedulerAction s) s\<rbrace> getSchedulerAction \<lbrace>P\<rbrace>"
  by (unfold getSchedulerAction_def, wp)

text \<open>Shorthand names for the relations between faults, errors and failures\<close>

definition
  fr :: "ExceptionTypes_A.fault \<Rightarrow> Fault_H.fault \<Rightarrow> bool"
where
  fr_def[simp]:
 "fr x y \<equiv> (y = fault_map x)"

definition
  ser :: "ExceptionTypes_A.syscall_error \<Rightarrow> Fault_H.syscall_error \<Rightarrow> bool"
where
  ser_def[simp]:
 "ser x y \<equiv> (y = syscall_error_map x)"

definition
  lfr :: "ExceptionTypes_A.lookup_failure \<Rightarrow> Fault_H.lookup_failure \<Rightarrow> bool"
where
  lfr_def[simp]:
 "lfr x y \<equiv> (y = lookup_failure_map x)"

text \<open>Correspondence and weakest precondition
        rules for the "on failure" transformers\<close>

lemma corres_injection:
  assumes x: "t = injection_handler fn"
  assumes y: "t' = injection_handler fn'"
  assumes z: "\<And>ft ft'. f' ft ft' \<Longrightarrow> f (fn ft) (fn' ft')"
  shows      "corres (f' \<oplus> r) P P' m m'
     \<Longrightarrow> corres (f \<oplus> r) P P' (t m) (t' m')"
  apply (simp add: injection_handler_def handleE'_def x y)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply assumption
      apply (case_tac v, (clarsimp simp: z)+)
     apply (rule wp_post_taut)
    apply (rule wp_post_taut)
   apply simp
  apply simp
  done

lemma rethrowFailure_injection:
  "rethrowFailure = injection_handler"
  by (intro ext, simp add: rethrowFailure_def injection_handler_def o_def)

lemma capFault_injection:
 "capFaultOnFailure addr b = injection_handler (Fault_H.CapFault addr b)"
  apply (rule ext)
  apply (simp add: capFaultOnFailure_def rethrowFailure_injection)
  done

lemma lookupError_injection:
 "lookupErrorOnFailure b = injection_handler (Fault_H.FailedLookup b)"
  apply (rule ext)
  apply (simp add: lookupErrorOnFailure_def rethrowFailure_injection)
  done

lemma corres_cap_fault:
  "corres (lfr \<oplus> r) P P' f g \<Longrightarrow>
   corres (fr \<oplus> r) P P' (cap_fault_on_failure addr b f)
                        (capFaultOnFailure addr b g)"
  by (fastforce intro: corres_injection[where f'=lfr]
         simp: cap_fault_injection capFault_injection)

lemmas corresK_cap_fault = corres_cap_fault[atomized, THEN corresK_lift_rule, rule_format, corresK]

lemmas capFault_wp[wp] = injection_wp[OF capFault_injection]
lemmas capFault_wp_E[wp] = injection_wp_E[OF capFault_injection]

lemmas capFault_bindE = injection_bindE[OF capFault_injection capFault_injection]

lemmas capFault_liftE[simp] = injection_liftE[OF capFault_injection]

lemma corres_lookup_error:
  "\<lbrakk> corres (lfr \<oplus> r) P P' f g \<rbrakk>
     \<Longrightarrow> corres (ser \<oplus> r) P P' (lookup_error_on_failure b f) (lookupErrorOnFailure b g)"
  by (fastforce intro: corres_injection[where f'=lfr]
         simp: lookup_error_injection lookupError_injection)

lemmas corresK_lookup_error =
  corres_lookup_error[atomized, THEN corresK_lift_rule, rule_format, corresK]

lemmas lookupError_wp[wp] = injection_wp[OF lookupError_injection]
lemmas lookupError_wp_E[wp] = injection_wp_E[OF lookupError_injection]

lemmas lookupError_bindE = injection_bindE[OF lookupError_injection lookupError_injection]

lemmas lookupError_liftE[simp] = injection_liftE[OF lookupError_injection]


lemma unifyFailure_injection:
  "unifyFailure = injection_handler (\<lambda>x. ())"
  by (rule ext,
      simp add: unifyFailure_def injection_handler_def
                rethrowFailure_def o_def)

lemmas unifyFailure_injection_corres
   = corres_injection [where f=dc, simplified, OF _ unifyFailure_injection]

lemmas unifyFailure_discard
   = unifyFailure_injection_corres [OF id_injection, simplified]

lemmas unifyFailure_wp = injection_wp [OF unifyFailure_injection]

lemmas unifyFailure_wp_E[wp] = injection_wp_E [OF unifyFailure_injection]

lemmas corres_unify_failure =
    corres_injection [OF unify_failure_injection unifyFailure_injection, rotated]

lemma ignoreFailure_wp[wp_split]:
  "\<lbrace>P\<rbrace> v \<lbrace>\<lambda>rv. Q ()\<rbrace>,\<lbrace>\<lambda>rv. Q ()\<rbrace> \<Longrightarrow>
    \<lbrace>P\<rbrace> ignoreFailure v \<lbrace>Q\<rbrace>"
  by (simp add: ignoreFailure_def const_def) wp

lemma ep'_cases_weak_wp:
  assumes "\<lbrace>P_A\<rbrace> a \<lbrace>Q\<rbrace>"
  assumes "\<And>q. \<lbrace>P_B\<rbrace> b q \<lbrace>Q\<rbrace>"
  assumes "\<And>q. \<lbrace>P_C\<rbrace> c q \<lbrace>Q\<rbrace>"
  shows
  "\<lbrace>P_A and P_B and P_C\<rbrace>
    case ts of
      IdleEP \<Rightarrow> a
    | SendEP q \<Rightarrow> b q
    | RecvEP q \<Rightarrow> c q \<lbrace>Q\<rbrace>"
  apply (cases ts)
  apply (simp, rule hoare_weaken_pre, rule assms, simp)+
  done

lemma ntfn'_cases_weak_wp:
  assumes "\<lbrace>P_A\<rbrace> a \<lbrace>Q\<rbrace>"
  assumes "\<And>q. \<lbrace>P_B\<rbrace> b q \<lbrace>Q\<rbrace>"
  assumes "\<And>bdg. \<lbrace>P_C\<rbrace> c bdg \<lbrace>Q\<rbrace>"
  shows
  "\<lbrace>P_A and P_B and P_C\<rbrace>
    case ts of
      IdleNtfn \<Rightarrow> a
    | WaitingNtfn q \<Rightarrow> b q
    | ActiveNtfn bdg \<Rightarrow> c bdg \<lbrace>Q\<rbrace>"
  apply (cases ts)
  apply (simp, rule hoare_weaken_pre, rule assms, simp)+
  done

lemma ko_at_imp_cte_wp_at':
  fixes x :: cte
  shows "\<lbrakk> ko_at' x ptr s \<rbrakk> \<Longrightarrow> cte_wp_at' (\<lambda>cte. cte = x) ptr s"
  apply (erule obj_atE')
  apply (clarsimp simp: projectKOs objBits_simps')
  apply (erule cte_wp_at_cteI')
    apply (simp add: cte_level_bits_def)+
  done

lemma modify_map_casesD:
  "modify_map m p f p' = Some cte \<Longrightarrow>
  (p \<noteq> p' \<longrightarrow> m p' = Some cte) \<and>
  (p = p' \<longrightarrow> (\<exists>cap node. m p = Some (CTE cap node) \<and> f (CTE cap node) = cte))"
  apply (simp add: modify_map_def split: if_split_asm)
  apply clarsimp
  apply (case_tac z)
  apply auto
  done

lemma modify_map_casesE:
  "\<lbrakk> modify_map m p f p' = Some cte;
     \<lbrakk> p \<noteq> p'; m p' = Some cte \<rbrakk> \<Longrightarrow> P;
     \<And>cap node. \<lbrakk> p = p'; m p = Some (CTE cap node); cte = f (CTE cap node) \<rbrakk> \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P"
  by (auto dest: modify_map_casesD)


lemma modify_map_cases:
  "(modify_map m p f p' = Some cte) =
  ((p \<noteq> p' \<longrightarrow> m p' = Some cte) \<and>
   (p = p' \<longrightarrow> (\<exists>cap node. m p = Some (CTE cap node) \<and> f (CTE cap node) = cte)))"
  apply (rule iffI)
   apply (erule modify_map_casesD)
  apply (clarsimp simp: modify_map_def)
  done


lemma no_0_modify_map [simp]:
  "no_0 (modify_map m p f) = no_0 m"
  by (simp add: no_0_def modify_map_def)


lemma modify_map_0 [simp]:
  "no_0 m \<Longrightarrow> modify_map m 0 f = m"
  by (rule ext) (auto simp add: modify_map_def no_0_def)


lemma modify_map_exists:
  "\<exists>cap node. m p = Some (CTE cap node) \<Longrightarrow> \<exists>cap' node'. modify_map m q f p = Some (CTE cap' node')"
  apply clarsimp
  apply (case_tac "f (CTE cap node)")
  apply (cases "q=p")
   apply (auto simp add: modify_map_cases)
  done


lemma modify_map_exists_rev:
  "modify_map m q f p = Some (CTE cap node) \<Longrightarrow> \<exists>cap' node'. m p = Some (CTE cap' node')"
  apply (case_tac "f (CTE cap node)")
  apply (cases "q=p")
   apply (auto simp add: modify_map_cases)
  done


lemma modify_map_if:
  "(modify_map m p f p' = Some cte) =
   (if p = p'
    then \<exists>cap node. m p = Some (CTE cap node) \<and> f (CTE cap node) = cte
    else \<exists>cap node. m p' = Some (CTE cap node) \<and> cte = CTE cap node)"
  apply (cases cte)
  apply (rule iffI)
   apply (drule modify_map_casesD)
   apply auto[1]
  apply (auto simp: modify_map_def)
  done

lemma corres_empty_on_failure:
  "corres ((\<lambda>x y. r [] []) \<oplus> r) P P' m m' \<Longrightarrow>
   corres r P P' (empty_on_failure m) (emptyOnFailure m')"
  apply (simp add: empty_on_failure_def emptyOnFailure_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch)
       apply assumption
      apply (rule corres_trivial, simp)
     apply wp+
   apply simp+
  done

lemmas corresK_empty_on_failure =
  corres_empty_on_failure[atomized, THEN corresK_lift_rule, rule_format, corresK]

lemma emptyOnFailure_wp[wp]:
  "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv. Q []\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> emptyOnFailure m \<lbrace>Q\<rbrace>"
  by (simp add: emptyOnFailure_def) wp

lemma withoutPreemption_lift:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> withoutPreemption f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  by simp

lemma withoutPreemption_R:
  "\<lbrace>\<top>\<rbrace> withoutPreemption f -, \<lbrace>Q\<rbrace>"
  by (wp withoutPreemption_lift)

lemma ko_at_cte_ipcbuffer:
  "ko_at' tcb p s \<Longrightarrow> cte_wp_at' (\<lambda>x. x = tcbIPCBufferFrame tcb) (p + tcbIPCBufferSlot * 0x10) s"
  apply (clarsimp simp: obj_at'_def projectKOs objBits_simps)
  apply (erule (2) cte_wp_at_tcbI')
   apply (fastforce simp add: tcb_cte_cases_def tcbIPCBufferSlot_def cteSizeBits_def)
  apply simp
  done

lemma set_ep_arch':  "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setEndpoint ntfn p \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  apply (simp add: setEndpoint_def setObject_def split_def)
  apply (wp updateObject_default_inv|simp)+
  done

lemma corres_const_on_failure:
  "corres ((\<lambda>_ _. r x y) \<oplus> r) P P' m m' \<Longrightarrow>
   corres r P P' (const_on_failure x m) (constOnFailure y m')"
  apply (simp add: const_on_failure_def constOnFailure_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch)
       apply assumption
      apply (rule corres_trivial, simp)
      apply (clarsimp simp: const_def)
     apply wp+
   apply simp+
  done

lemmas corresK_const_on_failure =
  corres_const_on_failure[atomized, THEN corresK_lift_rule, rule_format, corresK]

lemma constOnFailure_wp :
  "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>, \<lbrace>\<lambda>rv. Q n\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> constOnFailure n m \<lbrace>Q\<rbrace>"
  apply (simp add: constOnFailure_def const_def)
  apply (wp|simp)+
  done

lemma corres_throwError_str [corresK_concrete_rER]:
  "corres_underlyingK sr nf nf' (r (Inl a) (Inl b)) r \<top> \<top> (throwError a) (throw b)"
  "corres_underlyingK sr nf nf' (r (Inl a) (Inl b)) r \<top> \<top> (throwError a) (throwError b)"
 by (simp add: corres_underlyingK_def)+

end
end
