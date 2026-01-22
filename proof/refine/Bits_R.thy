(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Bits_R
imports Corres ArchStateRelationLemmas
begin

(* FIXME: clearMemory generates a warning on some architectures *)
crunch_ignore (add:
  withoutFailure throw catchFailure rethrowFailure capFaultOnFailure lookupErrorOnFailure
  nullCapOnFailure nothingOnFailure withoutPreemption preemptionPoint ignoreFailure
  emptyOnFailure unifyFailure maskInterrupt clearMemory clearMemoryVM  assertDerived
  setObject getObject updateObject loadObject
  ifM andM orM whenM whileM haskell_assert) (*FIXME arch-split RT: can these be removed?*)

lemma throwE_R: "\<lbrace>\<top>\<rbrace> throw f \<lbrace>P\<rbrace>,-"
  by (simp add: validE_R_def) wp

lemma withoutFailure_wp [wp]:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> withoutFailure f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> withoutFailure f \<lbrace>Q\<rbrace>,-"
  "\<lbrace>\<top>\<rbrace> withoutFailure f -,\<lbrace>E\<rbrace>"
  by (auto simp: validE_R_def validE_E_def valid_def)

(* no_fail_False is in simpset, but unsafe for wp *)
lemma no_fail_typeError[wp]:
  "no_fail \<bottom> (typeError xs ko)"
  by (rule no_fail_False)

lemma gen_isCap_simps:
  "isZombie v = (\<exists>v0 v1 v2. v = Zombie v0 v1 v2)"
  "isArchObjectCap v = (\<exists>v0. v = ArchObjectCap v0)"
  "isThreadCap v = (\<exists>v0. v = ThreadCap v0)"
  "isCNodeCap v = (\<exists>v0 v1 v2 v3. v = CNodeCap v0 v1 v2 v3)"
  "isNotificationCap v = (\<exists>v0 v1 v2 v3. v = NotificationCap v0 v1 v2 v3)"
  "isEndpointCap v = (\<exists>v0 v1 v2 v3 v4 v5. v = EndpointCap v0 v1 v2 v3 v4 v5)"
  "isUntypedCap v = (\<exists>d v0 v1 f. v = UntypedCap d v0 v1 f)"
  "isReplyCap v = (\<exists>v0 v1. v = ReplyCap v0 v1)"
  "isSchedContextCap v = (\<exists>v0 v1. v = SchedContextCap v0 v1)"
  "isSchedControlCap v = (v = SchedControlCap)"
  "isIRQControlCap v = (v = IRQControlCap)"
  "isIRQHandlerCap v = (\<exists>v0. v = IRQHandlerCap v0)"
  "isNullCap v = (v = NullCap)"
  "isDomainCap v = (v = DomainCap)"
  by (auto simp: gen_isCap_defs split: capability.splits)

lemmas isUntypedCap_simps[simp] = isUntypedCap_def[split_simps capability.split]

text \<open>Miscellaneous facts about low level constructs\<close>

locale Bits_R =
  assumes atcbContext_get_eq[simp]:
    "\<And>uc atcb. atcbContextGet (atcbContextSet uc atcb) = uc"
  assumes atcbContext_set_eq[simp]:
    "\<And>t. atcbContextSet (atcbContextGet t) t = t"
  assumes atcbContext_set_set[simp]:
    "\<And>uc uc' atcb. atcbContextSet uc (atcbContextSet uc' atcb) = atcbContextSet uc atcb"
  assumes objBitsKO_neq_0:
    "\<And>ko. objBitsKO ko \<noteq> 0"
  assumes pageBits_le_maxUntypedSizeBits[simp]:
    "pageBits \<le> maxUntypedSizeBits"

context Bits_R begin

lemma scBits_pos_power2:
  assumes "minSchedContextBits + scSize sc < word_bits"
  shows "(1::machine_word) < (2::machine_word) ^ (minSchedContextBits + scSize sc)"
  apply (insert assms)
  apply (subst word_less_nat_alt)
  apply (clarsimp simp: minSchedContextBits_def)
  by (auto simp: pow_mono_leq_imp_lt)

lemma objBitsKO_pos_power2[simp, intro!]:
  assumes "objBitsKO ko < word_bits"
  shows "(1::machine_word) < 2 ^ objBitsKO ko"
  using objBitsKO_neq_0
  by (simp add: assms word_2p_lem word_bits_size)

lemma objBits_pos_power2[simp]:
  assumes "objBits v < word_bits"
  shows "(1::machine_word) < 2 ^ objBits v"
  using assms
  unfolding objBits_def by simp

end

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

lemma projectKO_reply:
  "(projectKO_opt ko = Some t) = (ko = KOReply t)"
  by (cases ko) (auto simp: projectKO_opts_defs)

lemma reply_of'_KOReply[simp]:
  "reply_of' (KOReply reply) = Some reply"
  apply (clarsimp simp: projectKO_reply)
  done

lemma projectKO_sc:
  "(projectKO_opt ko = Some t) = (ko = KOSchedContext t)"
  by (cases ko) (auto simp: projectKO_opts_defs)

lemma sc_of'_Sched[simp]:
  "sc_of' (KOSchedContext sc) = Some sc"
  by (simp add: projectKO_sc)

lemmas gen_projectKOs[simp] =
  projectKO_ntfn projectKO_ep projectKO_cte projectKO_tcb projectKO_reply projectKO_sc
  projectKO_eq

(* same derivation on all architectures, since all objects fit inside address space *)
lemma (in Arch) obj_sizeBits_less_word_bits:
  "epSizeBits < word_bits"
  "ntfnSizeBits < word_bits"
  "tcbBlockSizeBits < word_bits"
  "cteSizeBits < word_bits"
  "replySizeBits < word_bits"
  by (simp_all add: objBits_defs word_bits_def)

requalify_facts Arch.obj_sizeBits_less_word_bits

lemma tcbBlockSizeBits_tcb_bits:
  "tcbBlockSizeBits = tcb_bits"
  by (simp add: tcbBlockSizeBits_def)

(* true on all arches *)
lemma zero_less_tcbBlockSizeBits[simp]:
  "0 < tcbBlockSizeBits"
  unfolding tcbBlockSizeBits_def by simp

(* same derivation on all architectures; some duplication for convenience in simpset *)
lemma (in Arch) tcb_slots_less_2p_tcbBlockSizeBits:
  "0 < (2::machine_word) ^ tcbBlockSizeBits"
  "1 < (2::machine_word) ^ tcbBlockSizeBits"
  "1 << cteSizeBits < (2::machine_word) ^ tcbBlockSizeBits"
  "2 << cteSizeBits < (2::machine_word) ^ tcbBlockSizeBits"
  "3 << cteSizeBits < (2::machine_word) ^ tcbBlockSizeBits"
  "4 << cteSizeBits < (2::machine_word) ^ tcbBlockSizeBits"
  "(2::machine_word) ^ cteSizeBits < 2 ^ tcbBlockSizeBits"
  unfolding tcbBlockSizeBits_def by (auto simp: objBits_simps')

requalify_facts Arch.tcb_slots_less_2p_tcbBlockSizeBits
declare tcb_slots_less_2p_tcbBlockSizeBits[simp]

(* variant for ASpec-equivalents *)
lemmas tcb_slots_less_2p_tcb_bits[simp] =
  tcb_slots_less_2p_tcbBlockSizeBits[simplified tcbBlockSizeBits_tcb_bits cteSizeBits_cte_level_bits]

(* same derivation on all architectures *)
lemma (in Arch) zero_one_less_2p_SizeBits[simp]:
  "(0::machine_word) < 2 ^ cteSizeBits"
  "(1::machine_word) < 2 ^ cteSizeBits"
  "(0::machine_word) < 2 ^ epSizeBits"
  "(1::machine_word) < 2 ^ epSizeBits"
  "(0::machine_word) < 2 ^ ntfnSizeBits"
  "(1::machine_word) < 2 ^ ntfnSizeBits"
  by (auto simp: objBits_simps')

requalify_facts Arch.zero_one_less_2p_SizeBits
declare zero_one_less_2p_SizeBits[simp]

lemma capAligned_epI:
  "ep_at' p s \<Longrightarrow> capAligned (EndpointCap p a b c d e)"
  apply (clarsimp simp: obj_at'_real_def capAligned_def PPtr_def
                        gen_objBits_simps capUntypedPtr_def gen_isCap_simps)
  apply (fastforce dest: ko_wp_at_norm
                   dest!: ko_wp_at_aligned
                   simp: gen_objBits_simps obj_sizeBits_less_word_bits)
  done

lemma capAligned_ntfnI:
  "ntfn_at' p s \<Longrightarrow> capAligned (NotificationCap p a b c)"
  apply (clarsimp simp: obj_at'_real_def capAligned_def PPtr_def
                        gen_objBits_simps capUntypedPtr_def gen_isCap_simps)
  apply (fastforce dest: ko_wp_at_norm
                   dest!: ko_wp_at_aligned
                   simp: gen_objBits_simps obj_sizeBits_less_word_bits)
  done

lemma capAligned_tcbI:
  "tcb_at' p s \<Longrightarrow> capAligned (ThreadCap p)"
  apply (clarsimp simp: obj_at'_real_def capAligned_def PPtr_def
                        gen_objBits_simps capUntypedPtr_def gen_isCap_simps)
  apply (fastforce dest: ko_wp_at_norm
                   dest!: ko_wp_at_aligned
                   simp: gen_objBits_simps obj_sizeBits_less_word_bits)
  done

lemma capAligned_replyI:
  "reply_at' p s \<Longrightarrow> capAligned (ReplyCap p r)"
  apply (clarsimp simp: obj_at'_real_def capAligned_def PPtr_def
                        gen_objBits_simps capUntypedPtr_def gen_isCap_simps)
  apply (fastforce dest: ko_wp_at_norm
                   dest!: ko_wp_at_aligned
                   simp: gen_objBits_simps obj_sizeBits_less_word_bits)
  done

lemma capAligned_sched_contextI:
  "\<lbrakk>sc_at'_n r p s; sc_size_bounds r\<rbrakk> \<Longrightarrow> capAligned (SchedContextCap p r)"
  by (clarsimp simp: obj_at'_real_def capAligned_def PPtr_def sc_size_bounds_def ko_wp_at'_def gen_isCap_simps
                     gen_objBits_simps word_bits_def capUntypedPtr_def RISCV64_H.maxUntypedSizeBits_def) (* FIXME arch-split RT *)

lemma sc_at'_n_sc_at':
  "sc_at'_n n p s \<Longrightarrow> sc_at' p s"
  apply (clarsimp simp: ko_wp_at'_def obj_at'_def)
  by (case_tac ko; clarsimp)

lemma ko_at_valid_objs':
  assumes ko: "ko_at' k p s"
  assumes vo: "valid_objs' s"
  assumes k: "\<And>ko. projectKO_opt ko = Some k \<Longrightarrow> injectKO k = ko"
  shows "valid_obj' (injectKO k) s" using ko vo
  by (clarsimp simp: valid_objs'_def obj_at'_def project_inject ranI)

lemmas ko_at_valid_objs'_pre =
  ko_at_valid_objs'[simplified project_inject, atomized, simplified, rule_format]

lemmas ep_ko_at_valid_objs_valid_ep' =
  ko_at_valid_objs'_pre[where 'a=endpoint, simplified injectKO_defs valid_obj'_def, simplified]

lemmas ntfn_ko_at_valid_objs_valid_ntfn' =
  ko_at_valid_objs'_pre[where 'a=notification, simplified injectKO_defs valid_obj'_def,
                        simplified]

lemmas tcb_ko_at_valid_objs_valid_tcb' =
  ko_at_valid_objs'_pre[where 'a=tcb, simplified injectKO_defs valid_obj'_def, simplified]

lemmas cte_ko_at_valid_objs_valid_cte' =
  ko_at_valid_objs'_pre[where 'a=cte, simplified injectKO_defs valid_obj'_def, simplified]

lemmas sc_ko_at_valid_objs_valid_sc' =
  ko_at_valid_objs'_pre[where 'a=sched_context, simplified injectKO_defs valid_obj'_def,
                        simplified]

lemmas reply_ko_at_valid_objs_valid_reply' =
  ko_at_valid_objs'_pre[where 'a=reply, simplified injectKO_defs valid_obj'_def, simplified]

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
  apply (fastforce simp add: valid_obj'_def valid_tcb'_def)
  done

lemma getCurThread_corres[corres]:
  "corres (=) \<top> \<top> (gets cur_thread) getCurThread"
  by (simp add: getCurThread_def curthread_relation)

lemma gct_wp [wp]: "\<lbrace>\<lambda>s. P (ksCurThread s) s\<rbrace> getCurThread \<lbrace>P\<rbrace>"
  by (unfold getCurThread_def, wp)

lemma getIdleThread_corres[corres]:
  "corres (=) \<top> \<top> (gets idle_thread) getIdleThread"
  by (simp add: getIdleThread_def state_relation_def)

lemma git_wp [wp]: "\<lbrace>\<lambda>s. P (ksIdleThread s) s\<rbrace> getIdleThread \<lbrace>P\<rbrace>"
  by (unfold getIdleThread_def, wp)

lemma getIdleSc_wp [wp]: "\<lbrace>\<lambda>s. P (ksIdleSC s) s\<rbrace> getIdleSC \<lbrace>P\<rbrace>"
  by (unfold getIdleSC_def, wp)

lemma gsa_wp [wp]: "\<lbrace>\<lambda>s. P (ksSchedulerAction s) s\<rbrace> getSchedulerAction \<lbrace>P\<rbrace>"
  by (unfold getSchedulerAction_def, wp)

lemma is_ep_cap_relation:
  "cap_relation c c' \<Longrightarrow> isEndpointCap c' = is_ep_cap c"
  by (simp add: gen_isCap_simps is_cap_simps)
     (cases c, auto)

lemma is_ntfn_cap_relation:
  "cap_relation c c' \<Longrightarrow> isNotificationCap c' = is_ntfn_cap c"
  by (simp add: gen_isCap_simps is_cap_simps)
     (cases c, auto)

text \<open>Shorthand names for the relations between faults, errors and failures\<close>

definition fr :: "ExceptionTypes_A.fault \<Rightarrow> Fault_H.fault \<Rightarrow> bool" where
  fr_def[simp]:
  "fr x y \<equiv> (y = fault_map x)"

definition ser :: "ExceptionTypes_A.syscall_error \<Rightarrow> Fault_H.syscall_error \<Rightarrow> bool" where
  ser_def[simp]:
  "ser x y \<equiv> (y = syscall_error_map x)"

definition lfr :: "ExceptionTypes_A.lookup_failure \<Rightarrow> Fault_H.lookup_failure \<Rightarrow> bool" where
  lfr_def[simp]:
  "lfr x y \<equiv> (y = lookup_failure_map x)"

text \<open>Correspondence and weakest precondition rules for the "on failure" transformers\<close>

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
  apply (clarsimp simp: gen_objBits_simps cteSizeBits_cte_level_bits)
  apply (erule cte_wp_at_cteI'; simp)
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
  "ko_at' tcb p s
   \<Longrightarrow> cte_wp_at' (\<lambda>x. x = tcbIPCBufferFrame tcb) (p + (tcbIPCBufferSlot << cteSizeBits)) s"
  by (fastforce elim!: cte_wp_at_tcbI' simp: obj_at'_def gen_objBits_simps tcbIPCBufferSlot_def)

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

lemma constOnFailure_wp :
  "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>, \<lbrace>\<lambda>rv. Q n\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> constOnFailure n m \<lbrace>Q\<rbrace>"
  apply (simp add: constOnFailure_def const_def)
  apply (wp|simp)+
  done

end
