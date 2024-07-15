(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Contains proofs that fastpath + callKernel is semantically identical to
   callKernel. *)

theory Fastpath_Equiv
imports Fastpath_Defs IsolatedThreadAction Refine.RAB_FN
begin

lemma setCTE_obj_at'_queued:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbQueued tcb)) t\<rbrace> setCTE p v \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P (tcbQueued tcb)) t\<rbrace>"
  unfolding setCTE_def
  by (rule setObject_cte_obj_at_tcb', simp+)

crunch cteInsert
  for obj_at'_queued: "obj_at' (\<lambda>tcb. P (tcbQueued tcb)) t"
  (wp: setCTE_obj_at'_queued crunch_wps)

crunch emptySlot
  for obj_at'_not_queued: "obj_at' (\<lambda>a. \<not> tcbQueued a) p"
  (wp: setCTE_obj_at'_queued)

lemma getEndpoint_obj_at':
  "\<lbrace>obj_at' P ptr\<rbrace> getEndpoint ptr \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (wp getEndpoint_wp)
  apply (clarsimp simp: obj_at'_def projectKOs)
  done

lemmas setEndpoint_obj_at_tcb' = setEndpoint_obj_at'_tcb

crunch tcbSchedEnqueue
  for tcbContext[wp]: "obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t"
  (simp: tcbQueuePrepend_def)

lemma setCTE_tcbContext:
  "\<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>
   setCTE slot cte
   \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>"
  apply (simp add: setCTE_def)
  apply (rule setObject_cte_obj_at_tcb', simp_all)
  done

context begin interpretation Arch . (*FIXME: arch_split*)

lemma setThreadState_tcbContext:
 "setThreadState st tptr \<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>"
  unfolding setThreadState_def rescheduleRequired_def
  apply (wpsimp wp: threadSet_wp hoare_drop_imps)
  apply (fastforce simp: obj_at'_def objBits_simps projectKOs  atcbContext_def ps_clear_upd)
  done

lemma setBoundNotification_tcbContext:
 "setBoundNotification ntfnPtr tptr \<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>"
  unfolding setBoundNotification_def
  apply (wpsimp wp: threadSet_wp hoare_drop_imps)
  apply (fastforce simp: obj_at'_def objBits_simps projectKOs)
  done

declare comp_apply [simp del]
crunch deleteCallerCap
  for tcbContext[wp]: "obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t"
  (wp: setEndpoint_obj_at_tcb' setBoundNotification_tcbContext
       setNotification_tcb crunch_wps setThreadState_tcbContext
   simp: crunch_simps unless_def)
declare comp_apply [simp]


crunch asUser
  for ksArch[wp]: "\<lambda>s. P (ksArchState s)"
  (wp: crunch_wps)

definition
   tcbs_of :: "kernel_state => word32 => tcb option"
where
  "tcbs_of s = (%x. if tcb_at' x s then projectKO_opt (the (ksPSpace s x)) else None)"

lemma obj_at_tcbs_of:
  "obj_at' P t s = (EX tcb. tcbs_of s t = Some tcb & P tcb)"
  apply (simp add: tcbs_of_def split: if_split)
  apply (intro conjI impI)
   apply (clarsimp simp: obj_at'_def projectKOs)
  apply (clarsimp simp: obj_at'_weakenE[OF _ TrueI])
  done

lemma st_tcb_at_tcbs_of:
  "st_tcb_at' P t s = (EX tcb. tcbs_of s t = Some tcb & P (tcbState tcb))"
  by (simp add: st_tcb_at'_def obj_at_tcbs_of)

lemma tcbs_of_ko_at':
  "\<lbrakk> tcbs_of s p = Some tcb \<rbrakk> \<Longrightarrow> ko_at' tcb p s"
  by (simp add: obj_at_tcbs_of)

lemma tcbs_of_valid_tcb':
  "\<lbrakk> valid_objs' s; tcbs_of s p = Some tcb \<rbrakk> \<Longrightarrow> valid_tcb' tcb s"
  by (frule tcbs_of_ko_at')
     (drule (1) ko_at_valid_objs', auto simp: projectKOs valid_obj'_def)

lemma acc_CNodeCap_repr:
  "isCNodeCap cap
     \<Longrightarrow> cap = CNodeCap (capCNodePtr cap) (capCNodeBits cap)
                        (capCNodeGuard cap) (capCNodeGuardSize cap)"
  by (clarsimp simp: isCap_simps)

lemma valid_cnode_cap_cte_at':
  "\<lbrakk> s \<turnstile>' c; isCNodeCap c; ptr = capCNodePtr c; v < 2 ^ capCNodeBits c \<rbrakk>
      \<Longrightarrow> cte_at' (ptr + v * 2^cteSizeBits) s"
  apply (drule less_mask_eq)
  apply (drule(1) valid_cap_cte_at'[where addr=v])
  apply (simp add: mult.commute mult.left_commute)
  done

lemmas valid_cnode_cap_cte_at''
  = valid_cnode_cap_cte_at'[simplified objBits_defs, simplified]

declare of_int_sint_scast[simp]

lemma of_bl_from_bool:
  "of_bl [x] = from_bool x"
  by (cases x, simp_all add: from_bool_def)

lemma dmo_clearExMonitor_setCurThread_swap:
  "(do _ \<leftarrow> doMachineOp ARM_HYP.clearExMonitor;
       setCurThread thread
    od)
    = (do _ \<leftarrow> setCurThread thread;
          doMachineOp ARM_HYP.clearExMonitor
       od)"
  apply (clarsimp simp: ARM_HYP.clearExMonitor_def)
  apply (simp add: doMachineOp_modify)
  apply (rule oblivious_modify_swap)
  apply (fastforce intro: oblivious_bind simp: setCurThread_def idleThreadNotQueued_def)
  done

lemma pd_at_asid_inj':
  "pd_at_asid' pd asid s \<Longrightarrow> pd_at_asid' pd' asid s \<Longrightarrow> pd' = pd"
  by (clarsimp simp: pd_at_asid'_def obj_at'_def)

lemma bind_case_sum_rethrow:
  "rethrowFailure fl f >>= case_sum e g
     = f >>= case_sum (e \<circ> fl) g"
  apply (simp add: rethrowFailure_def handleE'_def
                   bind_assoc)
  apply (rule bind_cong[OF refl])
  apply (simp add: throwError_bind split: sum.split)
  done

declare empty_fail_assertE[iff]

declare empty_fail_resolveAddressBits[iff]

lemma lookupExtraCaps_null:
  "msgExtraCaps info = 0 \<Longrightarrow>
     lookupExtraCaps thread buffer info = returnOk []"
  by (clarsimp simp: lookupExtraCaps_def
                     getExtraCPtrs_def liftE_bindE
                     upto_enum_step_def mapM_Nil
              split: Types_H.message_info.split option.split)

lemma isRecvEP_endpoint_case:
  "isRecvEP ep \<Longrightarrow> case_endpoint f g h ep = f (epQueue ep)"
  by (clarsimp simp: isRecvEP_def split: endpoint.split_asm)

lemma unifyFailure_catch_If:
  "catch (unifyFailure f >>=E g) h
     = f >>= (\<lambda>rv. if isRight rv then catch (g (theRight rv)) h else h ())"
  apply (simp add: unifyFailure_def rethrowFailure_def
                   handleE'_def catch_def bind_assoc
                   bind_bindE_assoc cong: if_cong)
  apply (rule bind_cong[OF refl])
  apply (simp add: throwError_bind isRight_def return_returnOk
            split: sum.split)
  done

lemma st_tcb_at_not_in_ep_queue:
  "\<lbrakk> st_tcb_at' P t s; ko_at' ep epptr s; sym_refs (state_refs_of' s);
     ep \<noteq> IdleEP; \<And>ts. P ts \<Longrightarrow> tcb_st_refs_of' ts = {} \<rbrakk>
      \<Longrightarrow> t \<notin> set (epQueue ep)"
  apply clarsimp
  apply (drule(1) sym_refs_ko_atD')
  apply (cases ep, simp_all add: st_tcb_at_refs_of_rev')
   apply (fastforce simp: st_tcb_at'_def obj_at'_def projectKOs)+
  done

lemma st_tcb_at_not_in_ntfn_queue:
  "\<lbrakk> st_tcb_at' P t s; ko_at' ntfn ntfnptr s; sym_refs (state_refs_of' s); ntfnObj ntfn = WaitingNtfn xs;
     \<And>ts. P ts \<Longrightarrow> (ntfnptr, TCBSignal) \<notin> tcb_st_refs_of' ts \<rbrakk>
      \<Longrightarrow> t \<notin> set xs"
  apply (drule(1) sym_refs_ko_atD')
  apply (clarsimp simp: st_tcb_at_refs_of_rev')
  apply (drule_tac x="(t, NTFNSignal)" in bspec, simp)
  apply (fastforce simp: st_tcb_at'_def obj_at'_def projectKOs ko_wp_at'_def tcb_bound_refs'_def)
  done

lemma sym_refs_upd_sD:
  "\<lbrakk> sym_refs ((state_refs_of' s) (p := S)); valid_pspace' s;
            ko_at' ko p s; refs_of' (injectKO koEx) = S;
            objBits koEx = objBits ko \<rbrakk>
      \<Longrightarrow> \<exists>s'. sym_refs (state_refs_of' s')
               \<and> (\<forall>p' (ko' :: endpoint). ko_at' ko' p' s \<and> injectKO ko' \<noteq> injectKO ko
                          \<longrightarrow> ko_at' ko' p' s')
               \<and> (\<forall>p' (ko' :: Structures_H.notification). ko_at' ko' p' s \<and> injectKO ko' \<noteq> injectKO ko
                          \<longrightarrow> ko_at' ko' p' s')
               \<and> (ko_at' koEx p s')"
  apply (rule exI, rule conjI)
   apply (rule state_refs_of'_upd[where ko'="injectKO koEx" and ptr=p and s=s,
                                  THEN ssubst[where P=sym_refs], rotated 2])
     apply simp+
   apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
   apply (clarsimp simp: project_inject objBits_def)
  apply (clarsimp simp: obj_at'_def ps_clear_upd projectKOs
                 split: if_split)
  apply (clarsimp simp: project_inject objBits_def)
  apply auto
  done

lemma sym_refs_upd_tcb_sD:
  "\<lbrakk> sym_refs ((state_refs_of' s) (p := {r \<in> state_refs_of' s p. snd r = TCBBound})); valid_pspace' s;
            ko_at' (tcb :: tcb) p s \<rbrakk>
      \<Longrightarrow> \<exists>s'. sym_refs (state_refs_of' s')
               \<and> (\<forall>p' (ko' :: endpoint).
                          ko_at' ko' p' s \<longrightarrow> ko_at' ko' p' s')
               \<and> (\<forall>p' (ko' :: Structures_H.notification).
                          ko_at' ko' p' s \<longrightarrow> ko_at' ko' p' s')
               \<and> (st_tcb_at' ((=) Running) p s')"
  apply (drule(2) sym_refs_upd_sD[where koEx="makeObject\<lparr>tcbState := Running, tcbBoundNotification := tcbBoundNotification tcb\<rparr>"])
    apply (clarsimp dest!: ko_at_state_refs_ofD')
   apply (simp add: objBits_simps)
  apply (erule exEI)
  apply clarsimp
  apply (auto simp: st_tcb_at'_def elim!: obj_at'_weakenE)
  done

lemma updateCap_cte_wp_at_cteMDBNode:
  "\<lbrace>cte_wp_at' (\<lambda>cte. P (cteMDBNode cte)) p\<rbrace>
     updateCap ptr cap
   \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>cte. P (cteMDBNode cte)) p\<rbrace>"
  apply (wp updateCap_cte_wp_at_cases)
  apply (simp add: o_def)
  done

lemma ctes_of_Some_cte_wp_at:
  "ctes_of s p = Some cte \<Longrightarrow> cte_wp_at' P p s = P cte"
  by (clarsimp simp: cte_wp_at_ctes_of)

lemma user_getreg_wp:
  "\<lbrace>\<lambda>s. tcb_at' t s \<and> (\<forall>rv. obj_at' (\<lambda>tcb. (user_regs o atcbContextGet o tcbArch) tcb r = rv) t s \<longrightarrow> Q rv s)\<rbrace>
      asUser t (getRegister r) \<lbrace>Q\<rbrace>"
  apply (rule_tac Q'="\<lambda>rv s. \<exists>rv'. rv' = rv \<and> Q rv' s" in hoare_post_imp)
   apply simp
  apply (rule hoare_pre, wp hoare_vcg_ex_lift user_getreg_rv)
  apply (clarsimp simp: obj_at'_def)
  done

lemma setUntypedCapAsFull_replyCap[simp]:
  "setUntypedCapAsFull cap (ReplyCap curThread False cg) slot =  return ()"
   by (clarsimp simp:setUntypedCapAsFull_def isCap_simps)

lemma option_case_liftM_getNotification_wp:
  "\<lbrace>\<lambda>s. \<forall>rv. (case x of None \<Rightarrow> rv = v | Some p \<Rightarrow> obj_at' (\<lambda>ntfn. f ntfn = rv) p s)
    \<longrightarrow> Q rv s\<rbrace> case x of None \<Rightarrow> return v | Some ptr \<Rightarrow> liftM f $ getNotification ptr \<lbrace> Q \<rbrace>"
  apply (rule hoare_pre, (wpc; wp getNotification_wp))
  apply (auto simp: obj_at'_def)
  done

lemma threadSet_st_tcb_at_state:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> (if p = t
        then obj_at' (\<lambda>tcb. P (tcbState (f tcb))) t s
        else st_tcb_at' P p s)\<rbrace>
  threadSet f t \<lbrace>\<lambda>_. st_tcb_at' P p\<rbrace>"
  apply (rule hoare_chain)
    apply (rule threadSet_obj_at'_really_strongest)
   prefer 2
   apply (simp add: st_tcb_at'_def)
  apply (clarsimp split: if_splits simp: st_tcb_at'_def o_def)
  done

lemma recv_ep_queued_st_tcb_at':
  "\<lbrakk> ko_at' (Structures_H.endpoint.RecvEP ts) epptr s ;
     t \<in> set ts;
     sym_refs (state_refs_of' s) \<rbrakk>
   \<Longrightarrow> st_tcb_at' isBlockedOnReceive t s"
  apply (drule obj_at_ko_at')
  apply clarsimp
  apply (drule (1) sym_refs_ko_atD')
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_real_def refs_of_rev')
  apply (erule_tac x=t in ballE; clarsimp?)
  apply (erule ko_wp_at'_weakenE)
  apply (clarsimp simp: isBlockedOnReceive_def projectKOs)
  done

lemma valid_ep_typ_at_lift':
  "\<lbrakk> \<And>p. \<lbrace>typ_at' TCBT p\<rbrace> f \<lbrace>\<lambda>rv. typ_at' TCBT p\<rbrace> \<rbrakk>
      \<Longrightarrow> \<lbrace>\<lambda>s. valid_ep' ep s\<rbrace> f \<lbrace>\<lambda>rv s. valid_ep' ep s\<rbrace>"
  apply (cases ep, simp_all add: valid_ep'_def)
   apply (wp hoare_vcg_const_Ball_lift typ_at_lifts | assumption)+
  done

lemma threadSet_tcbState_valid_objs:
  "\<lbrace>valid_tcb_state' st and valid_objs'\<rbrace>
     threadSet (tcbState_update (\<lambda>_. st)) t
   \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (wp threadSet_valid_objs')
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def)
  done

lemma possibleSwitchTo_rewrite:
  "monadic_rewrite True True
          (\<lambda>s. obj_at' (\<lambda>tcb. tcbPriority tcb = destPrio \<and> tcbDomain tcb = destDom) t s
              \<and> ksSchedulerAction s = ResumeCurrentThread
              \<and> ksCurThread s = thread
              \<and> ksCurDomain s = curDom
              \<and> destDom = curDom)
    (possibleSwitchTo t) (setSchedulerAction (SwitchToThread t))"
  supply if_split[split del]
  apply (simp add: possibleSwitchTo_def)
  (* under current preconditions both branch conditions are false *)
  apply (monadic_rewrite_l monadic_rewrite_if_l_False \<open>wpsimp wp: threadGet_wp cd_wp\<close>)
   apply (monadic_rewrite_l monadic_rewrite_if_l_False \<open>wpsimp wp: threadGet_wp cd_wp\<close>)
   (* discard unused getters before setSchedulerAction *)
   apply (simp add: getCurThread_def curDomain_def gets_bind_ign getSchedulerAction_def)
   apply (monadic_rewrite_symb_exec_l_drop, rule monadic_rewrite_refl)
  apply (auto simp: obj_at'_def)
  done

lemma scheduleSwitchThreadFastfail_False_wp:
  "\<lbrace>\<lambda>s. ct \<noteq> it \<and> cprio \<le> tprio \<rbrace>
   scheduleSwitchThreadFastfail ct it cprio tprio
   \<lbrace>\<lambda>rv s. \<not> rv \<rbrace>"
  unfolding scheduleSwitchThreadFastfail_def
  by (wp threadGet_wp)
     (auto dest!: obj_at_ko_at' simp: le_def obj_at'_def)

lemma lookupBitmapPriority_lift:
  assumes prqL1: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  and     prqL2: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  shows   "\<lbrace>\<lambda>s. P (lookupBitmapPriority d s) \<rbrace> f \<lbrace>\<lambda>_ s. P (lookupBitmapPriority d s) \<rbrace>"
  unfolding lookupBitmapPriority_def
  apply (rule hoare_pre)
   apply (wps prqL1 prqL2)
   apply wpsimp+
  done

(* slow path additionally requires current thread not idle *)
definition
  "fastpathBestSwitchCandidate t \<equiv> \<lambda>s.
     ksReadyQueuesL1Bitmap s (ksCurDomain s) = 0
   \<or> (\<forall>tprio. obj_at' (\<lambda>tcb. tcbPriority tcb = tprio) t s
              \<longrightarrow> (obj_at' (\<lambda>tcb. tcbPriority tcb \<le> tprio) (ksCurThread s) s
                  \<or> lookupBitmapPriority (ksCurDomain s) s \<le> tprio))"

lemma fastpathBestSwitchCandidateI:
  "\<lbrakk> ksReadyQueuesL1Bitmap s (ksCurDomain s) = 0
     \<or> tcbPriority ctcb \<le> tcbPriority ttcb
     \<or> lookupBitmapPriority (ksCurDomain s) s \<le> tcbPriority ttcb;
     ko_at' ttcb t s; ko_at' ctcb (ksCurThread s) s\<rbrakk>
   \<Longrightarrow> fastpathBestSwitchCandidate t s"
   unfolding fastpathBestSwitchCandidate_def
   by normalise_obj_at'

lemma fastpathBestSwitchCandidate_lift:
  assumes ct[wp]: "\<And>P. \<lbrace>\<lambda>s. P (ksCurThread s) \<rbrace> f \<lbrace> \<lambda>_ s. P (ksCurThread s) \<rbrace>"
  assumes cd[wp]: "\<And>P. \<lbrace>\<lambda>s. P (ksCurDomain s) \<rbrace> f \<lbrace> \<lambda>_ s. P (ksCurDomain s) \<rbrace>"
  assumes l1[wp]: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s) \<rbrace> f \<lbrace> \<lambda>_ s. P (ksReadyQueuesL1Bitmap s) \<rbrace>"
  assumes l2[wp]: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s) \<rbrace> f \<lbrace> \<lambda>_ s. P (ksReadyQueuesL2Bitmap s) \<rbrace>"
  assumes p[wp]: "\<And>P t. \<lbrace> obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t \<rbrace> f \<lbrace> \<lambda>_.  obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t \<rbrace>"
  shows "\<lbrace> tcb_at' t and fastpathBestSwitchCandidate t \<rbrace> f \<lbrace>\<lambda>rv. fastpathBestSwitchCandidate t \<rbrace>"
  unfolding fastpathBestSwitchCandidate_def lookupBitmapPriority_def l1IndexToPrio_def
  apply (rule hoare_pre)
   apply (rule hoare_lift_Pf2[where f=ksCurDomain])
    apply (wp hoare_vcg_disj_lift hoare_vcg_all_lift)
    apply (rule hoare_lift_Pf2[where f=ksCurThread])
     apply (rule hoare_lift_Pf2[where f=ksReadyQueuesL1Bitmap])
      apply (rule hoare_lift_Pf2[where f=ksReadyQueuesL2Bitmap])
       apply (wp hoare_vcg_imp_lift')
        apply (strengthen not_obj_at'_strengthen)
        apply (wpsimp simp: comp_def wp: l1 l2 hoare_vcg_disj_lift)+
  apply (drule (1) tcb_at_not_obj_at_elim'[rotated])
  apply (rename_tac tprio, erule_tac x=tprio in allE)
  apply clarsimp
  apply (drule (1) tcb_at_not_obj_at_elim'[rotated])
  apply (clarsimp simp: obj_at'_def)
  done

lemma fastpathBestSwitchCandidate_ksSchedulerAction_simp[simp]:
  "fastpathBestSwitchCandidate t (s\<lparr>ksSchedulerAction := a\<rparr>)
     = fastpathBestSwitchCandidate t s"
  unfolding fastpathBestSwitchCandidate_def lookupBitmapPriority_def
  by simp

lemma sched_act_SwitchToThread_rewrite:
  "\<lbrakk> sa = SwitchToThread t \<Longrightarrow> monadic_rewrite F E Q (m_sw t) f \<rbrakk>
   \<Longrightarrow> monadic_rewrite F E ((\<lambda>_. sa = SwitchToThread t) and Q)
       (case_scheduler_action m_res m_ch (\<lambda>t. m_sw t) sa) f"
  apply (cases sa; simp add: monadic_rewrite_impossible)
  apply (rename_tac t')
  apply (case_tac "t' = t"; simp add: monadic_rewrite_impossible)
  done

lemma schedule_rewrite_ct_not_runnable':
  "monadic_rewrite True True
            (\<lambda>s. ksSchedulerAction s = SwitchToThread t \<and> ct_in_state' (Not \<circ> runnable') s
                 \<and> (ksCurThread s \<noteq> ksIdleThread s)
                 \<and> fastpathBestSwitchCandidate t s)
            (schedule)
            (do setSchedulerAction ResumeCurrentThread; switchToThread t od)"
  supply subst_all [simp del]
  apply (simp add: schedule_def)
  (* switching to t *)
  apply (monadic_rewrite_l sched_act_SwitchToThread_rewrite[where t=t])
   (* not wasRunnable, skip enqueue *)
   apply (simp add: when_def)
   apply (monadic_rewrite_l monadic_rewrite_if_l_False)
   (* fastpath: \<not> (fastfail \<and> \<not> highest) *)
   apply (monadic_rewrite_l monadic_rewrite_if_l_False
            \<open>wpsimp simp: isHighestPrio_def'
                    wp: hoare_vcg_imp_lift hoare_vcg_disj_lift threadGet_wp''
                        scheduleSwitchThreadFastfail_False_wp\<close>)
   (* fastpath: no scheduleChooseNewThread *)
   apply (monadic_rewrite_l monadic_rewrite_if_l_False
            \<open>wpsimp simp: isHighestPrio_def'
                    wp: hoare_vcg_imp_lift hoare_vcg_disj_lift threadGet_wp''
                        scheduleSwitchThreadFastfail_False_wp\<close>)
   (* remove no-ops *)
   apply (repeat 10 monadic_rewrite_symb_exec_l) (* until switchToThread *)
              apply (simp add: setSchedulerAction_def)
              apply (subst oblivious_modify_swap[symmetric],
                     rule oblivious_switchToThread_schact)
              apply (rule monadic_rewrite_refl)
             apply (wpsimp wp: empty_fail_isRunnable simp: isHighestPrio_def')+
  apply (clarsimp simp: ct_in_state'_def not_pred_tcb_at'_strengthen
                        fastpathBestSwitchCandidate_def)
  apply normalise_obj_at'
  done

lemma resolveAddressBits_points_somewhere:
  "\<lbrace>\<lambda>s. \<forall>slot. Q slot s\<rbrace> resolveAddressBits cp cptr bits \<lbrace>Q\<rbrace>,-"
  apply (rule_tac Q'="\<lambda>rv s. \<forall>rv. Q rv s" in hoare_strengthen_postE_R)
   apply wp
  apply clarsimp
  done

lemma foldr_copy_register_tsrs:
  "foldr (\<lambda>r . copy_register_tsrs x y r r (\<lambda>x. x)) rs s
       = (s (y := TCBStateRegs (tsrState (s y))
                       (\<lambda>r. if r \<in> set rs then tsrContext (s x) r
                                 else tsrContext (s y) r)))"
  apply (induct rs)
   apply simp
  apply (simp add: copy_register_tsrs_def fun_eq_iff
            split: if_split)
  done

lemmas cteInsert_obj_at'_not_queued =  cteInsert_obj_at'_queued[of "\<lambda>a. \<not> a"]

lemma monadic_rewrite_threadGet:
  "monadic_rewrite E F (obj_at' (\<lambda>tcb. f tcb = v) t)
    (threadGet f t) (return v)"
  unfolding getThreadState_def threadGet_def
  apply (simp add: liftM_def)
  apply monadic_rewrite_symb_exec_l
    apply (rule_tac P="\<lambda>_. f x = v" in monadic_rewrite_pre_imp_eq)
    apply blast
   apply (wpsimp wp: OMG_getObject_tcb simp: obj_tcb_at')+
  done

lemma monadic_rewrite_getThreadState:
  "monadic_rewrite E F (obj_at' (\<lambda>tcb. tcbState tcb = v) t)
    (getThreadState t) (return v)"
  unfolding getThreadState_def
  by (rule monadic_rewrite_threadGet)

lemma setCTE_obj_at'_tcbIPCBuffer:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbIPCBuffer tcb)) t\<rbrace> setCTE p v \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P (tcbIPCBuffer tcb)) t\<rbrace>"
  unfolding setCTE_def
  by (rule setObject_cte_obj_at_tcb', simp+)

context
notes if_cong[cong]
begin
crunch cteInsert, asUser
  for obj_at'_tcbIPCBuffer[wp]: "obj_at' (\<lambda>tcb. P (tcbIPCBuffer tcb)) t"
  (wp: setCTE_obj_at'_queued crunch_wps threadSet_obj_at'_really_strongest)
end

crunch cteInsert, threadSet, asUser, emptySlot
  for ksReadyQueuesL1Bitmap_inv[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and ksReadyQueuesL2Bitmap_inv[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (wp: hoare_drop_imps)

crunch setEndpoint
  for ksReadyQueuesL1Bitmap_inv[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv)
crunch setEndpoint
  for ksReadyQueuesL2Bitmap_inv[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv)

lemma setThreadState_runnable_bitmap_inv:
  "runnable' ts \<Longrightarrow>
    \<lbrace> \<lambda>s. P (ksReadyQueuesL1Bitmap s) \<rbrace> setThreadState ts t \<lbrace>\<lambda>rv s. P (ksReadyQueuesL1Bitmap s) \<rbrace>"
  "runnable' ts \<Longrightarrow>
    \<lbrace> \<lambda>s. Q (ksReadyQueuesL2Bitmap s) \<rbrace> setThreadState ts t \<lbrace>\<lambda>rv s. Q (ksReadyQueuesL2Bitmap s) \<rbrace>"
   by (simp_all add: setThreadState_runnable_simp, wp+)

(* FIXME move *)
crunch curDomain
  for (no_fail) no_fail[intro!, wp, simp]

lemma setThreadState_tcbDomain_tcbPriority_obj_at'[wp]:
  "setThreadState ts t \<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb) (tcbPriority tcb)) t'\<rbrace>"
  unfolding setThreadState_def rescheduleRequired_def tcbSchedEnqueue_def tcbQueuePrepend_def
  apply (wpsimp wp: threadSet_wp hoare_drop_imps threadGet_wp simp: setQueue_def bitmap_fun_defs)
  apply (fastforce simp: obj_at'_def st_tcb_at'_def objBits_simps projectKOs)
  done

lemma setThreadState_tcbQueued_obj_at'[wp]:
  "setThreadState ts t \<lbrace>obj_at' (\<lambda>tcb. P (tcbQueued tcb)) t'\<rbrace>"
  unfolding setThreadState_def rescheduleRequired_def tcbSchedEnqueue_def tcbQueuePrepend_def
  apply (wpsimp wp: threadSet_wp hoare_drop_imps threadGet_wp simp: setQueue_def bitmap_fun_defs)
  apply (fastforce simp: obj_at'_def st_tcb_at'_def objBits_simps projectKOs)
  done

lemma setThreadState_tcbFault_obj_at'[wp]:
  "setThreadState ts t \<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t'\<rbrace>"
  unfolding setThreadState_def rescheduleRequired_def tcbSchedEnqueue_def tcbQueuePrepend_def
  apply (wpsimp wp: threadSet_wp hoare_drop_imps threadGet_wp simp: setQueue_def bitmap_fun_defs)
  apply (fastforce simp: obj_at'_def st_tcb_at'_def objBits_simps projectKOs)
  done

lemma setThreadState_tcbArch_obj_at'[wp]:
  "setThreadState ts t \<lbrace>obj_at' (\<lambda>tcb. P (tcbArch tcb)) t'\<rbrace>"
  unfolding setThreadState_def rescheduleRequired_def tcbSchedEnqueue_def tcbQueuePrepend_def
  apply (wpsimp wp: threadSet_wp hoare_drop_imps threadGet_wp simp: setQueue_def bitmap_fun_defs)
  apply (fastforce simp: obj_at'_def st_tcb_at'_def objBits_simps projectKOs)
  done

lemma fastpath_callKernel_SysCall_corres:
  "monadic_rewrite True False
         (invs' and ct_in_state' ((=) Running)
                and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
                and (\<lambda>s. ksDomainTime s \<noteq> 0) and ready_qs_runnable)
     (callKernel (SyscallEvent SysCall)) (fastpaths SysCall)"
  supply if_cong[cong] option.case_cong[cong] if_split[split del]
  supply empty_fail_getMRs[wp] (* FIXME *)
  supply empty_fail_getEndpoint[wp] (* FIXME *)
  apply (rule monadic_rewrite_introduce_alternative[OF callKernel_def[simplified atomize_eq]])
  apply (rule monadic_rewrite_guard_imp)
   apply (rule monadic_rewrite_bind_alternative_l, wpsimp)
   apply (rule monadic_rewrite_stateAssert)
   apply (simp add: handleEvent_def handleCall_def
                    handleInvocation_def liftE_bindE_handle
                    bind_assoc getMessageInfo_def)
   apply (simp add: catch_liftE_bindE unlessE_throw_catch_If
                    unifyFailure_catch_If catch_liftE
                    getMessageInfo_def alternative_bind
                    fastpaths_def
              cong: if_cong)
   apply (rule monadic_rewrite_bind_alternative_l, wp)
   apply (rule monadic_rewrite_bind_tail)
    apply (rule monadic_rewrite_bind_alternative_l, wp)
    apply (rule monadic_rewrite_bind_tail)
     apply (rename_tac msgInfo)
     apply (rule monadic_rewrite_bind_alternative_l, wp)
     apply (rule monadic_rewrite_bind_tail)
      apply monadic_rewrite_symb_exec_r
       apply (rename_tac tcbFault)
       apply (rule monadic_rewrite_alternative_r[rotated])
        apply (rule monadic_rewrite_alternative_l)
       apply (rule monadic_rewrite_if_r[rotated])
        apply (rule monadic_rewrite_alternative_l)
       apply (simp add: split_def Syscall_H.syscall_def
                        liftE_bindE_handle bind_assoc
                        capFaultOnFailure_def)
       apply (simp only: bindE_bind_linearise[where f="rethrowFailure fn f'" for fn f']
                         bind_case_sum_rethrow)
       apply (simp add: lookupCapAndSlot_def
                        lookupSlotForThread_def bindE_assoc
                        liftE_bind_return_bindE_returnOk split_def
                        getThreadCSpaceRoot_def locateSlot_conv
                        returnOk_liftE[symmetric] const_def
                        getSlotCap_def)
       apply (simp only: liftE_bindE_assoc)
       apply (rule monadic_rewrite_bind_alternative_l, wp)
       apply (rule monadic_rewrite_bind_tail)
        apply (rule monadic_rewrite_bind_alternative_l)
         apply (wp | simp)+
        apply (rule_tac fn="case_sum Inl (Inr \<circ> fst)" in monadic_rewrite_split_fn)
          apply (simp add: liftME_liftM[symmetric] liftME_def bindE_assoc)
          apply (rule monadic_rewrite_refl)
         apply (rule monadic_rewrite_if_r[rotated])
          apply (rule monadic_rewrite_alternative_l)
         apply (simp add: isRight_right_map isRight_case_sum)
         apply (rule monadic_rewrite_if_r[rotated])
          apply (rule monadic_rewrite_alternative_l)
         apply (rule monadic_rewrite_bind_alternative_l[OF lookupIPC_inv])
         apply monadic_rewrite_symb_exec_l
          apply (simp add: lookupExtraCaps_null returnOk_bind liftE_bindE_handle
                           bind_assoc liftE_bindE_assoc
                           decodeInvocation_def Let_def from_bool_0
                           performInvocation_def liftE_handle
                           liftE_bind)
          apply monadic_rewrite_symb_exec_r
           apply (rename_tac "send_ep")
           apply (rule monadic_rewrite_if_r[rotated])
            apply (rule monadic_rewrite_alternative_l)
           apply (simp add: getThreadVSpaceRoot_def locateSlot_conv)
           apply monadic_rewrite_symb_exec_r
            apply (rename_tac "pdCapCTE")
            apply (rule monadic_rewrite_if_r[rotated])
             apply (rule monadic_rewrite_alternative_l)
            apply monadic_rewrite_symb_exec_r
             apply monadic_rewrite_symb_exec_r
              apply monadic_rewrite_symb_exec_r
               apply (simp add: isHighestPrio_def')
               apply monadic_rewrite_symb_exec_r
                apply (rule monadic_rewrite_if_r[rotated])
                 apply (rule monadic_rewrite_alternative_l)
                apply (rule monadic_rewrite_if_r[rotated])
                 apply (rule monadic_rewrite_alternative_l)
                apply monadic_rewrite_symb_exec_r
                 apply (rule monadic_rewrite_if_r[rotated])
                  apply (rule monadic_rewrite_alternative_l)
                 apply monadic_rewrite_symb_exec_r
                  apply (rule monadic_rewrite_if_r[rotated])
                   apply (rule monadic_rewrite_alternative_l)
                  apply (rule monadic_rewrite_trans,
                         rule monadic_rewrite_pick_alternative_1)
                  apply monadic_rewrite_symb_exec_l
                   (* now committed to fastpath *)
                   apply (rule monadic_rewrite_trans)
                    apply (rule_tac F=True and E=True in monadic_rewrite_weaken_flags)
                    apply simp
                    apply (rule monadic_rewrite_bind_tail)
                     apply (monadic_rewrite_symb_exec_l_known thread)
                      apply (simp add: sendIPC_def bind_assoc)
                      apply (monadic_rewrite_symb_exec_l_known send_ep)
                       apply (rule_tac P="epQueue send_ep \<noteq> []" in monadic_rewrite_gen_asm)
                       apply (simp add: isRecvEP_endpoint_case list_case_helper bind_assoc)
                       apply (rule monadic_rewrite_bind_tail)
                        apply (elim conjE)
                        apply (rule monadic_rewrite_bind_tail, rename_tac dest_st)
                         apply (rule_tac P="\<exists>gr. dest_st = BlockedOnReceive (capEPPtr (fst (theRight rv))) gr"
                                  in monadic_rewrite_gen_asm)
                         apply monadic_rewrite_symb_exec_l_drop
                         apply (rule monadic_rewrite_bind)
                           apply clarsimp
                           apply (rule_tac msgInfo=msgInfo in doIPCTransfer_simple_rewrite)
                          apply (rule monadic_rewrite_bind_tail)
                           apply (rule monadic_rewrite_bind)
                             apply (rule_tac destPrio=destPrio
                                      and curDom=curDom and destDom=destDom and thread=thread
                                      in possibleSwitchTo_rewrite)
                            apply (rule monadic_rewrite_bind)
                              apply (rule monadic_rewrite_trans)
                               apply (rule setupCallerCap_rewrite)
                              apply (rule monadic_rewrite_bind_head)
                              apply (rule setThreadState_rewrite_simple, simp)
                             apply (rule monadic_rewrite_trans)
                              apply (monadic_rewrite_symb_exec_l_known BlockedOnReply)
                               apply simp
                               apply (rule monadic_rewrite_refl)
                              apply wpsimp
                             apply (rule monadic_rewrite_trans)
                              apply (rule monadic_rewrite_bind_head)
                              apply (rule_tac t="hd (epQueue send_ep)"
                                       in schedule_rewrite_ct_not_runnable')
                             apply (simp add: bind_assoc)
                             apply (rule monadic_rewrite_bind_tail)
                              apply (rule monadic_rewrite_bind)
                                apply (rule switchToThread_rewrite)
                               apply (rule monadic_rewrite_bind)
                                 apply (rule activateThread_simple_rewrite)
                                apply (rule monadic_rewrite_refl)
                               apply wp
                              apply (wp setCurThread_ct_in_state)
                             apply (simp only: st_tcb_at'_def[symmetric])
                             apply (wp, clarsimp simp: cur_tcb'_def ct_in_state'_def)
                            apply (simp add: getThreadCallerSlot_def getThreadReplySlot_def
                                             locateSlot_conv ct_in_state'_def cur_tcb'_def)

                            apply ((wp assert_inv threadSet_pred_tcb_at_state
                                       cteInsert_obj_at'_not_queued
                                    | wps)+)[1]

                               apply (wp fastpathBestSwitchCandidate_lift[where f="cteInsert c w w'" for c w w'])
                               apply ((wp assert_inv threadSet_pred_tcb_at_state cteInsert_obj_at'_not_queued | wps)+)[1]
                              apply ((wp assert_inv threadSet_pred_tcb_at_state cteInsert_obj_at'_not_queued | wps)+)[1]
                             apply ((wp assert_inv threadSet_pred_tcb_at_state cteInsert_obj_at'_not_queued | wps)+)[1]
                            apply ((wp assert_inv threadSet_pred_tcb_at_state cteInsert_obj_at'_not_queued | wps)+)[1]
                            apply (wpsimp wp: fastpathBestSwitchCandidate_lift[where f="threadSet f t" for f t])
                            apply ((wp assert_inv threadSet_pred_tcb_at_state
                                       cteInsert_obj_at'_not_queued
                                    | wps)+)[1]
                           apply (simp add: setSchedulerAction_def)
                           apply wp[1]
                          apply (simp cong: if_cong HOL.conj_cong add: if_bool_simps)
                          apply (simp_all only:)[5]
                          apply ((wp asUser_obj_at_unchanged mapM_x_wp'
                                     sts_st_tcb_at'_cases
                                     setThreadState_no_sch_change
                                     setEndpoint_obj_at_tcb'
                                     fastpathBestSwitchCandidate_lift[where f="setThreadState f t" for f t]
                                     fastpathBestSwitchCandidate_lift[where f="asUser t f" for f t]
                                     fastpathBestSwitchCandidate_lift[where f="setEndpoint a b" for a b]
                                     lookupBitmapPriority_lift
                                     setThreadState_runnable_bitmap_inv
                                     getEndpoint_obj_at'
                                   | simp add: setMessageInfo_def obj_at'_conj
                                   | wp (once) hoare_vcg_disj_lift)+)
                   apply (simp add: setThreadState_runnable_simp
                                    getThreadCallerSlot_def getThreadReplySlot_def
                                    locateSlot_conv bind_assoc)
                   apply (rule_tac P="\<lambda>v.  obj_at' (%tcb. tcbIPCBuffer tcb = v) (hd (epQueue send_ep))"
                           in monadic_rewrite_exists_v)
                   apply (rename_tac ipcBuffer)

                   apply (rule_tac P="\<lambda>v.  obj_at' (\<lambda>tcb. tcbState tcb = v) (hd (epQueue send_ep))"
                           in monadic_rewrite_exists_v)
                   apply (rename_tac destState)

                   apply (simp add: ARM_HYP_H.switchToThread_def getTCB_threadGet bind_assoc)
                   (* retrieving state or thread registers is not thread_action_isolatable,
                      translate into return with suitable precondition  *)
                   apply (rule monadic_rewrite_trans[OF _ monadic_rewrite_transverse])
                     apply (rule_tac v=destState in monadic_rewrite_getThreadState
                            | rule monadic_rewrite_bind monadic_rewrite_refl)+
                                      apply (wp mapM_x_wp' getObject_inv | wpc | simp | wp (once) hoare_drop_imps)+
                    apply (rule_tac v=destState in monadic_rewrite_getThreadState
                           | rule monadic_rewrite_bind monadic_rewrite_refl)+
                                 apply (wp mapM_x_wp' getObject_inv | wpc | simp | wp (once) hoare_drop_imps)+

                   apply (rule_tac P="inj (case_bool thread (hd (epQueue send_ep)))"
                            in monadic_rewrite_gen_asm)
                   apply (rule monadic_rewrite_trans[OF _ monadic_rewrite_transverse])
                     apply (rule monadic_rewrite_weaken_flags[where F=False and E=True], simp)
                     apply (rule isolate_thread_actions_rewrite_bind
                                 fastpath_isolate_rewrites fastpath_isolatables
                                 bool.simps setRegister_simple_modify_registers
                                 zipWithM_setRegister_simple_modify_registers
                                 threadGet_vcpu_isolatable[THEN thread_actions_isolatableD, simplified o_def]
                                 threadGet_vcpu_isolatable[simplified o_def]
                                 vcpuSwitch_isolatable[THEN thread_actions_isolatableD] vcpuSwitch_isolatable
                                 setVMRoot_isolatable[THEN thread_actions_isolatableD] setVMRoot_isolatable
                                 doMachineOp_isolatable[THEN thread_actions_isolatableD] doMachineOp_isolatable
                                 kernelExitAssertions_isolatable[THEN thread_actions_isolatableD]
                                 kernelExitAssertions_isolatable
                                 thread_actions_isolatable_bind
                              | assumption
                              | wp assert_inv)+
                   apply (rule_tac P="\<lambda>s. ksSchedulerAction s = ResumeCurrentThread
                                       \<and> tcb_at' thread s"
                              and F=True and E=False in monadic_rewrite_weaken_flags)
                   apply simp
                   apply (rule monadic_rewrite_isolate_final)
                     apply (simp add: isRight_case_sum cong: list.case_cong)
                    apply (clarsimp simp: fun_eq_iff if_flip
                                   cong: if_cong)
                    apply (drule obj_at_ko_at', clarsimp)
                    apply (frule get_tcb_state_regs_ko_at')
                    apply (clarsimp simp: zip_map2 zip_same_conv_map foldl_map
                                         foldl_fun_upd
                                         foldr_copy_register_tsrs
                                         isRight_case_sum
                                   cong: if_cong)
                    apply (simp add: upto_enum_def fromEnum_def
                                    enum_register  toEnum_def
                                    msgRegisters_unfold
                               cong: if_cong)
                    apply (clarsimp split: if_split)
                    apply (rule ext)
                    apply (simp add: badgeRegister_def msgInfoRegister_def
                                    ARM_HYP.badgeRegister_def
                                    ARM_HYP.msgInfoRegister_def
                             split: if_split)
                   apply simp
                  apply (wp | simp cong: if_cong bool.case_cong
                            | rule getCTE_wp' gts_wp' threadGet_wp
                                  getEndpoint_wp)+
        apply (rule validE_cases_valid)
        apply (simp add: isRight_def getSlotCap_def)
        apply (wp getCTE_wp')
        apply (rule resolveAddressBits_points_somewhere)
       apply (simp cong: if_cong bool.case_cong)
       apply wp
      apply simp
      apply (wp user_getreg_wp threadGet_wp)+

  apply clarsimp
  apply (subgoal_tac "ksCurThread s \<noteq> ksIdleThread s")
   prefer 2
   apply (fastforce simp: ct_in_state'_def dest: ct_running_not_idle' elim: pred_tcb'_weakenE)

  apply (clarsimp simp: ct_in_state'_def pred_tcb_at')
  apply (frule cte_wp_at_valid_objs_valid_cap', clarsimp+)
  apply (clarsimp simp: isCap_simps valid_cap'_def maskCapRights_def)
  apply (frule ko_at_valid_ep', clarsimp)
  apply (frule sym_refs_ko_atD'[where 'a=endpoint], clarsimp)
  apply (clarsimp simp: valid_ep'_def isRecvEP_endpoint_case neq_Nil_conv
                        tcbVTableSlot_def cte_level_bits_def
                        cte_at_tcb_at_16' length_msgRegisters
                        size_msgRegisters_def order_less_imp_le
                        ep_q_refs_of'_def st_tcb_at_refs_of_rev'
                  cong: if_cong)
  apply (rename_tac blockedThread ys tcba tcbb)
  apply (frule invs_mdb')
  apply (thin_tac "Ball S P" for S P)+
  supply imp_disjL[simp del]
  apply (subst imp_disjL[symmetric])

  (* clean up broken up disj implication and excessive references to same tcbs *)
  apply normalise_obj_at'
  apply (clarsimp simp: invs'_def valid_state'_def)
  apply (fold imp_disjL, intro allI impI)

  apply (subgoal_tac "ksCurThread s \<noteq> blockedThread")
   prefer 2
   apply normalise_obj_at'
  apply clarsimp
  apply (subgoal_tac "fastpathBestSwitchCandidate blockedThread s")
   prefer 2
   apply (rule_tac ttcb=tcbb and ctcb=tcb in fastpathBestSwitchCandidateI)
     apply (solves \<open>simp only: disj_ac\<close>)
    apply simp+
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def objBits_simps projectKOs valid_mdb'_def
                        valid_mdb_ctes_def inj_case_bool
                 split: bool.split)+
  apply (clarsimp simp: ready_qs_runnable_def)
  apply (drule_tac x=blockedThread in spec)
  apply (clarsimp simp: obj_at'_def projectKOs st_tcb_at'_def objBits_simps)
  done

lemma capability_case_Null_ReplyCap:
  "(case cap of NullCap \<Rightarrow> f | ReplyCap t b cg \<Rightarrow> g t b cg | _ \<Rightarrow> h)
     = (if isReplyCap cap then g (capTCBPtr cap) (capReplyMaster cap) (capReplyCanGrant cap)
             else if isNullCap cap then f else h)"
  by (simp add: isCap_simps split: capability.split split del: if_split)

lemma injection_handler_catch:
  "catch (injection_handler f x) y
      = catch x (y o f)"
  apply (simp add: injection_handler_def catch_def handleE'_def
                   bind_assoc)
  apply (rule bind_cong[OF refl])
  apply (simp add: throwError_bind split: sum.split)
  done

lemma doReplyTransfer_simple:
  "monadic_rewrite True False
     (obj_at' (\<lambda>tcb. tcbFault tcb = None) receiver)
     (doReplyTransfer sender receiver slot grant)
     (do state \<leftarrow> getThreadState receiver;
         assert (isReply state);
         cte \<leftarrow> getCTE slot;
         mdbnode \<leftarrow> return $ cteMDBNode cte;
         assert (mdbPrev mdbnode \<noteq> 0 \<and> mdbNext mdbnode = 0);
         parentCTE \<leftarrow> getCTE (mdbPrev mdbnode);
         assert (isReplyCap (cteCap parentCTE) \<and> capReplyMaster (cteCap parentCTE));
         doIPCTransfer sender Nothing 0 grant receiver;
         cteDeleteOne slot;
         setThreadState Running receiver;
         possibleSwitchTo receiver
         od)"
  apply (simp add: doReplyTransfer_def liftM_def nullPointer_def getSlotCap_def)
  apply (rule monadic_rewrite_bind_tail)+
        apply (monadic_rewrite_symb_exec_l_known None, simp)
         apply (rule monadic_rewrite_refl)
        apply (wpsimp wp: threadGet_const gts_wp' getCTE_wp' simp: o_def)+
  done

lemma receiveIPC_simple_rewrite:
  "monadic_rewrite True False
     ((\<lambda>_. isEndpointCap ep_cap \<and> \<not> isSendEP ep) and (ko_at' ep (capEPPtr ep_cap) and
      (\<lambda>s. \<forall>ntfnptr. bound_tcb_at' ((=) (Some ntfnptr)) thread s \<longrightarrow> obj_at' (Not \<circ> isActive) ntfnptr s)))
     (receiveIPC thread ep_cap True)
     (do
       setThreadState (BlockedOnReceive (capEPPtr ep_cap) (capEPCanGrant ep_cap)) thread;
       setEndpoint (capEPPtr ep_cap) (RecvEP (case ep of RecvEP q \<Rightarrow> (q @ [thread]) | _ \<Rightarrow> [thread]))
      od)"
  supply empty_fail_getEndpoint[wp]
  apply (rule monadic_rewrite_gen_asm)
  apply (simp add: receiveIPC_def)
  apply (monadic_rewrite_symb_exec_l_known ep)
    apply monadic_rewrite_symb_exec_l+
       apply (monadic_rewrite_l monadic_rewrite_if_l_False)
       apply (rule monadic_rewrite_is_refl)
       apply (cases ep; simp add: isSendEP_def)
      apply (wpsimp wp: getNotification_wp gbn_wp' getEndpoint_wp
                    simp: getBoundNotification_def)+
  apply (clarsimp simp: obj_at'_def projectKOs pred_tcb_at'_def)
  done

lemma empty_fail_isFinalCapability:
  "empty_fail (isFinalCapability cte)"
  by (simp add: isFinalCapability_def Let_def empty_fail_cond split: if_split)

lemma cteDeleteOne_replycap_rewrite:
  "monadic_rewrite True False
     (cte_wp_at' (\<lambda>cte. isReplyCap (cteCap cte)) slot)
     (cteDeleteOne slot)
     (emptySlot slot NullCap)"
  supply isFinalCapability_inv[wp] empty_fail_isFinalCapability[wp] (* FIXME *)
  apply (simp add: cteDeleteOne_def)
  apply (rule monadic_rewrite_symb_exec_l)
     apply (rule_tac P="cteCap cte \<noteq> NullCap \<and> isReplyCap (cteCap cte)
                        \<and> \<not> isEndpointCap (cteCap cte)
                        \<and> \<not> isNotificationCap (cteCap cte)"
              in monadic_rewrite_gen_asm)
     apply (simp add: finaliseCapTrue_standin_def capRemovable_def)
     apply monadic_rewrite_symb_exec_l
      apply (rule monadic_rewrite_refl)
     apply (wpsimp wp: getCTE_wp')+
  apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps)
  done

lemma cteDeleteOne_nullcap_rewrite:
  "monadic_rewrite True False
     (cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) slot)
     (cteDeleteOne slot)
     (return ())"
  apply (simp add: cteDeleteOne_def unless_def when_def)
  apply (monadic_rewrite_l monadic_rewrite_if_l_False \<open>wpsimp wp: getCTE_wp'\<close>)
   apply (monadic_rewrite_symb_exec_l, rule monadic_rewrite_refl)
   apply (wpsimp wp: getCTE_wp' simp: cte_wp_at_ctes_of)+
  done

lemma deleteCallerCap_nullcap_rewrite:
  "monadic_rewrite True False
     (cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) (thread + 2 ^ cte_level_bits * tcbCallerSlot))
     (deleteCallerCap thread)
     (return ())"
  apply (simp add: deleteCallerCap_def getThreadCallerSlot_def locateSlot_conv
                   getSlotCap_def)
  apply (monadic_rewrite_l cteDeleteOne_nullcap_rewrite \<open>wpsimp wp: getCTE_wp\<close>)
   apply (monadic_rewrite_symb_exec_l+, rule monadic_rewrite_refl)
    apply (wpsimp simp: cte_wp_at_ctes_of)+
  done

lemma emptySlot_cnode_caps:
  "\<lbrace>\<lambda>s. P (only_cnode_caps (ctes_of s)) \<and> cte_wp_at' (\<lambda>cte. \<not> isCNodeCap (cteCap cte)) slot s\<rbrace>
     emptySlot slot NullCap
   \<lbrace>\<lambda>rv s. P (only_cnode_caps (ctes_of s))\<rbrace>"
  apply (simp add: only_cnode_caps_def map_option_comp2
                   o_assoc[symmetric] cteCaps_of_def[symmetric])
  apply (wp emptySlot_cteCaps_of)
  apply (clarsimp simp: cteCaps_of_def cte_wp_at_ctes_of
                 elim!: rsubst[where P=P] del: ext intro!: ext
                 split: if_split)
  done

lemma asUser_obj_at_ep[wp]:
  "\<lbrace>obj_at' P p\<rbrace> asUser t m \<lbrace>\<lambda>rv. obj_at' (P :: endpoint \<Rightarrow> bool) p\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps | simp)+
  done

lemma setCTE_obj_at_ep[wp]:
  "\<lbrace>obj_at' (P :: endpoint \<Rightarrow> bool) p\<rbrace> setCTE ptr cte \<lbrace>\<lambda>rv. obj_at' P p\<rbrace>"
  unfolding setCTE_def
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_cte typeError_def in_monad
                 split: Structures_H.kernel_object.split_asm
                        if_split_asm)
  done

lemma setCTE_obj_at_ntfn[wp]:
  "\<lbrace>obj_at' (P :: Structures_H.notification \<Rightarrow> bool) p\<rbrace> setCTE ptr cte \<lbrace>\<lambda>rv. obj_at' P p\<rbrace>"
  unfolding setCTE_def
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_cte typeError_def in_monad
                 split: Structures_H.kernel_object.split_asm
                        if_split_asm)
  done

crunch emptySlot
  for obj_at_ep[wp]: "obj_at' (P :: endpoint \<Rightarrow> bool) p"

crunch emptySlot, asUser
  for gsCNodes[wp]: "\<lambda>s. P (gsCNodes s)"
  (wp: crunch_wps)

crunch possibleSwitchTo
  for tcbContext[wp]: "obj_at' (\<lambda>tcb. P ( (atcbContextGet o tcbArch) tcb)) t"
  (wp: crunch_wps simp_del: comp_apply)

crunch doFaultTransfer
  for only_cnode_caps[wp]: "\<lambda>s. P (only_cnode_caps (ctes_of s))"
  (wp: crunch_wps simp: crunch_simps)

(* FIXME: monadic_rewrite_l does not work with stateAssert here *)
lemma tcbSchedDequeue_rewrite_not_queued:
  "monadic_rewrite True False (tcb_at' t and obj_at' (Not \<circ> tcbQueued) t)
     (tcbSchedDequeue t) (return ())"
  apply (simp add: tcbSchedDequeue_def)
  apply wp_pre
  apply monadic_rewrite_symb_exec_l
    apply (monadic_rewrite_symb_exec_l_known False, simp)
     apply (rule monadic_rewrite_refl)
    apply (wpsimp wp: threadGet_const)+
  done

lemma schedule_known_rewrite:
  "monadic_rewrite True False
      (\<lambda>s. ksSchedulerAction s = SwitchToThread t
               \<and> tcb_at' t s
               \<and> obj_at' (Not \<circ> tcbQueued) t s
               \<and> ksCurThread s = t'
               \<and> st_tcb_at' (Not \<circ> runnable') t' s
               \<and> (ksCurThread s \<noteq> ksIdleThread s)
               \<and> fastpathBestSwitchCandidate t s)
      (schedule)
      (do Arch.switchToThread t;
          setCurThread t;
          setSchedulerAction ResumeCurrentThread od)"
  supply subst_all[simp del] if_split[split del]
  apply (simp add: schedule_def)
  apply (simp only: Thread_H.switchToThread_def)
  (* switching to t *)
  apply (monadic_rewrite_l sched_act_SwitchToThread_rewrite[where t=t])
   (* not wasRunnable, skip enqueue *)
   apply (simp add: when_def)
   apply (monadic_rewrite_l monadic_rewrite_if_l_False)
   (* fastpath: \<not> (fastfail \<and> \<not> highest) *)
   apply (monadic_rewrite_l monadic_rewrite_if_l_False
            \<open>wpsimp simp: isHighestPrio_def'
                    wp: hoare_vcg_imp_lift hoare_vcg_disj_lift threadGet_wp''
                        scheduleSwitchThreadFastfail_False_wp\<close>)
   (* fastpath: no scheduleChooseNewThread *)
   apply (monadic_rewrite_l monadic_rewrite_if_l_False
            \<open>wpsimp simp: isHighestPrio_def'
                    wp: hoare_vcg_imp_lift hoare_vcg_disj_lift threadGet_wp''
                        scheduleSwitchThreadFastfail_False_wp\<close>)
   apply (simp add: bind_assoc)
   apply (monadic_rewrite_l tcbSchedDequeue_rewrite_not_queued
                            \<open>wpsimp wp: Arch_switchToThread_obj_at_pre\<close>)
   (* remove no-ops *)
   apply simp
   apply (repeat 13 \<open>rule monadic_rewrite_symb_exec_l\<close>) (* until switchToThread *)
                              apply (rule monadic_rewrite_refl)
                             apply (wpsimp simp: isHighestPrio_def')+
  apply (clarsimp simp: ct_in_state'_def not_pred_tcb_at'_strengthen
                        fastpathBestSwitchCandidate_def)
  apply normalise_obj_at'
  done

lemma tcb_at_cte_at_offset:
  "\<lbrakk> tcb_at' t s; 2 ^ cte_level_bits * off \<in> dom tcb_cte_cases \<rbrakk>
    \<Longrightarrow> cte_at' (t + 2 ^ cte_level_bits * off) s"
  apply (clarsimp simp: obj_at'_def projectKOs objBits_simps)
  apply (erule(2) cte_wp_at_tcbI')
   apply fastforce
  apply simp
  done

lemma emptySlot_cte_wp_at_cteCap:
  "\<lbrace>\<lambda>s. (p = p' \<longrightarrow> P NullCap) \<and> (p \<noteq> p' \<longrightarrow> cte_wp_at' (\<lambda>cte. P (cteCap cte)) p s)\<rbrace>
     emptySlot p' irqopt
   \<lbrace>\<lambda>rv s. cte_wp_at' (\<lambda>cte. P (cteCap cte)) p s\<rbrace>"
  apply (simp add: tree_cte_cteCap_eq[unfolded o_def])
  apply (wp emptySlot_cteCaps_of)
  apply (clarsimp split: if_split)
  done

lemma setEndpoint_getCTE_pivot[unfolded K_bind_def]:
  "do setEndpoint p val; v <- getCTE slot; f v od
     = do v <- getCTE slot; setEndpoint p val; f v od"
  apply (simp add: getCTE_assert_opt setEndpoint_def
                   setObject_modify_assert
                   fun_eq_iff bind_assoc)
  apply (simp add: exec_gets assert_def assert_opt_def
                   exec_modify update_ep_map_to_ctes
            split: if_split option.split)
  done

lemma setEndpoint_setCTE_pivot[unfolded K_bind_def]:
  "do setEndpoint p val; setCTE slot cte; f od =
     do setCTE slot cte; setEndpoint p val; f od"
  supply if_split[split del]
  apply (rule monadic_rewrite_to_eq)
  apply simp
  apply (rule monadic_rewrite_guard_imp)
   apply (rule monadic_rewrite_trans,
          rule_tac f="ep_at' p" in monadic_rewrite_add_gets)
   apply (rule monadic_rewrite_transverse, rule monadic_rewrite_add_gets,
          rule monadic_rewrite_bind_tail)
    apply (rename_tac epat)
    apply (rule monadic_rewrite_transverse)
     apply (rule monadic_rewrite_bind_tail)
      apply (simp add: setEndpoint_def setObject_modify_assert bind_assoc)
      apply (rule_tac rv=epat in monadic_rewrite_gets_known)
     apply (wp setCTE_typ_at'[where T="koType TYPE(endpoint)", unfolded typ_at_to_obj_at']
                  | simp)+
    apply (simp add: setCTE_assert_modify bind_assoc)
    apply (rule monadic_rewrite_trans, rule monadic_rewrite_add_gets,
           rule monadic_rewrite_bind_tail)+
      apply (rename_tac cteat tcbat)
      apply (rule monadic_rewrite_trans, rule monadic_rewrite_bind_tail)
        apply (rule monadic_rewrite_trans)
         apply (rule_tac rv=cteat in monadic_rewrite_gets_known)
        apply (rule_tac rv=tcbat in monadic_rewrite_gets_known)
       apply (wp setEndpoint_typ_at'[where T="koType TYPE(tcb)", unfolded typ_at_to_obj_at']
                 setEndpoint_typ_at'[where T="koType TYPE(cte)", unfolded typ_at_to_obj_at']
                     | simp)+
      apply (rule_tac P="\<lambda>s. epat = ep_at' p s \<and> cteat = real_cte_at' slot s
                           \<and> tcbat = (tcb_at' (slot && ~~ mask 9) and (%y. slot && mask 9 : dom tcb_cte_cases)) s"
                   in monadic_rewrite_pre_imp_eq)
      apply (simp add: setEndpoint_def setObject_modify_assert bind_assoc
                       exec_gets assert_def exec_modify
                split: if_split)
      apply (auto split: if_split simp: obj_at'_def projectKOs objBits_defs
                    del: ext
                 intro!: arg_cong[where f=f] ext kernel_state.fold_congs)[1]
     apply wp+
  apply (simp add: objBits_defs)
  done

lemma setEndpoint_updateMDB_pivot[unfolded K_bind_def]:
  "do setEndpoint p val; updateMDB slot mf; f od =
     do updateMDB slot mf; setEndpoint p val; f od"
  by (clarsimp simp: updateMDB_def bind_assoc
                     setEndpoint_getCTE_pivot
                     setEndpoint_setCTE_pivot
              split: if_split)

lemma setEndpoint_updateCap_pivot[unfolded K_bind_def]:
  "do setEndpoint p val; updateCap slot mf; f od =
     do updateCap slot mf; setEndpoint p val; f od"
  by (clarsimp simp: updateCap_def bind_assoc
                     setEndpoint_getCTE_pivot
                     setEndpoint_setCTE_pivot)

lemma modify_setEndpoint_pivot[unfolded K_bind_def]:
  "\<lbrakk> \<And>ksf s. ksPSpace_update ksf (sf s) = sf (ksPSpace_update ksf s) \<rbrakk>
    \<Longrightarrow> (do modify sf; setEndpoint p val; f od) =
          (do setEndpoint p val; modify sf; f od)"
  apply (subgoal_tac "\<forall>s. ep_at' p (sf s) = ep_at' p s")
   apply (simp add: setEndpoint_def setObject_modify_assert
                    bind_assoc fun_eq_iff
                    exec_gets exec_modify assert_def
             split: if_split)
  apply atomize
  apply clarsimp
  apply (drule_tac x="\<lambda>_. ksPSpace s" in spec)
  apply (drule_tac x="s" in spec)
  apply (drule_tac f="ksPSpace" in arg_cong)
  apply simp
  apply (metis obj_at'_pspaceI)
  done

lemma setEndpoint_clearUntypedFreeIndex_pivot[unfolded K_bind_def]:
  "do setEndpoint p val; v <- clearUntypedFreeIndex slot; f od
     = do v <- clearUntypedFreeIndex slot; setEndpoint p val; f od"
  supply option.case_cong_weak[cong del]
  by (simp add: clearUntypedFreeIndex_def bind_assoc getSlotCap_def setEndpoint_getCTE_pivot
                updateTrackedFreeIndex_def modify_setEndpoint_pivot
         split: capability.split
      | rule bind_cong[OF refl] allI impI bind_apply_cong[OF refl])+

lemma emptySlot_setEndpoint_pivot[unfolded K_bind_def]:
  "(do emptySlot slot NullCap; setEndpoint p val; f od) =
      (do setEndpoint p val; emptySlot slot NullCap; f od)"
  apply (rule ext)
  apply (simp add: emptySlot_def bind_assoc
                   setEndpoint_getCTE_pivot
                   setEndpoint_updateCap_pivot
                   setEndpoint_updateMDB_pivot
                   case_Null_If Retype_H.postCapDeletion_def
                   setEndpoint_clearUntypedFreeIndex_pivot
            split: if_split
              | rule bind_apply_cong[OF refl])+
  done

lemma set_getCTE[unfolded K_bind_def]:
  "do setCTE p cte; v <- getCTE p; f v od
      = do setCTE p cte; f cte od"
  apply (simp add: getCTE_assert_opt bind_assoc)
  apply (rule monadic_rewrite_to_eq)
  apply (rule monadic_rewrite_bind_tail)
   apply (monadic_rewrite_symb_exec_l)
    apply (monadic_rewrite_symb_exec_l_known cte, rule monadic_rewrite_refl)
    apply (wpsimp simp: assert_opt_def wp: gets_wp)+
  done

lemma set_setCTE[unfolded K_bind_def]:
  "do setCTE p val; setCTE p val' od = setCTE p val'"
  supply if_split[split del]
  apply simp
  apply (rule monadic_rewrite_to_eq)
  apply (rule monadic_rewrite_guard_imp)
   apply (rule monadic_rewrite_trans,
          rule_tac f="real_cte_at' p" in monadic_rewrite_add_gets)
   apply (rule monadic_rewrite_transverse, rule monadic_rewrite_add_gets,
          rule monadic_rewrite_bind_tail)
    apply (rule monadic_rewrite_trans,
           rule_tac f="tcb_at' (p && ~~ mask 9) and K (p && mask 9 \<in> dom tcb_cte_cases)"
                  in monadic_rewrite_add_gets)
    apply (rule monadic_rewrite_transverse, rule monadic_rewrite_add_gets,
           rule monadic_rewrite_bind_tail)
     apply (rename_tac cteat tcbat)
     apply (rule monadic_rewrite_trans)
      apply (rule monadic_rewrite_bind_tail)
       apply (simp add: setCTE_assert_modify)
       apply (rule monadic_rewrite_trans, rule_tac rv=cteat in monadic_rewrite_gets_known)
       apply (rule_tac rv=tcbat in monadic_rewrite_gets_known)
      apply (wp setCTE_typ_at'[where T="koType TYPE(tcb)", unfolded typ_at_to_obj_at']
                setCTE_typ_at'[where T="koType TYPE(cte)", unfolded typ_at_to_obj_at']
                  | simp)+
     apply (simp add: setCTE_assert_modify bind_assoc)
     apply (rule monadic_rewrite_bind_tail)+
       apply (rule_tac P="c = cteat \<and> t = tcbat
                           \<and> (tcbat \<longrightarrow>
                                 (\<exists> getF setF. tcb_cte_cases (p && mask 9) = Some (getF, setF)
                                        \<and> (\<forall> f g tcb. setF f (setF g tcb) = setF (f o g) tcb)))"
                   in monadic_rewrite_gen_asm)
       apply (rule monadic_rewrite_is_refl[OF ext])
       apply (simp add: exec_modify split: if_split)
       apply (auto simp: simpler_modify_def projectKO_opt_tcb objBits_defs
                    del: ext
                 intro!: kernel_state.fold_congs ext
                  split: if_split)[1]
      apply wp+
  apply (clarsimp simp: objBits_defs intro!: all_tcbI)
  apply (auto simp: tcb_cte_cases_def split: if_split_asm)
  done

lemma setCTE_updateCapMDB:
  "p \<noteq> 0 \<Longrightarrow>
   setCTE p cte = do updateCap p (cteCap cte); updateMDB p (const (cteMDBNode cte)) od"
  supply if_split[split del]
  apply (simp add: updateCap_def updateMDB_def bind_assoc set_getCTE
                   cte_overwrite set_setCTE)
  apply (simp add: getCTE_assert_opt setCTE_assert_modify bind_assoc)
  apply (rule ext, simp add: exec_gets assert_opt_def exec_modify
                      split: if_split option.split)
  apply (cut_tac P=\<top> and p=p and s=x in cte_wp_at_ctes_of)
  apply (cases cte)
  apply (simp add: cte_wp_at_obj_cases')
  apply (auto simp: mask_out_sub_mask)
  done

lemma clearUntypedFreeIndex_simple_rewrite:
  "monadic_rewrite True False
    (cte_wp_at' (Not o isUntypedCap o cteCap) slot)
        (clearUntypedFreeIndex slot) (return ())"
  apply (simp add: clearUntypedFreeIndex_def getSlotCap_def)
  apply (rule monadic_rewrite_name_pre)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (monadic_rewrite_symb_exec_l_known cte)
    apply (simp split: capability.split, strengthen monadic_rewrite_refl)
    apply (wpsimp wp: getCTE_wp' simp: cte_wp_at_ctes_of)+
  done

lemma emptySlot_replymaster_rewrite[OF refl]:
  "mdbn = cteMDBNode cte \<Longrightarrow>
   monadic_rewrite True False
     ((\<lambda>_. mdbNext mdbn = 0 \<and> mdbPrev mdbn \<noteq> 0)
           and ((\<lambda>_. cteCap cte \<noteq> NullCap)
           and (cte_wp_at' ((=) cte) slot
           and cte_wp_at' (\<lambda>cte. isReplyCap (cteCap cte)) slot
           and cte_wp_at' (\<lambda>cte. isReplyCap (cteCap cte) \<and> capReplyMaster (cteCap cte))
                    (mdbPrev mdbn)
           and (\<lambda>s. reply_masters_rvk_fb (ctes_of s))
           and (\<lambda>s. no_0 (ctes_of s)))))
     (emptySlot slot NullCap)
     (do updateMDB (mdbPrev mdbn) (mdbNext_update (K 0) o mdbFirstBadged_update (K True)
                                              o mdbRevocable_update (K True));
         setCTE slot makeObject
      od)"
  supply if_split[split del]
  apply (rule monadic_rewrite_gen_asm)+
  apply (rule monadic_rewrite_guard_imp)
   apply (rule_tac P="slot \<noteq> 0" in monadic_rewrite_gen_asm)
   apply (clarsimp simp: emptySlot_def setCTE_updateCapMDB)
   apply (monadic_rewrite_l clearUntypedFreeIndex_simple_rewrite, simp)
   apply (monadic_rewrite_symb_exec_l_known cte)
    apply (simp add: updateMDB_def Let_def bind_assoc makeObject_cte case_Null_If)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_bind)
       apply (rule_tac P="mdbFirstBadged (cteMDBNode ctea) \<and> mdbRevocable (cteMDBNode ctea)"
                   in monadic_rewrite_gen_asm)
       apply (rule monadic_rewrite_is_refl)
       apply (case_tac ctea, rename_tac mdbnode, case_tac mdbnode)
       apply simp
      apply (simp add: Retype_H.postCapDeletion_def)
      apply (rule monadic_rewrite_refl)
     apply (solves wp | wp getCTE_wp')+
  apply (clarsimp simp: cte_wp_at_ctes_of reply_masters_rvk_fb_def)
  apply (fastforce simp: isCap_simps)
  done

lemma all_prio_not_inQ_not_tcbQueued: "\<lbrakk> obj_at' (\<lambda>a. (\<forall>d p. \<not> inQ d p a)) t s \<rbrakk> \<Longrightarrow> obj_at' (\<lambda>a. \<not> tcbQueued a) t s"
  apply (clarsimp simp: obj_at'_def inQ_def)
  done

crunch setThreadState, emptySlot, asUser
  for ntfn_obj_at[wp]: "obj_at' (P::(Structures_H.notification \<Rightarrow> bool)) ntfnptr"
  (wp: obj_at_setObject2 crunch_wps
   simp: crunch_simps updateObject_default_def in_monad)

lemma st_tcb_at_is_Reply_imp_not_tcbQueued:
  "\<And>s t. \<lbrakk> ready_qs_runnable s; st_tcb_at' isReply t s\<rbrakk>  \<Longrightarrow> obj_at' (\<lambda>tcb. \<not> tcbQueued tcb) t s"
  apply (clarsimp simp: ready_qs_runnable_def)
  apply (drule_tac x=t in spec)
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def isReply_def)
  apply (case_tac "tcbState obj"; clarsimp)
  done

lemma valid_objs_ntfn_at_tcbBoundNotification:
  "ko_at' tcb t s \<Longrightarrow> valid_objs' s \<Longrightarrow> tcbBoundNotification tcb \<noteq> None
   \<Longrightarrow> ntfn_at' (the (tcbBoundNotification tcb)) s"
  apply (drule(1) ko_at_valid_objs', simp add: projectKOs)
  apply (simp add: valid_obj'_def valid_tcb'_def valid_bound_ntfn'_def)
  apply clarsimp
  done

crunch setThreadState
  for bound_tcb_at'_Q[wp]: "\<lambda>s. Q (bound_tcb_at' P t s)"
  (wp: threadSet_pred_tcb_no_state crunch_wps simp: unless_def)

lemmas emptySlot_pred_tcb_at'_Q[wp] = lift_neg_pred_tcb_at'[OF emptySlot_typ_at' emptySlot_pred_tcb_at']

lemma emptySlot_tcb_at'[wp]:
  "\<lbrace>\<lambda>s. Q (tcb_at' t s)\<rbrace> emptySlot a b \<lbrace>\<lambda>_ s. Q (tcb_at' t s)\<rbrace>"
  by (simp add: tcb_at_typ_at', wp)

lemmas cnode_caps_gsCNodes_lift
    = hoare_lift_Pf2[where P="\<lambda>gs s. cnode_caps_gsCNodes (f s) gs" and f=gsCNodes for f]
    hoare_lift_Pf2[where P="\<lambda>gs s. Q s \<longrightarrow> cnode_caps_gsCNodes (f s) gs" and f=gsCNodes for f Q]

lemma resolveAddressBitsFn_eq_name_slot:
  "monadic_rewrite F E (\<lambda>s. (isCNodeCap cap \<longrightarrow> cte_wp_at' (\<lambda>cte. cteCap cte = cap) (slot s) s)
        \<and> valid_objs' s \<and> cnode_caps_gsCNodes' s)
    (resolveAddressBits cap capptr bits)
    (gets (resolveAddressBitsFn cap capptr bits o only_cnode_caps o ctes_of))"
  apply (rule monadic_rewrite_guard_imp, rule resolveAddressBitsFn_eq)
  apply auto
  done

crunch asUser
  for bound_tcb_at'_Q[wp]: "\<lambda>s. Q (bound_tcb_at' P t s)"
  (simp: crunch_simps wp: threadSet_pred_tcb_no_state crunch_wps)


lemma asUser_tcb_at'_Q[wp]:
  "\<lbrace>\<lambda>s. Q (tcb_at' t s)\<rbrace> asUser a b \<lbrace>\<lambda>_ s. Q (tcb_at' t s)\<rbrace>"
  by (simp add: tcb_at_typ_at', wp)

lemma active_ntfn_check_wp:
  "\<lbrace>\<lambda>s. Q (\<exists>ntfnptr. bound_tcb_at' ((=) (Some ntfnptr)) thread s
      \<and> \<not> obj_at' (Not o isActive) ntfnptr s) s \<rbrace> do bound_ntfn \<leftarrow> getBoundNotification thread;
      case bound_ntfn of None \<Rightarrow> return False
       | Some ntfnptr \<Rightarrow> liftM EndpointDecls_H.isActive $ getNotification ntfnptr
   od \<lbrace>Q\<rbrace>"
  apply (rule hoare_pre)
   apply (wp getNotification_wp gbn_wp' | wpc)+
  apply (auto simp: pred_tcb_at'_def obj_at'_def projectKOs)
  done

lemma tcbSchedEnqueue_tcbIPCBuffer:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbIPCBuffer tcb)) t\<rbrace>
  tcbSchedEnqueue t'
  \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbIPCBuffer tcb)) t\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def tcbQueuePrepend_def unless_when)
  apply (wp threadSet_obj_at' hoare_drop_imps threadGet_wp
        |simp split: if_split)+
  done

crunch rescheduleRequired
  for obj_at'_tcbIPCBuffer[wp]: "obj_at' (\<lambda>tcb. P (tcbIPCBuffer tcb)) t"
  (wp: crunch_wps tcbSchedEnqueue_tcbIPCBuffer simp: rescheduleRequired_def)

context
notes if_cong[cong]
begin
crunch setThreadState
  for obj_at'_tcbIPCBuffer[wp]: "obj_at' (\<lambda>tcb. P (tcbIPCBuffer tcb)) t"
  (wp: crunch_wps threadSet_obj_at'_really_strongest)

crunch handleFault
  for obj_at'_tcbIPCBuffer[wp]: "obj_at' (\<lambda>tcb. P (tcbIPCBuffer tcb)) t"
  (wp: crunch_wps constOnFailure_wp tcbSchedEnqueue_tcbIPCBuffer threadSet_obj_at'_really_strongest
   simp: zipWithM_x_mapM)
end

crunch emptySlot
  for obj_at'_tcbIPCBuffer[wp]: "obj_at' (\<lambda>tcb. P (tcbIPCBuffer tcb)) t"
  (wp: crunch_wps)

(* FIXME move *)
crunch getBoundNotification
  for (no_fail) no_fail[intro!, wp, simp]

lemma threadSet_tcb_at'[wp]:
  "threadSet f t' \<lbrace>\<lambda>s. P (tcb_at' addr s)\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (erule rsubst[where P=P])
  by (clarsimp simp: obj_at'_def projectKOs ps_clear_upd objBits_simps)

crunch rescheduleRequired, tcbSchedDequeue, setThreadState, setBoundNotification
  for tcb''[wp]: "\<lambda>s. P (tcb_at' addr s)"
  (wp: crunch_wps)

lemma fastpath_callKernel_SysReplyRecv_corres:
  "monadic_rewrite True False
     (invs' and ct_in_state' ((=) Running) and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
         and cnode_caps_gsCNodes' and ready_qs_runnable)
     (callKernel (SyscallEvent SysReplyRecv)) (fastpaths SysReplyRecv)"
  including classic_wp_pre
  supply if_cong[cong] option.case_cong[cong]
  supply if_split[split del]
  supply user_getreg_inv[wp] (* FIXME *)
  apply (rule monadic_rewrite_introduce_alternative[OF callKernel_def[simplified atomize_eq]])
  apply (rule monadic_rewrite_guard_imp)
   apply (rule monadic_rewrite_bind_alternative_l, wpsimp)
   apply (rule monadic_rewrite_stateAssert)
   apply (simp add: handleEvent_def handleReply_def
                    handleRecv_def liftE_bindE_handle liftE_handle
                    bind_assoc getMessageInfo_def liftE_bind)
   apply (simp add: catch_liftE_bindE unlessE_throw_catch_If
                    unifyFailure_catch_If catch_liftE
                    getMessageInfo_def alternative_bind
                    fastpaths_def getThreadCallerSlot_def
                    locateSlot_conv capability_case_Null_ReplyCap
                    getThreadCSpaceRoot_def
              cong: if_cong)
   apply (rule monadic_rewrite_bind_alternative_l, wp)
   apply (rule monadic_rewrite_bind_tail)
    apply monadic_rewrite_symb_exec_r
     apply (rename_tac msgInfo)
     apply monadic_rewrite_symb_exec_r
      apply monadic_rewrite_symb_exec_r
       apply (rename_tac tcbFault)
       apply (rule monadic_rewrite_alternative_r[rotated])
        apply (rule monadic_rewrite_alternative_l)
       apply (rule monadic_rewrite_if_r[rotated])
        apply (rule monadic_rewrite_alternative_l)
       apply (simp add: lookupCap_def liftME_def lookupCapAndSlot_def
                        lookupSlotForThread_def bindE_assoc
                        split_def getThreadCSpaceRoot_def
                        locateSlot_conv liftE_bindE bindE_bind_linearise
                        capFaultOnFailure_def rethrowFailure_injection
                        injection_handler_catch bind_bindE_assoc
                        getThreadCallerSlot_def bind_assoc
                        getSlotCap_def case_bool_If
                        isRight_def[where x="Inr v" for v]
                        isRight_def[where x="Inl v" for v]
                  cong: if_cong)
       apply monadic_rewrite_symb_exec_r
        apply (rename_tac "cTableCTE")
        apply (rule monadic_rewrite_transverse,
               monadic_rewrite_l resolveAddressBitsFn_eq wpsimp, rule monadic_rewrite_refl)
        apply monadic_rewrite_symb_exec_r
         apply (rename_tac "rab_ret")

         apply (rule_tac P="isRight rab_ret" in monadic_rewrite_cases[rotated])
          apply (case_tac rab_ret, simp_all add: isRight_def)[1]
          apply (rule monadic_rewrite_alternative_l)
         apply clarsimp
         apply (simp add: isRight_case_sum liftE_bind
                          isRight_def[where x="Inr v" for v])
         apply monadic_rewrite_symb_exec_r
          apply (rename_tac ep_cap)
          apply (rule monadic_rewrite_if_r[rotated])
           apply (rule monadic_rewrite_alternative_l)
          apply (monadic_rewrite_symb_exec
                   \<open>rule monadic_rewrite_symb_exec_r_nE[OF _ _ _ active_ntfn_check_wp, unfolded bind_assoc fun_app_def]\<close>
                   \<open>wpsimp simp: getBoundNotification_def wp: threadGet_wp\<close>)
          apply (rename_tac ep)
          apply (rule monadic_rewrite_if_r[rotated])
           apply (rule monadic_rewrite_alternative_l)
          apply monadic_rewrite_symb_exec_r
           apply (rename_tac ep)
           apply (rule monadic_rewrite_if_r[rotated])
            apply (rule monadic_rewrite_alternative_l)
           apply (rule monadic_rewrite_bind_alternative_l, wp)
           apply (rule monadic_rewrite_bind_tail)
            apply (rename_tac replyCTE)
            apply (rule monadic_rewrite_if_r[rotated])
             apply (rule monadic_rewrite_alternative_l)
            apply (simp add: bind_assoc)
            apply (rule monadic_rewrite_bind_alternative_l, wp assert_inv)
            apply (rule monadic_rewrite_assert)
            apply monadic_rewrite_symb_exec_r
             apply (rule monadic_rewrite_if_r[rotated])
              apply (rule monadic_rewrite_alternative_l)
             apply (simp add: getThreadVSpaceRoot_def locateSlot_conv)
             apply monadic_rewrite_symb_exec_r
              apply (rename_tac vTableCTE)
              apply (rule monadic_rewrite_if_r[rotated])
               apply (rule monadic_rewrite_alternative_l)

              apply monadic_rewrite_symb_exec_r
               apply monadic_rewrite_symb_exec_r
                apply (simp add: isHighestPrio_def')
                apply monadic_rewrite_symb_exec_r
                 apply (rule monadic_rewrite_if_r[rotated])
                  apply (rule monadic_rewrite_alternative_l)

                 apply monadic_rewrite_symb_exec_r
                  apply (rule monadic_rewrite_if_r[rotated])
                   apply (rule monadic_rewrite_alternative_l)
                  apply monadic_rewrite_symb_exec_r
                   apply (rule monadic_rewrite_if_r[rotated])
                    apply (rule monadic_rewrite_alternative_l)
                   apply (rule monadic_rewrite_trans,
                              rule monadic_rewrite_pick_alternative_1)
                   (* now committed to fastpath *)
                   apply (rule_tac P="\<lambda>v.  obj_at' (%tcb. tcbIPCBuffer tcb = v) (capTCBPtr (cteCap replyCTE))"
                         in monadic_rewrite_exists_v)
                   apply (rename_tac ipcBuffer)

                   apply (simp add: ARM_HYP_H.switchToThread_def bind_assoc)
                   apply (rule monadic_rewrite_trans[OF _ monadic_rewrite_transverse])

                     apply (rule monadic_rewrite_bind monadic_rewrite_refl)+
                          apply (wp mapM_x_wp' getObject_inv | wpc | simp add:
                            | wp (once) hoare_drop_imps )+

                    apply (rule monadic_rewrite_bind monadic_rewrite_refl)+
                                 apply (wp setCTE_obj_at'_tcbIPCBuffer assert_inv mapM_x_wp' getObject_inv | wpc | simp
                                   | wp (once) hoare_drop_imps )+

                   apply (rule monadic_rewrite_trans)
                    apply (rule monadic_rewrite_trans)
                     apply (rule monadic_rewrite_bind_head)
                     apply (rule monadic_rewrite_trans)
                      apply (rule doReplyTransfer_simple)
                     apply simp
                     apply (((rule monadic_rewrite_weaken_flags',
                             (rule_tac msgInfo=msgInfo in doIPCTransfer_simple_rewrite
                           | rule_tac destPrio=callerPrio
                                            and curDom=curDom and destDom=callerDom
                                            and thread=thread in possibleSwitchTo_rewrite))
                           | rule cteDeleteOne_replycap_rewrite
                           | rule monadic_rewrite_bind monadic_rewrite_refl
                           | wp assert_inv mapM_x_wp' sts_valid_objs'
                                asUser_obj_at_unchanged
                                hoare_strengthen_post[OF _ obj_at_conj'[simplified atomize_conjL], rotated]
                                 lookupBitmapPriority_lift
                                 setThreadState_runnable_bitmap_inv
                           | simp add: setMessageInfo_def setThreadState_runnable_simp
                           | wp (once) hoare_vcg_disj_lift)+)[1]
                    apply (simp add: setMessageInfo_def)
                    apply (rule monadic_rewrite_bind_tail)
                     apply (rename_tac unblocked)
                     apply (monadic_rewrite_symb_exec_l_known thread)
                      apply (monadic_rewrite_symb_exec_l_known cptr)
                       apply (rule monadic_rewrite_bind)
                         apply (rule monadic_rewrite_catch[OF _ monadic_rewrite_refl wp_post_tautE_E])
                         apply monadic_rewrite_symb_exec_l
                          apply (rename_tac cTableCTE2,
                                 rule_tac P="cteCap cTableCTE2 = cteCap cTableCTE"
                                   in monadic_rewrite_gen_asm)
                          apply simp
                          apply (rule monadic_rewrite_trans,
                                 rule monadic_rewrite_bindE[OF _ monadic_rewrite_refl])
                            apply (rule_tac slot="\<lambda>s. ksCurThread s + 2 ^ cte_level_bits * tcbCTableSlot"
                                     in resolveAddressBitsFn_eq_name_slot)
                           apply wp
                          apply (rule monadic_rewrite_trans)
                           apply (rule_tac rv=rab_ret
                                    in monadic_rewrite_gets_known[where m="Nondet_Monad.lift f"
                                    for f, folded bindE_def])
                          apply (simp add: Nondet_Monad.lift_def isRight_case_sum)
                          apply monadic_rewrite_symb_exec_l
                           apply (rename_tac ep_cap2)
                           apply (rule_tac P="cteCap ep_cap2 = cteCap ep_cap" in monadic_rewrite_gen_asm)
                           apply (simp add: cap_case_EndpointCap_NotificationCap)
                           apply (rule monadic_rewrite_liftE)
                           apply (rule monadic_rewrite_trans)
                            apply (rule monadic_rewrite_bind)
                              apply (rule deleteCallerCap_nullcap_rewrite)
                             apply (rule_tac ep=ep in receiveIPC_simple_rewrite)
                            apply (wp, simp)
                           apply (rule monadic_rewrite_bind_head)

                           apply (rule monadic_rewrite_weaken_flags[where E=True and F=True], simp)
                           apply (rule setThreadState_rewrite_simple)
                          apply clarsimp
                          apply (wp getCTE_known_cap)+
                        apply (rule monadic_rewrite_bind)
                          apply (rule_tac t="capTCBPtr (cteCap replyCTE)"
                                      and t'=thread
                                       in schedule_known_rewrite)
                         apply (rule monadic_rewrite_weaken_flags[where E=True and F=True], simp)
                         apply (rule monadic_rewrite_bind)
                           apply (rule activateThread_simple_rewrite)
                          apply (rule monadic_rewrite_refl)
                         apply wp
                        apply wp
                         apply (simp add: ct_in_state'_def, simp add: ct_in_state'_def[symmetric])
                         apply ((wp setCurThread_ct_in_state[folded st_tcb_at'_def]
                                    Arch_switchToThread_pred_tcb')+)[2]
                       apply (simp add: catch_liftE)
                       apply ((wpsimp wp: user_getreg_rv setEndpoint_obj_at_tcb'
                                          threadSet_pred_tcb_at_state[unfolded if_bool_eq_conj]
                                          fastpathBestSwitchCandidate_lift[where f="setEndpoint a b" for a b]
                                          fastpathBestSwitchCandidate_lift[where f="threadSet f t" for f t]
                               | wps)+)[3]
                    apply (simp cong: rev_conj_cong)
                    apply (wpsimp wp: setThreadState_tcbContext[simplified comp_apply]
                                      user_getreg_rv
                                      setThreadState_no_sch_change sts_valid_objs'
                                      sts_st_tcb_at'_cases sts_bound_tcb_at'
                                      fastpathBestSwitchCandidate_lift[where f="setThreadState s t" for s t]
                                      hoare_weak_lift_imp hoare_vcg_all_lift hoare_vcg_imp_lift
                                      hoare_weak_lift_imp cnode_caps_gsCNodes_lift
                                      hoare_vcg_ex_lift
                          | wps)+
                           apply (strengthen imp_consequent[where Q="tcb_at' t s" for t s])
                           apply ((wp user_getreg_rv setThreadState_no_sch_change
                                      sts_st_tcb_at'_cases sts_bound_tcb_at'
                                      emptySlot_obj_at'_not_queued emptySlot_obj_at_ep
                                      emptySlot_tcbContext[simplified comp_apply]
                                      emptySlot_cte_wp_at_cteCap
                                      emptySlot_cnode_caps
                                      user_getreg_inv asUser_typ_ats
                                      asUser_obj_at_not_queued asUser_obj_at' mapM_x_wp'
                                      hoare_weak_lift_imp hoare_vcg_all_lift hoare_vcg_imp_lift
                                      hoare_weak_lift_imp cnode_caps_gsCNodes_lift
                                      hoare_vcg_ex_lift
                                      fastpathBestSwitchCandidate_lift[where f="emptySlot a b" for a b]
                                   | simp del: comp_apply
                                   | clarsimp simp: obj_at'_weakenE[OF _ TrueI]
                                   | wps)+)

                            apply (wpsimp wp: fastpathBestSwitchCandidate_lift[where f="asUser a b" for a b])+
                           apply (clarsimp cong: conj_cong)
                           apply ((wp user_getreg_inv asUser_typ_ats
                                      asUser_obj_at_not_queued asUser_obj_at' mapM_x_wp'
                                      hoare_weak_lift_imp hoare_vcg_all_lift hoare_vcg_imp_lift
                                      hoare_weak_lift_imp cnode_caps_gsCNodes_lift
                                      hoare_vcg_ex_lift
                                   | clarsimp simp: obj_at'_weakenE[OF _ TrueI]
                                   | solves \<open>
                                       wp fastpathBestSwitchCandidate_lift[where f="asUser a b" for a b]
                                       \<close>)+)

                          apply (clarsimp | wp getCTE_wp' gts_imp')+

                   apply (simp add: ARM_HYP_H.switchToThread_def getTCB_threadGet bind_assoc)
                   apply (rule monadic_rewrite_trans[OF _ monadic_rewrite_transverse])

                     apply (rule monadic_rewrite_bind monadic_rewrite_refl)+
                                       apply (wp mapM_x_wp' handleFault_obj_at'_tcbIPCBuffer getObject_inv | wpc | simp
                                         | wp (once) hoare_drop_imps )+
                    apply (rule monadic_rewrite_bind monadic_rewrite_refl)+
                                 apply (wp setCTE_obj_at'_tcbIPCBuffer assert_inv mapM_x_wp' getObject_inv | wpc | simp
                                   | wp (once) hoare_drop_imps )+

                   apply (simp add: bind_assoc catch_liftE
                                    receiveIPC_def Let_def liftM_def
                                    setThreadState_runnable_simp)
                   apply monadic_rewrite_symb_exec_l
                    apply (rule monadic_rewrite_assert)

                    apply (rule_tac P="inj (case_bool thread (capTCBPtr (cteCap replyCTE)))"
                                    in monadic_rewrite_gen_asm)
                    apply (rule monadic_rewrite_trans[OF _ monadic_rewrite_transverse])
                      apply (rule monadic_rewrite_weaken_flags[where F=False and E=True], simp)
                      apply (rule isolate_thread_actions_rewrite_bind
                                  fastpath_isolate_rewrites fastpath_isolatables
                                  bool.simps setRegister_simple_modify_registers
                                  zipWithM_setRegister_simple_modify_registers
                                  thread_actions_isolatable_bind
                                  thread_actions_isolatableD[OF setCTE_isolatable]
                                  setCTE_isolatable
                                  threadGet_vcpu_isolatable[THEN thread_actions_isolatableD, simplified o_def]
                                  threadGet_vcpu_isolatable[simplified o_def]
                                  vcpuSwitch_isolatable[THEN thread_actions_isolatableD] vcpuSwitch_isolatable
                                  setVMRoot_isolatable[THEN thread_actions_isolatableD] setVMRoot_isolatable
                                  doMachineOp_isolatable[THEN thread_actions_isolatableD] doMachineOp_isolatable
                                  kernelExitAssertions_isolatable[THEN thread_actions_isolatableD]
                                  kernelExitAssertions_isolatable
                           | assumption
                           | wp assert_inv)+
                    apply (simp only: )
                    apply (rule_tac P="(\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
                                       and tcb_at' thread
                                       and (cte_wp_at' (\<lambda>cte. isReplyCap (cteCap cte))
                                                (thread + 2 ^ cte_level_bits * tcbCallerSlot)
                                       and (\<lambda>s. \<forall>x. tcb_at' (case_bool thread (capTCBPtr (cteCap replyCTE)) x) s)
                                       and valid_mdb')"
                                and F=True and E=False in monadic_rewrite_weaken_flags)
                    apply (rule monadic_rewrite_isolate_final2)
                       apply simp
                       apply monadic_rewrite_symb_exec_l
                        apply (rename_tac callerCTE)
                        apply (rule monadic_rewrite_assert)
                        apply monadic_rewrite_symb_exec_l
                         apply (rule monadic_rewrite_assert)
                         apply (simp add: emptySlot_setEndpoint_pivot)
                         apply (rule monadic_rewrite_bind)
                           apply (rule monadic_rewrite_is_refl)
                           apply (clarsimp simp: isSendEP_def split: Structures_H.endpoint.split)
                          apply (monadic_rewrite_symb_exec_r_known callerCTE)
                           apply (rule monadic_rewrite_trans, rule monadic_rewrite_bind_head,
                                       rule_tac cte=callerCTE in emptySlot_replymaster_rewrite)
                           apply (simp add: bind_assoc o_def)
                           apply (rule monadic_rewrite_refl)
                          apply (simp add: cte_wp_at_ctes_of pred_conj_def)
                          apply (clarsimp | wp getCTE_ctes_wp)+
                      apply (clarsimp simp: zip_map2 zip_same_conv_map foldl_map
                                            foldl_fun_upd
                                            foldr_copy_register_tsrs
                                            isRight_case_sum
                                      cong: if_cong)
                      apply (clarsimp simp: fun_eq_iff if_flip
                                      cong: if_cong)
                      apply (drule obj_at_ko_at', clarsimp)
                      apply (frule get_tcb_state_regs_ko_at')
                      apply (clarsimp simp: zip_map2 zip_same_conv_map foldl_map
                                            foldl_fun_upd
                                            foldr_copy_register_tsrs
                                            isRight_case_sum
                                      cong: if_cong)
                      apply (simp add: upto_enum_def fromEnum_def
                                       enum_register toEnum_def
                                       msgRegisters_unfold
                                 cong: if_cong)
                      apply (clarsimp split: if_split)
                      apply (rule ext)
                      apply (simp add: badgeRegister_def msgInfoRegister_def
                                       ARM_HYP.msgInfoRegister_def
                                       ARM_HYP.badgeRegister_def
                                 cong: if_cong
                                split: if_split)
                     apply simp
                    apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps
                                          map_to_ctes_partial_overwrite)
                    apply (simp add: valid_mdb'_def valid_mdb_ctes_def)
                   apply simp
                   apply (simp cong: if_cong bool.case_cong
                          | rule getCTE_wp' gts_wp' threadGet_wp
                                 getEndpoint_wp gets_wp
                                 user_getreg_wp
                                 gets_the_wp gct_wp getNotification_wp
                                 return_wp liftM_wp gbn_wp'
                          | (simp only: curDomain_def, wp)[1])+

  apply clarsimp
  apply (subgoal_tac "ksCurThread s \<noteq> ksIdleThread s")
   prefer 2
   apply (fastforce simp: ct_in_state'_def dest: ct_running_not_idle' elim: pred_tcb'_weakenE)

  apply (clarsimp simp: ct_in_state'_def pred_tcb_at')
  apply (subst tcb_at_cte_at_offset,
         erule obj_at'_weakenE[OF _ TrueI],
         simp add: tcb_cte_cases_def cte_level_bits_def tcbSlots)
  apply (clarsimp simp: valid_objs_ntfn_at_tcbBoundNotification
                        invs_valid_objs' if_apply_def2)
  apply (rule conjI[rotated])
   apply (fastforce elim: cte_wp_at_weakenE')
  apply (clarsimp simp: isRight_def)
  apply (frule cte_wp_at_valid_objs_valid_cap', clarsimp+)
  apply (frule resolveAddressBitsFn_real_cte_at',
    (clarsimp | erule cte_wp_at_weakenE')+)
  apply (frule real_cte_at', clarsimp)
  apply (frule cte_wp_at_valid_objs_valid_cap', clarsimp,
         clarsimp simp: isCap_simps, simp add: valid_cap_simps')
  apply (clarsimp simp: maskCapRights_def isCap_simps)
  apply (frule_tac p="p' + 2 ^ cte_level_bits * tcbCallerSlot" for p'
              in cte_wp_at_valid_objs_valid_cap', clarsimp+)
  apply (clarsimp simp: valid_cap_simps')
  apply (subst tcb_at_cte_at_offset,
         assumption, simp add: tcb_cte_cases_def cte_level_bits_def tcbSlots)
  apply (clarsimp simp: inj_case_bool cte_wp_at_ctes_of
                        length_msgRegisters
                        order_less_imp_le
                        tcb_at_invs' invs_mdb'
                 split: bool.split)
  apply (subst imp_disjL[symmetric], intro allI impI)
  apply (clarsimp simp: inj_case_bool cte_wp_at_ctes_of
                        length_msgRegisters size_msgRegisters_def order_less_imp_le
                        tcb_at_invs' invs_mdb'
                 split: bool.split)

  apply (subgoal_tac "fastpathBestSwitchCandidate v0a s")
   prefer 2
   apply normalise_obj_at'
   apply (rule_tac ttcb=tcba and ctcb=tcb in fastpathBestSwitchCandidateI)
     apply (erule disjE, blast, blast)
    apply simp+

  apply (clarsimp simp: obj_at_tcbs_of tcbSlots
                        cte_level_bits_def)
  apply (frule(1) st_tcb_at_is_Reply_imp_not_tcbQueued)
  apply (frule invs_pspace_aligned')
  apply (frule invs_pspace_distinct')
  apply (auto simp: obj_at_tcbs_of tcbSlots projectKOs
                        cte_level_bits_def)
  done

end

lemma cnode_caps_gsCNodes_from_sr:
  "\<lbrakk> valid_objs s; (s, s') \<in> state_relation \<rbrakk> \<Longrightarrow> cnode_caps_gsCNodes' s'"
  apply (clarsimp simp: cnode_caps_gsCNodes_def only_cnode_caps_def
                        o_def ran_map_option)
  apply (safe, simp_all)
  apply (clarsimp elim!: ranE)
  apply (frule(1) pspace_relation_cte_wp_atI[rotated])
   apply clarsimp
  apply (clarsimp simp: is_cap_simps)
  apply (frule(1) cte_wp_at_valid_objs_valid_cap)
  apply (clarsimp simp: valid_cap_simps cap_table_at_gsCNodes_eq)
  done

end
