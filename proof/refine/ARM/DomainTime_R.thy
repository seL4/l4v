(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory DomainTime_R
imports
  ADT_H
begin

text {* Preservation of domain time remaining over kernel invocations;
        invariance of domain list validity
*}

context begin interpretation Arch . (*FIXME: arch_split*)

(* FIXME move to DetSchedDomainTime_AI *)
crunch domain_list_inv[wp]: do_user_op "\<lambda>s. P (domain_list s)"
  (wp: select_wp)

(* abstract and haskell have identical domain list fields *)
abbreviation
  valid_domain_list' :: "'a kernel_state_scheme \<Rightarrow> bool"
where
  "valid_domain_list' \<equiv> \<lambda>s. valid_domain_list_2 (ksDomSchedule s)"

lemmas valid_domain_list'_def = valid_domain_list_2_def

(* first, crunching valid_domain_list' over the kernel - it is never changed *)

crunch ksDomSchedule_inv[wp]:
  sendFaultIPC, handleFault, replyFromKernel
  "\<lambda>s. P (ksDomSchedule s)"

crunch ksDomSchedule_inv[wp]: setDomain "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps simp: if_apply_def2)

crunch ksDomSchedule_inv[wp]: sendSignal "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps simp: crunch_simps simp: unless_def)

crunch ksDomSchedule_inv[wp]: finaliseCap "\<lambda>s. P (ksDomSchedule s)"
  (simp: crunch_simps assertE_def unless_def
 ignore: getObject setObject forM ignoreFailure
     wp: getObject_inv loadObject_default_inv crunch_wps)

crunch ksDomSchedule_inv[wp]: finaliseCap, capSwapForDelete "\<lambda>s. P (ksDomSchedule s)"
  (simp: crunch_simps simp: unless_def)

lemma finaliseSlot_ksDomSchedule_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s) \<rbrace> finaliseSlot param_a param_b \<lbrace>\<lambda>_ s. P (ksDomSchedule s)\<rbrace>"
  by (wp finaliseSlot_preservation | clarsimp)+

crunch ksDomSchedule_inv[wp]: invokeTCB "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps checkCap_inv finaliseSlot'_preservation simp: if_apply_def2 crunch_simps)

crunch ksDomSchedule_inv[wp]: doReplyTransfer "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps transferCapsToSlots_pres1 setObject_ep_ct
       setObject_ntfn_ct
        simp: unless_def crunch_simps
      ignore: transferCapsToSlots setObject getObject)

lemma cteRevoke_ksDomSchedule_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s) \<rbrace> cteRevoke param_a \<lbrace>\<lambda>_ s. P (ksDomSchedule s)\<rbrace>"
  by (wp cteRevoke_preservation | clarsimp)+

crunch ksDomSchedule_inv[wp]: finaliseCap "\<lambda>s. P (ksDomSchedule s)"
  (simp: crunch_simps assertE_def unless_def
 ignore: getObject setObject forM ignoreFailure
     wp: getObject_inv loadObject_default_inv crunch_wps)

crunch ksDomSchedule_inv[wp]: cancelBadgedSends "\<lambda>s. P (ksDomSchedule s)"
  (ignore: filterM setObject getObject
     simp: filterM_mapM crunch_simps
       wp: crunch_wps hoare_unless_wp)

crunch ksDomSchedule_inv[wp]: createNewObjects "\<lambda>s. P (ksDomSchedule s)"
  (simp: crunch_simps zipWithM_x_mapM wp: crunch_wps hoare_unless_wp)

crunch ksDomSchedule_inv[wp]: preemptionPoint "\<lambda>s. P (ksDomSchedule s)"
  (simp: whenE_def)

crunch ksDomSchedule_inv[wp]: performARMMMUInvocation "\<lambda>s. P (ksDomSchedule s)"
  (ignore: getObject setObject
   wp: crunch_wps getObject_cte_inv getASID_wp
   simp: unless_def)

crunch ksDomSchedule_inv[wp]: performInvocation "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps zipWithM_x_inv cteRevoke_preservation mapME_x_inv_wp
   simp: unless_def crunch_simps filterM_mapM)

crunch ksDomSchedule_inv[wp]: schedule "\<lambda>s. P (ksDomSchedule s)"
  (ignore: setNextPC threadSet simp:crunch_simps wp:findM_inv)

crunch ksDomSchedule_inv[wp]: activateThread "\<lambda>s. P (ksDomSchedule s)"

crunch ksDomSchedule_inv[wp]:
  receiveSignal, getNotification, receiveIPC, deleteCallerCap "\<lambda>s. P (ksDomSchedule s)"
  (wp: hoare_drop_imps simp: crunch_simps)

lemma handleRecv_ksDomSchedule_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s) \<rbrace> handleRecv e \<lbrace>\<lambda>_ s. P (ksDomSchedule s) \<rbrace>"
  unfolding handleRecv_def
  by (rule hoare_pre)
     (wp hoare_drop_imps | simp add: crunch_simps | wpc)+

crunch ksDomSchedule_inv[wp]: handleEvent "\<lambda>s. P (ksDomSchedule s)"
  (wp: hoare_drop_imps hv_inv' syscall_valid' throwError_wp withoutPreemption_lift
   simp: runErrorT_def
   ignore: setThreadState)

lemma callKernel_ksDomSchedule_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s) \<rbrace> callKernel e \<lbrace>\<lambda>_ s. P (ksDomSchedule s) \<rbrace>"
  unfolding callKernel_def
  by (rule hoare_pre)
     (wp | simp add: if_apply_def2)+


(* now we handle preservation of domain time remaining, which most of the kernel does not change *)

crunch ksDomainTime[wp]: setExtraBadge, cteInsert "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps)

crunch ksDomainTime[wp]: transferCapsToSlots "\<lambda>s. P (ksDomainTime s)"

crunch ksDomainTime[wp]: setupCallerCap, switchIfRequiredTo, doIPCTransfer, attemptSwitchTo "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: constOnFailure)

crunch ksDomainTime_inv[wp]: setEndpoint, setNotification, storePTE, storePDE
  "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps setObject_ksPSpace_only updateObject_default_inv
   ignore: setObject)

crunch ksDomainTime_inv[wp]: sendFaultIPC, handleFault, replyFromKernel "\<lambda>s. P (ksDomainTime s)"

crunch ksDomainTime_inv[wp]: setDomain "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps simp: if_apply_def2)

crunch ksDomainTime_inv[wp]: sendSignal "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps simp: crunch_simps simp: unless_def)

crunch ksDomainTime_inv[wp]: deleteASID "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps setObject_ksPSpace_only getObject_inv loadObject_default_inv
       updateObject_default_inv
   ignore: setObject getObject simp: whenE_def)

crunch ksDomainTime_inv[wp]: finaliseCap "\<lambda>s. P (ksDomainTime s)"
  (simp: crunch_simps assertE_def unless_def
 ignore: getObject setObject forM ignoreFailure
     wp: setObject_ksPSpace_only getObject_inv loadObject_default_inv crunch_wps)

crunch ksDomainTime_inv[wp]: cancelBadgedSends "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps setObject_ksPSpace_only getObject_inv loadObject_default_inv
       updateObject_default_inv hoare_unless_wp
   ignore: setObject getObject filterM
   simp: whenE_def filterM_mapM crunch_simps)

crunch ksDomainTime_inv[wp]: capSwapForDelete "\<lambda>s. P (ksDomainTime s)"
  (simp: crunch_simps simp: unless_def)

lemma finaliseSlot_ksDomainTime_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksDomainTime s) \<rbrace> finaliseSlot param_a param_b \<lbrace>\<lambda>_ s. P (ksDomainTime s)\<rbrace>"
  by (wp finaliseSlot_preservation | clarsimp)+

crunch ksDomainTime_inv[wp]: invokeTCB "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps checkCap_inv finaliseSlot'_preservation simp: if_apply_def2 crunch_simps)

crunch ksDomainTime_inv[wp]: doReplyTransfer "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps transferCapsToSlots_pres1 setObject_ep_ct
       setObject_ntfn_ct
        simp: unless_def crunch_simps
      ignore: transferCapsToSlots setObject getObject)

lemma cteRevoke_ksDomainTime_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksDomainTime s) \<rbrace> cteRevoke param_a \<lbrace>\<lambda>_ s. P (ksDomainTime s)\<rbrace>"
  by (wp cteRevoke_preservation | clarsimp)+

crunch ksDomainTime_inv[wp]: finaliseCap "\<lambda>s. P (ksDomainTime s)"
  (simp: crunch_simps assertE_def unless_def
 ignore: getObject setObject forM ignoreFailure
     wp: getObject_inv loadObject_default_inv crunch_wps)

crunch ksDomainTime_inv[wp]: cancelBadgedSends "\<lambda>s. P (ksDomainTime s)"
  (ignore: filterM setObject getObject
     simp: filterM_mapM crunch_simps 
       wp: crunch_wps)

crunch ksDomainTime_inv[wp]: createNewObjects "\<lambda>s. P (ksDomainTime s)"
  (simp: crunch_simps zipWithM_x_mapM
   wp: crunch_wps hoare_unless_wp
   ignore: getObject setObject)

crunch ksDomainTime_inv[wp]: performARMMMUInvocation "\<lambda>s. P (ksDomainTime s)"
  (ignore: getObject setObject
   wp: crunch_wps getObject_cte_inv getASID_wp setObject_ksPSpace_only updateObject_default_inv
   simp: unless_def)

crunch ksDomainTime_inv[wp]: preemptionPoint "\<lambda>s. P (ksDomainTime s)"
  (simp: whenE_def)

crunch ksDomainTime_inv[wp]: performInvocation "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps zipWithM_x_inv cteRevoke_preservation mapME_x_inv_wp
   simp: unless_def crunch_simps filterM_mapM)

crunch ksDomainTime_inv[wp]: activateThread "\<lambda>s. P (ksDomainTime s)"

crunch ksDomainTime_inv[wp]:
  receiveSignal, getNotification, receiveIPC, deleteCallerCap "\<lambda>s. P (ksDomainTime s)"
  (wp: hoare_drop_imps simp: crunch_simps)

lemma handleRecv_ksDomainTime_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksDomainTime s) \<rbrace> handleRecv e \<lbrace>\<lambda>_ s. P (ksDomainTime s) \<rbrace>"
  unfolding handleRecv_def
  by (rule hoare_pre)
     (wp hoare_drop_imps | simp add: crunch_simps | wpc)+

crunch ksDomainTime_inv[wp]: doUserOp "(\<lambda>s. P (ksDomainTime s))"
  (wp: select_wp)

crunch ksDomainTime_inv[wp]: getIRQState, chooseThread, handleYield "(\<lambda>s. P (ksDomainTime s))"

crunch ksDomainTime_inv[wp]: handleSend, handleReply "(\<lambda>s. P (ksDomainTime s))"
  (wp: hoare_drop_imps hv_inv' syscall_valid' throwError_wp withoutPreemption_lift
   simp: runErrorT_def
   ignore: setThreadState)

crunch ksDomainTime_inv[wp]: handleInvocation "(\<lambda>s. P (ksDomainTime s))"
  (wp: hoare_drop_imps hv_inv' syscall_valid' throwError_wp withoutPreemption_lift
   simp: runErrorT_def
   ignore: setThreadState)

crunch ksDomainTime_inv[wp]: handleCall "(\<lambda>s. P (ksDomainTime s))"
  (wp: crunch_wps setObject_ksPSpace_only updateObject_default_inv cteRevoke_preservation
   simp: crunch_simps unless_def
   ignore: syscall setObject loadObject getObject constOnFailure )

crunch domain_time'_inv[wp]: activateThread,handleHypervisorFault "\<lambda>s. P (ksDomainTime s)"
  (wp: hoare_drop_imps)

lemma nextDomain_domain_time_left'[wp]:
  "\<lbrace> valid_domain_list' \<rbrace>
   nextDomain
   \<lbrace>\<lambda>_ s. 0 < ksDomainTime s \<rbrace>"
   unfolding nextDomain_def Let_def
   apply (clarsimp simp: valid_domain_list'_def dschLength_def)
   apply (simp only: all_set_conv_all_nth)
   apply (erule_tac x="Suc (ksDomScheduleIdx s) mod length (ksDomSchedule s)" in allE)
   apply fastforce
   done

lemma rescheduleRequired_ksSchedulerAction[wp]:
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>_ s. ksSchedulerAction s = ChooseNewThread \<rbrace>"
  unfolding rescheduleRequired_def
  by (wp setSchedulerAction_direct)

lemma timerTick_valid_domain_time:
  "\<lbrace>\<lambda>s. 0 < ksDomainTime s\<rbrace>
   timerTick
   \<lbrace>\<lambda>_ s. ksDomainTime s = 0 \<longrightarrow> ksSchedulerAction s = ChooseNewThread\<rbrace>"
  apply (simp add: timerTick_def numDomains_def)
  apply wp
       apply (rule_tac Q="\<lambda>_ s. ksSchedulerAction s = ChooseNewThread" in hoare_strengthen_post)
        apply (wp | clarsimp simp: if_apply_def2)+
  done

lemma handleInterrupt_valid_domain_time:
  "\<lbrace>\<lambda>s.  0 < ksDomainTime s \<rbrace>
   handleInterrupt i
   \<lbrace>\<lambda>rv s.  ksDomainTime s = 0 \<longrightarrow> ksSchedulerAction s = ChooseNewThread\<rbrace>"
   apply (simp add: handleInterrupt_def)
   apply (case_tac "maxIRQ < i"; simp)
    subgoal by (wp hoare_false_imp) simp
   apply (rule_tac B="\<lambda>_ s. 0 < ksDomainTime s" in hoare_seq_ext[rotated])
    apply (rule hoare_pre, wp, simp)
   apply (rename_tac st)
   apply (case_tac st, simp_all)
    (* IRQSignal : no timer tick, trivial preservation of ksDomainTime *)
    apply (rule_tac Q="\<lambda>_ s. 0 < ksDomainTime s" in hoare_post_imp, clarsimp)
    apply (rule hoare_pre, (wp | wpc)+)
     apply (rule_tac Q="\<lambda>_ s. 0 < ksDomainTime s" in hoare_post_imp, clarsimp)
     apply wp
    (* IRQTimer : tick occurs *) (* IRQReserved : trivial *)
    apply (wp timerTick_valid_domain_time
          | clarsimp simp: handleReservedIRQ_def
          | wp_once hoare_vcg_imp_lift)+
  done

lemma schedule_domain_time_left':
  "\<lbrace> valid_domain_list' and
     (\<lambda>s. ksDomainTime s = 0 \<longrightarrow> ksSchedulerAction s = ChooseNewThread) \<rbrace>
   ThreadDecls_H.schedule
   \<lbrace>\<lambda>_ s. 0 < ksDomainTime s \<rbrace>"
  unfolding schedule_def
  supply word_neq_0_conv[simp]
  apply (wp | wpc)+
      apply (rule_tac Q="\<lambda>_. valid_domain_list'" in hoare_post_imp, clarsimp)
      apply (wp | clarsimp)+
  done

lemma handleEvent_ksDomainTime_inv:
  "\<lbrace>\<lambda>s. P (ksDomainTime  s) \<and> e \<noteq> Interrupt \<rbrace>
   handleEvent e
   \<lbrace>\<lambda>_ s. P (ksDomainTime s) \<rbrace>"
  apply (cases e, simp_all)
      apply (rename_tac syscall)
      apply (case_tac syscall, simp_all add: handle_send_def)
             apply (wp hv_inv'|simp add: handleEvent_def |wpc)+
  done

lemma callKernel_domain_time_left:
  "\<lbrace> (\<lambda>s. 0 < ksDomainTime s) and valid_domain_list' and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s) \<rbrace>
   callKernel e
   \<lbrace>\<lambda>_ s. 0 < ksDomainTime s \<rbrace>"
  including no_pre
  unfolding callKernel_def
  supply word_neq_0_conv[simp]
  apply (case_tac "e = Interrupt")
   apply (simp add: handleEvent_def)
   apply (rule hoare_pre)
   apply ((wp schedule_domain_time_left' handleInterrupt_valid_domain_time
          | wpc | simp)+)[1]
    apply (rule_tac Q="\<lambda>_ s. 0 < ksDomainTime s \<and> valid_domain_list' s" in hoare_post_imp)
     apply fastforce
    apply wp
   apply simp
  (* non-interrupt case; may throw but does not touch ksDomainTime in handleEvent *)
  apply simp
  apply ((wp schedule_domain_time_left' handleInterrupt_valid_domain_time
          | simp add: if_apply_def2)+)[1]
   apply (rule_tac Q="\<lambda>_ s. valid_domain_list' s \<and> 0 < ksDomainTime s" in hoare_post_imp)
    apply fastforce
   apply wp
  apply simp
  apply (rule hoare_pre)
   apply (rule_tac Q="\<lambda>_ s. valid_domain_list' s \<and> 0 < ksDomainTime s"
            in NonDetMonadVCG.hoare_post_impErr[rotated 2], assumption)
    apply (wp handleEvent_ksDomainTime_inv | clarsimp)+
  done

end

end
