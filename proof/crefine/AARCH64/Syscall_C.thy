(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Syscall_C
imports
  Interrupt_C
  Ipc_C
  Invoke_C
  Schedule_C
  Arch_C
begin

context begin interpretation Arch . (*FIXME: arch-split*)
crunch replyFromKernel
  for sch_act_wf[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
end

context kernel_m begin

lemma ccorres_If_False:
  "ccorres_underlying sr Gamm r xf arrel axf R R' hs b c
   \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf
            (R and (\<lambda>_. \<not> P)) R' hs (If P a b) c"
  by (rule ccorres_gen_asm, simp)

definition
  one_on_true :: "bool \<Rightarrow> nat"
where
 "one_on_true P \<equiv> if P then 1 else 0"

lemma one_on_true_True[simp]: "one_on_true True = 1"
  by (simp add: one_on_true_def)

lemma one_on_true_eq_0[simp]: "(one_on_true P = 0) = (\<not> P)"
  by (simp add: one_on_true_def split: if_split)

lemma cap_cases_one_on_true_sum:
  "one_on_true (isZombie cap) + one_on_true (isArchObjectCap cap)
     + one_on_true (isThreadCap cap) + one_on_true (isCNodeCap cap)
     + one_on_true (isNotificationCap cap) + one_on_true (isEndpointCap cap)
     + one_on_true (isUntypedCap cap) + one_on_true (isReplyCap cap)
     + one_on_true (isIRQControlCap cap) + one_on_true (isIRQHandlerCap cap)
     + one_on_true (isNullCap cap) + one_on_true (isDomainCap cap) = 1"
  by (cases cap, simp_all add: isCap_simps)

lemma performInvocation_Endpoint_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and st_tcb_at' simple' thread and ep_at' epptr
              and sch_act_sane and (\<lambda>s. thread = ksCurThread s))
       (UNIV \<inter> {s. block_' s = from_bool blocking}
             \<inter> {s. call_' s = from_bool do_call}
             \<inter> {s. badge_' s = badge}
             \<inter> {s. canGrant_' s = from_bool canGrant}
             \<inter> {s. canGrantReply_' s = from_bool canGrantReply}
             \<inter> {s. ep_' s = ep_Ptr epptr}) []
     (liftE (sendIPC blocking do_call badge canGrant canGrantReply thread epptr))
     (Call performInvocation_Endpoint_'proc)"
  apply cinit
   apply (ctac add: sendIPC_ccorres)
     apply (simp add: return_returnOk)
     apply (rule ccorres_return_CE, simp+)[1]
    apply wp
   apply simp
   apply (vcg exspec=sendIPC_modifies)
  apply (clarsimp simp add: rf_sr_ksCurThread sch_act_sane_not)
  done

(* This lemma now assumes 'weak_sch_act_wf (ksSchedulerAction s) s' in place of 'sch_act_simple'. *)

lemma performInvocation_Notification_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s))
       (UNIV \<inter> {s. ntfn_' s = ntfn_Ptr ntfnptr}
             \<inter> {s. badge_' s = badge}
             \<inter> {s. message_' s = message}) []
     (liftE (sendSignal ntfnptr badge))
     (Call performInvocation_Notification_'proc)"
  apply cinit
   apply (ctac add: sendSignal_ccorres)
     apply (simp add: return_returnOk)
     apply (rule ccorres_return_CE, simp+)[1]
    apply wp
   apply simp
   apply (vcg exspec=sendSignal_modifies)
  apply simp
  done

lemma performInvocation_Reply_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and tcb_at' receiver and st_tcb_at' active' sender and sch_act_simple
             and ((Not o real_cte_at' slot) or cte_wp_at' (\<lambda>cte. isReplyCap (cteCap cte)) slot)
             and cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap \<or> isReplyCap (cteCap cte))
                 slot and (\<lambda>s. ksCurThread s = sender))
       (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr receiver}
             \<inter> {s. slot_' s = cte_Ptr slot}
             \<inter> {s. canGrant_' s = from_bool grant}) []
     (liftE (doReplyTransfer sender receiver slot grant))
     (Call performInvocation_Reply_'proc)"
  apply cinit
   apply (ctac add: doReplyTransfer_ccorres)
     apply (simp add: return_returnOk)
     apply (rule ccorres_return_CE, simp+)[1]
    apply wp
   apply simp
   apply (vcg exspec=doReplyTransfer_modifies)
  apply (simp add: rf_sr_ksCurThread)
  apply (auto simp: isReply_def elim!: pred_tcb'_weakenE)
  done

lemma decodeInvocation_ccorres:
  "interpret_excaps extraCaps' = excaps_map extraCaps
  \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and valid_cap' cp and (\<lambda>s. \<forall>x \<in> zobj_refs' cp. ex_nonz_cap_to' x s)
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) cp \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. s \<turnstile>' fst v \<and> cte_at' (snd v) s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. \<forall>y \<in> zobj_refs' (fst v). ex_nonz_cap_to' y s)
              and sysargs_rel args buffer)
       (UNIV \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. call_' s = from_bool isCall}
             \<inter> {s. block_' s = from_bool isBlocking}
             \<inter> {s. call_' s = from_bool isCall}
             \<inter> {s. block_' s = from_bool isBlocking}
             \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. capIndex_' s = cptr}
             \<inter> {s. slot_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation cp (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}) []
       (decodeInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall id)
       (Call decodeInvocation_'proc)"
  apply (cinit' lift: call_' block_' invLabel_' length___unsigned_long_'
                      capIndex_' slot_' current_extra_caps_' cap_' buffer_')
   apply csymbr
   apply (simp add: cap_get_tag_isCap decodeInvocation_def
              cong: if_cong StateSpace.state.fold_congs
                    globals.fold_congs
               del: Collect_const)
   apply (cut_tac cap=cp in cap_cases_one_on_true_sum)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: Let_def isArchCap_T_isArchObjectCap liftME_invocationCatch)
    apply (rule ccorres_split_throws)
     apply (rule ccorres_trim_returnE)
       apply simp
      apply simp
     apply (rule ccorres_call, rule Arch_decodeInvocation_ccorres [where buffer=buffer])
        apply assumption
       apply simp+
    apply (vcg exspec=Arch_decodeInvocation_modifies)
   apply simp
   apply csymbr
   apply (simp add: cap_get_tag_isCap del: Collect_const)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: invocationCatch_def throwError_bind)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: invocationCatch_def throwError_bind)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: if_to_top_of_bind)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply (rule ccorres_if_cond_throws2[where Q=\<top> and Q'=\<top>])
       apply (clarsimp simp: isCap_simps)
       apply (frule cap_get_tag_isCap_unfolded_H_cap)
       apply (drule(1) cap_get_tag_to_H)
       apply (clarsimp simp: to_bool_def)
      apply (simp add: throwError_bind invocationCatch_def)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)
     apply (simp add: returnOk_bind ccorres_invocationCatch_Inr
                      performInvocation_def bind_assoc liftE_bindE)
     apply (ctac add: setThreadState_ccorres)
       apply csymbr
       apply csymbr
       apply csymbr
       apply csymbr
       apply (rule ccorres_pre_getCurThread)
       apply (simp only: liftE_bindE[symmetric])
       apply (ctac add: performInvocation_Endpoint_ccorres)
          apply (rule ccorres_alternative2)
          apply (rule ccorres_return_CE, simp+)[1]
         apply (rule ccorres_return_C_errorE, simp+)[1]
        apply wp
       apply simp
       apply (vcg exspec=performInvocation_Endpoint_modifies)
      apply simp
      apply (rule hoare_use_eq[where f=ksCurThread])
       apply (wp sts_invs_minor' sts_st_tcb_at'_cases
                 setThreadState_ct' hoare_vcg_all_lift)+
     apply simp
     apply (vcg exspec=setThreadState_modifies)
    apply vcg
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_rhs_assoc)+
    apply (csymbr)
    apply (simp add: if_to_top_of_bind Collect_const[symmetric]
                del: Collect_const)
    apply (rule ccorres_if_cond_throws2[where Q=\<top> and Q'=\<top>])
       apply (clarsimp simp:  isCap_simps)
       apply (frule cap_get_tag_isCap_unfolded_H_cap)
       apply (drule(1) cap_get_tag_to_H)
       apply (clarsimp simp: to_bool_def)
      apply (simp add: throwError_bind invocationCatch_def)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)
     apply (simp add: returnOk_bind ccorres_invocationCatch_Inr
                      performInvocation_def bindE_assoc)
     apply (simp add: liftE_bindE)
     apply (ctac add: setThreadState_ccorres)
       apply csymbr
       apply csymbr
       apply (simp only: liftE_bindE[symmetric])
       apply (ctac(no_vcg) add: performInvocation_Notification_ccorres)
         apply (rule ccorres_alternative2)
         apply (rule ccorres_return_CE, simp+)[1]
        apply (rule ccorres_return_C_errorE, simp+)[1]
       apply wp
      apply (wp sts_invs_minor')
     apply simp
     apply (vcg exspec=setThreadState_modifies)
    apply vcg
   apply (rule ccorres_Cond_rhs)
    apply (simp add: if_to_top_of_bind)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply (rule ccorres_if_cond_throws2[where Q=\<top> and Q'=\<top>])
       apply (clarsimp simp: isCap_simps)
       apply (frule cap_get_tag_isCap_unfolded_H_cap)
       apply (clarsimp simp: cap_get_tag_ReplyCap to_bool_def)
      apply (simp add: throwError_bind invocationCatch_def)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)
     apply (simp add: returnOk_bind ccorres_invocationCatch_Inr
                      performInvocation_def liftE_bindE
                      bind_assoc)
     apply (ctac add: setThreadState_ccorres)
       apply csymbr
       apply csymbr
       apply (rule ccorres_pre_getCurThread)
       apply (simp only: liftE_bindE[symmetric])
       apply (ctac add: performInvocation_Reply_ccorres)
          apply (rule ccorres_alternative2)
          apply (rule ccorres_return_CE, simp+)[1]
         apply (rule ccorres_return_C_errorE, simp+)[1]
        apply wp
       apply simp
       apply (vcg exspec=performInvocation_Reply_modifies)
      apply (simp add: cur_tcb'_def[symmetric])
      apply (rule_tac Q'="\<lambda>rv s. ksCurThread s = thread" in hoare_post_add)
      apply (simp cong: conj_cong)
      apply (strengthen imp_consequent)
      apply (wp sts_invs_minor' sts_st_tcb_at'_cases)
     apply simp
     apply (vcg exspec=setThreadState_modifies)
    apply vcg
   apply (rule ccorres_Cond_rhs)
    apply (simp add: if_to_top_of_bind)
    apply (rule ccorres_trim_returnE, simp+)
    apply (simp add: liftME_invocationCatch)
    apply (rule ccorres_call, rule decodeTCBInvocation_ccorres)
       apply assumption
      apply (simp+)[3]
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_trim_returnE, simp+)
    apply (simp add: liftME_invocationCatch)
    apply (rule ccorres_call,
           erule decodeDomainInvocation_ccorres,
           simp+)[1]
   apply (rule ccorres_Cond_rhs)
    apply (simp add: if_to_top_of_bind)
    apply (rule ccorres_trim_returnE, simp+)
    apply (simp add: liftME_invocationCatch)
    apply (rule ccorres_call,
           erule decodeCNodeInvocation_ccorres,
           simp+)[1]
   apply (rule ccorres_Cond_rhs)
    apply simp
    apply (rule ccorres_trim_returnE, simp+)
    apply (simp add: liftME_invocationCatch)
    apply (rule ccorres_call,
           erule decodeUntypedInvocation_ccorres, simp+)[1]
   apply (rule ccorres_Cond_rhs)
    apply (simp add: liftME_invocationCatch)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call, erule decodeIRQControlInvocation_ccorres,
           simp+)[1]
   apply (rule ccorres_Cond_rhs)
    apply (simp add: Let_def liftME_invocationCatch)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call,
           erule decodeIRQHandlerInvocation_ccorres, simp+)
   apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
   apply (simp add: isArchCap_T_isArchObjectCap one_on_true_def from_bool_0)
  apply (rule conjI)
   apply (clarsimp simp: tcb_at_invs' ct_in_state'_def
                         simple_sane_strg)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_cap'_def isCap_simps
                         unat_eq_0 sysargs_rel_n_def n_msgRegisters_def valid_tcb_state'_def
          | rule conjI | erule pred_tcb'_weakenE disjE
          | drule st_tcb_at_idle_thread')+
   apply fastforce
  apply (simp add: cap_lift_capEPBadge_mask_eq)
  apply (clarsimp simp: rf_sr_ksCurThread Collect_const_mem
                        cap_get_tag_isCap ThreadState_defs)
  apply (frule word_unat.Rep_inverse')
  apply (simp add: cap_get_tag_isCap[symmetric] cap_get_tag_ReplyCap)
  apply (rule conjI)
   apply (simp add: cap_get_tag_isCap)
   apply (clarsimp simp: isCap_simps cap_get_tag_to_H from_bool_neq_0)
  apply (insert ccap_relation_IRQHandler_mask, elim meta_allE, drule(1) meta_mp)
  apply (clarsimp simp: word_size)
  apply (clarsimp simp: cap_get_tag_isCap)
  apply (cases cp ; clarsimp simp: isCap_simps)
     apply (frule cap_get_tag_isCap_unfolded_H_cap, drule (1) cap_get_tag_to_H)
     apply fastforce
    apply (frule cap_get_tag_isCap_unfolded_H_cap, drule (1) cap_get_tag_to_H)
    apply (fastforce simp: cap_endpoint_cap_lift_def mask_eq_ucast_eq irq_len_val)
   apply (frule ccap_relation_ep_helpers)
    apply (clarsimp simp: cap_get_tag_isCap isEndpointCap_def)
   apply clarsimp
  apply (frule ccap_relation_reply_helpers)
   apply (clarsimp simp:  cap_get_tag_isCap isReplyCap_def)
  apply clarsimp
  done

lemma ccorres_Call_Seq:
  "\<lbrakk> \<Gamma> f = Some v; ccorres r xf P P' hs a (v ;; c) \<rbrakk>
       \<Longrightarrow> ccorres r xf P P' hs a (Call f ;; c)"
  apply (erule ccorres_semantic_equivD1)
  apply (rule semantic_equivI)
  apply (auto elim!: exec_elim_cases intro: exec.intros)
  done

lemma wordFromRights_mask_0:
  "wordFromRights rghts && ~~ mask 4 = 0"
  apply (simp add: wordFromRights_def word_ao_dist word_or_zero
            split: cap_rights.split)
  apply (simp add: mask_def split: if_split)
  done

lemma wordFromRights_mask_eq:
  "wordFromRights rghts && mask 4 = wordFromRights rghts"
  apply (cut_tac x="wordFromRights rghts" and y="mask 4" and z="~~ mask 4"
             in bit.conj_disj_distrib)
  apply (simp add: wordFromRights_mask_0)
  done

lemma mapM_loadWordUser_user_words_at:
  "\<lbrace>\<lambda>s. \<forall>rv. (\<forall>x < length xs. user_word_at (rv ! x) (xs ! x) s)
              \<and> length rv = length xs \<longrightarrow> Q rv s\<rbrace>
    mapM loadWordUser xs \<lbrace>Q\<rbrace>"
  apply (induct xs arbitrary: Q)
   apply (simp add: mapM_def sequence_def)
   apply wp
  apply (simp add: mapM_Cons)
  apply wp
   apply assumption
  apply (wp loadWordUser_user_word_at)
  apply clarsimp
  apply (drule spec, erule mp)
  apply clarsimp
  apply (case_tac x)
   apply simp
  apply simp
  done

lemma getSlotCap_slotcap_in_mem:
  "\<lbrace>\<top>\<rbrace> getSlotCap slot \<lbrace>\<lambda>cap s. slotcap_in_mem cap slot (ctes_of s)\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of slotcap_in_mem_def)
  done

lemma lookupExtraCaps_excaps_in_mem[wp]:
  "\<lbrace>\<top>\<rbrace> lookupExtraCaps thread buffer info \<lbrace>\<lambda>rv s. excaps_in_mem rv (ctes_of s)\<rbrace>,-"
  apply (simp add: excaps_in_mem_def lookupExtraCaps_def lookupCapAndSlot_def
                   split_def)
  apply (wp mapME_set)
      apply (wp getSlotCap_slotcap_in_mem | simp)+
  done

lemma getCurThread_ccorres:
  "ccorres ((=) \<circ> tcb_ptr_to_ctcb_ptr) thread_'
       \<top> UNIV hs getCurThread (\<acute>thread :== \<acute>ksCurThread)"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: getCurThread_def simpler_gets_def
                        rf_sr_ksCurThread)
  done

lemma getMessageInfo_ccorres:
  "ccorres (\<lambda>rv rv'. rv = messageInfoFromWord rv') ret__unsigned_long_' \<top>
       (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr thread}
             \<inter> {s. reg_' s = register_from_H AARCH64_H.msgInfoRegister}) []
       (getMessageInfo thread) (Call getRegister_'proc)"
  apply (simp add: getMessageInfo_def liftM_def[symmetric])
  apply (rule ccorres_rel_imp, rule ccorres_guard_imp2, rule getRegister_ccorres)
   apply simp
  apply simp
  done

lemma messageInfoFromWord_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call messageInfoFromWord_'proc
            {s'. seL4_MessageInfo_lift (ret__struct_seL4_MessageInfo_C_' s')
                  = mi_from_H (messageInfoFromWord (w_' s))}"
  apply (rule allI, rule conseqPost, rule messageInfoFromWord_spec[rule_format])
   apply simp_all
  apply (clarsimp simp: seL4_MessageInfo_lift_def mi_from_H_def
                        messageInfoFromWord_def Let_def
                        msgLengthBits_def msgExtraCapBits_def
                        msgMaxExtraCaps_def msgLabelBits_def shiftL_nat)
  done

lemma threadGet_tcbIpcBuffer_ccorres [corres]:
  "ccorres (=) w_bufferPtr_' (tcb_at' tptr) UNIV hs
           (threadGet tcbIPCBuffer tptr)
           (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t (Ptr &(tcb_ptr_to_ctcb_ptr tptr\<rightarrow>
                                  [''tcbIPCBuffer_C''])::machine_word ptr)\<rbrace>
               (\<acute>w_bufferPtr :==
                  h_val (hrs_mem \<acute>t_hrs)
                   (Ptr &(tcb_ptr_to_ctcb_ptr tptr\<rightarrow>[''tcbIPCBuffer_C''])::machine_word ptr)))"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_add_return2)
   apply (rule ccorres_pre_threadGet)
   apply (rule_tac P = "obj_at' (\<lambda>tcb. tcbIPCBuffer tcb = x) tptr" and
                   P'="{s'. \<exists>ctcb.
          cslift s' (tcb_ptr_to_ctcb_ptr tptr) = Some ctcb \<and>
                 tcbIPCBuffer_C ctcb = x }" in ccorres_from_vcg)
   apply (rule allI, rule conseqPre, vcg)
   apply clarsimp
   apply (clarsimp simp: return_def typ_heap_simps')
  apply (clarsimp simp: obj_at'_def ctcb_relation_def)
  done

lemma handleInvocation_def2:
  "handleInvocation isCall isBlocking =
   do thread \<leftarrow> getCurThread;
      info \<leftarrow> getMessageInfo thread;
      ptr \<leftarrow> asUser thread (getRegister AARCH64_H.capRegister);
      v \<leftarrow> (doE (cap, slot) \<leftarrow> capFaultOnFailure ptr False (lookupCapAndSlot thread ptr);
          buffer \<leftarrow> withoutFailure (VSpace_H.lookupIPCBuffer False thread);
          extracaps \<leftarrow> lookupExtraCaps thread buffer info;
          returnOk (slot, cap, extracaps, buffer)
      odE);
      case v of Inl f \<Rightarrow> liftE (when isBlocking (handleFault thread f))
        | Inr (slot, cap, extracaps, buffer) \<Rightarrow>
               do args \<leftarrow> getMRs thread buffer info;
                  v' \<leftarrow> do v \<leftarrow> RetypeDecls_H.decodeInvocation (msgLabel info) args ptr slot cap extracaps;
                               invocationCatch thread isBlocking isCall id v od;
                  case v' of Inr _ \<Rightarrow> liftE (replyOnRestart thread [] isCall)
                           | Inl (Inl syserr) \<Rightarrow> liftE (when isCall (replyFromKernel thread
                                                                   (msgFromSyscallError syserr)))
                           | Inl (Inr preempt) \<Rightarrow> throwError preempt
               od
   od"
  apply (simp add: handleInvocation_def Syscall_H.syscall_def runExceptT_def
                   liftE_bindE cong: sum.case_cong)
  apply (rule ext, (rule bind_apply_cong [OF refl])+)
  apply (clarsimp simp: bind_assoc split: sum.split)
  apply (rule bind_apply_cong [OF refl])+
  apply (clarsimp simp: invocationCatch_def throwError_bind
                        liftE_bindE bind_assoc
                 split: sum.split)
  apply (rule bind_apply_cong [OF refl])+
  apply (simp add: bindE_def bind_assoc)
  apply (rule bind_apply_cong [OF refl])+
  apply (clarsimp simp: lift_def throwError_bind returnOk_bind split: sum.split)
  apply (simp cong: bind_cong add: ts_Restart_case_helper')
  apply (simp add: when_def[symmetric] replyOnRestart_def[symmetric])
  apply (simp add: liftE_def replyOnRestart_twice alternative_bind
                   alternative_refl split: if_split)
  done

lemma thread_state_to_tsType_eq_Restart:
  "(thread_state_to_tsType ts = scast ThreadState_Restart)
       = (ts = Restart)"
  by (cases ts, simp_all add: ThreadState_defs)

lemma wordFromMessageInfo_spec:
  "\<forall>s. \<Gamma>\<turnstile> {s} Call wordFromMessageInfo_'proc
      {s'. \<forall>mi. seL4_MessageInfo_lift (mi_' s) = mi_from_H mi
                   \<longrightarrow> ret__unsigned_long_' s' = wordFromMessageInfo mi}"
  apply (rule allI, rule conseqPost[OF wordFromMessageInfo_spec[rule_format] _ subset_refl])
  apply (clarsimp simp: wordFromMessageInfo_def
                        msgLengthBits_def msgExtraCapBits_def msgMaxExtraCaps_def shiftL_nat)
  apply (drule sym[where t="mi_from_H mi" for mi])
  apply (clarsimp simp: seL4_MessageInfo_lift_def mi_from_H_def mask_def)
  apply (thin_tac _)+
  apply word_bitwise
  done

lemma handleDoubleFault_ccorres:
  "ccorres dc xfdc (invs' and  tcb_at' tptr and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and
        sch_act_not tptr)
      (UNIV \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr tptr})
      [] (handleDoubleFault tptr ex1 ex2)
         (Call handleDoubleFault_'proc)"
  apply (cinit lift: tptr_')
   apply (subst ccorres_seq_skip'[symmetric])
   apply (ctac (no_vcg))
    apply (rule ccorres_symb_exec_l)
       apply (rule ccorres_return_Skip)
      apply (wp asUser_inv getRestartPC_inv)+
    apply (rule empty_fail_asUser)
    apply (simp add: getRestartPC_def)
   apply wp
  apply clarsimp
  apply (simp add: ThreadState_defs)
  apply (fastforce simp: valid_tcb_state'_def)
  done

lemma cap_case_EndpointCap:
  "(case cap of EndpointCap ep b cs cr cg cgr \<Rightarrow> f ep b cs cr cg cgr | _ \<Rightarrow> g)
   = (if isEndpointCap cap then f (capEPPtr cap)  (capEPBadge cap) (capEPCanSend cap)
                                  (capEPCanReceive cap) (capEPCanGrant cap) (capEPCanGrantReply cap)
     else g)"
  by (cases cap; clarsimp simp: isCap_simps)

lemma cap_case_EndpointCap_CanSend_CanGrant:
  "(case cap of EndpointCap v0 v1 True v3 True v4 \<Rightarrow> f v0 v1 v3 v4
              | _ \<Rightarrow> g)
   = (if (isEndpointCap cap \<and> capEPCanSend cap \<and> capEPCanGrant cap)
      then f (capEPPtr cap)  (capEPBadge cap) (capEPCanReceive cap) (capEPCanGrantReply cap)
      else g)"
  by (simp add: isCap_simps
           split: capability.split bool.split)

lemma threadGet_tcbFaultHandler_ccorres [corres]:
  "ccorres (=) handlerCPtr_' (tcb_at' tptr) UNIV hs
           (threadGet tcbFaultHandler tptr)
           (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t (tcb_ptr_to_ctcb_ptr tptr)\<rbrace>
               (\<acute>handlerCPtr :==
                  h_val (hrs_mem \<acute>t_hrs)
                   (Ptr &(tcb_ptr_to_ctcb_ptr tptr\<rightarrow>[''tcbFaultHandler_C''])::machine_word ptr)))"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_add_return2)
   apply (rule ccorres_pre_threadGet)
   apply (rule_tac P = "obj_at' (\<lambda>tcb. tcbFaultHandler tcb = x) tptr" and
                   P'="{s'. \<exists> ctcb.
          cslift s' (tcb_ptr_to_ctcb_ptr tptr) = Some ctcb \<and>
                 tcbFaultHandler_C ctcb = x }" in ccorres_from_vcg)
   apply (rule allI, rule conseqPre, vcg)
   apply clarsimp
   apply (clarsimp simp: return_def typ_heap_simps')
  apply (clarsimp simp: obj_at'_def ctcb_relation_def)
done

lemma tcb_cte_cases_tcbFault_update_simp:
  "(f, u) \<in> ran tcb_cte_cases \<Longrightarrow> f (tcbFault_update (\<lambda>_. Some fault) tcb) = f tcb"
  unfolding tcb_cte_cases_def cteSizeBits_def
  by auto

lemma hrs_mem_update_use_hrs_mem:
  "hrs_mem_update f = (\<lambda>hrs. (hrs_mem_update $ (\<lambda>_. f (hrs_mem hrs))) hrs)"
  by (simp add: hrs_mem_update_def hrs_mem_def fun_eq_iff)

lemma sendFaultIPC_ccorres:
  "ccorres  (cfault_rel2 \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and st_tcb_at' simple' tptr and sch_act_not tptr)
      (UNIV \<inter> {s. (cfault_rel (Some fault) (seL4_Fault_lift(current_fault_' (globals s)))
                       (lookup_fault_lift(current_lookup_fault_' (globals s))))}
            \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr tptr})
      [] (sendFaultIPC tptr fault)
         (Call sendFaultIPC_'proc)"
  supply if_cong[cong] option.case_cong[cong]
  supply Collect_const[simp del]
  apply (cinit lift: tptr_' cong: call_ignore_cong)
   apply (simp add: liftE_bindE del:Collect_const cong:call_ignore_cong)
   apply (rule ccorres_symb_exec_r)
     apply (rule ccorres_split_nothrow)
         apply (rule threadGet_tcbFaultHandler_ccorres)
        apply ceqv
       apply (rule_tac  xf'=lu_ret___struct_lookupCap_ret_C_'
                in ccorres_split_nothrow_callE)
                apply (rule capFaultOnFailure_ccorres)
                apply (rule lookupCap_ccorres)
               apply simp+
           apply ceqv
          apply (rename_tac epcap epcap')
          apply clarsimp
          apply ccorres_rewrite
          apply csymbr
          apply (simp add: cap_case_EndpointCap)
          apply (rule ccorres_rhs_assoc2)
          apply (rule ccorres_rhs_assoc2)
          apply (rule ccorres_rhs_assoc2)
          apply (rule_tac val="from_bool (isEndpointCap epcap \<and> capEPCanSend epcap
                                          \<and> (capEPCanGrant epcap \<or> capEPCanGrantReply epcap))"
                   and xf'=ret__int_' and R=\<top> and R'=UNIV in ccorres_symb_exec_r_known_rv)
             apply (rule conseqPre, vcg)
             apply (fastforce simp: from_bool_eq_if' cap_get_tag_isCap isCap_simps
                                    ccap_relation_ep_helpers)
            apply ceqv
           apply clarsimp
           apply (rule ccorres_Cond_rhs)
            (* case: we send the IPC *)
            apply clarsimp
            apply (simp add: liftE_def bind_assoc)
            apply (rule ccorres_rhs_assoc)+
            apply (rule ccorres_rhs_assoc2)
            apply (rule ccorres_rhs_assoc2)
            apply (rule_tac ccorres_split_nothrow_novcg)
                apply (rule_tac P=\<top> and P'=invs'
                          and R="{s.
                        (cfault_rel (Some fault)
                        (seL4_Fault_lift(current_fault_' (globals s)))
                         (lookup_fault_lift(original_lookup_fault_'  s)))}"
                          in threadSet_ccorres_lemma4)
                 apply vcg
                apply (clarsimp simp: typ_heap_simps' rf_sr_tcb_update_twice)
                apply (intro conjI allI impI)
                  apply (simp add: typ_heap_simps' rf_sr_def)
                  apply (rule rf_sr_tcb_update_no_queue2[unfolded rf_sr_def, simplified],
                              assumption+, (simp add: typ_heap_simps')+)
                  apply (rule ball_tcb_cte_casesI, simp+)
                 apply (simp add: ctcb_relation_def cthread_state_relation_def)
                 apply (case_tac "tcbState tcb", simp+)
                apply (simp add: rf_sr_def)
                apply (rule rf_sr_tcb_update_no_queue2[unfolded rf_sr_def, simplified],
                       assumption+, (simp add: typ_heap_simps' | simp only: hrs_mem_update_use_hrs_mem)+)
                 apply (rule ball_tcb_cte_casesI, simp+)
                apply (clarsimp simp: typ_heap_simps')
                apply (simp add: ctcb_relation_def cthread_state_relation_def)
                apply (rule conjI)
                 apply (case_tac "tcbState tcb", simp+)
                apply (simp add: cfault_rel_def)
                apply (clarsimp)
                apply (clarsimp simp: seL4_Fault_lift_def Let_def is_cap_fault_def
                                split: if_split_asm)
               apply ceqv
              apply csymbr
              apply csymbr
              apply csymbr
              apply (ctac (no_vcg) add: sendIPC_ccorres)
               apply (ctac (no_vcg) add: ccorres_return_CE [unfolded returnOk_def comp_def])
              apply wp
             apply (wpsimp wp: threadSet_invs_trivial)
             apply (wpsimp wp: threadSet_pred_tcb_no_state threadSet_typ_at_lifts)

            apply (clarsimp simp: guard_is_UNIV_def)
            apply (subgoal_tac "capEPBadge epcap && mask 64 = capEPBadge epcap")
             apply (clarsimp simp: cap_get_tag_isCap isEndpointCap_def isCap_simps
                                    ccap_relation_ep_helpers)
            apply (drule cap_get_tag_isCap(4)[symmetric])
            apply (clarsimp simp: cap_get_tag_EndpointCap)
           apply (clarsimp simp: case_bool_If)
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
           apply clarsimp
           apply (clarsimp simp add: throwError_def return_def)
           apply (rule conseqPre, vcg)
           apply (clarsimp simp: EXCEPTION_FAULT_def EXCEPTION_NONE_def)
           apply (simp add: cfault_rel2_def cfault_rel_def EXCEPTION_FAULT_def)
           apply (simp add: seL4_Fault_CapFault_lift)
           apply (simp add: lookup_fault_missing_capability_lift is_cap_fault_def)
          apply clarsimp
          apply vcg
         apply clarsimp
         apply (rule ccorres_split_throws)
          apply (rule_tac P=\<top> and P'="{x. errstate x= err'}" in ccorres_from_vcg_throws)
          apply clarsimp
          apply (clarsimp simp add: throwError_def return_def)
          apply (rule conseqPre, vcg)
          apply (clarsimp simp: EXCEPTION_FAULT_def EXCEPTION_NONE_def)
          apply (simp add: cfault_rel2_def cfault_rel_def EXCEPTION_FAULT_def)
          apply (simp add: seL4_Fault_CapFault_lift is_cap_fault_def)
          apply (erule lookup_failure_rel_fault_lift [rotated, unfolded EXCEPTION_NONE_def, simplified]
                 , assumption)
         apply vcg
        apply (clarsimp simp: inQ_def)
        apply (rule_tac Q'="\<lambda>a b. invs' b \<and> st_tcb_at' simple' tptr b
                                 \<and> sch_act_not tptr b \<and> valid_cap' a b"
                 and E'="\<lambda> _. \<top>"
                 in hoare_strengthen_postE)
          apply (wp)
         apply (clarsimp simp: isCap_simps)
         apply (clarsimp simp: valid_cap'_def pred_tcb_at')+
       apply (vcg exspec=lookupCap_modifies)
      apply wpsimp+
     apply vcg
    apply (clarsimp, vcg)
   apply (rule conseqPre, vcg)
   apply fastforce+
  done

lemma handleFault_ccorres:
  "ccorres dc xfdc (invs' and st_tcb_at' simple' t and sch_act_not t)
      (UNIV \<inter> {s. (cfault_rel (Some flt) (seL4_Fault_lift(current_fault_' (globals s)))
                       (lookup_fault_lift(current_lookup_fault_' (globals s))) )}
            \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr t})
      hs (handleFault t flt)
         (Call handleFault_'proc)"
  apply (cinit lift: tptr_')
   apply (simp add: catch_def)
   apply (rule ccorres_symb_exec_r)
     apply (rule ccorres_split_nothrow_novcg_case_sum)
           apply (ctac (no_vcg) add: sendFaultIPC_ccorres)
          apply ceqv
         apply clarsimp
         apply (rule ccorres_cond_empty)
         apply (rule ccorres_return_Skip')
        apply clarsimp
        apply (rule ccorres_cond_univ)
        apply (ctac (no_vcg) add: handleDoubleFault_ccorres)
       apply (simp add: sendFaultIPC_def)
       apply wp
         apply ((wp hoare_vcg_all_liftE_R hoare_drop_impE_R |wpc |simp add: throw_def)+)[1]
        apply clarsimp
        apply ((wp hoare_vcg_all_liftE_R hoare_drop_impE_R |wpc |simp add: throw_def)+)[1]
       apply (wp)
      apply (simp add: guard_is_UNIV_def)
     apply (simp add: guard_is_UNIV_def)
    apply clarsimp
    apply vcg
   apply clarsimp
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply (clarsimp simp: pred_tcb_at')
  done

(* FIXME: move *)
lemma length_CL_from_H [simp]:
  "length_CL (mi_from_H mi) = msgLength mi"
  by (simp add: mi_from_H_def)

lemma getMRs_length:
  "\<lbrace>\<lambda>s. msgLength mi \<le> 120\<rbrace> getMRs thread buffer mi
  \<lbrace>\<lambda>args s. if buffer = None then length args = min (unat n_msgRegisters) (unat (msgLength mi))
            else length args = unat (msgLength mi)\<rbrace>"
  supply if_cong[cong]
  apply (cases buffer)
   apply (simp add: getMRs_def)
   apply (rule hoare_pre, wp)
    apply (rule asUser_const_rv)
    apply simp
    apply (wp mapM_length)
   apply (simp add: min_def length_msgRegisters)
  apply (clarsimp simp: n_msgRegisters_def)
  apply (simp add: getMRs_def)
  apply (rule hoare_pre, wp)
    apply simp
    apply (wp mapM_length asUser_const_rv mapM_length)+
  apply (clarsimp simp: length_msgRegisters)
  apply (simp add: min_def split: if_splits)
  apply (clarsimp simp: word_le_nat_alt)
  apply (simp add: msgMaxLength_def msgLengthBits_def n_msgRegisters_def)
  done

lemma handleInvocation_ccorres:
  "ccorres (K dc \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and ct_active' and sch_act_simple)
       (UNIV \<inter> {s. isCall_' s = from_bool isCall}
             \<inter> {s. isBlocking_' s = from_bool isBlocking}) []
       (handleInvocation isCall isBlocking) (Call handleInvocation_'proc)"
  apply (cinit' lift: isCall_' isBlocking_'
                simp: whileAnno_def handleInvocation_def2)
   apply (simp add: liftE_bindE del: Collect_const cong: call_ignore_cong)
   apply (ctac(no_vcg) add: getCurThread_ccorres)
     apply (ctac(no_vcg) add: getMessageInfo_ccorres)
      apply (simp del: Collect_const cong: call_ignore_cong)
      apply csymbr
      apply (ctac(no_vcg) add: getRegister_ccorres)
       apply (simp add: Syscall_H.syscall_def
                        liftE_bindE split_def bindE_bind_linearise
                  cong: call_ignore_cong
                   del: Collect_const)
       apply (rule_tac ccorres_split_nothrow_case_sum)
            apply (ctac add: capFaultOnFailure_ccorres
                                 [OF lookupCapAndSlot_ccorres])
           apply ceqv
          apply (simp add: ccorres_cond_iffs Collect_False
                     cong: call_ignore_cong
                      del: Collect_const)
          apply (simp only: bind_assoc)
          apply (ctac(no_vcg) add: lookupIPCBuffer_ccorres)
           apply (simp add: liftME_def bindE_assoc del: Collect_const)
           apply (simp add: bindE_bind_linearise del: Collect_const)
           apply (rule_tac xf'="\<lambda>s. (status_' s,
                                current_extra_caps_' (globals s))"
                             and ef'=fst and vf'=snd and es=errstate
                        in ccorres_split_nothrow_novcg_case_sum)
                 apply (rule ccorres_call, rule lookupExtraCaps_ccorres, simp+)
                apply (rule ceqv_tuple2, ceqv, ceqv)
               apply (simp add: returnOk_bind liftE_bindE
                                Collect_False
                                ccorres_cond_iffs ts_Restart_case_helper'
                           del: Collect_const cong: bind_cong)
               apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
                      rule_tac xf'="length___unsigned_long_'"
                            and r'="\<lambda>rv rv'. unat rv' = length rv"
                            in ccorres_split_nothrow)
                   apply (rule ccorres_add_return2)
                   apply (rule ccorres_symb_exec_l)
                      apply (rule_tac P="\<lambda>s. rvd \<noteq> Some 0 \<and> (if rvd = None then
                                               length x = min (unat (n_msgRegisters))
                                                            (unat (msgLength (messageInfoFromWord ret__unsigned_long)))
                                             else
                                               length x = (unat (msgLength (messageInfoFromWord ret__unsigned_long))))"
                                  and P'=UNIV
                                   in ccorres_from_vcg)
                      apply (clarsimp simp: return_def)
                      apply (rule conseqPre, vcg)
                      apply (clarsimp simp: word_less_nat_alt)
                      apply (rule conjI)
                       apply clarsimp
                       apply (case_tac rvd, clarsimp simp: option_to_ptr_def option_to_0_def min_def n_msgRegisters_def)
                       apply (clarsimp simp: option_to_0_def option_to_ptr_def)
                      apply clarsimp
                      apply (case_tac rvd,
                             clarsimp simp: option_to_0_def min_def option_to_ptr_def
                                            n_msgRegisters_def
                                     split: if_splits)
                      apply (clarsimp simp: option_to_0_def option_to_ptr_def)
                     apply wp
                    apply (wp getMRs_length)
                   apply simp
                  apply ceqv
                 apply csymbr
                 apply (simp only: bind_assoc[symmetric])
                 apply (rule ccorres_split_nothrow_novcg_case_sum)
                       apply (ctac add: decodeInvocation_ccorres)
                      apply ceqv
                     apply (simp add: Collect_False exception_defs
                                      replyOnRestart_def liftE_def bind_assoc
                                 del: Collect_const)
                     apply (rule ccorres_move_c_guard_tcb)
                     apply (rule getThreadState_ccorres_foo)
                     apply csymbr
                     apply (rule ccorres_abstract_cleanup)
                     apply (rule_tac P="ret__unsigned_longlong = thread_state_to_tsType rvg"
                                 in ccorres_gen_asm2)
                     apply (simp add: thread_state_to_tsType_eq_Restart from_bool_0
                                 del: Collect_const add: Collect_const[symmetric])
                     apply (rule ccorres_Cond_rhs_Seq)
                      apply (rule ccorres_rhs_assoc)+
                      apply (rule ccorres_Cond_rhs_Seq)
                       apply (simp add: bind_assoc)
                       apply (ctac(no_vcg) add: replyFromKernel_success_empty_ccorres)
                        apply (ctac(no_vcg) add: setThreadState_ccorres)
                         apply (rule ccorres_return_CE[folded return_returnOk], simp+)[1]
                        apply wp+
                       apply (rule hoare_strengthen_post, rule rfk_invs')
                       apply auto[1]
                      apply simp
                      apply (ctac(no_vcg) add: setThreadState_ccorres)
                       apply (rule ccorres_return_CE[folded return_returnOk], simp+)[1]
                      apply wp
                     apply simp
                     apply (rule ccorres_return_CE[folded return_returnOk], simp+)[1]
                    apply wpc
                     apply (simp add: syscall_error_rel_def from_bool_0 exception_defs
                                      Collect_False ccorres_cond_iffs Collect_True
                                 del: Collect_const)
                     apply (rule ccorres_rhs_assoc)+
                     apply (simp add: liftE_def Collect_const[symmetric]
                                 del: Collect_const)
                     apply (rule ccorres_Cond_rhs_Seq)
                      apply simp
                      apply (ctac(no_vcg) add: replyFromKernel_error_ccorres)
                       apply (rule ccorres_split_throws)
                        apply (rule ccorres_return_CE[folded return_returnOk], simp+)[1]
                       apply vcg
                      apply wp
                     apply simp
                     apply (rule ccorres_split_throws)
                      apply (rule ccorres_return_CE[folded return_returnOk], simp+)[1]
                     apply vcg
                    apply (simp add: cintr_def)
                    apply (rule ccorres_split_throws)
                     apply (rule ccorres_return_C_errorE, simp+)[1]
                    apply vcg
                   apply (simp add: invocationCatch_def o_def)
                   apply (rule_tac Q'="\<lambda>rv'. invs' and tcb_at' rv"
                               and E'="\<lambda>ft. invs' and tcb_at' rv"
                              in hoare_strengthen_postE)
                     apply (wp hoare_split_bind_case_sumE hoare_drop_imps
                               setThreadState_nonqueued_state_update
                               ct_in_state'_set setThreadState_st_tcb
                               hoare_vcg_all_lift
                                 | wpc | wps)+
                    apply auto[1]
                   apply clarsimp
                  apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem)
                  apply (simp add: ThreadState_defs mask_def)
                  apply (simp add: typ_heap_simps)
                  apply (case_tac ts, simp_all add: cthread_state_relation_def)[1]
                 apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem)
                 apply (clarsimp simp add: intr_and_se_rel_def exception_defs
                                           syscall_error_rel_def cintr_def
                                    split: sum.split_asm)
                apply (simp add: conj_comms)
                apply (wp getMRs_sysargs_rel)
               apply (simp add: )
               apply vcg
              apply (simp add: ccorres_cond_iffs ccorres_seq_cond_raise
                               Collect_True Collect_False
                          del: Collect_const)
              apply (rule ccorres_rhs_assoc)+
              apply (simp add: ccorres_cond_iffs Collect_const[symmetric]
                          del: Collect_const)
              apply (rule ccorres_Cond_rhs_Seq)
               apply (simp add: from_bool_0 liftE_def)
               apply (ctac(no_vcg) add: handleFault_ccorres)
                apply (rule ccorres_split_throws)
                 apply (rule ccorres_return_CE[folded return_returnOk], simp+)[1]
                apply vcg
               apply wp
              apply (simp add: from_bool_0 liftE_def)
              apply (rule ccorres_split_throws)
               apply (rule ccorres_return_CE[folded return_returnOk], simp+)[1]
              apply vcg
             apply (simp add: ball_conj_distrib)
             apply (wp lookupExtraCaps_excaps_in_mem
                       lec_eq[unfolded o_def] lec_derived'[unfolded o_def])
            apply (clarsimp simp: guard_is_UNIV_def option_to_ptr_def
                                  mi_from_H_def)
           apply (clarsimp simp: guard_is_UNIV_def)
          apply simp
          apply (wp lookupIPCBuffer_Some_0)
         apply (simp add: Collect_True liftE_def return_returnOk
                     del: Collect_const)
         apply (rule ccorres_rhs_assoc)+
         apply (rule_tac P=\<top> in ccorres_cross_over_guard)
         apply (rule ccorres_symb_exec_r)
           apply (rule ccorres_split_nothrow_novcg_dc)
              apply (rule ccorres_when[where R=\<top>])
               apply (simp add: from_bool_0 Collect_const_mem)
              apply (ctac add: handleFault_ccorres)
             apply (rule ccorres_split_throws)
              apply (rule ccorres_return_CE, simp+)[1]
             apply vcg
            apply wp
           apply (simp add: guard_is_UNIV_def)
          apply vcg
         apply (rule conseqPre, vcg)
         apply clarsimp
        apply (simp, wp lcs_eq[unfolded o_def])
       apply clarsimp
       apply (vcg exspec= lookupCapAndSlot_modifies)
      apply simp
      apply (wp getMessageInfo_less_4 getMessageInfo_le3 getMessageInfo_msgLength')+
     apply (simp add: msgMaxLength_def, wp getMessageInfo_msgLength')[1]
    apply simp
    apply wp
   apply (clarsimp simp: Collect_const_mem)
   apply (simp add: Kernel_C.msgInfoRegister_def AARCH64_H.msgInfoRegister_def
                    AARCH64.msgInfoRegister_def C_register_defs
                    Kernel_C.capRegister_def AARCH64_H.capRegister_def
                    AARCH64.capRegister_def)
   apply (clarsimp simp: cfault_rel_def option_to_ptr_def)
   apply (simp add: seL4_Fault_CapFault_lift is_cap_fault_def)
   apply (frule lookup_failure_rel_fault_lift, assumption)
   apply clarsimp
  apply (clarsimp simp: ct_in_state'_def pred_tcb_at')
  apply (auto simp: ct_in_state'_def sch_act_simple_def intro!: active_ex_cap'
              elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')[1]
  done

lemma ccorres_return_void_catchbrk:
  "ccorres_underlying sr G r xf ar axf P P' hs
     f return_void_C
  \<Longrightarrow> ccorres_underlying sr G r xf ar axf P P' (catchbrk_C # hs)
     f return_void_C"
  apply (simp add: return_void_C_def catchbrk_C_def)
  apply (rule ccorresI')
  apply clarsimp
  apply (erule exec_handlers_Seq_cases')
   prefer 2
   apply (clarsimp elim!: exec_Normal_elim_cases)
  apply (clarsimp elim!: exec_Normal_elim_cases)
  apply (erule exec_handlers.cases, simp_all)
   prefer 2
   apply (auto elim!: exec_Normal_elim_cases)[1]
  apply (clarsimp elim!: exec_Normal_elim_cases)
  apply (erule exec_Normal_elim_cases, simp_all)
  apply (clarsimp elim!: exec_Normal_elim_cases)
  apply (erule(4) ccorresE)
   apply (rule EHAbrupt)
    apply (fastforce intro: exec.intros)
   apply assumption
  apply clarsimp
  apply (frule exec_handlers_less)
   apply clarsimp
  apply fastforce
  done

lemma real_cte_tcbCallerSlot:
  "tcb_at' t s \<Longrightarrow> \<not> real_cte_at' (t + 2 ^ cte_level_bits * tcbCallerSlot) s"
  apply (clarsimp simp: obj_at'_def projectKOs objBits_simps'
                        cte_level_bits_def tcbCallerSlot_def)
  apply (drule_tac x=t and y="t + a" for a in ps_clearD, assumption)
    apply (rule le_neq_trans, simp_all)[1]
    apply (erule is_aligned_no_wrap')
    apply simp
   apply (subst field_simps[symmetric], rule is_aligned_no_overflow3, assumption, simp_all)
  done

lemma handleReply_ccorres:
  "ccorres dc xfdc
       (\<lambda>s. invs' s \<and> st_tcb_at' (\<lambda>a. \<not> isReply a) (ksCurThread s) s \<and> sch_act_simple s)
       UNIV
       []
       (handleReply)
       (Call handleReply_'proc)"
  apply cinit
   apply (rule ccorres_pre_getCurThread)

   apply (simp only: getThreadCallerSlot_def locateSlot_conv)


   apply (rule_tac P="\<lambda>s. thread=ksCurThread s \<and> invs' s \<and> is_aligned thread tcbBlockSizeBits"
                   and r'="\<lambda> a c. c = cte_Ptr a"
                   and xf'="callerSlot_'" and P'=UNIV in ccorres_split_nothrow)
       apply (rule ccorres_from_vcg)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def word_sle_def)
       apply (frule is_aligned_neg_mask_eq)
       apply (frule tcb_at_invs')
       apply (simp add: mask_def tcbCallerSlot_def
              cte_level_bits_def size_of_def
              ptr_add_assertion_positive
              tcb_cnode_index_defs rf_sr_ksCurThread
              rf_sr_tcb_ctes_array_assertion2[THEN array_assertion_shrink_right])
      apply ceqv

     apply (simp del: Collect_const)
     apply (rule ccorres_getSlotCap_cte_at)
     apply (rule ccorres_move_c_guard_cte)
     apply ctac
       apply (wpc, simp_all)
                 apply (rule ccorres_fail)
                apply (simp add: ccap_relation_NullCap_iff cap_tag_defs)
                apply (rule ccorres_split_throws)
                 apply (rule ccorres_Catch)
                 apply csymbr
                 apply (rule ccorres_cond_false)
                 apply (rule ccorres_cond_true)
                 apply simp
                 apply (rule ccorres_return_void_catchbrk)
                 apply (rule ccorres_return_void_C)
                apply (vcg exspec=doReplyTransfer_modifies)
               apply (rule ccorres_fail)+
          apply (wpc, simp_all)
           apply (rule ccorres_fail)
          apply (rule ccorres_split_throws)
           apply (rule ccorres_Catch)
           apply csymbr
           apply (rule ccorres_cond_true)
           apply (frule cap_get_tag_isCap_unfolded_H_cap(8))
           apply simp
           apply (rule ccorres_rhs_assoc)+
           apply csymbr+
           apply (frule cap_get_tag_ReplyCap)
           apply (clarsimp simp: to_bool_def)
           apply (csymbr, csymbr, csymbr)
           apply simp
           apply (rule ccorres_assert2)
           apply (rule ccorres_add_return2)
           apply (ctac (no_vcg))
            apply (rule ccorres_return_void_catchbrk)
            apply (rule ccorres_return_void_C)
           apply wp
          apply (vcg exspec=doReplyTransfer_modifies)
         apply (rule ccorres_fail)+
      apply simp_all
      apply (simp add: getSlotCap_def)
      apply (wp getCTE_wp')[1]
     apply vcg
    apply wp
   apply vcg
  apply clarsimp
  apply (intro allI conjI impI,
        simp_all add: cap_get_tag_isCap_unfolded_H_cap cap_tag_defs)
       apply (rule tcb_aligned', rule tcb_at_invs', simp)
      apply (auto simp: cte_wp_at_ctes_of valid_cap'_def
                     dest!: ctes_of_valid')[1]
      apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps)
     apply (simp add: real_cte_tcbCallerSlot[OF pred_tcb_at'])
     apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps)
    apply (fastforce simp: ccap_relation_reply_helpers cap_get_tag_isCap isCap_simps)+
  done

lemma deleteCallerCap_ccorres [corres]:
  "ccorres dc xfdc
       (\<lambda>s. invs' s \<and> tcb_at' receiver s)
       (UNIV \<inter> {s. receiver_' s = tcb_ptr_to_ctcb_ptr receiver})
       []
       (deleteCallerCap receiver)
       (Call deleteCallerCap_'proc)"
  apply (cinit lift: receiver_')
   apply (simp only: getThreadCallerSlot_def locateSlot_conv)
   apply (rule ccorres_move_array_assertion_tcb_ctes ccorres_Guard_Seq)+
   apply (rule_tac P="\<lambda>_. is_aligned receiver tcbBlockSizeBits" and r'="\<lambda> a c. cte_Ptr a = c"
                   and xf'="callerSlot_'" and P'=UNIV in ccorres_split_nothrow_novcg)
       apply (rule ccorres_from_vcg)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def word_sle_def)
       apply (frule is_aligned_neg_mask_eq)
       apply (simp add: mask_def tcbCallerSlot_def Kernel_C.tcbCaller_def
              cte_level_bits_def size_of_def)
       apply (drule ptr_val_tcb_ptr_mask2)
       apply (simp add: mask_def objBits_defs)
      apply ceqv
     apply (rule ccorres_symb_exec_l)
        apply (rule ccorres_symb_exec_l)
           apply (rule ccorres_symb_exec_r)
             apply (ctac add:  cteDeleteOne_ccorres[where w="ucast cap_reply_cap"])
            apply vcg
           apply (rule conseqPre, vcg, clarsimp simp: rf_sr_def
             gs_set_assn_Delete_cstate_relation[unfolded o_def])
          apply (wp | simp)+
      apply (simp add: getSlotCap_def)
      apply (wp getCTE_wp)+
   apply clarsimp
   apply (simp add: guard_is_UNIV_def ghost_assertion_data_get_def
                        ghost_assertion_data_set_def)
  apply (clarsimp simp: cte_wp_at_ctes_of cap_get_tag_isCap[symmetric]
                        cap_tag_defs tcb_cnode_index_defs word_sle_def
                        tcb_aligned')
  done

(* FIXME:  MOVE to Corres_C.thy *)
lemma ccorres_trim_redundant_throw_break:
  "\<lbrakk>ccorres_underlying rf_sr \<Gamma> arrel axf arrel axf G G' (SKIP # hs) a c;
          \<And>s f. axf (global_exn_var_'_update f s) = axf s \<rbrakk>
  \<Longrightarrow> ccorres_underlying rf_sr \<Gamma> r xf arrel axf G G' (SKIP # hs)
          a (c;; Basic (global_exn_var_'_update (\<lambda>_. Break));; THROW)"
  apply -
  apply (rule ccorres_trim_redundant_throw')
    apply simp
   apply simp
  apply simp
  done

lemma invs_valid_objs_strengthen:
  "invs' s \<longrightarrow> valid_objs' s" by fastforce

lemma option_to_ctcb_ptr_valid_ntfn:
  "valid_ntfn' ntfn s ==> (option_to_ctcb_ptr (ntfnBoundTCB ntfn) = NULL) = (ntfnBoundTCB ntfn = None)"
  apply (cases "ntfnBoundTCB ntfn", simp_all add: option_to_ctcb_ptr_def)
  apply (clarsimp simp: valid_ntfn'_def tcb_at_not_NULL)
  done


lemma deleteCallerCap_valid_ntfn'[wp]:
  "\<lbrace>\<lambda>s. valid_ntfn' x s\<rbrace> deleteCallerCap c \<lbrace>\<lambda>rv s. valid_ntfn' x s\<rbrace>"
  apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_ball_lift hoare_vcg_imp_lift
            | simp add: valid_ntfn'_def split: ntfn.splits)+
   apply auto
  done

lemma hoare_vcg_imp_liftE:
  "\<lbrakk>\<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>, \<lbrace>E\<rbrace>; \<lbrace>Q'\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow>  \<lbrace>\<lambda>s. P' s \<or> Q' s\<rbrace> f \<lbrace>\<lambda>rv s. P rv s \<longrightarrow> Q rv s\<rbrace>, \<lbrace>E\<rbrace>"
  apply (simp add: validE_def valid_def split_def split: sum.splits)
  done


lemma not_obj_at'_ntfn:
  "(\<not>obj_at' (P::Structures_H.notification \<Rightarrow> bool) t s) = (\<not> typ_at' NotificationT t s \<or> obj_at' (Not \<circ> P) t s)"
  apply (simp add: obj_at'_real_def projectKOs typ_at'_def ko_wp_at'_def objBits_simps)
  apply (rule iffI)
   apply (clarsimp)
   apply (case_tac ko)
   apply (clarsimp)+
  done

lemma handleRecv_ccorres:
  notes rf_sr_upd_safe[simp del]
  shows
  "ccorres dc xfdc
       (\<lambda>s. invs' s \<and> st_tcb_at' simple' (ksCurThread s) s \<and> sch_act_sane s)
       {s. isBlocking_' s = from_bool isBlocking}
       []
       (handleRecv isBlocking)
       (Call handleRecv_'proc)"
  supply if_cong[cong] option.case_cong[cong]
  apply (cinit lift: isBlocking_')
   apply (rule ccorres_pre_getCurThread)
   apply (ctac)
     apply (simp add: catch_def)
     apply (simp add: capFault_bindE)
     apply (simp add: bindE_bind_linearise)
     apply (rule_tac xf'=lu_ret___struct_lookupCap_ret_C_'
                        in ccorres_split_nothrow_case_sum)
          apply (rule  capFaultOnFailure_ccorres)
          apply (ctac add: lookupCap_ccorres)
         apply ceqv
        apply clarsimp
        apply (rule ccorres_Catch)
        apply csymbr
        apply (simp add: cap_get_tag_isCap del: Collect_const)
        apply (clarsimp simp: cap_case_EndpointCap_NotificationCap
                              capFaultOnFailure_if_case_sum)
        apply (rule ccorres_cond_both' [where Q=\<top> and Q'=\<top>])
          apply clarsimp
         apply (rule ccorres_rhs_assoc)+
         apply csymbr
         apply (simp add: case_bool_If capFaultOnFailure_if_case_sum)
         apply (rule ccorres_if_cond_throws_break2 [where Q=\<top> and Q'=\<top>])
            apply clarsimp
            apply (simp add: cap_get_tag_isCap[symmetric] cap_get_tag_EndpointCap
                        del: Collect_const)
            apply (simp add: to_bool_def)
           apply (rule ccorres_rhs_assoc)+
           apply (simp add: capFaultOnFailure_def rethrowFailure_def
                            handleE'_def throwError_def)
           apply (rule ccorres_cross_over_guard[where P=\<top>])
           apply (rule ccorres_symb_exec_r)
             apply (rule ccorres_cross_over_guard[where P=\<top>])
             apply (rule ccorres_symb_exec_r)
               apply (rule ccorres_add_return2)
               apply (rule ccorres_split_nothrow_call[where xf'=xfdc and d'="\<lambda>_. break_C"
                                                      and Q="\<lambda>_ _. True" and Q'="\<lambda>_ _. UNIV"])
                      apply (ctac add: handleFault_ccorres)
                     apply simp+
                  apply ceqv
                 apply (rule ccorres_break_return)
                  apply simp+
                apply wp
               apply (vcg exspec=handleFault_modifies)

              apply vcg
             apply (rule conseqPre, vcg)
             apply (clarsimp simp: rf_sr_upd_safe)

            apply vcg
           apply (rule conseqPre, vcg)
           apply (clarsimp simp: rf_sr_upd_safe)

          apply (simp add: liftE_bind)
          apply (ctac)
            apply (rule_tac P="\<lambda>s. ksCurThread s = thread" in ccorres_cross_over_guard)
            apply (ctac add: receiveIPC_ccorres)

           apply (wp hoare_vcg_all_lift)
          apply (rule conseqPost[where Q'=UNIV and A'="{}"], vcg exspec=deleteCallerCap_modifies)
           apply (clarsimp dest!: rf_sr_ksCurThread)
          apply simp
         apply clarsimp
         apply (vcg exspec=handleFault_modifies)

          apply (clarsimp simp: case_bool_If capFaultOnFailure_if_case_sum capFault_bindE)
          apply (simp add: liftE_bindE bind_bindE_assoc bind_assoc)
          apply (rule ccorres_cond_both' [where Q=\<top> and Q'=\<top>])
            apply clarsimp

           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply csymbr
           apply csymbr
           apply csymbr
           apply (rename_tac thread epCPtr rv rva ntfnptr)
           apply (rule_tac P="valid_cap' rv" in ccorres_cross_over_guard)
           apply (simp only: capFault_injection injection_handler_If injection_liftE
                            injection_handler_throwError if_to_top_of_bind)
           apply csymbr
           apply (rule ccorres_abstract_cleanup)
           apply csymbr
           apply csymbr
           apply (rule ccorres_if_lhs)

            apply (rule ccorres_pre_getNotification)
            apply (rename_tac ntfn)
            apply (rule_tac Q="valid_ntfn' ntfn and (\<lambda>s. thread = ksCurThread s)"
                      and Q'="\<lambda>s. ret__unsigned_longlonga = ptr_val (option_to_ctcb_ptr (ntfnBoundTCB ntfn))"
                in ccorres_if_cond_throws_break2)
               apply (clarsimp simp: cap_get_tag_isCap[symmetric] cap_get_tag_NotificationCap
                                     option_to_ctcb_ptr_valid_ntfn rf_sr_ksCurThread)
               apply (auto simp: option_to_ctcb_ptr_def)[1]
              apply (rule ccorres_rhs_assoc)+

              apply (simp add: capFaultOnFailure_def rethrowFailure_def
                               handleE'_def throwError_def)
              apply (rule ccorres_cross_over_guard[where P=\<top>])
              apply (rule ccorres_symb_exec_r)
                apply (rule ccorres_cross_over_guard[where P=\<top>])
                apply (rule ccorres_symb_exec_r)
                  apply (rule ccorres_add_return2)
                  apply (rule ccorres_split_nothrow_call[where xf'=xfdc and d'="\<lambda>_. break_C"
                                               and Q="\<lambda>_ _. True" and Q'="\<lambda>_ _. UNIV"])
                         apply (ctac add: handleFault_ccorres)
                        apply simp+
                     apply ceqv
                    apply (rule ccorres_break_return)
                     apply simp+
                   apply wp
                  apply (vcg exspec=handleFault_modifies)

                 apply vcg
                apply (rule conseqPre, vcg)
                apply (clarsimp simp: rf_sr_upd_safe)

               apply vcg
              apply (rule conseqPre, vcg)
              apply (clarsimp simp: rf_sr_upd_safe)

             apply (simp add: liftE_bind)
             apply (ctac  add: receiveSignal_ccorres)
            apply clarsimp
            apply (vcg exspec=handleFault_modifies)
           apply (rule ccorres_cond_true_seq)
           apply (rule ccorres_split_throws)
            apply (rule ccorres_rhs_assoc)+
            apply (simp add: capFaultOnFailure_def rethrowFailure_def
                                      handleE'_def throwError_def)
            apply (rule ccorres_cross_over_guard[where P=\<top>])
            apply (rule ccorres_symb_exec_r)
              apply (rule ccorres_cross_over_guard[where P=\<top>])
              apply (rule ccorres_symb_exec_r)
                apply (rule ccorres_add_return2)
                apply (ctac add: handleFault_ccorres)
                  apply (rule ccorres_break_return[where P=\<top> and P'=UNIV])
                   apply simp+
                 apply wp
                apply (vcg exspec=handleFault_modifies)

               apply vcg
              apply (rule conseqPre, vcg)
              apply (clarsimp simp: rf_sr_upd_safe)
             apply vcg
            apply (rule conseqPre, vcg)
            apply (clarsimp simp: rf_sr_upd_safe)
           apply (vcg exspec=handleFault_modifies)
        apply (simp add: capFaultOnFailure_def rethrowFailure_def
                         handleE'_def throwError_def)

        apply (rule ccorres_rhs_assoc)+
        apply (rule ccorres_cross_over_guard[where P=\<top>])
        apply (rule ccorres_symb_exec_r)
          apply (rule ccorres_cross_over_guard[where P=\<top>])
          apply (rule ccorres_symb_exec_r)
            apply (ctac add: handleFault_ccorres)
           apply vcg
          apply (rule conseqPre, vcg)
          apply (clarsimp simp: rf_sr_upd_safe)
        apply vcg
        apply (rule conseqPre, vcg)
        apply (clarsimp simp: rf_sr_upd_safe)

       apply clarsimp
       apply (rule ccorres_add_return2)
       apply (rule ccorres_rhs_assoc)+
       apply (rule ccorres_cross_over_guard[where P=\<top>])
       apply (rule ccorres_symb_exec_r)
         apply (ctac add: handleFault_ccorres)
           apply (rule ccorres_split_throws)
            apply (rule ccorres_return_void_C)
           apply vcg
          apply wp
         apply (vcg exspec=handleFault_modifies)
        apply vcg
       apply (rule conseqPre, vcg)
       apply (clarsimp simp: rf_sr_upd_safe)
      apply (wp)
      apply clarsimp
      apply (rename_tac thread epCPtr)
        apply (rule_tac Q'="(\<lambda>rv s. invs' s \<and> st_tcb_at' simple' thread s
               \<and> sch_act_sane s \<and> thread = ksCurThread s
               \<and> valid_cap' rv s)" in hoare_strengthen_postE_R[rotated])
       apply (intro conjI impI allI; clarsimp simp: sch_act_sane_def)
       apply (fastforce dest: obj_at_valid_objs'[OF _ invs_valid_objs'] ko_at_valid_ntfn')
      apply wp
     apply clarsimp
     apply (vcg exspec=isStopped_modifies exspec=lookupCap_modifies)

    apply wp
   apply clarsimp
   apply vcg

  apply (clarsimp simp add: sch_act_sane_def)
  apply (simp add: cap_get_tag_isCap[symmetric] del: rf_sr_upd_safe)
  apply (simp add: Kernel_C.capRegister_def AARCH64_H.capRegister_def ct_in_state'_def
                   AARCH64.capRegister_def C_register_defs
                   tcb_at_invs')
  apply (frule invs_valid_objs')
  apply (frule tcb_aligned'[OF tcb_at_invs'])
  apply clarsimp
  apply (intro conjI impI allI)
           apply (clarsimp simp: cfault_rel_def seL4_Fault_CapFault_lift
                            lookup_fault_missing_capability_lift is_cap_fault_def)+
         apply (clarsimp simp: cap_get_tag_NotificationCap)
         apply (rule cmap_relationE1[OF cmap_relation_ntfn], assumption, erule ko_at_projectKO_opt)
         apply (clarsimp simp: cnotification_relation_def Let_def)
        apply (clarsimp simp: cfault_rel_def seL4_Fault_CapFault_lift
                                 lookup_fault_missing_capability_lift is_cap_fault_def)+
     apply (clarsimp simp: cap_get_tag_NotificationCap)
     apply (simp add: ccap_relation_def to_bool_def)
    apply (clarsimp simp: cap_get_tag_NotificationCap valid_cap'_def)
    apply (drule obj_at_ko_at', clarsimp)
    apply (rule cmap_relationE1[OF cmap_relation_ntfn], assumption, erule ko_at_projectKO_opt)
    apply (clarsimp simp: typ_heap_simps)
   apply (clarsimp simp: cfault_rel_def seL4_Fault_CapFault_lift
                            lookup_fault_missing_capability_lift is_cap_fault_def)+
  apply (case_tac w, clarsimp+)
  done

lemma handleYield_ccorres:
  "ccorres dc xfdc
       (invs' and ct_active')
       UNIV
       []
       (handleYield)
       (Call handleYield_'proc)"
  apply cinit
   apply (rule ccorres_pre_getCurThread)
   apply (ctac add: tcbSchedDequeue_ccorres)
     apply (ctac  add: tcbSchedAppend_ccorres)
       apply (ctac add: rescheduleRequired_ccorres)
      apply (wp weak_sch_act_wf_lift_linear tcbSchedAppend_valid_objs')
     apply (vcg exspec= tcbSchedAppend_modifies)
    apply (wp weak_sch_act_wf_lift_linear)
   apply (vcg exspec= tcbSchedDequeue_modifies)
  apply (clarsimp simp: tcb_at_invs' invs_valid_objs'
                        valid_objs'_maxPriority valid_objs'_maxDomain)
  apply (auto simp: obj_at'_def st_tcb_at'_def ct_in_state'_def valid_objs'_maxDomain)
  done


lemma getIRQState_sp:
  "\<lbrace>P\<rbrace> getIRQState irq \<lbrace>\<lambda>rv s. rv = intStateIRQTable (ksInterruptState s) irq \<and> P s\<rbrace>"
  apply (simp add: getIRQState_def getInterruptState_def)
  apply wp
  apply simp
  done

lemma ccorres_pre_getIRQState:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. irq \<le> ucast Kernel_C.maxIRQ \<and> P (intStateIRQTable (ksInterruptState s) irq) s)
                  {s. \<forall>rv. index (intStateIRQTable_' (globals s)) (unat irq) = irqstate_to_C rv \<longrightarrow> s \<in> P' rv }
                          hs (getIRQState irq >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply (simp add: getIRQState_def getInterruptState_def)
       apply wp
       apply simp
      apply (rule getIRQState_sp)
     apply (simp add: getIRQState_def getInterruptState_def)
    apply assumption
   prefer 2
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply simp
   apply assumption
  apply clarsimp
  apply (erule allE)
  apply (erule impE)
   prefer 2
   apply assumption
  apply (clarsimp simp: rf_sr_def cstate_relation_def
                        Let_def cinterrupt_relation_def)
  done

(* FIXME: move *)
lemma ccorres_ntfn_cases:
  assumes P: "\<And>p b send d. cap = NotificationCap p b send d \<Longrightarrow> ccorres r xf (P p b send d) (P' p b send d) hs (a cap) (c cap)"
  assumes Q: "\<not>isNotificationCap cap \<Longrightarrow> ccorres r xf (Q cap) (Q' cap) hs (a cap) (c cap)"
  shows
  "ccorres r xf (\<lambda>s. (\<forall>p b send d. cap = NotificationCap p b send d \<longrightarrow> P p b send d s) \<and>
                     (\<not>isNotificationCap cap \<longrightarrow> Q cap s))
               ({s. \<forall>p b send d. cap = NotificationCap p b send d \<longrightarrow> s \<in> P' p b send d} \<inter>
                {s. \<not>isNotificationCap cap \<longrightarrow> s \<in> Q' cap})
               hs (a cap) (c cap)"
  apply (cases "isNotificationCap cap")
   apply (simp add: isCap_simps)
   apply (elim exE)
   apply (rule ccorres_guard_imp)
     apply (erule P)
    apply simp
   apply simp
  apply (rule ccorres_guard_imp)
    apply (erule Q)
   apply clarsimp
  apply clarsimp
  done

(* FIXME: generalise the one in Interrupt_C *)
lemma getIRQSlot_ccorres2:
  "ccorres ((=) \<circ> Ptr) slot_'
          \<top> UNIV hs
      (getIRQSlot irq) (\<acute>slot :== CTypesDefs.ptr_add intStateIRQNode_Ptr (uint (ucast irq :: machine_word)))"
  apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: getIRQSlot_def liftM_def getInterruptState_def
                        locateSlot_conv)
  apply (simp add: simpler_gets_def bind_def return_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                        cinterrupt_relation_def size_of_def
                        cte_level_bits_def mult.commute mult.left_commute ucast_nat_def)
  done

lemma getIRQSlot_ccorres3:
  "(\<And>rv. ccorresG rf_sr \<Gamma> r xf (P rv) (P' rv) hs (f rv) c) \<Longrightarrow>
   ccorresG rf_sr \<Gamma> r xf
     (\<lambda>s. P (intStateIRQNode (ksInterruptState s) + 2 ^ cte_level_bits * of_nat (unat irq)) s)
     {s. s \<in> P' (ptr_val (CTypesDefs.ptr_add intStateIRQNode_Ptr (uint (ucast irq :: machine_word))))} hs
     (getIRQSlot irq >>= f) c"
  apply (simp add: getIRQSlot_def locateSlot_conv liftM_def getInterruptState_def)
  apply (intro ccorres_symb_exec_l'[OF _ _gets_sp] empty_fail_gets gets_inv)
  apply (rule ccorres_guard_imp2, assumption)
  by (clarsimp simp: cte_C_size cte_level_bits_def ucast_nat_def
                     rf_sr_def cstate_relation_def Let_def cinterrupt_relation_def
              elim!: rsubst[of "\<lambda>t. _ \<in> P' t"])

lemma scast_maxIRQ_less_eq:
  "(Kernel_C.maxIRQ <s ucast b) = (scast Kernel_C.maxIRQ < b)" for b::irq
  by (auto simp: Kernel_C_maxIRQ word_sless_def word_sle_def sint_ucast_eq_uint is_down
                 word_less_def less_le_not_le maxIRQ_eq_ucast_irq_32_signed_uint)

lemmas scast_maxIRQ_is_less = scast_maxIRQ_less_eq [THEN iffD1]

lemma ucast_maxIRQ_is_less:
  "SCAST(32 signed \<rightarrow> 64) Kernel_C.maxIRQ < UCAST(irq_len \<rightarrow> 64) irq \<Longrightarrow> scast Kernel_C.maxIRQ < irq"
  by (simp add: Kernel_C_maxIRQ)

lemma validIRQcastingLess:
  "Kernel_C.maxIRQ <s ucast b \<Longrightarrow> Kernel_Config.maxIRQ < (b::irq)"
  by (drule scast_maxIRQ_is_less) (simp add: Kernel_C_maxIRQ)

lemma scast_maxIRQ_is_not_less:
  "\<not> Kernel_C.maxIRQ <s ucast b \<Longrightarrow> \<not> (scast Kernel_C.maxIRQ < b)" for b::irq
  by (simp add: scast_maxIRQ_less_eq)

lemma ucast_maxIRQ_is_not_less:
  "\<not> (SCAST(32 signed \<rightarrow> 64) Kernel_C.maxIRQ < UCAST(irq_len \<rightarrow> 64) irq) \<Longrightarrow>
   \<not> (scast Kernel_C.maxIRQ < irq)"
  by (simp add: Kernel_C_maxIRQ)

lemma get_gic_vcpu_ctrl_misr_invs'[wp]:
  "valid invs' (doMachineOp get_gic_vcpu_ctrl_misr) (\<lambda>_. invs')"
  by (simp add: get_gic_vcpu_ctrl_misr_def doMachineOp_def split_def select_f_returns | wp)+

lemma get_gic_vcpu_ctrl_eisr1_invs'[wp]:
  "valid invs' (doMachineOp get_gic_vcpu_ctrl_eisr1) (\<lambda>_. invs')"
  by (simp add: get_gic_vcpu_ctrl_eisr1_def doMachineOp_def split_def select_f_returns | wp)+

lemma get_gic_vcpu_ctrl_eisr0_invs'[wp]:
  "valid invs' (doMachineOp get_gic_vcpu_ctrl_eisr0) (\<lambda>_. invs')"
  by (simp add: get_gic_vcpu_ctrl_eisr0_def doMachineOp_def split_def select_f_returns | wp)+

lemma virq_to_H_arrayp[simp]:
  "virq_to_H (virq_C (ARRAY _. v)) = v"
  by (simp add: virq_to_H_def)

lemma virq_virq_active_set_virqEOIIRQEN_spec':
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. virq_get_tag \<acute>virq = scast virq_virq_active\<rbrace>
       Call virq_virq_active_set_virqEOIIRQEN_'proc
       \<lbrace> \<acute>ret__struct_virq_C = virq_C (ARRAY _. virqSetEOIIRQEN (virq_to_H \<^bsup>s\<^esup>virq) \<^bsup>s\<^esup>v64) \<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1) (* force vcg to unfold non-recursive procedure *)
  apply vcg
  apply (clarsimp simp: virq_to_H_def AARCH64_A.virqSetEOIIRQEN_def)
  apply (case_tac virq)
  apply clarsimp
  apply (rule array_ext)
  apply (clarsimp simp: virq_get_tag_def virq_tag_defs mask_def virq_type_def split: if_split)
  done

lemma virq_virq_invalid_set_virqEOIIRQEN_spec':
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. virq_get_tag \<acute>virq = scast virq_virq_invalid\<rbrace>
       Call virq_virq_invalid_set_virqEOIIRQEN_'proc
       \<lbrace> \<acute>ret__struct_virq_C = virq_C (ARRAY _. virqSetEOIIRQEN (virq_to_H \<^bsup>s\<^esup>virq) \<^bsup>s\<^esup>v64) \<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1) (* force vcg to unfold non-recursive procedure *)
  apply vcg
  apply (clarsimp simp: virq_to_H_def AARCH64_A.virqSetEOIIRQEN_def)
  apply (case_tac virq)
  apply clarsimp
  apply (rule array_ext)
  apply (clarsimp simp: virq_get_tag_def virq_tag_defs mask_def virq_type_def split: if_split)
  done

lemma virq_virq_pending_set_virqEOIIRQEN_spec':
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. virq_get_tag \<acute>virq = scast virq_virq_pending\<rbrace>
       Call virq_virq_pending_set_virqEOIIRQEN_'proc
       \<lbrace> \<acute>ret__struct_virq_C = virq_C (ARRAY _. virqSetEOIIRQEN (virq_to_H \<^bsup>s\<^esup>virq) \<^bsup>s\<^esup>v64) \<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1) (* force vcg to unfold non-recursive procedure *)
  apply vcg
  apply (clarsimp simp: virq_to_H_def AARCH64_A.virqSetEOIIRQEN_def)
  apply (case_tac virq)
  apply clarsimp
  apply (rule array_ext)
  apply (clarsimp simp: virq_get_tag_def virq_tag_defs mask_def virq_type_def split: if_split)
  done

lemma gic_vcpu_num_list_regs_cross_over:
  "\<lbrakk> of_nat (armKSGICVCPUNumListRegs (ksArchState s)) = gic_vcpu_num_list_regs_' t;
     valid_arch_state' s \<rbrakk>
   \<Longrightarrow> gic_vcpu_num_list_regs_' t \<le> 0x3F"
  apply (drule sym, simp)
  apply (clarsimp simp: valid_arch_state'_def max_armKSGICVCPUNumListRegs_def)
  apply (clarsimp simp: word_le_nat_alt unat_of_nat)
  done

lemma virqSetEOIIRQEN_id:
  "\<lbrakk> virq_get_tag (virq_C (ARRAY _. idx)) \<noteq> scast virq_virq_active;
     virq_get_tag (virq_C (ARRAY _. idx)) \<noteq> scast virq_virq_pending;
     virq_get_tag (virq_C (ARRAY _. idx)) \<noteq> scast virq_virq_invalid \<rbrakk>
    \<Longrightarrow> virqSetEOIIRQEN idx 0 = idx"
  apply (clarsimp simp: AARCH64_A.virqSetEOIIRQEN_def virq_get_tag_def virq_tag_defs mask_def
                        virq_type_def
                  split: if_split)
  apply (rule_tac x="idx >> 28" in two_bits_cases; simp)
  done

lemma vgicUpdateLR_ccorres_armHSCurVCPU:
  "\<lbrakk> v' = v ; n' = n ; n \<le> 63 \<rbrakk> \<Longrightarrow>
   ccorres dc xfdc
       (\<lambda>s. (\<exists>active. armHSCurVCPU (ksArchState s) = Some (vcpuptr,active) \<and>
                      vcpu_at' vcpuptr s))
       UNIV hs
       (vgicUpdateLR vcpuptr n v)
       (Guard C_Guard {s. s \<Turnstile>\<^sub>c armHSCurVCPU_' (globals s)}
         (Basic_heap_update
           (\<lambda>s. vgic_lr_C_Ptr &(vgic_C_Ptr &((armHSCurVCPU_' (globals s))\<rightarrow>[''vgic_C''])\<rightarrow>[''lr_C'']))
           (\<lambda>s. Arrays.update
                  (h_val (hrs_mem (t_hrs_' (globals s)))
                  (vgic_lr_C_Ptr &(vgic_C_Ptr &((armHSCurVCPU_' (globals s))\<rightarrow>[''vgic_C''])\<rightarrow>[''lr_C''])))
                  n' (virq_C (ARRAY _. v')))))"
  supply from_bool_eq_if[simp] from_bool_eq_if'[simp] from_bool_0[simp]
  apply (rule ccorres_guard_imp)
    apply (rule_tac P="\<lambda>s. armHSCurVCPU (ksArchState s) \<noteq> None
                            \<and> vcpu_at' (fst (the (armHSCurVCPU (ksArchState s)))) s"
                and P'=\<top> in ccorres_move_Guard)
     apply clarsimp
     apply (frule rf_sr_ksArchState_armHSCurVCPU)
     apply (clarsimp simp: cur_vcpu_relation_def split: option.splits)
     apply (fastforce simp: move_c_guard_vcpu[rule_format, simplified])
    apply (simp add: vgicUpdate_def vcpuUpdate_def vgicUpdateLR_def)
    apply (rule ccorres_pre_getObject_vcpu, rename_tac vcpu)
    apply (rule_tac P="\<lambda>s. armHSCurVCPU (ksArchState s) \<noteq> None
                            \<and> (fst (the (armHSCurVCPU (ksArchState s)))) = vcpuptr"
                    in ccorres_cross_over_guard)
    apply (rule_tac P="ko_at' vcpu vcpuptr"
      and P'="{s. armHSCurVCPU_' (globals s) = vcpu_Ptr vcpuptr }" in setObject_ccorres_helper
      , rule conseqPre, vcg)
      apply clarsimp
      apply (rule cmap_relationE1[OF cmap_relation_vcpu]
             ; (clarsimp simp: objBits_simps bit_simps)?)
        apply (assumption, erule ko_at_projectKO_opt)
      apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                            cmachine_state_relation_def update_vcpu_map_to_vcpu
                            typ_heap_simps' cpspace_relation_def update_vcpu_map_tos)
      apply (erule (1) cmap_relation_updI
             ; clarsimp simp: cvcpu_relation_regs_def cvgic_relation_def cvcpu_vppi_masked_relation_def
             ; (rule refl)?)
      apply (fastforce simp: virq_to_H_def split: if_split)
     apply (clarsimp simp add: objBits_simps bit_simps)+
  apply (clarsimp dest!: rf_sr_ksArchState_armHSCurVCPU simp: cur_vcpu_relation_def split: option.splits)
  done

(* folded calculation of eisr used in vgicMaintenance *)
definition
  eisr_calc :: "32 word \<Rightarrow> 32 word \<Rightarrow> nat"
where
  "eisr_calc eisr0 eisr1 \<equiv> if eisr0 \<noteq> 0 then word_ctz eisr0 else word_ctz eisr1 + 32"

lemma ccorres_vgicMaintenance:
  notes Collect_const[simp del]
  notes virq_virq_active_set_virqEOIIRQEN_spec = virq_virq_active_set_virqEOIIRQEN_spec'
  notes virq_virq_invalid_set_virqEOIIRQEN_spec = virq_virq_invalid_set_virqEOIIRQEN_spec'
  notes virq_virq_pending_set_virqEOIIRQEN_spec = virq_virq_pending_set_virqEOIIRQEN_spec'
  shows
  "ccorres dc xfdc
     (\<lambda>s. invs' s \<and> sch_act_not (ksCurThread s) s)
     UNIV hs
     vgicMaintenance (Call VGICMaintenance_'proc)"
  (is "ccorres _ _ ?PRE _ _ _ _")
proof -

  (* There are multiple helper lemmas to cover all the different word casts in C. The "32 word"
     comes from actual machine register sizes. "32 signed word" comes from integer constants,
     "64 word" is machine_word, and "64 signed word" comes from the return value of ctzl.
     The recurring 0x20/32 usually refer to the number of bits in a 32-bit word. *)

  have scast_mw_int_ctz_eq:
    "SCAST(machine_word_len \<rightarrow> int_literal_len) (of_nat (word_ctz x)) = of_nat (word_ctz x)"
    for x :: "32 word"
    using word_ctz_le[of x]
    by (subst scast_of_nat_small; simp add: word_ctz_le)

  have scast_int_mw_ctz_eq:
    "SCAST(int_literal_len \<rightarrow> machine_word_len) (of_nat (word_ctz x)) = of_nat (word_ctz x)"
    for x :: "32 word"
    using word_ctz_le[of x]
    by (subst scast_of_nat_small; simp add: word_ctz_le)

  have scast_s64_int_ctz_eq:
    "SCAST(64 signed \<rightarrow> int_literal_len) (word_of_nat (word_ctz x)) = word_of_nat (word_ctz x)"
    for x :: "32 word"
    using word_ctz_le[of x]
    by (subst scast_of_nat_small; simp add: word_ctz_le)

  have ctz_add_0x20_mw_int_eq:
    "SCAST(machine_word_len \<rightarrow> int_literal_len) (word_of_nat (word_ctz x) + 0x20)
     = word_of_nat (word_ctz x) + 0x20" for x :: "32 word"
  proof -
    have n32: "(0x20 :: machine_word) = of_nat 32" by simp

    show ?thesis
      using word_ctz_le[of x]
      apply (subst n32, subst of_nat_add[symmetric])
      apply (subst scast_of_nat_small; simp)
      done
  qed

  have ctz_add_0x20_unat_mw_eq:
    "unat (word_of_nat (word_ctz x) + 0x20 :: machine_word) = word_ctz x + 0x20"
    for x :: "32 word"
  proof -
    have n32: "(0x20 :: 64 word) = of_nat 32" by simp

    show ?thesis
      using word_ctz_le[of x]
      apply (subst n32, subst of_nat_add[symmetric])
      apply (subst unat_of_nat_eq; simp)
      done
  qed

  have ctz_add_0x20_int_mw_eq:
    "SCAST(int_literal_len \<rightarrow> machine_word_len) (word_of_nat (word_ctz x) + 0x20)
     = word_of_nat (word_ctz x) + 0x20" for x :: "32 word"
  proof -
    have n32: "(0x20 :: int_word) = of_nat 32" by simp

    show ?thesis
      using word_ctz_le[of x]
      apply (subst n32, subst of_nat_add[symmetric])
      apply (subst scast_of_nat_small; simp)
      done
  qed

  have ctz_add_0x20_s64_int_eq:
    "SCAST(64 signed \<rightarrow> int_literal_len) (word_of_nat (word_ctz x) + 0x20)
     = word_of_nat (word_ctz x) + 0x20" for x :: "32 word"
  proof -
    have n32: "(0x20 :: 64 signed word) = of_nat 32" by simp

    show ?thesis
      using word_ctz_le[of x]
      apply (subst n32, subst of_nat_add[symmetric])
      apply (subst scast_of_nat_small; simp)
      done
  qed

  have sint_s64_ctz_ge_0:
    "0 \<le> sint (word_of_nat (word_ctz x) :: 64 signed word)" for x :: "32 word"
    using word_ctz_le[of x]
    by (simp add: signed_of_nat bit_iff_odd)

  have sint_s64_ctz_le_32:
    "sint (word_of_nat (word_ctz x) :: 64 signed word) \<le> 32" for x :: "32 word"
    using word_ctz_le[of x]
    by (simp add: signed_of_nat signed_take_bit_int_eq_self)

  have sint_int_ctz_ge_0:
    "0 \<le> sint (word_of_nat (word_ctz x) :: int_word)" for x :: "32 word"
    using word_ctz_le[of x]
    by (simp add: signed_of_nat bit_iff_odd)

  have sint_int_ctz_less_32:
    "x \<noteq> 0 \<Longrightarrow> sint (word_of_nat (word_ctz x) :: int_word) < 32" for x :: "32 word"
    by (drule word_ctz_less, simp add: signed_of_nat signed_take_bit_int_eq_self)

  have unat_of_nat_ctz_plus_32s:
    "unat (of_nat (word_ctz w) + (0x20 :: int_word)) = word_ctz w + 32" for w :: "32 word"
    apply (subst unat_add_lem' ; clarsimp simp: unat_of_nat_ctz_smw)
    using word_ctz_le[where w=w, simplified] by (auto simp: unat_of_nat_eq)

  have unat_of_nat_ctz_plus_32:
    "unat (of_nat (word_ctz w) + (0x20 :: 32 word)) = word_ctz w + 32" for w :: "32 word"
    apply (subst unat_add_lem' ; clarsimp simp: unat_of_nat_ctz_mw)
    using word_ctz_le[where w=w, simplified] by (auto simp: unat_of_nat_eq)

  have eisr_calc_le:
    "eisr0 = 0 \<longrightarrow> eisr1 \<noteq> 0
     \<Longrightarrow> eisr_calc eisr0 eisr1 \<le> 63"
    for eisr0 and eisr1
    using word_ctz_le[where w=eisr0]  word_ctz_less[where w=eisr1]
    by (clarsimp simp: eisr_calc_def split: if_splits)

  have of_nat_word_ctz_0x21helper:
    "0x21 + word_of_nat (word_ctz w) \<noteq> (0 :: int_word)" for w :: "32 word"
    apply (subst unat_arith_simps, simp)
    apply (subst unat_add_lem'; clarsimp simp: unat_of_nat_ctz_smw)
    using word_ctz_le[where w=w, simplified]
    by simp

  show ?thesis
    supply if_cong[cong]
    apply (cinit)
     apply (rule ccorres_pre_getCurVCPU, rename_tac vcpuPtr_opt)
     apply wpc
      (* no current vcpu *)
      apply (rule ccorres_cond_true_seq)
      apply ccorres_rewrite
      apply (rule ccorres_return_void_C)
     (* have current vcpu *)
     apply clarsimp
     apply (rename_tac vcpuPtr active)
     apply wpfix
     apply wpc
      (* handle inactive current vcpu first *)
      prefer 2
      apply clarsimp
      apply (rule ccorres_cond_true_seq)
      apply ccorres_rewrite
      apply (rule ccorres_return_void_C)
     (* have active current vcpu, handle VGICMaintenance *)
     apply clarsimp
     apply (rule ccorres_cond_false_seq)
     apply ccorres_rewrite

     apply (ctac (no_vcg) add: get_gic_vcpu_ctrl_eisr0_ccorres)
      apply (ctac (no_vcg) add: get_gic_vcpu_ctrl_eisr1_ccorres)
       apply (ctac (no_vcg) add: get_gic_vcpu_ctrl_misr_ccorres)
        apply (rule ccorres_pre_gets_armKSGICVCPUNumListRegs_ksArchState[simplified comp_def],
               rename_tac num_list_regs)
        apply clarsimp
        apply (rule ccorres_Cond_rhs_Seq ; (clarsimp simp: vgicHCREN_def))
         apply (rule ccorres_rhs_assoc)+
         apply csymbr
         apply (fold eisr_calc_def)
         apply (rule_tac xf'=irq_idx_'
                   and val="if eisr0 \<noteq> 0
                               then of_nat (word_ctz eisr0)
                               else (if eisr1 \<noteq> 0 then of_nat (word_ctz eisr1 + 32) else -1)"
                   and R=\<top> and R'=UNIV
                   in ccorres_symb_exec_r_known_rv)
            apply clarsimp
            apply (rule conseqPre, vcg)


    subgoal by (clarsimp simp: ucast_up_preserves_not0 word_ctz_upcast_id_32_64 scast_s64_int_ctz_eq
                               ctz_add_0x20_s64_int_eq sint_s64_ctz_ge_0
                               order.trans[OF sint_s64_ctz_le_32])

           apply ceqv
          apply clarsimp
          apply (simp add: if_to_top_of_bind)
          apply (rule_tac C'="{s. eisr0 = 0 \<and> eisr1 = 0
                                   \<or> num_list_regs \<le> eisr_calc eisr0 eisr1}"
                     and Q="\<lambda>s. num_list_regs \<le> 63"
                     and Q'="{s. gic_vcpu_num_list_regs_' (globals s) = of_nat num_list_regs}"
                     in ccorres_rewrite_cond_sr_Seq)
           apply clarsimp
    subgoal for _ eisr0 eisr1
      using word_ctz_not_minus_1[where w=eisr1] word_ctz_not_minus_1[where w=eisr0]
      by (clarsimp split: if_splits simp: eisr_calc_def word_le_nat_alt unat_of_nat_eq
                                          of_nat_eq_signed_scast of_nat_word_ctz_0x21helper
                                          ctz_add_0x20_int_mw_eq scast_int_mw_ctz_eq
                                          ctz_add_0x20_unat_mw_eq less_trans[OF word_ctz_less])
          apply (rule ccorres_Cond_rhs_Seq)

           (* check if current thread is runnable, if so handle fault *)
           (* NOTE: this block repeats three times in the proof of ccorres_vgicMaintenance *)
           apply clarsimp
           apply (rule ccorres_inst[where P="?PRE" and P'=UNIV])
    subgoal for _ _ eisr0 eisr1
      apply (rule ccorres_guard_imp)
        apply (rule ccorres_pre_getCurThread, rename_tac cthread)
        apply (rule_tac P="tcb_at' cthread" in ccorres_cross_over_guard)
        apply (rule ccorres_symb_exec_r)
          apply (ctac) (* isRunnable *)
            apply (clarsimp simp: when_def to_bool_def)
            apply (rule ccorres_cond[where R=\<top>], simp)
             apply (ctac add: handleFault_ccorres)
            apply (rule ccorres_return_Skip)
           apply wpsimp
          apply vcg
         apply vcg
        apply (rule conseqPre, vcg, clarsimp)
       apply clarsimp
       apply (clarsimp simp: pred_tcb_at'_def tcb_runnable_imp_simple tcb_at_invs')
      apply clarsimp
      apply (drule (1) obj_at_cslift_tcb)
      apply (clarsimp simp: cfault_rel_def seL4_Fault_VGICMaintenance_lift_def
                            seL4_Fault_lift_def seL4_Fault_tag_defs is_cap_fault_def Let_def
                            eisr_calc_def mask_eq_iff
                      split: if_splits
             ; fastforce simp: uint_nat unat_of_nat_ctz_mw
                        dest: word_ctz_less[where w=eisr1] word_ctz_less[where w=eisr0])
      done

          apply (simp only:) (* rewrite if condition to False *)
          apply (clarsimp simp: bind_assoc)
          apply (rule ccorres_rhs_assoc)+
          apply (ctac add: get_gic_vcpu_ctrl_lr_ccorres)
            apply (rename_tac virq virq')
            apply clarsimp

            apply (prop_tac "(if eisr0 \<noteq> 0 then of_nat (word_ctz eisr0)
                              else if eisr1 \<noteq> 0 then of_nat (word_ctz eisr1) + 32 else - 1)
                              = (of_nat (eisr_calc eisr0 eisr1) :: (machine_word_len sword))")
             apply (fastforce split: if_splits simp: eisr_calc_def)

            (* getting type and setting EOIIRQEN for valid virq types is captured by virqSetEOIIRQEN *)
            apply (rule ccorres_rhs_assoc2)
            apply (rule_tac xf'=virq_'
                     and val="virq_C (ARRAY _. AARCH64_H.virqSetEOIIRQEN virq 0)"
                     and R=\<top> and R'="{s. virq_' s = virq_C (ARRAY _. virq)}"
                     in ccorres_symb_exec_r_known_rv)
               apply (rule conseqPre, vcg)
               apply (fastforce simp: virqSetEOIIRQEN_id[simplified])
              apply ceqv
             apply (ctac add: set_gic_vcpu_ctrl_lr_ccorres)
               apply clarsimp

               (* we already know we have a current active vcpu from the haskell *)
               (* FIXME: if we already know we have an active vcpu, there's no point having the C
                         code check for it *)
               apply (rule_tac Q="\<lambda>s. (armHSCurVCPU \<circ> ksArchState) s = Some (vcpuPtr, True)"
                           and Q'=UNIV and C'=UNIV
                        in ccorres_rewrite_cond_sr_Seq)
                apply (solves \<open>clarsimp dest!: rf_sr_ksArchState_armHSCurVCPU
                                        simp: cur_vcpu_relation_def\<close>)
               apply ccorres_rewrite
               apply (rule ccorres_split_nothrow) (* updating vgic LR of current vcpu *)
                   (* active *)
                   apply (rule ccorres_move_const_guards)+
                   apply (rule vgicUpdateLR_ccorres_armHSCurVCPU ; clarsimp simp: word_ctz_le)
                    apply (fastforce dest: word_ctz_less
                                     simp: eisr_calc_def unat_of_nat_ctz_smw unat_of_nat_ctz_plus_32s)
                   apply (erule eisr_calc_le)
                  apply ceqv

                 (* check if current thread is runnable, if so handle fault *)
                 apply clarsimp
                 apply (rule ccorres_inst[where P="?PRE" and P'=UNIV])
    subgoal for _ _ eisr0 eisr1
      apply (rule ccorres_guard_imp)
        apply (rule ccorres_pre_getCurThread, rename_tac cthread)
        apply (rule_tac P="tcb_at' cthread" in ccorres_cross_over_guard)
        apply (rule ccorres_symb_exec_r)
          apply (ctac) (* isRunnable *)
            apply (clarsimp simp: when_def to_bool_def)
            apply (rule ccorres_cond[where R=\<top>], simp)
             apply (ctac add: handleFault_ccorres)
            apply (rule ccorres_return_Skip)
           apply wpsimp
          apply vcg
         apply vcg
        apply (rule conseqPre, vcg, clarsimp)
       apply clarsimp
       apply (clarsimp simp: pred_tcb_at'_def tcb_runnable_imp_simple tcb_at_invs')
      apply clarsimp
      apply (drule (1) obj_at_cslift_tcb)
      apply (clarsimp simp: cfault_rel_def seL4_Fault_VGICMaintenance_lift_def
                            seL4_Fault_lift_def seL4_Fault_tag_defs is_cap_fault_def Let_def
                            eisr_calc_def and_mask_eq_iff_le_mask word_le_nat_alt
                            ctz_add_0x20_int_mw_eq scast_int_mw_ctz_eq ctz_add_0x20_unat_mw_eq
                      split: if_splits;
             fastforce simp: unat_of_nat_eq mask_def
                       dest!: word_ctz_less[where w=eisr0] word_ctz_less[where w=eisr1])
      done
                apply wpsimp
                apply wps
                apply wpsimp
               apply clarsimp
               apply vcg
              apply (wpsimp wp: hoare_vcg_const_imp_lift hoare_vcg_all_lift hoare_vcg_imp_lift'
                     | assumption (* schematic asm *)
                     | clarsimp simp: conj_comms cong: conj_cong
                     | wps)+
             apply (vcg exspec=set_gic_vcpu_ctrl_lr_modifies)
            apply clarsimp
            apply (vcg exspec=set_gic_vcpu_ctrl_lr_modifies)
           apply (wpsimp wp: hoare_vcg_const_imp_lift hoare_vcg_all_lift hoare_vcg_imp_lift'
                  | wps)+
          apply (vcg exspec=get_gic_vcpu_ctrl_lr_modifies)
         apply clarsimp
         apply vcg

        (* check if current thread is runnable, if so handle fault *)
        apply (rule ccorres_inst[where P="?PRE" and P'=UNIV])
    subgoal for _ _ eisr0 eisr1
      apply (rule ccorres_guard_imp)
        apply (rule ccorres_pre_getCurThread, rename_tac cthread)
        apply (rule_tac P="tcb_at' cthread" in ccorres_cross_over_guard)
        apply (rule ccorres_symb_exec_r)
          apply (ctac) (* isRunnable *)
            apply (clarsimp simp: when_def to_bool_def)
            apply (rule ccorres_cond[where R=\<top>], simp)
             apply (ctac add: handleFault_ccorres)
            apply (rule ccorres_return_Skip)
           apply wpsimp
          apply vcg
         apply vcg
        apply (rule conseqPre, vcg, clarsimp)
       apply clarsimp
       apply (clarsimp simp: pred_tcb_at'_def tcb_runnable_imp_simple tcb_at_invs')
      apply clarsimp
      apply (drule (1) obj_at_cslift_tcb)
      apply (clarsimp simp: cfault_rel_def seL4_Fault_VGICMaintenance_lift_def
                            seL4_Fault_lift_def seL4_Fault_tag_defs is_cap_fault_def Let_def
                            eisr_calc_def mask_eq_iff
                      split: if_splits
             ; fastforce simp: uint_nat unat_of_nat_ctz_mw
                        dest: word_ctz_less[where w=eisr1] word_ctz_less[where w=eisr0])
      done

       (* clean up get_gic_vcpu_ctrl_misr postcondition *)
       apply (wp hoare_vcg_all_lift)
       apply (rule_tac Q'="\<lambda>_ s. ?PRE s \<and> armHSCurVCPU (ksArchState s) = Some (vcpuPtr, active)" in hoare_post_imp)
        apply clarsimp
    subgoal for _ _ eisr0 eisr1
      apply (clarsimp simp: invs'_HScurVCPU_vcpu_at' valid_arch_state'_def max_armKSGICVCPUNumListRegs_def dest!: invs_arch_state')
      using sint_ctz[where x=eisr0, simplified]
      apply (clarsimp simp: word_sless_alt word_sle_eq sint_int_ctz_ge_0 split: if_split)
      using sint_ctz[where x=eisr1, simplified]
      apply (subst signed_arith_sint; clarsimp simp: word_size; simp add: sint_int_ctz_ge_0)
      using sint_ctz[where x=eisr1, simplified]
      apply (subst signed_arith_sint; clarsimp simp: word_size; simp add: sint_int_ctz_less_32)
      done
       apply clarsimp
       apply wpsimp+
  apply (clarsimp simp: cur_vcpu_relation_def eisr_calc_def ucast_up_preserves_not0
                        ctz_add_0x20_mw_int_eq scast_mw_int_ctz_eq
                  split: option.splits)
  done
qed

lemma vcpuUpdate_vppi_masked_ccorres_armHSCurVCPU:
  "\<lbrakk> v' = from_bool v ; n' = fromEnum n \<rbrakk> \<Longrightarrow>
   ccorres dc xfdc
       (\<lambda>s. (armHSCurVCPU (ksArchState s) \<noteq> None) \<and>
          (fst (the (armHSCurVCPU (ksArchState s)))) = vcpuptr \<and>
          vcpu_at' (fst (the (armHSCurVCPU (ksArchState s)))) s)
       UNIV hs
       (vcpuUpdate vcpuptr
            (\<lambda>vcpu.
                vcpuVPPIMasked_update
                 (\<lambda>_ a. if a = n then v else vcpuVPPIMasked vcpu a) vcpu))
       (Guard C_Guard {s. s \<Turnstile>\<^sub>c armHSCurVCPU_' (globals s)}
         (Basic_heap_update
           (\<lambda>s. vcpu_vppi_masked_C_Ptr &((armHSCurVCPU_' (globals s))\<rightarrow>[''vppi_masked_C'']))
           (\<lambda>s. Arrays.update
                  (h_val (hrs_mem (t_hrs_' (globals s)))
                  ((vcpu_vppi_masked_C_Ptr &((armHSCurVCPU_' (globals s))\<rightarrow>[''vppi_masked_C'']))))
                  n' v')))"
  supply from_bool_eq_if[simp] from_bool_eq_if'[simp] from_bool_0[simp]
  apply (rule ccorres_guard_imp)
    apply (rule_tac P="\<lambda>s. armHSCurVCPU (ksArchState s) \<noteq> None
                            \<and> vcpu_at' (fst (the (armHSCurVCPU (ksArchState s)))) s"
                and P'=\<top> in ccorres_move_Guard)
     apply clarsimp
     apply (frule rf_sr_ksArchState_armHSCurVCPU)
     apply (clarsimp simp: cur_vcpu_relation_def split: option.splits)
     apply (fastforce simp: move_c_guard_vcpu[rule_format, simplified])
    apply (simp add: vgicUpdate_def vcpuUpdate_def vgicUpdateLR_def)
    apply (rule ccorres_pre_getObject_vcpu, rename_tac vcpu)
    apply (rule_tac P="\<lambda>s. armHSCurVCPU (ksArchState s) \<noteq> None
                            \<and> (fst (the (armHSCurVCPU (ksArchState s)))) = vcpuptr"
                    in ccorres_cross_over_guard)
    apply (rule_tac P="ko_at' vcpu vcpuptr"
      and P'="{s. armHSCurVCPU_' (globals s) = vcpu_Ptr vcpuptr }" in setObject_ccorres_helper
      , rule conseqPre, vcg)
      apply clarsimp
      apply (rule cmap_relationE1[OF cmap_relation_vcpu]
             ; (clarsimp simp: objBits_simps archObjSize_def bit_simps)?)
        apply (assumption, erule ko_at_projectKO_opt)
      apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                            cmachine_state_relation_def update_vcpu_map_to_vcpu
                            typ_heap_simps' cpspace_relation_def update_vcpu_map_tos)
      apply (erule (1) cmap_relation_updI
             ; clarsimp simp: cvcpu_relation_regs_def cvgic_relation_def cvcpu_vppi_masked_relation_def
             ; (rule refl)?)

      apply (split if_split)
      apply (rule conjI)
       apply clarsimp
  using maxBound_is_bound[where 'a=vppievent_irq, simplified fromEnum_maxBound_vppievent_irq_def]
       apply -
       apply (clarsimp simp: fromEnum_eq_iff less_eq_Suc_le fromEnum_eq_iff split: if_split)
      apply (rule impI)
      apply (subst Arrays.index_update2, simp)
       apply (rule vppievent_irq_noteq_fromEnum_mono)
       apply simp
      apply blast
     apply (clarsimp simp add: objBits_simps archObjSize_def bit_simps)+
  apply (clarsimp dest!: rf_sr_ksArchState_armHSCurVCPU simp: cur_vcpu_relation_def split: option.splits)
  done

lemma ccorres_VPPIEvent:
  notes Collect_const[simp del]
  shows
  "ccorres dc xfdc
     (\<lambda>s. invs' s \<and> sch_act_not (ksCurThread s) s \<and> irqVPPIEventIndex irq \<noteq> None)
     \<lbrace>\<acute>irq = ucast irq\<rbrace> hs
     (vppiEvent irq) (Call VPPIEvent_'proc)"
  (is "ccorres _ _ ?PRE _ _ _ _")
proof -
  show ?thesis
    apply (cinit lift: irq_')
     apply (rule_tac P="irqVPPIEventIndex irq \<noteq> None" in ccorres_gen_asm)
     apply (rule ccorres_pre_getCurVCPU, rename_tac vcpuPtr_opt)
     apply wpc
      (* no current vcpu *)
      apply clarsimp
      apply (rule ccorres_cond_false)
      apply ccorres_rewrite
      apply (rule ccorres_return_Skip)
     (* have current vcpu *)
     apply clarsimp
     apply (rename_tac vcpuPtr active)
     apply wpfix
     apply wpc
      (* handle inactive current vcpu first *)
      prefer 2
      apply clarsimp
      apply (rule ccorres_cond_false)
      apply ccorres_rewrite
      apply (rule ccorres_return_Skip)
     (* have active current vcpu, handle VGICMaintenance *)
     apply clarsimp
     apply (rule ccorres_cond_true)
     apply ccorres_rewrite
     apply (rule ccorres_rhs_assoc)+
     apply (ctac (no_vcg) add: maskInterrupt_ccorres)
      apply csymbr
      (* updating vppi mask of current vcpu *)
      apply (rule ccorres_split_nothrow)
          apply clarsimp
          apply (rule ccorres_move_const_guards)+
          apply (rule vcpuUpdate_vppi_masked_ccorres_armHSCurVCPU; clarsimp)
         apply ceqv

        (* check if current thread is runnable, if so handle fault *)
        apply (rule ccorres_inst[where P="?PRE" and P'=UNIV])
    subgoal for _ _ eisr0 eisr1
      apply (rule ccorres_guard_imp)
        apply (rule ccorres_pre_getCurThread, rename_tac cthread)
        apply (rule_tac P="tcb_at' cthread" in ccorres_cross_over_guard)
        apply (rule ccorres_symb_exec_r)
          apply (ctac) (* isRunnable *)
            apply (clarsimp simp: when_def to_bool_def)
            apply (rule ccorres_cond[where R=\<top>], simp)
             apply (ctac add: handleFault_ccorres)
            apply (rule ccorres_return_Skip)
           apply wpsimp
          apply vcg
         apply vcg
        apply (rule conseqPre, vcg, clarsimp)
       apply clarsimp
       apply (clarsimp simp: pred_tcb_at'_def tcb_runnable_imp_simple tcb_at_invs')
      apply clarsimp
      apply (drule (1) obj_at_cslift_tcb)
      apply (clarsimp simp: cfault_rel_def seL4_Fault_VPPIEvent_lift_def
                            seL4_Fault_lift_def seL4_Fault_tag_defs is_cap_fault_def Let_def
                            mask_eq_iff irq_len_val
                      split: if_splits)
      apply (simp add: ucast_and_mask ge_mask_eq irq_len_val ucast_and_mask_source word_and_le1)
      done

        apply (wpsimp simp: vcpuUpdate_def wp: setVCPU_VPPIMasked_invs' | wps)+
      apply vcg
     apply (wpsimp wp: dmo_maskInterrupt_True
                   simp: irqVPPIEventIndex_def IRQ_def fromEnum_def enum_vppievent_irq
                   split: if_splits
            | wps)+
    apply (clarsimp simp: cur_vcpu_relation_def invs'_HScurVCPU_vcpu_at' irqVTimerEvent_def
                          word_le_nat_alt mask_def
                    split: option.splits)
    done
qed

lemma ccorres_handleReservedIRQ:
  "ccorres dc xfdc
    (invs' and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> sch_act_not (ksCurThread s) s))
    (UNIV \<inter> {s. irq_' s = ucast irq}) hs
    (handleReservedIRQ irq) (Call handleReservedIRQ_'proc)"
  supply Collect_const[simp del]
  apply (cinit lift: irq_')
   apply (clarsimp simp: ucast_up_ucast is_up)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (clarsimp simp: ucast_up_ucast is_up)
    apply ccorres_rewrite
    apply (prop_tac "irq = irqVGICMaintenance")
     apply (clarsimp simp: ucast_up_ucast is_up irqVGICMaintenance_def)
     apply (simp flip: word_unat.Rep_inject)
    apply (simp add: irqVGICMaintenance_def irqVPPIEventIndex_def IRQ_def irqVTimerEvent_def)
    apply (rule ccorres_add_return2)
    apply (ctac (no_vcg) add: ccorres_vgicMaintenance)
     apply (rule ccorres_return_void_C)
    apply wpsimp
   (* potentially handling VPPIEvent *)
   apply (simp flip: word_unat.Rep_inject add: irqVGICMaintenance_def)
   apply csymbr
   apply (rule ccorres_when[where R=\<top>])
  subgoal
    by (clarsimp simp: irqVPPIEventIndex_def IRQ_def fromEnum_def enum_vppievent_irq
                       VPPIEventIRQ_invalid_def
                 simp flip: word_unat.Rep_inject split: if_splits)
   apply clarsimp
   apply (rule ccorres_add_return2)
   apply (ctac (no_vcg) add: ccorres_VPPIEvent)
    apply (rule ccorres_return_void_C)
   apply wpsimp
  apply clarsimp
  apply (clarsimp simp: irqVPPIEventIndex_def IRQ_def non_kernel_IRQs_def irqVGICMaintenance_def
                         ge_mask_eq
                  simp flip: word_unat.Rep_inject split: if_splits)
  done

(* Because of a case distinction, this proof occurs multiple times in handleInterrupt_ccorres below.
   The proof matches up the C expression "!config_set(CONFIG_ARM_GIC_V3_SUPPORT)"
   with config_ARM_GIC_V3 from the spec side. *)
method maybe_maskInterrupt_before_ack =
    simp only: maskIrqSignal_def when_def,
    csymbr, (* unwrap config_set(..) *)
    rule ccorres_cond_seq,
    rule ccorres_cond_both[where P="\<lambda>_. \<not>config_ARM_GIC_V3" and R=\<top>],
       simp add: Kernel_Config.config_ARM_GIC_V3_def, (* match up !config_set(..) condition *)
      rule ccorres_gen_asm[where P="\<not>config_ARM_GIC_V3"],
      simp,
      ctac (no_vcg) add: maskInterrupt_ccorres,
       ctac add: ackInterrupt_ccorres,
      wp,
     rule ccorres_gen_asm[where P="config_ARM_GIC_V3"],
     simp,
     ctac add: ackInterrupt_ccorres

lemma handleInterrupt_ccorres:
  "ccorres dc xfdc
     (invs' and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> sch_act_not (ksCurThread s) s))
     \<lbrace>\<acute>irq = ucast irq\<rbrace>
     hs
     (handleInterrupt irq)
     (Call handleInterrupt_'proc)"
  apply (cinit lift: irq_' cong: call_ignore_cong)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add:  Kernel_C_maxIRQ del: Collect_const)
    apply (rule ccorres_rhs_assoc)+
    apply (subst doMachineOp_bind)
      apply (rule maskInterrupt_empty_fail)
     apply (rule ackInterrupt_empty_fail)
    apply (ctac add: maskInterrupt_ccorres)
      apply (subst bind_return_unit[where f="doMachineOp (ackInterrupt irq)"])
      apply (ctac add: ackInterrupt_ccorres)
        apply (rule ccorres_split_throws)
         apply (rule ccorres_return_void_C)
        apply vcg
       apply wp
      apply (vcg exspec=ackInterrupt_modifies)
     apply wp
    apply (vcg exspec=maskInterrupt_modifies)
   apply (simp add: Kernel_C_maxIRQ del: Collect_const)
   apply (rule ccorres_pre_getIRQState)
    apply wpc
      apply simp
      apply (rule ccorres_fail)
     apply (simp add: bind_assoc cong: call_ignore_cong)
     apply (rule ccorres_move_const_guards)+
     apply (rule ccorres_cond_true_seq)
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply (rule getIRQSlot_ccorres3)
     apply (rule ccorres_getSlotCap_cte_at)
     apply (rule_tac P="cte_at' rv" in ccorres_cross_over_guard)
     apply (rule ccorres_Guard_Seq)
     apply (rule ccorres_Guard_intStateIRQNode_array_Ptr)
     apply (rule ccorres_move_array_assertion_irq ccorres_move_c_guard_cte)+
     apply ctac
       apply csymbr
       apply csymbr
       apply (rule ccorres_ntfn_cases)
        apply (clarsimp cong: call_ignore_cong simp del: Collect_const)
        apply (rule_tac b=send in ccorres_case_bools)
         apply simp
         apply (rule ccorres_cond_true_seq)
         apply (rule ccorres_rhs_assoc)+
         apply csymbr
         apply csymbr
         apply (rule ccorres_cond_true_seq)
         apply (rule ccorres_rhs_assoc)+
         apply csymbr
         apply csymbr
         apply (ctac (no_vcg) add: sendSignal_ccorres)
          apply (simp add: maskIrqSignal_def)
          apply (ctac (no_vcg) add: maskInterrupt_ccorres)
           apply (ctac add: ackInterrupt_ccorres)
          apply wp+
        apply (simp del: Collect_const)
        apply (rule ccorres_cond_true_seq)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr+
        apply (rule ccorres_cond_false_seq)
        apply (simp add: maskIrqSignal_def)
        apply (ctac (no_vcg) add: maskInterrupt_ccorres)
         apply (ctac add: ackInterrupt_ccorres)
        apply wp
       apply (rule_tac P=\<top> and P'="{s. ret__int_' s = 0 \<and> cap_get_tag cap \<noteq> scast cap_notification_cap}" in ccorres_inst)
       apply (clarsimp simp: isCap_simps simp del: Collect_const)
       apply (case_tac rva, simp_all del: Collect_const)[1]
                  prefer 3
                  apply metis
                 apply ((simp add: maskIrqSignal_def,
                        rule ccorres_guard_imp2,
                        rule ccorres_cond_false_seq, simp,
                        rule ccorres_cond_false_seq, simp,
                        ctac (no_vcg) add: maskInterrupt_ccorres,
                        ctac (no_vcg) add: ackInterrupt_ccorres,
                        wp, simp)+)
      apply (wpsimp wp: getSlotCap_wp)
     apply simp
     apply vcg
    apply (simp add: bind_assoc)
    apply (rule ccorres_move_const_guards)+
    apply (rule ccorres_cond_false_seq)
    apply (rule ccorres_cond_true_seq)
    apply (rule ccorres_rhs_assoc)+
    apply (ctac (no_vcg) add: timerTick_ccorres)
     apply (ctac (no_vcg) add: resetTimer_ccorres)
      apply (ctac add: ackInterrupt_ccorres )
     apply wp+
   apply (simp del: Collect_const)
   apply (rule ccorres_move_const_guards)+
   apply (rule ccorres_cond_false_seq)
   apply (rule ccorres_cond_false_seq)
   apply (rule ccorres_cond_true_seq)
   apply (ctac add: ccorres_handleReservedIRQ)
     apply (ctac (no_vcg) add: ackInterrupt_ccorres)
    apply wp
   apply (vcg exspec=handleReservedIRQ_modifies)
  apply (clarsimp simp: Kernel_C_maxIRQ not_less ucast_irq_array_guard)
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_ctes_of non_kernel_IRQs_def)
  apply (clarsimp)
  apply (clarsimp simp: Kernel_C.IRQTimer_def Kernel_C.IRQSignal_def
                        cte_wp_at_ctes_of ucast_ucast_b is_up)
  apply (intro conjI impI)
       apply clarsimp
       apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
       apply (clarsimp simp: typ_heap_simps')
       apply (simp add: cap_get_tag_isCap)
       apply (clarsimp simp: isCap_simps)
       apply (frule cap_get_tag_isCap_unfolded_H_cap)
       apply (frule cap_get_tag_to_H, assumption)
       apply (clarsimp simp: to_bool_def)
      apply (unat_arith, simp) (* nat irq bound based on irq_len *)
     apply (simp add: word_neq_0_conv word_less_nat_alt)
    apply (unat_arith, simp) (* word irq bound based on irq_len *)
   apply (clarsimp simp: IRQReserved_def)+
  done
end

end
