(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Fastpath_C
imports
  SyscallArgs_C
  Delete_C
  Syscall_C
  "Refine.RAB_FN"
  "CLib.MonadicRewrite_C"
begin

context begin interpretation Arch . (*FIXME: arch_split*)

definition
 "fastpaths sysc \<equiv> case sysc of
  SysCall \<Rightarrow> doE
    curThread \<leftarrow> liftE $ getCurThread;
    mi \<leftarrow> liftE $ getMessageInfo curThread;
    cptr \<leftarrow> liftE $ asUser curThread $ getRegister capRegister;

    fault \<leftarrow> liftE $ threadGet tcbFault curThread;
    pickFastpath \<leftarrow> liftE $ alternative (return True) (return False);
    unlessE (fault = None \<and> msgExtraCaps mi = 0
                \<and> msgLength mi \<le> scast n_msgRegisters \<and> pickFastpath)
       $ throwError ();

    ctab \<leftarrow> liftE $ getThreadCSpaceRoot curThread >>= getCTE;
    epCap \<leftarrow> unifyFailure (doE t \<leftarrow> resolveAddressBits (cteCap ctab) cptr (size cptr);
         liftE (getSlotCap (fst t)) odE);
    unlessE (isEndpointCap epCap \<and> capEPCanSend epCap)
       $ throwError ();
    ep \<leftarrow> liftE $ getEndpoint (capEPPtr epCap);
    unlessE (isRecvEP ep) $ throwError ();
    dest \<leftarrow> returnOk $ hd $ epQueue ep;
    newVTable \<leftarrow> liftE $ getThreadVSpaceRoot dest >>= getCTE;
    unlessE (isValidVTableRoot $ cteCap newVTable) $ throwError ();
    pd \<leftarrow> returnOk $ capPDBasePtr $ capCap $ cteCap newVTable;
    curDom \<leftarrow> liftE $ curDomain;
    curPrio \<leftarrow> liftE $ threadGet tcbPriority curThread;
    destPrio \<leftarrow> liftE $ threadGet tcbPriority dest;
    highest \<leftarrow> liftE $ isHighestPrio curDom destPrio;
    unlessE (destPrio \<ge> curPrio \<or> highest) $ throwError ();
    unlessE (capEPCanGrant epCap \<or> capEPCanGrantReply epCap) $ throwError ();
    asidMap \<leftarrow> liftE $ gets $ armKSASIDMap o ksArchState;
    unlessE (\<exists>v. {hwasid. (hwasid, pd) \<in> ran asidMap} = {v})
        $ throwError ();
    destDom \<leftarrow> liftE $ threadGet tcbDomain dest;
    unlessE (destDom = curDom) $ throwError ();

    liftE $ do
      setEndpoint (capEPPtr epCap)
           (case tl (epQueue ep) of [] \<Rightarrow> IdleEP | _ \<Rightarrow> RecvEP (tl (epQueue ep)));
      threadSet (tcbState_update (\<lambda>_. BlockedOnReply)) curThread;
      replySlot \<leftarrow> getThreadReplySlot curThread;
      callerSlot \<leftarrow> getThreadCallerSlot dest;
      replySlotCTE \<leftarrow> getCTE replySlot;
      assert (mdbNext (cteMDBNode replySlotCTE) = 0
                   \<and> isReplyCap (cteCap replySlotCTE)
                   \<and> capReplyMaster (cteCap replySlotCTE)
                   \<and> mdbFirstBadged (cteMDBNode replySlotCTE)
                   \<and> mdbRevocable (cteMDBNode replySlotCTE));
      destState \<leftarrow> getThreadState dest;
      cteInsert (ReplyCap curThread False (blockingIPCCanGrant destState)) replySlot callerSlot;

      forM_x (take (unat (msgLength mi)) ARM_H.msgRegisters)
             (\<lambda>r. do v \<leftarrow> asUser curThread (getRegister r);
                    asUser dest (setRegister r v) od);
      setThreadState Running dest;
      Arch.switchToThread dest;
      setCurThread dest;

      asUser dest $ zipWithM_x setRegister
               [ARM_H.badgeRegister, ARM_H.msgInfoRegister]
               [capEPBadge epCap, wordFromMessageInfo (mi\<lparr> msgCapsUnwrapped := 0 \<rparr>)];

      stateAssert kernelExitAssertions []
    od

  odE <catch> (\<lambda>_. callKernel (SyscallEvent sysc))
  | SysReplyRecv \<Rightarrow> doE
    curThread \<leftarrow> liftE $ getCurThread;
    mi \<leftarrow> liftE $ getMessageInfo curThread;
    cptr \<leftarrow> liftE $ asUser curThread $ getRegister capRegister;

    fault \<leftarrow> liftE $ threadGet tcbFault curThread;
    pickFastpath \<leftarrow> liftE $ alternative (return True) (return False);
    unlessE (fault = None \<and> msgExtraCaps mi = 0
                \<and> msgLength mi \<le> scast n_msgRegisters \<and> pickFastpath)
       $ throwError ();

    ctab \<leftarrow> liftE $ getThreadCSpaceRoot curThread >>= getCTE;
    epCap \<leftarrow> unifyFailure (doE t \<leftarrow> resolveAddressBits (cteCap ctab) cptr (size cptr);
         liftE (getSlotCap (fst t)) odE);

    unlessE (isEndpointCap epCap \<and> capEPCanReceive epCap)
       $ throwError ();

    bound_ntfn \<leftarrow> liftE $ getBoundNotification curThread;
    active_ntfn \<leftarrow> liftE $ case bound_ntfn of None \<Rightarrow> return False
      | Some ntfnptr \<Rightarrow> liftM isActive $ getNotification ntfnptr;
    unlessE (\<not> active_ntfn) $ throwError ();

    ep \<leftarrow> liftE $ getEndpoint (capEPPtr epCap);
    unlessE (\<not> isSendEP ep) $ throwError ();

    callerSlot \<leftarrow> liftE $ getThreadCallerSlot curThread;
    callerCTE \<leftarrow> liftE $ getCTE callerSlot;
    callerCap \<leftarrow> returnOk $ cteCap callerCTE;
    unlessE (isReplyCap callerCap \<and> \<not> capReplyMaster callerCap)
       $ throwError ();

    caller \<leftarrow> returnOk $ capTCBPtr callerCap;
    callerFault \<leftarrow> liftE $ threadGet tcbFault caller;
    unlessE (callerFault = None) $ throwError ();
    newVTable \<leftarrow> liftE $ getThreadVSpaceRoot caller >>= getCTE;
    unlessE (isValidVTableRoot $ cteCap newVTable) $ throwError ();

    curDom \<leftarrow> liftE $ curDomain;
    callerPrio \<leftarrow> liftE $ threadGet tcbPriority caller;
    highest \<leftarrow> liftE $ isHighestPrio curDom callerPrio;
    unlessE highest $ throwError ();

    pd \<leftarrow> returnOk $ capPDBasePtr $ capCap $ cteCap newVTable;
    asidMap \<leftarrow> liftE $ gets $ armKSASIDMap o ksArchState;
    unlessE (\<exists>v. {hwasid. (hwasid, pd) \<in> ran asidMap} = {v})
        $ throwError ();
    callerDom \<leftarrow> liftE $ threadGet tcbDomain caller;
    unlessE (callerDom = curDom) $ throwError ();

    liftE $ do
      epCanGrant \<leftarrow> return $ capEPCanGrant epCap;
      threadSet (tcbState_update (\<lambda>_. BlockedOnReceive (capEPPtr epCap) epCanGrant)) curThread;
      setEndpoint (capEPPtr epCap)
           (case ep of IdleEP \<Rightarrow> RecvEP [curThread] | RecvEP ts \<Rightarrow> RecvEP (ts @ [curThread]));
      mdbPrev \<leftarrow> liftM (mdbPrev o cteMDBNode) $ getCTE callerSlot;
      assert (mdbPrev \<noteq> 0);
      updateMDB mdbPrev (mdbNext_update (K 0) o mdbFirstBadged_update (K True)
                                              o mdbRevocable_update (K True));
      setCTE callerSlot makeObject;

      forM_x (take (unat (msgLength mi)) ARM_H.msgRegisters)
             (\<lambda>r. do v \<leftarrow> asUser curThread (getRegister r);
                    asUser caller (setRegister r v) od);
      setThreadState Running caller;
      Arch.switchToThread caller;
      setCurThread caller;

      asUser caller $ zipWithM_x setRegister
               [ARM_H.badgeRegister, ARM_H.msgInfoRegister]
               [0, wordFromMessageInfo (mi\<lparr> msgCapsUnwrapped := 0 \<rparr>)];

      stateAssert kernelExitAssertions []
    od

  odE <catch> (\<lambda>_. callKernel (SyscallEvent sysc))

  | _ \<Rightarrow> callKernel (SyscallEvent sysc)"


lemma setCTE_obj_at'_queued:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbQueued tcb)) t\<rbrace> setCTE p v \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P (tcbQueued tcb)) t\<rbrace>"
  unfolding setCTE_def
  by (rule setObject_cte_obj_at_tcb', simp+)

crunch obj_at'_queued: cteInsert "obj_at' (\<lambda>tcb. P (tcbQueued tcb)) t"
  (wp: setCTE_obj_at'_queued crunch_wps)

crunch obj_at'_not_queued: emptySlot "obj_at' (\<lambda>a. \<not> tcbQueued a) p"
  (wp: setCTE_obj_at'_queued)

lemma getEndpoint_obj_at':
  "\<lbrace>obj_at' P ptr\<rbrace> getEndpoint ptr \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (wp getEndpoint_wp)
  apply (clarsimp simp: obj_at'_def projectKOs)
  done

lemmas setEndpoint_obj_at_tcb' = setEndpoint_obj_at'_tcb

lemma tcbSchedEnqueue_tcbContext[wp]:
  "\<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>
     tcbSchedEnqueue t'
   \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>"
  apply (rule tcbSchedEnqueue_obj_at_unchangedT[OF all_tcbI])
  apply simp
  done

lemma setCTE_tcbContext:
  "\<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>
  setCTE slot cte
  \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>"
  apply (simp add: setCTE_def)
  apply (rule setObject_cte_obj_at_tcb', simp_all)
  done

lemma seThreadState_tcbContext:
 "\<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>
    setThreadState a b
  \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>"
  apply (rule setThreadState_obj_at_unchanged)
  apply (clarsimp simp: atcbContext_def)+
  done

lemma setBoundNotification_tcbContext:
 "\<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>
    setBoundNotification a b
  \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>"
  apply (rule setBoundNotification_obj_at_unchanged)
  apply (clarsimp simp: atcbContext_def)+
  done

declare comp_apply [simp del]
crunch tcbContext[wp]: deleteCallerCap "obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t"
  (wp: setEndpoint_obj_at_tcb' setBoundNotification_tcbContext
       setNotification_tcb crunch_wps seThreadState_tcbContext
   simp: crunch_simps unless_def)
declare comp_apply [simp]


crunch ksArch[wp]: asUser "\<lambda>s. P (ksArchState s)"
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

end

context kernel_m begin

lemma getCTE_h_val_ccorres_split:
  assumes var: "\<And>s f s'. var (var_update f s) = f (var s)
                  \<and> ((s', var_update f s) \<in> rf_sr) = ((s', s) \<in> rf_sr)"
     and "\<And>rv' t t'. ceqv \<Gamma> var rv' t t' g (g' rv')"
     and "\<And>rv rv'. \<lbrakk> ccap_relation (cteCap rv) rv'; P rv \<rbrakk>
                \<Longrightarrow> ccorres r xf (Q rv) (Q' rv rv') hs (f rv) (g' rv')"
  shows
  "ccorres r xf (\<lambda>s. \<forall>cte. ctes_of s slot = Some cte \<longrightarrow> P cte \<and> Q cte s)
                {s. (\<forall>cte cap. ccap_relation (cteCap cte) cap \<and> P cte
                          \<longrightarrow> var_update (\<lambda>_. cap) s \<in> Q' cte cap)
                           \<and> slot' = cte_Ptr slot} hs
       (getCTE slot >>= (\<lambda>rv. f rv))
   ((Basic (\<lambda>s. var_update (\<lambda>_. h_val (hrs_mem (t_hrs_' (globals s))) (cap_Ptr &(slot' \<rightarrow>[''cap_C'']))) s));; g)"
    (is "ccorres r xf ?G ?G' hs ?f ?g")
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_pre_getCTE)
   apply (rule_tac A="cte_wp_at' ((=) rv and P) slot and Q rv" and A'="?G'" in ccorres_guard_imp2)
    apply (rule_tac P="P rv" in ccorres_gen_asm)
    apply (rule ccorres_symb_exec_r)
      apply (rule_tac xf'=var in ccorres_abstract)
       apply (rule assms)
      apply (rule ccorres_gen_asm2, erule(1) assms)
     apply vcg
    apply (rule conseqPre, vcg, clarsimp simp: var)
   apply (clarsimp simp: cte_wp_at_ctes_of var)
   apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
   apply (clarsimp simp: typ_heap_simps' dest!: ccte_relation_ccap_relation)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma cap_'_cap_'_update_var_props:
  "cap_' (cap_'_update f s) = f (cap_' s) \<and>
         ((s', cap_'_update f s) \<in> rf_sr) = ((s', s) \<in> rf_sr)"
  by simp

lemmas getCTE_cap_h_val_ccorres_split
    = getCTE_h_val_ccorres_split[where var_update=cap_'_update and P=\<top>,
                                 OF cap_'_cap_'_update_var_props]

lemma getCTE_ccorres_helper:
  "\<lbrakk> \<And>\<sigma> cte cte'. \<Gamma> \<turnstile> {s. (\<sigma>, s) \<in> rf_sr \<and> P \<sigma> \<and> s \<in> P' \<and> ctes_of \<sigma> slot = Some cte
                               \<and> cslift s (cte_Ptr slot) = Some cte'
                               \<and> ccte_relation cte cte'}
                       f {s. (\<sigma>, s) \<in> rf_sr \<and> r cte (xf s)} \<rbrakk> \<Longrightarrow>
     ccorres r xf P P' hs (getCTE slot) f"
  apply atomize
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_add_return2)
   apply (rule ccorres_pre_getCTE)
   apply (rule_tac P="cte_wp_at' ((=) x) slot and P"
                in ccorres_from_vcg[where P'=P'])
   apply (erule allEI)
   apply (drule_tac x="the (ctes_of \<sigma> slot)" in spec)
   apply (erule HoarePartial.conseq)
   apply (clarsimp simp: return_def cte_wp_at_ctes_of)
   apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
   apply simp
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

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

lemma ccorres_abstract_all:
  "\<lbrakk>\<And>rv' t t'. ceqv Gamm xf' rv' t t' d (d' rv');
    \<And>rv'. ccorres_underlying sr Gamm r xf arrel axf (G rv') (G' rv') hs a (d' rv')\<rbrakk>
       \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf (\<lambda>s. \<forall>rv'. G rv' s) {s. s \<in> G' (xf' s)} hs a d"
  apply (erule ccorres_abstract)
  apply (rule ccorres_guard_imp2)
   apply assumption
  apply simp
  done

declare of_int_sint_scast[simp]

lemma isCNodeCap_capUntypedPtr_capCNodePtr:
  "isCNodeCap c \<Longrightarrow> capUntypedPtr c = capCNodePtr c"
  by (clarsimp simp: isCap_simps)

lemma of_bl_from_bool:
  "of_bl [x] = from_bool x"
  by (cases x, simp_all)

lemma lookup_fp_ccorres':
  assumes bits: "bits = size cptr"
  shows
  "ccorres (\<lambda>mcp ccp. ccap_relation (case mcp of Inl v => NullCap | Inr v => v) ccp)
                ret__struct_cap_C_'
           (valid_cap' cap and valid_objs')
           (UNIV \<inter> {s. ccap_relation cap (cap_' s)} \<inter> {s. cptr_' s = cptr}) []
       (cutMon ((=) s) (doE t \<leftarrow> resolveAddressBits cap cptr bits;
                             liftE (getSlotCap (fst t))
                         odE))
       (Call lookup_fp_'proc)"
  apply (cinit' lift: cptr_')
   apply (rule ccorres_rhs_assoc2)
   apply (rule ccorres_symb_exec_r)
     apply (rule_tac xf'=ret__int_' in ccorres_abstract, ceqv)
     apply (rule_tac P="rv' = from_bool (isCNodeCap cap)" in ccorres_gen_asm2)
     apply (simp add: from_bool_0 del: Collect_const cong: call_ignore_cong)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: resolveAddressBits.simps split_def del: Collect_const
                      split del: if_split)
      apply (rule ccorres_drop_cutMon)
      apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
       apply vcg
      apply (rule conseqPre, vcg)
      apply (clarsimp simp: throwError_def return_def isRight_def isLeft_def
                            ccap_relation_NullCap_iff)
     apply (clarsimp simp del: Collect_const cong: call_ignore_cong)
     apply (rule_tac P="valid_cap' cap and valid_objs'"
                and P'="UNIV \<inter> {s. ccap_relation cap (cap_' s) \<and> isCNodeCap cap}
                             \<inter> {s. bits_' s = 32 - of_nat bits \<and> bits \<le> 32 \<and> bits \<noteq> 0}"
                   in ccorres_inst)
     apply (thin_tac "isCNodeCap cap")
     defer
     apply vcg
    apply (rule conseqPre, vcg)
    apply clarsimp
   apply (clarsimp simp: word_size cap_get_tag_isCap bits
                         of_bl_from_bool from_bool_0)
  proof (induct cap cptr bits arbitrary: s
            rule: resolveAddressBits.induct)
  case (1 acap acptr abits as)

    have sub_mask_neq_0_eq:
      "\<And>v :: word32. v && 0x1F \<noteq> 0 \<Longrightarrow> 0x20 - (0x20 - (v && 0x1F) && mask 5) = v && 0x1F"
      apply (subst word_le_mask_eq)
        apply (simp only: mask_def)
        apply (rule word_le_minus_mono, simp_all add: word_le_sub1 word_sub_le_iff)[1]
        apply (rule order_trans, rule word_and_le1, simp)
       apply (simp add: word_bits_def)
      done

    have valid_cnode_bits_0:
      "\<And>s acap. \<lbrakk> isCNodeCap acap; s \<turnstile>' acap \<rbrakk> \<Longrightarrow> capCNodeBits acap \<noteq> 0"
      by (clarsimp simp: isCap_simps valid_cap'_def)

    have cap_get_tag_update_1:
      "\<And>f cap. cap_get_tag (cap_C.words_C_update (\<lambda>w. Arrays.update w (Suc 0) (f w)) cap) = cap_get_tag cap"
      by (simp add: cap_get_tag_def cong: if_cong)

    show ?case
    supply if_cong[cong] option.case_cong[cong]
    apply (cinitlift cap_' bits_')
    apply (rename_tac cbits ccap)
    apply (elim conjE)
    apply (rule_tac F="capCNodePtr_CL (cap_cnode_cap_lift ccap)
                             = capCNodePtr acap
                        \<and> capCNodeGuardSize acap < 32
                        \<and> capCNodeBits acap < 32
                        \<and> capCNodeGuard_CL (cap_cnode_cap_lift ccap)
                             = capCNodeGuard acap
                        \<and> unat (capCNodeGuardSize_CL (cap_cnode_cap_lift ccap))
                             = capCNodeGuardSize acap
                        \<and> unat (capCNodeRadix_CL (cap_cnode_cap_lift ccap))
                             = capCNodeBits acap
                        \<and> unat (0x20 - capCNodeRadix_CL (cap_cnode_cap_lift ccap))
                             = 32 - capCNodeBits acap
                        \<and> unat ((0x20 :: word32) - of_nat abits) = 32 - abits
                        \<and> unat (capCNodeGuardSize_CL (cap_cnode_cap_lift ccap)
                                 + capCNodeRadix_CL (cap_cnode_cap_lift ccap))
                             = capCNodeGuardSize acap + capCNodeBits acap"
                   in Corres_UL_C.ccorres_req)
     apply (clarsimp simp: cap_get_tag_isCap[symmetric])
     apply (clarsimp simp: cap_lift_cnode_cap cap_to_H_simps valid_cap'_def
                           capAligned_def cap_cnode_cap_lift_def objBits_simps
                           word_mod_2p_is_mask[where n=5, simplified]
                    elim!: ccap_relationE)
     apply (simp add: unat_sub[unfolded word_le_nat_alt]
                      unat_of_nat32 word_bits_def)
     apply (subst unat_plus_simple[symmetric], subst no_olen_add_nat)
     apply (rule order_le_less_trans, rule add_le_mono)
       apply (rule word_le_nat_alt[THEN iffD1], rule word_and_le1)+
     apply (simp add: mask_def)
    apply (rule ccorres_guard_imp2)
     apply csymbr+
     apply (rule ccorres_Guard_Seq, csymbr)
     apply (simp add: resolveAddressBits.simps bindE_assoc extra_sle_sless_unfolds
                      Collect_True
                 split del: if_split del: Collect_const cong: call_ignore_cong)
     apply (simp add: cutMon_walk_bindE del: Collect_const
                         split del: if_split cong: call_ignore_cong)
     apply (rule ccorres_drop_cutMon_bindE, rule ccorres_assertE)
     apply (rule ccorres_cutMon)
     apply csymbr
     apply (simp add: locateSlot_conv liftE_bindE cutMon_walk_bind)
     apply (rule ccorres_drop_cutMon_bind, rule ccorres_stateAssert)

     apply (rule_tac P="abits < capCNodeBits acap + capCNodeGuardSize acap"
                 in ccorres_case_bools2)
      apply (rule ccorres_drop_cutMon)
      apply csymbr+
      apply (rule ccorres_symb_exec_r)
        apply (rule_tac xf'=ret__int_' in ccorres_abstract_all, ceqv)
        apply (rule ccorres_Cond_rhs_Seq)
         apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
          apply vcg
         apply (rule conseqPre, vcg)
         apply (clarsimp simp: unlessE_def split: if_split)
         apply (simp add: throwError_def return_def cap_tag_defs
                          isRight_def isLeft_def
                          ccap_relation_NullCap_iff
                          in_bindE)
         apply auto[1]
        apply (simp del: Collect_const cong: call_ignore_cong)
        apply (rule ccorres_Guard_Seq)+
        apply csymbr+
        apply (simp del: Collect_const cong: call_ignore_cong)
        apply (rule ccorres_move_array_assertion_cnode_ctes ccorres_move_c_guard_cte
          | csymbr)+
        apply (rule ccorres_symb_exec_r)
          apply ccorres_remove_UNIV_guard
          apply csymbr+
          apply (rule ccorres_cond_false_seq)
          apply (simp add: ccorres_expand_while_iff_Seq[symmetric]
                           whileAnno_def cong: call_ignore_cong)
          apply (rule ccorres_cond_false)
          apply (rule ccorres_cond_true_seq)
          apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
           apply vcg
          apply (rule conseqPre, vcg)
          apply (clarsimp simp: unlessE_def split: if_split cong: call_ignore_cong)
          apply (simp add: throwError_def return_def cap_tag_defs isRight_def
                           isLeft_def ccap_relation_NullCap_iff)
          apply fastforce
         apply (simp del: Collect_const)
         apply vcg
        apply (rule conseqPre, vcg, clarsimp)
       apply (simp del: Collect_const)
       apply vcg
      apply (rule conseqPre, vcg, clarsimp)

     apply (rule ccorres_cutMon)
     apply (simp add: cutMon_walk_bindE unlessE_whenE
                 del: Collect_const
                 split del: if_split cong: call_ignore_cong)
     apply (rule ccorres_drop_cutMon_bindE)
     apply csymbr+
     apply (rule ccorres_rhs_assoc2)
     apply (rule_tac r'=dc and xf'=xfdc in ccorres_splitE[OF _ ceqv_refl])
        apply (rule ccorres_Cond_rhs_Seq)
         apply (rule ccorres_Guard_Seq)+
         apply csymbr
         apply (simp add: unat_sub word_le_nat_alt if_1_0_0 shiftl_shiftr3 word_size
                     del: Collect_const)
         apply (rule ccorres_Cond_rhs)
          apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: whenE_def throwError_def return_def
                                ccap_relation_NullCap_iff isRight_def isLeft_def)
         apply (simp add: whenE_def)
         apply (rule ccorres_returnOk_skip)
        apply simp
        apply (rule ccorres_cond_false)
        apply (rule_tac P="valid_cap' acap" in ccorres_from_vcg[where P'=UNIV])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: valid_cap'_def isCap_simps if_1_0_0)
        apply (simp add: unat_eq_0[symmetric] whenE_def returnOk_def return_def)
      apply (rule ccorres_cutMon)
       apply (simp add: liftE_bindE locateSlot_conv
                   del: Collect_const cong: call_ignore_cong)
       apply (rule_tac P="abits = capCNodeBits acap + capCNodeGuardSize acap"
                   in ccorres_case_bools2)
        apply (rule ccorres_drop_cutMon)
        apply (simp del: Collect_const)
        apply (simp add: liftE_def getSlotCap_def del: Collect_const)
        apply (rule ccorres_Guard_Seq)+
        apply csymbr+
        apply (simp)
        apply (rule ccorres_move_array_assertion_cnode_ctes
                    ccorres_move_c_guard_cte
                    ccorres_rhs_assoc | csymbr)+
        apply (rule getCTE_cap_h_val_ccorres_split)
         apply ceqv
        apply (rename_tac "getCTE_cap")
        apply (csymbr | rule ccorres_Guard_Seq)+
        apply (rule ccorres_cond_false_seq)
        apply (simp add: ccorres_expand_while_iff_Seq[symmetric]
                         whileAnno_def del: Collect_const)
        apply (rule ccorres_cond_false)
        apply (rule ccorres_cond_false_seq)
        apply (simp del: Collect_const)
        apply (rule_tac P'="{s. cap_' s = getCTE_cap}"
                       in ccorres_from_vcg_throws[where P=\<top>])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: word_sle_def return_def returnOk_def
                              isRight_def)
       apply (simp add: bind_bindE_assoc
                   del: Collect_const cong: call_ignore_cong if_cong)
       apply (simp add: liftE_bindE "1.prems" unlessE_def
                        cutMon_walk_bind cnode_cap_case_if
                   del: Collect_const cong: if_cong call_ignore_cong)
       apply (rule ccorres_Guard_Seq)+
       apply csymbr+
       apply (simp del: Collect_const cong: call_ignore_cong)
       apply (rule ccorres_drop_cutMon_bind)
       apply (rule ccorres_getSlotCap_cte_at)
       apply (rule ccorres_move_c_guard_cte
                   ccorres_move_array_assertion_cnode_ctes
                 | csymbr)+
       apply ctac
         apply (csymbr | rule ccorres_Guard_Seq)+
         apply (rule ccorres_cond_true_seq)
         apply (rule ccorres_rhs_assoc | csymbr)+
         apply (simp add: ccorres_expand_while_iff_Seq[symmetric]
                          whileAnno_def if_to_top_of_bindE bindE_assoc
                          split_def
                    cong: if_cong call_ignore_cong)
         apply (rule ccorres_cutMon)
         apply (simp add: cutMon_walk_if cong: call_ignore_cong)
         apply (rule_tac Q'="\<lambda>s. ret__int_' s = from_bool (isCNodeCap rv)"
                       in ccorres_cond_both'[where Q=\<top>])
           apply (clarsimp simp: from_bool_0)
          apply (rule ccorres_rhs_assoc)+
          apply (rule_tac P="ccorres r xf Gd Gd' hs a" for r xf Gd Gd' hs a in rsubst)
           apply (rule "1.hyps",
                  (rule refl in_returns in_bind[THEN iffD2, OF exI, OF exI, OF conjI]
                       acc_CNodeCap_repr
                        | assumption
                        | clarsimp simp: unlessE_whenE locateSlot_conv
                                         "1.prems"
                        | clarsimp simp: whenE_def[where P=False])+)[1]
          apply (simp add: whileAnno_def extra_sle_sless_unfolds)
         apply (rule ccorres_drop_cutMon)
         apply (simp add: liftE_def getSlotCap_def)
         apply (rule ccorres_pre_getCTE)
         apply (rule ccorres_cond_false_seq)
         apply (rule_tac P="\<lambda>s. cteCap rva = rv" and P'="{s. cap_' s = cap}"
                      in ccorres_from_vcg_throws)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: return_def returnOk_def word_sle_def isRight_def)
        apply simp
        apply (wp getSlotCap_wp)
       apply (simp add: if_1_0_0)
       apply vcg
      apply (wp whenE_throwError_wp)
     apply (simp add: ccHoarePost_def del: Collect_const)
     apply vcg
    apply (clarsimp simp: Collect_const_mem if_1_0_0 of_bl_from_bool
               split del: if_split cong: if_cong)
    apply (clarsimp simp: cap_get_tag_isCap
                          option.split[where P="\<lambda>x. x"]
                          isCNodeCap_capUntypedPtr_capCNodePtr
                          )
    apply (clarsimp simp: word_less_nat_alt word_le_nat_alt linorder_not_less
                    cong: conj_cong)
    apply (clarsimp simp: word_less_nat_alt word_le_nat_alt linorder_not_less
                    cong: rev_conj_cong)
    apply (subgoal_tac "\<not> isZombie acap \<and> \<not> isThreadCap acap")
     prefer 2
     apply (clarsimp simp: isCap_simps)
    apply (simp add: imp_conjL)
    apply (simp only: all_simps[symmetric] imp_conjL cong: imp_cong,
           simp only: all_simps, simp)
    apply (simp add: unat_shiftr_le_bound)
    apply (frule(1) valid_cnode_bits_0, clarsimp)
    apply (intro conjI impI)
                     apply (simp add: size_of_def)
                     apply (erule (1) valid_cnode_cap_cte_at'')
                      apply simp
                     apply (rule shiftr_less_t2n')
                      apply simp
                     apply simp
                    apply (simp add:size_of_def)
                    apply (erule (1) valid_cnode_cap_cte_at'')
                     apply simp
                    apply (rule shiftr_less_t2n')
                     apply simp
                    apply simp
                   apply (clarsimp simp: cte_wp_at_ctes_of)
                   apply (clarsimp dest!: ctes_of_valid')
                  apply (simp add: cte_level_bits_def size_of_def field_simps)
                  apply (simp add: shiftl_shiftr3 word_size)
                  apply (simp add: word_bw_assocs mask_and_mask min.absorb2)
                 apply (simp_all add: unat_sub word_le_nat_alt unat_eq_0[symmetric])
               apply (simp_all add: unat_plus_if' if_P)
           apply (clarsimp simp: shiftr_over_and_dist
                                 size_of_def cte_level_bits_def field_simps shiftl_shiftl
                                 shiftl_shiftr3 word_size)+
         apply (clarsimp simp: unat_gt_0 from_bool_0 trans [OF eq_commute from_bool_eq_if])
         apply (intro conjI impI, simp_all)[1]
         apply (rule word_unat.Rep_inject[THEN iffD1], subst unat_plus_if')
         apply (simp add: unat_plus_if' unat_of_nat32 word_bits_def)
        apply (clarsimp simp: shiftr_over_and_dist
                              size_of_def cte_level_bits_def field_simps shiftl_shiftl
                              shiftl_shiftr3 word_size)+
      apply (clarsimp simp: unat_gt_0 from_bool_0 trans [OF eq_commute from_bool_eq_if])

      apply (intro conjI impI, simp_all)[1]
      apply (rule word_unat.Rep_inject[THEN iffD1], simp add: unat_of_nat32 word_bits_def)
    done
qed

lemmas lookup_fp_ccorres
    = lookup_fp_ccorres'[OF refl, THEN ccorres_use_cutMon]

lemma ccap_relation_case_sum_Null_endpoint:
  "ccap_relation (case x of Inl v => NullCap | Inr v => v) ccap
     \<Longrightarrow> (cap_get_tag ccap = scast cap_endpoint_cap)
           = (isRight x \<and> isEndpointCap (theRight x))"
  by (clarsimp simp: cap_get_tag_isCap isRight_def isCap_simps
              split: sum.split_asm)

lemma ccorres_catch_bindE_symb_exec_l:
  "\<lbrakk> \<And>s. \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>rv. (=) s\<rbrace>; empty_fail f;
      \<And>rv. ccorres_underlying sr G r xf ar axf (Q rv) (Q' rv) hs (catch (g rv) h >>= j) c;
      \<And>ex. ccorres_underlying sr G r xf ar axf (R ex) (R' ex) hs (h ex >>= j) c;
      \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> \<rbrakk>
    \<Longrightarrow>
  ccorres_underlying sr G r xf ar axf P {s. (\<forall>rv. s \<in> Q' rv) \<and> (\<forall>ex. s \<in> R' ex)} hs
          (catch (f >>=E g) h >>= j) c"
  apply (simp add: catch_def bindE_def bind_assoc lift_def)
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l[where G=P])
      apply wpc
       apply (simp add: throwError_bind)
       apply assumption+
    apply (clarsimp simp: valid_def validE_def split_def split: sum.split_asm)
   apply assumption
  apply clarsimp
  done

definition
  "pd_has_hwasid pd =
     (\<lambda>s. \<exists>v. asid_map_pd_to_hwasids (armKSASIDMap (ksArchState s)) pd = {v})"

lemma ccap_relation_pd_helper:
  "\<lbrakk> ccap_relation cap cap'; cap_get_tag cap' = scast cap_page_directory_cap \<rbrakk>
        \<Longrightarrow> capPDBasePtr_CL (cap_page_directory_cap_lift cap') = capPDBasePtr (capCap cap)"
  by (clarsimp simp: cap_lift_page_directory_cap cap_to_H_simps
                     cap_page_directory_cap_lift
              elim!: ccap_relationE)

lemma stored_hw_asid_get_ccorres_split':
  assumes  ptr: "ptr = CTypesDefs.ptr_add pd 0xFF0"
  assumes ceqv: "\<And>rv' t t'. ceqv Gamm stored_hw_asid___struct_pde_C_' rv' t t' c (c' rv')"
   and ccorres: "\<And>shw_asid. pde_get_tag shw_asid = scast pde_pde_invalid \<Longrightarrow>
                      ccorres_underlying rf_sr Gamm r xf ar axf
                                   (Q shw_asid) (R shw_asid) hs
                                   a (c' shw_asid)"
  shows "ccorres_underlying rf_sr Gamm r xf ar axf
                (\<lambda>s. page_directory_at' (ptr_val pd) s \<and> valid_pde_mappings' s
                      \<and> (\<forall>shw_asid. asid_map_pd_to_hwasids (armKSASIDMap (ksArchState s)) (ptr_val pd)
                               = set_option (pde_stored_asid shw_asid) \<and> pde_get_tag shw_asid = scast pde_pde_invalid
                             \<longrightarrow> P shw_asid \<and> Q shw_asid s))
                {s. \<forall>stored_hw_asid. P stored_hw_asid \<and> pde_get_tag stored_hw_asid = scast pde_pde_invalid
                            \<and> (cslift s \<circ>\<^sub>m pd_pointer_to_asid_slot) (ptr_val pd) = Some stored_hw_asid
                      \<longrightarrow> s \<lparr> stored_hw_asid___struct_pde_C_' := stored_hw_asid \<rparr>
                                 \<in> R stored_hw_asid} hs
                a (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t ptr\<rbrace>
                       (\<acute>stored_hw_asid___struct_pde_C :==
                               h_val (hrs_mem \<acute>t_hrs) ptr);; c)"
  unfolding ptr
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_Guard_Seq)
   apply (rule ccorres_symb_exec_r)
     apply (rule ccorres_abstract_all[OF ceqv])
     apply (rule_tac A="\<lambda>s. asid_map_pd_to_hwasids (armKSASIDMap (ksArchState s)) (ptr_val pd)
                               = set_option (pde_stored_asid rv') \<and> pde_get_tag rv' = scast pde_pde_invalid
                            \<longrightarrow> P rv' \<and> Q rv' s"
                and A'="{s. P rv' \<longrightarrow> s \<in> R rv'}
                         \<inter> {s. (cslift s \<circ>\<^sub>m pd_pointer_to_asid_slot) (ptr_val pd)
                                  = Some rv' \<and> pde_get_tag rv' = scast pde_pde_invalid}"
                in ccorres_guard_imp2)
      apply (rule_tac P="pde_get_tag rv' = scast pde_pde_invalid" in ccorres_gen_asm)
      apply (erule ccorres)
     apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                           carch_state_relation_def
                           map_comp_Some_iff)
    apply vcg
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply clarsimp
  apply (frule_tac x=pd_asid_slot in page_directory_pde_atI')
   apply (simp add: pd_asid_slot_def pageBits_def)
  apply (cases pd)
  apply (simp add: typ_at_to_obj_at_arches)
  apply (drule obj_at_ko_at')
  apply (clarsimp simp: pd_asid_slot_def)
  apply (erule cmap_relationE1[OF rf_sr_cpde_relation], erule ko_at_projectKO_opt)
  apply (frule(1) valid_pde_mappings_ko_atD')
  apply (clarsimp simp: typ_heap_simps' map_comp_Some_iff
                        valid_pde_mapping'_def)
  apply (clarsimp simp: pd_pointer_to_asid_slot_def page_directory_at'_def
                        add_mask_eq pdBits_def pageBits_def word_bits_def
                        valid_pde_mapping_offset'_def pd_asid_slot_def
                         pdeBits_def)
  apply (simp add: cpde_relation_def Let_def pde_lift_def
            split: if_split_asm)
  done

lemma ptr_add_0xFF0:
  "pde_Ptr (pd + 0x3FC0) = CTypesDefs.ptr_add (pde_Ptr pd) 0xFF0"
  by simp

lemmas stored_hw_asid_get_ccorres_split
    = stored_hw_asid_get_ccorres_split'[OF refl]
      stored_hw_asid_get_ccorres_split'[OF ptr_add_0xFF0]

lemma dmo_clearExMonitor_setCurThread_swap:
  "(do _ \<leftarrow> doMachineOp ARM.clearExMonitor;
               setCurThread thread
            od)
    = (do _ \<leftarrow> setCurThread thread;
            doMachineOp ARM.clearExMonitor od)"
  apply (simp add: setCurThread_def doMachineOp_def split_def)
  apply (rule oblivious_modify_swap[symmetric])
  apply (intro oblivious_bind,
         simp_all add: select_f_oblivious)
  done

lemma monadic_rewrite_gets_l:
  "(\<And>x. monadic_rewrite F E (P x) (g x) m)
    \<Longrightarrow> monadic_rewrite F E (\<lambda>s. P (f s) s) (gets f >>= (\<lambda>x. g x)) m"
  by (auto simp add: monadic_rewrite_def exec_gets)

lemma pd_at_asid_inj':
  "pd_at_asid' pd asid s \<Longrightarrow> pd_at_asid' pd' asid s \<Longrightarrow> pd' = pd"
  by (clarsimp simp: pd_at_asid'_def obj_at'_def)

lemma armv_contextSwitch_HWASID_fp_rewrite:
  "monadic_rewrite True False
    (pd_has_hwasid pd and pd_at_asid' pd asid and
        (\<lambda>s. asid_map_pd_to_hwasids (armKSASIDMap (ksArchState s)) pd
                                     = set_option (pde_stored_asid v)))
    (armv_contextSwitch pd asid)
    (doMachineOp (armv_contextSwitch_HWASID pd (the (pde_stored_asid v))))"
  apply (simp add: getHWASID_def armv_contextSwitch_def
                        bind_assoc loadHWASID_def
                        findPDForASIDAssert_def
                        checkPDAt_def checkPDUniqueToASID_def
                        checkPDASIDMapMembership_def
                        stateAssert_def2[folded assert_def])
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_gets_l)
   apply (rule monadic_rewrite_symb_exec_l)
      apply (wpsimp)+
     apply (simp add: empty_fail_findPDForASID empty_fail_catch)
    apply (rule monadic_rewrite_assert monadic_rewrite_gets_l)+
    apply (rule_tac P="asidMap asid \<noteq> None \<and> fst (the (asidMap asid)) = the (pde_stored_asid v)"
        in monadic_rewrite_gen_asm)
    apply (simp only: case_option_If2 simp_thms if_True if_False
                      split_def, simp)
    apply (rule monadic_rewrite_refl)
   apply (wp findPDForASID_pd_at_wp | simp only: const_def)+
  apply (clarsimp simp: pd_has_hwasid_def cte_level_bits_def
                        field_simps cte_wp_at_ctes_of
                        word_0_sle_from_less
                        isCap_simps invs_valid_pspace'
              simp del: Collect_const rf_sr_upd_safe)
  apply (drule(1) pd_at_asid_inj')
  apply (clarsimp simp: singleton_eq_o2s singleton_eq_o2s[THEN trans[OF eq_commute]])
  apply (cases "pde_stored_asid v", simp_all)
  apply (clarsimp simp: asid_map_pd_to_hwasids_def set_eq_subset
                 elim!: ranE)
  apply (case_tac "x = asid")
   apply clarsimp
  apply (erule notE, rule_tac a=x in ranI)
  apply simp
  done

lemma switchToThread_fp_ccorres:
  "ccorres dc xfdc (pspace_aligned' and pspace_distinct' and valid_objs' and no_0_obj'
                          and valid_pde_mappings' and valid_arch_state'
                          and tcb_at' thread
                          and cte_wp_at' (\<lambda>cte. isValidVTableRoot (cteCap cte)
                                              \<and> capPDBasePtr (capCap (cteCap cte)) = pd)
                                         (thread + tcbVTableSlot * 0x10)
                          and pd_has_hwasid pd
                          and (\<lambda>s. asid_map_pd_to_hwasids (armKSASIDMap (ksArchState s)) pd
                                     = set_option (pde_stored_asid v)))
                   (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr thread}
                         \<inter> {s. cap_pd_' s = pde_Ptr pd}
                         \<inter> {s. stored_hw_asid___struct_pde_C_' s = v}) []
      (Arch.switchToThread thread
            >>= (\<lambda>_. setCurThread thread))
      (Call switchToThread_fp_'proc)"
  apply (cinit' lift: thread_' cap_pd_' stored_hw_asid___struct_pde_C_')
   apply (simp add: ARM_H.switchToThread_def bind_assoc
                    setVMRoot_def cap_case_isPageDirectoryCap
               del: Collect_const cong: call_ignore_cong)
   apply (simp add: getThreadVSpaceRoot_def locateSlot_conv getSlotCap_def
               del: Collect_const cong: call_ignore_cong)
   apply (simp only: )
   apply (rule ccorres_rhs_assoc2)
   apply (rule ccorres_symb_exec_r, rule_tac xf'="ret__unsigned_'" in ccorres_abstract,
          ceqv, rename_tac "hw_asid_ret")
     apply (rule ccorres_getCTE, rename_tac cte)
     apply (rule_tac P="isValidVTableRoot (cteCap cte)
                        \<and> capPDBasePtr (capCap (cteCap cte)) = pd" in ccorres_gen_asm)
     apply (erule conjE, drule isValidVTableRootD)
     apply (simp del: Collect_const cong: call_ignore_cong)
     apply (rule ccorres_catch_bindE_symb_exec_l,
            rule findPDForASID_inv,
            rule empty_fail_findPDForASID)
       apply (rename_tac "pd_found")
       apply (rule_tac P="pd_found \<noteq> pd"
                    in ccorres_case_bools2)
        apply (simp add: bindE_assoc catch_liftE_bindE bind_assoc
                         checkPDNotInASIDMap_def
                         checkPDASIDMapMembership_def
                         catch_throwError)
        apply (rule ccorres_stateAssert)
        apply (rule ccorres_False[where P'=UNIV])
       apply (simp add: catch_liftE bind_assoc
                   del: Collect_const cong: call_ignore_cong)
       apply (rule monadic_rewrite_ccorres_assemble[rotated])
        apply (rule monadic_rewrite_bind_head)
        apply (rule_tac pd=pd and v=v
                     in armv_contextSwitch_HWASID_fp_rewrite)
       apply (ctac(no_vcg) add: armv_contextSwitch_HWASID_ccorres)
        apply (simp add: storeWordUser_def bind_assoc case_option_If2
                         split_def
                    del: Collect_const)
        apply (simp only: dmo_clearExMonitor_setCurThread_swap
                             dc_def[symmetric])
        apply (rule ccorres_split_nothrow_novcg_dc)
           apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp del: rf_sr_upd_safe)
           apply (clarsimp simp: setCurThread_def simpler_modify_def
                                    rf_sr_def cstate_relation_def Let_def
                                    carch_state_relation_def cmachine_state_relation_def)
          apply (ctac add: clearExMonitor_fp_ccorres)
         apply wp
        apply (simp add: guard_is_UNIV_def)
       apply wp
      apply (simp add: bind_assoc checkPDNotInASIDMap_def
                       checkPDASIDMapMembership_def)
      apply (rule ccorres_stateAssert)
      apply (rule ccorres_False[where P'=UNIV])
     apply simp
     apply (wp findPDForASID_pd_at_wp)[1]
    apply (simp del: Collect_const)
    apply vcg
   apply (rule conseqPre, vcg, clarsimp)
  apply (clarsimp simp: pd_has_hwasid_def cte_level_bits_def
                        field_simps cte_wp_at_ctes_of
                        pd_at_asid'_def word_0_sle_from_less
                        isCap_simps invs_valid_pspace'
              simp del: Collect_const rf_sr_upd_safe)
  apply (frule_tac P="\<lambda>Sf. Sf x = S'" for x S'
            in subst[OF meta_eq_to_obj_eq, OF asid_map_pd_to_hwasids_def])
  apply (clarsimp simp: isCap_simps dest!: isValidVTableRootD)
  apply (rule context_conjI)
   apply (drule singleton_eqD[OF sym])
   apply clarsimp
   apply (fastforce simp: ran_def)
  apply (frule ctes_of_valid', clarsimp, clarsimp simp: valid_cap'_def)
  apply (auto simp: singleton_eq_o2s projectKOs obj_at'_def
                    pde_stored_asid_def split: if_split_asm)
  done

lemma thread_state_ptr_set_tsType_np_spec:
  defines "ptr s \<equiv> cparent \<^bsup>s\<^esup>ts_ptr [''tcbState_C''] :: tcb_C ptr"
  shows
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. hrs_htd \<^bsup>s\<^esup>t_hrs \<Turnstile>\<^sub>t ptr s
                 \<and> (tsType_' s = scast ThreadState_Running \<or> tsType_' s = scast ThreadState_Restart
                          \<or> tsType_' s = scast ThreadState_BlockedOnReply)\<rbrace>
              Call thread_state_ptr_set_tsType_np_'proc
       {t. (\<exists>thread_state.
               tsType_CL (thread_state_lift thread_state) = tsType_' s \<and>
               tcbQueued_CL (thread_state_lift thread_state)
                    = tcbQueued_CL (thread_state_lift (tcbState_C (the (cslift s (ptr s))))) \<and>
               t_hrs_' (globals t) = hrs_mem_update (heap_update (ptr s)
                          (the (cslift s (ptr s))\<lparr>tcbState_C := thread_state\<rparr>))
                  (t_hrs_' (globals s))
           )}"
  apply (intro allI, rule conseqPre, vcg)
  apply (clarsimp simp: ptr_def)
  apply (clarsimp simp: h_t_valid_clift_Some_iff)
  apply (frule h_t_valid_c_guard_cparent[OF h_t_valid_clift], simp+,
         simp add: typ_uinfo_t_def)
  apply (frule clift_subtype, simp+)
  apply (clarsimp simp: typ_heap_simps' word_sle_def word_sless_def)
  apply (subst parent_update_child, erule typ_heap_simps', simp+)
  apply (clarsimp simp: typ_heap_simps')
  apply (rule exI, rule conjI[OF _ conjI [OF _ refl]])
  apply (simp_all add: thread_state_lift_def)
  apply (auto simp: "StrictC'_thread_state_defs" mask_def)
  done

lemma thread_state_ptr_mset_blockingObject_tsType_spec:
  defines "ptr s \<equiv> cparent \<^bsup>s\<^esup>ts_ptr [''tcbState_C''] :: tcb_C ptr"
  shows
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. hrs_htd \<^bsup>s\<^esup>t_hrs \<Turnstile>\<^sub>t ptr s \<and> is_aligned (ep_ref_' s) 4
                         \<and> tsType_' s && mask 4 = tsType_' s\<rbrace>
              Call thread_state_ptr_mset_blockingObject_tsType_'proc
       {t. (\<exists>thread_state.
               tsType_CL (thread_state_lift thread_state) = tsType_' s
             \<and> blockingObject_CL (thread_state_lift thread_state) = ep_ref_' s
             \<and> tcbQueued_CL (thread_state_lift thread_state)
                  = tcbQueued_CL (thread_state_lift (tcbState_C (the (cslift s (ptr s)))))
             \<and> t_hrs_' (globals t) = hrs_mem_update (heap_update (ptr s)
                          (the (cslift s (ptr s))\<lparr>tcbState_C := thread_state\<rparr>))
                  (t_hrs_' (globals s))
           )}"
  apply (intro allI, rule conseqPre, vcg)
  apply (clarsimp simp: ptr_def)
  apply (frule h_t_valid_c_guard_cparent, simp+)
   apply (simp add: typ_uinfo_t_def)
  apply (clarsimp simp: h_t_valid_clift_Some_iff)
  apply (frule clift_subtype, simp+)
  apply (clarsimp simp: typ_heap_simps')
  apply (subst parent_update_child, erule typ_heap_simps', simp+)
  apply (clarsimp simp: typ_heap_simps' word_sless_def word_sle_def)
  apply (rule exI, intro conjI[rotated], rule refl)
    apply (simp_all add: thread_state_lift_def word_ao_dist
                         is_aligned_mask mask_def mask_eq_0_eq_x,
           simp_all add: mask_eq_x_eq_0)
  done

lemma mdb_node_ptr_mset_mdbNext_mdbRevocable_mdbFirstBadged_spec:
  defines "ptr s \<equiv> cparent \<^bsup>s\<^esup>node_ptr [''cteMDBNode_C''] :: cte_C ptr"
  shows
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. hrs_htd \<^bsup>s\<^esup>t_hrs \<Turnstile>\<^sub>t ptr s \<and> is_aligned (mdbNext___unsigned_long_' s) 4
                         \<and> mdbRevocable___unsigned_long_' s && mask 1 = mdbRevocable___unsigned_long_' s
                         \<and> mdbFirstBadged___unsigned_long_' s && mask 1 = mdbFirstBadged___unsigned_long_' s\<rbrace>
              Call mdb_node_ptr_mset_mdbNext_mdbRevocable_mdbFirstBadged_'proc
       {t. (\<exists>mdb_node.
               mdb_node_lift mdb_node = mdb_node_lift (cteMDBNode_C (the (cslift s (ptr s))))
                           \<lparr> mdbNext_CL := mdbNext___unsigned_long_' s, mdbRevocable_CL := mdbRevocable___unsigned_long_' s,
                             mdbFirstBadged_CL := mdbFirstBadged___unsigned_long_' s \<rparr>
               \<and> t_hrs_' (globals t) = hrs_mem_update (heap_update (ptr s)
                          (the (cslift s (ptr s)) \<lparr> cteMDBNode_C := mdb_node \<rparr>))
                  (t_hrs_' (globals s))
           )}"
  apply (intro allI, rule conseqPre, vcg)
  apply (clarsimp simp: ptr_def)
  apply (clarsimp simp: h_t_valid_clift_Some_iff)
  apply (frule h_t_valid_c_guard_cparent[OF h_t_valid_clift], simp+,
         simp add: typ_uinfo_t_def)
  apply (frule clift_subtype, simp+)
  apply (clarsimp simp: typ_heap_simps' word_sle_def word_sless_def)
  apply (subst parent_update_child, erule typ_heap_simps', simp+)
  apply (clarsimp simp: typ_heap_simps')
  apply (rule exI, rule conjI[OF _ refl])
  apply (simp add: mdb_node_lift_def word_ao_dist shiftr_over_or_dist ucast_id)
  apply (fold limited_and_def)
  apply (simp add: limited_and_simps mask_def)
  done


lemma mdb_node_ptr_set_mdbPrev_np_spec:
  defines "ptr s \<equiv> cparent \<^bsup>s\<^esup>node_ptr [''cteMDBNode_C''] :: cte_C ptr"
  shows
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. hrs_htd \<^bsup>s\<^esup>t_hrs \<Turnstile>\<^sub>t ptr s \<and> is_aligned (mdbPrev___unsigned_long_' s) 4\<rbrace>
              Call mdb_node_ptr_set_mdbPrev_np_'proc
       {t. (\<exists>mdb_node.
               mdb_node_lift mdb_node = mdb_node_lift (cteMDBNode_C (the (cslift s (ptr s))))
                           \<lparr> mdbPrev_CL := mdbPrev___unsigned_long_' s \<rparr>
               \<and> t_hrs_' (globals t) = hrs_mem_update (heap_update (ptr s)
                          (the (cslift s (ptr s)) \<lparr> cteMDBNode_C := mdb_node \<rparr>))
                  (t_hrs_' (globals s))
           )}"
  apply (intro allI, rule conseqPre, vcg)
  apply (clarsimp simp: ptr_def)
  apply (clarsimp simp: h_t_valid_clift_Some_iff)
  apply (frule h_t_valid_c_guard_cparent[OF h_t_valid_clift], simp+,
         simp add: typ_uinfo_t_def)
  apply (frule clift_subtype, simp+)
  apply (clarsimp simp: typ_heap_simps')
  apply (subst parent_update_child, erule typ_heap_simps', simp+)
  apply (clarsimp simp: typ_heap_simps' word_sle_def word_sless_def)
  apply (rule exI, rule conjI [OF _ refl])
  apply (simp add: mdb_node_lift_def limited_and_simps mask_def)
  done

lemma endpoint_ptr_mset_epQueue_tail_state_spec:
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. hrs_htd \<^bsup>s\<^esup>t_hrs \<Turnstile>\<^sub>t ep_ptr_' s \<and> is_aligned (epQueue_tail_' s) 4
                         \<and> state_' s && mask 2 = state_' s\<rbrace>
              Call endpoint_ptr_mset_epQueue_tail_state_'proc
       {t. (\<exists>endpoint.
               endpoint_lift endpoint = endpoint_lift (the (cslift s (ep_ptr_' s)))
                           \<lparr> endpoint_CL.state_CL := state_' s, epQueue_tail_CL := epQueue_tail_' s \<rparr>
               \<and> t_hrs_' (globals t) = hrs_mem_update (heap_update (ep_ptr_' s)
                          endpoint)
                  (t_hrs_' (globals s))
           )}"
  apply (intro allI, rule conseqPre, vcg)
  apply (clarsimp simp: h_t_valid_clift_Some_iff typ_heap_simps'
                        word_sle_def word_sless_def)
  apply (rule exI, rule conjI[OF _ refl])
  apply (simp add: endpoint_lift_def word_ao_dist
                   mask_def)
  apply (fold limited_and_def)
  apply (simp add: limited_and_simps)
  done

lemma endpoint_ptr_set_epQueue_head_np_spec:
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. hrs_htd \<^bsup>s\<^esup>t_hrs \<Turnstile>\<^sub>t ep_ptr_' s \<and> is_aligned (epQueue_head_' s) 4\<rbrace>
              Call endpoint_ptr_set_epQueue_head_np_'proc
       {t. (\<exists>endpoint.
               endpoint_lift endpoint = endpoint_lift (the (cslift s (ep_ptr_' s)))
                           \<lparr> epQueue_head_CL := epQueue_head_' s \<rparr>
               \<and> t_hrs_' (globals t) = hrs_mem_update (heap_update (ep_ptr_' s)
                          endpoint)
                  (t_hrs_' (globals s))
           )}"
  apply (intro allI, rule conseqPre, vcg)
  apply (clarsimp simp: h_t_valid_clift_Some_iff typ_heap_simps'
                        word_sless_def word_sle_def)
  apply (rule exI, rule conjI[OF _ refl])
  apply (simp add: endpoint_lift_def word_ao_dist
                   mask_def)
  apply (simp add: limited_and_simps)
  done

lemma ccorres_call_hSkip':
  assumes  cul: "ccorres_underlying sr \<Gamma> r xf' r xf' P (i ` P') [SKIP] a (Call f)"
  and      gsr: "\<And>a b x s t. (x, t) \<in> sr \<Longrightarrow> (x, g a b (clean s t)) \<in> sr"
  and      csr: "\<And>x s t. (x, t) \<in> sr \<Longrightarrow> (x, clean s t) \<in> sr"
  and      res: "\<And>a s t rv. r rv (xf' t) \<Longrightarrow> r rv (xf (g a t (clean s t)))"
  and     ares: "\<And>s t rv. r rv (xf' t) \<Longrightarrow> r rv (xf (clean s t))"
  and      ist: "\<And>x s. (x, s) \<in> sr \<Longrightarrow> (x, i s) \<in> sr"
  shows "ccorres_underlying sr \<Gamma> r xf r xf P P' [SKIP] a (call i f clean (\<lambda>x y. Basic (g x y)))"
  apply (rule ccorresI')
  apply (erule exec_handlers.cases, simp_all)[1]
   apply clarsimp
   apply (erule exec_call_Normal_elim, simp_all)[1]
    apply (clarsimp elim!: exec_Normal_elim_cases)
   apply (rule ccorresE[OF cul ist], assumption+, simp+)
    apply (rule EHAbrupt)
     apply (erule(1) exec.Call)
    apply (rule EHOther, rule exec.Skip, simp)
   apply clarsimp
   apply (erule exec_handlers.cases, simp_all)[1]
    apply (clarsimp elim!: exec_Normal_elim_cases)
   apply (clarsimp elim!: exec_Normal_elim_cases)
   apply (erule rev_bexI)
   apply (simp add: unif_rrel_simps csr ares)
  apply clarsimp
  apply (erule exec_call_Normal_elim, simp_all)[1]
     apply (clarsimp elim!: exec_Normal_elim_cases)
     apply (rule ccorresE[OF cul ist], assumption+, simp+)
      apply (rule EHOther, erule(1) exec.Call)
      apply simp
     apply (simp add: unif_rrel_simps)
     apply (erule rev_bexI)
     apply (simp add: gsr res)
    apply (rule ccorresE[OF cul ist], assumption+, simp+)
     apply (rule EHOther, erule(1) exec.Call)
     apply simp
    apply simp
   apply (rule ccorresE[OF cul ist], assumption+, simp+)
    apply (rule EHOther, erule(1) exec.Call)
    apply simp
   apply simp
  apply (rule ccorresE[OF cul ist], assumption+, simp+)
   apply (rule EHOther, erule exec.CallUndefined)
   apply simp
  apply simp
  done

(* The naming convention here is that xf', xfr, and xfru are the terms we instantiate *)
lemma ccorres_call_hSkip:
  assumes  cul: "ccorres_underlying rf_sr \<Gamma> r xfdc r xfdc A C' [SKIP] a (Call f)"
  and      ggl: "\<And>x y s. globals (g x y s) = globals s"
  and      igl: "\<And>s. globals (i s) = globals s"
  shows "ccorres_underlying rf_sr \<Gamma> r xfdc r xfdc
          A {s. i s \<in> C'} [SKIP] a (call i f (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) (\<lambda>x y. Basic (g x y)))"
  using cul
  unfolding rf_sr_def
  apply -
  apply (rule ccorres_call_hSkip')
       apply (erule ccorres_guard_imp)
        apply simp
       apply clarsimp
      apply (simp_all add: ggl xfdc_def)
  apply (clarsimp simp: igl)
  done

lemma bind_case_sum_rethrow:
  "rethrowFailure fl f >>= case_sum e g
     = f >>= case_sum (e \<circ> fl) g"
  apply (simp add: rethrowFailure_def handleE'_def
                   bind_assoc)
  apply (rule bind_cong[OF refl])
  apply (simp add: throwError_bind split: sum.split)
  done

lemma ccorres_pre_getCTE2:
  "(\<And>rv. ccorresG rf_sr \<Gamma> r xf (P rv) (P' rv) hs (f rv) c) \<Longrightarrow>
   ccorresG rf_sr \<Gamma> r xf (\<lambda>s. \<forall>cte. ctes_of s p = Some cte \<longrightarrow> P cte s)
                         {s. \<forall>cte cte'. cslift s (cte_Ptr p) = Some cte' \<and> ccte_relation cte cte'
                                          \<longrightarrow> s \<in> P' cte} hs
         (getCTE p >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp2, erule ccorres_pre_getCTE)
  apply (clarsimp simp: map_comp_Some_iff ccte_relation_def
                        c_valid_cte_def cl_valid_cte_def
                        c_valid_cap_def)
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

lemma fastpath_mi_check:
  "((mi && mask 9) + 3) && ~~ mask 3 = 0
      = (msgExtraCaps (messageInfoFromWord mi) = 0
            \<and> msgLength (messageInfoFromWord mi) \<le> scast n_msgRegisters
            \<and> length_CL (seL4_MessageInfo_lift (seL4_MessageInfo_C (FCP (K mi))))
                  \<le> scast n_msgRegisters)"
  (is "?P = (?Q \<and> ?R \<and> ?S)")
proof -
  have le_Q: "?P = (?Q \<and> ?S)"
    apply (simp add: mask_def messageInfoFromWord_def Let_def
                     msgExtraCapBits_def msgLengthBits_def
                     seL4_MessageInfo_lift_def fcp_beta n_msgRegisters_def)
    apply word_bitwise
    apply blast
    done
  have Q_R: "?S \<Longrightarrow> ?R"
    apply (clarsimp simp: messageInfoFromWord_def Let_def msgLengthBits_def
                          msgExtraCapBits_def mask_def n_msgRegisters_def
                          seL4_MessageInfo_lift_def fcp_beta)
    apply (subst if_not_P, simp_all)
    apply (simp add: msgMaxLength_def linorder_not_less)
    apply (erule order_trans, simp)
    done
  from le_Q Q_R show ?thesis
    by blast
qed

lemma messageInfoFromWord_raw_spec:
  "\<forall>s. \<Gamma>\<turnstile> {s} Call messageInfoFromWord_raw_'proc
       \<lbrace>\<acute>ret__struct_seL4_MessageInfo_C
    = (seL4_MessageInfo_C (FCP (K \<^bsup>s\<^esup>w)))\<rbrace>"
  apply vcg
  apply (clarsimp simp: word_sless_def word_sle_def)
  apply (case_tac v)
  apply (simp add: cart_eq fcp_beta)
  done

lemma mi_check_messageInfo_raw:
  "length_CL (seL4_MessageInfo_lift (seL4_MessageInfo_C (FCP (K mi))))
                  \<le> scast n_msgRegisters
    \<Longrightarrow> seL4_MessageInfo_lift (seL4_MessageInfo_C (FCP (K mi)))
        = mi_from_H (messageInfoFromWord mi)"
  apply (simp add: messageInfoFromWord_def Let_def mi_from_H_def
                   seL4_MessageInfo_lift_def fcp_beta msgLengthBits_def msgExtraCapBits_def
                   msgMaxExtraCaps_def shiftL_nat mask_def msgLabelBits_def)
  apply (subst if_not_P)
   apply (simp add: linorder_not_less msgMaxLength_def n_msgRegisters_def)
   apply (erule order_trans, simp)
  apply simp
  done

lemma fastpath_mi_check_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. True\<rbrace> Call fastpath_mi_check_'proc
           \<lbrace>(\<acute>ret__int = 0) = (msgExtraCaps (messageInfoFromWord \<^bsup>s\<^esup>msgInfo) = 0
              \<and> msgLength (messageInfoFromWord \<^bsup>s\<^esup>msgInfo) \<le> scast n_msgRegisters
              \<and> seL4_MessageInfo_lift (seL4_MessageInfo_C (FCP (K \<^bsup>s\<^esup>msgInfo)))
                  = mi_from_H (messageInfoFromWord \<^bsup>s\<^esup>msgInfo))\<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: seL4_MsgLengthBits_def seL4_MsgExtraCapBits_def
                        word_sle_def if_1_0_0)
  apply (cut_tac mi="msgInfo_' s" in fastpath_mi_check)
  apply (simp add: mask_def)
  apply (auto intro: mi_check_messageInfo_raw[unfolded K_def])
  done

lemma isValidVTableRoot_fp_lemma:
  "(index (cap_C.words_C ccap) 0 && 0x1F = 0x10 || scast cap_page_directory_cap)
            = isValidVTableRoot_C ccap"
  apply (simp add: isValidVTableRoot_C_def ARM_H.isValidVTableRoot_def
                   cap_case_isPageDirectoryCap if_bool_simps)
  apply (subst split_word_eq_on_mask[where m="mask 4"])
  apply (simp add: mask_def word_bw_assocs word_ao_dist cap_page_directory_cap_def)
  apply (subgoal_tac "cap_get_tag ccap = scast cap_page_directory_cap
                  \<Longrightarrow> (index (cap_C.words_C ccap) 0 && 0x10 = 0x10) = to_bool (capPDIsMapped_CL (cap_page_directory_cap_lift ccap))")
   apply (clarsimp simp add: cap_get_tag_eq_x mask_def
                             cap_page_directory_cap_def split: if_split)
   apply (rule conj_cong[OF refl])
   apply clarsimp
  apply (clarsimp simp: cap_lift_page_directory_cap
                        cap_to_H_simps
                        to_bool_def bool_mask[folded word_neq_0_conv]
                        cap_page_directory_cap_lift_def
                 elim!: ccap_relationE split: if_split)
  apply (thin_tac "P" for P)
  apply word_bitwise
  done

lemma isValidVTableRoot_fp_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call isValidVTableRoot_fp_'proc
       {t. ret__unsigned_long_' t = from_bool (isValidVTableRoot_C (pd_cap_' s))}"
  apply vcg
  apply (clarsimp simp: word_sle_def word_sless_def isValidVTableRoot_fp_lemma)
  apply (simp add: from_bool_def split: if_split)
  done

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

end

abbreviation "tcb_Ptr_Ptr \<equiv> (Ptr :: word32 \<Rightarrow> tcb_C ptr ptr)"

abbreviation(input)
  "ptr_basic_update ptrfun vfun
      \<equiv> Basic (\<lambda>s. globals_update (t_hrs_'_update (hrs_mem_update
                    (heap_update (ptrfun s) (vfun s)))) s)"

context kernel_m begin

lemma fastpath_dequeue_ccorres:
  "dest1 = dest2 \<and> dest2 = tcb_ptr_to_ctcb_ptr dest \<and> ep_ptr1 = ep_Ptr ep_ptr \<Longrightarrow>
   ccorres dc xfdc
       (ko_at' (RecvEP (dest # xs)) ep_ptr and invs')
            {s. dest2 = tcb_ptr_to_ctcb_ptr dest
               \<and> dest1 = tcb_ptr_to_ctcb_ptr dest
               \<and> ep_ptr1 = ep_Ptr ep_ptr} hs
   (setEndpoint ep_ptr (case xs of [] \<Rightarrow> IdleEP | _ \<Rightarrow> RecvEP xs))
   (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t dest1\<rbrace>
     (CALL endpoint_ptr_set_epQueue_head_np(ep_ptr1,ptr_val (h_val (hrs_mem \<acute>t_hrs) (tcb_Ptr_Ptr &(dest2\<rightarrow>[''tcbEPNext_C''])))));;
      Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t dest1\<rbrace>
     (IF h_val (hrs_mem \<acute>t_hrs) (tcb_Ptr_Ptr &(dest1\<rightarrow>[''tcbEPNext_C''])) \<noteq> tcb_Ptr 0 THEN
      Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t h_val (hrs_mem \<acute>t_hrs) (tcb_Ptr_Ptr &(dest1\<rightarrow>[''tcbEPNext_C'']))\<rbrace>
       (Guard C_Guard {s. s \<Turnstile>\<^sub>c dest1} (
       (ptr_basic_update (\<lambda>s. tcb_Ptr_Ptr &(h_val (hrs_mem (t_hrs_' (globals s)))
                                (tcb_Ptr_Ptr &(dest1\<rightarrow>[''tcbEPNext_C'']))\<rightarrow>[''tcbEPPrev_C''])) (\<lambda>_. NULL))))
      ELSE
        CALL endpoint_ptr_mset_epQueue_tail_state(ep_ptr1,0,scast EPState_Idle)
      FI))"
  unfolding setEndpoint_def
  apply (rule setObject_ccorres_helper[rotated])
    apply simp
   apply (simp add: objBits_simps')
  apply (rule conseqPre, vcg)
  apply clarsimp
  apply (drule(1) ko_at_obj_congD')
  apply (frule ko_at_valid_ep', clarsimp)
  apply (rule cmap_relationE1[OF cmap_relation_ep], assumption,
         erule ko_at_projectKO_opt)
  apply (clarsimp simp: typ_heap_simps' valid_ep'_def
                        isRecvEP_endpoint_case neq_Nil_conv)
  apply (drule(1) obj_at_cslift_tcb)
  apply (clarsimp simp: typ_heap_simps')
  apply (case_tac "xs")
   apply (clarsimp simp: cendpoint_relation_def Let_def
                         isRecvEP_endpoint_case
                         tcb_queue_relation'_def
                         typ_heap_simps' endpoint_state_defs)
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
   apply (rule conjI)
    apply (clarsimp simp: cpspace_relation_def update_ep_map_tos
                          typ_heap_simps')
    apply (erule(1) cpspace_relation_ep_update_ep2)
     apply (simp add: cendpoint_relation_def endpoint_state_defs)
    apply simp
   apply (simp add: carch_state_relation_def cmachine_state_relation_def
                    h_t_valid_clift_Some_iff update_ep_map_tos
                    typ_heap_simps')
  apply (clarsimp simp: neq_Nil_conv cendpoint_relation_def Let_def
                        isRecvEP_endpoint_case tcb_queue_relation'_def
                        typ_heap_simps' endpoint_state_defs)
  apply (clarsimp simp: is_aligned_weaken[OF is_aligned_tcb_ptr_to_ctcb_ptr]
                        tcb_at_not_NULL)
  apply (drule(1) obj_at_cslift_tcb)+
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                        typ_heap_simps' tcb_at_not_NULL[OF obj_at'_weakenE, OF _ TrueI])
  apply (rule conjI)
   apply (clarsimp simp: cpspace_relation_def update_ep_map_tos
                         update_tcb_map_tos typ_heap_simps')
   apply (rule conjI, erule ctcb_relation_null_queue_ptrs)
    apply (rule ext, simp add: tcb_null_queue_ptrs_def
                        split: if_split)
   apply (rule conjI)
    apply (rule cpspace_relation_ep_update_ep, assumption+)
     apply (simp add: Let_def cendpoint_relation_def EPState_Recv_def)
     apply (simp add: tcb_queue_relation'_def tcb_queue_update_other)
    apply (simp add: isRecvEP_def)
   apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
   apply simp
   apply (rule cnotification_relation_ep_queue [OF invs_sym'], assumption+)
     apply (simp add: isRecvEP_def)
    apply simp
   apply (erule (1) map_to_ko_atI')
  apply (simp add: carch_state_relation_def typ_heap_simps'
                   cmachine_state_relation_def h_t_valid_clift_Some_iff
                   update_ep_map_tos)
  apply (erule cready_queues_relation_null_queue_ptrs)
  apply (rule ext, simp add: tcb_null_ep_ptrs_def split: if_split)
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

lemma cntfn_relation_double_fun_upd:
  "\<lbrakk> cnotification_relation mp ntfn ntfn'
       = cnotification_relation (mp(a := b)) ntfn ntfn';
     cnotification_relation (mp(a := b)) ntfn ntfn'
       = cnotification_relation (mp(a := b, c := d)) ntfn ntfn' \<rbrakk>
   \<Longrightarrow> cnotification_relation mp ntfn ntfn'
         = cnotification_relation (mp(a := b, c := d)) ntfn ntfn'"
  by simp

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

lemma fastpath_enqueue_ccorres:
  "\<lbrakk> epptr' = ep_Ptr epptr \<rbrakk> \<Longrightarrow>
   ccorres dc xfdc
         (ko_at' ep epptr and (\<lambda>s. thread = ksCurThread s)
                and (\<lambda>s. sym_refs ((state_refs_of' s) (thread := {r \<in> state_refs_of' s thread. snd r = TCBBound})))
                and K (\<not> isSendEP ep) and valid_pspace' and cur_tcb')
         UNIV hs
     (setEndpoint epptr (case ep of IdleEP \<Rightarrow> RecvEP [thread] | RecvEP ts \<Rightarrow> RecvEP (ts @ [thread])))
     (\<acute>ret__unsigned :== CALL endpoint_ptr_get_epQueue_tail(epptr');;
      \<acute>endpointTail :== tcb_Ptr \<acute>ret__unsigned;;
      IF \<acute>endpointTail = tcb_Ptr 0 THEN
         (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>ksCurThread\<rbrace>
            (ptr_basic_update (\<lambda>s. tcb_Ptr_Ptr &((ksCurThread_' (globals s))\<rightarrow>[''tcbEPPrev_C''])) (\<lambda>_. NULL)));;
         (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>ksCurThread\<rbrace>
          (ptr_basic_update (\<lambda>s. tcb_Ptr_Ptr &((ksCurThread_' (globals s))\<rightarrow>[''tcbEPNext_C''])) (\<lambda>_. NULL)));;
           (CALL endpoint_ptr_set_epQueue_head_np(epptr',ucast (ptr_val \<acute>ksCurThread)));;
           (CALL endpoint_ptr_mset_epQueue_tail_state(epptr',ucast (ptr_val \<acute>ksCurThread),
            scast EPState_Recv))
      ELSE
        Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>endpointTail\<rbrace>
          (ptr_basic_update (\<lambda>s. tcb_Ptr_Ptr &((endpointTail_' s)\<rightarrow>[''tcbEPNext_C'']))
                      (ksCurThread_' o globals));;
         (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>ksCurThread\<rbrace>
          (ptr_basic_update (\<lambda>s. tcb_Ptr_Ptr &((ksCurThread_' (globals s))\<rightarrow>[''tcbEPPrev_C'']))
                      endpointTail_'));;
         (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>ksCurThread\<rbrace>
          (ptr_basic_update (\<lambda>s. tcb_Ptr_Ptr &((ksCurThread_' (globals s))\<rightarrow>[''tcbEPNext_C'']))
                      (\<lambda>_. NULL)));;
           (CALL endpoint_ptr_mset_epQueue_tail_state(epptr',ucast (ptr_val \<acute>ksCurThread),
            scast EPState_Recv))
      FI)"
  unfolding setEndpoint_def
  apply clarsimp
  apply (rule setObject_ccorres_helper[rotated])
    apply simp
   apply (simp add: objBits_simps')
  apply (rule conseqPre, vcg)
  apply clarsimp
  apply (drule(1) ko_at_obj_congD')
  apply (frule ko_at_valid_ep', clarsimp)
  apply (rule cmap_relationE1[OF cmap_relation_ep], assumption,
         erule ko_at_projectKO_opt)
  apply (simp add: cur_tcb'_def)
  apply (drule(1) obj_at_cslift_tcb)
  apply (clarsimp simp: typ_heap_simps' valid_ep'_def rf_sr_ksCurThread)
  apply (cases ep,
         simp_all add: isSendEP_def cendpoint_relation_def Let_def
                       tcb_queue_relation'_def)
   apply (rename_tac list)
   apply (clarsimp simp: NULL_ptr_val[symmetric] tcb_queue_relation_last_not_NULL
                         ct_in_state'_def
                  dest!: trans [OF sym [OF ptr_val_def] arg_cong[where f=ptr_val]])
   apply (frule obj_at_cslift_tcb[rotated], erule(1) bspec[OF _ last_in_set])
   apply clarsimp
   apply (drule(2) sym_refs_upd_tcb_sD)
   apply clarsimp
   apply (frule st_tcb_at_not_in_ep_queue,
          fastforce, simp+)
   apply (subgoal_tac "ksCurThread \<sigma> \<noteq> last list")
    prefer 2
    apply clarsimp
   apply (clarsimp simp: typ_heap_simps' EPState_Recv_def mask_def
                         is_aligned_weaken[OF is_aligned_tcb_ptr_to_ctcb_ptr])
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
   apply (rule conjI)
    apply (clarsimp simp: cpspace_relation_def update_ep_map_tos
                          typ_heap_simps')
    apply (rule conjI, erule ctcb_relation_null_queue_ptrs)
     apply (rule ext, simp add: tcb_null_queue_ptrs_def
                         split: if_split)
    apply (rule conjI)
     apply (rule_tac S="tcb_ptr_to_ctcb_ptr ` set (ksCurThread \<sigma> # list)"
                   in cpspace_relation_ep_update_an_ep,
                 assumption+)
         apply (simp add: cendpoint_relation_def Let_def EPState_Recv_def
                          tcb_queue_relation'_def)
         apply (drule_tac qend="tcb_ptr_to_ctcb_ptr (last list)"
                     and qend'="tcb_ptr_to_ctcb_ptr (ksCurThread \<sigma>)"
                     and tn_update="tcbEPNext_C_update"
                     and tp_update="tcbEPPrev_C_update"
                     in tcb_queue_relation_append,
                    clarsimp+, simp_all)[1]
           apply (rule sym, erule init_append_last)
          apply (fastforce simp: tcb_at_not_NULL)
         apply (clarsimp simp add: tcb_at_not_NULL[OF obj_at'_weakenE[OF _ TrueI]])
        apply clarsimp+
     apply (subst st_tcb_at_not_in_ep_queue, assumption, blast, clarsimp+)
     apply (drule(1) ep_ep_disjoint[rotated -1, where epptr=epptr],
            blast, blast,
            simp_all add: Int_commute endpoint_not_idle_cases image_image)[1]
    apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
    apply simp
    apply (rule cntfn_relation_double_fun_upd)
     apply (rule cnotification_relation_ep_queue, assumption+)
        apply fastforce
       apply (simp add: isRecvEP_def)
      apply simp
     apply (fastforce dest!: map_to_ko_atI)

    apply (rule cnotification_relation_q_cong)
    apply (clarsimp split: if_split)
    apply (clarsimp simp: restrict_map_def ntfn_q_refs_of'_def
                   split: if_split Structures_H.notification.split_asm Structures_H.ntfn.split_asm)
    apply (erule notE[rotated], erule_tac ntfnptr=p and ntfn=a in st_tcb_at_not_in_ntfn_queue,
           auto dest!: map_to_ko_atI)[1]
   apply (simp add: carch_state_relation_def typ_heap_simps' update_ep_map_tos
                    cmachine_state_relation_def h_t_valid_clift_Some_iff)
   apply (erule cready_queues_relation_null_queue_ptrs)
   apply (rule ext, simp add: tcb_null_ep_ptrs_def split: if_split)
  apply (clarsimp simp: typ_heap_simps' EPState_Recv_def mask_def
                        is_aligned_weaken[OF is_aligned_tcb_ptr_to_ctcb_ptr])
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (drule(2) sym_refs_upd_tcb_sD)
  apply (rule conjI)
   apply (clarsimp simp: cpspace_relation_def update_ep_map_tos
                         typ_heap_simps' ct_in_state'_def)
   apply (rule conjI, erule ctcb_relation_null_queue_ptrs)
    apply (rule ext, simp add: tcb_null_queue_ptrs_def
                        split: if_split)
   apply (rule conjI)
    apply (rule_tac S="{tcb_ptr_to_ctcb_ptr (ksCurThread \<sigma>)}"
                 in cpspace_relation_ep_update_an_ep, assumption+)
        apply (simp add: cendpoint_relation_def Let_def EPState_Recv_def
                         tcb_queue_relation'_def)
       apply clarsimp+
    apply (erule notE[rotated], erule st_tcb_at_not_in_ep_queue,
           auto)[1]
   apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
   apply simp
   apply (rule cnotification_relation_q_cong)
   apply (clarsimp split: if_split)
   apply (clarsimp simp: restrict_map_def ntfn_q_refs_of'_def
                  split: if_split Structures_H.notification.split_asm Structures_H.ntfn.split_asm)
   apply (erule notE[rotated], rule_tac ntfnptr=p and ntfn=a in st_tcb_at_not_in_ntfn_queue,
          assumption+, auto dest!: map_to_ko_atI)[1]
  apply (simp add: carch_state_relation_def typ_heap_simps' update_ep_map_tos
                   cmachine_state_relation_def h_t_valid_clift_Some_iff)
  apply (erule cready_queues_relation_null_queue_ptrs)
  apply (rule ext, simp add: tcb_null_ep_ptrs_def split: if_split)
  done

lemma setCTE_rf_sr:
  "\<lbrakk> (\<sigma>, s) \<in> rf_sr; ctes_of \<sigma> ptr = Some cte'';
     t_hrs_' (globals s') = hrs_mem_update
        (heap_update (cte_Ptr ptr) cte')
        (t_hrs_' (globals s));
     ccte_relation cte cte';
     (globals s')\<lparr> t_hrs_' := undefined \<rparr>
          = (globals s)\<lparr> t_hrs_' := undefined \<rparr> \<rbrakk>
      \<Longrightarrow>
   \<exists>x\<in>fst (setCTE ptr cte \<sigma>).
             (snd x, s') \<in> rf_sr"
  apply (rule fst_setCTE[OF ctes_of_cte_at], assumption)
  apply (erule rev_bexI)
  apply clarsimp
  apply (frule(1) rf_sr_ctes_of_clift)
  apply (subgoal_tac "\<exists>hrs. globals s' = globals s
                          \<lparr> t_hrs_' := hrs \<rparr>")
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                         typ_heap_simps' cpspace_relation_def)
   apply (rule conjI)
    apply (erule(2) cmap_relation_updI, simp)
   apply (erule_tac t = s'a in ssubst)
   apply (simp add: heap_to_user_data_def)
   apply (rule conjI)
    apply (erule(1) setCTE_tcb_case)
   apply (simp add: carch_state_relation_def cmachine_state_relation_def
                    cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                    typ_heap_simps' h_t_valid_clift_Some_iff)
  apply (cases "globals s", cases "globals s'")
  apply simp
  done

lemma getCTE_setCTE_rf_sr:
  "\<lbrakk> (\<sigma>, s) \<in> rf_sr; ctes_of \<sigma> ptr = Some cte;
     t_hrs_' (globals s') = hrs_mem_update
        (heap_update (cte_Ptr ptr) cte')
        (t_hrs_' (globals s));
     ccte_relation (f cte) cte';
     (globals s')\<lparr> t_hrs_' := undefined \<rparr>
          = (globals s)\<lparr> t_hrs_' := undefined \<rparr> \<rbrakk>

      \<Longrightarrow>
   \<exists>x\<in>fst ((do cte \<leftarrow> getCTE ptr;
                      setCTE ptr (f cte)
                    od)
                    \<sigma>).
             (snd x, s') \<in> rf_sr"
  apply (drule setCTE_rf_sr, assumption+)
  apply (clarsimp simp: Bex_def in_bind_split in_getCTE2 cte_wp_at_ctes_of)
  done

lemma ccte_relation_eq_ccap_relation:
  notes option.case_cong_weak [cong]
  shows
  "ccte_relation cte ccte
      = (ccap_relation (cteCap cte) (cte_C.cap_C ccte)
            \<and> mdb_node_to_H (mdb_node_lift (cteMDBNode_C ccte))
                   = (cteMDBNode cte))"
  apply (simp add: ccte_relation_def map_option_Some_eq2 cte_lift_def
                   ccap_relation_def)
  apply (simp add: cte_to_H_def split: option.split)
  apply (cases cte, clarsimp simp: c_valid_cte_def conj_comms)
  done

lemma cap_reply_cap_ptr_new_np_updateCap_ccorres:
  "ccorres dc xfdc
        (cte_at' ptr and tcb_at' thread)
        (UNIV \<inter> {s. cap_ptr_' s = cap_Ptr &(cte_Ptr ptr \<rightarrow> [''cap_C''])}
              \<inter> {s. capTCBPtr___unsigned_long_' s = ptr_val (tcb_ptr_to_ctcb_ptr thread)}
              \<inter> {s. capReplyMaster___unsigned_long_' s = from_bool m}
              \<inter> {s. capReplyCanGrant___unsigned_long_' s = from_bool canGrant}) []
     (updateCap ptr (ReplyCap thread m canGrant))
     (Call cap_reply_cap_ptr_new_np_'proc)"
  apply (rule ccorres_from_vcg, rule allI)
  apply (rule conseqPre, vcg)
  apply (clarsimp simp: cte_wp_at_ctes_of word_sle_def)
   apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
  apply (clarsimp simp: updateCap_def split_def typ_heap_simps'
                        word_sless_def word_sle_def)
  apply (erule(1) getCTE_setCTE_rf_sr, simp_all add: typ_heap_simps')
  apply (clarsimp simp: ccte_relation_eq_ccap_relation
                        ccap_relation_def c_valid_cap_def)
  apply (frule is_aligned_tcb_ptr_to_ctcb_ptr)
  apply (rule ssubst[OF cap_lift_reply_cap])
   apply (simp add: cap_get_tag_def cap_reply_cap_def ctcb_size_bits_def
                    mask_def word_ao_dist
                    limited_and_simps
                    limited_and_simps1[OF lshift_limited_and, OF limited_and_from_bool])
  apply (simp add: cap_to_H_simps word_ao_dist cl_valid_cap_def ctcb_size_bits_def
                   limited_and_simps cap_reply_cap_def
                   limited_and_simps1[OF lshift_limited_and, OF limited_and_from_bool]
                   shiftr_over_or_dist word_bw_assocs mask_def)
  apply (cases m ; clarsimp)
  apply (cases canGrant ; clarsimp)
  done

lemma fastpath_copy_mrs_ccorres:
notes nat_min_simps [simp del]
shows
  "ccorres dc xfdc (\<top> and (\<lambda>_. len <= length ARM_H.msgRegisters))
     (UNIV \<inter> {s. unat (length___unsigned_long_' s) = len}
           \<inter> {s. src_' s = tcb_ptr_to_ctcb_ptr src}
           \<inter> {s. dest_' s = tcb_ptr_to_ctcb_ptr dest}) []
     (forM_x (take len ARM_H.msgRegisters)
             (\<lambda>r. do v \<leftarrow> asUser src (getRegister r);
                    asUser dest (setRegister r v) od))
     (Call fastpath_copy_mrs_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit' lift: length___unsigned_long_' src_' dest_' simp: word_sle_def word_sless_def)
   apply (unfold whileAnno_def)
   apply (rule ccorres_rel_imp)
    apply (rule_tac F="K \<top>" in ccorres_mapM_x_while)
        apply clarsimp
        apply (rule ccorres_guard_imp2)
         apply (rule ccorres_rhs_assoc)+
         apply (rule_tac xf'="i_'" in ccorres_abstract, ceqv)
         apply csymbr
         apply (ctac(no_vcg))
          apply ctac
         apply wp
        apply (clarsimp simp: rf_sr_ksCurThread)
        apply (simp add: msgRegisters_ccorres[symmetric] length_msgRegisters)
        apply (simp add: n_msgRegisters_def msgRegisters_unfold)
        apply (drule(1) order_less_le_trans)
        apply (clarsimp simp: "StrictC'_register_defs" msgRegistersC_def fupdate_def
          | drule nat_less_cases' | erule disjE)+
       apply (simp add: min.absorb2)
      apply (rule allI, rule conseqPre, vcg)
      apply (simp)
     apply (simp add: length_msgRegisters n_msgRegisters_def word_bits_def hoare_TrueI)+
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
  "\<lbrace>\<lambda>s. tcb_at' t s \<and> (\<forall>rv. obj_at' (\<lambda>tcb. (atcbContextGet o tcbArch) tcb r = rv) t s \<longrightarrow> Q rv s)\<rbrace>
      asUser t (getRegister r) \<lbrace>Q\<rbrace>"
  apply (rule_tac Q="\<lambda>rv s. \<exists>rv'. rv' = rv \<and> Q rv' s" in hoare_post_imp)
   apply simp
  apply (rule hoare_pre, wp hoare_vcg_ex_lift user_getreg_rv)
  apply (clarsimp simp: obj_at'_def)
  done

lemma cap_page_directory_cap_get_capPDBasePtr_spec2:
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. True\<rbrace>
     Call cap_page_directory_cap_get_capPDBasePtr_'proc
   \<lbrace>cap_get_tag \<^bsup>s\<^esup>cap = scast cap_page_directory_cap
       \<longrightarrow> \<acute>ret__unsigned = capPDBasePtr_CL (cap_page_directory_cap_lift \<^bsup>s\<^esup>cap)\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply vcg
  apply (clarsimp simp: word_sle_def word_sless_def
                        cap_page_directory_cap_lift_def
                        cap_lift_page_directory_cap mask_def)
  done

lemma ccorres_flip_Guard2:
  assumes cc: "ccorres_underlying sr \<Gamma> r xf arrel axf A C hs a (Guard F S (Guard F1 S1 c) ;; d)"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf A C hs a (Guard F1 S1 (Guard F S c) ;; d)"
  apply (rule ccorres_name_pre_C)
  using cc
  apply (case_tac "s \<in> (S1 \<inter> S)")
   apply (clarsimp simp: ccorres_underlying_def)
   apply (erule exec_handlers.cases;
    fastforce elim!: exec_Normal_elim_cases intro: exec_handlers.intros exec.Guard exec.Seq)
  apply (clarsimp simp: ccorres_underlying_def)
  apply (case_tac "s \<in> S")
   apply (fastforce intro: exec.Guard exec.GuardFault exec_handlers.intros exec.Seq)
  apply (fastforce intro: exec.Guard exec.GuardFault exec_handlers.intros exec.Seq)
  done

lemmas cte_C_numeral_fold = cte_C_size[THEN meta_eq_to_obj_eq,
    THEN arg_cong[where f="of_nat :: _ \<Rightarrow> word32"], simplified, symmetric]

lemmas ccorres_move_c_guard_tcb_ctes2
    = ccorres_move_c_guard_tcb_ctes[unfolded cte_C_numeral_fold]

lemma setUntypedCapAsFull_replyCap[simp]:
  "setUntypedCapAsFull cap (ReplyCap curThread False cg) slot =  return ()"
   by (clarsimp simp:setUntypedCapAsFull_def isCap_simps)

end

context kernel_m begin

lemma obj_at_bound_tcb_grandD:
  "\<lbrakk> obj_at' P t s; valid_objs' s; no_0_obj' s; (s, s') \<in> rf_sr \<rbrakk>
    \<Longrightarrow> \<exists>tcb tcb' ntfn ntfn'. ko_at' tcb t s \<and> P tcb
       \<and> cslift s' (tcb_ptr_to_ctcb_ptr t) = Some tcb'
       \<and> ctcb_relation tcb tcb'
       \<and> ((tcbBoundNotification_C tcb' = NULL) = (tcbBoundNotification tcb = None))
       \<and> (tcbBoundNotification tcb \<noteq> None \<longrightarrow> ko_at' ntfn (the (tcbBoundNotification tcb)) s)
       \<and> (tcbBoundNotification tcb \<noteq> None \<longrightarrow> cslift s' (tcbBoundNotification_C tcb') = Some ntfn')
       \<and> (tcbBoundNotification tcb \<noteq> None \<longrightarrow> cnotification_relation (cslift s') ntfn ntfn')"
  apply (clarsimp simp: pred_tcb_at'_def)
  apply (drule(1) obj_at_cslift_tcb, clarsimp)
  apply (rule exI, rule conjI, assumption)
  apply (clarsimp simp: ctcb_relation_def
                                 option_to_ptr_def option_to_0_def)
  apply (simp add: return_def split: option.split_asm)
  apply (drule_tac s="ntfn_Ptr x"for x in sym)
  apply (drule(1) ko_at_valid_objs', clarsimp simp: projectKOs)
  apply (clarsimp simp: projectKOs valid_obj'_def valid_tcb'_def)
  apply (drule obj_at_ko_at', clarsimp)
  apply (rule conjI, clarsimp)
  apply (rule cmap_relationE1[OF cmap_relation_ntfn], assumption, erule ko_at_projectKO_opt)
  apply auto
  done

lemma cnotification_relation_isActive:
  "cnotification_relation tcbs ntfn ntfn'
       \<Longrightarrow> (notification_CL.state_CL (notification_lift ntfn') = scast NtfnState_Active)
     = EndpointDecls_H.isActive ntfn"
  apply (clarsimp simp: cnotification_relation_def Let_def)
  apply (cases ntfn, simp)
  apply (rename_tac ntfna ooeuoue)
  apply (case_tac ntfna, simp_all add: notification_state_defs isActive_def)
  done

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

lemma getCurDomain_maxDom_ccorres_dom_':
  "ccorres (\<lambda>rv rv'. rv' = ucast rv) dom_'
     (\<lambda>s. ksCurDomain s \<le> maxDomain) UNIV hs
     curDomain (\<acute>dom :== (if maxDom \<noteq> 0 then \<acute>ksCurDomain else 0))"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  using maxDom_to_H
  apply (clarsimp simp: curDomain_def simpler_gets_def rf_sr_ksCurDomain maxDom_def)
  done

lemma fastpath_call_ccorres:
  notes hoare_TrueI[simp]
  shows "ccorres dc xfdc
     (\<lambda>s. invs' s \<and> ct_in_state' ((=) Running) s
                  \<and> obj_at' (\<lambda>tcb. (atcbContextGet o tcbArch) tcb ARM_H.capRegister = cptr
                                 \<and>  (atcbContextGet o tcbArch) tcb ARM_H.msgInfoRegister = msginfo)
                        (ksCurThread s) s)
     (UNIV \<inter> {s. cptr_' s = cptr} \<inter> {s. msgInfo_' s = msginfo}) []
     (fastpaths SysCall) (Call fastpath_call_'proc)"
proof -
    have [simp]: "scast Kernel_C.tcbCaller = tcbCallerSlot"
     by (simp add:Kernel_C.tcbCaller_def tcbCallerSlot_def)
    have [simp]: "scast Kernel_C.tcbVTable = tcbVTableSlot"
     by (simp add:Kernel_C.tcbVTable_def tcbVTableSlot_def)

    have tcbs_of_cte_wp_at_vtable:
      "\<And>s tcb ptr. tcbs_of s ptr = Some tcb \<Longrightarrow>
      cte_wp_at' \<top> (ptr + 0x10 * tcbVTableSlot) s"
    apply (clarsimp simp:tcbs_of_def cte_at'_obj_at'
      split:if_splits)
    apply (drule_tac x = "0x10 * tcbVTableSlot" in bspec)
     apply (simp add:tcb_cte_cases_def tcbVTableSlot_def)
    apply simp
    done

  have tcbs_of_cte_wp_at_caller:
    "\<And>s tcb ptr. tcbs_of s ptr = Some tcb \<Longrightarrow>
    cte_wp_at' \<top> (ptr + 0x10 * tcbCallerSlot) s"
    apply (clarsimp simp:tcbs_of_def cte_at'_obj_at'
      split:if_splits)
    apply (drule_tac x = "0x10 * tcbCallerSlot" in bspec)
     apply (simp add:tcb_cte_cases_def tcbCallerSlot_def)
    apply simp
    done

  have tcbs_of_aligned':
    "\<And>s ptr tcb. \<lbrakk>tcbs_of s ptr = Some tcb;pspace_aligned' s\<rbrakk> \<Longrightarrow> is_aligned ptr tcbBlockSizeBits"
    apply (clarsimp simp:tcbs_of_def obj_at'_def split:if_splits)
    apply (drule pspace_alignedD')
    apply simp+
    apply (simp add:projectKO_opt_tcb objBitsKO_def
      split: Structures_H.kernel_object.splits)
    done

  (* FIXME indentation is wonky in this proof, fix will come in a future patch, hopefully when
     automatic indentation is improved *)
  show ?thesis
  supply if_cong[cong] option.case_cong[cong]
  apply (cinit lift: cptr_' msgInfo_')
     apply (simp add: catch_liftE_bindE unlessE_throw_catch_If
                      unifyFailure_catch_If catch_liftE
                      getMessageInfo_def alternative_bind
                cong: if_cong call_ignore_cong del: Collect_const)
     apply (rule ccorres_pre_getCurThread)
     apply (rename_tac curThread)
     apply (rule ccorres_symb_exec_l3[OF _ user_getreg_inv' _ empty_fail_user_getreg])+
       apply (rename_tac msginfo' cptr')
       apply (rule_tac P="msginfo' = msginfo \<and> cptr' = cptr" in ccorres_gen_asm)
       apply (simp del: Collect_const cong: call_ignore_cong)
       apply (simp only: )
       apply (csymbr, csymbr)
       apply (rule ccorres_rhs_assoc2)
       apply (rule_tac r'="\<lambda>ft ft'. (ft' = scast seL4_Fault_NullFault) = (ft = None)"
                 and xf'="ret__unsigned_'" in ccorres_split_nothrow)
           apply (rule_tac P="cur_tcb' and (\<lambda>s. curThread = ksCurThread s)"
                     in ccorres_from_vcg[where P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: cur_tcb'_def rf_sr_ksCurThread)
           apply (drule(1) obj_at_cslift_tcb, clarsimp)
           apply (clarsimp simp: typ_heap_simps' ctcb_relation_def cfault_rel_def)
           apply (rule rev_bexI, erule threadGet_eq)
           apply (clarsimp simp: seL4_Fault_lift_def Let_def split: if_split_asm)
          apply ceqv
         apply csymbr
         apply csymbr
         apply (simp del: Collect_const cong: call_ignore_cong)
       apply (rule ccorres_Cond_rhs_Seq)
          apply (rule ccorres_alternative2)
          apply (rule ccorres_split_throws)
           apply (fold dc_def)[1]
           apply (rule ccorres_call_hSkip)
             apply (rule slowpath_ccorres)
            apply simp
           apply simp
          apply (vcg exspec=slowpath_noreturn_spec)
         apply (rule ccorres_alternative1)
         apply (rule ccorres_if_lhs[rotated])
          apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
          apply simp
         apply (simp del: Collect_const cong: call_ignore_cong)
         apply (elim conjE)
       apply (rule ccorres_abstract_ksCurThread, ceqv)
       apply (simp add: getThreadCSpaceRoot_def locateSlot_conv
                   del: Collect_const cong: call_ignore_cong)
       apply (rule ccorres_pre_getCTE2)
       apply (rule ccorres_move_array_assertion_tcb_ctes
                   ccorres_move_c_guard_tcb_ctes2
                   ccorres_move_const_guard
                   ccorres_rhs_assoc)+
       apply (simp only: )
       apply (ctac add: lookup_fp_ccorres)
         apply (rename_tac luRet ep_cap)
         apply (rule ccorres_abstract_ksCurThread, ceqv)
         apply (rule ccorres_move_array_assertion_tcb_ctes
             | simp del: Collect_const cong: call_ignore_cong)+
         apply (csymbr, csymbr)
         apply (simp add: ccap_relation_case_sum_Null_endpoint
                          of_bl_from_bool from_bool_0
                     del: Collect_const cong: call_ignore_cong)
         apply (rule ccorres_Cond_rhs_Seq)
          apply (simp add: from_bool_0 if_1_0_0 cong: if_cong)
          apply (rule ccorres_cond_true_seq)
          apply (rule ccorres_split_throws)
           apply (fold dc_def)[1]
           apply (rule ccorres_call_hSkip)
             apply (rule slowpath_ccorres, simp+)
          apply (vcg exspec=slowpath_noreturn_spec)
         apply (rule ccorres_rhs_assoc)+
         apply csymbr+
         apply (simp add: if_1_0_0 isRight_case_sum
                     del: Collect_const cong: call_ignore_cong)
         apply (elim conjE)
         apply (frule(1) cap_get_tag_isCap[THEN iffD2])
         apply (simp add: ccap_relation_ep_helpers from_bool_0
                     del: Collect_const cong: call_ignore_cong)
         apply (rule ccorres_Cond_rhs_Seq)
          apply simp
          apply (rule ccorres_split_throws)
           apply (fold dc_def)[1]
           apply (rule ccorres_call_hSkip)
             apply (rule slowpath_ccorres, simp+)
          apply (vcg exspec=slowpath_noreturn_spec)
         apply (simp del: Collect_const cong: call_ignore_cong)
         apply (csymbr, csymbr)
         apply (simp add: ccap_relation_ep_helpers
                     del: Collect_const cong: call_ignore_cong)
         apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
         apply (rule_tac xf'="\<lambda>s. (dest_' s, ret__unsigned_' s)"
                      and r'="\<lambda>ep v. snd v = scast EPState_Recv = isRecvEP ep
                               \<and> (isRecvEP ep \<longrightarrow> epQueue ep \<noteq> []
                                          \<and> fst v = tcb_ptr_to_ctcb_ptr (hd (epQueue ep)))"
                     in ccorres_split_nothrow)
             apply (rule ccorres_add_return2)
             apply (rule ccorres_pre_getEndpoint, rename_tac ep)
             apply (rule_tac P="ko_at' ep (capEPPtr (theRight luRet)) and valid_objs'"
                          in ccorres_from_vcg[where P'=UNIV])
             apply (rule allI, rule conseqPre, vcg)
             apply (clarsimp simp: return_def)
             apply (erule cmap_relationE1[OF cmap_relation_ep], erule ko_at_projectKO_opt)
             apply (frule(1) ko_at_valid_ep')
             apply (clarsimp simp: typ_heap_simps')
             apply (simp add: cendpoint_relation_def Let_def isRecvEP_def
                              endpoint_state_defs valid_ep'_def
                       split: endpoint.split_asm)
             apply (clarsimp simp: tcb_queue_relation'_def neq_Nil_conv)
            apply (rule ceqv_tuple2)
             apply ceqv
            apply ceqv
           apply (rename_tac send_ep send_ep_c)
           apply (rule_tac P="ko_at' send_ep (capEPPtr (theRight luRet))
                                and valid_objs'" in ccorres_cross_over_guard)
           apply (simp del: Collect_const cong: call_ignore_cong)
           apply (rule ccorres_Cond_rhs_Seq)
            apply simp
            apply (rule ccorres_split_throws)
             apply (fold dc_def)[1]
             apply (rule ccorres_call_hSkip)
               apply (rule slowpath_ccorres, simp+)
            apply (vcg exspec=slowpath_noreturn_spec)
           apply (simp add: getThreadVSpaceRoot_def locateSlot_conv
                       del: Collect_const cong: call_ignore_cong)
           apply (rule ccorres_move_c_guard_tcb_ctes2
                       ccorres_move_array_assertion_tcb_ctes
                       ccorres_move_const_guard)+
           apply (rule_tac var="newVTable_'" and var_update="newVTable_'_update"
                        in getCTE_h_val_ccorres_split[where P=\<top>])
             apply simp
            apply ceqv
           apply (rename_tac pd_cap pd_cap_c)
           apply (rule ccorres_symb_exec_r)
             apply (rule_tac xf'=ret__unsigned_' in ccorres_abstract, ceqv)
             apply (rename_tac pd_cap_c_ptr_maybe)
             apply csymbr+
             apply (simp add: isValidVTableRoot_conv from_bool_0
                         del: Collect_const cong: call_ignore_cong)
             apply (rule ccorres_Cond_rhs_Seq)
              apply simp
              apply (rule ccorres_split_throws)
               apply (fold dc_def)[1]
               apply (rule ccorres_call_hSkip)
                 apply (rule slowpath_ccorres, simp+)
              apply (vcg exspec=slowpath_noreturn_spec)
             apply (simp del: Collect_const cong: call_ignore_cong)
             apply (drule isValidVTableRootD)
             apply (rule_tac P="pd_cap_c_ptr_maybe = capUntypedPtr (cteCap pd_cap)"
                         in ccorres_gen_asm2)
             apply (simp add: ccap_relation_pd_helper ptr_add_assertion_positive
                         del: Collect_const cong: call_ignore_cong)
             apply (rule ccorres_move_array_assertion_pd
                    | (rule ccorres_flip_Guard ccorres_flip_Guard2,
                       rule ccorres_move_array_assertion_pd)
                    |  rule ccorres_flip_Guard2, rule ccorres_Guard_True_Seq)+
             apply (rule stored_hw_asid_get_ccorres_split[where P=\<top>], ceqv)
             apply (rule ccorres_abstract_ksCurThread, ceqv)
             apply (rename_tac ksCurThread_x)
               apply (ctac add: getCurDomain_maxDom_ccorres_dom_')
                 apply (rename_tac curDom curDom')
                 apply (rule ccorres_move_c_guard_tcb ccorres_move_const_guard)+
                 apply (simp add: prio_and_dom_limit_helpers del: Collect_const)
                 apply (rule ccorres_pre_threadGet)
                 apply (rule ccorres_pre_threadGet)
                 apply (rename_tac curPrio destPrio)
                 (* use isHighestPrio on the left, but entire if condition on the right *)
                 apply (rule ccorres_rhs_assoc2)
                 (* we can do this with just knowledge from abstract and state relation,
                    which avoids some False schematic instantiation on the C side *)
                 apply (rule_tac xf'=ret__int_'
                           and r'="\<lambda>hi rv'. rv' = from_bool (\<not> (curPrio \<le> destPrio \<or> hi))"
                           and P'=UNIV in ccorres_split_nothrow)
                     apply (rule ccorres_guard_impR)
                      apply (simp add: from_bool_eq_if from_bool_eq_if' from_bool_0 if_1_0_0
                                        ccorres_IF_True del: Collect_const)
                      (* but as a result, we have to duplicate some info to the C side  *)
                      apply (rule_tac P="obj_at' ((=) curPrio \<circ> tcbPriority) curThread
                                           and obj_at' ((=) destPrio \<circ> tcbPriority)
                                                       (hd (epQueue send_ep))
                                           and (\<lambda>s. ksCurThread s = curThread)
                                           and (\<lambda>s. ksCurThread s = ksCurThread_x)"
                                in ccorres_cross_over_guard)
                      apply (rule_tac xf'=ret__int_' and val="from_bool (destPrio < curPrio)"
                                and R="obj_at' ((=) curPrio \<circ> tcbPriority) curThread
                                           and obj_at' ((=) destPrio \<circ> tcbPriority)
                                             (hd (epQueue send_ep))
                                           and (\<lambda>s. ksCurThread s = curThread)
                                           and (\<lambda>s. ksCurThread s = ksCurThread_x)"
                                and R'=UNIV in ccorres_symb_exec_r_known_rv)
                        apply (rule conseqPre, vcg)
                        apply clarsimp
                        apply (simp add: from_bool_eq_if from_bool_eq_if' from_bool_0 if_1_0_0
                                          ccorres_IF_True del: Collect_const)
                        apply (drule(1) obj_at_cslift_tcb)+
                        apply (clarsimp simp: typ_heap_simps' rf_sr_ksCurThread)
                        apply (simp add: ctcb_relation_unat_tcbPriority_C
                                          word_less_nat_alt linorder_not_le)
                        apply ceqv
                       apply (simp add: Collect_const_mem from_bool_eq_if from_bool_eq_if' from_bool_0 if_1_0_0 ccorres_IF_True del: Collect_const)
                       apply (simp add: if_1_0_0 ccap_relation_ep_helpers from_bool_0 word_le_not_less
                                    del: Collect_const cong: call_ignore_cong)

                       apply (rule ccorres_Cond_rhs)
                        apply (simp add: bindE_assoc del: Collect_const)
                        apply (rule ccorres_Guard_Seq)
                        apply (rule ccorres_add_return2)
                        apply (ctac add: isHighestPrio_ccorres)
                        apply (simp add: Collect_const_mem from_bool_eq_if from_bool_eq_if' from_bool_0 if_1_0_0 ccorres_IF_True del: Collect_const)
                        apply (clarsimp simp: to_bool_def)
                        apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
                        apply clarsimp
                        apply (rule conseqPre, vcg)
                        apply (clarsimp simp: from_bool_eq_if from_bool_eq_if' from_bool_0 if_1_0_0)
                        apply (clarsimp simp: return_def)
                        apply (rule wp_post_taut)
                        apply (vcg exspec=isHighestPrio_modifies)
                       apply (simp add: Collect_const_mem from_bool_eq_if from_bool_eq_if' from_bool_0 if_1_0_0 ccorres_IF_True del: Collect_const)
                       apply (rule_tac P=\<top> and P'="{s. ret__int_' s = 0}" in ccorres_from_vcg)
                       apply (clarsimp simp: isHighestPrio_def' simpler_gets_def)
                       apply (rule conseqPre, vcg)
                       apply clarsimp
                      apply clarsimp
                      apply vcg
                     apply (simp add: Collect_const_mem from_bool_eq_if from_bool_eq_if' from_bool_0 if_1_0_0 ccorres_IF_True del: Collect_const)
                     apply clarsimp
                     apply (drule(1) obj_at_cslift_tcb)+
                     apply (clarsimp simp: typ_heap_simps' rf_sr_ksCurThread)
                     apply (simp add: ctcb_relation_unat_tcbPriority_C ctcb_relation_tcbPriority
                                       word_less_nat_alt linorder_not_le)
                    apply ceqv
                   apply (clarsimp simp del: Collect_const)
                   apply (rule ccorres_Cond_rhs_Seq)
                    apply (simp add: bindE_assoc from_bool_0 catch_throwError del: Collect_const)
                    apply (rule ccorres_split_throws)
                     apply (fold dc_def)[1]
                     apply (rule ccorres_call_hSkip)
                       apply (rule slowpath_ccorres, simp+)
                    apply (vcg exspec=slowpath_noreturn_spec)
                   apply (simp del: Collect_const add: from_bool_0 cong: call_ignore_cong)

                   apply (rule ccorres_rhs_assoc2)
                   apply (rule ccorres_rhs_assoc2)
                   apply (rule_tac val="from_bool (\<not> (capEPCanGrant (theRight luRet)
                                                       \<or> capEPCanGrantReply (theRight luRet)))"
                            and xf'=ret__int_' and R=\<top> and R'=UNIV
                            in ccorres_symb_exec_r_known_rv)
                      apply (clarsimp, rule conseqPre, vcg)
                      apply (fastforce simp: ccap_relation_ep_helpers from_bool_0 from_bool_eq_if')
                     apply ceqv

               apply (rule ccorres_Cond_rhs_Seq)
                apply simp
                apply (rule ccorres_split_throws)
                 apply (fold dc_def)[1]
                 apply (rule ccorres_call_hSkip)
                   apply (rule slowpath_ccorres, simp+)
                apply (vcg exspec=slowpath_noreturn_spec)
                 apply (simp add: ccap_relation_pd_helper cap_get_tag_isCap_ArchObject2
                         del: Collect_const Word_Lib.ptr_add_def cong: call_ignore_cong)
                 apply csymbr
                 apply (rule ccorres_symb_exec_l3[OF _ gets_inv _ empty_fail_gets])
                  apply (rename_tac asidMap)
                  apply (rule_tac P="asid_map_pd_to_hwasids asidMap (capPDBasePtr (capCap ((cteCap pd_cap))))
                                        = set_option (pde_stored_asid shw_asid)" in ccorres_gen_asm)
                  apply (simp del: Collect_const cong: call_ignore_cong)
                  apply (rule ccorres_Cond_rhs_Seq)
                   apply (simp add: pde_stored_asid_def asid_map_pd_to_hwasids_def)
                   apply (rule ccorres_split_throws)
                    apply (fold dc_def)[1]
                    apply (rule ccorres_call_hSkip)
                      apply (rule slowpath_ccorres, simp+)
                   apply (vcg exspec=slowpath_noreturn_spec)
                  apply (simp add: pde_stored_asid_def asid_map_pd_to_hwasids_def
                                   to_bool_def
                              del: Collect_const cong: call_ignore_cong)
                  apply (rule ccorres_move_c_guard_tcb ccorres_move_const_guard)+
                   apply (rule ccorres_pre_threadGet)
                    apply (rename_tac destDom)
                    apply (rule_tac C'="{s. destDom \<noteq> curDom}"
                              and Q="obj_at' ((=) destDom \<circ> tcbDomain) (hd (epQueue send_ep))
                                       and (\<lambda>s. ksCurDomain s = curDom \<and> curDom \<le> maxDomain
                                                \<and> destDom \<le> maxDomain)"
                              and Q'=UNIV in ccorres_rewrite_cond_sr_Seq)
                     apply (simp add: Collect_const_mem from_bool_eq_if from_bool_eq_if' from_bool_0 if_1_0_0 ccorres_IF_True del: Collect_const)
                     apply clarsimp
                      apply (drule(1) obj_at_cslift_tcb)+
                      apply (clarsimp simp: typ_heap_simps' rf_sr_ksCurDomain)
                      apply (solves \<open>clarsimp simp: maxDomain_def numDomains_def maxDom_def\<close>)
                    apply (rule ccorres_seq_cond_raise[THEN iffD2])
                    apply (rule_tac R=\<top> in ccorres_cond2', blast)
                     apply (rule ccorres_split_throws)
                      apply (fold dc_def)[1]
                      apply (rule ccorres_call_hSkip)
                        apply (rule slowpath_ccorres, simp+)
                     apply (vcg exspec=slowpath_noreturn_spec)
                    apply (simp del: Collect_const cong: call_ignore_cong)

                    apply (rule ccorres_rhs_assoc2)
                    apply (rule_tac xf'=xfdc and r'=dc in ccorres_split_nothrow)
                        apply (simp only: ucast_id tl_drop_1 One_nat_def scast_0)
                        apply (rule fastpath_dequeue_ccorres)
                        apply simp
                       apply ceqv
                      apply csymbr
                      apply csymbr
                      apply (rule_tac xf'=xfdc and r'=dc in ccorres_split_nothrow)
                          apply (rule_tac P="cur_tcb' and (\<lambda>s. ksCurThread s = curThread)"
                                       in ccorres_from_vcg[where P'=UNIV])
                          apply (rule allI, rule conseqPre, vcg)
                          apply (clarsimp simp: cur_tcb'_def rf_sr_ksCurThread)
                          apply (drule(1) obj_at_cslift_tcb)
                          apply (clarsimp simp: typ_heap_simps')
                          apply (rule rev_bexI, erule threadSet_eq)
                          apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
                          apply (rule conjI)
                           apply (clarsimp simp: cpspace_relation_def typ_heap_simps'
                                                 update_tcb_map_tos map_to_tcbs_upd)
                           apply (subst map_to_ctes_upd_tcb_no_ctes, assumption)
                            apply (rule ball_tcb_cte_casesI, simp_all)[1]
                           apply (simp add: cep_relations_drop_fun_upd)
                           apply (erule cmap_relation_updI, erule ko_at_projectKO_opt)
                            apply (simp add: ctcb_relation_def cthread_state_relation_def)
                           apply simp
                          apply (rule conjI, erule cready_queues_relation_not_queue_ptrs)
                            apply (rule ext, simp split: if_split add: typ_heap_simps')
                           apply (rule ext, simp split: if_split add: typ_heap_simps')
                          apply (simp add: carch_state_relation_def cmachine_state_relation_def
                                           typ_heap_simps' map_comp_update projectKO_opt_tcb
                                           cvariable_relation_upd_const ko_at_projectKO_opt)
                         apply ceqv
                        apply (rule ccorres_abstract_ksCurThread, ceqv)
                        apply (rule ccorres_move_c_guard_tcb_ctes
                                    ccorres_move_array_assertion_tcb_ctes
                                    ccorres_move_const_guard)+
                        apply (simp add: getThreadReplySlot_def getThreadCallerSlot_def
                                         locateSlot_conv
                                    del: Collect_const cong: call_ignore_cong)
                        apply (rule ccorres_symb_exec_r)
                          apply (rule_tac xf'="replySlot_'" in ccorres_abstract, ceqv)
                          apply (rename_tac replySlot,
                                 rule_tac P="replySlot = cte_Ptr (curThread
                                               + (tcbReplySlot << cte_level_bits))"
                                    in ccorres_gen_asm2)
                          apply (rule ccorres_move_const_guard
                                      ccorres_move_array_assertion_tcb_ctes
                                      ccorres_move_c_guard_tcb_ctes)+
                          apply csymbr
                          apply (simp add: cteInsert_def bind_assoc dc_def[symmetric]
                                      del: Collect_const cong: call_ignore_cong)
                          apply (rule ccorres_pre_getCTE2, rename_tac curThreadReplyCTE)
                          apply (simp only: getThreadState_def)
                          apply (rule ccorres_assert2)
                          apply (rule ccorres_pre_threadGet, rename_tac destState)
                          apply (rule_tac P="isReceive destState" in ccorres_gen_asm)
                          apply (rule ccorres_pre_getCTE2, rename_tac curThreadReplyCTE2)
                          apply (rule ccorres_pre_getCTE2, rename_tac destCallerCTE)
                          apply (rule ccorres_assert2)+
                          apply (rule_tac xf'=ret__unsigned_'
                                   and val="from_bool (blockingIPCCanGrant destState)"
                                   and R="st_tcb_at' ((=) destState) (hd (epQueue send_ep))
                                          and K(isReceive destState)"
                                   and R'=UNIV in ccorres_symb_exec_r_known_rv)
                             apply (clarsimp, rule conseqPre, vcg)
                             apply (clarsimp simp: typ_heap_simps' st_tcb_at_h_t_valid
                                                   pred_tcb_at'_def)
                             apply (drule (1) obj_at_cslift_tcb)
                             apply clarsimp
                             apply (drule ctcb_relation_blockingIPCCanGrantD, blast)
                             apply fastforce
                            apply ceqv
                           apply csymbr

                          apply (rule_tac P="curThreadReplyCTE2 = curThreadReplyCTE"
                                          in ccorres_gen_asm)
                          apply (rule ccorres_move_c_guard_tcb_ctes2)
                          apply (ctac add: cap_reply_cap_ptr_new_np_updateCap_ccorres)
                            apply (rule_tac xf'=xfdc and r'=dc in ccorres_split_nothrow)
                                apply (rule_tac P="cte_wp_at' (\<lambda>cte. cteMDBNode cte = nullMDBNode)
                                                     (hd (epQueue send_ep)
                                                           + (tcbCallerSlot << cte_level_bits))
                                               and cte_wp_at' ((=) curThreadReplyCTE) (curThread
                                                           + (tcbReplySlot << cte_level_bits))
                                               and tcb_at' curThread and (no_0 o ctes_of)
                                               and tcb_at' (hd (epQueue send_ep))"
                                             in ccorres_from_vcg[where P'=UNIV])
                                apply (rule allI, rule conseqPre, vcg)
                                apply (clarsimp simp: cte_wp_at_ctes_of size_of_def
                                                      tcb_cnode_index_defs tcbCallerSlot_def
                                                      tcbReplySlot_def cte_level_bits_def
                                                      valid_mdb'_def valid_mdb_ctes_def)
                                apply (subst aligned_add_aligned, erule tcb_aligned',
                                       simp add: is_aligned_def, simp add: objBits_defs, simp)
                                apply (rule_tac x="hd (epQueue send_ep) + v" for v
                                          in cmap_relationE1[OF cmap_relation_cte], assumption+)
                                apply (clarsimp simp: typ_heap_simps' updateMDB_def Let_def)
                                apply (subst if_not_P)
                                 apply clarsimp
                                apply (simp add: split_def)
                                apply (rule getCTE_setCTE_rf_sr, simp_all)[1]
                                apply (case_tac destCallerCTE, case_tac curThreadReplyCTE,
                                       case_tac "cteMDBNode curThreadReplyCTE")
                                apply (clarsimp simp add: ccte_relation_eq_ccap_relation)
                                apply (clarsimp simp: nullMDBNode_def revokable'_def)
                               apply ceqv
                              apply (rule ccorres_move_c_guard_cte)
                              apply (rule_tac xf'=xfdc and r'=dc in ccorres_split_nothrow)
                                  apply (rule_tac P="cte_at' (hd (epQueue send_ep)
                                                               + (tcbCallerSlot << cte_level_bits))
                                                     and cte_wp_at' ((=) curThreadReplyCTE) (curThread
                                                               + (tcbReplySlot << cte_level_bits))
                                                     and tcb_at' (hd (epQueue send_ep))
                                                     and (no_0 o ctes_of)"
                                                 in ccorres_from_vcg[where P'=UNIV])
                                  apply (rule allI, rule conseqPre, vcg)
                                  apply (clarsimp simp: cte_wp_at_ctes_of size_of_def
                                                        tcb_cnode_index_defs tcbCallerSlot_def
                                                        tcbReplySlot_def cte_level_bits_def)
                                  apply (subst aligned_add_aligned, erule tcb_aligned',
                                         simp add: is_aligned_def, simp add: objBits_defs, simp)
                                  apply (rule_tac x="curThread + 0x20" in cmap_relationE1[OF cmap_relation_cte],
                                         assumption+)
                                  apply (clarsimp simp: typ_heap_simps' updateMDB_def Let_def)
                                  apply (subst if_not_P)
                                   apply clarsimp
                                  apply (simp add: split_def)
                                  apply (rule getCTE_setCTE_rf_sr, simp_all)[1]
                                  apply (simp add: ccte_relation_eq_ccap_relation)
                                  apply (case_tac curThreadReplyCTE,
                                         case_tac "cteMDBNode curThreadReplyCTE",
                                         simp)
                                 apply ceqv
                                apply (simp add: updateMDB_def
                                  del: Collect_const cong: call_ignore_cong)
                                apply (rule ccorres_split_nothrow_dc)
                                   apply (ctac add: fastpath_copy_mrs_ccorres[unfolded forM_x_def])
                                  apply (rule ccorres_move_c_guard_tcb)
                                  apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
                                      apply (simp add: setThreadState_runnable_simp)
                                      apply (rule_tac P=\<top> in threadSet_ccorres_lemma2, vcg)
                                      apply (clarsimp simp: typ_heap_simps' rf_sr_def
                                                            cstate_relation_def Let_def)
                                      apply (rule conjI)
                                       apply (clarsimp simp: cpspace_relation_def typ_heap_simps'
                                                             update_tcb_map_tos map_to_tcbs_upd)
                                       apply (subst map_to_ctes_upd_tcb_no_ctes, assumption)
                                        apply (rule ball_tcb_cte_casesI, simp_all)[1]
                                       apply (simp add: cep_relations_drop_fun_upd)
                                       apply (erule cmap_relation_updI, erule ko_at_projectKO_opt)
                                        apply (simp add: ctcb_relation_def cthread_state_relation_def)
                                       apply simp
                                      apply (rule conjI, erule cready_queues_relation_not_queue_ptrs)
                                        apply (rule ext, simp split: if_split)
                                       apply (rule ext, simp split: if_split)
                                      apply (simp add: carch_state_relation_def cmachine_state_relation_def
                                                       typ_heap_simps' map_comp_update projectKO_opt_tcb
                                                       cvariable_relation_upd_const ko_at_projectKO_opt)
                                     apply ceqv
                                    apply (simp only: bind_assoc[symmetric])
                                    apply (rule ccorres_stateAssert_after)
                                     apply (rule ccorres_split_nothrow_novcg_dc)
                                        apply simp
                                        apply (rule ccorres_call,
                                               rule_tac v=shw_asid and pd="capUntypedPtr (cteCap pd_cap)"
                                                     in switchToThread_fp_ccorres,
                                               simp+)[1]
                                       apply (rule_tac P="\<lambda>s. ksCurThread s = hd (epQueue send_ep)"
                                                    in ccorres_cross_over_guard)
                                       apply csymbr
                                       apply csymbr
                                       apply (rule ccorres_call_hSkip)
                                         apply (fold dc_def)[1]
                                         apply (rule fastpath_restore_ccorres)
                                        apply simp
                                       apply simp
                                      apply (simp add: setCurThread_def)
                                      apply wp
                                      apply (rule_tac P=\<top> in hoare_triv, simp)
                                     apply simp
                                    apply (simp add: imp_conjL rf_sr_ksCurThread del: all_imp_to_ex)
                                    apply (clarsimp simp: ccap_relation_ep_helpers guard_is_UNIV_def
                                                          mi_from_H_def)
                                   apply (simp add: pd_has_hwasid_def)
                                   apply (wp sts_valid_objs')
                                  apply (simp del: Collect_const)
                                  apply (vcg exspec=thread_state_ptr_set_tsType_np_modifies)
                                 apply (simp add: pred_conj_def)
                                 apply (rule mapM_x_wp'[OF hoare_weaken_pre])
                                  apply wp
                                 apply clarsimp
                                apply simp

                                apply (vcg exspec=fastpath_copy_mrs_modifies)
                               apply (simp add: valid_tcb_state'_def)
                               apply wp
                               apply (wp updateMDB_weak_cte_wp_at)
                              apply simp
                              apply (vcg exspec=mdb_node_ptr_mset_mdbNext_mdbRevocable_mdbFirstBadged_modifies)
                             apply (simp add: o_def)
                             apply (wp | simp
                                        | wp (once) updateMDB_weak_cte_wp_at
                                        | wp (once) updateMDB_cte_wp_at_other)+
                            apply (vcg exspec=mdb_node_ptr_set_mdbPrev_np_modifies)
                           apply (wp updateCap_cte_wp_at_cteMDBNode
                                     updateCap_cte_wp_at_cases
                                     updateCap_no_0 | simp)+

                          apply (vcg exspec=cap_reply_cap_ptr_new_np_modifies)

                         (* imp_disjL causes duplication of conclusions of implications involving
                            disjunctions which chokes the vcg; we want fewer implications at the
                            expense of disjunctions on asm side  *)
                         supply imp_disjL[simp del]
                         supply imp_disjL[symmetric, simp]
                         apply clarsimp
                         apply (vcg exspec=thread_state_ptr_get_blockingIPCCanGrant_modifies)
                         apply (simp add: word_sle_def)
                         apply vcg

                        apply (rule conseqPre, vcg, clarsimp)
                       apply (simp add: cte_level_bits_def field_simps shiftl_t2n
                                        ctes_of_Some_cte_wp_at
                                   del: all_imp_to_ex cong: imp_cong conj_cong)
                       apply (wp hoare_vcg_all_lift threadSet_ctes_of
                                 hoare_vcg_imp_lift' threadSet_valid_objs'
                                 threadSet_st_tcb_at_state threadSet_cte_wp_at'
                                 threadSet_cur
                               | simp add: cur_tcb'_def[symmetric]
                               | strengthen not_obj_at'_strengthen)+

                      apply (vcg exspec=thread_state_ptr_set_tsType_np_modifies)
                       apply (wp hoare_vcg_all_lift threadSet_ctes_of
                                 hoare_vcg_imp_lift' threadSet_valid_objs'
                                 threadSet_st_tcb_at_state threadSet_cte_wp_at'
                                 threadSet_cur
                               | simp add: cur_tcb'_def[symmetric])+
                     apply (simp add: valid_tcb'_def tcb_cte_cases_def
                                      valid_tcb_state'_def)
                     apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift
                               set_ep_valid_objs'
                               setObject_no_0_obj'[where 'a=endpoint, folded setEndpoint_def]
                               | strengthen not_obj_at'_strengthen)+
                      apply (rule_tac Q="\<lambda>_ s. hd (epQueue send_ep) \<noteq> curThread
                                              \<and> pred_tcb_at' itcbState ((=) (tcbState xa)) (hd (epQueue send_ep)) s"
                               in hoare_post_imp)
                       apply fastforce
                      apply wp+
                    apply (simp del: Collect_const)
                    apply (vcg exspec=endpoint_ptr_mset_epQueue_tail_state_modifies
                             exspec=endpoint_ptr_set_epQueue_head_np_modifies)
                   apply simp
                  apply wp[1]
                 apply clarsimp
                 apply (vcg exspec=cap_endpoint_cap_get_capCanGrant_modifies
                            exspec=cap_endpoint_cap_get_capCanGrantReply_modifies)
                  apply clarsimp
                  (* throw away results of isHighestPrio and the fastfail shortcut *)
                  apply (wp (once) hoare_drop_imp, wp)
                  apply (wp (once) hoare_drop_imp, wp)
                 apply simp
                 apply (vcg exspec=isHighestPrio_modifies)
                apply clarsimp
                apply (wp cd_wp)
           apply clarsimp
           apply vcg
            apply clarsimp
            apply (vcg exspec=cap_page_directory_cap_get_capPDBasePtr_spec2)
           apply clarsimp
           apply (rule conseqPre,
                  vcg exspec=cap_page_directory_cap_get_capPDBasePtr_spec2,
                  clarsimp)
                apply wp[1]
               apply (simp del: Collect_const)
          apply (rule getEndpoint_wp)
         apply (simp del: Collect_const)
         apply (vcg exspec=endpoint_ptr_get_epQueue_head_modifies
                    exspec=endpoint_ptr_get_state_modifies)
        apply (simp add: if_1_0_0 getSlotCap_def)
        apply (rule valid_isRight_theRight_split)
        apply simp
        apply (wp getCTE_wp')
        apply (rule validE_R_abstract_rv)
        apply wp
       apply (simp add: if_1_0_0 del: Collect_const)
       apply (vcg exspec=lookup_fp_modifies)
      apply simp
      apply (rule threadGet_wp)
     apply (simp del: Collect_const)
     apply clarsimp
     apply vcg
    apply simp
    apply (rule user_getreg_wp)
   apply simp
   apply (rule user_getreg_wp)
   apply (rule conjI)
   apply (clarsimp simp: obj_at_tcbs_of ct_in_state'_def st_tcb_at_tcbs_of
                         invs_cur' invs_valid_objs' ctes_of_valid'
                         word_sle_def
                         invs'_bitmapQ_no_L1_orphans)
   apply (frule cte_wp_at_valid_objs_valid_cap', clarsimp)
   apply (clarsimp simp: isCap_simps valid_cap'_def maskCapRights_def)
   apply (clarsimp simp add:obj_at'_def projectKO_eq)
   apply (frule invs_valid_objs')
   apply (erule valid_objsE')
    apply simp
   apply (clarsimp simp:projectKO_opt_ep split:Structures_H.kernel_object.splits)
   apply (clarsimp simp:isRecvEP_def valid_obj'_def valid_ep'_def
     split:Structures_H.endpoint.split_asm)
   apply (erule not_NilE)

   (* sort out destination being queued in the endpoint, hence not the current thread *)
   apply (subgoal_tac "st_tcb_at' isBlockedOnReceive x s")
    prefer 2
    apply (rule_tac ts="x # xs'" and epptr=v0 in recv_ep_queued_st_tcb_at'
           ; clarsimp simp: obj_at'_def projectKOs invs_sym')
   apply (subgoal_tac "x \<noteq> ksCurThread s")
    prefer 2
    apply (fastforce simp: st_tcb_at_tcbs_of isBlockedOnReceive_def)

   apply (drule_tac x = x in bspec)
    apply fastforce
   apply (clarsimp simp:obj_at_tcbs_of)
   apply (frule_tac ptr2 = x in tcbs_of_aligned')
    apply (simp add:invs_pspace_aligned')
   apply (frule_tac ptr2 = x in tcbs_of_cte_wp_at_vtable)
   apply (clarsimp simp:size_of_def field_simps word_sless_def word_sle_def
      dest!:ptr_val_tcb_ptr_mask2[unfolded mask_def])
   apply (frule_tac p="x + offs" for offs in ctes_of_valid', clarsimp)
   apply (clarsimp simp: isCap_simps valid_cap'_def invs_valid_pde_mappings'
                  dest!: isValidVTableRootD)
   apply (clarsimp simp: invs_sym' tcbCallerSlot_def
                         tcbVTableSlot_def tcbReplySlot_def
                         conj_comms tcb_cnode_index_defs field_simps
                         obj_at_tcbs_of)
   apply (clarsimp simp: cte_level_bits_def isValidVTableRoot_def
                         ARM_H.isValidVTableRoot_def cte_wp_at_ctes_of
                         capAligned_def objBits_simps)
   apply (simp cong: conj_cong)
   apply (clarsimp simp add: invs_ksCurDomain_maxDomain')
   apply (rule conjI) (* tcbDomain \<le> maxDomain *)
    apply (drule invs_valid_objs')
    apply (solves \<open>drule_tac t=x in valid_objs'_maxDomain; clarsimp simp: obj_at_tcbs_of\<close>)
   apply clarsimp
   apply (rule conjI) (* isReceive on queued tcb state *)
    apply (fastforce simp: st_tcb_at_tcbs_of isBlockedOnReceive_def isReceive_def)
   apply clarsimp
   apply (rule conjI, fastforce dest!: invs_queues simp: valid_queues_def)
   apply (frule invs_mdb', clarsimp simp: valid_mdb'_def valid_mdb_ctes_def)
   apply (case_tac xb, clarsimp, drule(1) nullcapsD')
   apply (clarsimp simp: pde_stored_asid_def to_bool_def
                         length_msgRegisters word_le_nat_alt[symmetric])
   apply (frule tcb_aligned'[OF obj_at_tcbs_of[THEN iffD2], OF exI, simplified])
   apply (clarsimp simp: objBits_defs)
   apply (safe del: notI disjE)[1]
     apply (rule not_sym, clarsimp)
     apply (drule aligned_sub_aligned[where a="x + 0x10" and b=x for x])
       apply (erule tcbs_of_aligned'[unfolded tcbBlockSizeBits_def, simplified])
       apply (simp add:invs_pspace_aligned')
      apply (simp add: objBits_defs)
     apply (simp add: objBits_defs is_aligned_def dvd_def)
    apply (clarsimp simp:tcbs_of_def obj_at'_def projectKO_opt_tcb
      split:if_splits Structures_H.kernel_object.splits)
    apply (drule pspace_distinctD')
     apply (simp add:invs_pspace_distinct')
    apply (simp add:objBits_simps)
   apply (clarsimp simp: obj_at_tcbs_of split: list.split)
   apply (erule_tac x = v0 in valid_objsE'[OF invs_valid_objs',rotated])
    apply (clarsimp simp: valid_obj'_def valid_ep'_def isRecvEP_def neq_Nil_conv size_of_def
      split: Structures_H.endpoint.split_asm
      cong: list.case_cong)
    apply (simp add:obj_at_tcbs_of)
   apply simp
  apply (clarsimp simp: syscall_from_H_def[split_simps syscall.split]
                        word_sle_def word_sless_def rf_sr_ksCurThread
                        ptr_val_tcb_ptr_mask' size_of_def cte_level_bits_def
                        tcb_cnode_index_defs tcbCTableSlot_def tcbVTableSlot_def
                        tcbReplySlot_def tcbCallerSlot_def
              simp del: Collect_const split del: if_split)
  apply (drule(1) obj_at_cslift_tcb)
  apply (clarsimp simp: ccte_relation_eq_ccap_relation of_bl_from_bool from_bool_0
                        if_1_0_0 ccap_relation_case_sum_Null_endpoint
                        isRight_case_sum typ_heap_simps')
  apply (frule(1) cap_get_tag_isCap[THEN iffD2])
  apply (clarsimp simp: typ_heap_simps' ccap_relation_ep_helpers)
  apply (erule cmap_relationE1[OF cmap_relation_ep],
         erule ko_at_projectKO_opt)
  apply (frule(1) ko_at_valid_ep')
  apply (clarsimp simp: cendpoint_relation_def Let_def
                        isRecvEP_endpoint_case neq_Nil_conv
                        tcb_queue_relation'_def valid_ep'_def
                        mi_from_H_def)
  apply (clarsimp simp: from_bool_0
                        pdBits_def pageBits_def
                        cap_get_tag_isCap_ArchObject2
                        ccap_relation_pd_helper)
  apply (clarsimp simp: isCap_simps pdeBits_def dest!: isValidVTableRootD)
  done
qed

lemma isMasterReplyCap_fp_conv:
  "ccap_relation cap cap' \<Longrightarrow>
    (index (cap_C.words_C cap') 0 && 0x1F = scast cap_reply_cap)
       = (isReplyCap cap \<and> \<not> capReplyMaster cap)"
  apply (rule trans)
   apply (rule_tac m="mask 4" in split_word_eq_on_mask)
  apply (simp add: cap_get_tag_isCap[symmetric])
  apply (rule conj_cong)
   apply (simp add: mask_def word_bw_assocs cap_get_tag_eq_x
                    cap_reply_cap_def split: if_split)
  apply (clarsimp simp: cap_lift_reply_cap cap_to_H_simps
                        isCap_simps
                 elim!: ccap_relationE)
  apply (simp add: mask_def cap_reply_cap_def word_bw_assocs
                   to_bool_def)
  apply (thin_tac "P" for P)
  apply (rule iffI)
   apply (drule_tac f="\<lambda>v. v >> 4" in arg_cong)
   apply (simp add: shiftr_over_and_dist)
  apply (drule_tac f="\<lambda>v. v << 4" in arg_cong)
  apply (simp add: shiftl_over_and_dist shiftr_shiftl1 mask_def
                   word_bw_assocs)
  done

lemma ccap_relation_reply_helper:
  "\<lbrakk> ccap_relation cap cap'; isReplyCap cap \<rbrakk>
     \<Longrightarrow> cap_reply_cap_CL.capTCBPtr_CL (cap_reply_cap_lift cap')
           = ptr_val (tcb_ptr_to_ctcb_ptr (capTCBPtr cap))"
  by (clarsimp simp: cap_get_tag_isCap[symmetric]
                     cap_lift_reply_cap cap_to_H_simps
                     cap_reply_cap_lift_def
              elim!: ccap_relationE)

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

lemmas array_assertion_abs_tcb_ctes_add
    = array_assertion_abs_tcb_ctes_add[where
          tcb="\<lambda>s. Ptr (tcb' s)" for tcb', simplified]

lemmas ccorres_move_array_assertion_tcb_ctes [corres_pre]
    = ccorres_move_array_assertions [OF array_assertion_abs_tcb_ctes(1)[where
          tcb="\<lambda>s. Ptr (tcb' s)" for tcb', simplified]]
      ccorres_move_array_assertions [OF array_assertion_abs_tcb_ctes(2)]
      ccorres_move_Guard_Seq[OF array_assertion_abs_tcb_ctes_add]
      ccorres_move_Guard[OF array_assertion_abs_tcb_ctes_add]

lemmas ccorres_move_c_guard_tcb_ctes3
    = ccorres_move_c_guards  [OF c_guard_abs_tcb_ctes[where
          tcb="\<lambda>s. Ptr (tcb' s)" for tcb', simplified],
       unfolded cte_C_numeral_fold]

lemma fastpath_reply_cap_check_ccorres:
  "ccorres (\<lambda>rv rv'. \<forall>cap. ccap_relation cap ccap
          \<longrightarrow> rv' = from_bool (isReplyCap cap \<and> \<not> capReplyMaster cap)) ret__int_'
      \<top> ({s. cap_' s = ccap}) []
      (return ()) (Call fastpath_reply_cap_check_'proc)"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: extra_sle_sless_unfolds isMasterReplyCap_fp_conv
                        from_bool_def return_def)
  apply (simp split: bool.split if_split)
  done

lemma fastpath_reply_recv_ccorres:
  notes hoare_TrueI[simp]
  shows "ccorres dc xfdc
       (\<lambda>s. invs' s \<and> ct_in_state' ((=) Running) s
               \<and> obj_at' (\<lambda>tcb.  (atcbContextGet o tcbArch) tcb capRegister = cptr
                              \<and>  (atcbContextGet o tcbArch) tcb msgInfoRegister = msginfo)
                     (ksCurThread s) s)
       (UNIV \<inter> {s. cptr_' s = cptr} \<inter> {s. msgInfo_' s = msginfo}) []
       (fastpaths SysReplyRecv) (Call fastpath_reply_recv_'proc)"
  proof -
   have [simp]: "Kernel_C.tcbCaller = scast tcbCallerSlot"
     by (simp add:Kernel_C.tcbCaller_def tcbCallerSlot_def)
   have [simp]: "Kernel_C.tcbVTable = scast tcbVTableSlot"
     by (simp add:Kernel_C.tcbVTable_def tcbVTableSlot_def)

  have tcbs_of_cte_wp_at_vtable:
    "\<And>s tcb ptr. tcbs_of s ptr = Some tcb \<Longrightarrow>
    cte_wp_at' \<top> (ptr + 0x10 * tcbVTableSlot) s"
    apply (clarsimp simp:tcbs_of_def cte_at'_obj_at'
      split:if_splits)
    apply (drule_tac x = "0x10 * tcbVTableSlot" in bspec)
     apply (simp add:tcb_cte_cases_def tcbVTableSlot_def)
    apply simp
    done

  have tcbs_of_cte_wp_at_caller:
    "\<And>s tcb ptr. tcbs_of s ptr = Some tcb \<Longrightarrow>
    cte_wp_at' \<top> (ptr + 0x10 * tcbCallerSlot) s"
    apply (clarsimp simp:tcbs_of_def cte_at'_obj_at'
      split:if_splits)
    apply (drule_tac x = "0x10 * tcbCallerSlot" in bspec)
     apply (simp add:tcb_cte_cases_def tcbCallerSlot_def)
    apply simp
    done

  have tcbs_of_aligned':
    "\<And>s ptr tcb. \<lbrakk>tcbs_of s ptr = Some tcb;pspace_aligned' s\<rbrakk> \<Longrightarrow> is_aligned ptr tcbBlockSizeBits"
    apply (clarsimp simp:tcbs_of_def obj_at'_def split:if_splits)
    apply (drule pspace_alignedD')
    apply simp+
    apply (simp add:projectKO_opt_tcb objBitsKO_def
      split: Structures_H.kernel_object.splits)
    done

  (* FIXME indentation is wonky in this proof, fix will come in a future patch, hopefully when
     automatic indentation is improved *)
  show ?thesis
  using [[goals_limit = 1]]
  supply option.case_cong_weak[cong del]
  supply if_cong[cong]
  apply (cinit lift: cptr_' msgInfo_')
     apply (simp add: catch_liftE_bindE unlessE_throw_catch_If
                      unifyFailure_catch_If catch_liftE
                      getMessageInfo_def alternative_bind
                cong: if_cong call_ignore_cong del: Collect_const)
     apply (rule ccorres_pre_getCurThread)
     apply (rename_tac curThread)
     apply (rule ccorres_symb_exec_l3[OF _ user_getreg_inv' _ empty_fail_user_getreg])+
       apply (rename_tac msginfo' cptr')
       apply (rule_tac P="msginfo' = msginfo \<and> cptr' = cptr" in ccorres_gen_asm)
       apply (simp del: Collect_const cong: call_ignore_cong)
       apply (simp only:)
       apply (csymbr, csymbr)
       apply (rule ccorres_rhs_assoc2)
       apply (rule_tac r'="\<lambda>ft ft'. (ft' = scast seL4_Fault_NullFault) = (ft = None)"
                 and xf'="ret__unsigned_'" in ccorres_split_nothrow)
           apply (rule_tac P="cur_tcb' and (\<lambda>s. curThread = ksCurThread s)"
                     in ccorres_from_vcg[where P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: cur_tcb'_def rf_sr_ksCurThread)
           apply (drule(1) obj_at_cslift_tcb, clarsimp)
           apply (clarsimp simp: typ_heap_simps' ctcb_relation_def cfault_rel_def)
           apply (rule rev_bexI, erule threadGet_eq)
           apply (clarsimp simp: seL4_Fault_lift_def Let_def split: if_split_asm)
          apply ceqv
         apply csymbr
         apply csymbr
       apply (simp only:)
       apply (rule ccorres_Cond_rhs_Seq)
        apply (rule ccorres_alternative2)
        apply (rule ccorres_split_throws)
         apply (fold dc_def)[1]
         apply (rule ccorres_call_hSkip)
           apply (rule slowpath_ccorres)
          apply simp
         apply simp
        apply (vcg exspec=slowpath_noreturn_spec)
       apply (rule ccorres_alternative1)
       apply (rule ccorres_if_lhs[rotated])
        apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
        apply simp
       apply (simp del: Collect_const cong: call_ignore_cong)
       apply (elim conjE)
       apply (simp add: getThreadCSpaceRoot_def locateSlot_conv
                   del: Collect_const cong: call_ignore_cong)
       apply (rule ccorres_pre_getCTE2)
       apply (rule ccorres_abstract_ksCurThread, ceqv)
       apply (rule ccorres_move_array_assertion_tcb_ctes
                   ccorres_move_c_guard_tcb_ctes3
                   ccorres_move_const_guard
                   ccorres_rhs_assoc)+
       apply (ctac add: lookup_fp_ccorres)
         apply (rename_tac luRet ep_cap)
         apply (rule ccorres_abstract_ksCurThread, ceqv)
         apply (rule ccorres_move_array_assertion_tcb_ctes
             | simp del: Collect_const cong: call_ignore_cong)+
         apply (csymbr, csymbr)
         apply (simp add: ccap_relation_case_sum_Null_endpoint
                          of_bl_from_bool from_bool_0
                     del: Collect_const cong: call_ignore_cong)
         apply (rule ccorres_Cond_rhs_Seq)
          apply (simp add: if_1_0_0 cong: if_cong)
          apply (rule ccorres_cond_true_seq)
          apply (rule ccorres_split_throws)
           apply (fold dc_def)[1]
           apply (rule ccorres_call_hSkip)
             apply (rule slowpath_ccorres)
            apply simp
           apply simp
          apply (vcg exspec=slowpath_noreturn_spec)
         apply (rule ccorres_rhs_assoc)+
         apply csymbr+
         apply (simp add: if_1_0_0 isRight_case_sum
                     del: Collect_const cong: call_ignore_cong)
         apply (elim conjE)
         apply (frule(1) cap_get_tag_isCap[THEN iffD2])
         apply (simp add: ccap_relation_ep_helpers from_bool_0
                     del: Collect_const cong: call_ignore_cong)
         apply (rule ccorres_Cond_rhs_Seq)
          apply simp
          apply (rule ccorres_split_throws)
           apply (fold dc_def)[1]
           apply (rule ccorres_call_hSkip)
             apply (rule slowpath_ccorres)
            apply simp
           apply simp
          apply (vcg exspec=slowpath_noreturn_spec)
         apply (simp del: Collect_const cong: call_ignore_cong)
            apply (rule ccorres_pre_getBoundNotification)
           apply (rule ccorres_rhs_assoc2)
           apply (rule_tac xf'=ret__int_' and r'="\<lambda>rv rv'. rv' = from_bool rv"
                 in ccorres_split_nothrow)
               apply (rule_tac P="bound_tcb_at' ((=) bound_ntfn) curThread
                        and valid_objs' and no_0_obj'
                        and (\<lambda>s. curThread = ksCurThread s)" in ccorres_from_vcg[where P'=UNIV])
               apply (rule allI, rule conseqPre, vcg)
               apply (clarsimp simp: rf_sr_ksCurThread pred_tcb_at'_def)
               apply (drule(3) obj_at_bound_tcb_grandD, clarsimp simp: typ_heap_simps if_1_0_0 return_def)
               apply (simp add: in_liftM Bex_def getNotification_def getObject_return objBits_simps'
                                return_def cnotification_relation_isActive
                                trans [OF eq_commute from_bool_eq_if])
              apply ceqv
             apply (simp only: from_bool_0)
             apply (rule ccorres_Cond_rhs_Seq)
            apply (rule ccorres_split_throws)
             apply simp
             apply (fold dc_def)[1]
             apply (rule ccorres_call_hSkip)
               apply (rule slowpath_ccorres, simp+)
            apply (vcg exspec=slowpath_noreturn_spec)
             apply (simp del: Collect_const cong: call_ignore_cong)
             apply (csymbr, csymbr)
             apply (simp add: ccap_relation_ep_helpers
                         del: Collect_const cong: call_ignore_cong)
             apply (rule_tac xf'="ret__unsigned_'"
                          and r'="\<lambda>ep v. (v = scast EPState_Send) = isSendEP ep"
                         in ccorres_split_nothrow)
                 apply (rule ccorres_add_return2)
                 apply (rule ccorres_pre_getEndpoint, rename_tac ep)
                 apply (rule_tac P="ko_at' ep (capEPPtr (theRight luRet)) and valid_objs'"
                              in ccorres_from_vcg[where P'=UNIV])
                 apply (rule allI, rule conseqPre, vcg)
                 apply (clarsimp simp: return_def)
                 apply (erule cmap_relationE1[OF cmap_relation_ep], erule ko_at_projectKO_opt)
                 apply (clarsimp simp: typ_heap_simps')
                 apply (simp add: cendpoint_relation_def Let_def isSendEP_def
                                  endpoint_state_defs
                           split: endpoint.split_asm)
                apply ceqv
               apply (rename_tac send_ep send_ep_is_send)
               apply (rule_tac P="ko_at' send_ep (capEPPtr (theRight luRet))
                                    and valid_objs'" in ccorres_cross_over_guard)
               apply (simp del: Collect_const cong: call_ignore_cong)
               apply (rule ccorres_Cond_rhs_Seq)
                apply (simp del: Collect_const not_None_eq)
                apply (rule ccorres_split_throws)
                 apply (fold dc_def)[1]
                 apply (rule ccorres_call_hSkip)
                   apply (rule slowpath_ccorres, simp+)
                apply (vcg exspec=slowpath_noreturn_spec)
               apply (simp add: getThreadVSpaceRoot_def locateSlot_conv
                                getThreadCallerSlot_def
                           del: Collect_const cong: if_cong call_ignore_cong)
               apply (rule ccorres_abstract_ksCurThread, ceqv)
               apply (rename_tac ksCurThread_y)
               apply (rule ccorres_move_const_guard
                           ccorres_move_c_guard_tcb_ctes2
                           ccorres_move_array_assertion_tcb_ctes)+
               apply (rule_tac xf'="ksCurThread_' \<circ> globals"
                           and val="tcb_ptr_to_ctcb_ptr curThread"
                           in ccorres_abstract_known)
                apply (rule Seq_weak_ceqv, rule Basic_ceqv)
                apply (rule rewrite_xfI, clarsimp simp only: o_def)
                apply (rule refl)
               apply csymbr
               apply (rule ccorres_move_c_guard_cte)
               apply (rule_tac var="callerCap_'" and var_update="callerCap_'_update"
                            in getCTE_h_val_ccorres_split[where P=\<top>])
                 apply simp
                apply ceqv
               apply (rename_tac caller_cap caller_cap_c)
               apply (rule_tac P="\<lambda>_. capAligned (cteCap caller_cap)"
                            in ccorres_cross_over_guard)
           apply (rule ccorres_add_return, ctac add: fastpath_reply_cap_check_ccorres)
             apply (drule spec, drule_tac P="ccap_relation cp caller_cap_c" for cp in mp, assumption)
             apply (simp add: from_bool_0
                         del: Collect_const cong: call_ignore_cong)
             apply (rule ccorres_Cond_rhs_Seq)
              apply (simp cong: conj_cong)
                apply (rule ccorres_split_throws)
                 apply (fold dc_def)[1]
                 apply (rule ccorres_call_hSkip)
                   apply (rule slowpath_ccorres, simp+)
                apply (vcg exspec=slowpath_noreturn_spec)
               apply (simp del: Collect_const cong: call_ignore_cong)
               apply (csymbr, csymbr)
               apply (rule_tac r'="\<lambda>ft ft'. (ft' = scast seL4_Fault_NullFault) = (ft = None)"
                        and xf'="ret__unsigned_'" in ccorres_split_nothrow)
                   apply (rule threadGet_vcg_corres)
                   apply (rule allI, rule conseqPre, vcg)
                   apply (clarsimp simp: obj_at_tcbs_of)
                   apply (clarsimp simp: typ_heap_simps' ctcb_relation_def cfault_rel_def
                                         ccap_relation_reply_helper)
                   apply (clarsimp simp: seL4_Fault_lift_def Let_def split: if_split_asm)
                  apply ceqv
                 apply csymbr
                 apply (simp del: Collect_const not_None_eq cong: call_ignore_cong)
                 apply (rule ccorres_Cond_rhs_Seq)
                  apply (simp del: Collect_const not_None_eq)
                  apply (rule ccorres_split_throws)
                   apply (fold dc_def)[1]
                   apply (rule ccorres_call_hSkip)
                     apply (rule slowpath_ccorres, simp+)
                  apply (vcg exspec=slowpath_noreturn_spec)
                 apply (simp del: Collect_const cong: call_ignore_cong)
                 apply (rule ccorres_move_c_guard_tcb_ctes3 ccorres_move_const_guards
                             ccorres_move_array_assertion_tcb_ctes)+
                 apply (rule_tac var="newVTable_'" and var_update="newVTable_'_update"
                                in getCTE_h_val_ccorres_split[where P=\<top>])
                   apply simp
                  apply ceqv
                 apply (rename_tac pd_cap pd_cap_c)
                 apply (rule ccorres_symb_exec_r)
                   apply (rule_tac xf'=ret__unsigned_' in ccorres_abstract, ceqv)
                   apply (rename_tac pd_cap_c_ptr_maybe)
                   apply csymbr+
                   apply (simp add: isValidVTableRoot_conv from_bool_0
                               del: Collect_const cong: call_ignore_cong)
                   apply (rule ccorres_Cond_rhs_Seq)

                    apply simp
                    apply (rule ccorres_split_throws)
                     apply (fold dc_def)[1]
                     apply (rule ccorres_call_hSkip)
                       apply (rule slowpath_ccorres, simp+)
                    apply (vcg exspec=slowpath_noreturn_spec)
                   apply (simp del: Collect_const cong: call_ignore_cong)
                   apply (drule isValidVTableRootD)
                   apply (rule_tac P="pd_cap_c_ptr_maybe = capUntypedPtr (cteCap pd_cap)"
                               in ccorres_gen_asm2)
                   apply (simp add: ccap_relation_pd_helper cap_get_tag_isCap_ArchObject2
                                    ccap_relation_reply_helper
                                    ptr_add_assertion_positive
                           del: Collect_const Word_Lib.ptr_add_def cong: call_ignore_cong)
                   apply (rule ccorres_move_array_assertion_pd
                          | (rule ccorres_flip_Guard ccorres_flip_Guard2,
                             rule ccorres_move_array_assertion_pd)
                          |  rule ccorres_flip_Guard2, rule ccorres_Guard_True_Seq)+
                   apply (rule stored_hw_asid_get_ccorres_split[where P=\<top>], ceqv)

                   apply (ctac add: getCurDomain_maxDom_ccorres_dom_')
                     apply (rename_tac curDom curDom')
                     apply (rule_tac P="curDom \<le> maxDomain" in ccorres_gen_asm)
                     apply (simp add: prio_and_dom_limit_helpers del: Collect_const)
                     apply (rule ccorres_move_c_guard_tcb)
                     apply (rule ccorres_pre_threadGet)
                     apply (ctac add: isHighestPrio_ccorres)
                      apply (rename_tac highest highest')
                      apply (clarsimp simp: to_bool_def simp del: Collect_const)
                      apply (rule ccorres_cond_seq)
                      apply (rule ccorres_cond2'[where R=\<top>], blast)

                      apply (rule ccorres_split_throws)
                      apply (fold dc_def)[1]
                      apply (rule ccorres_call_hSkip)
                      apply (rule slowpath_ccorres, simp+)
                      apply (vcg exspec=slowpath_noreturn_spec)
                      apply (simp del: Collect_const add: from_bool_0 cong: call_ignore_cong)

                     apply csymbr+
                     apply (rule ccorres_symb_exec_l3[OF _ gets_inv _ empty_fail_gets])
                      apply (rename_tac asidMap)
                      apply (rule_tac P="asid_map_pd_to_hwasids asidMap (capPDBasePtr (capCap ((cteCap pd_cap))))
                                            = set_option (pde_stored_asid shw_asid)" in ccorres_gen_asm)
                      apply (simp del: Collect_const cong: call_ignore_cong)
                      apply (rule ccorres_Cond_rhs_Seq)
                       apply (simp add: pde_stored_asid_def asid_map_pd_to_hwasids_def)
                       apply (rule ccorres_split_throws)
                        apply (fold dc_def)[1]
                        apply (rule ccorres_call_hSkip)
                          apply (rule slowpath_ccorres, simp+)
                       apply (vcg exspec=slowpath_noreturn_spec)
                      apply (simp add: pde_stored_asid_def asid_map_pd_to_hwasids_def
                                       to_bool_def
                                  del: Collect_const cong: call_ignore_cong)

                  apply (rule ccorres_move_c_guard_tcb ccorres_move_const_guard)+
                   apply (rule ccorres_symb_exec_l3[OF _ threadGet_inv _ empty_fail_threadGet])
                    apply (rename_tac destDom)

                    apply (rule ccorres_seq_cond_raise[THEN iffD2])
                    apply (rule_tac R="obj_at' ((=) destDom \<circ> tcbDomain)
                                                  (capTCBPtr (cteCap caller_cap))
                                        and (\<lambda>s. ksCurDomain s = curDom \<and> curDom \<le> maxDomain
                                                 \<and> destDom \<le> maxDomain)"
                                   in ccorres_cond2')
                      apply clarsimp
                      apply (drule(1) obj_at_cslift_tcb)+
                      apply (clarsimp simp: typ_heap_simps' rf_sr_ksCurDomain)
                      apply (drule ctcb_relation_tcbDomain[symmetric])
                      apply (clarsimp simp: up_ucast_inj_eq[symmetric] maxDom_def
                                            maxDomain_def numDomains_def)

                     apply simp
                     apply (rule ccorres_split_throws)
                      apply (fold dc_def)[1]
                      apply (rule ccorres_call_hSkip)
                        apply (rule slowpath_ccorres, simp+)
                     apply (vcg exspec=slowpath_noreturn_spec)
                    apply (simp add: pde_stored_asid_def asid_map_pd_to_hwasids_def
                                     to_bool_def
                                del: Collect_const cong: call_ignore_cong)

                    apply (rule ccorres_rhs_assoc2)
                    apply (rule ccorres_rhs_assoc2)
                    apply (rule_tac xf'=xfdc and r'=dc in ccorres_split_nothrow)
                        apply (rule_tac P="capAligned (theRight luRet)" in ccorres_gen_asm)
                        apply (rule_tac P=\<top> and P'="\<lambda>s. ksCurThread s = curThread"
                                   in threadSet_ccorres_lemma3)
                         apply vcg
                        apply (clarsimp simp: rf_sr_ksCurThread typ_heap_simps'
                                              h_t_valid_clift_Some_iff)
                        apply (clarsimp simp: capAligned_def isCap_simps objBits_simps
                                              "StrictC'_thread_state_defs" mask_def)
                        apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                              typ_heap_simps' objBits_defs)
                        apply (rule conjI)
                         apply (clarsimp simp: cpspace_relation_def typ_heap_simps'
                                               update_tcb_map_tos map_to_tcbs_upd)
                         apply (subst map_to_ctes_upd_tcb_no_ctes, assumption)
                          apply (rule ball_tcb_cte_casesI, simp_all)[1]
                         apply (simp add: cep_relations_drop_fun_upd)
                         apply (erule cmap_relation_updI, erule ko_at_projectKO_opt)
                          apply (simp add: ctcb_relation_def cthread_state_relation_def
                                           "StrictC'_thread_state_defs" from_bool_0
                                           to_bool_def if_1_0_0)
                          apply (clarsimp simp: ccap_relation_ep_helpers)
                         apply simp
                        apply (rule conjI, erule cready_queues_relation_not_queue_ptrs)
                          apply (rule ext, simp split: if_split)
                         apply (rule ext, simp split: if_split)
                        apply (simp add: carch_state_relation_def cmachine_state_relation_def
                                         typ_heap_simps' map_comp_update projectKO_opt_tcb
                                         cvariable_relation_upd_const ko_at_projectKO_opt)
                       apply ceqv
                      apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
                      apply (rule_tac xf'=xfdc and r'=dc in ccorres_split_nothrow)
                          apply (rule fastpath_enqueue_ccorres[unfolded o_def,simplified])
                          apply simp
                         apply ceqv
                        apply (simp add: liftM_def del: Collect_const cong: call_ignore_cong)
                        apply (rule ccorres_move_c_guard_tcb_ctes3)
                        apply (rule_tac r'="\<lambda>rv rv'. rv' = mdbPrev (cteMDBNode rv)"
                                    and xf'=ret__unsigned_' in ccorres_split_nothrow)
                            apply (rule_tac P="tcb_at' curThread
                                            and K (curThread = ksCurThread_y)
                                            and (\<lambda>s. ksCurThread s = ksCurThread_y)"
                                         in getCTE_ccorres_helper[where P'=UNIV])
                            apply (rule conseqPre, vcg)
                            apply (clarsimp simp: typ_heap_simps' cte_level_bits_def
                                                  tcbCallerSlot_def size_of_def
                                                  tcb_cnode_index_defs)
                            apply (clarsimp simp: ccte_relation_def map_option_Some_eq2)
                           apply ceqv
                          apply (rule ccorres_assert)
                          apply (rename_tac mdbPrev_cte mdbPrev_cte_c)
                          apply (rule ccorres_split_nothrow_dc)
                             apply (simp add: updateMDB_def Let_def
                                         del: Collect_const cong: if_cong)
                             apply (rule_tac P="cte_wp_at' ((=) mdbPrev_cte)
                                                  (curThread + (tcbCallerSlot << cte_level_bits))
                                                   and valid_mdb'"
                                         in ccorres_from_vcg[where P'=UNIV])
                             apply (rule allI, rule conseqPre, vcg)
                             apply (clarsimp simp: cte_wp_at_ctes_of)
                             apply (drule(2) valid_mdb_ctes_of_prev[rotated])
                             apply (clarsimp simp: cte_wp_at_ctes_of)
                             apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
                             apply (clarsimp simp: typ_heap_simps' split_def)
                             apply (rule getCTE_setCTE_rf_sr, simp_all)[1]
                             apply (clarsimp simp: ccte_relation_def map_option_Some_eq2
                                                   cte_to_H_def mdb_node_to_H_def
                                                   c_valid_cte_def)
                            apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
                                   rule ccorres_rhs_assoc2)
                            apply (rule ccorres_split_nothrow_dc)
                               apply (rule_tac P="cte_at' (curThread + (tcbCallerSlot << cte_level_bits))
                                                     and tcb_at' curThread
                                                     and K (curThread = ksCurThread_y)"
                                          in ccorres_from_vcg[where P'=UNIV])
                               apply (rule allI, rule conseqPre, vcg)
                               apply (clarsimp simp: cte_wp_at_ctes_of)
                               apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
                               apply (clarsimp simp: typ_heap_simps' split_def tcbCallerSlot_def
                                                     tcb_cnode_index_defs
                                                     cte_level_bits_def size_of_def
                                                     packed_heap_update_collapse_hrs)
                               apply (rule setCTE_rf_sr, simp_all add: typ_heap_simps')[1]
                               apply (clarsimp simp: ccte_relation_eq_ccap_relation makeObject_cte
                                                     mdb_node_to_H_def nullMDBNode_def
                                                     ccap_relation_NullCap_iff)
                              apply csymbr
                              apply (ctac add: fastpath_copy_mrs_ccorres[unfolded forM_x_def])
                                apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
                                    apply (simp add: setThreadState_runnable_simp)
                                    apply (rule_tac P=\<top> in threadSet_ccorres_lemma2, vcg)
                                    apply (clarsimp simp: typ_heap_simps' rf_sr_def
                                                          cstate_relation_def Let_def)
                                    apply (rule conjI)
                                     apply (clarsimp simp: cpspace_relation_def typ_heap_simps'
                                                           update_tcb_map_tos map_to_tcbs_upd)
                                     apply (subst map_to_ctes_upd_tcb_no_ctes, assumption)
                                      apply (rule ball_tcb_cte_casesI, simp_all)[1]
                                     apply (simp add: cep_relations_drop_fun_upd)
                                     apply (erule cmap_relation_updI, erule ko_at_projectKO_opt)
                                      apply (simp add: ctcb_relation_def cthread_state_relation_def)
                                     apply simp
                                    apply (rule conjI, erule cready_queues_relation_not_queue_ptrs)
                                      apply (rule ext, simp split: if_split)
                                     apply (rule ext, simp split: if_split)
                                    apply (simp add: carch_state_relation_def cmachine_state_relation_def
                                                     typ_heap_simps' map_comp_update projectKO_opt_tcb
                                                     cvariable_relation_upd_const ko_at_projectKO_opt)
                                   apply ceqv
                                  apply (simp only: bind_assoc[symmetric])
                                  apply (rule ccorres_stateAssert_after)
                                   apply (rule ccorres_split_nothrow_novcg_dc)
                                      apply (rule ccorres_call,
                                             rule_tac v=shw_asid and pd="capUntypedPtr (cteCap pd_cap)"
                                                   in switchToThread_fp_ccorres,
                                             simp+)[1]
                                     apply (rule_tac P="\<lambda>s. ksCurThread s = capTCBPtr (cteCap caller_cap)"
                                                  in ccorres_cross_over_guard)
                                     apply csymbr
                                     apply csymbr
                                     apply (rule ccorres_call_hSkip)
                                       apply (fold dc_def)[1]
                                       apply (rule fastpath_restore_ccorres)
                                      apply simp
                                     apply simp
                                    apply (simp add: setCurThread_def)
                                    apply wp
                                    apply (rule_tac P=\<top> in hoare_triv, simp)
                                   apply simp
                                  apply (simp add: imp_conjL rf_sr_ksCurThread del: all_imp_to_ex)
                                  apply (clarsimp simp: ccap_relation_ep_helpers guard_is_UNIV_def
                                                        mi_from_H_def)
                                 apply (simp add: pd_has_hwasid_def)
                                 apply (wp sts_valid_objs')
                                apply (simp del: Collect_const)
                                apply (vcg exspec=thread_state_ptr_set_tsType_np_modifies)
                               apply simp
                               apply (rule mapM_x_wp'[OF hoare_weaken_pre], wp)
                               apply clarsimp
                              apply simp
                              apply (vcg exspec=fastpath_copy_mrs_modifies)
                             apply (simp add: valid_tcb_state'_def)
                             apply wp
                             apply (wp setCTE_cte_wp_at_other)
                            apply (simp del: Collect_const)
                            apply vcg
                           apply (simp add: o_def)
                           apply (wp | simp
                                      | wp (once) updateMDB_weak_cte_wp_at
                                      | wp (once) updateMDB_cte_wp_at_other)+
                          apply (vcg exspec=mdb_node_ptr_mset_mdbNext_mdbRevocable_mdbFirstBadged_modifies)
                         apply simp
                         apply (wp getCTE_wp')
                        apply simp
                        apply vcg
                       apply (simp add: shiftl_t2n)
                       apply (wp hoare_drop_imps setEndpoint_valid_mdb' set_ep_valid_objs'
                              setObject_no_0_obj'[where 'a=endpoint, folded setEndpoint_def])
                      apply simp
                      apply (vcg exspec=endpoint_ptr_mset_epQueue_tail_state_modifies
                                 exspec=endpoint_ptr_set_epQueue_head_np_modifies
                                 exspec=endpoint_ptr_get_epQueue_tail_modifies)
                     apply (simp add: valid_pspace'_def pred_conj_def conj_comms
                                      valid_mdb'_def)
                     apply (wp threadSet_cur threadSet_tcbState_valid_objs
                               threadSet_state_refs_of' threadSet_ctes_of
                               valid_ep_typ_at_lift' threadSet_cte_wp_at'
                                  | simp)+
                    apply (vcg exspec=thread_state_ptr_mset_blockingObject_tsType_modifies)

                     apply simp
                     apply (rule threadGet_wp)
                    apply simp
                    apply wp[1]
                      apply clarsimp
                      apply (wp (once) hoare_drop_imp)
                      apply wp
                      apply (wp (once) hoare_drop_imps)
                      apply wp
                     apply (simp del: Collect_const)
                     apply clarsimp
                     apply (vcg exspec=isHighestPrio_modifies)
                    apply (wp cd_wp)
                    apply (simp cong: if_cong)
                   apply (simp cong: if_cong)
                   apply vcg
                apply (simp add: syscall_from_H_def del: Collect_const)
                apply (vcg exspec=cap_page_directory_cap_get_capPDBasePtr_spec2)
               apply (rule conseqPre,
                      vcg exspec=cap_page_directory_cap_get_capPDBasePtr_spec2,
                      clarsimp)
              apply (simp add:ccap_relation_reply_helper cong:if_cong)
              apply (rule threadGet_wp)
             apply (simp add: syscall_from_H_def ccap_relation_reply_helper)
             apply (vcg exspec=seL4_Fault_get_seL4_FaultType_modifies)
            apply simp
            apply wp
           apply simp
           apply (vcg exspec=fastpath_reply_cap_check_modifies)
          apply simp
              apply (rule getEndpoint_wp)
             apply (simp add: syscall_from_H_def ccap_relation_reply_helper)
             apply (vcg exspec=endpoint_ptr_get_state_modifies)
            apply simp
            apply (wp option_case_liftM_getNotification_wp[unfolded fun_app_def])
           apply (simp del: Collect_const)
           apply vcg
          apply (simp add: if_1_0_0 getSlotCap_def)
          apply (rule valid_isRight_theRight_split)
          apply (wp getCTE_wp')
          apply (rule validE_R_abstract_rv)
          apply wp
         apply (simp del: Collect_const)
         apply (vcg exspec=lookup_fp_modifies)
        apply simp
        apply (rule threadGet_wp)
       apply (simp del: Collect_const)
       apply vcg
      apply simp
      apply (rule user_getreg_wp)
     apply simp
     apply (rule user_getreg_wp)
    apply (rule conjI)
     apply (clarsimp simp: ct_in_state'_def obj_at_tcbs_of word_sle_def)
     apply (clarsimp simp add: invs_ksCurDomain_maxDomain')
     apply (rule conjI, fastforce)
     apply (frule invs_queues)
     apply (simp add: valid_queues_def)
     apply (frule tcbs_of_aligned')
      apply (simp add:invs_pspace_aligned')
     apply (frule tcbs_of_cte_wp_at_caller)
     apply (clarsimp simp:size_of_def field_simps
        dest!:ptr_val_tcb_ptr_mask2[unfolded mask_def])
     apply (frule st_tcb_at_state_refs_ofD')
     apply (clarsimp simp: obj_at_tcbs_of ct_in_state'_def st_tcb_at_tcbs_of
                           invs_cur' invs_valid_objs' ctes_of_valid'
                           fun_upd_def[symmetric] fun_upd_idem pred_tcb_at'_def invs_no_0_obj')
     apply (frule cte_wp_at_valid_objs_valid_cap', clarsimp)
     apply (clarsimp simp: isCap_simps valid_cap'_def[split_simps capability.split]
                           maskCapRights_def cte_wp_at_ctes_of cte_level_bits_def)
     apply (frule_tac p = a in ctes_of_valid',clarsimp)
     apply (simp add:valid_cap_simps')
     apply (clarsimp simp:cte_level_bits_def)
     apply (frule_tac p="p + tcbCallerSlot * cte_size"for p cte_size in ctes_of_valid', clarsimp)
     apply (clarsimp simp: valid_capAligned)
     apply (frule_tac ptr2 = v0a in tcbs_of_cte_wp_at_vtable)
     apply (frule_tac ptr2 = v0a in tcbs_of_aligned')
      apply (simp add:invs_pspace_aligned')
     apply (clarsimp simp:size_of_def field_simps cte_wp_at_ctes_of
       word_sle_def word_sless_def
       dest!:ptr_val_tcb_ptr_mask2[unfolded mask_def])
     apply (clarsimp simp: valid_cap_simps' obj_at_tcbs_of)
     apply (frule_tac p="p + tcbVTableSlot * cte_size" for p cte_size in ctes_of_valid', clarsimp)
     apply (clarsimp simp: isCap_simps valid_cap_simps' capAligned_def
                           invs_valid_pde_mappings' obj_at_tcbs_of
                    dest!: isValidVTableRootD)
     apply (frule invs_mdb')
     apply (clarsimp simp: cte_wp_at_ctes_of tcbSlots cte_level_bits_def
                           makeObject_cte isValidVTableRoot_def
                           ARM_H.isValidVTableRoot_def
                           pde_stored_asid_def to_bool_def
                           valid_mdb'_def valid_tcb_state'_def
                           word_le_nat_alt[symmetric] length_msgRegisters)
     apply (frule ko_at_valid_ep', fastforce)
     apply (rule conjI) (* tcbDomain \<le> maxDomain *)
      apply (drule invs_valid_objs')
      apply (solves \<open>drule_tac t=v0a in valid_objs'_maxDomain; clarsimp simp: obj_at_tcbs_of\<close>)
      apply clarsimp
     apply (safe del: notI disjE)[1]
       apply (simp add: isSendEP_def valid_ep'_def tcb_at_invs'
                 split: Structures_H.endpoint.split_asm)
       apply (rule subst[OF endpoint.sel(1)],
              erule st_tcb_at_not_in_ep_queue[where P="(=) Running", rotated],
              clarsimp+)
       apply (simp add: obj_at_tcbs_of st_tcb_at_tcbs_of)
      apply (drule invs_sym')
      apply (erule_tac  P=sym_refs in subst[rotated])
      apply (rule fun_upd_idem[symmetric])
      apply (clarsimp simp: tcb_bound_refs'_def)
      apply (case_tac ntfnptr, simp_all)[1]
      apply (clarsimp simp: set_eq_subset)
     apply (clarsimp simp: field_simps)
    apply (clarsimp simp: syscall_from_H_def[split_simps syscall.split]
                          word_sle_def word_sless_def rf_sr_ksCurThread
                          ptr_val_tcb_ptr_mask' size_of_def cte_level_bits_def
                          tcb_cnode_index_defs tcbSlots
                simp del: Collect_const)
    apply (frule obj_at_bound_tcb_grandD, clarsimp, clarsimp, simp)
    apply (clarsimp simp: typ_heap_simps if_1_0_0)
    apply (clarsimp simp: ccte_relation_eq_ccap_relation
                          if_1_0_0 ccap_relation_case_sum_Null_endpoint
                          isRight_case_sum typ_heap_simps'
                          pdBits_def pageBits_def pdeBits_def
                          cap_get_tag_isCap mi_from_H_def)
    apply (intro conjI impI allI
           ; clarsimp simp: isCap_simps capAligned_def objBits_simps' ccap_relation_pd_helper
                            cap_get_tag_isCap_ArchObject2 pdeBits_def typ_heap_simps isRight_def
                     dest!: ptr_val_tcb_ptr_mask2[unfolded objBits_def mask_def, simplified]
                            isValidVTableRootD
                     split: sum.splits)
     apply (clarsimp simp: ctcb_relation_def)+
    done
qed

lemmas monadic_rewrite_symb_exec_l' = monadic_rewrite_symb_exec_l'_preserve_names

lemma possibleSwitchTo_rewrite:
  "monadic_rewrite True True
          (\<lambda>s. obj_at' (\<lambda>tcb. tcbPriority tcb = destPrio \<and> tcbDomain tcb = destDom) t s
              \<and> ksSchedulerAction s = ResumeCurrentThread
              \<and> ksCurThread s = thread
              \<and> ksCurDomain s = curDom
              \<and> destDom = curDom)
    (possibleSwitchTo t) (setSchedulerAction (SwitchToThread t))"
  apply (simp add: possibleSwitchTo_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_symb_exec_l'[OF threadGet_inv empty_fail_threadGet,
                                               where P'=\<top>], simp)
      apply (rule monadic_rewrite_bind_tail)
       apply (rule_tac P="targetDom = curDom" in monadic_rewrite_gen_asm)
       apply simp
       apply (rule_tac P="action = ResumeCurrentThread" in monadic_rewrite_gen_asm)
       apply simp
       apply (rule monadic_rewrite_refl)
      apply (wp threadGet_wp cd_wp |simp add: bitmap_fun_defs)+
   apply (simp add: getCurThread_def curDomain_def gets_bind_ign getSchedulerAction_def)
   apply (rule monadic_rewrite_refl)
  apply clarsimp
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

lemma schedule_rewrite_ct_not_runnable':
  "monadic_rewrite True True
            (\<lambda>s. ksSchedulerAction s = SwitchToThread t \<and> ct_in_state' (Not \<circ> runnable') s
                 \<and> (ksCurThread s \<noteq> ksIdleThread s)
                 \<and> fastpathBestSwitchCandidate t s)
            (schedule)
            (do setSchedulerAction ResumeCurrentThread; switchToThread t od)"
  apply (simp add: schedule_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_bind_tail)
      apply (rule_tac P="action = SwitchToThread t" in monadic_rewrite_gen_asm, simp)
      apply (rule monadic_rewrite_bind_tail)
       apply (rule_tac P="\<not> wasRunnable \<and> action = SwitchToThread t"
              in monadic_rewrite_gen_asm,simp)
       apply (rule monadic_rewrite_bind_tail, rename_tac idleThread)
        apply (rule monadic_rewrite_bind_tail, rename_tac targetPrio)
         apply (rule monadic_rewrite_bind_tail, rename_tac curPrio)
          apply (rule monadic_rewrite_bind_tail, rename_tac fastfail)
           apply (rule monadic_rewrite_bind_tail, rename_tac curDom)
            apply (rule monadic_rewrite_bind_tail, rename_tac highest)
             apply (rule_tac P="\<not> (fastfail \<and> \<not> highest)" in monadic_rewrite_gen_asm, simp only:)
             apply simp
             apply (rule monadic_rewrite_refl)
            apply (wpsimp wp: hoare_vcg_imp_lift)
            apply (simp add: isHighestPrio_def')
            apply wp+
          apply (wp hoare_vcg_disj_lift)
           apply (wp scheduleSwitchThreadFastfail_False_wp)
          apply (wp hoare_vcg_disj_lift threadGet_wp'' | simp add: comp_def)+
   (* remove no-ops, somewhat by magic *)
   apply (rule monadic_rewrite_symb_exec_l'_TT, solves wp,
          wpsimp wp: empty_fail_isRunnable simp: isHighestPrio_def')+
            apply (simp add: setSchedulerAction_def)
            apply (subst oblivious_modify_swap[symmetric], rule oblivious_switchToThread_schact)
            apply (rule monadic_rewrite_refl)
           apply wp+
  apply (clarsimp simp: ct_in_state'_def)
  apply (strengthen not_pred_tcb_at'_strengthen, simp)
  apply normalise_obj_at'
  apply (simp add: fastpathBestSwitchCandidate_def)
  apply (erule_tac x="tcbPriority ko" in allE)
  apply (erule impE, normalise_obj_at'+)
  done

crunch tcb2[wp]: "Arch.switchToThread" "tcb_at' t"
  (ignore: ARM.clearExMonitor)

lemma resolveAddressBits_points_somewhere:
  "\<lbrace>\<lambda>s. \<forall>slot. Q slot s\<rbrace> resolveAddressBits cp cptr bits \<lbrace>Q\<rbrace>,-"
  apply (rule_tac Q'="\<lambda>rv s. \<forall>rv. Q rv s" in hoare_post_imp_R)
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

lemma monadic_rewrite_exists_v:
  "[| !! v. monadic_rewrite E F (Q v) f g |]
    ==> monadic_rewrite E F (%x. (EX v. P v x) & (ALL v. P v x --> Q v x)) f g"
  apply (rule monadic_rewrite_name_pre)
  apply clarsimp
  apply (erule_tac x=v in meta_allE)
  apply (erule monadic_rewrite_imp)
  apply clarsimp
  done

lemma monadic_rewrite_threadGet:
  "monadic_rewrite E F (obj_at' (\<lambda>tcb. f tcb = v) t)
    (threadGet f t) (return v)"
  unfolding getThreadState_def
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans[rotated])
    apply (rule monadic_rewrite_gets_known)
   apply (unfold threadGet_def liftM_def fun_app_def)
   apply (rule monadic_rewrite_symb_exec_l' | wp | rule empty_fail_getObject getObject_inv)+
     apply (clarsimp; rule no_fail_getObject_tcb)
    apply (simp only: exec_gets)
    apply (rule_tac P = "(\<lambda>s. (f x)=v) and tcb_at' t" in monadic_rewrite_refl3)
    apply (simp add:)
   apply (wp OMG_getObject_tcb | wpc)+
  apply (auto intro: obj_tcb_at')
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
crunches cteInsert, asUser
  for obj_at'_tcbIPCBuffer[wp]: "obj_at' (\<lambda>tcb. P (tcbIPCBuffer tcb)) t"
  (wp: setCTE_obj_at'_queued crunch_wps threadSet_obj_at'_really_strongest)
end

crunch ksReadyQueues_inv[wp]: cteInsert "\<lambda>s. P (ksReadyQueues s)"
  (wp: hoare_drop_imps)

crunches cteInsert, threadSet, asUser, emptySlot
  for ksReadyQueuesL1Bitmap_inv[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and ksReadyQueuesL2Bitmap_inv[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (wp: hoare_drop_imps)

crunch ksReadyQueuesL1Bitmap_inv[wp]: setEndpoint "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv)
crunch ksReadyQueuesL2Bitmap_inv[wp]: setEndpoint "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv)

lemma setThreadState_runnable_bitmap_inv:
  "runnable' ts \<Longrightarrow>
    \<lbrace> \<lambda>s. P (ksReadyQueuesL1Bitmap s) \<rbrace> setThreadState ts t \<lbrace>\<lambda>rv s. P (ksReadyQueuesL1Bitmap s) \<rbrace>"
  "runnable' ts \<Longrightarrow>
    \<lbrace> \<lambda>s. Q (ksReadyQueuesL2Bitmap s) \<rbrace> setThreadState ts t \<lbrace>\<lambda>rv s. Q (ksReadyQueuesL2Bitmap s) \<rbrace>"
   by (simp_all add: setThreadState_runnable_simp, wp+)

lemma fastpath_callKernel_SysCall_corres:
  "monadic_rewrite True False
         (invs' and ct_in_state' ((=) Running)
                and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
                and (\<lambda>s. ksDomainTime s \<noteq> 0))
     (callKernel (SyscallEvent SysCall)) (fastpaths SysCall)"
  supply if_cong[cong]
  apply (rule monadic_rewrite_introduce_alternative)
   apply (simp add: callKernel_def)
  apply (rule monadic_rewrite_imp)
   apply (simp add: handleEvent_def handleCall_def
                    handleInvocation_def liftE_bindE_handle
                    bind_assoc getMessageInfo_def)
   apply (simp add: catch_liftE_bindE unlessE_throw_catch_If
                    unifyFailure_catch_If catch_liftE
                    getMessageInfo_def alternative_bind
                    fastpaths_def
              cong: if_cong)
   apply (rule monadic_rewrite_rdonly_bind_l, wp)
   apply (rule monadic_rewrite_bind_tail)
    apply (rule monadic_rewrite_rdonly_bind_l, wp)
    apply (rule monadic_rewrite_bind_tail)
     apply (rename_tac msgInfo)
     apply (rule monadic_rewrite_rdonly_bind_l, wp)
     apply (rule monadic_rewrite_bind_tail)
      apply (rule monadic_rewrite_symb_exec_r
                     [OF threadGet_inv no_fail_threadGet])
       apply (rename_tac thread msgInfo ptr tcbFault)
       apply (rule monadic_rewrite_alternative_rhs[rotated])
        apply (rule monadic_rewrite_alternative_l)
       apply (rule monadic_rewrite_if_rhs[rotated])
        apply (rule monadic_rewrite_alternative_l)
       apply (simp add: split_def Syscall_H.syscall_def
                        liftE_bindE_handle bind_assoc
                        capFaultOnFailure_def)
       apply (simp only: bindE_bind_linearise[where f="rethrowFailure fn f'" for fn f']
                         bind_case_sum_rethrow)
       apply (simp add: lookupCapAndSlot_def lookupSlotForThread_def
                        lookupSlotForThread_def bindE_assoc
                        liftE_bind_return_bindE_returnOk split_def
                        getThreadCSpaceRoot_def locateSlot_conv
                        returnOk_liftE[symmetric] const_def
                        getSlotCap_def)
       apply (simp only: liftE_bindE_assoc)
       apply (rule monadic_rewrite_rdonly_bind_l, wp)
       apply (rule monadic_rewrite_bind_tail)
        apply (rule monadic_rewrite_rdonly_bind_l)
         apply (wp | simp)+
        apply (rule_tac fn="case_sum Inl (Inr \<circ> fst)" in monadic_rewrite_split_fn)
          apply (simp add: liftME_liftM[symmetric] liftME_def bindE_assoc)
          apply (rule monadic_rewrite_refl)
         apply (rule monadic_rewrite_if_rhs[rotated])
          apply (rule monadic_rewrite_alternative_l)
         apply (simp add: isRight_right_map isRight_case_sum)
         apply (rule monadic_rewrite_if_rhs[rotated])
          apply (rule monadic_rewrite_alternative_l)
         apply (rule monadic_rewrite_rdonly_bind_l[OF lookupIPC_inv])
         apply (rule monadic_rewrite_symb_exec_l[OF lookupIPC_inv empty_fail_lookupIPCBuffer])
          apply (simp add: lookupExtraCaps_null returnOk_bind liftE_bindE_handle
                           bind_assoc liftE_bindE_assoc
                           decodeInvocation_def Let_def from_bool_0
                           performInvocation_def liftE_handle
                           liftE_bind)
          apply (rule monadic_rewrite_symb_exec_r [OF getEndpoint_inv no_fail_getEndpoint])
           apply (rename_tac "send_ep")
           apply (rule monadic_rewrite_if_rhs[rotated])
            apply (rule monadic_rewrite_alternative_l)
           apply (simp add: getThreadVSpaceRoot_def locateSlot_conv)
           apply (rule monadic_rewrite_symb_exec_r [OF getCTE_inv no_fail_getCTE])
            apply (rename_tac "pdCapCTE")
            apply (rule monadic_rewrite_if_rhs[rotated])
             apply (rule monadic_rewrite_alternative_l)
            apply (rule monadic_rewrite_symb_exec_r[OF curDomain_inv],
                   simp only: curDomain_def, rule non_fail_gets)
             apply (rename_tac "curDom")
             apply (rule monadic_rewrite_symb_exec_r [OF threadGet_inv no_fail_threadGet])+
               apply (rename_tac curPrio destPrio)
               apply (simp add: isHighestPrio_def')
               apply (rule monadic_rewrite_symb_exec_r [OF gets_inv non_fail_gets])
                apply (rename_tac highest)
                apply (rule monadic_rewrite_if_rhs[rotated])
                 apply (rule monadic_rewrite_alternative_l)
                apply (rule monadic_rewrite_if_rhs[rotated])
                 apply (rule monadic_rewrite_alternative_l)
                apply (simp add: isRight_case_sum)
                apply (rule monadic_rewrite_symb_exec_r [OF gets_inv non_fail_gets])
                 apply (rename_tac asidMap)
                 apply (rule monadic_rewrite_if_rhs[rotated])
                  apply (rule monadic_rewrite_alternative_l)

                 apply (rule monadic_rewrite_symb_exec_r[OF threadGet_inv no_fail_threadGet])
                  apply (rename_tac "destDom")
                  apply (rule monadic_rewrite_if_rhs[rotated])
                   apply (rule monadic_rewrite_alternative_l)
                  apply (rule monadic_rewrite_trans,
                         rule monadic_rewrite_pick_alternative_1)
                  apply (rule monadic_rewrite_symb_exec_l[OF get_mrs_inv' empty_fail_getMRs])
                   (* now committed to fastpath *)
                   apply (rule monadic_rewrite_trans)
                    apply (rule_tac F=True and E=True in monadic_rewrite_weaken)
                    apply simp
                    apply (rule monadic_rewrite_bind_tail)
                     apply (rule_tac x=thread in monadic_rewrite_symb_exec,
                            (wp empty_fail_getCurThread)+)
                     apply (simp add: sendIPC_def bind_assoc)
                     apply (rule_tac x=send_ep in monadic_rewrite_symb_exec,
                            (wp empty_fail_getEndpoint getEndpoint_obj_at')+)
                     apply (rule_tac P="epQueue send_ep \<noteq> []" in monadic_rewrite_gen_asm)
                     apply (simp add: isRecvEP_endpoint_case list_case_helper bind_assoc)
                     apply (rule monadic_rewrite_bind_tail)
                      apply (elim conjE)
                      apply (rule monadic_rewrite_bind_tail, rename_tac dest_st)
                      apply (rule_tac P="\<exists>gr. dest_st = BlockedOnReceive (capEPPtr (fst (theRight rv))) gr"
                               in monadic_rewrite_gen_asm)
                      apply (rule monadic_rewrite_symb_exec2, (wp | simp)+)
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
                           apply (rule_tac x=BlockedOnReply in monadic_rewrite_symb_exec,
                                  (wp empty_fail_getThreadState)+)
                           apply simp
                           apply (rule monadic_rewrite_refl)
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
                         apply (wp fastpathBestSwitchCandidate_lift[where f="threadSet f t" for f t])
                          apply simp
                         apply ((wp assert_inv threadSet_pred_tcb_at_state
                                    cteInsert_obj_at'_not_queued
                                 | wps)+)[1]
                        apply (simp add: setSchedulerAction_def)
                        apply wp[1]
                       apply (simp cong: if_cong conj_cong add: if_bool_simps)
                       apply (simp_all only:)[5]
                       apply ((wp setThreadState_oa_queued[of _ "\<lambda>a _ _. \<not> a"]
                                  setThreadState_obj_at_unchanged
                                  asUser_obj_at_unchanged mapM_x_wp'
                                  sts_st_tcb_at'_cases
                                  setThreadState_no_sch_change
                                  setEndpoint_obj_at_tcb'
                                  fastpathBestSwitchCandidate_lift[where f="setThreadState f t" for f t]
                                  setThreadState_oa_queued
                                  fastpathBestSwitchCandidate_lift[where f="asUser t f" for f t]
                                  fastpathBestSwitchCandidate_lift[where f="setEndpoint a b" for a b]
                                  lookupBitmapPriority_lift
                                  setThreadState_runnable_bitmap_inv
                                | simp add: setMessageInfo_def
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

                 apply (simp add: ARM_H.switchToThread_def bind_assoc)
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
                    apply (rule monadic_rewrite_weaken[where F=False and E=True], simp)
                    apply (rule isolate_thread_actions_rewrite_bind
                                  fastpath_isolate_rewrites fastpath_isolatables
                                  bool.simps setRegister_simple
                                  setVMRoot_isolatable[THEN thread_actions_isolatableD] setVMRoot_isolatable
                                  doMachineOp_isolatable[THEN thread_actions_isolatableD] doMachineOp_isolatable
                                  kernelExitAssertions_isolatable[THEN thread_actions_isolatableD]
                                  kernelExitAssertions_isolatable
                                  zipWithM_setRegister_simple
                                  thread_actions_isolatable_bind
                              | assumption
                              | wp assert_inv)+
                  apply (rule_tac P="\<lambda>s. ksSchedulerAction s = ResumeCurrentThread
                                      \<and> tcb_at' thread s"
                             and F=True and E=False in monadic_rewrite_weaken)
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
                                   ARM.badgeRegister_def
                                   ARM.msgInfoRegister_def
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
                        n_msgRegisters_def order_less_imp_le
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
  apply (frule_tac t="blockedThread" in valid_queues_not_runnable_not_queued, assumption)
  subgoal by (fastforce simp: st_tcb_at'_def elim: obj_at'_weakenE)
  apply (subgoal_tac "fastpathBestSwitchCandidate blockedThread s")
   prefer 2
   apply (rule_tac ttcb=tcbb and ctcb=tcb in fastpathBestSwitchCandidateI)
     apply (solves \<open>simp only: disj_ac\<close>)
    apply simp+
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def objBits_simps projectKOs
      valid_mdb'_def valid_mdb_ctes_def inj_case_bool
      split: bool.split)+
  done

lemmas fastpath_call_ccorres_callKernel
    = monadic_rewrite_ccorres_assemble[OF fastpath_call_ccorres fastpath_callKernel_SysCall_corres]

lemma capability_case_Null_ReplyCap:
  "(case cap of NullCap \<Rightarrow> f | ReplyCap t b cg \<Rightarrow> g t b cg | _ \<Rightarrow> h)
     = (if isReplyCap cap then g (capTCBPtr cap) (capReplyMaster cap) (capReplyCanGrant cap)
             else if isNullCap cap then f else h)"
  by (simp add: isCap_simps split: capability.split)

end

context begin interpretation Arch . (*FIXME: arch_split*)

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
        apply (rule monadic_rewrite_symb_exec_l, (wp empty_fail_threadGet)+)
         apply (rule_tac P="rv = None" in monadic_rewrite_gen_asm, simp)
         apply (rule monadic_rewrite_refl)
        apply (wp threadGet_const gts_wp' getCTE_wp')+
  apply (simp add: o_def)
  done

lemma monadic_rewrite_if_known:
  "monadic_rewrite F E ((\<lambda>s. C = X) and \<top>) (if C then f else g) (if X then f else g)"
  apply (rule monadic_rewrite_gen_asm)
  apply (simp split del: if_split)
  apply (rule monadic_rewrite_refl)
  done

end

context kernel_m begin

lemma receiveIPC_simple_rewrite:
  "monadic_rewrite True False
     ((\<lambda>_. isEndpointCap ep_cap \<and> \<not> isSendEP ep) and (ko_at' ep (capEPPtr ep_cap) and
      (\<lambda>s. \<forall>ntfnptr. bound_tcb_at' ((=) (Some ntfnptr)) thread s \<longrightarrow> obj_at' (Not \<circ> isActive) ntfnptr s)))
     (receiveIPC thread ep_cap True)
     (do
       setThreadState (BlockedOnReceive (capEPPtr ep_cap) (capEPCanGrant ep_cap)) thread;
       setEndpoint (capEPPtr ep_cap) (RecvEP (case ep of RecvEP q \<Rightarrow> (q @ [thread]) | _ \<Rightarrow> [thread]))
      od)"
  apply (rule monadic_rewrite_gen_asm)
  apply (simp add: receiveIPC_def)
  apply (rule monadic_rewrite_imp)
   apply (rule_tac rv=ep in monadic_rewrite_symb_exec_l_known,
          (wp empty_fail_getEndpoint)+)
    apply (rule monadic_rewrite_symb_exec_l, (wp | simp add: getBoundNotification_def)+)
     apply (rule monadic_rewrite_symb_exec_l)
        apply (rule hoare_pre, wpc, wp+, simp)
       apply (simp split: option.split)
      apply (rule monadic_rewrite_trans, rule monadic_rewrite_if_known[where X=False], simp)
      apply (rule monadic_rewrite_refl3[where P=\<top>])
      apply (cases ep, simp_all add: isSendEP_def)[1]
     apply (wp getNotification_wp gbn_wp' getEndpoint_wp | wpc)+
  apply (clarsimp simp: obj_at'_def projectKOs pred_tcb_at'_def)
  done

lemma empty_fail_isFinalCapability:
  "empty_fail (isFinalCapability cte)"
  by (simp add: isFinalCapability_def Let_def split: if_split)

lemma cteDeleteOne_replycap_rewrite:
  "monadic_rewrite True False
     (cte_wp_at' (\<lambda>cte. isReplyCap (cteCap cte)) slot)
     (cteDeleteOne slot)
     (emptySlot slot NullCap)"
  apply (simp add: cteDeleteOne_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_symb_exec_l, (wp empty_fail_getCTE)+)
    apply (rule_tac P="cteCap rv \<noteq> NullCap \<and> isReplyCap (cteCap rv)
                          \<and> \<not> isEndpointCap (cteCap rv)
                          \<and> \<not> isNotificationCap (cteCap rv)"
             in monadic_rewrite_gen_asm)
    apply (simp add: finaliseCapTrue_standin_def
                     capRemovable_def)
    apply (rule monadic_rewrite_symb_exec_l,
           (wp isFinalCapability_inv empty_fail_isFinalCapability)+)
     apply (rule monadic_rewrite_refl)
    apply (wp getCTE_wp')+
  apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps)
  done

lemma cteDeleteOne_nullcap_rewrite:
  "monadic_rewrite True False
     (cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) slot)
     (cteDeleteOne slot)
     (return ())"
  apply (simp add: cteDeleteOne_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_symb_exec_l, (wp empty_fail_getCTE)+)
    apply (rule_tac P="cteCap rv = NullCap" in monadic_rewrite_gen_asm)
    apply simp
    apply (rule monadic_rewrite_refl)
   apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma deleteCallerCap_nullcap_rewrite:
  "monadic_rewrite True False
     (cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) (thread + 2 ^ cte_level_bits * tcbCallerSlot))
     (deleteCallerCap thread)
     (return ())"
  apply (simp add: deleteCallerCap_def getThreadCallerSlot_def locateSlot_conv
                   getSlotCap_def)
  apply (rule monadic_rewrite_imp)
  apply (rule monadic_rewrite_symb_exec_l, (wp empty_fail_getCTE)+)
    apply (rule monadic_rewrite_assert)
    apply (rule cteDeleteOne_nullcap_rewrite)
   apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

end

lemma emptySlot_cnode_caps:
  "\<lbrace>\<lambda>s. P (only_cnode_caps (ctes_of s)) \<and> cte_wp_at' (\<lambda>cte. \<not> isCNodeCap (cteCap cte)) slot s\<rbrace>
     emptySlot slot NullCap
   \<lbrace>\<lambda>rv s. P (only_cnode_caps (ctes_of s))\<rbrace>"
  apply (simp add: only_cnode_caps_def map_option_comp2
                   o_assoc[symmetric] cteCaps_of_def[symmetric])
  apply (wp emptySlot_cteCaps_of)
  apply (clarsimp simp: cteCaps_of_def cte_wp_at_ctes_of
                 elim!: rsubst[where P=P] intro!: ext
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

crunch obj_at_ep[wp]: emptySlot "obj_at' (P :: endpoint \<Rightarrow> bool) p"

crunch nosch[wp]: emptySlot "\<lambda>s. P (ksSchedulerAction s)"

context begin interpretation Arch .
crunches emptySlot, asUser
  for gsCNodes[wp]: "\<lambda>s. P (gsCNodes s)"
  (wp: crunch_wps)
end

crunch cte_wp_at'[wp]: possibleSwitchTo "cte_wp_at' P p"
  (wp: hoare_drop_imps)

crunch tcbContext[wp]: possibleSwitchTo "obj_at' (\<lambda>tcb. P ( (atcbContextGet o tcbArch) tcb)) t"
  (wp: crunch_wps simp_del: comp_apply)

crunch only_cnode_caps[wp]: doFaultTransfer "\<lambda>s. P (only_cnode_caps (ctes_of s))"
  (wp: crunch_wps simp: crunch_simps)

context kernel_m begin

lemma tcbSchedDequeue_rewrite_not_queued: "monadic_rewrite True False (tcb_at' t and obj_at' (Not \<circ> tcbQueued) t) (tcbSchedDequeue t) (return ())"
  apply (simp add: tcbSchedDequeue_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule_tac P="\<not> queued" in monadic_rewrite_gen_asm)
     apply (simp add: when_def)
     apply (rule monadic_rewrite_refl)
    apply (wp threadGet_const)

   apply (rule monadic_rewrite_symb_exec_l)
      apply wp+
    apply (rule monadic_rewrite_refl)
   apply (wp)
  apply (clarsimp simp: o_def obj_at'_def)
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
  apply (simp add: schedule_def)
  apply (simp only: switchToThread_def)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_bind_tail)
      apply (rule_tac P="action = SwitchToThread t" in monadic_rewrite_gen_asm, simp)
      apply (rule monadic_rewrite_bind_tail)
       apply (rule_tac P="\<not> wasRunnable \<and> action = SwitchToThread t" in monadic_rewrite_gen_asm,simp)
       apply (rule monadic_rewrite_bind_tail, rename_tac idleThread)
        apply (rule monadic_rewrite_bind_tail, rename_tac targetPrio)
        apply (rule monadic_rewrite_bind_tail, rename_tac curPrio)
         apply (rule monadic_rewrite_bind_tail, rename_tac fastfail)
          apply (rule monadic_rewrite_bind_tail, rename_tac curDom)
           apply (rule monadic_rewrite_bind_tail, rename_tac highest)
            apply (rule_tac P="\<not> (fastfail \<and> \<not> highest)" in monadic_rewrite_gen_asm, simp only:)
            apply simp
            apply (simp add: bind_assoc)
            apply (rule monadic_rewrite_bind_tail)
             apply (rule monadic_rewrite_bind)
               apply (rule monadic_rewrite_trans)
                apply (rule tcbSchedDequeue_rewrite_not_queued)
               apply (rule monadic_rewrite_refl)
              apply (rule monadic_rewrite_bind_tail)
               apply (rule monadic_rewrite_refl)
              apply (wpsimp wp: Arch_switchToThread_obj_at_pre)+
           apply (wp hoare_vcg_imp_lift)+
            apply (simp add: isHighestPrio_def')
            apply wp+
         apply (wp hoare_vcg_disj_lift)
           apply (wp scheduleSwitchThreadFastfail_False_wp)
          apply wp+
        apply (wp hoare_vcg_disj_lift threadGet_wp'')
        apply (wp hoare_vcg_disj_lift threadGet_wp'')
       apply clarsimp
       apply wp
      apply (simp add: comp_def)
      apply wp
     apply wp
    apply wp
   (* remove no-ops, somewhat by magic *)
   apply (rule monadic_rewrite_symb_exec_l'_TT, solves wp,
      wpsimp wp: empty_fail_isRunnable simp: isHighestPrio_def')+
           apply (rule monadic_rewrite_trans)
            apply (rule monadic_rewrite_bind_tail)
             apply (rule monadic_rewrite_symb_exec_l)
                apply simp+
              apply (rule monadic_rewrite_refl)
             apply wp+
           apply (rule monadic_rewrite_refl)
          apply wp+
  apply (clarsimp simp: ct_in_state'_def)
  apply (rule conjI)
   apply (rule not_pred_tcb_at'_strengthen, assumption)
  apply normalise_obj_at'
  apply (simp add: fastpathBestSwitchCandidate_def)
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
                   exec_modify update_ep_map_tos
            split: if_split option.split)
  done

lemma setEndpoint_setCTE_pivot[unfolded K_bind_def]:
  "do setEndpoint p val; setCTE slot cte; f od =
     do setCTE slot cte; setEndpoint p val; f od"
  apply (rule monadic_rewrite_to_eq)
  apply simp
  apply (rule monadic_rewrite_imp)
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
                   in monadic_rewrite_refl3)
      apply (simp add: setEndpoint_def setObject_modify_assert bind_assoc
                       exec_gets assert_def exec_modify
                split: if_split)
      apply (auto split: if_split simp: obj_at'_def projectKOs objBits_defs
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
  apply simp
  apply (rule monadic_rewrite_to_eq)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_bind_tail)
    apply (simp add: getCTE_assert_opt bind_assoc)
    apply (rule monadic_rewrite_trans,
           rule_tac rv="Some cte" in monadic_rewrite_gets_known)
    apply (simp add: assert_opt_def)
    apply (rule monadic_rewrite_refl)
   apply wp
  apply simp
  done

lemma set_setCTE[unfolded K_bind_def]:
  "do setCTE p val; setCTE p val' od = setCTE p val'"
  apply simp
  apply (rule monadic_rewrite_to_eq)
  apply (rule monadic_rewrite_imp)
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
       apply (rule monadic_rewrite_refl2)
       apply (simp add: exec_modify split: if_split)
       apply (auto simp: simpler_modify_def projectKO_opt_tcb objBits_defs
                 intro!: kernel_state.fold_congs ext
                  split: if_split)[1]
      apply wp+
  apply (clarsimp simp: objBits_defs intro!: all_tcbI)
  apply (auto simp: tcb_cte_cases_def split: if_split_asm)
  done

lemma setCTE_updateCapMDB:
  "p \<noteq> 0 \<Longrightarrow>
   setCTE p cte = do updateCap p (cteCap cte); updateMDB p (const (cteMDBNode cte)) od"
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
  apply (rule monadic_rewrite_imp)
   apply (rule_tac rv=cte in monadic_rewrite_symb_exec_l_known, wp+)
    apply (simp split: capability.split,
      strengthen monadic_rewrite_refl, simp)
    apply clarsimp
   apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of)
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
  apply (rule monadic_rewrite_gen_asm)+
  apply (rule monadic_rewrite_imp)
   apply (rule_tac P="slot \<noteq> 0" in monadic_rewrite_gen_asm)
   apply (clarsimp simp: emptySlot_def setCTE_updateCapMDB)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_head)
    apply (rule clearUntypedFreeIndex_simple_rewrite)
   apply simp
   apply (rule_tac rv=cte in monadic_rewrite_symb_exec_l_known, (wp empty_fail_getCTE)+)
    apply (simp add: updateMDB_def Let_def bind_assoc makeObject_cte case_Null_If)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_bind)
       apply (rule_tac P="mdbFirstBadged (cteMDBNode ctea) \<and> mdbRevocable (cteMDBNode ctea)"
                   in monadic_rewrite_gen_asm)
       apply (rule monadic_rewrite_refl2)
       apply (case_tac ctea, rename_tac mdbnode, case_tac mdbnode)
       apply simp
      apply (simp add: Retype_H.postCapDeletion_def)
      apply (rule monadic_rewrite_refl)
     apply (wp getCTE_wp')+
  apply (clarsimp simp: cte_wp_at_ctes_of reply_masters_rvk_fb_def)
  apply (fastforce simp: isCap_simps)
  done

lemma all_prio_not_inQ_not_tcbQueued: "\<lbrakk> obj_at' (\<lambda>a. (\<forall>d p. \<not> inQ d p a)) t s \<rbrakk> \<Longrightarrow> obj_at' (\<lambda>a. \<not> tcbQueued a) t s"
  apply (clarsimp simp: obj_at'_def inQ_def)
done

crunches setThreadState, emptySlot, asUser
  for ntfn_obj_at[wp]: "obj_at' (P::(Structures_H.notification \<Rightarrow> bool)) ntfnptr"
  (wp: obj_at_setObject2 crunch_wps
   simp: crunch_simps updateObject_default_def in_monad)

lemma st_tcb_at_is_Reply_imp_not_tcbQueued: "\<And>s t.\<lbrakk> invs' s; st_tcb_at' isReply t s\<rbrakk> \<Longrightarrow> obj_at' (\<lambda>a. \<not> tcbQueued a) t s"
  apply (clarsimp simp: invs'_def valid_state'_def valid_queues_def st_tcb_at'_def valid_queues_no_bitmap_def)
  apply (rule all_prio_not_inQ_not_tcbQueued)
  apply (clarsimp simp: obj_at'_def)
  apply (erule_tac x="d" in allE)
  apply (erule_tac x="p" in allE)
  apply (erule conjE)
  apply (erule_tac x="t" in ballE)
   apply (clarsimp simp: obj_at'_def runnable'_def isReply_def)
   apply (case_tac "tcbState obj")
          apply ((clarsimp simp: inQ_def)+)[8]
  apply (clarsimp simp: valid_queues'_def obj_at'_def)
done

lemma valid_objs_ntfn_at_tcbBoundNotification:
  "ko_at' tcb t s \<Longrightarrow> valid_objs' s \<Longrightarrow> tcbBoundNotification tcb \<noteq> None
    \<Longrightarrow> ntfn_at' (the (tcbBoundNotification tcb)) s"
  apply (drule(1) ko_at_valid_objs', simp add: projectKOs)
  apply (simp add: valid_obj'_def valid_tcb'_def valid_bound_ntfn'_def)
  apply clarsimp
  done

crunch bound_tcb_at'_Q[wp]: setThreadState "\<lambda>s. Q (bound_tcb_at' P t s)"
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
  apply (rule monadic_rewrite_imp, rule resolveAddressBitsFn_eq)
  apply auto
  done

crunch bound_tcb_at'_Q[wp]: asUser "\<lambda>s. Q (bound_tcb_at' P t s)"
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
  apply (simp add: tcbSchedEnqueue_def unless_when)
  apply (wp threadSet_obj_at' hoare_drop_imps threadGet_wp
        |simp split: if_split)+
  done

crunch obj_at'_tcbIPCBuffer[wp]: rescheduleRequired "obj_at' (\<lambda>tcb. P (tcbIPCBuffer tcb)) t"
  (wp: crunch_wps tcbSchedEnqueue_tcbIPCBuffer simp: rescheduleRequired_def)

context
notes if_cong[cong]
begin
crunch obj_at'_tcbIPCBuffer[wp]: setThreadState "obj_at' (\<lambda>tcb. P (tcbIPCBuffer tcb)) t"
  (wp: crunch_wps threadSet_obj_at'_really_strongest)

crunch obj_at'_tcbIPCBuffer[wp]: handleFault "obj_at' (\<lambda>tcb. P (tcbIPCBuffer tcb)) t"
  (wp: crunch_wps constOnFailure_wp tcbSchedEnqueue_tcbIPCBuffer threadSet_obj_at'_really_strongest
   simp: zipWithM_x_mapM)
end

crunch obj_at'_tcbIPCBuffer[wp]: emptySlot "obj_at' (\<lambda>tcb. P (tcbIPCBuffer tcb)) t"
  (wp: crunch_wps)

lemma fastpath_callKernel_SysReplyRecv_corres:
  "monadic_rewrite True False
     (invs' and ct_in_state' ((=) Running) and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
         and cnode_caps_gsCNodes')
     (callKernel (SyscallEvent SysReplyRecv)) (fastpaths SysReplyRecv)"
  including no_pre
  supply option.case_cong_weak[cong del]
  supply if_cong[cong]
  apply (rule monadic_rewrite_introduce_alternative)
   apply (simp add: callKernel_def)
  apply (rule monadic_rewrite_imp)
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
   apply (rule monadic_rewrite_rdonly_bind_l, wp)
   apply (rule monadic_rewrite_bind_tail)
    apply (rule monadic_rewrite_symb_exec_r, wp+)
     apply (rename_tac thread msgInfo)
     apply (rule monadic_rewrite_symb_exec_r, wp+)
      apply (rename_tac cptr)
      apply (rule monadic_rewrite_symb_exec_r[OF threadGet_inv no_fail_threadGet])
       apply (rename_tac tcbFault)
       apply (rule monadic_rewrite_alternative_rhs[rotated])
        apply (rule monadic_rewrite_alternative_l)
       apply (rule monadic_rewrite_if_rhs[rotated])
        apply (rule monadic_rewrite_alternative_l)
       apply (simp add: lookupCap_def liftME_def lookupCapAndSlot_def
                        lookupSlotForThread_def bindE_assoc
                        split_def getThreadCSpaceRoot_def
                        locateSlot_conv liftE_bindE bindE_bind_linearise
                        capFaultOnFailure_def rethrowFailure_injection
                        injection_handler_catch bind_bindE_assoc
                        getThreadCallerSlot_def bind_assoc
                        getSlotCap_def
                        case_bool_If o_def
                        isRight_def[where x="Inr v" for v]
                        isRight_def[where x="Inl v" for v]
                  cong: if_cong)
       apply (rule monadic_rewrite_symb_exec_r, wp+)
        apply (rename_tac "cTableCTE")

        apply (rule monadic_rewrite_transverse,
               rule monadic_rewrite_bind_head,
               rule resolveAddressBitsFn_eq)
        apply (rule monadic_rewrite_symb_exec_r, (wp | simp)+)
         apply (rename_tac "rab_ret")

         apply (rule_tac P="isRight rab_ret" in monadic_rewrite_cases[rotated])
          apply (case_tac rab_ret, simp_all add: isRight_def)[1]
          apply (rule monadic_rewrite_alternative_l)
         apply clarsimp
         apply (simp add: isRight_case_sum liftE_bind
                          isRight_def[where x="Inr v" for v])
         apply (rule monadic_rewrite_symb_exec_r, wp+)
          apply (rename_tac ep_cap)
          apply (rule monadic_rewrite_if_rhs[rotated])
           apply (rule monadic_rewrite_alternative_l)
            apply (rule monadic_rewrite_symb_exec_r[OF _ _ _ active_ntfn_check_wp, unfolded bind_assoc fun_app_def])
            apply (rule hoare_pre, (wp | wpc | simp)+)[1]
           apply (unfold getBoundNotification_def)[1]
           apply (wp threadGet_wp)
          apply (rename_tac ep)
          apply (rule monadic_rewrite_if_rhs[rotated])
           apply (rule monadic_rewrite_alternative_l)
          apply (rule monadic_rewrite_symb_exec_r, wp+)
           apply (rename_tac ep)
           apply (rule monadic_rewrite_if_rhs[rotated])
            apply (rule monadic_rewrite_alternative_l)
           apply (rule monadic_rewrite_rdonly_bind_l, wp)
           apply (rule monadic_rewrite_bind_tail)
            apply (rename_tac replyCTE)
            apply (rule monadic_rewrite_if_rhs[rotated])
             apply (rule monadic_rewrite_alternative_l)
            apply (simp add: bind_assoc)
            apply (rule monadic_rewrite_rdonly_bind_l, wp assert_inv)
            apply (rule monadic_rewrite_assert)
            apply (rule monadic_rewrite_symb_exec_r, wp+)
             apply (rename_tac callerFault)
             apply (rule monadic_rewrite_if_rhs[rotated])
              apply (rule monadic_rewrite_alternative_l)
             apply (simp add: getThreadVSpaceRoot_def locateSlot_conv)
             apply (rule monadic_rewrite_symb_exec_r, wp+)
              apply (rename_tac vTableCTE)
              apply (rule monadic_rewrite_if_rhs[rotated])
               apply (rule monadic_rewrite_alternative_l)

                apply (rule monadic_rewrite_symb_exec_r[OF curDomain_inv],
                        simp only: curDomain_def, rule non_fail_gets)
                 apply (rename_tac "curDom")
                apply (rule monadic_rewrite_symb_exec_r
                         [OF threadGet_inv no_fail_threadGet])
                apply (rename_tac callerPrio)
                apply (simp add: isHighestPrio_def')
               apply (rule monadic_rewrite_symb_exec_r [OF gets_inv non_fail_gets])
               apply (rename_tac highest)
           apply (rule monadic_rewrite_if_rhs[rotated])
            apply (rule monadic_rewrite_alternative_l)

              apply (rule monadic_rewrite_symb_exec_r, wp+)
                apply (rename_tac asidMap)
              apply (rule monadic_rewrite_if_rhs[rotated])
               apply (rule monadic_rewrite_alternative_l)
                  apply (rule monadic_rewrite_symb_exec_r[OF threadGet_inv no_fail_threadGet])
                   apply (rename_tac "callerDom")
                   apply (rule monadic_rewrite_if_rhs[rotated])
                    apply (rule monadic_rewrite_alternative_l)
                   apply (rule monadic_rewrite_trans,
                              rule monadic_rewrite_pick_alternative_1)
                    apply (rule_tac P="\<lambda>v.  obj_at' (%tcb. tcbIPCBuffer tcb = v) (capTCBPtr (cteCap replyCTE))"
                          in monadic_rewrite_exists_v)
                    apply (rename_tac ipcBuffer)

                    apply (simp add: ARM_H.switchToThread_def bind_assoc)
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
                     apply (((rule monadic_rewrite_weaken2,
                             (rule_tac msgInfo=msgInfo in doIPCTransfer_simple_rewrite
                           | rule_tac destPrio=callerPrio
                                            and curDom=curDom and destDom=callerDom
                                            and thread=thread in possibleSwitchTo_rewrite))
                           | rule cteDeleteOne_replycap_rewrite
                           | rule monadic_rewrite_bind monadic_rewrite_refl
                           | wp assert_inv mapM_x_wp'
                                setThreadState_obj_at_unchanged
                                asUser_obj_at_unchanged
                                hoare_strengthen_post[OF _ obj_at_conj'[simplified atomize_conjL], rotated]
                                lookupBitmapPriority_lift
                                setThreadState_runnable_bitmap_inv
                           | simp add: setMessageInfo_def setThreadState_runnable_simp
                           | wp (once) hoare_vcg_disj_lift)+)[1]
                    apply (simp add: setMessageInfo_def)
                    apply (rule monadic_rewrite_bind_tail)
                    apply (rename_tac unblocked)
                     apply (rule_tac rv=thread in monadic_rewrite_symb_exec_l_known,
                                       (wp empty_fail_getCurThread)+)
                      apply (rule_tac rv=cptr in monadic_rewrite_symb_exec_l_known,
                                       (wp empty_fail_asUser empty_fail_getRegister)+)
                       apply (rule monadic_rewrite_bind)
                         apply (rule monadic_rewrite_catch[OF _ monadic_rewrite_refl True_E_E])
                         apply (rule monadic_rewrite_symb_exec_l, (wp empty_fail_getCTE)+)
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
                                 in monadic_rewrite_gets_known[where m="NonDetMonad.lift f"
                                    for f, folded bindE_def])
                          apply (simp add: NonDetMonad.lift_def isRight_case_sum)
                          apply (rule monadic_rewrite_symb_exec_l, (wp empty_fail_getCTE)+)
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

                           apply (rule monadic_rewrite_weaken[where E=True and F=True], simp)
                           apply (rule setThreadState_rewrite_simple)
                          apply clarsimp
                          apply (wp getCTE_known_cap)+
                        apply (rule monadic_rewrite_bind)
                          apply (rule_tac t="capTCBPtr (cteCap replyCTE)"
                                      and t'=thread
                                       in schedule_known_rewrite)
                         apply (rule monadic_rewrite_weaken[where E=True and F=True], simp)
                         apply (rule monadic_rewrite_bind)
                           apply (rule activateThread_simple_rewrite)
                          apply (rule monadic_rewrite_refl)
                         apply wp
                        apply wp
                         apply (simp add: ct_in_state'_def, simp add: ct_in_state'_def[symmetric])
                         apply ((wp setCurThread_ct_in_state[folded st_tcb_at'_def]
                                    Arch_switchToThread_pred_tcb')+)[2]
                       apply (simp add: catch_liftE)
                       apply (wp setEndpoint_obj_at_tcb' threadSet_pred_tcb_at_state[unfolded if_bool_eq_conj])

                       apply (wp setEndpoint_obj_at_tcb'
                                 threadSet_pred_tcb_at_state[unfolded if_bool_eq_conj]
                                 fastpathBestSwitchCandidate_lift[where f="setEndpoint a b" for a b]
                                 fastpathBestSwitchCandidate_lift[where f="threadSet f t" for f t]
                              | simp
                              | rule hoare_lift_Pf2[where f=ksCurThread, OF _ setEndpoint_ct']
                                     hoare_lift_Pf2[where f=ksCurThread, OF _ threadSet_ct])+

                      apply (simp cong: rev_conj_cong)
                      apply (strengthen imp_consequent[where Q="tcb_at' t s" for t s])
                      apply (unfold setSchedulerAction_def)[3]
                      apply ((wp setThreadState_oa_queued user_getreg_rv setThreadState_no_sch_change
                                 setThreadState_obj_at_unchanged
                                 sts_st_tcb_at'_cases sts_bound_tcb_at'
                                 emptySlot_obj_at'_not_queued
                                 emptySlot_cte_wp_at_cteCap
                                 emptySlot_cnode_caps
                                 user_getreg_inv asUser_typ_ats
                                 asUser_obj_at_not_queued asUser_obj_at' mapM_x_wp'
                                 static_imp_wp hoare_vcg_all_lift hoare_vcg_imp_lift
                                 static_imp_wp cnode_caps_gsCNodes_lift
                                 hoare_vcg_ex_lift
                             | simp del: comp_apply
                             | clarsimp simp: obj_at'_weakenE[OF _ TrueI])+)

                          apply (rule hoare_lift_Pf2[where f=ksCurThread, OF _ setThreadState_ct'])
                          apply (wp setThreadState_oa_queued
                                    fastpathBestSwitchCandidate_lift[where f="setThreadState f t" for f t])
                          apply (simp add: setThreadState_runnable_simp)
                          apply (wp threadSet_tcbState_st_tcb_at')
                         apply (clarsimp simp del: comp_apply)
                         apply (wp emptySlot_obj_at_ep)+

                         apply ((wp setThreadState_oa_queued user_getreg_rv
                                    setThreadState_no_sch_change
                                    setThreadState_obj_at_unchanged
                                    sts_st_tcb_at'_cases sts_bound_tcb_at'
                                    emptySlot_obj_at'_not_queued
                                    emptySlot_cte_wp_at_cteCap
                                    emptySlot_cnode_caps
                                    user_getreg_inv asUser_typ_ats
                                    asUser_obj_at_not_queued asUser_obj_at' mapM_x_wp'
                                    static_imp_wp hoare_vcg_all_lift hoare_vcg_imp_lift
                                    static_imp_wp cnode_caps_gsCNodes_lift
                                    hoare_vcg_ex_lift
                                | simp del: comp_apply
                                | clarsimp simp: obj_at'_weakenE[OF _ TrueI]
                                | solves \<open>
                                    rule hoare_lift_Pf2[where f=ksCurThread, OF _ emptySlot_ct]
                                         hoare_lift_Pf2[where f=ksCurThread, OF _ asUser_ct],
                                    wp fastpathBestSwitchCandidate_lift[where f="emptySlot a b" for a b]
                                       fastpathBestSwitchCandidate_lift[where f="asUser a b" for a b]
                                       user_getreg_inv asUser_typ_ats\<close>)+)

                        apply (clarsimp | wp getCTE_wp' gts_imp')+

                    apply (simp add: ARM_H.switchToThread_def bind_assoc)
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
                   apply (rule monadic_rewrite_symb_exec_l, (wp empty_fail_getThreadState)+)
                    apply (rule monadic_rewrite_assert)

                    apply (rule_tac P="inj (case_bool thread (capTCBPtr (cteCap replyCTE)))"
                                    in monadic_rewrite_gen_asm)
                    apply (rule monadic_rewrite_trans[OF _ monadic_rewrite_transverse])
                      apply (rule monadic_rewrite_weaken[where F=False and E=True], simp)
                      apply (rule isolate_thread_actions_rewrite_bind
                                  fastpath_isolate_rewrites fastpath_isolatables
                                  bool.simps setRegister_simple
                                  zipWithM_setRegister_simple
                                  thread_actions_isolatable_bind
                                  thread_actions_isolatableD[OF setCTE_isolatable]
                                  setCTE_isolatable
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
                                and F=True and E=False in monadic_rewrite_weaken)
                    apply (rule monadic_rewrite_isolate_final2)
                       apply simp
                       apply (rule monadic_rewrite_symb_exec_l, (wp empty_fail_getCTE)+)
                        apply (rename_tac callerCTE)
                        apply (rule monadic_rewrite_assert)
                        apply (rule monadic_rewrite_symb_exec_l, (wp empty_fail_getCTE)+)
                         apply (rule monadic_rewrite_assert)
                         apply (simp add: emptySlot_setEndpoint_pivot)
                         apply (rule monadic_rewrite_bind)
                           apply (rule monadic_rewrite_refl2)
                           apply (clarsimp simp: isSendEP_def split: Structures_H.endpoint.split)
                          apply (rule_tac Q="\<lambda>rv. (\<lambda>_. rv = callerCTE) and Q'" for Q'
                                              in monadic_rewrite_symb_exec_r, wp+)
                           apply (rule monadic_rewrite_gen_asm, simp)
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
                                       ARM.msgInfoRegister_def
                                       ARM.badgeRegister_def
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
                        n_msgRegisters_def order_less_imp_le
                        tcb_at_invs' invs_mdb'
                 split: bool.split)
  apply (subst imp_disjL[symmetric], intro allI impI)
  apply (clarsimp simp: inj_case_bool cte_wp_at_ctes_of
                        length_msgRegisters
                        n_msgRegisters_def order_less_imp_le
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
  apply (auto simp: obj_at_tcbs_of tcbSlots
                        cte_level_bits_def)
  done

lemmas fastpath_reply_recv_ccorres_callKernel
    = monadic_rewrite_ccorres_assemble[OF fastpath_reply_recv_ccorres fastpath_callKernel_SysReplyRecv_corres]

lemma cnode_caps_gsCNodes_from_sr:
  "valid_objs s \<Longrightarrow> (s, s') \<in> state_relation
    \<Longrightarrow> cnode_caps_gsCNodes' s'"
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

end
