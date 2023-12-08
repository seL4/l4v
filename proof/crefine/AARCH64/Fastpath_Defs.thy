(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Contains the design specification of optimised fast paths though the kernel.
   These paths check for specific circumstances before engaging, otherwise
   falling back to the full kernel design specification (callKernel).
   For this reason, fastpath + callKernel is expected to be semantically
   identical to callKernel. *)

theory Fastpath_Defs
imports ArchMove_C
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
                \<and> msgLength mi \<le> of_nat size_msgRegisters \<and> pickFastpath)
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

\<comment> \<open> (* FIXME AARCH64 TODO *) AArch64+hyp specific tests
    /* Need to test that the ASID is still valid */
    asid_t asid = cap_vspace_cap_get_capVSMappedASID(newVTable);
    asid_map_t asid_map = findMapForASID(asid);
    if (unlikely(asid_map_get_type(asid_map) != asid_map_asid_map_vspace ||
                 VSPACE_PTR(asid_map_asid_map_vspace_get_vspace_root(asid_map)) != cap_pd)) {
        slowpath(SysCall);
    }
    /* Ensure the vmid is valid. */
    if (unlikely(!asid_map_asid_map_vspace_get_stored_vmid_valid(asid_map))) {
        slowpath(SysCall);
    }
    /* vmids are the tags used instead of hw_asids in hyp mode */
    stored_hw_asid.words[0] = asid_map_asid_map_vspace_get_stored_hw_vmid(asid_map);
\<close>

\<^cancel>\<open> this check appears to only happen on AARCH32
    pd \<leftarrow> returnOk $ \<^cancel>\<open>capPTBasePtr\<close> XXX $ capCap $ cteCap newVTable;
\<close>
    curDom \<leftarrow> liftE $ curDomain;
    curPrio \<leftarrow> liftE $ threadGet tcbPriority curThread;
    destPrio \<leftarrow> liftE $ threadGet tcbPriority dest;
    highest \<leftarrow> liftE $ isHighestPrio curDom destPrio;
    unlessE (destPrio \<ge> curPrio \<or> highest) $ throwError ();
    unlessE (capEPCanGrant epCap \<or> capEPCanGrantReply epCap) $ throwError ();

\<^cancel>\<open> this check appears to only happen on AARCH32
    asidMap \<leftarrow> liftE $ gets $ riscvKSASIDTable o ksArchState;
    unlessE (\<exists>v. {hwasid. (hwasid, pd) \<in> ran asidMap} = {v})
        $ throwError ();
\<close>
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

      forM_x (take (unat (msgLength mi)) msgRegisters)
             (\<lambda>r. do v \<leftarrow> asUser curThread (getRegister r);
                    asUser dest (setRegister r v) od);
      setThreadState Running dest;
      Arch.switchToThread dest;
      setCurThread dest;

      asUser dest $ zipWithM_x setRegister
               [badgeRegister, msgInfoRegister]
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
                \<and> msgLength mi \<le> of_nat size_msgRegisters \<and> pickFastpath)
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

\<comment> \<open> (* FIXME AARCH64 TODO *) AArch64+hyp specific tests
    /* Need to test that the ASID is still valid */
    asid_t asid = cap_vspace_cap_get_capVSMappedASID(newVTable);
    asid_map_t asid_map = findMapForASID(asid);
    if (unlikely(asid_map_get_type(asid_map) != asid_map_asid_map_vspace ||
                 VSPACE_PTR(asid_map_asid_map_vspace_get_vspace_root(asid_map)) != cap_pd)) {
        slowpath(SysReplyRecv);
    }

    /* Ensure the vmid is valid. */
    if (unlikely(!asid_map_asid_map_vspace_get_stored_vmid_valid(asid_map))) {
        slowpath(SysReplyRecv);
    }

    /* vmids are the tags used instead of hw_asids in hyp mode */
    stored_hw_asid.words[0] = asid_map_asid_map_vspace_get_stored_hw_vmid(asid_map);
\<close>

\<^cancel>\<open> this check appears to only happen on AARCH32
    pd \<leftarrow> returnOk $ \<^cancel>\<open>capPTBasePtr\<close> XXX $ capCap $ cteCap newVTable;
    asidMap \<leftarrow> liftE $ gets $ riscvKSASIDTable o ksArchState;
    unlessE (\<exists>v. {hwasid. (hwasid, pd) \<in> ran asidMap} = {v})
        $ throwError ();
\<close>
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

      forM_x (take (unat (msgLength mi)) msgRegisters)
             (\<lambda>r. do v \<leftarrow> asUser curThread (getRegister r);
                    asUser caller (setRegister r v) od);
      setThreadState Running caller;
      Arch.switchToThread caller;
      setCurThread caller;

      asUser caller $ zipWithM_x setRegister
               [badgeRegister, msgInfoRegister]
               [0, wordFromMessageInfo (mi\<lparr> msgCapsUnwrapped := 0 \<rparr>)];

      stateAssert kernelExitAssertions []
    od

  odE <catch> (\<lambda>_. callKernel (SyscallEvent sysc))

  | _ \<Rightarrow> callKernel (SyscallEvent sysc)"

end

end
