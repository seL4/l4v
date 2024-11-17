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

context begin interpretation Arch . (*FIXME: arch-split*)

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

    vspace_root \<leftarrow> returnOk $ capPTBasePtr $ capCap $ cteCap newVTable; \<comment> \<open>cap_pd in C\<close>
    asid \<leftarrow> returnOk $ fst $ the $ capPTMappedAddress $ capCap $ cteCap newVTable;
    ap_entry_opt \<leftarrow> liftE $ getASIDPoolEntry asid; \<comment> \<open>asid_map_t asid_map in C\<close>
    unlessE (\<exists>ap_entry. ap_entry_opt = Some ap_entry \<and> apVSpace ap_entry = vspace_root
                        \<and> apVMID ap_entry \<noteq> None) \<comment> \<open>C makes VMID check separate\<close>
        $ throwError ();
    \<comment> \<open>C code now saves the VMID from the ap_entry to stored_hw_asid.words[0] and the Haskell does
       nothing, and these need to sync up in the preconditions of switchToThread_fp_ccorres\<close>

    curDom \<leftarrow> liftE $ curDomain;
    curPrio \<leftarrow> liftE $ threadGet tcbPriority curThread;
    destPrio \<leftarrow> liftE $ threadGet tcbPriority dest;
    highest \<leftarrow> liftE $ isHighestPrio curDom destPrio;
    unlessE (destPrio \<ge> curPrio \<or> highest) $ throwError ();
    unlessE (capEPCanGrant epCap \<or> capEPCanGrantReply epCap) $ throwError ();

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
    \<comment> \<open>(* AArch64 does not check whether the caller cap is a ReplyMaster cap, since slow path
          fails in that case. AArch32 C code does perform the redundant check.
          See fastpath_reply_cap_check *)\<close>
    unlessE (isReplyCap callerCap) $ throwError ();

    caller \<leftarrow> returnOk $ capTCBPtr callerCap;
    callerFault \<leftarrow> liftE $ threadGet tcbFault caller;
    unlessE (callerFault = None) $ throwError ();
    newVTable \<leftarrow> liftE $ getThreadVSpaceRoot caller >>= getCTE;
    unlessE (isValidVTableRoot $ cteCap newVTable) $ throwError ();

    vspace_root \<leftarrow> returnOk $ capPTBasePtr $ capCap $ cteCap newVTable; \<comment> \<open>cap_pd in C\<close>
    asid \<leftarrow> returnOk $ fst $ the $ capPTMappedAddress $ capCap $ cteCap newVTable;
    ap_entry_opt \<leftarrow> liftE $ getASIDPoolEntry asid; \<comment> \<open>asid_map_t asid_map in C\<close>
    unlessE (\<exists>ap_entry. ap_entry_opt = Some ap_entry \<and> apVSpace ap_entry = vspace_root
                        \<and> apVMID ap_entry \<noteq> None) \<comment> \<open>C makes VMID check separate\<close>
        $ throwError ();
    \<comment> \<open>C code now saves the VMID from the ap_entry to stored_hw_asid.words[0] and the Haskell does
       nothing, and these need to sync up in the preconditions of switchToThread_fp_ccorres\<close>

    curDom \<leftarrow> liftE $ curDomain;
    callerPrio \<leftarrow> liftE $ threadGet tcbPriority caller;
    highest \<leftarrow> liftE $ isHighestPrio curDom callerPrio;
    unlessE highest $ throwError ();

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
