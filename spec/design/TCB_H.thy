(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file TCB_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Thread Control Blocks"

theory TCB_H
imports
  NotificationDecls_H
  TCBDecls_H
  CNode_H
  VSpace_H
  "./$L4V_ARCH/ArchTCB_H"
begin

context begin interpretation Arch .
requalify_consts
  decodeTransfer
  gpRegisters
  frameRegisters
  getRegister
  setNextPC
  getRestartPC
  sanitiseRegister
  setRegister
  performTransfer
  msgInfoRegister
  msgRegisters
  tpidrurwRegister
  fromVPtr
end

defs decodeTCBInvocation_def:
"decodeTCBInvocation label args cap slot extraCaps \<equiv>
    (case invocationType label of
          TCBReadRegisters \<Rightarrow>   decodeReadRegisters args cap
        | TCBWriteRegisters \<Rightarrow>   decodeWriteRegisters args cap
        | TCBCopyRegisters \<Rightarrow>   decodeCopyRegisters args cap $ map fst extraCaps
        | TCBSuspend \<Rightarrow>   returnOk $ Suspend (capTCBPtr cap)
        | TCBResume \<Rightarrow>   returnOk $ Resume (capTCBPtr cap)
        | TCBConfigure \<Rightarrow>   decodeTCBConfigure args cap slot extraCaps
        | TCBSetPriority \<Rightarrow>   decodeSetPriority args cap
        | TCBSetMCPriority \<Rightarrow>   decodeSetMCPriority args cap
        | TCBSetIPCBuffer \<Rightarrow>   decodeSetIPCBuffer args cap slot extraCaps
        | TCBSetSpace \<Rightarrow>   decodeSetSpace args cap slot extraCaps
        | TCBBindNotification \<Rightarrow>   decodeBindNotification cap extraCaps
        | TCBUnbindNotification \<Rightarrow>   decodeUnbindNotification cap
        | _ \<Rightarrow>   throw IllegalOperation
        )"

defs decodeCopyRegisters_def:
"decodeCopyRegisters x0 cap extraCaps\<equiv> (case x0 of
    (flags#_) \<Rightarrow>    (doE
    suspendSource \<leftarrow> returnOk ( flags !! 0);
    resumeTarget \<leftarrow> returnOk ( flags !! 1);
    transferFrame \<leftarrow> returnOk ( flags !! 2);
    transferInteger \<leftarrow> returnOk ( flags !! 3);
    transferArch \<leftarrow> decodeTransfer $ fromIntegral $ flags `~shiftR~` 8;
    whenE (null extraCaps) $ throw TruncatedMessage;
    srcTCB \<leftarrow> (case head extraCaps of
          ThreadCap ptr \<Rightarrow>  
            returnOk ptr
        | _ \<Rightarrow>   throw $ InvalidCapability 1
        );
    returnOk CopyRegisters_ \<lparr>
        copyRegsTarget= capTCBPtr cap,
        copyRegsSource= srcTCB,
        copyRegsSuspendSource= suspendSource,
        copyRegsResumeTarget= resumeTarget,
        copyRegsTransferFrame= transferFrame,
        copyRegsTransferInteger= transferInteger,
        copyRegsTransferArch= transferArch \<rparr>
    odE)
  | _ \<Rightarrow>    throw TruncatedMessage
  )"

defs decodeReadRegisters_def:
"decodeReadRegisters x0 cap\<equiv> (case x0 of
    (flags#n#_) \<Rightarrow>    (doE
    rangeCheck n 1 $ length frameRegisters + length gpRegisters;
    transferArch \<leftarrow> decodeTransfer $ fromIntegral $ flags `~shiftR~` 8;
    self \<leftarrow> withoutFailure $ getCurThread;
    whenE (capTCBPtr cap = self) $ throw IllegalOperation;
    returnOk ReadRegisters_ \<lparr>
        readRegsThread= capTCBPtr cap,
        readRegsSuspend= flags !! 0,
        readRegsLength= n,
        readRegsArch= transferArch \<rparr>
    odE)
  | _ \<Rightarrow>    throw TruncatedMessage
  )"

defs decodeWriteRegisters_def:
"decodeWriteRegisters x0 cap\<equiv> (case x0 of
    (flags#n#values) \<Rightarrow>    (doE
    whenE (genericLength values < n) $ throw TruncatedMessage;
    transferArch \<leftarrow> decodeTransfer $ fromIntegral $ flags `~shiftR~` 8;
    self \<leftarrow> withoutFailure $ getCurThread;
    whenE (capTCBPtr cap = self) $ throw IllegalOperation;
    returnOk WriteRegisters_ \<lparr>
        writeRegsThread= capTCBPtr cap,
        writeRegsResume= flags !! 0,
        writeRegsValues= genericTake n values,
        writeRegsArch= transferArch \<rparr>
    odE)
  | _ \<Rightarrow>    throw TruncatedMessage
  )"

defs decodeTCBConfigure_def:
"decodeTCBConfigure x0 cap slot x3\<equiv> (case (x0, x3) of
    ((faultEP#packedPrioProps#cRootData#vRootData#buffer#_), (cRoot#vRoot#bufferFrame#_)) \<Rightarrow>    (doE
    prio \<leftarrow> returnOk ( packedPrioProps && mask priorityBits);
    mcp \<leftarrow> returnOk ( (packedPrioProps `~shiftR~` priorityBits) && mask priorityBits);
    setPriority \<leftarrow> decodeSetPriority [prio] cap;
    setMCP \<leftarrow> decodeSetMCPriority [mcp] cap;
    setIPCParams \<leftarrow> decodeSetIPCBuffer [buffer] cap slot [bufferFrame];
    setSpace \<leftarrow> decodeSetSpace [faultEP, cRootData, vRootData]
        cap slot [cRoot, vRoot];
    returnOk $ ThreadControl_ \<lparr>
        tcThread= capTCBPtr cap,
        tcThreadCapSlot= tcThreadCapSlot setSpace,
        tcNewFaultEP= tcNewFaultEP setSpace,
        tcNewMCPriority= tcNewMCPriority setMCP,
        tcNewPriority= tcNewPriority setPriority,
        tcNewCRoot= tcNewCRoot setSpace,
        tcNewVRoot= tcNewVRoot setSpace,
        tcNewIPCBuffer= tcNewIPCBuffer setIPCParams \<rparr>
    odE)
  | (_, _) \<Rightarrow>    throw TruncatedMessage
  )"

defs checkPrio_def:
"checkPrio prio\<equiv> (doE
    ct \<leftarrow> withoutFailure $ getCurThread;
    mcp \<leftarrow> withoutFailure $ threadGet tcbMCP ct;
    whenE (prio > fromIntegral mcp) $ throw (RangeError (fromIntegral minPriority) (fromIntegral mcp))
odE)"

defs decodeSetPriority_def:
"decodeSetPriority x0 cap\<equiv> (case x0 of
    (newPrio#_) \<Rightarrow>    (doE
    checkPrio newPrio;
    returnOk $ ThreadControl_ \<lparr>
        tcThread= capTCBPtr cap,
        tcThreadCapSlot= 0,
        tcNewFaultEP= Nothing,
        tcNewMCPriority= Nothing,
        tcNewPriority= Just $ fromIntegral newPrio,
        tcNewCRoot= Nothing,
        tcNewVRoot= Nothing,
        tcNewIPCBuffer= Nothing \<rparr>
    odE)
  | _ \<Rightarrow>    throw TruncatedMessage
  )"

defs decodeSetMCPriority_def:
"decodeSetMCPriority x0 cap\<equiv> (case x0 of
    (newMCP#_) \<Rightarrow>    (doE
    checkPrio newMCP;
    returnOk $ ThreadControl_ \<lparr>
        tcThread= capTCBPtr cap,
        tcThreadCapSlot= 0,
        tcNewFaultEP= Nothing,
        tcNewMCPriority= Just $ fromIntegral newMCP,
        tcNewPriority= Nothing,
        tcNewCRoot= Nothing,
        tcNewVRoot= Nothing,
        tcNewIPCBuffer= Nothing \<rparr>
    odE)
  | _ \<Rightarrow>    throw TruncatedMessage
  )"

defs decodeSetIPCBuffer_def:
"decodeSetIPCBuffer x0 cap slot x3\<equiv> (case (x0, x3) of
    ((bufferPtr#_), ((bufferCap, bufferSlot)#_)) \<Rightarrow>    (doE
    ipcBuffer \<leftarrow> returnOk ( VPtr bufferPtr);
    bufferFrame \<leftarrow> if ipcBuffer = 0
        then returnOk Nothing
        else (doE
            bufferCap' \<leftarrow> deriveCap bufferSlot bufferCap;
            checkValidIPCBuffer ipcBuffer bufferCap';
            returnOk $ Just (bufferCap', bufferSlot)
        odE);
    returnOk $ ThreadControl_ \<lparr>
        tcThread= capTCBPtr cap,
        tcThreadCapSlot= slot,
        tcNewFaultEP= Nothing,
        tcNewMCPriority= Nothing,
        tcNewPriority= Nothing,
        tcNewCRoot= Nothing,
        tcNewVRoot= Nothing,
        tcNewIPCBuffer= Just (ipcBuffer, bufferFrame) \<rparr>
    odE)
  | (_, _) \<Rightarrow>    throw TruncatedMessage
  )"

defs decodeSetSpace_def:
"decodeSetSpace x0 cap slot x3\<equiv> (case (x0, x3) of
    ((faultEP#cRootData#vRootData#_), (cRootArg#vRootArg#_)) \<Rightarrow>    (doE
    canChangeCRoot \<leftarrow> withoutFailure $ liftM Not $
        slotCapLongRunningDelete =<< getThreadCSpaceRoot (capTCBPtr cap);
    canChangeVRoot \<leftarrow> withoutFailure $ liftM Not $
        slotCapLongRunningDelete =<< getThreadVSpaceRoot (capTCBPtr cap);
    unlessE (canChangeCRoot \<and> canChangeVRoot) $
        throw IllegalOperation;
    (cRootCap, cRootSlot) \<leftarrow> returnOk ( cRootArg);
    cRootCap' \<leftarrow> deriveCap cRootSlot $ if cRootData = 0
        then cRootCap
        else updateCapData False cRootData cRootCap;
    cRoot \<leftarrow> (case cRootCap' of
          CNodeCap _ _ _ _ \<Rightarrow>   returnOk (cRootCap', cRootSlot)
        | _ \<Rightarrow>   throw IllegalOperation
        );
    (vRootCap, vRootSlot) \<leftarrow> returnOk ( vRootArg);
    vRootCap' \<leftarrow> deriveCap vRootSlot $ if vRootData = 0
        then vRootCap
        else updateCapData False vRootData vRootCap;
    vRoot \<leftarrow> if isValidVTableRoot vRootCap'
        then returnOk (vRootCap', vRootSlot)
        else throw IllegalOperation;
    returnOk $ ThreadControl_ \<lparr>
        tcThread= capTCBPtr cap,
        tcThreadCapSlot= slot,
        tcNewFaultEP= Just $ CPtr faultEP,
        tcNewMCPriority= Nothing,
        tcNewPriority= Nothing,
        tcNewCRoot= Just cRoot,
        tcNewVRoot= Just vRoot,
        tcNewIPCBuffer= Nothing \<rparr>
    odE)
  | (_, _) \<Rightarrow>    throw TruncatedMessage
  )"

defs decodeBindNotification_def:
"decodeBindNotification cap extraCaps\<equiv> (doE
    whenE (null extraCaps) $ throw TruncatedMessage;
    tcb \<leftarrow> returnOk ( capTCBPtr cap);
    ntfn \<leftarrow> withoutFailure $ getBoundNotification tcb;
    (case ntfn of
          Some v11 \<Rightarrow>   throw IllegalOperation
        | None \<Rightarrow>   returnOk ()
        );
    (ntfnPtr, rights) \<leftarrow> (case fst (head extraCaps) of
          NotificationCap ptr v12 v13 recv \<Rightarrow>   returnOk (ptr, recv)
        | _ \<Rightarrow>   throw IllegalOperation
        );
    whenE (Not rights) $ throw IllegalOperation;
    notification \<leftarrow> withoutFailure $ getNotification ntfnPtr;
    (case (ntfnObj notification, ntfnBoundTCB notification) of
          (IdleNtfn, None) \<Rightarrow>   returnOk ()
        | (ActiveNtfn _, None) \<Rightarrow>   returnOk ()
        | _ \<Rightarrow>   throw IllegalOperation
        );
    returnOk NotificationControl_ \<lparr>
        notificationTCB= tcb,
        notificationPtr= Just ntfnPtr \<rparr>
odE)"

defs decodeUnbindNotification_def:
"decodeUnbindNotification cap\<equiv> (doE
    tcb \<leftarrow> returnOk ( capTCBPtr cap);
    ntfn \<leftarrow> withoutFailure $ getBoundNotification tcb;
    (case ntfn of
          None \<Rightarrow>   throw IllegalOperation
        | Some v15 \<Rightarrow>   returnOk ()
        );
    returnOk NotificationControl_ \<lparr>
        notificationTCB= tcb,
        notificationPtr= Nothing \<rparr>
odE)"

defs invokeTCB_def:
"invokeTCB x0\<equiv> (case x0 of
    (Suspend thread) \<Rightarrow>   
    withoutPreemption $ (do
        suspend thread;
        return []
    od)
  | (Resume thread) \<Rightarrow>   
    withoutPreemption $ (do
        restart thread;
        return []
    od)
  | (ThreadControl target slot faultep mcp priority cRoot vRoot buffer) \<Rightarrow>    (doE
        tCap \<leftarrow> returnOk ( ThreadCap_ \<lparr> capTCBPtr= target \<rparr>);
        withoutPreemption $ maybe (return ())
            (\<lambda> ep. threadSet (\<lambda> t. t \<lparr>tcbFaultHandler := ep\<rparr>) target)
            faultep;
        withoutPreemption $ maybe (return ()) (setMCPriority target) mcp;
        withoutPreemption $ maybe (return ()) (setPriority target) priority;
        maybe (returnOk ()) (\<lambda> (newCap, srcSlot). (doE
            rootSlot \<leftarrow> withoutPreemption $ getThreadCSpaceRoot target;
            cteDelete rootSlot True;
            withoutPreemption
                $ checkCapAt newCap srcSlot
                $ checkCapAt tCap slot
                $ assertDerived srcSlot newCap
                $ cteInsert newCap srcSlot rootSlot
        odE)
                                                   )
          cRoot;
        maybe (returnOk ()) (\<lambda> (newCap, srcSlot). (doE
            rootSlot \<leftarrow> withoutPreemption $ getThreadVSpaceRoot target;
            cteDelete rootSlot True;
            withoutPreemption
                $ checkCapAt newCap srcSlot
                $ checkCapAt tCap slot
                $ assertDerived srcSlot newCap
                $ cteInsert newCap srcSlot rootSlot
        odE)
                                                   )
          vRoot;
        maybe (returnOk ())
            (\<lambda> (ptr, frame). (doE
                bufferSlot \<leftarrow> withoutPreemption $ getThreadBufferSlot target;
                cteDelete bufferSlot True;
                withoutPreemption $ threadSet
                    (\<lambda> t. t \<lparr>tcbIPCBuffer := ptr\<rparr>) target;
                withoutPreemption $ asUser target $ setRegister tpidrurwRegister $ fromVPtr ptr;
                withoutPreemption $ (case frame of
                      Some (newCap, srcSlot) \<Rightarrow>  
                        checkCapAt newCap srcSlot
                            $ checkCapAt tCap slot
                            $ assertDerived srcSlot newCap
                            $ cteInsert newCap srcSlot bufferSlot
                    | None \<Rightarrow>   return ())
                    
            odE)
                    )
            buffer;
        returnOk []
  odE)
  | (CopyRegisters dest src suspendSource resumeTarget transferFrame transferInteger transferArch) \<Rightarrow>    withoutPreemption $ (do
    when suspendSource $ suspend src;
    when resumeTarget $ restart dest;
    when transferFrame $ (do
        mapM_x (\<lambda> r. (do
                v \<leftarrow> asUser src $ getRegister r;
                asUser dest $ setRegister r v
        od)
                                             )
            frameRegisters;
        pc \<leftarrow> asUser dest getRestartPC;
        asUser dest $ setNextPC pc
    od);
    when transferInteger $ (
        mapM_x (\<lambda> r. (do
                v \<leftarrow> asUser src $ getRegister r;
                asUser dest $ setRegister r v
        od)
                                             )
            gpRegisters
    );
    performTransfer transferArch src dest;
    return []
  od)
  | (ReadRegisters src suspendSource n arch) \<Rightarrow>   
  withoutPreemption $ (do
    when suspendSource $ suspend src;
    self \<leftarrow> getCurThread;
    performTransfer arch src self;
    regs \<leftarrow> return ( genericTake n $ frameRegisters @ gpRegisters);
    asUser src $ mapM getRegister regs
  od)
  | (WriteRegisters dest resumeTarget values arch) \<Rightarrow>   
  withoutPreemption $ (do
    self \<leftarrow> getCurThread;
    performTransfer arch self dest;
    t \<leftarrow> threadGet id dest;
    asUser dest $ (do
        zipWithM (\<lambda> r v. setRegister r (sanitiseRegister t r v))
            (frameRegisters @ gpRegisters) values;
        pc \<leftarrow> getRestartPC;
        setNextPC pc
    od);
    when resumeTarget $ restart dest;
    return []
  od)
  | (NotificationControl tcb (Some ntfnPtr)) \<Rightarrow>   
  withoutPreemption $ (do
    bindNotification tcb ntfnPtr;
    return []
  od)
  | (NotificationControl tcb None) \<Rightarrow>   
  withoutPreemption $ (do
    unbindNotification tcb;
    return []
  od)
  )"

defs decodeDomainInvocation_def:
"decodeDomainInvocation label args extraCaps\<equiv> (doE
    whenE (invocationType label \<noteq> DomainSetSet) $ throw IllegalOperation;
    domain \<leftarrow> (case args of
          (x#_) \<Rightarrow>   (doE
                     whenE (fromIntegral x \<ge> numDomains) $
                         throw InvalidArgument_ \<lparr> invalidArgumentNumber= 0 \<rparr>;
                     returnOk $ fromIntegral x
          odE)
        | _ \<Rightarrow>   throw TruncatedMessage
        );
    whenE (null extraCaps) $ throw TruncatedMessage;
    (case fst (head extraCaps) of
          ThreadCap ptr \<Rightarrow>   returnOk $ (ptr, domain)
        | _ \<Rightarrow>   throw InvalidArgument_ \<lparr> invalidArgumentNumber= 1 \<rparr>
        )
odE)"

defs checkCapAt_def:
"checkCapAt cap ptr action\<equiv> (do
        cap' \<leftarrow> liftM cteCap $ getCTE ptr;
        when (sameObjectAs cap cap') action
od)"

defs setMessageInfo_def:
"setMessageInfo thread info\<equiv> (do
        x \<leftarrow> return ( wordFromMessageInfo info);
        asUser thread $ setRegister msgInfoRegister x
od)"

defs getMessageInfo_def:
"getMessageInfo thread\<equiv> (do
        x \<leftarrow> asUser thread $ getRegister msgInfoRegister;
        return $ messageInfoFromWord x
od)"

defs setMRs_def:
"setMRs thread buffer messageData\<equiv> (do
        intSize \<leftarrow> return ( fromIntegral wordSize);
        hardwareMRs \<leftarrow> return ( msgRegisters);
        bufferMRs \<leftarrow> return ( (case buffer of
                  Some bufferPtr \<Rightarrow>  
                    map (\<lambda> x. bufferPtr +
                            PPtr (x*intSize))
                        [fromIntegral $ length hardwareMRs+1  .e.  msgMaxLength]
                | None \<Rightarrow>   []
                ));
        msgLength \<leftarrow> return ( min
                (length messageData)
                (length hardwareMRs + length bufferMRs));
        mrs \<leftarrow> return ( take msgLength messageData);
        asUser thread $ zipWithM_x setRegister hardwareMRs mrs;
        zipWithM_x storeWordUser bufferMRs $ drop (length hardwareMRs) mrs;
        return $ fromIntegral msgLength
od)"

defs getMRs_def:
"getMRs thread buffer info\<equiv> (do
        intSize \<leftarrow> return ( fromIntegral wordSize);
        hardwareMRs \<leftarrow> return ( msgRegisters);
        hardwareMRValues \<leftarrow> asUser thread $ mapM getRegister hardwareMRs;
        bufferMRValues \<leftarrow> (case buffer of
              Some bufferPtr \<Rightarrow>   (do
                bufferMRs \<leftarrow> return ( map (\<lambda> x. bufferPtr +
                            PPtr (x*intSize))
                        [fromIntegral $ length hardwareMRs+1 .e.  msgMaxLength]);
                mapM loadWordUser bufferMRs
              od)
            | None \<Rightarrow>   return []
            );
        values \<leftarrow> return ( hardwareMRValues @ bufferMRValues);
        return $ take (fromIntegral $ msgLength info) values
od)"

defs copyMRs_def:
"copyMRs sender sendBuf receiver recvBuf n\<equiv> (do
        intSize \<leftarrow> return ( fromIntegral wordSize);
        hardwareMRs \<leftarrow> return ( take (fromIntegral n) msgRegisters);
        forM hardwareMRs (\<lambda> r. (do
            v \<leftarrow> asUser sender $ getRegister r;
            asUser receiver $ setRegister r v
        od));
        bufferMRs \<leftarrow> (case (sendBuf, recvBuf) of
              (Some sbPtr, Some rbPtr) \<Rightarrow>  
                mapM (\<lambda> x. (do
                    v \<leftarrow> loadWordUser (sbPtr + PPtr (x*intSize));
                    storeWordUser (rbPtr + PPtr (x*intSize)) v
                od)
                ) [fromIntegral $ length msgRegisters+1  .e.  n]
            | _ \<Rightarrow>   return []
            );
        return $ min n $ fromIntegral $ length hardwareMRs + length bufferMRs
od)"

defs getExtraCPtrs_def:
"getExtraCPtrs buffer x1\<equiv> (case x1 of
    (MI _ count _ _) \<Rightarrow>    (do
        intSize \<leftarrow> return ( fromIntegral wordSize);
        (case buffer of
              Some bufferPtr \<Rightarrow>   (do
                offset \<leftarrow> return ( msgMaxLength+1);
                bufferPtrs \<leftarrow> return ( map (\<lambda> x. bufferPtr +
                        PPtr ((x+offset)*intSize)) [1, 2  .e.  count]);
                mapM (liftM CPtr \<circ> loadWordUser) bufferPtrs
              od)
            | None \<Rightarrow>   return []
            )
    od)
  )"

defs lookupExtraCaps_def:
"lookupExtraCaps thread buffer info\<equiv> (doE
        cptrs \<leftarrow> withoutFailure $ getExtraCPtrs buffer info;
        mapME (\<lambda> cptr.
          capFaultOnFailure cptr False $ lookupCapAndSlot thread cptr) cptrs
odE)"

defs getExtraCPtr_def:
"getExtraCPtr buffer n\<equiv> (do
        intSize \<leftarrow> return ( fromIntegral wordSize);
        ptr \<leftarrow> return ( buffer + bufferCPtrOffset +
                  PPtr ((fromIntegral n) * intSize));
        cptr \<leftarrow> loadWordUser ptr;
        return $ CPtr cptr
od)"

defs setExtraBadge_def:
"setExtraBadge buffer badge n\<equiv> (do
        intSize \<leftarrow> return ( fromIntegral wordSize);
        badgePtr \<leftarrow> return ( buffer + bufferCPtrOffset +
                       PPtr ((fromIntegral n) * intSize));
        storeWordUser badgePtr badge
od)"

defs bufferCPtrOffset_def:
"bufferCPtrOffset \<equiv>
        let intSize = fromIntegral wordSize
        in PPtr ((msgMaxLength+2)*intSize)"

defs setupCallerCap_def:
"setupCallerCap sender receiver\<equiv> (do
    setThreadState BlockedOnReply sender;
    replySlot \<leftarrow> getThreadReplySlot sender;
    masterCTE \<leftarrow> getCTE replySlot;
    masterCap \<leftarrow> return ( cteCap masterCTE);
    haskell_assert (isReplyCap masterCap \<and> capReplyMaster masterCap \<and>
            capTCBPtr masterCap = sender)
        [];
    haskell_assert (mdbNext (cteMDBNode masterCTE) = nullPointer)
        [];
    callerSlot \<leftarrow> getThreadCallerSlot receiver;
    callerCap \<leftarrow> getSlotCap callerSlot;
    haskell_assert (isNullCap callerCap)
        [];
    cteInsert (ReplyCap sender False) replySlot callerSlot
od)"

defs deleteCallerCap_def:
"deleteCallerCap receiver\<equiv> (do
    callerSlot \<leftarrow> getThreadCallerSlot receiver;
    callerCap \<leftarrow> getSlotCap callerSlot;
    haskell_assert (isReplyCap callerCap \<or> isNullCap callerCap)
        [];
    cteDeleteOne callerSlot
od)"

defs getThreadCSpaceRoot_def:
"getThreadCSpaceRoot thread\<equiv> (
        locateSlotTCB thread tcbCTableSlot
)"

defs getThreadVSpaceRoot_def:
"getThreadVSpaceRoot thread \<equiv> locateSlotTCB thread tcbVTableSlot"

defs getThreadReplySlot_def:
"getThreadReplySlot thread \<equiv> locateSlotTCB thread tcbReplySlot"

defs getThreadCallerSlot_def:
"getThreadCallerSlot thread \<equiv> locateSlotTCB thread tcbCallerSlot"

defs getThreadBufferSlot_def:
"getThreadBufferSlot thread \<equiv> locateSlotTCB thread tcbIPCBufferSlot"

defs threadGet_def:
"threadGet f tptr \<equiv> liftM f $ getObject tptr"

defs threadSet_def:
"threadSet f tptr\<equiv> (do
        tcb \<leftarrow> getObject tptr;
        setObject tptr $ f tcb
od)"


defs asUser_def:
"asUser tptr f\<equiv> (do
        uc \<leftarrow> threadGet  (atcbContextGet o tcbArch) tptr;
        (a, uc') \<leftarrow> select_f (f uc);
        threadSet (\<lambda> tcb. tcb \<lparr> tcbArch := atcbContextSet uc' (tcbArch tcb)\<rparr>) tptr;
        return a
od)"

end
