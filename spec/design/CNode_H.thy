(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "CNodes"

theory CNode_H
imports
  FaultMonad_H
  ThreadDecls_H
  RetypeDecls_H
  TCBDecls_H
  CSpaceDecls_H
  EndpointDecls_H
  PSpaceFuns_H
begin


consts
decodeCNodeInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> capability \<Rightarrow> capability list \<Rightarrow> ( syscall_error , cnode_invocation ) kernel_f"

consts
invokeCNode :: "cnode_invocation \<Rightarrow> unit kernel_p"

consts
setUntypedCapAsFull :: "capability \<Rightarrow> capability \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts
cteInsert :: "capability \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts
cteMove :: "capability \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts
capSwapForDelete :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts
cteSwap :: "capability \<Rightarrow> machine_word \<Rightarrow> capability \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts
cteDelete :: "machine_word \<Rightarrow> bool \<Rightarrow> unit kernel_p"

consts
emptySlot :: "machine_word \<Rightarrow> irq option \<Rightarrow> unit kernel"

consts
finaliseSlot :: "machine_word \<Rightarrow> bool \<Rightarrow> (bool * irq option) kernel_p"

consts
capRemovable :: "capability \<Rightarrow> machine_word \<Rightarrow> bool"

consts
capCyclicZombie :: "capability \<Rightarrow> machine_word \<Rightarrow> bool"

consts
reduceZombie :: "capability \<Rightarrow> machine_word \<Rightarrow> bool \<Rightarrow> unit kernel_p"

consts
cteDeleteOne :: "machine_word \<Rightarrow> unit kernel"

consts
cteRecycle :: "machine_word \<Rightarrow> unit kernel_p"

consts
createNewObjects :: "object_type \<Rightarrow> machine_word \<Rightarrow> machine_word list \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> unit kernel"

consts
insertNewCap :: "machine_word \<Rightarrow> machine_word \<Rightarrow> capability \<Rightarrow> unit kernel"

consts
insertInitCap :: "machine_word \<Rightarrow> capability \<Rightarrow> unit kernel"

consts
setupReplyMaster :: "machine_word \<Rightarrow> unit kernel"

consts
noReplyCapsFor :: "machine_word \<Rightarrow> kernel_state \<Rightarrow> bool"

consts
isMDBParentOf :: "cte \<Rightarrow> cte \<Rightarrow> bool"

consts
updateMDB :: "machine_word \<Rightarrow> (mdbnode \<Rightarrow> mdbnode) \<Rightarrow> unit kernel"

consts
ensureNoChildren :: "machine_word \<Rightarrow> ( syscall_error , unit ) kernel_f"

consts
ensureEmptySlot :: "machine_word \<Rightarrow> ( syscall_error , unit ) kernel_f"

consts
locateSlot :: "machine_word \<Rightarrow> machine_word \<Rightarrow> (machine_word) kernel"

consts
getCTE :: "machine_word \<Rightarrow> cte kernel"

consts
setCTE :: "machine_word \<Rightarrow> cte \<Rightarrow> unit kernel"

consts
updateCap :: "machine_word \<Rightarrow> capability \<Rightarrow> unit kernel"

consts
getSlotCap :: "machine_word \<Rightarrow> capability kernel"

consts
isFinalCapability :: "cte \<Rightarrow> bool kernel"

consts
longRunningDelete :: "capability \<Rightarrow> bool"

consts
slotCapLongRunningDelete :: "machine_word \<Rightarrow> bool kernel"

consts
getReceiveSlots :: "machine_word \<Rightarrow> (machine_word) option \<Rightarrow> machine_word list kernel"

consts
loadCapTransfer :: "machine_word \<Rightarrow> cap_transfer kernel"

consts
capTransferFromWords :: "machine_word \<Rightarrow> cap_transfer kernel"


function
  cteRevoke :: "machine_word \<Rightarrow> unit kernel_p"
where
 "cteRevoke p s = 

(\<lambda>slot.  (doE
    cte \<leftarrow> withoutPreemption $ getCTE slot;
    nextPtr \<leftarrow> returnOk ( mdbNext $ cteMDBNode cte);
    unlessE ((isNullCap $ cteCap cte) \<or> (nextPtr = nullPointer)) $ (doE
        nextCTE \<leftarrow> withoutPreemption $ getCTE nextPtr;
        whenE (cte `~isMDBParentOf~` nextCTE) $ (doE
            cteDelete nextPtr True;
            preemptionPoint;
            cteRevoke slot
        odE)
    odE)
odE))


  p s"
by auto

defs decodeCNodeInvocation_def:
"decodeCNodeInvocation label x1 x2 extraCaps\<equiv> (let (v1, cap) = (x1, x2) in
  if isCNodeCap cap
  then
  (case v1 of
  (index # bits # args) \<Rightarrow>   (doE
    inv \<leftarrow> returnOk ( invocationType label);
    unlessE (inv `~elem~` [CNodeRevoke  .e.  CNodeSaveCaller]) $
        throw IllegalOperation;
    destSlot \<leftarrow> lookupTargetSlot cap (CPtr index) (fromIntegral bits);
    (case (inv `~elem~` [CNodeCopy  .e.  CNodeMutate], inv, args, extraCaps) of
          (True, _, srcIndex#srcDepth#args, srcRootCap#_) \<Rightarrow>   (doE
            ensureEmptySlot destSlot;
            srcSlot \<leftarrow> lookupSourceSlot srcRootCap
                (CPtr srcIndex) (fromIntegral srcDepth);
            srcCTE \<leftarrow> withoutFailure $ getCTE srcSlot;
            whenE (isNullCap $ cteCap srcCTE) $
                throw $ FailedLookup True $ MissingCapability_ \<lparr>
                    missingCapBitsLeft= fromIntegral srcDepth \<rparr>;
            (rights, capData) \<leftarrow>
              (case (inv, args) of
                  (CNodeCopy, rights#_) \<Rightarrow>  
                    returnOk $ (rightsFromWord rights, Nothing)
                | (CNodeMint, rights#newData#_) \<Rightarrow>  
                    returnOk $ (rightsFromWord rights, Just newData)
                | (CNodeMove, _) \<Rightarrow>  
                    returnOk $ (allRights, Nothing)
                | (CNodeMutate, newData#_) \<Rightarrow>  
                    returnOk $ (allRights, Just newData)
                | _ \<Rightarrow>   throw TruncatedMessage
                );
            isMove \<leftarrow> returnOk ( inv `~elem~` [CNodeMove, CNodeMutate]);
            srcCap \<leftarrow> returnOk ( maskCapRights rights $ cteCap srcCTE);
            newCap \<leftarrow> (if isMove then returnOk else deriveCap srcSlot) $
              (case capData of
                  Some w \<Rightarrow>   updateCapData isMove w srcCap
                | None \<Rightarrow>   srcCap
                );
            whenE (isNullCap newCap) $ throw IllegalOperation;
            returnOk $
                (if isMove then Move else Insert) newCap srcSlot destSlot
          odE)
        | (_, CNodeRevoke, _, _) \<Rightarrow>   returnOk $ Revoke destSlot
        | (_, CNodeDelete, _, _) \<Rightarrow>   returnOk $ Delete destSlot
        | (_, CNodeSaveCaller, _, _) \<Rightarrow>   (doE
            ensureEmptySlot destSlot;
            returnOk $ SaveCaller destSlot
        odE)
        | (_, CNodeRecycle, _, _) \<Rightarrow>   (doE
            cte \<leftarrow> withoutFailure $ getCTE destSlot;
            unlessE (hasRecycleRights $ cteCap cte) $ throw IllegalOperation;
            returnOk $ Recycle destSlot
        odE)
        | (_, CNodeRotate, pivotNewData#pivotIndex#pivotDepth#srcNewData#srcIndex#srcDepth#_, pivotRootCap#srcRootCap#_) \<Rightarrow>   (doE
            srcSlot \<leftarrow> lookupSourceSlot srcRootCap
                    (CPtr srcIndex) (fromIntegral srcDepth);
            pivotSlot \<leftarrow> lookupPivotSlot pivotRootCap
                    (CPtr pivotIndex) (fromIntegral pivotDepth);
            whenE (pivotSlot = srcSlot \<or> pivotSlot = destSlot) $
                throw IllegalOperation;
            unlessE (srcSlot = destSlot) $ ensureEmptySlot destSlot;
            srcCap \<leftarrow> withoutFailure $ liftM cteCap $ getCTE srcSlot;
            whenE (isNullCap srcCap) $
                throw $ FailedLookup True $ MissingCapability_ \<lparr>
                    missingCapBitsLeft= fromIntegral srcDepth \<rparr>;
            pivotCap \<leftarrow> withoutFailure $ liftM cteCap $ getCTE pivotSlot;
            whenE (isNullCap pivotCap) $
                throw $ FailedLookup False $ MissingCapability_ \<lparr>
                    missingCapBitsLeft= fromIntegral pivotDepth \<rparr>;
            newSrcCap \<leftarrow> returnOk ( updateCapData True srcNewData srcCap);
            newPivotCap \<leftarrow> returnOk ( updateCapData True pivotNewData pivotCap);
            whenE (isNullCap newSrcCap) $ throw IllegalOperation;
            whenE (isNullCap newPivotCap) $ throw IllegalOperation;
            returnOk $ Rotate newSrcCap newPivotCap srcSlot pivotSlot destSlot
        odE)
        | _ \<Rightarrow>   throw TruncatedMessage
        )
  odE)
  | _ \<Rightarrow>   throw $ if invocationType label `~elem~` [CNodeRevoke  .e.  CNodeSaveCaller]
        then TruncatedMessage
        else IllegalOperation
  )
  else   haskell_fail []
  )"

defs invokeCNode_def:
"invokeCNode x0\<equiv> (case x0 of
    (Revoke destSlot) \<Rightarrow>    cteRevoke destSlot
  | (Delete destSlot) \<Rightarrow>    cteDelete destSlot True
  | (Recycle destSlot) \<Rightarrow>    cteRecycle destSlot
  | (Insert cap srcSlot destSlot) \<Rightarrow>   
    withoutPreemption $ cteInsert cap srcSlot destSlot
  | (Move cap srcSlot destSlot) \<Rightarrow>   
    withoutPreemption $ cteMove cap srcSlot destSlot
  | (Rotate cap1 cap2 slot1 slot2 slot3) \<Rightarrow>    withoutPreemption $
    if (slot1 = slot3)
      then cteSwap cap1 slot1 cap2 slot2
      else (do
             cteMove cap2 slot2 slot3;
             cteMove cap1 slot1 slot2
      od)
  | (SaveCaller destSlot) \<Rightarrow>    withoutPreemption $ (do
    thread \<leftarrow> getCurThread;
    srcSlot \<leftarrow> getThreadCallerSlot thread;
    cap \<leftarrow> getSlotCap srcSlot;
    (case cap of
          NullCap \<Rightarrow>   return ()
        | ReplyCap _ False \<Rightarrow>   cteMove cap srcSlot destSlot
        | _ \<Rightarrow>   haskell_fail []
        )
  od)
  )"

defs setUntypedCapAsFull_def:
"setUntypedCapAsFull srcCap newCap srcSlot\<equiv> (
        if (isUntypedCap srcCap \<and> isUntypedCap newCap \<and>
           capPtr srcCap = capPtr newCap \<and> capBlockSize srcCap = capBlockSize newCap)
           then updateCap srcSlot (srcCap \<lparr> capFreeIndex := maxFreeIndex (capBlockSize srcCap) \<rparr>) else return ()
)"

defs cteInsert_def:
"cteInsert newCap srcSlot destSlot\<equiv> (do
        srcCTE \<leftarrow> getCTE srcSlot;
        srcMDB \<leftarrow> return ( cteMDBNode srcCTE);
        srcCap \<leftarrow> return ( cteCap srcCTE);
        newCapIsRevocable \<leftarrow> return ( (case newCap of
                  EndpointCap _ _ _ _ _ \<Rightarrow>  
                    capEPBadge newCap \<noteq> capEPBadge srcCap
                | AsyncEndpointCap _ _ _ _ \<Rightarrow>  
                    capAEPBadge newCap \<noteq> capAEPBadge srcCap
                | IRQHandlerCap _ \<Rightarrow>   isIRQControlCap srcCap
                | UntypedCap _ _ _ \<Rightarrow>   True
                | _ \<Rightarrow>   False
                ));
        newMDB \<leftarrow> return ( srcMDB \<lparr>
                mdbPrev := srcSlot,
                mdbRevocable := newCapIsRevocable,
                mdbFirstBadged := newCapIsRevocable \<rparr>);
        oldCTE \<leftarrow> getCTE destSlot;
        haskell_assert (isNullCap $ cteCap oldCTE)
                [];
        haskell_assert (mdbPrev (cteMDBNode oldCTE) = nullPointer \<and>
                mdbNext (cteMDBNode oldCTE) = nullPointer)
                [];
        setUntypedCapAsFull srcCap newCap srcSlot;
        updateCap destSlot newCap;
        updateMDB destSlot (const newMDB);
        updateMDB srcSlot (\<lambda> m. m \<lparr> mdbNext := destSlot \<rparr>);
        updateMDB (mdbNext newMDB) (\<lambda> m. m \<lparr> mdbPrev := destSlot \<rparr>)
od)"

defs cteMove_def:
"cteMove newCap srcSlot destSlot\<equiv> (do
        oldCTE \<leftarrow> getCTE destSlot;
        haskell_assert (isNullCap $ cteCap oldCTE)
                [];
        haskell_assert (mdbPrev (cteMDBNode oldCTE) = nullPointer \<and>
                mdbNext (cteMDBNode oldCTE) = nullPointer)
                [];
        cte \<leftarrow> getCTE srcSlot;
        mdb \<leftarrow> return ( cteMDBNode cte);
        updateCap destSlot newCap;
        updateCap srcSlot NullCap;
        updateMDB destSlot (const mdb);
        updateMDB srcSlot (const nullMDBNode);
        updateMDB (mdbPrev mdb) (\<lambda> m. m \<lparr> mdbNext := destSlot \<rparr>);
        updateMDB (mdbNext mdb) (\<lambda> m. m \<lparr> mdbPrev := destSlot \<rparr>)
od)"

defs capSwapForDelete_def:
"capSwapForDelete slot1 slot2\<equiv> when (slot1 \<noteq> slot2) $ (do
    cap1 \<leftarrow> liftM cteCap $ getCTE slot1;
    cap2 \<leftarrow> liftM cteCap $ getCTE slot2;
    cteSwap cap1 slot1 cap2 slot2
od)"

defs cteSwap_def:
"cteSwap cap1 slot1 cap2 slot2\<equiv> (do
    cte1 \<leftarrow> getCTE slot1;
    updateCap slot1 cap2;
    updateCap slot2 cap1;
    mdb1 \<leftarrow> return ( cteMDBNode cte1);
    updateMDB (mdbPrev mdb1) (\<lambda> m. m \<lparr> mdbNext := slot2 \<rparr>);
    updateMDB (mdbNext mdb1) (\<lambda> m. m \<lparr> mdbPrev := slot2 \<rparr>);
    cte2 \<leftarrow> getCTE slot2;
    mdb2 \<leftarrow> return ( cteMDBNode cte2);
    updateMDB slot1 (const mdb2);
    updateMDB slot2 (const mdb1);
    updateMDB (mdbPrev mdb2) (\<lambda> m. m \<lparr> mdbNext := slot1 \<rparr>);
    updateMDB (mdbNext mdb2) (\<lambda> m. m \<lparr> mdbPrev := slot1 \<rparr>)
od)"

defs cteDelete_def:
"cteDelete slot exposed\<equiv> (doE
    (success, irq) \<leftarrow> finaliseSlot slot exposed;
    whenE (exposed \<or> success) $ withoutPreemption $ emptySlot slot irq
odE)"

defs emptySlot_def:
"emptySlot slot irq\<equiv> (do
    newCTE \<leftarrow> getCTE slot;
    mdbNode \<leftarrow> return ( cteMDBNode newCTE);
    prev \<leftarrow> return ( mdbPrev mdbNode);
    next \<leftarrow> return ( mdbNext mdbNode);
    (case (cteCap newCTE) of
          NullCap \<Rightarrow>   return ()
        | _ \<Rightarrow>   (do
            updateMDB prev (\<lambda> mdb. mdb \<lparr> mdbNext := next \<rparr>);
            updateMDB next (\<lambda> mdb. mdb \<lparr>
                    mdbPrev := prev,
                    mdbFirstBadged :=
                        mdbFirstBadged mdb \<or> mdbFirstBadged mdbNode \<rparr>);
            updateCap slot NullCap;
            updateMDB slot (const nullMDBNode);
            (case irq of
                  Some irq \<Rightarrow>   deletedIRQHandler irq
                | None \<Rightarrow>   return ()
                )
        od)
        )
od)"

defs capRemovable_def:
"capRemovable x0 slot\<equiv> (case x0 of
    NullCap \<Rightarrow>    True
  | (Zombie slot' _ n) \<Rightarrow>   
    (n = 0) \<or> (n = 1 \<and> slot = slot')
  | _ \<Rightarrow>    error []
  )"

defs capCyclicZombie_def:
"capCyclicZombie x0 slot\<equiv> (case x0 of
    NullCap \<Rightarrow>    False
  | (Zombie slot' _ _) \<Rightarrow>   
    slot = slot'
  | _ \<Rightarrow>    False
  )"

defs reduceZombie_def:
"reduceZombie x0 slot x2\<equiv> (let (v5, v6) = (x0, x2) in
  if isZombie v5 \<and> capZombieNumber v5 = 0
  then  
    haskell_fail []
  else if isZombie v5 \<and> \<not> v6
  then let ptr = capZombiePtr v5
  in   (doE
    haskell_assertE (ptr \<noteq> slot) [];
    capAtPtr \<leftarrow> withoutPreemption $ liftM cteCap $ getCTE ptr;
    (case capAtPtr of
          (Zombie ptr2 _ _) \<Rightarrow>   haskell_assertE (ptr2 \<noteq> ptr)
                []
        | _ \<Rightarrow>   returnOk ()
        );
    withoutPreemption $ capSwapForDelete ptr slot
  odE)
  else if isZombie v5 \<and> v6
  then let z = v5; ptr = capZombiePtr z; n = capZombieNumber z
  in   (doE
    endSlot \<leftarrow> withoutPreemption $ locateSlot ptr (fromIntegral (n - 1));
    cteDelete endSlot False;
    ourCTE  \<leftarrow> withoutPreemption $ getCTE slot;
    (let c2 = (cteCap ourCTE) in
        if isNullCap c2
        then  returnOk ()
        else if isZombie c2
        then let ptr2 = capZombiePtr c2
        in 
            if (ptr = ptr2 \<and> capZombieNumber c2 = n
                    \<and> capZombieType z = capZombieType c2)
            then withoutPreemption $ (do
                endCTE \<leftarrow> getCTE endSlot;
                haskell_assert (isNullCap $ cteCap endCTE)
                    [];
                newCap \<leftarrow> return ( z \<lparr> capZombieNumber := n- 1 \<rparr>);
                updateCap slot newCap
            od)
            else haskell_assertE (ptr2 = slot \<and> ptr \<noteq> slot)
                    []
        else  haskell_fail []
        )
  odE)
  else   haskell_fail []
  )"

defs cteRecycle_def:
"cteRecycle slot\<equiv> (doE
    cteRevoke slot;
    finaliseSlot slot True;
    withoutPreemption $ (do
        cte \<leftarrow> getCTE slot;
        unless (isNullCap $ cteCap cte) $ (do
            is_final \<leftarrow> isFinalCapability cte;
            cap \<leftarrow> recycleCap is_final $ cteCap cte;
            updateCap slot cap
        od)
    od)
odE)"

defs createNewObjects_def:
"createNewObjects newType srcSlot destSlots regionBase userSizeBits\<equiv> (do
    objectSizeBits \<leftarrow> return ( getObjectSize newType userSizeBits);
    zipWithM_x (\<lambda> num slot. (do
      cap \<leftarrow> createObject newType
              (PPtr (num `~shiftL~` objectSizeBits) + regionBase) userSizeBits;
      insertNewCap srcSlot slot cap
    od)
                                   )
      [0  .e.  fromIntegral (length destSlots - 1)] destSlots
od)"

defs insertNewCap_def:
"insertNewCap parent slot cap\<equiv> (do
    next \<leftarrow> liftM (mdbNext \<circ> cteMDBNode) $ getCTE parent;
    oldCTE \<leftarrow> getCTE slot;
    haskell_assert (isNullCap (cteCap oldCTE)
            \<and> mdbNext (cteMDBNode oldCTE) = nullPointer
            \<and> mdbPrev (cteMDBNode oldCTE) = nullPointer)
            [];
    setCTE slot $ CTE cap (MDB next parent True True);
    updateMDB next   $ (\<lambda> m. m \<lparr> mdbPrev := slot \<rparr>);
    updateMDB parent $ (\<lambda> m. m \<lparr> mdbNext := slot \<rparr>)
od)"

defs insertInitCap_def:
"insertInitCap slot cap\<equiv> (do
    oldCTE \<leftarrow> getCTE slot;
    haskell_assert (isNullCap $ cteCap oldCTE) [];
    haskell_assert (Not $ isNullCap cap) [];
    haskell_assert (mdbPrev (cteMDBNode oldCTE) = nullPointer \<and>
            mdbNext (cteMDBNode oldCTE) = nullPointer)
           [];
    updateCap slot cap;
    updateMDB slot (const (nullMDBNode \<lparr>
        mdbRevocable := True,
        mdbFirstBadged := True \<rparr>))
od)"

defs setupReplyMaster_def:
"setupReplyMaster thread\<equiv> (do
    slot \<leftarrow> locateSlot (PPtr $ fromPPtr thread) tcbReplySlot;
    oldCTE \<leftarrow> getCTE slot;
    when (isNullCap $ cteCap oldCTE) $ (do
        stateAssert (noReplyCapsFor thread)
            [];
        cap \<leftarrow> return ( ReplyCap_ \<lparr> capTCBPtr= thread, capReplyMaster= True \<rparr>);
        mdb \<leftarrow> return ( nullMDBNode \<lparr> mdbRevocable := True, mdbFirstBadged := True \<rparr>);
        setCTE slot $ CTE cap mdb
    od)
od)"

defs isMDBParentOf_def:
"isMDBParentOf x0 x1\<equiv> (case (x0, x1) of
    ((CTE a mdbA), (CTE b mdbB)) \<Rightarrow>   
    if
    Not $ mdbRevocable mdbA  then False
    else if
    Not $ a `~sameRegionAs~` b then False
    else if
    True                     then (if isEndpointCap a & capEPBadge a ~= 0
        then let badge = capEPBadge a in
         
            (badge = capEPBadge b) \<and> (Not $ mdbFirstBadged mdbB)
        else if isAsyncEndpointCap a & capAEPBadge a ~= 0
        then let badge = capAEPBadge a in
         
            (badge = capAEPBadge b) \<and> (Not $ mdbFirstBadged mdbB)
        else  True
        )
    else undefined
  )"

defs updateMDB_def:
"updateMDB x0 f\<equiv> (let slot = x0 in
  if slot = 0 then   return ()
  else   (do
        cte \<leftarrow> getCTE slot;
        mdb \<leftarrow> return ( cteMDBNode cte);
        mdb' \<leftarrow> return ( f mdb);
        cte' \<leftarrow> return ( cte \<lparr> cteMDBNode := mdb' \<rparr>);
        setCTE slot cte'
  od)
  )"

defs ensureNoChildren_def:
"ensureNoChildren slot\<equiv> (doE
        cte \<leftarrow> withoutFailure $ getCTE slot;
        whenE (mdbNext (cteMDBNode cte) \<noteq> nullPointer) $ (doE
            next \<leftarrow> withoutFailure $ getCTE (mdbNext $ cteMDBNode cte);
            whenE (cte `~isMDBParentOf~` next) $ throw RevokeFirst
        odE)
odE)"

defs ensureEmptySlot_def:
"ensureEmptySlot slot\<equiv> (doE
        cte \<leftarrow> withoutFailure $ getCTE slot;
        unlessE (isNullCap $ cteCap cte) $ throw DeleteFirst
odE)"

defs locateSlot_def:
"locateSlot cnode offset\<equiv> (do
        slotSize \<leftarrow> return ( 1 `~shiftL~` objBits (undefined::cte));
        return $ PPtr $ fromPPtr $ cnode + PPtr (slotSize * offset)
od)"

defs getCTE_def:
"getCTE \<equiv> getObject"

defs setCTE_def:
"setCTE \<equiv> setObject"

defs updateCap_def:
"updateCap slot newCap\<equiv> (do
        cte \<leftarrow> getCTE slot;
        setCTE slot (cte \<lparr> cteCap := newCap \<rparr>)
od)"

defs getSlotCap_def:
"getSlotCap ptr\<equiv> (do
    cte \<leftarrow> getCTE ptr;
    return $ cteCap cte
od)"

defs isFinalCapability_def:
"isFinalCapability x0\<equiv> (let cte = x0; mdb = cteMDBNode cte
  in   (do
    prevIsSameObject \<leftarrow> if mdbPrev mdb = nullPointer
        then return False
        else (do
            prev \<leftarrow> getCTE (mdbPrev mdb);
            return $ sameObjectAs (cteCap prev) (cteCap cte)
        od);
    if prevIsSameObject
        then return False
        else if mdbNext mdb = nullPointer
            then return True
            else (do
                next \<leftarrow> getCTE (mdbNext mdb);
                return $ Not $ sameObjectAs (cteCap cte) (cteCap next)
            od)
  od)
  )"

defs longRunningDelete_def:
"longRunningDelete x0\<equiv> (case x0 of
    (ThreadCap _) \<Rightarrow>    True
  | (CNodeCap _ _ _ _) \<Rightarrow>    True
  | (Zombie _ _ _) \<Rightarrow>    True
  | _ \<Rightarrow>    False
  )"

defs slotCapLongRunningDelete_def:
"slotCapLongRunningDelete slot\<equiv> (do
    cte \<leftarrow> getCTE slot;
    (case cteCap cte of
          NullCap \<Rightarrow>   return False
        | _ \<Rightarrow>   (do
            final \<leftarrow> isFinalCapability cte;
            return $ final \<and> longRunningDelete (cteCap cte)
        od)
        )
od)"

defs getReceiveSlots_def:
"getReceiveSlots thread x1\<equiv> (case x1 of
    (Some buffer) \<Rightarrow>    (do
        ct \<leftarrow> loadCapTransfer buffer;
        emptyOnFailure $ (doE
            cptr \<leftarrow> returnOk ( ctReceiveRoot ct);
            cnode \<leftarrow> unifyFailure $ lookupCap thread cptr;
            slot \<leftarrow> unifyFailure $ lookupTargetSlot
                cnode (ctReceiveIndex ct) (ctReceiveDepth ct);
            cte \<leftarrow> withoutFailure $ getCTE slot;
            unlessE (isNullCap $ cteCap cte) $ throw ();
            returnOk [slot]
        odE)
    od)
  | None \<Rightarrow>    return []
  )"

defs loadCapTransfer_def:
"loadCapTransfer buffer\<equiv> (do
        intSize \<leftarrow> return ( fromIntegral wordSize);
        offset \<leftarrow> return ( msgMaxLength + msgMaxExtraCaps + 2);
        capTransferFromWords (buffer + PPtr (offset*intSize))
od)"

defs capTransferFromWords_def:
"capTransferFromWords ptr\<equiv> (do
        intSize \<leftarrow> return ( fromIntegral wordSize);
        w0 \<leftarrow> loadWordUser ptr;
        w1 \<leftarrow> loadWordUser $ ptr + PPtr intSize;
        w2 \<leftarrow> loadWordUser $ ptr + PPtr (2 * intSize);
        return CT_ \<lparr>
            ctReceiveRoot= CPtr w0,
            ctReceiveIndex= CPtr w1,
            ctReceiveDepth= fromIntegral w2 \<rparr>
od)"


end
