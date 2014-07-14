(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

header "Untyped Objects"

theory Untyped_H
imports
  RetypeDecls_H
  CSpaceDecls_H
  CNode_H
  Invocations_H
  Config_H
begin

definition
getFreeRef :: "machine_word \<Rightarrow> nat \<Rightarrow> machine_word"
where
"getFreeRef base freeIndex\<equiv> base + (fromIntegral freeIndex)"

definition
getFreeIndex :: "machine_word \<Rightarrow> machine_word \<Rightarrow> nat"
where
"getFreeIndex base free\<equiv> fromIntegral $ fromPPtr (free - base)"

definition
alignUp :: "machine_word \<Rightarrow> nat \<Rightarrow> machine_word"
where
"alignUp baseValue alignment \<equiv>
  (baseValue + (1 `~shiftL~` alignment) - 1) && complement (mask alignment)"

definition
decodeUntypedInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> machine_word \<Rightarrow> capability \<Rightarrow> capability list \<Rightarrow> ( syscall_error , untyped_invocation ) kernel_f"
where
"decodeUntypedInvocation label x1 slot cap x4\<equiv> (case (x1, x4) of
    ((newTypeW#userObjSizeW#nodeIndexW#nodeDepthW#nodeOffset#nodeWindow#_), (rootCap#_)) \<Rightarrow>   
  (doE
    unlessE (invocationType label = UntypedRetype) $ throw IllegalOperation;
    whenE (fromIntegral newTypeW > fromEnum (maxBound ::object_type)) $
        throw $ InvalidArgument 0;
    newType \<leftarrow> returnOk ( toEnum (fromIntegral newTypeW) ::object_type);
    userObjSize \<leftarrow> returnOk ( fromIntegral userObjSizeW);
    rangeCheck userObjSize 0 $ bitSize nullPointer - 2;
    whenE (newType = fromAPIType CapTableObject \<and> userObjSize = 0) $
        throw $ InvalidArgument 1;
    whenE (newType = fromAPIType Untyped \<and> userObjSize < 4) $
        throw $ InvalidArgument 1;
    nodeIndex \<leftarrow> returnOk ( CPtr nodeIndexW);
    nodeDepth \<leftarrow> returnOk ( fromIntegral nodeDepthW);
    nodeCap \<leftarrow> if nodeDepth = 0
        then returnOk rootCap
        else (doE
            nodeSlot \<leftarrow> lookupTargetSlot rootCap nodeIndex nodeDepth;
            withoutFailure $ getSlotCap nodeSlot
        odE);
    (case nodeCap of
          CNodeCap _ _ _ _ \<Rightarrow>   returnOk ()
        | _ \<Rightarrow>   throw $ FailedLookup False $ MissingCapability_ \<lparr>
            missingCapBitsLeft= nodeDepth \<rparr>
        );
    nodeSize \<leftarrow> returnOk ( 1 `~shiftL~` (capCNodeBits nodeCap));
    rangeCheck nodeOffset 0 $ nodeSize - 1;
    rangeCheck nodeWindow 1 retypeFanOutLimit;
    rangeCheck nodeWindow 1 $ nodeSize - nodeOffset;
    slots \<leftarrow> withoutFailure $
        mapM (locateSlot $ capCNodePtr nodeCap)
            [nodeOffset  .e.  nodeOffset+nodeWindow - 1];
    mapME_x ensureEmptySlot slots;
    freeIndex \<leftarrow> withoutFailure $ constOnFailure (capFreeIndex cap) $ (doE
            ensureNoChildren slot;
            returnOk 0
    odE);
    freeRef \<leftarrow> returnOk ( getFreeRef (capPtr cap) freeIndex);
    objectSize \<leftarrow> returnOk ( getObjectSize newType userObjSize);
    untypedFreeBytes \<leftarrow> returnOk ( (bit (capBlockSize cap)) - freeIndex);
    maxCount \<leftarrow> returnOk ( untypedFreeBytes `~shiftR~` objectSize);
    whenE (fromIntegral maxCount < nodeWindow) $
        throw $ NotEnoughMemory $ fromIntegral untypedFreeBytes;
    alignedFreeRef \<leftarrow> returnOk ( PPtr $ alignUp (fromPPtr freeRef) objectSize);
    returnOk $ Retype_ \<lparr>
        retypeSource= slot,
        retypeRegionBase= capPtr cap,
        retypeFreeRegionBase= alignedFreeRef,
        retypeNewType= newType,
        retypeNewSizeBits= userObjSize,
        retypeSlots= slots \<rparr>
  odE)
  | (_, _) \<Rightarrow>    throw $
    if invocationType label = UntypedRetype
        then TruncatedMessage
        else IllegalOperation
  )"

definition
invokeUntyped :: "untyped_invocation \<Rightarrow> unit kernel"
where
"invokeUntyped x0\<equiv> (case x0 of
    (Retype srcSlot base freeRegionBase newType userSize destSlots) \<Rightarrow>    (do
    cap \<leftarrow> getSlotCap srcSlot;
    when (base = freeRegionBase) $
        deleteObjects base (capBlockSize cap);
    totalObjectSize \<leftarrow> return ( (length destSlots) `~shiftL~` (getObjectSize newType userSize));
    freeRef \<leftarrow> return ( freeRegionBase + PPtr (fromIntegral totalObjectSize));
    updateCap srcSlot (cap \<lparr>capFreeIndex := getFreeIndex base freeRef\<rparr>);
    createNewObjects newType srcSlot destSlots freeRegionBase userSize
    od)
  )"


end
