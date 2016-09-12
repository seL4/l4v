(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file Untyped_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Untyped Objects"

theory Untyped_H
imports
  RetypeDecls_H
  CSpaceDecls_H
  CNode_H
  Invocations_H
  InvocationLabels_H
  Config_H
  "../machine/MachineExports"
begin

consts
  cNodeOverlap :: "(machine_word \<Rightarrow> nat option) \<Rightarrow> (machine_word \<Rightarrow> bool) \<Rightarrow> bool"

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
    rangeCheck userObjSize 0 $ finiteBitSize nullPointer - 3;
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
        mapM (locateSlotCap nodeCap)
            [nodeOffset  .e.  nodeOffset+nodeWindow - 1];
    mapME_x ensureEmptySlot slots;
    reset \<leftarrow> withoutFailure $ constOnFailure False $ (doE
            ensureNoChildren slot;
            returnOk True
    odE);
    freeIndex \<leftarrow> returnOk ( if reset then 0 else capFreeIndex cap);
    freeRef \<leftarrow> returnOk ( getFreeRef (capPtr cap) freeIndex);
    objectSize \<leftarrow> returnOk ( getObjectSize newType userObjSize);
    untypedFreeBytes \<leftarrow> returnOk ( (bit (capBlockSize cap)) - freeIndex);
    maxCount \<leftarrow> returnOk ( untypedFreeBytes `~shiftR~` objectSize);
    whenE (fromIntegral maxCount < nodeWindow) $
        throw $ NotEnoughMemory $ fromIntegral untypedFreeBytes;
    notFrame \<leftarrow> returnOk ( Not $ isFrameType newType);
    isDevice \<leftarrow> returnOk ( capIsDevice cap);
    whenE (isDevice \<and> notFrame \<and> newType \<noteq> fromAPIType Untyped) $
           throw $ InvalidArgument 1;
    alignedFreeRef \<leftarrow> returnOk ( PPtr $ alignUp (fromPPtr freeRef) objectSize);
    returnOk $ Retype_ \<lparr>
        retypeSource= slot,
        retypeResetUntyped= reset,
        retypeRegionBase= capPtr cap,
        retypeFreeRegionBase= alignedFreeRef,
        retypeNewType= newType,
        retypeNewSizeBits= userObjSize,
        retypeSlots= slots,
        retypeIsDevice= isDevice \<rparr>
  odE)
  | (_, _) \<Rightarrow>    throw $
    if invocationType label = UntypedRetype
        then TruncatedMessage
        else IllegalOperation
  )"

definition
resetUntypedCap :: "machine_word \<Rightarrow> unit kernel_p"
where
"resetUntypedCap slot\<equiv> (doE
    cap \<leftarrow> withoutPreemption $ getSlotCap slot;
    sz \<leftarrow> returnOk ( capBlockSize cap);
    unlessE (capFreeIndex cap = 0) $ (doE
        withoutPreemption $ deleteObjects (capPtr cap) sz;
        if (capIsDevice cap \<or> sz < resetChunkBits)
            then withoutPreemption $ (do
                unless (capIsDevice cap) $ doMachineOp $
                    clearMemory (PPtr (fromPPtr (capPtr cap))) (1 `~shiftL~` sz);
                updateFreeIndex slot 0
            od)
            else forME_x (reverse [capPtr cap, capPtr cap + (1 `~shiftL~` resetChunkBits)  .e.
                            getFreeRef (capPtr cap) (capFreeIndex cap) - 1])
                (\<lambda> addr. (doE
                    withoutPreemption $ doMachineOp $ clearMemory
                        (PPtr (fromPPtr addr)) (1 `~shiftL~` resetChunkBits);
                    withoutPreemption $ updateFreeIndex slot
                        (getFreeIndex (capPtr cap) addr);
                    preemptionPoint
                odE))
    odE)
odE)"

definition
invokeUntyped :: "untyped_invocation \<Rightarrow> unit kernel_p"
where
"invokeUntyped x0\<equiv> (case x0 of
    (Retype srcSlot reset base retypeBase newType userSize destSlots isDev) \<Rightarrow>    (doE
    whenE reset $ resetUntypedCap srcSlot;
    withoutPreemption $ (do
        totalObjectSize \<leftarrow> return ( (length destSlots) `~shiftL~` (getObjectSize newType userSize));
        stateAssert (\<lambda> x. Not (cNodeOverlap (gsCNodes x)
                (\<lambda> x. fromPPtr retypeBase \<le> x
                    \<and> x \<le> fromPPtr retypeBase + fromIntegral totalObjectSize - 1)))
            [];
        freeRef \<leftarrow> return ( retypeBase + PPtr (fromIntegral totalObjectSize));
        updateFreeIndex srcSlot (getFreeIndex base freeRef);
        createNewObjects newType srcSlot destSlots retypeBase userSize isDev
    od)
    odE)
  )"


end
