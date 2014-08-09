(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

header "Initialisation"

theory KernelInit_H
imports
  KI_Decls_H
  ArchRetype_H
  Retype_H
  Config_H
begin

defs allocRegion_def:
"allocRegion bits \<equiv>
    let
        s = 1 `~shiftL~` bits;
        align = (\<lambda>  b. (((b - 1) `~shiftR~` bits) + 1) `~shiftL~` bits);
        isUsable = (\<lambda>  (b, t). let r = align b in r \<ge> b \<and> r + s - 1 \<le> t)
    in
                          (do
    freeMem \<leftarrow> gets initFreeMemory;
    (case isUsable `~break~` freeMem of
          (small, (b, t)#rest) \<Rightarrow>   (do
            result \<leftarrow> return ( align b);
            below \<leftarrow> return ( if result = b then [] else [(b, result - 1)]);
            above \<leftarrow> return ( if result + s - 1 = t then [] else [(result + s, t)]);
            modify (\<lambda> st. st \<lparr> initFreeMemory := small@below@above@rest \<rparr>);
            return result
          od)
        | _ \<Rightarrow>   haskell_fail []
        )
                          od)"

defs allocFrame_def:
"allocFrame \<equiv> allocRegion pageBits"

defs allocPage_def:
"allocPage\<equiv> (do
    frame \<leftarrow> allocFrame;
    clr \<leftarrow> return ( (fromPPtr (ptrFromPAddr frame) `~shiftR~` pageBits)
            && mask pageColourBits);
    (cptr, slot) \<leftarrow> allocRootSlotWithColour clr;
    doKernelOp $ (do
        cap \<leftarrow> createInitPage frame;
        byteLength \<leftarrow> return ( 1 `~shiftL~` pageBits);
        doMachineOp $ clearMemory (ptrFromPAddr frame) byteLength;
        insertInitCap slot cap
    od);
    return $ (VPtr $ fromCPtr cptr, ptrFromPAddr frame, slot)
od)"

defs mapForInitTask_def:
"mapForInitTask frame page\<equiv> (do
    slot \<leftarrow> requestRootSlot $ CPtr $ fromVPtr page;
    doKernelOp $ (do
        cap \<leftarrow> createInitPage frame;
        insertInitCap slot cap
    od)
od)"

defs makeRootCNode_def:
"makeRootCNode\<equiv> (do
    slotBits \<leftarrow> return ( objBits (undefined::cte));
    levelBits \<leftarrow> return ( rootCNodeSize);
    levelSize \<leftarrow> return ( 1 `~shiftL~` levelBits);
    frame \<leftarrow> liftM ptrFromPAddr $ allocRegion (levelBits + slotBits);
    rootCNCap \<leftarrow> doKernelOp $
        createObject (fromAPIType CapTableObject) frame levelBits;
    rootCNCap' \<leftarrow> return ( rootCNCap \<lparr>
            capCNodeGuardSize := bitSize frame - pageBits - levelBits \<rparr>);
    rootSlots \<leftarrow> mapM (\<lambda> n. doKernelOp $ (do
        slot \<leftarrow> locateSlot (capCNodePtr rootCNCap') n;
        cptr \<leftarrow> return ( CPtr $ n `~shiftL~` pageBits);
        return (cptr, slot)
    od)
                           ) [0 .e. levelSize - 1];
    modify (\<lambda> st. st \<lparr> initFreeSlotsL1 := rootSlots \<rparr>);
    provideRegion $ BootRegion
        (CPtr 0) (CPtr $ (1 `~shiftL~` (pageBits+levelBits)) - 1)
        BRNodeL1 $ fromIntegral levelBits;
    return rootCNCap'
od)"

defs allocRootSlot_def:
"allocRootSlot\<equiv> (do
    freeSlots \<leftarrow> gets initFreeSlotsL1;
    (case freeSlots of
        result#rest \<Rightarrow>   (do
        modify (\<lambda> st. st \<lparr> initFreeSlotsL1 := rest \<rparr>);
        return result
        od)
      | _ \<Rightarrow>   haskell_fail []
      )
od)"

defs allocRootSlotWithColour_def:
"allocRootSlotWithColour c\<equiv> (do
    freeSlots \<leftarrow> gets initFreeSlotsL1;
    matchingSlots \<leftarrow> return ( filter (\<lambda> slot.
                fromCPtr (fst slot) `~shiftR~` pageBits
                    && mask pageColourBits = c) freeSlots);
    (case matchingSlots of
        result#_ \<Rightarrow>   (do
        modify (\<lambda> st. st \<lparr> initFreeSlotsL1 := delete result freeSlots \<rparr>);
        return result
        od)
      | _ \<Rightarrow>   haskell_fail $ [] @ show c @ []
      )
od)"

defs requestRootSlot_def:
"requestRootSlot addr\<equiv> (do
    freeSlots \<leftarrow> gets initFreeSlotsL1;
    (requested,others) \<leftarrow> return ( partition (\<lambda> x. fst x = addr) freeSlots);
    (case requested of
        [(_,result)] \<Rightarrow>   (do
        modify (\<lambda> st. st \<lparr> initFreeSlotsL1 := others \<rparr>);
        return result
        od)
      | [] \<Rightarrow>   haskell_fail $ [] @ show addr
      | _ \<Rightarrow>   haskell_fail []
      )
od)"

defs makeSlots_def:
"makeSlots\<equiv> (do
    slotBits \<leftarrow> return ( objBits (undefined::cte));
    slotSize \<leftarrow> return ( 1 `~shiftL~` slotBits);
    levelBits \<leftarrow> return ( pageBits - slotBits);
    levelSize \<leftarrow> return ( 1 `~shiftL~` levelBits);
    frame \<leftarrow> liftM ptrFromPAddr allocFrame;
    (cptr,slot) \<leftarrow> allocRootSlot;
    node \<leftarrow> doKernelOp $ (do
        cap \<leftarrow> createObject (fromAPIType CapTableObject)
            frame levelBits;
        cap' \<leftarrow> return ( cap \<lparr> capCNodeGuardSize := pageBits - levelBits \<rparr>);
        insertInitCap slot cap';
        return $ capCNodePtr cap'
    od);
    newSlots \<leftarrow> return ( map
            (\<lambda> n. (cptr + CPtr n, node + (slotSize * PPtr n)))
            [0 .e. levelSize - 1]);
    oldSlots \<leftarrow> gets initFreeSlotsL2;
    modify (\<lambda> st. st \<lparr> initFreeSlotsL2 := oldSlots @ newSlots \<rparr>);
    provideRegion $ BootRegion
        cptr (cptr - 1 + (CPtr $ 1 `~shiftL~` levelBits))
        BRNodeL2 $ fromIntegral levelBits
od)"

defs provideCap_def:
"provideCap cap\<equiv> (do
    freeSlots \<leftarrow> gets initFreeSlotsL2;
    when (freeSlots = []) makeSlots;
    freeSlots \<leftarrow> gets initFreeSlotsL2;
    (case freeSlots of
        (cptr,slot)#rest \<Rightarrow>   (do
        modify (\<lambda> st. st \<lparr> initFreeSlotsL2 := rest \<rparr>);
        unless (isNullCap cap) $ doKernelOp $ insertInitCap slot cap;
        return (cptr, slot)
        od)
      | _ \<Rightarrow>   haskell_fail []
      )
od)"

defs provideRegion_def:
"provideRegion r \<equiv> addRegionWithMerge r 0"

defs mergeBRs_def:
"mergeBRs x0 x1 n\<equiv> (case (x0, x1) of
    ((BootRegion a b BRLargeBlocks s), (BootRegion c d BRLargeBlocks t)) \<Rightarrow>   
    if
    (b = c - 1) \<and> (s && mask n = s) \<and> (t && mask n = 0) then Just (BootRegion a d BRLargeBlocks (s || t))
    else if
    True      then Nothing
    else undefined
  | ((BootRegion a b BRSmallBlocks s), (BootRegion c d BRSmallBlocks t)) \<Rightarrow>   
    if
    (b = c - 1) \<and> (s = t) then Just (BootRegion a d BRSmallBlocks s)
    else if
    True      then Nothing
    else undefined
  | ((BootRegion a b BRRootTask s), (BootRegion c d BRRootTask t)) \<Rightarrow>   
    if
    (b = c - 1) \<and> (s = t) then Just (BootRegion a d BRRootTask s)
    else if
    True      then Nothing
    else undefined
  | ((BootRegion b1 t1 BRDeviceCaps d1), (BootRegion b2 t2 BRDeviceCaps d2)) \<Rightarrow>   
    let
        n1 = fromCPtr $ t1 - b1 + 1;
        s1 = fromIntegral $ d1 && mask 8;
        s2 = fromIntegral $ d2 && mask 8
    in
    if
    (t1 = b2 - 1) \<and> (s1 = s2) \<and> (d1 `~shiftR~` s1 = (d2 `~shiftR~` s1) - n1) then Just (BootRegion b1 t2 BRDeviceCaps d1)
    else if
    True      then Nothing
    else undefined
  | (_, _) \<Rightarrow>    Nothing
  )"

defs addRegionWithMerge_def:
"addRegionWithMerge r n \<equiv>
    let
        tryMergeList = (\<lambda>  xs. (case xs of
              [] \<Rightarrow>   [r]
            | _ \<Rightarrow>   (case mergeBRs (last xs) r n of
                  None \<Rightarrow>   xs @ [r]
                | Some r' \<Rightarrow>   init xs @ [r']
                )
            ))
    in
                                (do
    regions \<leftarrow> gets initRegions;
    modify (\<lambda> st. st \<lparr> initRegions := tryMergeList regions \<rparr>)
                                od)"

defs initKernel_def:
"initKernel entry initFrames initOffset kernelFrames bootFrames\<equiv> (do
        pageSize \<leftarrow> return ( bit pageBits);
        wordSize \<leftarrow> return ( bitSize entry);
        allMemory \<leftarrow> doMachineOp getMemoryRegions;
        allFrames \<leftarrow> return ( concat $
              map (\<lambda> (s, e). [s, s+pageSize  .e.  s+(e-s) - 1])
                  allMemory);
        initPSpace $ map (\<lambda> (s, e). (ptrFromPAddr s, ptrFromPAddr e))
                         allMemory;
        mapM (\<lambda> p. reserveFrame (ptrFromPAddr p) True) kernelFrames;
        initKernelVM;
        when (null initFrames)
            $ haskell_fail [];
        when (null kernelFrames)
            $ haskell_fail [];
        unless (distinct initFrames)
            $ haskell_fail [];
        unless (distinct kernelFrames)
            $ haskell_fail [];
        when (0 `~elem~` initFrames)
            $ haskell_fail [];
        when (0 `~elem~` kernelFrames)
            $ haskell_fail [];
        unless (andList $ map (flip elem allFrames) initFrames)
            $ haskell_fail [];
        unless (andList $ map (flip elem allFrames) kernelFrames)
            $ haskell_fail [];
        when (orList $ map (flip elem initFrames) kernelFrames)
            $ haskell_fail [];
        unless (andList $ map (flip elem kernelFrames) bootFrames)
            $ haskell_fail [];
        unless (distinct allFrames)
            $ haskell_fail [];
        unless (isAligned (fromVPtr initOffset) pageBits)
            $ haskell_fail [];
        unless (andList $ map (\<lambda> b. isAligned b pageBits) initFrames)
            $ haskell_fail [];
        unless (andList $ map (\<lambda> b. isAligned b pageBits) kernelFrames)
            $ haskell_fail [];
        unless (distinct bootFrames)
            $ haskell_fail [];
        unless (andList $ map (\<lambda> (s, e). (e-s) < bit wordSize
                                      \<and> bit pageBits \<le> (e-s))
                          allMemory) $ haskell_fail [];
        emptyFrames \<leftarrow> return (
                filter (flip notElem ([0] @ initFrames @ kernelFrames)) allFrames);
        freeGroups \<leftarrow> return ( rangesBy (\<lambda> a b. a + pageSize = b)
                (sort emptyFrames));
        freeMemory \<leftarrow> return (
                map (\<lambda> fs. (head fs, last fs + pageSize - 1)) freeGroups);
        bootGroups \<leftarrow> return ( rangesBy (\<lambda> a b. a + pageSize = b) bootFrames);
        bootMemory \<leftarrow> return (
                map (\<lambda> fs. (head fs, last fs + pageSize - 1)) bootGroups);
        (bootInfo, infoVPtr, infoPPtr, tcbCap) \<leftarrow>
          runInit freeMemory bootMemory $ (do
            rootCNCap \<leftarrow> makeRootCNode;
            makeSlots;
            initMappings \<leftarrow> return ( map
                    (\<lambda> f. (f, (VPtr$fromIntegral f) - initOffset)) initFrames);
            (buffer, infoPtrs) \<leftarrow> mapTaskRegions initMappings;
            tcbCap \<leftarrow> createInitCaps rootCNCap buffer;
            createSmallBlockCaps;
            createDeviceCaps;
            untypedCount \<leftarrow> countUntypedCaps;
            freeSlotCount \<leftarrow> liftM length $ gets initFreeSlotsL2;
            when (freeSlotCount < untypedCount + minFreeSlots) $ (do
                makeSlots;
                untypedCount' \<leftarrow> countUntypedCaps;
                freeSlotCount' \<leftarrow> liftM length $ gets initFreeSlotsL2;
                haskell_assert (freeSlotCount' \<ge> untypedCount' + minFreeSlots) $
                    []
            od);
            createUntypedCaps;
            createFreeSlotRegions;
            createEmptyRegions;
            return (fst buffer, infoPtrs, tcbCap)
          od);
        bootInfoWords \<leftarrow> return ( wordsFromBootInfo bootInfo);
        intSize \<leftarrow> return ( bitSize (undefined::machine_word) div 8);
        haskell_assert (length bootInfoWords * intSize < 1 `~shiftL~` pageBits) $
            [] @ show bootInfo;
        mapM_x
            (split  storeWordUser
            )
            (zipE2 (infoPPtr) ( infoPPtr+(PPtr $ fromIntegral intSize)) (bootInfoWords));
        activateInitialThread (capTCBPtr tcbCap) entry infoVPtr
od)"

defs mapTaskRegions_def:
"mapTaskRegions taskMappings\<equiv> (do
    mapM (uncurry mapForInitTask) taskMappings;
    (bufferPtr,_,bufferSlot) \<leftarrow> allocPage;
    (infoVPtr,infoPPtr,_) \<leftarrow> allocPage;
    pages \<leftarrow> return ( sort $ map snd taskMappings);
    pageSize \<leftarrow> return ( 1 `~shiftL~` pageBits);
    pageGroups \<leftarrow> return ( [bufferPtr]#[infoVPtr]#
            rangesBy (\<lambda> a b. a + pageSize = b) pages);
    rootTaskRegions \<leftarrow> return (
            map (\<lambda> ps. BootRegion
                    (CPtr $ fromVPtr $ head ps)
                    (CPtr $ fromVPtr $ last ps + pageSize - 1)
                    BRRootTask (fromIntegral pageBits))
                $ pageGroups);
    mapM_x provideRegion rootTaskRegions;
    return ((bufferPtr, bufferSlot), (infoVPtr, infoPPtr))
od)"

defs createInitCaps_def:
"createInitCaps rootCNCap x1\<equiv> (case x1 of
    (bufferPtr, bufferSlot) \<Rightarrow>    (do
    (nullCapPtr,_) \<leftarrow> provideCap NullCap;
    haskell_assert (nullCapPtr = CPtr 0) [];
    tcbBits \<leftarrow> return ( objBits (undefined ::tcb));
    tcbFrame \<leftarrow> liftM ptrFromPAddr $ allocRegion $ tcbBits;
    idleFrame \<leftarrow> liftM ptrFromPAddr $ allocRegion $ tcbBits;
    tcbCap \<leftarrow> doKernelOp $ createObject (fromAPIType TCBObject) tcbFrame 0;
    idleCap \<leftarrow> doKernelOp $ createObject (fromAPIType TCBObject) idleFrame 0;
    provideCap tcbCap;
    (_,rootCNSlot) \<leftarrow> provideCap rootCNCap;
    (_,rootVNSlot) \<leftarrow> provideCap NullCap;
    irqCap \<leftarrow> initInterruptController;
    provideCap irqCap;
    provideCap DomainCap;
    initVSpace rootCNSlot rootVNSlot;
    doKernelOp $ (do
        threadCRoot \<leftarrow> getThreadCSpaceRoot (capTCBPtr tcbCap);
        cteInsert rootCNCap rootCNSlot threadCRoot;
        threadVRoot \<leftarrow> getThreadVSpaceRoot (capTCBPtr tcbCap);
        rootVNCap \<leftarrow> getSlotCap rootVNSlot;
        cteInsert rootVNCap rootVNSlot threadVRoot;
        threadSet (\<lambda> t. t \<lparr> tcbIPCBuffer := bufferPtr \<rparr>)
            (capTCBPtr tcbCap);
        threadBuffer \<leftarrow> getThreadBufferSlot (capTCBPtr tcbCap);
        bufferCap \<leftarrow> getSlotCap bufferSlot;
        bufferCap' \<leftarrow> nullCapOnFailure $ deriveCap bufferSlot bufferCap;
        cteInsert bufferCap' bufferSlot threadBuffer;
        setPriority (capTCBPtr tcbCap) maxPriority
    od);
    configureIdleThread (capTCBPtr idleCap);
    doKernelOp $ setIdleThread (capTCBPtr idleCap);
    firstFreeSlot \<leftarrow> liftM (fst \<circ> head) $ gets initFreeSlotsL2;
    provideRegion $ BootRegion (CPtr 0) (firstFreeSlot - 1) BRInitCaps 0;
    return tcbCap
    od)
  )"

defs createUntypedCaps_def:
"createUntypedCaps\<equiv> (do
    freeRegions \<leftarrow> getUntypedRegions;
    modify (\<lambda> st. st \<lparr> initFreeMemory := [], initBootMemory := [] \<rparr>);
    blocks \<leftarrow> return ( concat (map (uncurry makeBlockList) freeRegions));
    mapM_x storeLargeBlock blocks
od)"

defs storeLargeBlock_def:
"storeLargeBlock x0\<equiv> (case x0 of
    (addr, bits) \<Rightarrow>    (do
   ptr \<leftarrow> return ( ptrFromPAddr addr);
   (cptr, _) \<leftarrow> provideCap (UntypedCap ptr bits 0);
   addRegionWithMerge (BootRegion cptr cptr BRLargeBlocks (bit bits)) bits
    od)
  )"

defs makeBlockList_def:
"makeBlockList s e \<equiv>
    let
        n = bitSize s;
        magnitudes = [0  .e.  n - 1];
        makeLowBlock = (\<lambda>  ((start, end), xs, ys) b.
            if start !! b \<and> start \<le> end
            then ((start + bit b, end), (start, b) # xs, ys)
            else ((start, end), xs, ys));
        makeHighBlock = (\<lambda>  ((start, end), xs, ys) b.
            if (end + 1) !! b \<and> start \<le> end
            then ((start, end - bit b), xs, (end - bit b + 1, b) # ys)
            else ((start, end), xs, ys));
        makeBlocks = (\<lambda>  v b. makeLowBlock (makeHighBlock v b) b);
        result = foldl makeBlocks ((s, e), [], []) magnitudes;
        returnVal = (\<lambda>  (_, low, high). reverse high @ reverse low)
    in
                           returnVal result"

defs countUntypedCaps_def:
"countUntypedCaps\<equiv> (do
    freeRegions \<leftarrow> getUntypedRegions;
    return $ sum $ map (\<lambda> (b,t). length (makeBlockList b t)) freeRegions
od)"

defs getUntypedRegions_def:
"getUntypedRegions\<equiv> gets (\<lambda> st. initFreeMemory st @ initBootMemory st)"

defs createDeviceCaps_def:
"createDeviceCaps\<equiv> (do
    devices \<leftarrow> doKernelOp $ doMachineOp getDeviceRegions;
    forM_x devices (\<lambda> (base, end). (do
            cap \<leftarrow> doKernelOp $ createDeviceCap (base, end);
            (cptr,_) \<leftarrow> provideCap cap;
            rawmagnitude \<leftarrow> return ( end - base);
            sz \<leftarrow> return ( find (\<lambda> sz. rawmagnitude = bit (pageBitsForSize sz))
                          [minBound  .e.  maxBound]);
            magnitude \<leftarrow> (case sz of
                  Some magnitude \<Rightarrow>   return $ pageBitsForSize magnitude
                | None \<Rightarrow>   haskell_fail []
                );
            provideRegion $ BootRegion cptr cptr BRDeviceCaps
                (fromIntegral base || fromIntegral magnitude)
    od))
od)"

defs createSmallBlockCaps_def:
"createSmallBlockCaps\<equiv> (do
    caps \<leftarrow> replicateM minSmallBlocks $ (do
        frame \<leftarrow> liftM ptrFromPAddr allocFrame;
        return $ UntypedCap frame pageBits 0
    od);
    storeSmallBlockCaps caps
od)"

defs storeSmallBlockCaps_def:
"storeSmallBlockCaps \<equiv> mapM_x storeSmallBlockCap"

defs storeSmallBlockCap_def:
"storeSmallBlockCap cap\<equiv> (do
    (cptr, _) \<leftarrow> provideCap cap;
    dWord \<leftarrow> return ( fromIntegral pageBits);
    provideRegion $ BootRegion cptr cptr BRSmallBlocks dWord
od)"

defs createFreeSlotRegions_def:
"createFreeSlotRegions\<equiv> (do
    slots \<leftarrow> gets initFreeSlotsL2;
    modify (\<lambda> st. st \<lparr> initFreeSlotsL2 := [] \<rparr>);
    haskell_assert (length slots \<ge> minFreeSlots) $
        [] @ show (length slots) @
        [] @ show minFreeSlots;
    ranges \<leftarrow> return ( rangesBy (\<lambda> a b. a = b - 1) $ sort $ map fst slots);
    mapM_x (\<lambda> slots. provideRegion $
            BootRegion (head slots) (last slots) BRFreeSlots 0
        ) ranges
od)"

defs createEmptyRegions_def:
"createEmptyRegions\<equiv> (do
    l1magnitude \<leftarrow> return ( bit (pageBits + rootCNodeSize));
    slots \<leftarrow> gets initFreeSlotsL1;
    modify (\<lambda> st. st \<lparr> initFreeSlotsL1 := [] \<rparr>);
    pageSize \<leftarrow> return ( 1 `~shiftL~` pageBits);
    ranges \<leftarrow> return ( rangesBy (\<lambda> a b. a + pageSize = b) $ sort $ map fst slots);
    mapM_x (\<lambda> slots. provideRegion $
            BootRegion (head slots) (last slots + pageSize - 1) BREmpty 0
        ) ranges;
    provideRegion $ BootRegion l1magnitude maxBound BREmpty 0
od)"


consts
  newKSDomSchedule :: "(domain \<times> machine_word) list"
  newKSDomScheduleIdx :: nat
  newKSCurDomain :: domain
  newKSDomainTime :: machine_word
 
definition
  newKernelState :: "machine_word \<Rightarrow> kernel_state"
where
"newKernelState arg \<equiv> \<lparr>
        ksPSpace= newPSpace,
        gsUserPages= (\<lambda>x. None),
        gsCNodes= (\<lambda>x. None),
        ksDomScheduleIdx = newKSDomScheduleIdx,
        ksDomSchedule = newKSDomSchedule,
        ksCurDomain = newKSCurDomain,
        ksDomainTime = newKSDomainTime,
        ksReadyQueues= const [],
        ksCurThread= error [],
        ksIdleThread= error [],
        ksSchedulerAction= ResumeCurrentThread,
        ksInterruptState= error [],
        ksWorkUnitsCompleted= 0,
        ksArchState= fst (ArchStateData_H.newKernelState arg),
        ksMachineState= init_machine_state
	\<rparr>"

end
