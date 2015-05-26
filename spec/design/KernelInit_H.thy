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

defs noInitFailure_def:
"noInitFailure \<equiv> lift"

defs minNum4kUntypedObj_def:
"minNum4kUntypedObj \<equiv> 12"

defs maxNumFreememRegions_def:
"maxNumFreememRegions \<equiv> 2"

defs getAPRegion_def:
"getAPRegion kernelFrameEnd\<equiv> (do
   memRegions \<leftarrow> doKernelOp $ doMachineOp getMemoryRegions;
   subRegions \<leftarrow> return $ (flip map) memRegions (\<lambda> x.
        let (s,e) = x in
        if s < kernelFrameEnd then (kernelFrameEnd,e) else (s,e)
      );
   return $ map ptrFromPAddrRegion subRegions
od)"

defs initFreemem_def:
"initFreemem kernelFrameEnd uiRegion\<equiv> (do
   memRegions \<leftarrow> getAPRegion kernelFrameEnd;
   region \<leftarrow> return ( fromRegion uiRegion);
   fst' \<leftarrow> return ( fst \<circ> fromRegion);
   snd' \<leftarrow> return ( snd \<circ> fromRegion);
   subUI \<leftarrow> return ( \<lambda> r.
           if fst region \<ge> fst' r  \<and> snd region \<le> snd' r
           then [(fst' r, fst region), (snd region, snd' r)]
           else [(fst' r, snd' r)]);
   freeRegions \<leftarrow> return ( concat $ map subUI memRegions);
   freeRegions' \<leftarrow> return ( take maxNumFreememRegions $ freeRegions @
                      (if (length freeRegions < maxNumFreememRegions)
                       then replicate (maxNumFreememRegions - length freeRegions) (PPtr 0, PPtr 0)
                       else []));
   noInitFailure $ modify (\<lambda> st. st \<lparr> initFreeMemory := map Region freeRegions' \<rparr>)
od)"

defs allocRegion_def:
"allocRegion bits \<equiv>
    let
        s = 1 `~shiftL~` bits;
        align = (\<lambda>  b. (((b - 1) `~shiftR~` bits) + 1) `~shiftL~` bits);
        isUsable = (\<lambda>  reg. let r = (align \<circ> fst \<circ> fromRegion) reg in
                           r \<ge> (fst $ fromRegion reg) \<and> r + s - 1 \<le> (snd $ fromRegion reg));
        isAlignedUsable = (\<lambda>  reg.
            let
                b = fst $ fromRegion reg;
                t = snd $ fromRegion reg;
                (r, q) = (align b, align t)
            in (r = b \<or> q = t) \<and> t - b \<ge> s)
    in
                          (do
    freeMem \<leftarrow> noInitFailure $ gets initFreeMemory;
    (case isAlignedUsable `~break~` freeMem of
          (small, r#rest) \<Rightarrow>   (do
            (b, t) \<leftarrow> return ( fromRegion r);
            (result, region) \<leftarrow> return ( if align b = b then (b, Region (b + s, t)) else (t - s, Region (b, t - s)));
            noInitFailure $ modify (\<lambda> st. st \<lparr> initFreeMemory := small@ [region] @rest \<rparr>);
            return $ addrFromPPtr result
          od)
        | (_, []) \<Rightarrow>  
            (case isUsable `~break~` freeMem of
                  (small, r'#rest) \<Rightarrow>   (do
                    (b, t) \<leftarrow> return ( fromRegion r');
                    result \<leftarrow> return ( align b);
                    below \<leftarrow> return ( if result = b then [] else [Region (b, result)]);
                    above \<leftarrow> return ( if result + s = t then [] else [Region (result + s, t)]);
                    noInitFailure $ modify (\<lambda> st. st \<lparr> initFreeMemory := small@below@above@rest \<rparr>);
                    return $ addrFromPPtr result
                  od)
                | _ \<Rightarrow>   haskell_fail []
                )
        )
                          od)"

defs initKernel_def:
"initKernel entry initFrames initOffset kernelFrames bootFrames\<equiv> (do
        wordSize \<leftarrow> return ( finiteBitSize entry);
        uiRegion \<leftarrow> return ( coverOf $ map (\<lambda> x. Region (ptrFromPAddr x, (ptrFromPAddr x) + bit (pageBits))) initFrames);
        kernelRegion \<leftarrow> return ( coverOf $ map (\<lambda> x. Region (ptrFromPAddr x, (ptrFromPAddr x) + bit (pageBits))) kernelFrames);
        kePPtr \<leftarrow> return ( fst $ fromRegion $ uiRegion);
        kfEndPAddr \<leftarrow> return ( addrFromPPtr kePPtr);
        (startPPtr,endPPtr) \<leftarrow> return $ fromRegion uiRegion;
        vptrStart \<leftarrow> return ( (VPtr (fromPAddr $ addrFromPPtr $ startPPtr )) + initOffset);
        vptrEnd \<leftarrow> return ( (VPtr (fromPAddr $ addrFromPPtr $ endPPtr )) + initOffset);
        allMemory \<leftarrow> doMachineOp getMemoryRegions;
        initPSpace $ map (\<lambda> (s, e). (ptrFromPAddr s, ptrFromPAddr e))
                         allMemory;
        mapM (\<lambda> p. reserveFrame (ptrFromPAddr p) True) $ kernelFrames @ bootFrames;
        initKernelVM;
        initCPU;
        initPlatform;
        runInit $ (do
                initFreemem kfEndPAddr uiRegion;
                rootCNCap \<leftarrow> makeRootCNode;
                initInterruptController rootCNCap biCapIRQControl;
                ipcBufferVPtr \<leftarrow> return ( vptrEnd);
                ipcBufferCap \<leftarrow> createIPCBufferFrame rootCNCap ipcBufferVPtr;
                biFrameVPtr \<leftarrow> return ( vptrEnd + (1 `~shiftL~` pageBits));
                createBIFrame rootCNCap biFrameVPtr 0 1;
                createFramesOfRegion rootCNCap uiRegion True initOffset;
                itPDCap \<leftarrow> createITPDPTs rootCNCap vptrStart biFrameVPtr;
                writeITPDPTs rootCNCap itPDCap;
                itAPCap \<leftarrow> createITASIDPool rootCNCap;
                doKernelOp $ writeITASIDPool itAPCap itPDCap;
                createIdleThread;
                createInitialThread rootCNCap itPDCap ipcBufferCap entry ipcBufferVPtr biFrameVPtr;
                createUntypedObject rootCNCap (Region (0,0));
                createDeviceFrames rootCNCap;
                finaliseBIFrame;
                syncBIFrame
        od)
od)"

defs finaliseBIFrame_def:
"finaliseBIFrame\<equiv> (do
  cur \<leftarrow> noInitFailure $ gets $ initSlotPosCur;
  max \<leftarrow> noInitFailure $ gets $ initSlotPosMax;
  noInitFailure $ modify (\<lambda> s. s \<lparr> initBootInfo := (initBootInfo s) \<lparr>bifNullCaps := [cur  .e.  max - 1]\<rparr>\<rparr>)
od)"

defs createInitialThread_def:
"createInitialThread rootCNCap itPDCap ipcBufferCap entry ipcBufferVPtr biFrameVPtr\<equiv> (do
      tcbBits \<leftarrow> return ( objBits (makeObject::tcb));
      tcb' \<leftarrow> allocRegion tcbBits;
      tcbPPtr \<leftarrow> return ( ptrFromPAddr tcb');
      doKernelOp $ (do
         placeNewObject tcbPPtr (makeObject::tcb) 0;
         srcSlot \<leftarrow> locateSlot (capCNodePtr rootCNCap) biCapITCNode;
         destSlot \<leftarrow> getThreadCSpaceRoot tcbPPtr;
         cteInsert rootCNCap srcSlot destSlot;
         srcSlot \<leftarrow> locateSlot (capCNodePtr rootCNCap) biCapITPD;
         destSlot \<leftarrow> getThreadVSpaceRoot tcbPPtr;
         cteInsert itPDCap srcSlot destSlot;
         srcSlot \<leftarrow> locateSlot (capCNodePtr rootCNCap) biCapITIPCBuf;
         destSlot \<leftarrow> getThreadBufferSlot tcbPPtr;
         cteInsert ipcBufferCap srcSlot destSlot;
         threadSet (\<lambda> t. t\<lparr>tcbIPCBuffer := ipcBufferVPtr\<rparr>) tcbPPtr;
         activateInitialThread tcbPPtr entry biFrameVPtr;
         cap \<leftarrow> return $ ThreadCap tcbPPtr;
         slot \<leftarrow> locateSlot (capCNodePtr rootCNCap) biCapITTCB;
         insertInitCap slot cap
      od);
      return ()
od)"

defs createIdleThread_def:
"createIdleThread\<equiv> (do
      paddr \<leftarrow> allocRegion $ objBits (makeObject ::tcb);
      tcbPPtr \<leftarrow> return ( ptrFromPAddr paddr);
      doKernelOp $ (do
            placeNewObject tcbPPtr (makeObject::tcb) 0;
            modify (\<lambda> s. s \<lparr>ksIdleThread := tcbPPtr\<rparr>);
            setCurThread tcbPPtr;
            setSchedulerAction ResumeCurrentThread
      od);
      configureIdleThread tcbPPtr
od)"

defs createUntypedObject_def:
"createUntypedObject rootCNodeCap bootMemReuseReg\<equiv> (do
    regStart \<leftarrow> return ( (fst \<circ> fromRegion));
    regStartPAddr \<leftarrow> return ( (addrFromPPtr \<circ> regStart));
    regEnd \<leftarrow> return ( (snd \<circ> fromRegion));
    regEndPAddr \<leftarrow> return ( (addrFromPPtr \<circ> regEnd));
    slotBefore \<leftarrow> noInitFailure $ gets initSlotPosCur;
    mapM_x (\<lambda> i. provideUntypedCap rootCNodeCap i (fromIntegral pageBits) slotBefore)
             [regStartPAddr bootMemReuseReg, (regStartPAddr bootMemReuseReg + bit pageBits)  .e.  (regEndPAddr bootMemReuseReg - 1)];
    currSlot \<leftarrow> noInitFailure $ gets initSlotPosCur;
    mapM_x (\<lambda> _. (do
             paddr \<leftarrow> allocRegion pageBits;
             provideUntypedCap rootCNodeCap paddr (fromIntegral pageBits) slotBefore
    od)
                                                                                    )
          [(currSlot - slotBefore)  .e.  (fromIntegral minNum4kUntypedObj - 1)];
    freemem \<leftarrow> noInitFailure $ gets initFreeMemory;
    (flip mapM) (take maxNumFreememRegions freemem)
        (\<lambda> reg. (
            (\<lambda> f. mapM (f reg) [4  .e.  (finiteBitSize (undefined::machine_word)) - 2])
                (\<lambda> reg bits. (do
                    reg' \<leftarrow> (if Not (isAligned (regStartPAddr reg) (bits + 1))
                                \<and> (regEndPAddr reg) - (regStartPAddr reg) \<ge> bit bits
                        then (do
                            provideUntypedCap rootCNodeCap (regStartPAddr reg) (fromIntegral bits) slotBefore;
                            return $ Region (regStart reg + bit bits, regEnd reg)
                        od)
                        else return reg);
                    if Not (isAligned (regEndPAddr reg') (bits + 1)) \<and> (regEndPAddr reg') - (regStartPAddr reg') \<ge> bit bits
                        then (do
                            provideUntypedCap rootCNodeCap (regEndPAddr reg' - bit bits) (fromIntegral bits) slotBefore;
                            return $ Region (regStart reg', regEnd reg' - bit bits)
                        od)
                        else return reg' 
                od)
                                         )
        )
        );
    emptyReg \<leftarrow> return ( Region (PPtr 0, PPtr 0));
    freemem' \<leftarrow> return ( replicate maxNumFreememRegions emptyReg);
    slotAfter \<leftarrow> noInitFailure $ gets initSlotPosCur;
    noInitFailure $ modify (\<lambda> s. s \<lparr> initFreeMemory := freemem',
                      initBootInfo := (initBootInfo s) \<lparr>
                           bifUntypedObjCaps := [slotBefore  .e.  slotAfter - 1] \<rparr>\<rparr>)
od)"

defs mapTaskRegions_def:
"mapTaskRegions taskMappings\<equiv> (
        haskell_fail $ [] @ show taskMappings
)"

defs allocFrame_def:
"allocFrame \<equiv> allocRegion pageBits"

defs makeRootCNode_def:
"makeRootCNode\<equiv> (do
      slotBits \<leftarrow> return ( objBits (undefined::cte));
      levelBits \<leftarrow> return ( rootCNodeSize);
      frame \<leftarrow> liftM ptrFromPAddr $ allocRegion (levelBits + slotBits);
      rootCNCap \<leftarrow> doKernelOp $ createObject (fromAPIType CapTableObject) frame levelBits;
      rootCNCap \<leftarrow> return $ rootCNCap \<lparr>capCNodeGuardSize := 32 - levelBits\<rparr>;
      slot \<leftarrow> doKernelOp $ locateSlot (capCNodePtr rootCNCap) biCapITCNode;
      doKernelOp $ insertInitCap slot rootCNCap;
      return rootCNCap
od)"

defs provideCap_def:
"provideCap rootCNodeCap cap\<equiv> (do
    currSlot \<leftarrow> noInitFailure $ gets initSlotPosCur;
    maxSlot \<leftarrow> noInitFailure $ gets initSlotPosMax;
    when (currSlot \<ge> maxSlot) $ throwError InitFailure;
    slot \<leftarrow> doKernelOp $ locateSlot (capCNodePtr rootCNodeCap) currSlot;
    doKernelOp $ insertInitCap slot cap;
    noInitFailure $ modify (\<lambda> st. st \<lparr> initSlotPosCur := currSlot + 1 \<rparr>)
od)"

defs provideUntypedCap_def:
"provideUntypedCap rootCNodeCap pptr magnitudeBits slotPosBefore\<equiv> (do
    currSlot \<leftarrow> noInitFailure $ gets initSlotPosCur;
    i \<leftarrow> return ( currSlot - slotPosBefore);
    untypedObjs \<leftarrow> noInitFailure $ gets (bifUntypedObjPAddrs \<circ> initBootInfo);
    haskell_assert (length untypedObjs = fromIntegral i) [];
    untypedObjs' \<leftarrow> noInitFailure $ gets (bifUntypedObjSizeBits \<circ> initBootInfo);
    haskell_assert (length untypedObjs' = fromIntegral i) [];
    bootInfo \<leftarrow> noInitFailure $ gets initBootInfo;
    bootInfo' \<leftarrow> return ( bootInfo \<lparr> bifUntypedObjPAddrs := untypedObjs @ [pptr],
                               bifUntypedObjSizeBits := untypedObjs' @ [magnitudeBits] \<rparr>);
    noInitFailure $ modify (\<lambda> st. st \<lparr> initBootInfo := bootInfo' \<rparr>);
    provideCap rootCNodeCap $ UntypedCap_ \<lparr>
                                  capPtr= ptrFromPAddr pptr,
                                  capBlockSize= fromIntegral magnitudeBits,
                                  capFreeIndex= 0 \<rparr>
od)"

defs coverOf_def:
"coverOf x0\<equiv> (case x0 of
    [] \<Rightarrow>    Region (0,0)
  | [x] \<Rightarrow>    x
  | (x#xs) \<Rightarrow>  
    let
        (l,h) = fromRegion x;;
        (ll,hh) = fromRegion $ coverOf xs;;
        ln = if l \<le> ll then l else ll;;
        hn = if h \<le> hh then hh else h
    in
    Region (ln, hn)
  )"


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
