(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
  VSpace lookup code.
*)

theory ArchVSpace_H
imports
  "../CNode_H"
  "../KI_Decls_H"
  ArchVSpaceDecls_H
begin
context Arch begin global_naming ARM_H


defs globalsBase_def:
"globalsBase \<equiv> VPtr 0xffffc000"

defs idleThreadStart_def:
"idleThreadStart \<equiv> globalsBase + VPtr 0x100"

defs idleThreadCode_def:
"idleThreadCode \<equiv>
    [ 0xe3a00000
    , 0xeafffffc
    ]"

defs mapKernelWindow_def:
"mapKernelWindow\<equiv> (do
    baseoffset \<leftarrow> return ( kernelBase `~shiftR~` pageBitsForSize (ARMSection));
    pdeBits \<leftarrow> return ( objBits (undefined ::pde));
    pteBits \<leftarrow> return ( objBits (undefined ::pte));
    ptSize \<leftarrow> return ( ptBits - pteBits);
    pdSize \<leftarrow> return ( pdBits - pdeBits);
    globalPD \<leftarrow> gets $ armKSGlobalPD \<circ> ksArchState;
    globalPTs \<leftarrow> gets $ armKSGlobalPTs \<circ> ksArchState;
    startentry \<leftarrow> return $ (PPtr (fromPPtr globalPD ));
    deleteObjects (startentry) pdBits;
    placeNewObject (startentry) (makeObject ::pde) pdSize;
    forM_x [baseoffset, baseoffset+16  .e.  (bit pdSize) - 16 - 1] $ createSectionPDE;
    forM_x [(bit pdSize) - 16, (bit pdSize) - 2] (\<lambda> offset. (do
          virt \<leftarrow> return ( offset `~shiftL~` pageBitsForSize (ARMSection));
          phys \<leftarrow> return ( addrFromPPtr $ PPtr $ fromVPtr virt);
          pde \<leftarrow> return ( SectionPDE_ \<lparr>
                  pdeFrame= phys,
                  pdeParity= True,
                  pdeDomain= 0,
                  pdeCacheable= True,
                  pdeGlobal= True,
                  pdeExecuteNever= False,
                  pdeRights= VMKernelOnly \<rparr>);
          slot \<leftarrow> return ( globalPD + PPtr ((fromVPtr offset) `~shiftL~` pdeBits));
          storePDE slot pde
    od));
    paddr \<leftarrow> return ( addrFromPPtr $ PPtr $ fromPPtr $ head globalPTs);
    pde \<leftarrow> return ( PageTablePDE_ \<lparr>pdeTable= paddr ,pdeParity= True, pdeDomain= 0\<rparr>);
    slot \<leftarrow> return ( globalPD + PPtr (((bit pdSize) - 1) `~shiftL~` pdeBits));
    deleteObjects (PPtr $ fromPPtr $ head globalPTs) ptBits;
    placeNewObject (PPtr $ fromPPtr $ head globalPTs) (makeObject ::pte) ptSize;
    storePDE slot pde;
    mapGlobalsFrame;
    kernelDevices \<leftarrow> doMachineOp getKernelDevices;
    mapM_x mapKernelDevice kernelDevices
od)"

defs createSectionPDE_def:
"createSectionPDE offset\<equiv> (do
    pdeBits \<leftarrow> return ( objBits (undefined ::pde));
    pteBits \<leftarrow> return ( objBits (undefined ::pte));
    globalPD \<leftarrow> gets $ armKSGlobalPD \<circ> ksArchState;
    virt \<leftarrow> return ( fromVPtr $ offset `~shiftL~` pageBitsForSize (ARMSection));
    phys \<leftarrow> return ( addrFromPPtr $ PPtr virt);
    base \<leftarrow> return ( fromVPtr offset);
    pde \<leftarrow> return ( SuperSectionPDE_ \<lparr>
            pdeFrame= phys,
            pdeParity= True,
            pdeCacheable= True,
            pdeGlobal= True,
            pdeExecuteNever= False,
            pdeRights= VMKernelOnly \<rparr>);
    slots \<leftarrow> return ( map (\<lambda> n. globalPD + PPtr (n `~shiftL~` pdeBits))
            [base  .e.  base + 15]);
    (flip $ mapM_x ) slots (\<lambda> slot.  storePDE slot pde)
od)"

defs mapKernelDevice_def:
"mapKernelDevice x0\<equiv> (case x0 of
    (addr, ptr) \<Rightarrow>    (do
    vptr \<leftarrow> return ( VPtr $ fromPPtr ptr);
    mapKernelFrame addr vptr VMKernelOnly $ VMAttributes False False True
    od)
  )"

defs activateGlobalVSpace_def:
"activateGlobalVSpace\<equiv> (do
    globalPD \<leftarrow> gets $ armKSGlobalPD \<circ> ksArchState;
    doMachineOp $ (do
        setCurrentPD $ addrFromPPtr globalPD;
        invalidateTLB
    od)
od)"

defs createITPDPTs_def:
"createITPDPTs rootCNCap vptrStart biFrameVPtr\<equiv>  (doE
    pdSize \<leftarrow> returnOk ( pdBits - objBits (makeObject ::pde));
    ptSize \<leftarrow> returnOk ( ptBits - objBits (makeObject ::pte));
    pdPPtr \<leftarrow> allocRegion pdBits;
    doKernelOp $ placeNewObject (ptrFromPAddr pdPPtr) (makeObject::pde) pdSize;
    pdCap \<leftarrow> returnOk $ ArchObjectCap $ PageDirectoryCap (ptrFromPAddr pdPPtr) (Just itASID);
    slot  \<leftarrow> doKernelOp $ locateSlotCap rootCNCap biCapITPD;
    doKernelOp $ insertInitCap slot $ pdCap;
    slotBefore \<leftarrow> noInitFailure $ gets $ initSlotPosCur;
    btmVPtr \<leftarrow> returnOk ( vptrStart `~shiftR~` (pdSize + pageBits) `~shiftL~` (pdSize + pageBits));
    step \<leftarrow> returnOk ( 1 `~shiftL~` (ptSize + pageBits));
    topVPtr \<leftarrow> returnOk ( biFrameVPtr + (bit biFrameSizeBits) - 1);
    forME_x [btmVPtr,btmVPtr + step  .e.  topVPtr] (\<lambda> vptr. (doE
        ptPPtr \<leftarrow> allocRegion ptBits;
        doKernelOp $ placeNewObject (ptrFromPAddr ptPPtr) (makeObject::pte) ptSize;
        provideCap rootCNCap $ ArchObjectCap $ PageTableCap (ptrFromPAddr ptPPtr) (Just (itASID, vptr))
    odE));
    slotAfter \<leftarrow> noInitFailure $ gets initSlotPosCur;
    bootInfo \<leftarrow> noInitFailure $ gets initBootInfo;
    bootInfo' \<leftarrow> returnOk ( bootInfo \<lparr>bifUIPDCaps := [slotBefore - 1  .e.  slotBefore - 1], bifUIPTCaps := [slotBefore  .e.  slotAfter - 1] \<rparr>);
    noInitFailure $ modify (\<lambda> s. s \<lparr> initBootInfo := bootInfo' \<rparr>);
    returnOk pdCap
odE)"

defs writeITPDPTs_def:
"writeITPDPTs rootCNCap pdCap \<equiv>
  (case pdCap of
      ArchObjectCap cap \<Rightarrow>   (doE
      doKernelOp $ copyGlobalMappings $ capPDBasePtr cap;
      ptSlots \<leftarrow> noInitFailure $ gets $ bifUIPTCaps \<circ> initBootInfo;
      doKernelOp $ (
          (flip mapM) ptSlots (\<lambda> pos. (do
              slot \<leftarrow> locateSlotCap rootCNCap pos;
              cte \<leftarrow> getCTE slot;
              mapITPTCap pdCap (cteCap cte)
          od)
           )
      );
      frameSlots \<leftarrow> noInitFailure $ gets $ bifUIFrameCaps \<circ> initBootInfo;
      doKernelOp $ (do
           (flip mapM) frameSlots (\<lambda> pos. (do
              slot \<leftarrow> locateSlotCap rootCNCap pos;
              cte \<leftarrow> getCTE slot;
              mapITFrameCap pdCap (cteCap cte)
           od)
                                              );
           slot \<leftarrow> locateSlotCap rootCNCap biCapITIPCBuf;
           cte \<leftarrow> getCTE slot;
           mapITFrameCap pdCap (cteCap cte);
           slot \<leftarrow> locateSlotCap rootCNCap biCapBIFrame;
           cte \<leftarrow> getCTE slot;
           mapITFrameCap pdCap (cteCap cte)
      od)
      odE)
    | _ \<Rightarrow>   haskell_fail $ (show pdCap) @ []
    )"

defs createITASIDPool_def:
"createITASIDPool rootCNCap\<equiv> (doE
    apPPtr \<leftarrow> allocRegion $ objBits (undefined ::asidpool);
    doKernelOp $ placeNewObject (ptrFromPAddr apPPtr) (makeObject::asidpool) 0;
    slot \<leftarrow> doKernelOp $ locateSlotCap rootCNCap biCapITASIDPool;
    asidPoolCap \<leftarrow> returnOk $ ArchObjectCap $ ASIDPoolCap (ptrFromPAddr apPPtr) 0;
    doKernelOp $ insertInitCap slot asidPoolCap;
    slot \<leftarrow> doKernelOp $ locateSlotCap rootCNCap biCapASIDControl;
    asidControlCap \<leftarrow> returnOk $ ArchObjectCap $ ASIDControlCap;
    doKernelOp $ insertInitCap slot asidControlCap;
    returnOk asidPoolCap
odE)"

defs writeITASIDPool_def:
"writeITASIDPool apCap pdCap\<equiv> (do
    apPtr \<leftarrow> (case apCap of
                     ArchObjectCap (ASIDPoolCap ptr _) \<Rightarrow>   return ptr
                   | _ \<Rightarrow>   haskell_fail []
                   );
    pdPtr \<leftarrow> (case pdCap of
                     ArchObjectCap (PageDirectoryCap ptr _) \<Rightarrow>   return ptr
                   | _ \<Rightarrow>   haskell_fail []
                   );
 ap \<leftarrow> liftM (inv ASIDPool) $  getObject apPtr;
    ap' \<leftarrow> return ( ap aLU [(itASID, Just pdPtr)]);
    setObject apPtr (ASIDPool ap');
    asidTable \<leftarrow> gets (armKSASIDTable \<circ> ksArchState);
    asidTable' \<leftarrow> return ( asidTable aLU [(asidHighBitsOf itASID, Just apPtr)]);
    modify (\<lambda> s. s \<lparr>
         ksArchState := (ksArchState s) \<lparr> armKSASIDTable := asidTable' \<rparr>\<rparr>)
od)"

defs mapITPTCap_def:
"mapITPTCap pdCap ptCap\<equiv> (do
    pd \<leftarrow> (case pdCap of
                ArchObjectCap (PageDirectoryCap ptr _) \<Rightarrow>   return ptr
              | _ \<Rightarrow>   haskell_fail []
              );
    ptCap' \<leftarrow> (case ptCap of
                    ArchObjectCap c \<Rightarrow>   return c
                  | _ \<Rightarrow>   haskell_fail []
                  );
    (pt,vptr) \<leftarrow> (case ptCap' of
                              PageTableCap pt' (Some (_, vptr')) \<Rightarrow>   return (pt', vptr')
                            | _ \<Rightarrow>   haskell_fail $ [] @ (show ptCap)
                            );
    offset \<leftarrow> return ( fromVPtr $ vptr `~shiftR~` pageBitsForSize ARMSection);
    targetSlot \<leftarrow> return ( pd + (PPtr $ offset `~shiftL~` 2));
    pde \<leftarrow> return ( PageTablePDE_ \<lparr>
            pdeTable= addrFromPPtr pt,
            pdeParity= True,
            pdeDomain= 0 \<rparr>);
    storePDE targetSlot pde
od)"

defs mapITFrameCap_def:
"mapITFrameCap pdCap frameCap\<equiv> (do
    pd' \<leftarrow> (case pdCap of
                 ArchObjectCap (PageDirectoryCap ptr _) \<Rightarrow>   return ptr
               | _ \<Rightarrow>   haskell_fail $ [] @ (show pdCap)
               );
    frameCap' \<leftarrow> (case frameCap of
                       ArchObjectCap c \<Rightarrow>   return c
                     | _ \<Rightarrow>   haskell_fail $ [] @ (show frameCap)
                     );
    (frame,vptr) \<leftarrow> (case frameCap' of
                                PageCap frame' _ _ (Some (_, vptr')) \<Rightarrow>   return (frame', vptr')
                              | _ \<Rightarrow>   haskell_fail $ [] @ (show frameCap)
                              );
    offset \<leftarrow> return ( fromVPtr $ vptr `~shiftR~` pageBitsForSize ARMSection);
    pd \<leftarrow> return ( pd' + (PPtr $ offset `~shiftL~` 2));
    pde \<leftarrow> getObject pd;
    pt \<leftarrow> (case pde of
                       PageTablePDE ref _ _ \<Rightarrow>   return $ ptrFromPAddr ref
                     | _ \<Rightarrow>   haskell_fail $ [] @ (show pd) @ [] @ (show pde)
                     );
    offset \<leftarrow> return ( fromVPtr $ ((vptr &&(mask $ pageBitsForSize ARMSection))
                               `~shiftR~` pageBitsForSize ARMSmallPage));
    targetSlot \<leftarrow> return ( pt + (PPtr $ offset `~shiftL~` 2));
    pte \<leftarrow> return ( SmallPagePTE_ \<lparr>
            pteFrame= addrFromPPtr frame,
            pteCacheable= True,
            pteGlobal= False,
            pteExecuteNever= False,
            pteRights= VMReadWrite \<rparr>);
    storePTE targetSlot pte
od)"

defs createIPCBufferFrame_def:
"createIPCBufferFrame rootCNCap vptr\<equiv> (doE
      pptr \<leftarrow> allocFrame;
      doKernelOp $ doMachineOp $ clearMemory (ptrFromPAddr pptr) (1 `~shiftL~` pageBits);
      cap \<leftarrow> createITFrameCap (ptrFromPAddr pptr) vptr (Just itASID) False;
      slot \<leftarrow> doKernelOp $ locateSlotCap rootCNCap biCapITIPCBuf;
      doKernelOp $ insertInitCap slot cap;
      bootInfo \<leftarrow> noInitFailure $ gets (initBootInfo);
      bootInfo' \<leftarrow> returnOk ( bootInfo \<lparr> bifIPCBufVPtr := vptr\<rparr>);
      noInitFailure $ modify (\<lambda> s. s \<lparr>initBootInfo := bootInfo' \<rparr>);
      returnOk cap
odE)"

defs createBIFrame_def:
"createBIFrame rootCNCap vptr nodeId numNodes\<equiv> (doE
      pptr \<leftarrow> allocFrame;
      bootInfo \<leftarrow> noInitFailure $ gets initBootInfo;
      bootInfo' \<leftarrow> returnOk ( bootInfo \<lparr> bifNodeID := nodeId,
                                 bifNumNodes := numNodes \<rparr>);
      noInitFailure $ modify (\<lambda> s. s \<lparr>
          initBootInfo := bootInfo',
          initBootInfoFrame := pptr,
          initSlotPosCur := biCapDynStart
          \<rparr>);
      doKernelOp $ doMachineOp $ clearMemory (ptrFromPAddr pptr) (1 `~shiftL~` pageBits);
      cap \<leftarrow> createITFrameCap (ptrFromPAddr pptr) vptr (Just itASID) False;
      slot \<leftarrow> doKernelOp $ locateSlotCap rootCNCap biCapBIFrame;
      doKernelOp $ insertInitCap slot cap;
      returnOk cap
odE)"

defs createITFrameCap_def:
"createITFrameCap pptr vptr asid large\<equiv> (doE
    sz \<leftarrow> returnOk ( if large then ARMLargePage else ARMSmallPage);
    addr \<leftarrow> returnOk ( (case asid of
                      Some asid' \<Rightarrow>   Just (asid', vptr)
                    | None \<Rightarrow>   Nothing
                    ));
    frame \<leftarrow> returnOk ( PageCap_ \<lparr>
             capVPBasePtr= pptr,
             capVPRights= VMReadWrite,
             capVPSize= sz,
             capVPMappedAddress= addr \<rparr>);
    returnOk $ ArchObjectCap $ frame
odE)"

defs createFramesOfRegion_def:
"createFramesOfRegion rootCNCap region doMap\<equiv> (doE
    curSlotPos \<leftarrow> noInitFailure $ gets initSlotPosCur;
    (startPPtr, endPPtr) \<leftarrow> returnOk $ fromRegion region;
    forME_x [startPPtr,startPPtr + (bit pageBits)  .e.  endPPtr] (\<lambda> ptr. (doE
        vptr \<leftarrow> vptrFromPPtr $ ptr;
        frameCap \<leftarrow> if doMap then
                    createITFrameCap ptr vptr (Just itASID) False
                    else createITFrameCap ptr 0 Nothing False;
        provideCap rootCNCap frameCap
    odE));
    slotPosAfter \<leftarrow> noInitFailure $ gets initSlotPosCur;
    bootInfo \<leftarrow> noInitFailure $ gets initBootInfo;
    bootInfo' \<leftarrow> returnOk ( bootInfo \<lparr> bifUIFrameCaps := [curSlotPos  .e.  slotPosAfter - 1] \<rparr>);
    noInitFailure $ modify (\<lambda> s. s \<lparr> initBootInfo := bootInfo' \<rparr>)
odE)"

defs mapGlobalsFrame_def:
"mapGlobalsFrame\<equiv> (do
    globalsFrame \<leftarrow> gets $ armKSGlobalsFrame \<circ> ksArchState;
    mapKernelFrame (addrFromPPtr globalsFrame) globalsBase VMReadOnly $
        VMAttributes True True True;
    writeIdleCode
od)"

defs writeIdleCode_def:
"writeIdleCode\<equiv> (do
    globalsFrame \<leftarrow> gets $ armKSGlobalsFrame \<circ> ksArchState;
    offset \<leftarrow> return ( fromVPtr $ idleThreadStart - globalsBase);
    doMachineOp $ mapM_x
        (split  storeWord
        )
        (zipE2 (globalsFrame + PPtr offset) ( globalsFrame + PPtr offset + 4) (idleThreadCode))
od)"

defs mapKernelFrame_def:
"mapKernelFrame paddr vaddr vmrights attributes\<equiv> (do
    idx \<leftarrow> return ( fromVPtr $ ( (vaddr && (mask $ pageBitsForSize ARMSection))
                          `~shiftR~` pageBitsForSize ARMSmallPage));
    globalPT \<leftarrow> getARMGlobalPT;
    pte \<leftarrow> return ( SmallPagePTE_ \<lparr>
                 pteFrame= paddr,
                 pteCacheable= armPageCacheable attributes,
                 pteGlobal= True,
                 pteExecuteNever= False,
                 pteRights= vmrights \<rparr>);
    storePTE (PPtr ((fromPPtr globalPT) + (idx `~shiftL~` 2))) pte
od)"

defs getARMGlobalPT_def:
"getARMGlobalPT\<equiv> (do
    pt \<leftarrow> gets (head \<circ> armKSGlobalPTs \<circ> ksArchState);
    return pt
od)"

defs createDeviceFrames_def:
"createDeviceFrames rootCNodeCap\<equiv> (doE
    deviceRegions \<leftarrow> doKernelOp $ doMachineOp getDeviceRegions;
    (flip mapME_x) deviceRegions (\<lambda> (start,end). (doE
        frameSize \<leftarrow> returnOk $ if (isAligned start (pageBitsForSize ARMSection))
                         \<and> isAligned end (pageBitsForSize ARMSection)
            then ARMSection else ARMSmallPage;
        slotBefore \<leftarrow> noInitFailure $ gets initSlotPosCur;
        (flip mapME_x) [start, (start + (bit (pageBitsForSize frameSize)))  .e.  (end - 1)]
              (\<lambda> f. (doE
                  frameCap \<leftarrow> createITFrameCap (ptrFromPAddr f) 0 Nothing (frameSize = ARMSection);
                  provideCap rootCNodeCap frameCap
              odE)
                                                  );
        slotAfter \<leftarrow> noInitFailure $ gets initSlotPosCur;
        biDeviceRegion \<leftarrow> returnOk ( BIDeviceRegion_ \<lparr>
                                  bidrBasePAddr= start,
                                  bidrFrameSizeBits= fromIntegral $ pageBitsForSize frameSize,
                                  bidrFrameCaps= SlotRegion (slotBefore, slotAfter) \<rparr>);
        devRegions \<leftarrow> noInitFailure $ gets (bifDeviceRegions \<circ> initBootInfo);
        devRegions' \<leftarrow> returnOk ( devRegions @ [biDeviceRegion]);
        bootInfo \<leftarrow> noInitFailure $ gets (initBootInfo);
        bootInfo' \<leftarrow> returnOk ( bootInfo \<lparr> bifDeviceRegions := devRegions' \<rparr>);
        noInitFailure $ modify (\<lambda> st. st \<lparr> initBootInfo := bootInfo' \<rparr>)
    odE)
        );
    bInfo \<leftarrow> noInitFailure $ gets (initBootInfo);
    bInfo' \<leftarrow> returnOk ( bInfo \<lparr> bifNumDeviceRegions := (fromIntegral \<circ> length \<circ> bifDeviceRegions) bInfo \<rparr>);
    noInitFailure $ modify (\<lambda> st. st \<lparr> initBootInfo := bInfo' \<rparr>)
odE)"

defs copyGlobalMappings_def:
"copyGlobalMappings newPD\<equiv> (do
    globalPD \<leftarrow> gets (armKSGlobalPD \<circ> ksArchState);
    pdeBits \<leftarrow> return ( objBits (undefined ::pde));
    pdSize \<leftarrow> return ( 1 `~shiftL~` (pdBits - pdeBits));
    forM_x [fromVPtr kernelBase `~shiftR~` 20  .e.  pdSize - 1] (\<lambda> index. (do
        offset \<leftarrow> return ( PPtr index `~shiftL~` pdeBits);
        pde \<leftarrow> getObject (globalPD + offset);
        storePDE (newPD + offset) pde
    od))
od)"

defs createMappingEntries_def:
"createMappingEntries base vptr x2 vmRights attrib pd\<equiv> (case x2 of
    ARMSmallPage \<Rightarrow>    (doE
    p \<leftarrow> lookupErrorOnFailure False $ lookupPTSlot pd vptr;
    returnOk $ Inl (SmallPagePTE_ \<lparr>
        pteFrame= base,
        pteCacheable= armPageCacheable attrib,
        pteGlobal= False,
        pteExecuteNever= armExecuteNever attrib,
        pteRights= vmRights \<rparr>, [p])
    odE)
  | ARMLargePage \<Rightarrow>    (doE
    p \<leftarrow> lookupErrorOnFailure False $ lookupPTSlot pd vptr;
    returnOk $ Inl (LargePagePTE_ \<lparr>
        pteFrame= base,
        pteCacheable= armPageCacheable attrib,
        pteGlobal= False,
        pteExecuteNever= armExecuteNever attrib,
        pteRights= vmRights \<rparr>, [p, p + 4  .e.  p + 60])
  odE)
  | ARMSection \<Rightarrow>    (doE
    p \<leftarrow> returnOk ( lookupPDSlot pd vptr);
    returnOk $ Inr (SectionPDE_ \<lparr>
        pdeFrame= base,
        pdeParity= armParityEnabled attrib,
        pdeDomain= 0,
        pdeCacheable= armPageCacheable attrib,
        pdeGlobal= False,
        pdeExecuteNever= armExecuteNever attrib,
        pdeRights= vmRights \<rparr>, [p])
  odE)
  | ARMSuperSection \<Rightarrow>    (doE
    p \<leftarrow> returnOk ( lookupPDSlot pd vptr);
    returnOk $ Inr (SuperSectionPDE_ \<lparr>
        pdeFrame= base,
        pdeParity= armParityEnabled attrib,
        pdeCacheable= armPageCacheable attrib,
        pdeGlobal= False,
        pdeExecuteNever= armExecuteNever attrib,
        pdeRights= vmRights \<rparr>, [p, p + 4  .e.  p + 60])
  odE)
  )"

defs ensureSafeMapping_def:
"ensureSafeMapping x0\<equiv> (case x0 of
    (Inl (InvalidPTE, _)) \<Rightarrow>    returnOk ()
  | (Inl (SmallPagePTE _ _ _ _ _, ptSlots)) \<Rightarrow>   
    forME_x ptSlots (\<lambda> slot. (doE
        pte \<leftarrow> withoutFailure $ getObject slot;
        (case pte of
              InvalidPTE \<Rightarrow>   returnOk ()
            | SmallPagePTE _ _ _ _ _ \<Rightarrow>   returnOk ()
            | _ \<Rightarrow>   throw DeleteFirst
            )
    odE))
  | (Inl (LargePagePTE _ _ _ _ _, ptSlots)) \<Rightarrow>   
    forME_x ptSlots (\<lambda> slot. (doE
        pte \<leftarrow> withoutFailure $ getObject slot;
        (case pte of
              InvalidPTE \<Rightarrow>   returnOk ()
            | LargePagePTE _ _ _ _ _ \<Rightarrow>   returnOk ()
            | _ \<Rightarrow>   throw DeleteFirst
            )
    odE))
  | (Inr (InvalidPDE, _)) \<Rightarrow>    returnOk ()
  | (Inr (PageTablePDE _ _ _, _)) \<Rightarrow>   
    haskell_fail []
  | (Inr (SectionPDE _ _ _ _ _ _ _, pdSlots)) \<Rightarrow>   
    forME_x pdSlots (\<lambda> slot. (doE
        pde \<leftarrow> withoutFailure $ getObject slot;
        (case pde of
              InvalidPDE \<Rightarrow>   returnOk ()
            | SectionPDE _ _ _ _ _ _ _ \<Rightarrow>   returnOk ()
            | _ \<Rightarrow>   throw DeleteFirst
            )
    odE))
  | (Inr (SuperSectionPDE _ _ _ _ _ _, pdSlots)) \<Rightarrow>   
    forME_x pdSlots (\<lambda> slot. (doE
        pde \<leftarrow> withoutFailure $ getObject slot;
        (case pde of
              InvalidPDE \<Rightarrow>   returnOk ()
            | SuperSectionPDE _ _ _ _ _ _ \<Rightarrow>   returnOk ()
            | _ \<Rightarrow>   throw DeleteFirst
            )
    odE))
  )"

defs lookupIPCBuffer_def:
"lookupIPCBuffer isReceiver thread\<equiv> (do
    bufferPtr \<leftarrow> threadGet tcbIPCBuffer thread;
    bufferFrameSlot \<leftarrow> getThreadBufferSlot thread;
    bufferCap \<leftarrow> getSlotCap bufferFrameSlot;
    (let v40 = bufferCap in
        if isArchObjectCap v40 \<and> isPageCap (capCap v40)
        then let frame = capCap v40
        in  (do
            rights \<leftarrow> return ( capVPRights frame);
            pBits \<leftarrow> return ( pageBitsForSize $ capVPSize frame);
            if (rights = VMReadWrite \<or> Not isReceiver \<and> rights = VMReadOnly)
              then (do
                 ptr \<leftarrow> return ( capVPBasePtr frame +
                           PPtr (fromVPtr bufferPtr && mask pBits));
                 haskell_assert (ptr \<noteq> 0)
                            [];
                 return $ Just ptr
              od)
              else return Nothing
        od)
        else  return Nothing
        )
od)"

defs findPDForASID_def:
"findPDForASID asid\<equiv> (doE
    haskell_assertE (asid > 0) [];
    haskell_assertE (asid \<le> snd asidRange) [];
    asidTable \<leftarrow> withoutFailure $ gets (armKSASIDTable \<circ> ksArchState);
    poolPtr \<leftarrow> returnOk ( asidTable (asidHighBitsOf asid));
 pool \<leftarrow> liftME (inv ASIDPool) $  (case poolPtr of
          Some ptr \<Rightarrow>   withoutFailure $ getObject ptr
        | None \<Rightarrow>   throw InvalidRoot
        );
    pd \<leftarrow> returnOk ( pool (asid && mask asidLowBits));
    (case pd of
          Some ptr \<Rightarrow>   (doE
            haskell_assertE (ptr \<noteq> 0) [];
            withoutFailure $ checkPDAt ptr;
            returnOk ptr
          odE)
        | None \<Rightarrow>   throw InvalidRoot
        )
odE)"

defs findPDForASIDAssert_def:
"findPDForASIDAssert asid\<equiv> (do
    pd \<leftarrow> findPDForASID asid `~catchFailure~`
        const (haskell_fail []);
    haskell_assert (pd && mask pdBits = 0)
        [];
    checkPDAt pd;
    checkPDUniqueToASID pd asid;
    asidMap \<leftarrow> gets (armKSASIDMap \<circ> ksArchState);
    flip haskell_assert []
        $ (case asidMap asid of
              None \<Rightarrow>   True
            | Some (_, pd') \<Rightarrow>   pd = pd'
            );
    return pd
od)"

defs checkPDUniqueToASID_def:
"checkPDUniqueToASID pd asid \<equiv> checkPDASIDMapMembership pd [asid]"

defs checkPDNotInASIDMap_def:
"checkPDNotInASIDMap pd \<equiv> checkPDASIDMapMembership pd []"

defs lookupPTSlot_def:
"lookupPTSlot pd vptr\<equiv> (doE
    pdSlot \<leftarrow> returnOk ( lookupPDSlot pd vptr);
    pde \<leftarrow> withoutFailure $ getObject pdSlot;
    (case pde of
          PageTablePDE _ _ _ \<Rightarrow>   (doE
            pt \<leftarrow> returnOk ( ptrFromPAddr $ pdeTable pde);
            withoutFailure $ lookupPTSlotFromPT pt vptr
          odE)
        | _ \<Rightarrow>   throw $ MissingCapability 20
        )
odE)"

defs lookupPTSlotFromPT_def:
"lookupPTSlotFromPT pt vptr\<equiv> (do
    ptIndex \<leftarrow> return ( fromVPtr $ vptr `~shiftR~` 12 && 0xff);
    ptSlot \<leftarrow> return ( pt + (PPtr $ ptIndex `~shiftL~` 2));
    checkPTAt pt;
    return ptSlot
od)"

defs lookupPDSlot_def:
"lookupPDSlot pd vptr \<equiv>
    let pdIndex = fromVPtr $ vptr `~shiftR~` 20
    in pd + (PPtr $ pdIndex `~shiftL~` 2)"

defs handleVMFault_def:
"handleVMFault thread x1\<equiv> (case x1 of
    ARMDataAbort \<Rightarrow>    (doE
    addr \<leftarrow> withoutFailure $ doMachineOp getFAR;
    fault \<leftarrow> withoutFailure $ doMachineOp getDFSR;
    throw $ VMFault addr [0, fault && mask 14]
    odE)
  | ARMPrefetchAbort \<Rightarrow>    (doE
    pc \<leftarrow> withoutFailure $ asUser thread $ getRestartPC;
    fault \<leftarrow> withoutFailure $ doMachineOp getIFSR;
    throw $ VMFault (VPtr pc) [1, fault && mask 14]
  odE)
  )"

defs deleteASIDPool_def:
"deleteASIDPool base ptr\<equiv> (do
    haskell_assert (base && mask asidLowBits = 0)
        [];
    asidTable \<leftarrow> gets (armKSASIDTable \<circ> ksArchState);
    when (asidTable (asidHighBitsOf base) = Just ptr) $ (do
 pool \<leftarrow> liftM (inv ASIDPool) $  getObject ptr;
        forM [0  .e.  (bit asidLowBits) - 1] (\<lambda> offset. (
            when (isJust $ pool offset) $ (do
                flushSpace $ base + offset;
                invalidateASIDEntry $ base + offset
            od)
        ));
        asidTable' \<leftarrow> return ( asidTable aLU [(asidHighBitsOf base, Nothing)]);
        modify (\<lambda> s. s \<lparr>
            ksArchState := (ksArchState s) \<lparr> armKSASIDTable := asidTable' \<rparr>\<rparr>);
        tcb \<leftarrow> getCurThread;
        setVMRoot tcb
    od)
od)"

defs deleteASID_def:
"deleteASID asid pd\<equiv> (do
    asidTable \<leftarrow> gets (armKSASIDTable \<circ> ksArchState);
    (case asidTable (asidHighBitsOf asid) of
          None \<Rightarrow>   return ()
        | Some poolPtr \<Rightarrow>   (do
 pool \<leftarrow> liftM (inv ASIDPool) $  getObject poolPtr;
            when (pool (asid && mask asidLowBits) = Just pd) $ (do
                flushSpace asid;
                invalidateASIDEntry asid;
                pool' \<leftarrow> return ( pool aLU [(asid && mask asidLowBits, Nothing)]);
                setObject poolPtr $ ASIDPool pool';
                tcb \<leftarrow> getCurThread;
                setVMRoot tcb
            od)
        od)
        )
od)"

defs pageTableMapped_def:
"pageTableMapped asid vaddr pt \<equiv> catchFailure
    ((doE
        pd \<leftarrow> findPDForASID asid;
        pdSlot \<leftarrow> returnOk ( lookupPDSlot pd vaddr);
        pde \<leftarrow> withoutFailure $ getObject pdSlot;
        (case pde of
              PageTablePDE pt' _ _ \<Rightarrow>   returnOk $
                if pt' = addrFromPPtr pt then Just pd else Nothing
            | _ \<Rightarrow>   returnOk Nothing)
            
    odE)
            )
    (\<lambda> _. return Nothing)"

defs unmapPageTable_def:
"unmapPageTable asid vaddr pt\<equiv> (do
    maybePD \<leftarrow> pageTableMapped asid vaddr pt;
    (case maybePD of
          Some pd \<Rightarrow>   (do
            pdSlot \<leftarrow> return ( lookupPDSlot pd vaddr);
            storePDE pdSlot InvalidPDE;
            doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr pdSlot) (addrFromPPtr pdSlot);
            flushTable pd asid vaddr
          od)
        | None \<Rightarrow>   return ()
        )
od)"

defs unmapPage_def:
"unmapPage magnitude asid vptr ptr\<equiv> ignoreFailure $ (doE
    pd \<leftarrow> findPDForASID asid;
    (case magnitude of
          ARMSmallPage \<Rightarrow>   (doE
            p \<leftarrow> lookupPTSlot pd vptr;
            checkMappingPPtr ptr magnitude (Inl p);
            withoutFailure $ (do
                storePTE p InvalidPTE;
                doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr p) (addrFromPPtr p)
            od)
          odE)
        | ARMLargePage \<Rightarrow>   (doE
            p \<leftarrow> lookupPTSlot pd vptr;
            checkMappingPPtr ptr magnitude (Inl p);
            withoutFailure $ (do
                slots \<leftarrow> return ( map (\<lambda> x. x + p) [0, 4  .e.  60]);
                mapM (flip storePTE InvalidPTE) slots;
                doMachineOp $
                    cleanCacheRange_PoU (VPtr $ fromPPtr $ (head slots))
                                        (VPtr $ (fromPPtr (last slots)) + (bit (objBits (undefined ::pte)) - 1 ))
                                        (addrFromPPtr (head slots))
            od)
        odE)
        | ARMSection \<Rightarrow>   (doE
            p \<leftarrow> returnOk ( lookupPDSlot pd vptr);
            checkMappingPPtr ptr magnitude (Inr p);
            withoutFailure $ (do
                storePDE p InvalidPDE;
                doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr p) (addrFromPPtr p)
            od)
        odE)
        | ARMSuperSection \<Rightarrow>   (doE
            p \<leftarrow> returnOk ( lookupPDSlot pd vptr);
            checkMappingPPtr ptr magnitude (Inr p);
            withoutFailure $ (do
                slots \<leftarrow> return ( map (\<lambda> x. x + p) [0, 4  .e.  60]);
                mapM (flip storePDE InvalidPDE) slots;
                doMachineOp $
                    cleanCacheRange_PoU (VPtr $ fromPPtr $ (head slots))
                                        (VPtr $ (fromPPtr  (last slots)) + (bit (objBits (undefined ::pde)) - 1))
                                        (addrFromPPtr (head slots))
            od)
        odE)
        );
    withoutFailure $ flushPage magnitude pd asid vptr
odE)"

defs checkMappingPPtr_def:
"checkMappingPPtr pptr magnitude x2\<equiv> (case x2 of
    (Inl pt) \<Rightarrow>    (doE
    pte \<leftarrow> withoutFailure $ getObject pt;
    (case (pte, magnitude) of
          (SmallPagePTE base _ _ _ _, ARMSmallPage) \<Rightarrow>  
            unlessE (base = addrFromPPtr pptr) $ throw InvalidRoot
        | (LargePagePTE base _ _ _ _, ARMLargePage) \<Rightarrow>  
            unlessE (base = addrFromPPtr pptr) $ throw InvalidRoot
        | _ \<Rightarrow>   throw InvalidRoot
        )
    odE)
  | (Inr pd) \<Rightarrow>    (doE
    pde \<leftarrow> withoutFailure $ getObject pd;
    (case (pde, magnitude) of
          (SectionPDE base _ _ _ _ _ _, ARMSection) \<Rightarrow>  
            unlessE (base = addrFromPPtr pptr) $ throw InvalidRoot
        | (SuperSectionPDE base _ _ _ _ _, ARMSuperSection) \<Rightarrow>  
            unlessE (base = addrFromPPtr pptr) $ throw InvalidRoot
        | _ \<Rightarrow>   throw InvalidRoot
        )
  odE)
  )"

defs armv_contextSwitch_HWASID_def:
"armv_contextSwitch_HWASID pd hwasid \<equiv> (do
   setCurrentPD $ addrFromPPtr pd;
   setHardwareASID hwasid
od)"

defs armv_contextSwitch_def:
"armv_contextSwitch pd asid \<equiv> (do
   hwasid \<leftarrow> getHWASID asid;
   doMachineOp $ armv_contextSwitch_HWASID pd hwasid
od)"

defs setVMRoot_def:
"setVMRoot tcb\<equiv> (do
    threadRootSlot \<leftarrow> getThreadVSpaceRoot tcb;
    threadRoot \<leftarrow> getSlotCap threadRootSlot;
    catchFailure
        ((case threadRoot of
              ArchObjectCap (PageDirectoryCap pd (Some asid)) \<Rightarrow>   (doE
                pd' \<leftarrow> findPDForASID asid;
                whenE (pd \<noteq> pd') $ (
                    throw InvalidRoot
                );
                withoutFailure $ armv_contextSwitch pd asid
              odE)
            | _ \<Rightarrow>   throw InvalidRoot)
            )
        (\<lambda> _. (do
            (case threadRoot of
                  ArchObjectCap (PageDirectoryCap pd (Some _)) \<Rightarrow>   checkPDNotInASIDMap pd
                | _ \<Rightarrow>   return ()
                );
            globalPD \<leftarrow> gets (armKSGlobalPD \<circ> ksArchState);
            doMachineOp $ setCurrentPD $ addrFromPPtr globalPD 
        od)
                                                               )
od)"

defs setVMRootForFlush_def:
"setVMRootForFlush pd asid\<equiv> (do
    tcb \<leftarrow> getCurThread;
    threadRootSlot \<leftarrow> getThreadVSpaceRoot tcb;
    threadRoot \<leftarrow> getSlotCap threadRootSlot;
    (let v44 = threadRoot in
        if isArchObjectCap v44 \<and> isPageDirectoryCap (capCap v44) \<and> capPDMappedASID (capCap v44) \<noteq> None \<and> capPDBasePtr (capCap v44) = pd
        then let cur_pd = pd in  return False
        else  (do
            armv_contextSwitch pd asid;
            return True
        od)
        )
od)"

defs isValidVTableRoot_def:
"isValidVTableRoot x0\<equiv> (case x0 of
    (ArchObjectCap (PageDirectoryCap _ (Some _))) \<Rightarrow>    True
  | _ \<Rightarrow>    False
  )"

defs checkValidIPCBuffer_def:
"checkValidIPCBuffer vptr x1\<equiv> (case x1 of
    (ArchObjectCap (PageCap _ _ _ _)) \<Rightarrow>    (doE
    whenE (vptr && mask msgAlignBits \<noteq> 0) $ throw AlignmentError;
    returnOk ()
    odE)
  | _ \<Rightarrow>    throw IllegalOperation
  )"

defs maskVMRights_def:
"maskVMRights r m\<equiv> (case (r, capAllowRead m, capAllowWrite m) of
      (VMNoAccess, _, _) \<Rightarrow>   VMNoAccess
    | (VMReadOnly, True, _) \<Rightarrow>   VMReadOnly
    | (VMReadWrite, True, False) \<Rightarrow>   VMReadOnly
    | (VMReadWrite, True, True) \<Rightarrow>   VMReadWrite
    | _ \<Rightarrow>   VMKernelOnly
    )"

defs attribsFromWord_def:
"attribsFromWord w \<equiv> VMAttributes_ \<lparr>
    armPageCacheable= w !! 0,
    armParityEnabled= w !! 1,
    armExecuteNever= w !! 2 \<rparr>"

defs storeHWASID_def:
"storeHWASID asid hw_asid \<equiv> (do
    pd \<leftarrow> findPDForASIDAssert asid;
    asidMap \<leftarrow> gets (armKSASIDMap \<circ> ksArchState);
    asidMap' \<leftarrow> return ( asidMap aLU [(asid, Just (hw_asid, pd))]);
    modify (\<lambda> s. s \<lparr>
        ksArchState := (ksArchState s)
        \<lparr> armKSASIDMap := asidMap' \<rparr>\<rparr>);
    hwASIDMap \<leftarrow> gets (armKSHWASIDTable \<circ> ksArchState);
    hwASIDMap' \<leftarrow> return ( hwASIDMap aLU [(hw_asid, Just asid)]);
    modify (\<lambda> s. s \<lparr>
        ksArchState := (ksArchState s)
        \<lparr> armKSHWASIDTable := hwASIDMap' \<rparr>\<rparr>)
od)"

defs loadHWASID_def:
"loadHWASID asid\<equiv> (do
    asidMap \<leftarrow> gets (armKSASIDMap \<circ> ksArchState);
    findPDForASIDAssert asid;
    return $ (case asidMap asid of
          None \<Rightarrow>   Nothing
        | Some (hw_asid, _) \<Rightarrow>   Just hw_asid
        )
od)"

defs invalidateASID_def:
"invalidateASID asid\<equiv> (do
    findPDForASIDAssert asid;
    asidMap \<leftarrow> gets (armKSASIDMap \<circ> ksArchState);
    asidMap' \<leftarrow> return ( asidMap aLU [(asid, Nothing)]);
    modify (\<lambda> s. s \<lparr>
        ksArchState := (ksArchState s)
        \<lparr> armKSASIDMap := asidMap' \<rparr>\<rparr>)
od)"

defs invalidateHWASIDEntry_def:
"invalidateHWASIDEntry hwASID\<equiv> (do
    asidMap \<leftarrow> gets (armKSHWASIDTable \<circ> ksArchState);
    asidMap' \<leftarrow> return ( asidMap aLU [(hwASID, Nothing)]);
    modify (\<lambda> s. s \<lparr>
        ksArchState := (ksArchState s)
        \<lparr> armKSHWASIDTable := asidMap' \<rparr>\<rparr>)
od)"

defs invalidateASIDEntry_def:
"invalidateASIDEntry asid\<equiv> (do
    maybeHWASID \<leftarrow> loadHWASID asid;
    when (isJust maybeHWASID) $ invalidateHWASIDEntry (fromJust maybeHWASID);
    invalidateASID asid
od)"

defs findFreeHWASID_def:
"findFreeHWASID\<equiv> (do
    hwASIDTable \<leftarrow> gets (armKSHWASIDTable \<circ> ksArchState);
    nextASID \<leftarrow> gets (armKSNextASID \<circ> ksArchState);
    maybe_asid \<leftarrow> return ( find (\<lambda> a. isNothing (hwASIDTable a))
                      ([nextASID  .e.  maxBound] @ init [minBound  .e.  nextASID]));
    (case maybe_asid of
          Some hw_asid \<Rightarrow>   return hw_asid
        | None \<Rightarrow>   (do
            invalidateASID $ fromJust $ hwASIDTable nextASID;
            doMachineOp $ invalidateTLB_ASID nextASID;
            invalidateHWASIDEntry nextASID;
            new_nextASID \<leftarrow> return (
                    if nextASID = maxBound
                    then minBound
                    else nextASID + 1);
            modify (\<lambda> s. s \<lparr>
                ksArchState := (ksArchState s)
                \<lparr> armKSNextASID := new_nextASID \<rparr>\<rparr>);
            return nextASID
        od)
        )
od)"

defs getHWASID_def:
"getHWASID asid\<equiv> (do
    maybe_hw_asid \<leftarrow> loadHWASID asid;
    (case maybe_hw_asid of
          Some hw_asid \<Rightarrow>  
            return hw_asid
        | None \<Rightarrow>   (do
            new_hw_asid \<leftarrow> findFreeHWASID;
            storeHWASID asid new_hw_asid;
            return new_hw_asid
        od)
        )
od)"

defs doFlush_def:
"doFlush x0 vstart vend pstart\<equiv> (case x0 of
    Clean \<Rightarrow>   
    cleanCacheRange_RAM vstart vend pstart
  | Invalidate \<Rightarrow>   
    invalidateCacheRange_RAM vstart vend pstart
  | CleanInvalidate \<Rightarrow>   
    cleanInvalidateCacheRange_RAM vstart vend pstart
  | Unify \<Rightarrow>    (do
    cleanCacheRange_PoU vstart vend pstart;
    dsb;
    invalidateCacheRange_I vstart vend pstart;
    branchFlushRange vstart vend pstart;
    isb
  od)
  )"

defs flushPage_def:
"flushPage arg1 pd asid vptr \<equiv> (do
    haskell_assert (vptr && mask pageBits = 0)
        [];
    root_switched \<leftarrow> setVMRootForFlush pd asid;
    maybe_hw_asid \<leftarrow> loadHWASID asid;
    when (isJust maybe_hw_asid) $ (do
 hw_asid \<leftarrow> liftM the $  return ( maybe_hw_asid);
      doMachineOp $ invalidateTLB_VAASID (fromVPtr vptr || (fromIntegral $ fromHWASID hw_asid));
      when root_switched $ (do
          tcb \<leftarrow> getCurThread;
          setVMRoot tcb
      od)
    od)
od)"

defs flushTable_def:
"flushTable pd asid vptr\<equiv> (do
    haskell_assert (vptr && mask (pageBitsForSize ARMSection) = 0)
        [];
    root_switched \<leftarrow> setVMRootForFlush pd asid;
    maybe_hw_asid \<leftarrow> loadHWASID asid;
    when (isJust maybe_hw_asid) $ (do
      doMachineOp $ invalidateTLB_ASID (fromJust maybe_hw_asid);
      when root_switched $ (do
          tcb \<leftarrow> getCurThread;
          setVMRoot tcb
      od)
    od)
od)"

defs flushSpace_def:
"flushSpace asid\<equiv> (do
    maybe_hw_asid \<leftarrow> loadHWASID asid;
    doMachineOp cleanCaches_PoU;
    (case maybe_hw_asid of
          None \<Rightarrow>   return ()
        | Some hw_asid \<Rightarrow>   (
            doMachineOp $ invalidateTLB_ASID hw_asid
        )
        )
od)"

defs invalidateTLBByASID_def:
"invalidateTLBByASID asid\<equiv> (do
    maybe_hw_asid \<leftarrow> loadHWASID asid;
    (case maybe_hw_asid of
          None \<Rightarrow>   return ()
        | Some hw_asid \<Rightarrow>   (
            doMachineOp $ invalidateTLB_ASID hw_asid
        )
        )
od)"

defs labelToFlushType_def:
"labelToFlushType label\<equiv> (case invocationType label of
        ArchInvocationLabel ARMPDClean_Data \<Rightarrow>   Clean
      | ArchInvocationLabel ARMPageClean_Data \<Rightarrow>   Clean
      | ArchInvocationLabel ARMPDInvalidate_Data \<Rightarrow>   Invalidate
      | ArchInvocationLabel ARMPageInvalidate_Data \<Rightarrow>   Invalidate
      | ArchInvocationLabel ARMPDCleanInvalidate_Data \<Rightarrow>   CleanInvalidate
      | ArchInvocationLabel ARMPageCleanInvalidate_Data \<Rightarrow>   CleanInvalidate
      | ArchInvocationLabel ARMPDUnify_Instruction \<Rightarrow>   Unify
      | ArchInvocationLabel ARMPageUnify_Instruction \<Rightarrow>   Unify
      | _ \<Rightarrow>   error []
      )"

defs pageBase_def:
"pageBase vaddr magnitude\<equiv> vaddr && (complement $ mask (pageBitsForSize magnitude))"

defs resolveVAddr_def:
"resolveVAddr pd vaddr\<equiv> (do
    pdSlot \<leftarrow> return ( lookupPDSlot pd vaddr);
    pde \<leftarrow> getObject pdSlot;
    (case pde of
          SectionPDE frame v54 v55 v56 v57 v58 v59 \<Rightarrow>   return $ Just (ARMSection, frame)
        | SuperSectionPDE frame v60 v61 v62 v63 v64 \<Rightarrow>   return $ Just (ARMSuperSection, frame)
        | PageTablePDE table v65 v66 \<Rightarrow>   (do
            pt \<leftarrow> return ( ptrFromPAddr table);
            pteSlot \<leftarrow> lookupPTSlotFromPT pt vaddr;
            pte \<leftarrow> getObject pteSlot;
            (case pte of
                  LargePagePTE frame v46 v47 v48 v49 \<Rightarrow>   return $ Just (ARMLargePage, frame)
                | SmallPagePTE frame v50 v51 v52 v53 \<Rightarrow>   return $ Just (ARMSmallPage, frame)
                | _ \<Rightarrow>   return Nothing
                )
        od)
        | _ \<Rightarrow>   return Nothing
        )
od)"

defs decodeARMMMUInvocation_def:
"decodeARMMMUInvocation label args x2 cte x4 extraCaps\<equiv> (let cap = x4 in
  if isPageDirectoryCap cap
  then  
    (case (isPDFlushLabel (invocationType label), args) of
          (True, start#end#_) \<Rightarrow>   (doE
            whenE (end \<le> start) $
                throw $ InvalidArgument 1;
            whenE (VPtr start \<ge> kernelBase \<or> VPtr end > kernelBase) $
                throw IllegalOperation;
            (pd,asid) \<leftarrow> (case cap of
                  PageDirectoryCap pd (Some asid) \<Rightarrow>   returnOk (pd,asid)
                | _ \<Rightarrow>   throw $ InvalidCapability 0
                );
            pdCheck \<leftarrow> lookupErrorOnFailure False $ findPDForASID asid;
            whenE (pdCheck \<noteq> pd) $ throw $ InvalidCapability 0;
            frameInfo \<leftarrow>
                 withoutFailure $ resolveVAddr (capPDBasePtr cap) (VPtr start);
            (case frameInfo of
                  None \<Rightarrow>   returnOk $ InvokePageDirectory PageDirectoryNothing
                | Some frameInfo \<Rightarrow>   (doE
                    withoutFailure $ checkValidMappingSize (fst frameInfo);
                    baseStart \<leftarrow> returnOk ( pageBase (VPtr start) (fst frameInfo));
                    baseEnd \<leftarrow> returnOk ( pageBase (VPtr end - 1) (fst frameInfo));
                    whenE (baseStart \<noteq> baseEnd) $
                        throw $ RangeError start $ fromVPtr $ baseStart +
                                  mask (pageBitsForSize (fst frameInfo));
                    offset \<leftarrow> returnOk ( start && mask (pageBitsForSize (fst frameInfo)));
                    pStart \<leftarrow> returnOk ( snd frameInfo + toPAddr offset);
                    returnOk $ InvokePageDirectory $ PageDirectoryFlush_ \<lparr>
                         pdFlushType= labelToFlushType label,
                         pdFlushStart= VPtr start,
                         pdFlushEnd= VPtr end - 1,
                         pdFlushPStart= pStart,
                         pdFlushPD= pd,
                         pdFlushASID= asid \<rparr>
                odE)
                )
          odE)
        | (True, _) \<Rightarrow>   throw TruncatedMessage
        | _ \<Rightarrow>   throw IllegalOperation
        )
  else if isPageTableCap cap
  then  
    (case (invocationType label, args, extraCaps) of
          (ArchInvocationLabel ARMPageTableMap, vaddr#attr#_, (pdCap,_)#_) \<Rightarrow>   (doE
            whenE (isJust $ capPTMappedAddress cap) $
                throw $ InvalidCapability 0;
            (pd,asid) \<leftarrow> (case pdCap of
                  ArchObjectCap (PageDirectoryCap pd (Some asid)) \<Rightarrow>   returnOk (pd,asid)
                | _ \<Rightarrow>   throw $ InvalidCapability 1
                );
            whenE (VPtr vaddr \<ge> kernelBase) $
                throw $ InvalidArgument 0;
            pdCheck \<leftarrow> lookupErrorOnFailure False $ findPDForASID asid;
            whenE (pdCheck \<noteq> pd) $ throw $ InvalidCapability 1;
            pdIndex \<leftarrow> returnOk ( vaddr `~shiftR~` 20);
            vaddr' \<leftarrow> returnOk ( pdIndex `~shiftL~` 20);
            pdSlot \<leftarrow> returnOk ( pd + (PPtr $ pdIndex `~shiftL~` 2));
            oldpde \<leftarrow> withoutFailure $ getObject pdSlot;
            unlessE (oldpde = InvalidPDE) $ throw DeleteFirst;
            pde \<leftarrow> returnOk ( PageTablePDE_ \<lparr>
                    pdeTable= addrFromPPtr $ capPTBasePtr cap,
                    pdeParity= armParityEnabled $ attribsFromWord attr,
                    pdeDomain= 0 \<rparr>);
            returnOk $ InvokePageTable $ PageTableMap_ \<lparr>
                ptMapCap= ArchObjectCap $
                    cap \<lparr> capPTMappedAddress:= Just (asid, VPtr vaddr') \<rparr>,
                ptMapCTSlot= cte,
                ptMapPDE= pde,
                ptMapPDSlot= pdSlot \<rparr>
          odE)
        | (ArchInvocationLabel ARMPageTableMap, _, _) \<Rightarrow>   throw TruncatedMessage
        | (ArchInvocationLabel ARMPageTableUnmap, _, _) \<Rightarrow>   (doE
            cteVal \<leftarrow> withoutFailure $ getCTE cte;
            final \<leftarrow> withoutFailure $ isFinalCapability cteVal;
            unlessE final $ throw RevokeFirst;
            returnOk $ InvokePageTable $ PageTableUnmap_ \<lparr>
                ptUnmapCap= cap,
                ptUnmapCapSlot= cte \<rparr>
        odE)
        | _ \<Rightarrow>   throw IllegalOperation
        )
  else if isPageCap cap
  then  
 (
    (case (invocationType label, args, extraCaps) of
          (ArchInvocationLabel ARMPageMap, vaddr#rightsMask#attr#_, (pdCap,_)#_) \<Rightarrow>   (doE
            whenE (isJust $ capVPMappedAddress cap) $
                throw $ InvalidCapability 0;
            (pd,asid) \<leftarrow> (case pdCap of
                  ArchObjectCap (PageDirectoryCap pd (Some asid)) \<Rightarrow>   returnOk (pd,asid)
                | _ \<Rightarrow>   throw $ InvalidCapability 1
                );
            pdCheck \<leftarrow> lookupErrorOnFailure False $ findPDForASID asid;
            whenE (pdCheck \<noteq> pd) $ throw $ InvalidCapability 1;
            vtop \<leftarrow> returnOk ( vaddr + bit (pageBitsForSize $ capVPSize cap) - 1);
            whenE (VPtr vtop \<ge> kernelBase) $
                throw $ InvalidArgument 0;
            vmRights \<leftarrow> returnOk ( maskVMRights (capVPRights cap) $
                    rightsFromWord rightsMask);
            checkVPAlignment (capVPSize cap) (VPtr vaddr);
            entries \<leftarrow> createMappingEntries (addrFromPPtr $ capVPBasePtr cap)
                (VPtr vaddr) (capVPSize cap) vmRights
                (attribsFromWord attr) pd;
            ensureSafeMapping entries;
            returnOk $ InvokePage $ PageMap_ \<lparr>
                pageMapASID= asid,
                pageMapCap= ArchObjectCap $
                    cap \<lparr> capVPMappedAddress:= Just (asid, VPtr vaddr) \<rparr>,
                pageMapCTSlot= cte,
                pageMapEntries= entries \<rparr>
          odE)
        | (ArchInvocationLabel ARMPageMap, _, _) \<Rightarrow>   throw TruncatedMessage
        | (ArchInvocationLabel ARMPageRemap, rightsMask#attr#_, (pdCap, _)#_) \<Rightarrow>   (doE
            (pd,asid) \<leftarrow> (case pdCap of
                  ArchObjectCap (PageDirectoryCap pd (Some asid)) \<Rightarrow>   returnOk (pd,asid)
                | _ \<Rightarrow>   throw $ InvalidCapability 1
                );
            (asidCheck, vaddr) \<leftarrow> (case capVPMappedAddress cap of
                  Some a \<Rightarrow>   returnOk a
                | _ \<Rightarrow>   throw $ InvalidCapability 0
                );
            pdCheck \<leftarrow> lookupErrorOnFailure False $ findPDForASID asidCheck;
            whenE (pdCheck \<noteq> pd \<or> asidCheck \<noteq> asid) $ throw $ InvalidCapability 1;
            vmRights \<leftarrow> returnOk ( maskVMRights (capVPRights cap) $
                    rightsFromWord rightsMask);
            checkVPAlignment (capVPSize cap) vaddr;
            entries \<leftarrow> createMappingEntries (addrFromPPtr $ capVPBasePtr cap)
                vaddr (capVPSize cap) vmRights (attribsFromWord attr) pd;
            ensureSafeMapping entries;
            returnOk $ InvokePage $ PageRemap_ \<lparr>
                pageRemapASID= asidCheck,
                pageRemapEntries= entries \<rparr>
        odE)
        | (ArchInvocationLabel ARMPageRemap, _, _) \<Rightarrow>   throw TruncatedMessage
        | (ArchInvocationLabel ARMPageUnmap, _, _) \<Rightarrow>   returnOk $ InvokePage $ PageUnmap_ \<lparr>
                pageUnmapCap= cap,
                pageUnmapCapSlot= cte \<rparr>
        | (ArchInvocationLabel ARMPageClean_Data, _, _) \<Rightarrow>   decodeARMPageFlush label args cap
        | (ArchInvocationLabel ARMPageInvalidate_Data, _, _) \<Rightarrow>   decodeARMPageFlush label args cap
        | (ArchInvocationLabel ARMPageCleanInvalidate_Data, _, _) \<Rightarrow>   decodeARMPageFlush label args cap
        | (ArchInvocationLabel ARMPageUnify_Instruction, _, _) \<Rightarrow>   decodeARMPageFlush label args cap
        | (ArchInvocationLabel ARMPageGetAddress, _, _) \<Rightarrow>   returnOk $ InvokePage $ PageGetAddr (capVPBasePtr cap)
        | _ \<Rightarrow>   throw IllegalOperation
        )
 )
  else if isASIDControlCap cap
  then  
    (case (invocationType label, args, extraCaps) of
          (ArchInvocationLabel ARMASIDControlMakePool, index#depth#_, (untyped,parentSlot)#(root,_)#_) \<Rightarrow>   (doE
            asidTable \<leftarrow> withoutFailure $ gets (armKSASIDTable \<circ> ksArchState);
            free \<leftarrow> returnOk ( filter (\<lambda> (x,y). x \<le> (1 `~shiftL~` asidHighBits) - 1 \<and> isNothing y) $ assocs asidTable);
            whenE (null free) $ throw DeleteFirst;
            base \<leftarrow> returnOk ( (fst $ head free) `~shiftL~` asidLowBits);
            pool \<leftarrow> returnOk ( makeObject ::asidpool);
            frame \<leftarrow> (let v67 = untyped in
                if isUntypedCap v67 \<and> capBlockSize v67 = objBits pool
                then  (doE
                    ensureNoChildren parentSlot;
                    returnOk $ capPtr untyped
                odE)
                else  throw $ InvalidCapability 1
                );
            destSlot \<leftarrow> lookupTargetSlot
                root (CPtr index) (fromIntegral depth);
            ensureEmptySlot destSlot;
            returnOk $ InvokeASIDControl $ MakePool_ \<lparr>
                makePoolFrame= frame,
                makePoolSlot= destSlot,
                makePoolParent= parentSlot,
                makePoolBase= base \<rparr>
          odE)
        | (ArchInvocationLabel ARMASIDControlMakePool, _, _) \<Rightarrow>   throw TruncatedMessage
        | _ \<Rightarrow>   throw IllegalOperation
        )
  else if isASIDPoolCap cap
  then  
    (case (invocationType label, extraCaps) of
          (ArchInvocationLabel ARMASIDPoolAssign, (pdCap,pdCapSlot)#_) \<Rightarrow>  
            (case pdCap of
                  ArchObjectCap (PageDirectoryCap _ None) \<Rightarrow>   (doE
                    asidTable \<leftarrow> withoutFailure $ gets (armKSASIDTable \<circ> ksArchState);
                    base \<leftarrow> returnOk ( capASIDBase cap);
                    poolPtr \<leftarrow> returnOk ( asidTable (asidHighBitsOf base));
                    whenE (isNothing poolPtr) $ throw $ FailedLookup False InvalidRoot;
 p \<leftarrow> liftME the $  returnOk ( poolPtr);
                    whenE (p \<noteq> capASIDPool cap) $ throw $ InvalidCapability 0;
 pool \<leftarrow> liftME (inv ASIDPool) $  withoutFailure $ getObject $ p;
                    free \<leftarrow> returnOk ( filter (\<lambda> (x,y). x \<le>  (1 `~shiftL~` asidLowBits) - 1
                                                 \<and> x + base \<noteq> 0 \<and> isNothing y) $ assocs pool);
                    whenE (null free) $ throw DeleteFirst;
                    asid \<leftarrow> returnOk ( fst $ head free);
                    returnOk $ InvokeASIDPool $ Assign_ \<lparr>
                        assignASID= asid + base,
                        assignASIDPool= capASIDPool cap,
                        assignASIDCTSlot= pdCapSlot \<rparr>
                  odE)
                | _ \<Rightarrow>   throw $ InvalidCapability 1
                )
        | (ArchInvocationLabel ARMASIDPoolAssign, _) \<Rightarrow>   throw TruncatedMessage
        | _ \<Rightarrow>   throw IllegalOperation
        )
  else undefined
  )"

defs decodeARMPageFlush_def:
"decodeARMPageFlush label args cap\<equiv> (case (args, capVPMappedAddress cap) of
      (start#end#_, Some (asid, vaddr)) \<Rightarrow>   (doE
        pd \<leftarrow> lookupErrorOnFailure False $ findPDForASID asid;
        whenE (end \<le> start) $
            throw $ InvalidArgument 1;
        pageSize \<leftarrow> returnOk ( 1 `~shiftL~` pageBitsForSize (capVPSize cap));
        pageBase \<leftarrow> returnOk ( addrFromPPtr $ capVPBasePtr cap);
        whenE (start \<ge> pageSize \<or> end > pageSize) $
            throw $ InvalidArgument 0;
        pstart \<leftarrow> returnOk ( pageBase + toPAddr start);
        start' \<leftarrow> returnOk ( start + fromVPtr vaddr);
        end' \<leftarrow> returnOk ( end + fromVPtr vaddr);
        returnOk $ InvokePage $ PageFlush_ \<lparr>
              pageFlushType= labelToFlushType label,
              pageFlushStart= VPtr $ start',
              pageFlushEnd= VPtr $ end' - 1,
              pageFlushPStart= pstart,
              pageFlushPD= pd,
              pageFlushASID= asid \<rparr>
      odE)
    | (_#_#_, None) \<Rightarrow>   throw IllegalOperation
    | _ \<Rightarrow>   throw TruncatedMessage
    )"

defs checkVPAlignment_def:
"checkVPAlignment sz w \<equiv>
    unlessE (w && mask (pageBitsForSize sz) = 0) $
           throw AlignmentError"

defs performARMMMUInvocation_def:
"performARMMMUInvocation i\<equiv> withoutPreemption $ (do
    (case i of
          InvokePageDirectory oper \<Rightarrow>   performPageDirectoryInvocation oper
        | InvokePageTable oper \<Rightarrow>   performPageTableInvocation oper
        | InvokePage oper \<Rightarrow>   performPageInvocation oper
        | InvokeASIDControl oper \<Rightarrow>   performASIDControlInvocation oper
        | InvokeASIDPool oper \<Rightarrow>   performASIDPoolInvocation oper
        );
    return $ []
od)"

defs performPageDirectoryInvocation_def:
"performPageDirectoryInvocation x0\<equiv> (case x0 of
    (PageDirectoryFlush typ start end pstart pd asid) \<Rightarrow>   
    when (start < end) $ (do
        root_switched \<leftarrow> setVMRootForFlush pd asid;
        doMachineOp $ doFlush typ start end pstart;
        when root_switched $ (do
            tcb \<leftarrow> getCurThread;
            setVMRoot tcb
        od)
    od)
  | PageDirectoryNothing \<Rightarrow>    return ()
  )"

defs performPageTableInvocation_def:
"performPageTableInvocation x0\<equiv> (case x0 of
    (PageTableMap cap ctSlot pde pdSlot) \<Rightarrow>    (do
    updateCap ctSlot cap;
    storePDE pdSlot pde;
    doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr $ pdSlot) (addrFromPPtr pdSlot)
    od)
  | (PageTableUnmap cap ctSlot) \<Rightarrow>    (do
    (case capPTMappedAddress cap of
          Some (asid, vaddr) \<Rightarrow>   (do
            unmapPageTable asid vaddr (capPTBasePtr cap);
            ptr \<leftarrow> return ( capPTBasePtr cap);
            pteBits \<leftarrow> return ( objBits InvalidPTE);
            slots \<leftarrow> return ( [ptr, ptr + bit pteBits  .e.  ptr + bit ptBits - 1]);
            mapM_x (flip storePTE InvalidPTE) slots;
            doMachineOp $
                cleanCacheRange_PoU (VPtr $ fromPPtr $ ptr)
                                    (VPtr $ fromPPtr $ (ptr + (1 `~shiftL~` ptBits) - 1))
                                    (addrFromPPtr ptr)
          od)
        | None \<Rightarrow>   return ()
        );
 cap \<leftarrow> liftM capCap $  getSlotCap ctSlot;
    updateCap ctSlot (ArchObjectCap $
                           cap \<lparr> capPTMappedAddress := Nothing \<rparr>)
  od)
  )"

defs pteCheckIfMapped_def:
"pteCheckIfMapped slot\<equiv> (do
    pt \<leftarrow> getObject slot;
    return $ pt \<noteq> InvalidPTE
od)"

defs pdeCheckIfMapped_def:
"pdeCheckIfMapped slot\<equiv> (do
    pd \<leftarrow> getObject slot;
    return $ pd \<noteq> InvalidPDE
od)"

defs performPageInvocation_def:
"performPageInvocation x0\<equiv> (case x0 of
    (PageMap asid cap ctSlot entries) \<Rightarrow>    (do
    updateCap ctSlot cap;
    (case entries of
          Inl (pte, slots) \<Rightarrow>   (do
            tlbFlush \<leftarrow> pteCheckIfMapped (head slots);
            mapM (flip storePTE pte) slots;
            doMachineOp $
                cleanCacheRange_PoU (VPtr $ fromPPtr $ head slots)
                                    (VPtr $ (fromPPtr (last slots)) + (bit (objBits (undefined::pte)) - 1))
                                    (addrFromPPtr (head slots));
            when tlbFlush $ invalidateTLBByASID asid
          od)
        | Inr (pde, slots) \<Rightarrow>   (do
            tlbFlush \<leftarrow> pdeCheckIfMapped (head slots);
            mapM (flip storePDE pde) slots;
            doMachineOp $
                cleanCacheRange_PoU (VPtr $ fromPPtr $ head slots)
                                    (VPtr $ (fromPPtr (last slots)) + (bit (objBits (undefined::pde)) - 1))
                                    (addrFromPPtr (head slots));
            when tlbFlush $ invalidateTLBByASID asid
        od)
        )
    od)
  | (PageRemap asid (Inl (pte, slots))) \<Rightarrow>    (do
    tlbFlush \<leftarrow> pteCheckIfMapped (head slots);
    mapM (flip storePTE pte) slots;
    doMachineOp $
        cleanCacheRange_PoU (VPtr $ fromPPtr $ head slots)
                            (VPtr $ (fromPPtr (last slots)) + (bit (objBits (undefined::pte)) - 1))
                            (addrFromPPtr (head slots));
    when tlbFlush $ invalidateTLBByASID asid
  od)
  | (PageRemap asid (Inr (pde, slots))) \<Rightarrow>    (do
    tlbFlush \<leftarrow> pdeCheckIfMapped (head slots);
    mapM (flip storePDE pde) slots;
    doMachineOp $
        cleanCacheRange_PoU (VPtr $ fromPPtr $ head slots)
                            (VPtr $ (fromPPtr (last slots)) + (bit (objBits (undefined::pde)) - 1))
                            (addrFromPPtr (head slots));
    when tlbFlush $ invalidateTLBByASID asid
  od)
  | (PageUnmap cap ctSlot) \<Rightarrow>    (do
    (case capVPMappedAddress cap of
          Some (asid, vaddr) \<Rightarrow>   unmapPage (capVPSize cap) asid vaddr
                                    (capVPBasePtr cap)
        | None \<Rightarrow>   return ()
        );
 cap \<leftarrow> liftM capCap $  getSlotCap ctSlot;
    updateCap ctSlot (ArchObjectCap $
                           cap \<lparr> capVPMappedAddress := Nothing \<rparr>)
  od)
  | (PageFlush typ start end pstart pd asid) \<Rightarrow>   
    when (start < end) $ (do
        root_switched \<leftarrow> setVMRootForFlush pd asid;
        doMachineOp $ doFlush typ start end pstart;
        when root_switched $ (do
            tcb \<leftarrow> getCurThread;
            setVMRoot tcb
        od)
    od)
  | (PageGetAddr ptr) \<Rightarrow>    (do
    paddr \<leftarrow> return ( fromPAddr $ addrFromPPtr ptr);
    ct \<leftarrow> getCurThread;
    msgTransferred \<leftarrow> setMRs ct Nothing [paddr];
    msgInfo \<leftarrow> return $ MI_ \<lparr>
            msgLength= msgTransferred,
            msgExtraCaps= 0,
            msgCapsUnwrapped= 0,
            msgLabel= 0 \<rparr>;
    setMessageInfo ct msgInfo
  od)
  )"

defs performASIDControlInvocation_def:
"performASIDControlInvocation x0\<equiv> (case x0 of
    (MakePool frame slot parent base) \<Rightarrow>    (do
    deleteObjects frame pageBits;
    pcap \<leftarrow> getSlotCap parent;
    updateCap parent (pcap \<lparr>capFreeIndex := maxFreeIndex (capBlockSize pcap) \<rparr>);
    placeNewObject frame (makeObject ::asidpool) 0;
    poolPtr \<leftarrow> return ( PPtr $ fromPPtr frame);
    cteInsert (ArchObjectCap $ ASIDPoolCap poolPtr base) parent slot;
    haskell_assert (base && mask asidLowBits = 0)
        [];
    asidTable \<leftarrow> gets (armKSASIDTable \<circ> ksArchState);
    asidTable' \<leftarrow> return ( asidTable aLU [(asidHighBitsOf base, Just poolPtr)]);
    modify (\<lambda> s. s \<lparr>
        ksArchState := (ksArchState s) \<lparr> armKSASIDTable := asidTable' \<rparr>\<rparr>)
    od)
  )"

defs performASIDPoolInvocation_def:
"performASIDPoolInvocation x0\<equiv> (case x0 of
    (Assign asid poolPtr ctSlot) \<Rightarrow>    (do
    oldcap \<leftarrow> getSlotCap ctSlot;
 pool \<leftarrow> liftM (inv ASIDPool) $  getObject poolPtr;
 cap \<leftarrow> liftM capCap $  return ( oldcap);
    updateCap ctSlot (ArchObjectCap $ cap \<lparr> capPDMappedASID := Just asid \<rparr>);
    pool' \<leftarrow> return ( pool aLU [(asid && mask asidLowBits, Just $ capPDBasePtr cap)]);
    setObject poolPtr $ ASIDPool pool'
    od)
  )"

defs storePDE_def:
"storePDE slot pde\<equiv> (do
    setObject slot pde;
    doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) $ wordFromPDE pde
od)"

defs storePTE_def:
"storePTE slot pte\<equiv> (do
    setObject slot pte;
    doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) $ wordFromPTE pte
od)"


defs checkValidMappingSize_def:
  "checkValidMappingSize sz \<equiv> stateAssert
    (\<lambda>s. 2 ^ pageBitsForSize sz <= gsMaxObjectSize s) []"

end
end
