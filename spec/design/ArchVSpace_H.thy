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
  CNode_H
  KI_Decls_H
  ArchVSpaceDecls_H
begin

defs kernelBase_def:
"kernelBase \<equiv> VPtr 0xf0000000"

defs globalsBase_def:
"globalsBase \<equiv> VPtr 0xff000000"

defs idleThreadStart_def:
"idleThreadStart \<equiv> globalsBase + VPtr 0x100"

defs idleThreadCode_def:
"idleThreadCode \<equiv>
    [ 0xe3a00000
    , 0xee070f9a
    , 0xee070f90
    , 0xeafffffc
    ]"

defs initKernelVM_def:
"initKernelVM\<equiv> (do
    createGlobalPD;
    allMemory \<leftarrow> doMachineOp getMemoryRegions;
    mapM_x mapKernelRegion allMemory;
    kernelDevices \<leftarrow> doMachineOp getKernelDevices;
    mapM_x mapKernelDevice kernelDevices;
    createGlobalsFrame;
    mapGlobalsFrame;
    activateGlobalPD
od)"

defs initVSpace_def:
"initVSpace cRootSlot vRootSlot\<equiv> (do
    provideRegion $ BootRegion
        (CPtr $ fromVPtr kernelBase) maxBound BRCapsOnly 0;
    vRoot \<leftarrow> createInitialRoot vRootSlot;
    cRoot \<leftarrow> doKernelOp $ getSlotCap cRootSlot;
    populateInitialRoot vRoot cRoot;
    doKernelOp $ doMachineOp cleanCaches_PoU
od)"

defs createGlobalPD_def:
"createGlobalPD\<equiv> (do
    globalPD \<leftarrow> gets $ armKSGlobalPD \<circ> ksArchState;
    deleteObjects (PPtr $ fromPPtr globalPD) pdBits;
    placeNewObject (PPtr $ fromPPtr globalPD) (makeObject ::pde)
          (pdBits `~shiftR~` (objBits (makeObject ::pde)));
    globalPTs \<leftarrow> gets $ armKSGlobalPTs \<circ> ksArchState;
    deleteObjects (PPtr $ fromPPtr $ head globalPTs) pageBits;
    placeNewObject (PPtr $ fromPPtr $ head globalPTs) (makeObject ::pte)
          (pageBits `~shiftR~` (objBits (makeObject ::pte)));
    return ()
od)"

defs activateGlobalPD_def:
"activateGlobalPD\<equiv> (do
    doMachineOp cleanCaches_PoU;
    globalPD \<leftarrow> gets $ armKSGlobalPD \<circ> ksArchState;
    doMachineOp $ (do
        setCurrentPD $ addrFromPPtr globalPD;
        invalidateTLB
    od)
od)"

defs mapKernelRegion_def:
"mapKernelRegion x0\<equiv> (case x0 of
    (phys, physEnd) \<Rightarrow>    (do
    magnitude \<leftarrow> return ( physEnd - phys);
    pdeBits \<leftarrow> return ( objBits (undefined ::pde));
    haskell_assert (magnitude \<ge> bit (pageBitsForSize ARMSection))
        [];
    globalPD \<leftarrow> gets $ armKSGlobalPD \<circ> ksArchState;
    if (magnitude < bit (pageBitsForSize ARMSuperSection))
      then forM_x [phys, phys + bit (pageBitsForSize ARMSection)  .e.  phys + magnitude - 1] (\<lambda> phys. (do
          virt \<leftarrow> return ( VPtr $ fromPPtr $ ptrFromPAddr phys);
          pde \<leftarrow> return ( SectionPDE_ \<lparr>
                  pdeFrame= phys,
                  pdeParity= True,
                  pdeDomain= 0,
                  pdeCacheable= True,
                  pdeGlobal= True,
                  pdeExecuteNever= False,
                  pdeRights= VMKernelOnly \<rparr>);
          offset \<leftarrow> return ( fromVPtr virt `~shiftR~` pageBitsForSize ARMSection);
          slot \<leftarrow> return ( globalPD + PPtr (offset `~shiftL~` pdeBits));
          storePDE slot pde
      od))
      else forM_x [phys, phys + bit (pageBitsForSize ARMSuperSection)  .e.  phys + magnitude - 1] (\<lambda> phys. (do
          virt \<leftarrow> return ( VPtr $ fromPPtr $ ptrFromPAddr phys);
          pde \<leftarrow> return ( SuperSectionPDE_ \<lparr>
                  pdeFrame= phys,
                  pdeParity= True,
                  pdeCacheable= True,
                  pdeGlobal= True,
                  pdeExecuteNever= False,
                  pdeRights= VMKernelOnly \<rparr>);
          offset \<leftarrow> return ( fromVPtr virt `~shiftR~` pageBitsForSize ARMSection);
          slots \<leftarrow> return ( map (\<lambda> n. globalPD + PPtr (n `~shiftL~` pdeBits))
                  [offset  .e.  offset + 15]);
          mapM_x (flip storePDE pde) slots
      od))
    od)
  )"

defs mapKernelFrame_def:
"mapKernelFrame paddr vptr rights attributes\<equiv> (do
    haskell_assert (vptr \<ge> kernelBase) [];
    pd \<leftarrow> gets $ armKSGlobalPD \<circ> ksArchState;
    pdSlot \<leftarrow> return ( lookupPDSlot pd vptr);
    pde \<leftarrow> getObject pdSlot;
    pteBits \<leftarrow> return ( objBits (undefined ::pte));
    ptIndex \<leftarrow> return ( fromVPtr $ vptr `~shiftR~` 12 && 0xff);
    ptSlot \<leftarrow> (case pde of
          PageTablePDE _ _ _ \<Rightarrow>   (do
            pt \<leftarrow> return ( ptrFromPAddr $ pdeTable pde);
            return $ pt + (PPtr $ ptIndex `~shiftL~` pteBits)
          od)
        | InvalidPDE  \<Rightarrow>   (do
            ptFrame \<leftarrow> allocKernelPT;
            pde \<leftarrow> return ( PageTablePDE_ \<lparr>
                    pdeTable= addrFromPPtr ptFrame,
                    pdeParity= True,
                    pdeDomain= 0 \<rparr>);
            storePDE pdSlot pde;
            return $ PPtr $ fromPPtr ptFrame + (ptIndex `~shiftL~` pteBits)
        od)
        | _ \<Rightarrow>   haskell_fail []
        );
    pte \<leftarrow> getObject ptSlot;
    (case pte of
          InvalidPTE  \<Rightarrow>   (do
            pte' \<leftarrow> return ( SmallPagePTE_ \<lparr>
                pteFrame= paddr,
                pteCacheable= armPageCacheable attributes,
                pteGlobal= True,
                pteExecuteNever= False,
                pteRights= rights \<rparr>);
            storePTE ptSlot pte'
          od)
        | _ \<Rightarrow>   haskell_fail []
        )
od)"

defs allocKernelPT_def:
"allocKernelPT\<equiv> (do
    pts \<leftarrow> gets $ armKSGlobalPTs \<circ> ksArchState;
    (case pts of
          [] \<Rightarrow>   haskell_fail []
        | (pt#pts') \<Rightarrow>   (do
            modify (\<lambda> ks. ks \<lparr>
                ksArchState := (ksArchState ks) \<lparr> armKSGlobalPTs := pts' \<rparr> \<rparr>);
            return pt
        od)
        )
od)"

defs mapKernelDevice_def:
"mapKernelDevice x0\<equiv> (case x0 of
    (addr, ptr) \<Rightarrow>    (do
    vptr \<leftarrow> return ( VPtr $ fromPPtr ptr);
    mapKernelFrame addr vptr VMKernelOnly $ VMAttributes False False False
    od)
  )"

defs createGlobalsFrame_def:
"createGlobalsFrame\<equiv> (do
    globals \<leftarrow> gets $ armKSGlobalsFrame \<circ> ksArchState;
    deleteObjects (PPtr $ fromPPtr globals) pageBits;
    reserveFrame (PPtr $ fromPPtr globals) True;
    offset \<leftarrow> return ( fromVPtr $ idleThreadStart - globalsBase);
    doMachineOp $ mapM_x
        (split  storeWord
        )
        (zipE2 (globals + PPtr offset) ( globals + PPtr offset + 4) (idleThreadCode))
od)"

defs mapGlobalsFrame_def:
"mapGlobalsFrame\<equiv> (do
    globalsFrame \<leftarrow> gets $ armKSGlobalsFrame \<circ> ksArchState;
    mapKernelFrame (addrFromPPtr globalsFrame) globalsBase VMReadOnly $
        VMAttributes True True False
od)"

defs createInitialRoot_def:
"createInitialRoot slot\<equiv> (do
    asid \<leftarrow> return ( 1);
    initPDFrame \<leftarrow> allocRegion pdBits;
    initPD \<leftarrow> return ( ptrFromPAddr initPDFrame);
    rootCap \<leftarrow> return ( ArchObjectCap $ PageDirectoryCap_ \<lparr>
            capPDBasePtr= initPD,
            capPDMappedASID= Just asid \<rparr>);
    doKernelOp $ (do
        placeNewObject (ptrFromPAddr initPDFrame) (makeObject ::pde)
              (pdBits `~shiftR~` (objBits (makeObject ::pde)));
        copyGlobalMappings initPD;
        insertInitCap slot rootCap
    od);
    initASIDPoolFrame \<leftarrow> allocRegion $ objBits (undefined ::asidpool);
    initASIDPoolPtr \<leftarrow> return ( ptrFromPAddr initASIDPoolFrame);
 emptyASIDPool \<leftarrow> liftM (inv ASIDPool) $  return ( (makeObject ::asidpool));
    initASIDPool \<leftarrow> return ( ASIDPool $ emptyASIDPool aLU [(asid && mask asidLowBits, Just initPD)]);
    doKernelOp $ (do
        placeNewObject (ptrFromPAddr initASIDPoolFrame) initASIDPool 0;
        asidTable \<leftarrow> gets (armKSASIDTable \<circ> ksArchState);
        asidTable' \<leftarrow> return (
                asidTable aLU [(asidHighBitsOf asid, Just initASIDPoolPtr)]);
        modify (\<lambda> s. s \<lparr>
            ksArchState := (ksArchState s) \<lparr> armKSASIDTable := asidTable' \<rparr>\<rparr>)
    od);
    provideCap $ ArchObjectCap $ ASIDControlCap;
    provideCap $ ArchObjectCap $ ASIDPoolCap_ \<lparr>
        capASIDPool= initASIDPoolPtr,
        capASIDBase= 0 \<rparr>;
    return rootCap
od)"

defs populateInitialRoot_def:
"populateInitialRoot vRoot cRoot\<equiv> (do
    asid \<leftarrow> return ( fromJust $ capPDMappedASID $ capCap vRoot);
 pdCap \<leftarrow> liftM capCap $  return ( vRoot);
    pd \<leftarrow> return ( capPDBasePtr pdCap);
    (case cRoot of
          CNodeCap _ _ _ _ \<Rightarrow>   return ()
        | _ \<Rightarrow>   haskell_fail []
        );
    haskell_assert (capCNodeGuard cRoot = 0) $
        [];
    haskell_assert (capCNodeBits cRoot + capCNodeGuardSize cRoot + pageBits =
            finiteBitSize (undefined::machine_word)) $
        [];
    forM_x [0  .e.  1 `~shiftL~` capCNodeBits cRoot - 1] (\<lambda> index. (do
        cSlot \<leftarrow> doKernelOp $ locateSlot (capCNodePtr cRoot) index;
        cte \<leftarrow> doKernelOp $ getObject cSlot;
        (let v2 = cteCap cte in
            if isArchObjectCap v2 \<and> isPageCap (capCap v2)
            then
            let pageCap = capCap v2
            in  (do
                haskell_assert (capVPSize pageCap = ARMSmallPage) $
                    [];
                vaddr \<leftarrow> return ( VPtr $ index `~shiftL~` pageBits);
                pageCap' \<leftarrow> return ( pageCap \<lparr>
                        capVPMappedAddress := Just (asid, vaddr) \<rparr>);
                cte' \<leftarrow> return ( cte \<lparr> cteCap := ArchObjectCap pageCap' \<rparr>);
                doKernelOp $ setObject cSlot cte';
                mapUserFrame pd asid
                    (addrFromPPtr $ capVPBasePtr pageCap) vaddr
            od)
            else  return ()
            )
    od))
od)"

defs allocUserPT_def:
"allocUserPT asid vaddr\<equiv> (do
    initPTFrame \<leftarrow> allocRegion ptBits;
    doKernelOp $ placeNewObject (ptrFromPAddr initPTFrame)
        (makeObject ::pte) (ptBits `~shiftR~` (objBits (makeObject ::pte)));
    initPT \<leftarrow> return ( ptrFromPAddr initPTFrame);
    provideCap $ ArchObjectCap $ PageTableCap_ \<lparr>
        capPTBasePtr= initPT,
        capPTMappedAddress= Just (asid, vaddr) \<rparr>;
    return initPT
od)"

defs mapUserFrame_def:
"mapUserFrame pd asid paddr vptr\<equiv> (do
    haskell_assert (vptr < kernelBase) [];
    pdSlot \<leftarrow> return ( lookupPDSlot pd vptr);
    pde \<leftarrow> doKernelOp $ getObject pdSlot;
    pteBits \<leftarrow> return ( objBits (undefined ::pte));
    ptIndex \<leftarrow> return ( fromVPtr $ vptr `~shiftR~` 12 && 0xff);
    ptSlot \<leftarrow> (case pde of
          PageTablePDE _ _ _ \<Rightarrow>   (do
            pt \<leftarrow> return ( ptrFromPAddr $ pdeTable pde);
            return $ pt + (PPtr $ ptIndex `~shiftL~` pteBits)
          od)
        | InvalidPDE  \<Rightarrow>   (do
            ptFrame \<leftarrow> allocUserPT asid vptr;
            pde \<leftarrow> return ( PageTablePDE_ \<lparr>
                    pdeTable= addrFromPPtr ptFrame,
                    pdeParity= True,
                    pdeDomain= 0 \<rparr>);
            doKernelOp $ storePDE pdSlot pde;
            return $ PPtr $ fromPPtr ptFrame + (ptIndex `~shiftL~` pteBits)
        od)
        | _ \<Rightarrow>   haskell_fail []
        );
    doKernelOp $ (do
        pte \<leftarrow> getObject ptSlot;
        (case pte of
              InvalidPTE  \<Rightarrow>   (do
                pte' \<leftarrow> return ( SmallPagePTE_ \<lparr>
                    pteFrame= paddr,
                    pteCacheable= True,
                    pteGlobal= False,
                    pteExecuteNever= False,
                    pteRights= VMReadWrite \<rparr>);
                storePTE ptSlot pte'
              od)
            | _ \<Rightarrow>   haskell_fail []
            )
    od)
od)"

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
    (let v4 = bufferCap in
        if isArchObjectCap v4 \<and> isPageCap (capCap v4)
        then let frame = capCap v4
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
            ptIndex \<leftarrow> returnOk ( fromVPtr $ vptr `~shiftR~` 12 && 0xff);
            ptSlot \<leftarrow> returnOk ( pt + (PPtr $ ptIndex `~shiftL~` 2));
            withoutFailure $ checkPTAt pt;
            returnOk ptSlot
          odE)
        | _ \<Rightarrow>   throw $ MissingCapability 20
        )
odE)"

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
    (let v8 = threadRoot in
        if isArchObjectCap v8 \<and> isPageDirectoryCap (capCap v8) \<and> capPDMappedASID (capCap v8) \<noteq> None \<and> capPDBasePtr (capCap v8) = pd
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

defs createInitPage_def:
"createInitPage addr\<equiv> (do
    ptr \<leftarrow> return ( ptrFromPAddr addr);
    reserveFrame ptr False;
    return $ ArchObjectCap $ PageCap ptr VMReadWrite ARMSmallPage Nothing
od)"

defs createDeviceCap_def:
"createDeviceCap x0\<equiv> (case x0 of
    (addr, end) \<Rightarrow>    (do
    wptr \<leftarrow> return ( ptrFromPAddr addr);
    rawmagnitude \<leftarrow> return ( end - addr);
    sz \<leftarrow> return ( find (\<lambda> sz. rawmagnitude = bit (pageBitsForSize sz))
                  [minBound  .e.  maxBound]);
    magnitude \<leftarrow> (case sz of
          Some magnitude \<Rightarrow>   return magnitude
        | None \<Rightarrow>   haskell_fail []
        );
    return $ ArchObjectCap $ PageCap wptr VMReadWrite magnitude Nothing
    od)
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
        ARMPDClean_Data \<Rightarrow>   Clean
      | ARMPageClean_Data \<Rightarrow>   Clean
      | ARMPDInvalidate_Data \<Rightarrow>   Invalidate
      | ARMPageInvalidate_Data \<Rightarrow>   Invalidate
      | ARMPDCleanInvalidate_Data \<Rightarrow>   CleanInvalidate
      | ARMPageCleanInvalidate_Data \<Rightarrow>   CleanInvalidate
      | ARMPDUnify_Instruction \<Rightarrow>   Unify
      | ARMPageUnify_Instruction \<Rightarrow>   Unify
      | _ \<Rightarrow>   error []
      )"

defs pageBase_def:
"pageBase vaddr magnitude\<equiv> vaddr && (complement $ mask (pageBitsForSize magnitude))"

defs lookupPTSlot_nofail_def:
"lookupPTSlot_nofail pt vptr \<equiv>
    let ptIndex = fromVPtr $ (vptr `~shiftR~` 12) && mask 8
    in pt + (PPtr $ ptIndex `~shiftL~` 2)"

defs resolveVAddr_def:
"resolveVAddr pd vaddr\<equiv> (do
    pdSlot \<leftarrow> return ( lookupPDSlot pd vaddr);
    pde \<leftarrow> getObject pdSlot;
    (case pde of
          SectionPDE frame v18 v19 v20 v21 v22 v23 \<Rightarrow>   return $ Just (ARMSection, frame)
        | SuperSectionPDE frame v24 v25 v26 v27 v28 \<Rightarrow>   return $ Just (ARMSuperSection, frame)
        | PageTablePDE table v29 v30 \<Rightarrow>   (do
            pt \<leftarrow> return ( ptrFromPAddr table);
            pteSlot \<leftarrow> return ( lookupPTSlot_nofail pt vaddr);
            pte \<leftarrow> getObject pteSlot;
            (case pte of
                  LargePagePTE frame v10 v11 v12 v13 \<Rightarrow>   return $ Just (ARMLargePage, frame)
                | SmallPagePTE frame v14 v15 v16 v17 \<Rightarrow>   return $ Just (ARMSmallPage, frame)
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
    (case (isPDFlush (invocationType label), args) of
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
          (ARMPageTableMap, vaddr#attr#_, (pdCap,_)#_) \<Rightarrow>   (doE
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
        | (ARMPageTableMap, _, _) \<Rightarrow>   throw TruncatedMessage
        | (ARMPageTableUnmap, _, _) \<Rightarrow>   (doE
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
    (case (invocationType label, args, extraCaps) of
          (ARMPageMap, vaddr#rightsMask#attr#_, (pdCap,_)#_) \<Rightarrow>   (doE
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
        | (ARMPageMap, _, _) \<Rightarrow>   throw TruncatedMessage
        | (ARMPageRemap, rightsMask#attr#_, (pdCap, _)#_) \<Rightarrow>   (doE
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
        | (ARMPageRemap, _, _) \<Rightarrow>   throw TruncatedMessage
        | (ARMPageUnmap, _, _) \<Rightarrow>   returnOk $ InvokePage $ PageUnmap_ \<lparr>
                pageUnmapCap= cap,
                pageUnmapCapSlot= cte \<rparr>
        | (ARMPageClean_Data, _, _) \<Rightarrow>   decodeARMPageFlush label args cap
        | (ARMPageInvalidate_Data, _, _) \<Rightarrow>   decodeARMPageFlush label args cap
        | (ARMPageCleanInvalidate_Data, _, _) \<Rightarrow>   decodeARMPageFlush label args cap
        | (ARMPageUnify_Instruction, _, _) \<Rightarrow>   decodeARMPageFlush label args cap
        | (ARMPageGetAddress, _, _) \<Rightarrow>   returnOk $ InvokePage $ PageGetAddr (capVPBasePtr cap)
        | _ \<Rightarrow>   throw IllegalOperation
        )
  else if isASIDControlCap cap
  then  
    (case (invocationType label, args, extraCaps) of
          (ARMASIDControlMakePool, index#depth#_, (untyped,parentSlot)#(root,_)#_) \<Rightarrow>   (doE
            asidTable \<leftarrow> withoutFailure $ gets (armKSASIDTable \<circ> ksArchState);
            free \<leftarrow> returnOk ( filter (\<lambda> (x,y). x \<le> (1 `~shiftL~` asidHighBits) - 1 \<and> isNothing y) $ assocs asidTable);
            whenE (null free) $ throw DeleteFirst;
            base \<leftarrow> returnOk ( (fst $ head free) `~shiftL~` asidLowBits);
            pool \<leftarrow> returnOk ( makeObject ::asidpool);
            frame \<leftarrow> (let v31 = untyped in
                if isUntypedCap v31 \<and> capBlockSize v31 = objBits pool
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
        | (ARMASIDControlMakePool, _, _) \<Rightarrow>   throw TruncatedMessage
        | _ \<Rightarrow>   throw IllegalOperation
        )
  else if isASIDPoolCap cap
  then  
    (case (invocationType label, extraCaps) of
          (ARMASIDPoolAssign, (pdCap,pdCapSlot)#_) \<Rightarrow>  
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
        | (ARMASIDPoolAssign, _) \<Rightarrow>   throw TruncatedMessage
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


end
