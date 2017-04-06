(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchVSpace_H.thy *)
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
  "../Untyped_H"
  "../KI_Decls_H"
  ArchVSpaceDecls_H
begin

context Arch begin global_naming X64_H

defs kernelBase_def:
"kernelBase \<equiv> VPtr 0xffffffff80000000"

defs globalsBase_def:
"globalsBase \<equiv> VPtr 0xffffc000"

defs idleThreadStart_def:
"idleThreadStart \<equiv> globalsBase + VPtr 0x100"

defs copyGlobalMappings_def:
"copyGlobalMappings newPM\<equiv> (do
    globalPM \<leftarrow> gets (x64KSGlobalPML4 \<circ> ksArchState);
    base \<leftarrow> return ( getPML4Index pptrBase);
    pml4eBits \<leftarrow> return ( objBits (undefined ::pml4e));
    pmSize \<leftarrow> return ( 1 `~shiftL~` ptTranslationBits);
    forM_x [base  .e.  pmSize - 1] (\<lambda> index. (do
        offset \<leftarrow> return ( PPtr index `~shiftL~` pml4eBits);
        pml4e \<leftarrow> getObject $ globalPM + offset;
        storePML4E (newPM + offset) pml4e
    od))
od)"

defs createMappingEntries_def:
"createMappingEntries base vptr x2 vmRights attrib vspace\<equiv> (case x2 of
    X64SmallPage \<Rightarrow>    (doE
    p \<leftarrow> lookupErrorOnFailure False $ lookupPTSlot vspace vptr;
    returnOk $ (VMPTE $ SmallPagePTE_ \<lparr>
        pteFrame= base,
        pteGlobal= False,
        ptePAT= x64PAT attrib,
        pteDirty= False,
        pteAccessed= False,
        pteCacheDisabled= x64CacheDisabled attrib,
        pteWriteThrough= x64WriteThrough attrib,
        pteExecuteDisable= False,
        pteRights= vmRights \<rparr>, VMPTEPtr p)
    odE)
  | X64LargePage \<Rightarrow>    (doE
    p \<leftarrow> lookupErrorOnFailure False $ lookupPDSlot vspace vptr;
    returnOk $ (VMPDE $ LargePagePDE_ \<lparr>
        pdeFrame= base,
        pdeGlobal= False,
        pdePAT= x64PAT attrib,
        pdeDirty= False,
        pdeAccessed= False,
        pdeCacheDisabled= x64CacheDisabled attrib,
        pdeWriteThrough= x64WriteThrough attrib,
        pdeExecuteDisable= False,
        pdeRights= vmRights \<rparr>, VMPDEPtr p)
  odE)
  | X64HugePage \<Rightarrow>    (doE
    p \<leftarrow> lookupErrorOnFailure False $ lookupPDPTSlot vspace vptr;
    returnOk $ (VMPDPTE $ HugePagePDPTE_ \<lparr>
        pdpteFrame= base,
        pdpteGlobal= False,
        pdptePAT= False,
        pdpteDirty= False,
        pdpteAccessed= False,
        pdpteCacheDisabled= x64CacheDisabled attrib,
        pdpteWriteThrough= x64WriteThrough attrib,
        pdpteExecuteDisable= False,
        pdpteRights= vmRights \<rparr>, VMPDPTEPtr p)
  odE)
  )"

defs ensureSafeMapping_def:
"ensureSafeMapping x0\<equiv> (case x0 of
    (VMPTE InvalidPTE, _) \<Rightarrow>    returnOk ()
  | (VMPDE InvalidPDE, _) \<Rightarrow>    returnOk ()
  | (VMPDPTE InvalidPDPTE, _) \<Rightarrow>    returnOk ()
  | (VMPTE (SmallPagePTE _ _ _ _ _ _ _ _ _), VMPTEPtr slot) \<Rightarrow>    (doE
        pte \<leftarrow> withoutFailure $ getObject slot;
        (case pte of
              InvalidPTE \<Rightarrow>   returnOk ()
            | _ \<Rightarrow>   throw DeleteFirst
            )
  odE)
  | (VMPDE (LargePagePDE _ _ _ _ _ _ _ _ _), VMPDEPtr slot) \<Rightarrow>    (doE
        pde \<leftarrow> withoutFailure $ getObject slot;
        (case pde of
              InvalidPDE \<Rightarrow>   returnOk ()
            | _ \<Rightarrow>   throw DeleteFirst
            )
  odE)
  | (VMPDPTE (HugePagePDPTE _ _ _ _ _ _ _ _ _), VMPDPTEPtr slot) \<Rightarrow>    (doE
        pdpte \<leftarrow> withoutFailure $ getObject slot;
        (case pdpte of
              InvalidPDPTE \<Rightarrow>   returnOk ()
            | _ \<Rightarrow>   throw DeleteFirst
            )
  odE)
  | _ \<Rightarrow>    haskell_fail []
  )"

defs lookupIPCBuffer_def:
"lookupIPCBuffer isReceiver thread\<equiv> (do
    bufferPtr \<leftarrow> threadGet tcbIPCBuffer thread;
    bufferFrameSlot \<leftarrow> getThreadBufferSlot thread;
    bufferCap \<leftarrow> getSlotCap bufferFrameSlot;
    (let v14 = bufferCap in
        if isArchObjectCap v14 \<and> isPageCap (capCap v14)
        then let frame = capCap v14
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

defs findVSpaceForASID_def:
"findVSpaceForASID asid\<equiv> (doE
    haskell_assertE (asid > 0) [];
    haskell_assertE (asid \<le> snd asidRange) [];
    asidTable \<leftarrow> withoutFailure $ gets (x64KSASIDTable \<circ> ksArchState);
    poolPtr \<leftarrow> returnOk ( asidTable (asidHighBitsOf asid));
 pool \<leftarrow> liftME (inv ASIDPool) $  (case poolPtr of
          Some ptr \<Rightarrow>   withoutFailure $ getObject ptr
        | None \<Rightarrow>   throw InvalidRoot
        );
    pm \<leftarrow> returnOk ( pool (asid && mask asidLowBits));
    (case pm of
          Some ptr \<Rightarrow>   (doE
            haskell_assertE (ptr \<noteq> 0) [];
            returnOk ptr
          odE)
        | None \<Rightarrow>   throw InvalidRoot
        )
odE)"

defs findVSpaceForASIDAssert_def:
"findVSpaceForASIDAssert asid\<equiv> (do
    pm \<leftarrow> findVSpaceForASID asid `~catchFailure~`
        const (haskell_fail []);
    haskell_assert (pm && mask pml4Bits = 0)
        [];
    checkPML4At pm;
    checkPML4UniqueToASID pm asid;
    asidMap \<leftarrow> gets (x64KSASIDMap \<circ> ksArchState);
    flip haskell_assert []
        $ (case asidMap asid of
              None \<Rightarrow>   True
            | Some pm' \<Rightarrow>   pm = pm'
            );
    return pm
od)"

defs checkPML4UniqueToASID_def:
"checkPML4UniqueToASID pd asid \<equiv> checkPML4ASIDMapMembership pd [asid]"

defs checkPML4NotInASIDMap_def:
"checkPML4NotInASIDMap pd \<equiv> checkPML4ASIDMapMembership pd []"

defs lookupPTSlot_def:
"lookupPTSlot pm vptr\<equiv> (doE
    pdSlot \<leftarrow> lookupPDSlot pm vptr;
    pde \<leftarrow> withoutFailure $ getObject pdSlot;
    (case pde of
          PageTablePDE _ _ _ _ _ _ \<Rightarrow>   (doE
            pt \<leftarrow> returnOk ( ptrFromPAddr $ pdeTable pde);
            ptIndex \<leftarrow> returnOk ( getPTIndex vptr);
            ptSlot \<leftarrow> returnOk ( pt + (PPtr $ ptIndex `~shiftL~` 3));
            returnOk ptSlot
          odE)
        | _ \<Rightarrow>   throw $ MissingCapability pdShiftBits
        )
odE)"

defs lookupPDSlot_def:
"lookupPDSlot pm vptr\<equiv> (doE
    pdptSlot \<leftarrow> lookupPDPTSlot pm vptr;
    pdpte \<leftarrow> withoutFailure $ getObject pdptSlot;
    (case pdpte of
          PageDirectoryPDPTE _ _ _ _ _ _ \<Rightarrow>   (doE
            pd \<leftarrow> returnOk ( ptrFromPAddr $ pdpteTable pdpte);
            pdIndex \<leftarrow> returnOk ( getPDIndex vptr);
            pdSlot \<leftarrow> returnOk ( pd + (PPtr $ pdIndex `~shiftL~` 3));
            returnOk pdSlot
          odE)
        | _ \<Rightarrow>   throw $ MissingCapability pdptShiftBits
        )
odE)"

defs lookupPDPTSlot_def:
"lookupPDPTSlot pm vptr\<equiv> (doE
    pml4Slot \<leftarrow> returnOk ( lookupPML4Slot pm vptr);
    pml4e \<leftarrow> withoutFailure $ getObject pml4Slot;
    (case pml4e of
          PDPointerTablePML4E _ _ _ _ _ _ \<Rightarrow>   (doE
            pdpt \<leftarrow> returnOk ( ptrFromPAddr $ pml4eTable pml4e);
            pdptIndex \<leftarrow> returnOk ( getPDPTIndex vptr);
            pdptSlot \<leftarrow> returnOk ( pdpt + (PPtr $ pdptIndex `~shiftL~` 3));
            returnOk pdptSlot
          odE)
        | _ \<Rightarrow>   throw $ MissingCapability pml4ShiftBits
        )
odE)"

defs lookupPML4Slot_def:
"lookupPML4Slot pm vptr \<equiv>
    let pmIndex = getPML4Index vptr
    in pm + (PPtr $ pmIndex `~shiftL~` 3)"

defs handleVMFault_def:
"handleVMFault thread f\<equiv> (doE
    addr \<leftarrow> withoutFailure $ doMachineOp getFaultAddress;
    fault \<leftarrow> withoutFailure $ asUser thread $ getRegister (Register ErrorRegister);
    (case f of
          X64DataFault \<Rightarrow>   throw $ ArchFault $ VMFault addr [0, fault && mask 5]
        | X64InstructionFault \<Rightarrow>   throw $ ArchFault $ VMFault addr [1, fault && mask 5]
        )
odE)"

defs deleteASIDPool_def:
"deleteASIDPool base ptr\<equiv> (do
    haskell_assert (base && mask asidLowBits = 0)
        [];
    asidTable \<leftarrow> gets (x64KSASIDTable \<circ> ksArchState);
    when (asidTable (asidHighBitsOf base) = Just ptr) $ (do
 pool \<leftarrow> liftM (inv ASIDPool) $  getObject ptr;
        forM [0  .e.  (bit asidLowBits) - 1] (\<lambda> offset. (
            when (isJust $ pool offset) $ invalidateASIDEntry (base + offset) $ fromJust $ pool offset
        ));
        asidTable' \<leftarrow> return ( asidTable aLU [(asidHighBitsOf base, Nothing)]);
        modify (\<lambda> s. s \<lparr>
            ksArchState := (ksArchState s) \<lparr> x64KSASIDTable := asidTable' \<rparr>\<rparr>);
        tcb \<leftarrow> getCurThread;
        setVMRoot tcb
    od)
od)"

defs deleteASID_def:
"deleteASID asid pm\<equiv> (do
    asidTable \<leftarrow> gets (x64KSASIDTable \<circ> ksArchState);
    (case asidTable (asidHighBitsOf asid) of
          None \<Rightarrow>   return ()
        | Some poolPtr \<Rightarrow>   (do
 pool \<leftarrow> liftM (inv ASIDPool) $  getObject poolPtr;
            when (pool (asid && mask asidLowBits) = Just pm) $ (do
                invalidateASIDEntry asid pm;
                pool' \<leftarrow> return ( pool aLU [(asid && mask asidLowBits, Nothing)]);
                setObject poolPtr $ ASIDPool pool';
                tcb \<leftarrow> getCurThread;
                setVMRoot tcb
            od)
        od)
        )
od)"

defs unmapPDPT_def:
"unmapPDPT asid vaddr pdpt\<equiv> ignoreFailure $ (doE
    vspace \<leftarrow> findVSpaceForASID asid;
    pmSlot \<leftarrow> returnOk ( lookupPML4Slot vspace vaddr);
    pml4e \<leftarrow> withoutFailure $ getObject pmSlot;
    (case pml4e of
          PDPointerTablePML4E pt' _ _ _ _ _ \<Rightarrow>  
            if pt' = addrFromPPtr pdpt then returnOk () else throw InvalidRoot
        | _ \<Rightarrow>   throw InvalidRoot
        );
    withoutFailure $ (do
        flushPDPT (addrFromPPtr vspace) asid;
        storePML4E pmSlot InvalidPML4E
    od)
odE)"

defs unmapPageDirectory_def:
"unmapPageDirectory asid vaddr pd\<equiv> ignoreFailure $ (doE
    vspace \<leftarrow> findVSpaceForASID asid;
    pdptSlot \<leftarrow> lookupPDPTSlot vspace vaddr;
    pdpte \<leftarrow> withoutFailure $ getObject pdptSlot;
    (case pdpte of
          PageDirectoryPDPTE pd' _ _ _ _ _ \<Rightarrow>  
            if pd' = addrFromPPtr pd then returnOk () else throw InvalidRoot
        | _ \<Rightarrow>   throw InvalidRoot
        );
    withoutFailure $ (do
        flushPD (addrFromPPtr vspace) asid;
        storePDPTE pdptSlot InvalidPDPTE;
        invalidatePageStructureCacheASID (addrFromPPtr vspace) asid
    od)
odE)"

defs unmapPageTable_def:
"unmapPageTable asid vaddr pt\<equiv> ignoreFailure $ (doE
    vspace \<leftarrow> findVSpaceForASID asid;
    pdSlot \<leftarrow> lookupPDSlot vspace vaddr;
    pde \<leftarrow> withoutFailure $ getObject pdSlot;
    (case pde of
          PageTablePDE pt' _ _ _ _ _ \<Rightarrow>  
            if pt' = addrFromPPtr pt then returnOk () else throw InvalidRoot
        | _ \<Rightarrow>   throw InvalidRoot
        );
    withoutFailure $ (do
        flushTable vspace vaddr pt asid;
        storePDE pdSlot InvalidPDE;
        invalidatePageStructureCacheASID (addrFromPPtr vspace) asid
    od)
odE)"

defs unmapPage_def:
"unmapPage magnitude asid vptr ptr\<equiv> ignoreFailure $ (doE
    vspace \<leftarrow> findVSpaceForASID asid;
    (case magnitude of
          X64SmallPage \<Rightarrow>   (doE
            p \<leftarrow> lookupPTSlot vspace vptr;
            pte \<leftarrow> withoutFailure $ getObject p;
            checkMappingPPtr ptr (VMPTE pte);
            withoutFailure $ storePTE p InvalidPTE
          odE)
        | X64LargePage \<Rightarrow>   (doE
            p \<leftarrow> lookupPDSlot vspace vptr;
            pde \<leftarrow> withoutFailure $ getObject p;
            checkMappingPPtr ptr (VMPDE pde);
            withoutFailure $ storePDE p InvalidPDE
        odE)
        | X64HugePage \<Rightarrow>   (doE
            p \<leftarrow> lookupPDPTSlot vspace vptr;
            pdpte \<leftarrow> withoutFailure $ getObject p;
            checkMappingPPtr ptr (VMPDPTE pdpte);
            withoutFailure $ storePDPTE p InvalidPDPTE
        odE)
        );
    withoutFailure $ doMachineOp $ invalidateTranslationSingleASID vptr $ fromASID asid
odE)"

defs checkMappingPPtr_def:
"checkMappingPPtr pptr x1\<equiv> (case x1 of
    (VMPTE pte) \<Rightarrow>   
    (case pte of
          SmallPagePTE base _ _ _ _ _ _ _ _ \<Rightarrow>  
            unlessE (base = addrFromPPtr pptr) $ throw InvalidRoot
        | _ \<Rightarrow>   throw InvalidRoot
        )
  | (VMPDE pde) \<Rightarrow>   
    (case pde of
          LargePagePDE base _ _ _ _ _ _ _ _ \<Rightarrow>  
            unlessE (base = addrFromPPtr pptr) $ throw InvalidRoot
        | _ \<Rightarrow>   throw InvalidRoot
        )
  | (VMPDPTE pdpte) \<Rightarrow>   
    (case pdpte of
          HugePagePDPTE base _ _ _ _ _ _ _ _ \<Rightarrow>  
            unlessE (base = addrFromPPtr pptr) $ throw InvalidRoot
        | _ \<Rightarrow>   throw InvalidRoot
        )
  )"

defs getCurrentCR3_def:
"getCurrentCR3\<equiv> gets (x64KSCurrentCR3 \<circ> ksArchState)"

defs setCurrentCR3_def:
"setCurrentCR3 cr3\<equiv> (do
    modify (\<lambda> s. s \<lparr> ksArchState := (ksArchState s) \<lparr> x64KSCurrentCR3 := cr3 \<rparr>\<rparr>);
    doMachineOp $ writeCR3 (cr3BaseAddress cr3) $ fromASID $ cr3pcid cr3
od)"

defs invalidateLocalPageStructureCacheASID_def:
"invalidateLocalPageStructureCacheASID ptr asid\<equiv> (do
    curCR3 \<leftarrow> getCurrentCR3;
    setCurrentCR3 (CR3 ptr asid);
    setCurrentCR3 curCR3
od)"

defs invalidatePageStructureCacheASID_def:
"invalidatePageStructureCacheASID p a \<equiv> invalidateLocalPageStructureCacheASID p a"

defs getCurrentVSpaceRoot_def:
"getCurrentVSpaceRoot\<equiv> (do
    cur \<leftarrow> getCurrentCR3;
    return $ cr3BaseAddress cur
od)"

defs setCurrentVSpaceRoot_def:
"setCurrentVSpaceRoot vspace asid \<equiv> setCurrentCR3 $ CR3 vspace asid"

defs updateASIDMap_def:
"updateASIDMap asid\<equiv> (do
    vs \<leftarrow> findVSpaceForASIDAssert asid;
    asidMap \<leftarrow> gets (x64KSASIDMap \<circ> ksArchState);
    asidMap' \<leftarrow> return ( asidMap aLU [(asid, Just vs)]);
    modify (\<lambda> s. s \<lparr>
        ksArchState := (ksArchState s)
        \<lparr> x64KSASIDMap := asidMap' \<rparr>\<rparr>)
od)"

defs setVMRoot_def:
"setVMRoot tcb\<equiv> (do
    threadRootSlot \<leftarrow> getThreadVSpaceRoot tcb;
    threadRoot \<leftarrow> getSlotCap threadRootSlot;
    catchFailure
        ((case threadRoot of
              ArchObjectCap (PML4Cap pd (Some asid)) \<Rightarrow>   (doE
                pd' \<leftarrow> findVSpaceForASID asid;
                whenE (pd \<noteq> pd') $ throw InvalidRoot;
                withoutFailure $ updateASIDMap asid;
                curCR3 \<leftarrow> withoutFailure $ getCurrentCR3;
                whenE (curCR3 \<noteq> CR3 (addrFromPPtr pd) asid) $
                        withoutFailure $ setCurrentCR3 $ CR3 (addrFromPPtr pd) asid
              odE)
            | _ \<Rightarrow>   throw InvalidRoot)
            )
        (\<lambda> _. (do
            globalPML4 \<leftarrow> gets (x64KSGlobalPML4 \<circ> ksArchState);
            setCurrentVSpaceRoot (addrFromKPPtr globalPML4) 0
        od)
                                                             )
od)"

defs isValidVTableRoot_def:
"isValidVTableRoot x0\<equiv> (case x0 of
    (ArchObjectCap (PML4Cap _ (Some _))) \<Rightarrow>    True
  | _ \<Rightarrow>    False
  )"

defs checkValidIPCBuffer_def:
"checkValidIPCBuffer vptr x1\<equiv> (case x1 of
    (ArchObjectCap (PageCap _ _ _ _ _ _)) \<Rightarrow>    (doE
    whenE (vptr && mask 9 \<noteq> 0) $ throw AlignmentError;
    returnOk ()
    odE)
  | _ \<Rightarrow>    throw IllegalOperation
  )"

defs maskVMRights_def:
"maskVMRights r m\<equiv> (case (r, capAllowRead m, capAllowWrite m) of
      (VMReadOnly, True, _) \<Rightarrow>   VMReadOnly
    | (VMReadWrite, True, False) \<Rightarrow>   VMReadOnly
    | (VMReadWrite, True, True) \<Rightarrow>   VMReadWrite
    | _ \<Rightarrow>   VMKernelOnly
    )"

defs flushAll_def:
"flushAll vspace asid\<equiv> doMachineOp $ invalidateASID vspace (fromASID asid)"

defs flushPDPT_def:
"flushPDPT p a \<equiv> flushAll p a"

defs flushPD_def:
"flushPD p a \<equiv> flushAll p a"

defs flushTable_def:
"flushTable arg1 vptr pt asid \<equiv> (do
    haskell_assert (vptr && mask (ptTranslationBits + pageBits) = 0)
        [];
    pteBits \<leftarrow> return ( objBits (undefined ::pte));
    ptSize \<leftarrow> return ( 1 `~shiftL~` ptTranslationBits);
    forM_x [0  .e.  ptSize - 1] (\<lambda> index. (do
        offset \<leftarrow> return ( PPtr index `~shiftL~` pteBits);
        pte \<leftarrow> getObject $ pt + offset;
        (case pte of
              InvalidPTE \<Rightarrow>   return ()
            | _ \<Rightarrow>   let index' = index `~shiftL~` pageBits
                 in doMachineOp $ invalidateTranslationSingleASID (VPtr $ (fromVPtr vptr) + index') $ fromASID asid
            )
    od))
od)"

defs invalidateASID'_def:
"invalidateASID' asid\<equiv> (do
    findVSpaceForASIDAssert asid;
    asidMap \<leftarrow> gets (x64KSASIDMap \<circ> ksArchState);
    asidMap' \<leftarrow> return ( asidMap aLU [(asid, Nothing)]);
    modify (\<lambda> s. s \<lparr>
        ksArchState := (ksArchState s)
        \<lparr> x64KSASIDMap := asidMap' \<rparr>\<rparr>)
od)"

defs invalidateASIDEntry_def:
"invalidateASIDEntry asid vspace\<equiv> (do
    doMachineOp $ hwASIDInvalidate (addrFromPPtr vspace) (fromASID asid);
    invalidateASID' asid
od)"

defs attribsFromWord_def:
"attribsFromWord w \<equiv> VMAttributes_ \<lparr>
    x64WriteThrough= w !! 0,
    x64PAT= w !! 2,
    x64CacheDisabled= w !! 1 \<rparr>"

defs pageBase_def:
"pageBase vaddr magnitude\<equiv> vaddr && (complement $ mask (pageBitsForSize magnitude))"

defs decodeX64FrameInvocation_def:
"decodeX64FrameInvocation label args cte x3 extraCaps\<equiv> (let cap = x3 in
  if isPageCap cap
  then  
    (let (ilabel, args, extraCaps) = (invocationType label, args, extraCaps) in
        case (ilabel, args, extraCaps) of
        (ArchInvocationLabel X64PageMap, vaddr#rightsMask#attr#_, (vspaceCap, _)#_) =>  (doE
            whenE (isJust $ capVPMappedAddress cap) $
                throw $ InvalidCapability 0;
            (vspace,asid) \<leftarrow> (case vspaceCap of
                  ArchObjectCap (PML4Cap vspace (Some asid)) \<Rightarrow>   returnOk (vspace, asid)
                | _ \<Rightarrow>   throw $ InvalidCapability 1
                );
            vspaceCheck \<leftarrow> lookupErrorOnFailure False $ findVSpaceForASID asid;
            whenE (vspaceCheck \<noteq> vspace) $ throw $ InvalidCapability 1;
            vtop \<leftarrow> returnOk ( vaddr + (bit (pageBitsForSize $ capVPSize cap) - 1));
            whenE (VPtr vtop > kernelBase) $
                throw $ InvalidArgument 0;
            vmRights \<leftarrow> returnOk ( maskVMRights (capVPRights cap) $
                    rightsFromWord rightsMask);
            checkVPAlignment (capVPSize cap) (VPtr vaddr);
            entries \<leftarrow> createMappingEntries (addrFromPPtr $ capVPBasePtr cap)
                (VPtr vaddr) (capVPSize cap) vmRights
                (attribsFromWord attr) vspace;
            ensureSafeMapping entries;
            returnOk $ InvokePage $ PageMap_ \<lparr>
                pageMapCap= ArchObjectCap $ cap \<lparr> capVPMappedAddress:= Just (asid, VPtr vaddr) \<rparr>,
                pageMapCTSlot= cte,
                pageMapEntries= entries,
                pageMapVSpace= vspace \<rparr>
        odE)
        | (ArchInvocationLabel X64PageMap, _, _) =>  throw TruncatedMessage
        | (ArchInvocationLabel X64PageRemap, rightsMask#attr#_, (vspaceCap, _)#_) =>  (doE
            whenE (capVPMapType cap = VMIOSpaceMap) $ throw IllegalOperation;
            (vspace,asid) \<leftarrow> (case vspaceCap of
                  ArchObjectCap (PML4Cap vspace (Some asid)) \<Rightarrow>   returnOk (vspace,asid)
                | _ \<Rightarrow>   throw $ InvalidCapability 1
                );
            vspaceCheck \<leftarrow> lookupErrorOnFailure False $ findVSpaceForASID asid;
            whenE (vspaceCheck \<noteq> vspace) $ throw $ InvalidCapability 1;
            vaddr \<leftarrow> (case capVPMappedAddress cap of
                  Some (_, v) \<Rightarrow>   returnOk v
                | _ \<Rightarrow>   throw $ InvalidCapability 0
                );
            vmRights \<leftarrow> returnOk ( maskVMRights (capVPRights cap) $
                    rightsFromWord rightsMask);
            checkVPAlignment (capVPSize cap) vaddr;
            entries \<leftarrow> createMappingEntries (addrFromPPtr $ capVPBasePtr cap)
                vaddr (capVPSize cap) vmRights (attribsFromWord attr) vspace;
            returnOk $ InvokePage $ PageRemap_ \<lparr>
                pageRemapEntries= entries,
                pageRemapASID= asid,
                pageRemapVSpace= vspace \<rparr>
        odE)
        | (ArchInvocationLabel X64PageRemap, _, _) =>  throw TruncatedMessage
        | (ArchInvocationLabel X64PageUnmap, _, _) =>
              returnOk $ InvokePage $ PageUnmap_ \<lparr>
                pageUnmapCap= cap,
                pageUnmapCapSlot= cte \<rparr>
        | (ArchInvocationLabel X64PageGetAddress, _, _) =>  returnOk $ InvokePage $ PageGetAddr (capVPBasePtr cap)
        | _ =>  throw IllegalOperation
        )
  else   haskell_fail []
  )"

defs decodeX64PDPointerTableInvocation_def:
"decodeX64PDPointerTableInvocation label args cte x3 extraCaps\<equiv> (let cap = x3 in
  if isPDPointerTableCap cap
  then   (
    (let (label, args, extraCaps) = (invocationType label, args, extraCaps) in
        case (label, args, extraCaps) of
        (ArchInvocationLabel X64PDPTMap, vaddr'#attr#_, (vspaceCap,_)#_) =>  (doE
            whenE (isJust $ capPDPTMappedAddress cap) $
                throw $ InvalidCapability 0;
            (vspace,asid) \<leftarrow> (case vspaceCap of
                  ArchObjectCap (PML4Cap vspace (Some asid)) \<Rightarrow>   returnOk (vspace,asid)
                | _ \<Rightarrow>   throw $ InvalidCapability 1
                );
            shiftBits \<leftarrow> returnOk ( pageBits + ptTranslationBits + ptTranslationBits + ptTranslationBits);
            vaddr \<leftarrow> returnOk ( vaddr' && complement (mask shiftBits));
            whenE (VPtr vaddr \<ge> kernelBase ) $
                throw $ InvalidArgument 0;
            vspaceCheck \<leftarrow> lookupErrorOnFailure False $ findVSpaceForASID asid;
            whenE (vspaceCheck \<noteq> vspace) $ throw $ InvalidCapability 1;
            pml4Slot \<leftarrow> returnOk ( lookupPML4Slot vspace (VPtr vaddr));
            oldpml4e \<leftarrow> withoutFailure $ getObject pml4Slot;
            unlessE (oldpml4e = InvalidPML4E) $ throw DeleteFirst;
            pml4e \<leftarrow> returnOk ( PDPointerTablePML4E_ \<lparr>
                    pml4eTable= addrFromPPtr $ capPTBasePtr cap,
                    pml4eAccessed= False,
                    pml4eCacheDisabled= x64CacheDisabled $ attribsFromWord attr,
                    pml4eWriteThrough= x64WriteThrough $ attribsFromWord attr,
                    pml4eExecuteDisable= False,
                    pml4eRights= VMReadWrite \<rparr>);
            returnOk $ InvokePDPT $ PDPTMap_ \<lparr>
                pdptMapCap= ArchObjectCap $ cap \<lparr> capPDPTMappedAddress:= Just (asid, (VPtr vaddr)) \<rparr>,
                pdptMapCTSlot= cte,
                pdptMapPML4E= pml4e,
                pdptMapPML4Slot= pml4Slot,
                pdptMapVSpace= vspace \<rparr>
        odE)
        | (ArchInvocationLabel X64PageDirectoryMap, _, _) =>  throw TruncatedMessage
        | (ArchInvocationLabel X64PageDirectoryUnmap, _, _) =>  (doE
            cteVal \<leftarrow> withoutFailure $ getCTE cte;
            final \<leftarrow> withoutFailure $ isFinalCapability cteVal;
            unlessE final $ throw RevokeFirst;
            returnOk $ InvokePDPT $ PDPTUnmap_ \<lparr>
                pdptUnmapCap= cap,
                pdptUnmapCapSlot= cte \<rparr>
        odE)
        | _ =>  throw IllegalOperation
        )
  )
  else   haskell_fail []
  )"

defs decodeX64PageDirectoryInvocation_def:
"decodeX64PageDirectoryInvocation label args cte x3 extraCaps\<equiv> (let cap = x3 in
  if isPageDirectoryCap cap
  then  
    (let (label, args, extraCaps) = (invocationType label, args, extraCaps) in
        case (label, args, extraCaps) of
        (ArchInvocationLabel X64PageDirectoryMap, vaddr'#attr#_, (pml4Cap,_)#_) =>  (doE
            whenE (isJust $ capPDMappedAddress cap) $
                throw $ InvalidCapability 0;
            (pml,asid) \<leftarrow> (case pml4Cap of
                  ArchObjectCap (PML4Cap pml (Some asid)) \<Rightarrow>   returnOk (pml,asid)
                | _ \<Rightarrow>   throw $ InvalidCapability 1
                );
            shiftBits \<leftarrow> returnOk ( pageBits + ptTranslationBits + ptTranslationBits);
            vaddr \<leftarrow> returnOk ( vaddr' && complement (mask shiftBits));
            whenE (VPtr vaddr \<ge> kernelBase ) $
                throw $ InvalidArgument 0;
            pmlCheck \<leftarrow> lookupErrorOnFailure False $ findVSpaceForASID asid;
            whenE (pmlCheck \<noteq> pml) $ throw $ InvalidCapability 1;
            pdptSlot \<leftarrow> lookupErrorOnFailure False $ lookupPDPTSlot pml (VPtr vaddr);
            oldpde \<leftarrow> withoutFailure $ getObject pdptSlot;
            unlessE (oldpde = InvalidPDPTE) $ throw DeleteFirst;
            pdpte \<leftarrow> returnOk ( PageDirectoryPDPTE_ \<lparr>
                    pdpteTable= addrFromPPtr $ capPTBasePtr cap,
                    pdpteAccessed= False,
                    pdpteCacheDisabled= x64CacheDisabled $ attribsFromWord attr,
                    pdpteWriteThrough= x64WriteThrough $ attribsFromWord attr,
                    pdpteExecuteDisable= False,
                    pdpteRights= VMReadWrite \<rparr>);
            returnOk $ InvokePageDirectory $ PageDirectoryMap_ \<lparr>
                pdMapCap= ArchObjectCap $ cap \<lparr> capPDMappedAddress:= Just (asid, (VPtr vaddr)) \<rparr>,
                pdMapCTSlot= cte,
                pdMapPDPTE= pdpte,
                pdMapPDPTSlot= pdptSlot,
                pdMapVSpace= pml \<rparr>
        odE)
        | (ArchInvocationLabel X64PageDirectoryMap, _, _) =>  throw TruncatedMessage
        | (ArchInvocationLabel X64PageDirectoryUnmap, _, _) =>  (doE
            cteVal \<leftarrow> withoutFailure $ getCTE cte;
            final \<leftarrow> withoutFailure $ isFinalCapability cteVal;
            unlessE final $ throw RevokeFirst;
            returnOk $ InvokePageDirectory $ PageDirectoryUnmap_ \<lparr>
                pdUnmapCap= cap,
                pdUnmapCapSlot= cte \<rparr>
        odE)
        | _ =>  throw IllegalOperation
        )
  else   haskell_fail []
  )"

defs decodeX64PageTableInvocation_def:
"decodeX64PageTableInvocation label args cte x3 extraCaps\<equiv> (let cap = x3 in
  if isPageTableCap cap
  then  
   (let (label, args, extraCaps) = (invocationType label, args, extraCaps) in
        case (label, args, extraCaps) of
        (ArchInvocationLabel X64PageTableMap, vaddr'#attr#_, (pml4Cap,_)#_) =>  (doE
            whenE (isJust $ capPTMappedAddress cap) $
                throw $ InvalidCapability 0;
            (pml,asid) \<leftarrow> (case pml4Cap of
                  ArchObjectCap (PML4Cap pml (Some asid)) \<Rightarrow>   returnOk (pml,asid)
                | _ \<Rightarrow>   throw $ InvalidCapability 1
                );
            shiftBits \<leftarrow> returnOk ( pageBits + ptTranslationBits);
            vaddr \<leftarrow> returnOk ( vaddr' && complement (mask shiftBits));
            whenE (VPtr vaddr \<ge> kernelBase ) $
                throw $ InvalidArgument 0;
            pmlCheck \<leftarrow> lookupErrorOnFailure False $ findVSpaceForASID asid;
            whenE (pmlCheck \<noteq> pml) $ throw $ InvalidCapability 1;
            pdSlot \<leftarrow> lookupErrorOnFailure False $ lookupPDSlot pml (VPtr vaddr);
            oldpde \<leftarrow> withoutFailure $ getObject pdSlot;
            unlessE (oldpde = InvalidPDE) $ throw DeleteFirst;
            pde \<leftarrow> returnOk ( PageTablePDE_ \<lparr>
                    pdeTable= addrFromPPtr $ capPTBasePtr cap,
                    pdeAccessed= False,
                    pdeCacheDisabled= x64CacheDisabled $ attribsFromWord attr,
                    pdeWriteThrough= x64WriteThrough $ attribsFromWord attr,
                    pdeExecuteDisable= False,
                    pdeRights= VMReadWrite\<rparr>);
            returnOk $ InvokePageTable $ PageTableMap_ \<lparr>
                ptMapCap= ArchObjectCap $ cap \<lparr> capPTMappedAddress:= Just (asid, (VPtr vaddr)) \<rparr>,
                ptMapCTSlot= cte,
                ptMapPDE= pde,
                ptMapPDSlot= pdSlot,
                ptMapVSpace= pml \<rparr>
        odE)
        | (ArchInvocationLabel X64PageTableMap, _, _) =>  throw TruncatedMessage
        | (ArchInvocationLabel X64PageTableUnmap, _, _) =>  (doE
            cteVal \<leftarrow> withoutFailure $ getCTE cte;
            final \<leftarrow> withoutFailure $ isFinalCapability cteVal;
            unlessE final $ throw RevokeFirst;
            returnOk $ InvokePageTable $ PageTableUnmap_ \<lparr>
                ptUnmapCap= cap,
                ptUnmapCapSlot= cte \<rparr>
        odE)
        | _ =>  throw IllegalOperation
        )
  else   haskell_fail []
  )"

defs decodeX64ASIDControlInvocation_def:
"decodeX64ASIDControlInvocation label args x2 extraCaps\<equiv> (case x2 of
    ASIDControlCap \<Rightarrow>   
    (let (label, args, extraCaps) = (invocationType label, args, extraCaps) in
        case (label, args, extraCaps) of
        (ArchInvocationLabel X64ASIDControlMakePool, index#depth#_, (untyped,parentSlot)#(croot,_)#_) =>  (doE
            asidTable \<leftarrow> withoutFailure $ gets (x64KSASIDTable \<circ> ksArchState);
            free \<leftarrow> returnOk ( filter (\<lambda> (x,y). x \<le> (1 `~shiftL~` asidHighBits) - 1 \<and> isNothing y) $ assocs asidTable);
            whenE (null free) $ throw DeleteFirst;
            base \<leftarrow> returnOk ( (fst $ head free) `~shiftL~` asidLowBits);
            pool \<leftarrow> returnOk ( makeObject ::asidpool);
            frame \<leftarrow> (let v18 = untyped in
                if isUntypedCap v18 \<and> capBlockSize v18 = objBits pool \<and> \<not> capIsDevice v18
                then  (doE
                    ensureNoChildren parentSlot;
                    returnOk $ capPtr untyped
                odE)
                else  throw $ InvalidCapability 1
                );
            destSlot \<leftarrow> lookupTargetSlot croot (CPtr index) (fromIntegral depth);
            ensureEmptySlot destSlot;
            returnOk $ InvokeASIDControl $ MakePool_ \<lparr>
                makePoolFrame= frame,
                makePoolSlot= destSlot,
                makePoolParent= parentSlot,
                makePoolBase= base \<rparr>
        odE)
        | (ArchInvocationLabel X64ASIDControlMakePool, _, _) =>  throw TruncatedMessage
        | _ =>  throw IllegalOperation
        )
  | _ \<Rightarrow>    haskell_fail []
  )"

defs decodeX64ASIDPoolInvocation_def:
"decodeX64ASIDPoolInvocation label x1 extraCaps\<equiv> (let cap = x1 in
  if isASIDPoolCap cap
  then  
    (let (label, extraCaps) = (invocationType label, extraCaps) in
        case (label, extraCaps) of
        (ArchInvocationLabel X64ASIDPoolAssign, (vspaceCap,vspaceCapSlot)#_) => 
            (case vspaceCap of
                  ArchObjectCap (PML4Cap _ None) \<Rightarrow>   (doE
                    asidTable \<leftarrow> withoutFailure $ gets (x64KSASIDTable \<circ> ksArchState);
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
                        assignASIDCTSlot= vspaceCapSlot \<rparr>
                  odE)
                | _ \<Rightarrow>   throw $ InvalidCapability 1
                )
        | (ArchInvocationLabel X64ASIDPoolAssign, _) =>  throw TruncatedMessage
        | _ =>  throw IllegalOperation
        )
  else   haskell_fail []
  )"

defs decodeX64MMUInvocation_def:
"decodeX64MMUInvocation label args x2 cte x4 extraCaps\<equiv> (let cap = x4 in
  if isPageCap cap
  then
 decodeX64FrameInvocation label args cte cap extraCaps
  else if isPDPointerTableCap cap
  then
 decodeX64PDPointerTableInvocation label args cte cap extraCaps
  else if isPageDirectoryCap cap
  then
 decodeX64PageDirectoryInvocation label args cte cap extraCaps
  else if isPageTableCap cap
  then
 decodeX64PageTableInvocation label args cte cap extraCaps
  else if isASIDControlCap cap
  then
 decodeX64ASIDControlInvocation label args cap extraCaps
  else if isASIDPoolCap cap
  then
 decodeX64ASIDPoolInvocation label cap extraCaps
  else   haskell_fail []
  )"

defs checkVPAlignment_def:
"checkVPAlignment sz w \<equiv>
    unlessE (w && mask (pageBitsForSize sz) = 0) $
           throw AlignmentError"

defs performX64MMUInvocation_def:
"performX64MMUInvocation i\<equiv> withoutPreemption $ (do
    (case i of
          InvokePDPT oper \<Rightarrow>   performPDPTInvocation oper
        | InvokePageDirectory oper \<Rightarrow>   performPageDirectoryInvocation oper
        | InvokePageTable oper \<Rightarrow>   performPageTableInvocation oper
        | InvokePage oper \<Rightarrow>   performPageInvocation oper
        | InvokeASIDControl oper \<Rightarrow>   performASIDControlInvocation oper
        | InvokeASIDPool oper \<Rightarrow>   performASIDPoolInvocation oper
        | _ \<Rightarrow>   haskell_fail []
        );
    return $ []
od)"

defs performPDPTInvocation_def:
"performPDPTInvocation x0\<equiv> (case x0 of
    (PDPTMap cap ctSlot pml4e pml4Slot vspace) \<Rightarrow>    (do
    updateCap ctSlot cap;
    storePML4E pml4Slot pml4e;
    asid \<leftarrow> (case cap of
              ArchObjectCap (PDPointerTableCap _ (Some (a, _))) \<Rightarrow>   return a
            | _ \<Rightarrow>   haskell_fail []
            );
    invalidatePageStructureCacheASID (addrFromPPtr vspace) asid
    od)
  | (PDPTUnmap cap ctSlot) \<Rightarrow>    (do
    (case capPDPTMappedAddress cap of
          Some (asid, vaddr) \<Rightarrow>   (do
            unmapPDPT asid vaddr (capPDPTBasePtr cap);
            ptr \<leftarrow> return ( capPDPTBasePtr cap);
            pdpteBits \<leftarrow> return ( objBits InvalidPDPTE);
            slots \<leftarrow> return ( [ptr, ptr + bit pdpteBits  .e.  ptr + bit pdptBits - 1]);
            mapM_x (flip storePDPTE InvalidPDPTE) slots
          od)
        | _ \<Rightarrow>   return ()
        );
 cap \<leftarrow> liftM capCap $  getSlotCap ctSlot;
    updateCap ctSlot (ArchObjectCap $ cap \<lparr> capPDPTMappedAddress := Nothing \<rparr>)
  od)
  )"

defs performPageDirectoryInvocation_def:
"performPageDirectoryInvocation x0\<equiv> (case x0 of
    (PageDirectoryMap cap ctSlot pdpte pdptSlot vspace) \<Rightarrow>    (do
    updateCap ctSlot cap;
    storePDPTE pdptSlot pdpte;
    asid \<leftarrow> (case cap of
              ArchObjectCap (PageDirectoryCap _ (Some (a, _))) \<Rightarrow>   return a
            | _ \<Rightarrow>   haskell_fail []
            );
    invalidatePageStructureCacheASID (addrFromPPtr vspace) asid
    od)
  | (PageDirectoryUnmap cap ctSlot) \<Rightarrow>    (do
    (case capPDMappedAddress cap of
          Some (asid, vaddr) \<Rightarrow>   (do
            unmapPageDirectory asid vaddr (capPDBasePtr cap);
            ptr \<leftarrow> return ( capPDBasePtr cap);
            pdeBits \<leftarrow> return ( objBits InvalidPDE);
            slots \<leftarrow> return ( [ptr, ptr + bit pdeBits  .e.  ptr + bit pdBits - 1]);
            mapM_x (flip storePDE InvalidPDE) slots
          od)
        | _ \<Rightarrow>   return ()
        );
 cap \<leftarrow> liftM capCap $  getSlotCap ctSlot;
    updateCap ctSlot (ArchObjectCap $ cap \<lparr> capPDMappedAddress := Nothing \<rparr>)
  od)
  )"

defs performPageTableInvocation_def:
"performPageTableInvocation x0\<equiv> (case x0 of
    (PageTableMap cap ctSlot pde pdSlot vspace) \<Rightarrow>    (do
    updateCap ctSlot cap;
    storePDE pdSlot pde;
    asid \<leftarrow> (case cap of
              ArchObjectCap (PageTableCap _ (Some (a, _))) \<Rightarrow>   return a
            | _ \<Rightarrow>   haskell_fail []
            );
    invalidatePageStructureCacheASID (addrFromPPtr vspace) asid
    od)
  | (PageTableUnmap cap slot) \<Rightarrow>    (do
    (case capPTMappedAddress cap of
          Some (asid, vaddr) \<Rightarrow>   (do
            unmapPageTable asid vaddr (capPTBasePtr cap);
            ptr \<leftarrow> return ( capPTBasePtr cap);
            pteBits \<leftarrow> return ( objBits InvalidPTE);
            slots \<leftarrow> return ( [ptr, ptr + bit pteBits  .e.  ptr + bit ptBits - 1]);
            mapM_x (flip storePTE InvalidPTE) slots
          od)
        | _ \<Rightarrow>   return ()
        );
 cap \<leftarrow> liftM capCap $  getSlotCap slot;
    updateCap slot (ArchObjectCap $ cap \<lparr> capPTMappedAddress := Nothing \<rparr>)
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
    (PageMap cap ctSlot entries vspace) \<Rightarrow>    (do
    updateCap ctSlot cap;
    (case entries of
          (VMPTE pte, VMPTEPtr slot) \<Rightarrow>   storePTE slot pte
        | (VMPDE pde, VMPDEPtr slot) \<Rightarrow>   storePDE slot pde
        | (VMPDPTE pdpte, VMPDPTEPtr slot) \<Rightarrow>   storePDPTE slot pdpte
        | _ \<Rightarrow>   haskell_fail []
        );
    asid \<leftarrow> (case cap of
          ArchObjectCap (PageCap _ _ _ _ _ (Some (as, _))) \<Rightarrow>   return as
        | _ \<Rightarrow>   haskell_fail []
        );
    invalidateLocalPageStructureCacheASID (addrFromPPtr vspace) asid
    od)
  | (PageRemap entries asid vspace) \<Rightarrow>    (do
    (case entries of
          (VMPTE pte, VMPTEPtr slot) \<Rightarrow>   storePTE slot pte
        | (VMPDE pde, VMPDEPtr slot) \<Rightarrow>   storePDE slot pde
        | (VMPDPTE pdpte, VMPDPTEPtr slot) \<Rightarrow>   storePDPTE slot pdpte
        | _ \<Rightarrow>   haskell_fail []
        );
    invalidateLocalPageStructureCacheASID (addrFromPPtr vspace) asid
  od)
  | (PageUnmap cap ctSlot) \<Rightarrow>    (do
    (case capVPMappedAddress cap of
          Some (asid, vaddr) \<Rightarrow>   unmapPage (capVPSize cap) asid vaddr
                                    (capVPBasePtr cap)
        | _ \<Rightarrow>   return ()
        );
 cap \<leftarrow> liftM capCap $  getSlotCap ctSlot;
    updateCap ctSlot (ArchObjectCap $
                          cap \<lparr> capVPMappedAddress := Nothing \<rparr>)
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
    updateFreeIndex parent (maxFreeIndex (capBlockSize pcap));
    placeNewObject frame (makeObject ::asidpool) 0;
    poolPtr \<leftarrow> return ( PPtr $ fromPPtr frame);
    cteInsert (ArchObjectCap $ ASIDPoolCap poolPtr base) parent slot;
    haskell_assert (base && mask asidLowBits = 0)
        [];
    asidTable \<leftarrow> gets (x64KSASIDTable \<circ> ksArchState);
    asidTable' \<leftarrow> return ( asidTable aLU [(asidHighBitsOf base, Just poolPtr)]);
    modify (\<lambda> s. s \<lparr>
        ksArchState := (ksArchState s) \<lparr> x64KSASIDTable := asidTable' \<rparr>\<rparr>)
    od)
  )"

defs performASIDPoolInvocation_def:
"performASIDPoolInvocation x0\<equiv> (case x0 of
    (Assign asid poolPtr ctSlot) \<Rightarrow>    (do
    oldcap \<leftarrow> getSlotCap ctSlot;
 cap \<leftarrow> liftM capCap $  return ( oldcap);
    updateCap ctSlot (ArchObjectCap $ cap \<lparr> capPML4MappedASID := Just asid \<rparr>);
 pool \<leftarrow> liftM (inv ASIDPool) $  getObject poolPtr;
    pool' \<leftarrow> return ( pool aLU [(asid && mask asidLowBits, Just $ capPML4BasePtr cap)]);
    setObject poolPtr $ ASIDPool pool'
    od)
  )"

defs storePML4E_def:
"storePML4E slot pml4e\<equiv> (do
    setObject slot pml4e;
    doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) $ wordFromPML4E pml4e
od)"

defs storePDPTE_def:
"storePDPTE slot pdpte\<equiv> (do
    setObject slot pdpte;
    doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) $ wordFromPDPTE pdpte
od)"

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

defs mapKernelWindow_def:
"mapKernelWindow \<equiv> error []"

defs activateGlobalVSpace_def:
"activateGlobalVSpace \<equiv> error []"

defs createIPCBufferFrame_def:
"createIPCBufferFrame \<equiv> error []"

defs createBIFrame_def:
"createBIFrame \<equiv> error []"

defs createFramesOfRegion_def:
"createFramesOfRegion \<equiv> error []"

defs createITPDPTs_def:
"createITPDPTs  \<equiv> error []"

defs writeITPDPTs_def:
"writeITPDPTs  \<equiv> error []"

defs createITASIDPool_def:
"createITASIDPool  \<equiv> error []"

defs writeITASIDPool_def:
"writeITASIDPool  \<equiv> error []"

defs createDeviceFrames_def:
"createDeviceFrames  \<equiv> error []"

defs vptrFromPPtr_def:
"vptrFromPPtr  \<equiv> error []"


defs checkValidMappingSize_def:
  "checkValidMappingSize sz \<equiv> stateAssert
    (\<lambda>s. 2 ^ pageBitsForSize sz <= gsMaxObjectSize s) []"

end

end
