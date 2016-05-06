(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Retyping Objects"

theory ArchRetype_H
imports
  ArchRetypeDecls_H
  ArchVSpaceDecls_H
  Hardware_H
  "../KI_Decls_H"
begin

context X64 begin

defs deriveCap_def:
"deriveCap x0 x1\<equiv> (let c = x1 in
  if isPageTableCap c \<and> capPTMappedAddress c \<noteq> None
  then   returnOk c
  else if isPageTableCap c \<and> capPTMappedAddress c = None
  then   throw IllegalOperation
  else if isPageDirectoryCap c \<and> capPDMappedAddress c \<noteq> None
  then   returnOk c
  else if isPageDirectoryCap c \<and> capPDMappedAddress c = None
  then   throw IllegalOperation
  else if isPDPointerTableCap c \<and> capPDPTMappedAddress c \<noteq> None
  then   returnOk c
  else if isPDPointerTableCap c \<and> capPDPTMappedAddress c = None
  then   throw IllegalOperation
  else if isPML4Cap c \<and> capPML4MappedASID c \<noteq> None
  then   throw IllegalOperation
  else if isPML4Cap c \<and> capPML4MappedASID c = None
  then   returnOk c
  else if isPageCap c
  then   throw IllegalOperation
  else if isASIDControlCap c
  then   returnOk $ c \<lparr> capVPMappedAddress := Nothing, capVPMapType := VMNoMap \<rparr>
  else if isASIDPoolCap c
  then   returnOk c
  else if isIOPortCap c
  then   returnOk c
  else if isIOSpaceCap c
  then   returnOk c
  else if isIOPageTableCap c \<and> capIOPTMappedAddress c \<noteq> None
  then   returnOk c
  else if isIOPageTableCap c \<and> capIOPTMappedAddress c = None
  then   returnOk c
  else undefined
  )"

defs ioSpaceGetDomainID_def:
"ioSpaceGetDomainID dat \<equiv> error []"

defs ioSpaceGetPCIDevice_def:
"ioSpaceGetPCIDevice dat \<equiv> error []"

defs ioPortGetFirstPort_def:
"ioPortGetFirstPort dat \<equiv> error []"

defs ioPortGetLastPort_def:
"ioPortGetLastPort dat \<equiv> error []"

defs updateCapData_def:
"updateCapData preserve newData x2\<equiv> (let c = x2 in
  if isIOSpaceCap c
  then  
    let
        pciDevice = ioSpaceGetPCIDevice newData;
        domID = ioSpaceGetDomainID newData;
        fstValidDom = firstValidIODomain;
        domIDBits = numIODomainIDBits
    in
    if (Not preserve \<and> capIOPCIDevice c = Nothing \<and> domID \<ge> fstValidDom
                    \<and> domID \<noteq> 0 \<and> domID \<le> mask domIDBits)
               then (ArchObjectCap (IOSpaceCap domID pciDevice))
               else NullCap
  else if isIOPortCap c
  then  
    let
        firstPort = ioPortGetFirstPort newData;
        lastPort = ioPortGetLastPort newData
    in
    if (capIOPortFirstPort c \<le> capIOPortLastPort c)
     then if (firstPort \<le> lastPort \<and> firstPort \<ge> capIOPortFirstPort c
                      \<and> lastPort \<le> capIOPortLastPort c)
               then (ArchObjectCap (IOPortCap firstPort lastPort))
               else NullCap
    else error []
  else   ArchObjectCap c
  )"

defs maskCapRights_def:
"maskCapRights r x1\<equiv> (let c = x1 in
  if isPageCap c
  then   ArchObjectCap $ c \<lparr>
    capVPRights := maskVMRights (capVPRights c) r \<rparr>
  else   ArchObjectCap c
  )"

defs finaliseCap_def:
"finaliseCap x0 x1\<equiv> (case (x0, x1) of
    ((ASIDPoolCap ptr b), True) \<Rightarrow>    (do
    deleteASIDPool b ptr;
    return NullCap
    od)
  | ((PML4Cap ptr (Some a)), True) \<Rightarrow>    (do
    deleteASID a ptr;
    return NullCap
  od)
  | ((PDPointerTableCap ptr (Some (a, v))), True) \<Rightarrow>    (do
    unmapPDPT a v ptr;
    return NullCap
  od)
  | ((PageDirectoryCap ptr (Some (a, v))), True) \<Rightarrow>    (do
    unmapPageDirectory a v ptr;
    return NullCap
  od)
  | ((PageTableCap ptr (Some (a, v))), True) \<Rightarrow>    (do
    unmapPageTable a v ptr;
    return NullCap
  od)
  | ((IOSpaceCap _ _), True) \<Rightarrow>    return NullCap
  | (c, b) \<Rightarrow>    (case (c, b) of
      ((IOPageTableCap baseptr level (Some (asid,ioaddr))), True) \<Rightarrow>   (do
        deleteIOPageTable c;
        unmapIOPageTable level asid ioaddr baseptr;
        return NullCap
      od)
    | ((PageCap baseptr _ VMIOSpaceMap vpsz _ (Some (asid, vaddr))), _) \<Rightarrow>   (do
        unmapIOPage vpsz (fromIntegral asid) vaddr baseptr;
        return NullCap
    od)
    | ((PageCap ptr _ _ s _ (Some (a, v))), _) \<Rightarrow>   (do
        unmapPage s a v ptr;
        return NullCap
    od)
    | (_, _) \<Rightarrow>   return NullCap
    )
  )"

defs resetMemMapping_def:
"resetMemMapping x0\<equiv> (case x0 of
    (PageCap p rts mtyp sz isdev _) \<Rightarrow>    PageCap p rts mtyp sz isdev Nothing
  | (PageTableCap ptr _) \<Rightarrow>    PageTableCap ptr Nothing
  | (PageDirectoryCap ptr _) \<Rightarrow>    PageDirectoryCap ptr Nothing
  | (PDPointerTableCap ptr _ ) \<Rightarrow>    PDPointerTableCap ptr Nothing
  | (PML4Cap ptr _) \<Rightarrow>    PML4Cap ptr Nothing
  | cap \<Rightarrow>    cap
  )"

defs recycleCap_def:
"recycleCap is_final x1 \<equiv> (let cap = x1 in
  if isPageCap cap
  then   (do
      doMachineOp $ clearMemory (capVPBasePtr cap)
          (1 `~shiftL~` (pageBitsForSize $ capVPSize cap));
      finaliseCap cap is_final;
      return $ resetMemMapping cap
  od)
  else if isPageTableCap cap
  then let ptr = capPTBasePtr cap in   (do
    pteBits \<leftarrow> return ( objBits InvalidPTE);
    slots \<leftarrow> return ( [ptr, ptr + bit pteBits  .e.  ptr + bit ptTranslationBits - 1]);
    mapM_x (flip storePTE InvalidPTE) slots;
    (case capPTMappedAddress cap of
          None \<Rightarrow>   return ()
        | Some (a, v) \<Rightarrow>   unmapPageTable a v ptr
        );
    finaliseCap cap is_final;
    return (if is_final then resetMemMapping cap else cap)
  od)
  else if isPageDirectoryCap cap
  then let ptr = capPDBasePtr cap in   (do
    pdeBits \<leftarrow> return ( objBits InvalidPDE);
    slots \<leftarrow> return ( [ptr, ptr + bit pdeBits  .e.  ptr + bit ptTranslationBits - 1]);
    mapM_x (flip storePDE InvalidPDE) slots;
    (case capPDMappedAddress cap of
          None \<Rightarrow>   return ()
        | Some (a, v) \<Rightarrow>   unmapPageDirectory a v ptr
        );
    finaliseCap cap is_final;
    return (if is_final then resetMemMapping cap else cap)
  od)
  else if isPDPointerTableCap cap
  then let ptr = capPDPTBasePtr cap in   (do
    pdpteBits \<leftarrow> return ( objBits InvalidPDPTE);
    slots \<leftarrow> return ( [ptr, ptr + bit pdpteBits  .e.  ptr + bit ptTranslationBits - 1]);
    mapM_x (flip storePDPTE InvalidPDPTE) slots;
    (case capPDMappedAddress cap of
          None \<Rightarrow>   return ()
        | Some (a, v) \<Rightarrow>   unmapPDPT a v ptr
        );
    finaliseCap cap is_final;
    return (if is_final then resetMemMapping cap else cap)
  od)
  else if isPML4Cap cap
  then let ptr = capPML4BasePtr cap in   (do
    pmBits \<leftarrow> return ( objBits InvalidPML4E);
    slots \<leftarrow> return ( [ptr, ptr + bit pmBits  .e.  ptr + bit ptTranslationBits - 1]);
    mapM_x (flip storePML4E InvalidPML4E) slots;
    finaliseCap cap is_final;
    return (if is_final then resetMemMapping cap else cap)
  od)
  else if isIOPortCap cap
  then   return cap
  else if isIOSpaceCap cap
  then   (do
    finaliseCap cap is_final;
    return cap
  od)
  else if isIOPageTableCap cap
  then let ptr = capIOPTBasePtr cap in   (do
    iopteBits \<leftarrow> return ( objBits InvalidIOPTE);
    slots \<leftarrow> return ( [ptr, ptr + bit iopteBits  .e.  ptr + bit ioptBits - 1]);
    mapM_x (flip storeIOPTE InvalidIOPTE) slots;
    finaliseCap cap is_final;
    return cap
  od)
  else if isASIDControlCap cap
  then   return ASIDControlCap
  else if isASIDPoolCap cap
  then let base = capASIDBase cap; ptr = capASIDPool cap in   (do
    asidTable \<leftarrow> gets (x64KSASIDTable \<circ> ksArchState);
    when (asidTable (asidHighBitsOf base) = Just ptr) $ (do
        deleteASIDPool base ptr;
        setObject ptr (makeObject ::asidpool);
        asidTable \<leftarrow> gets (x64KSASIDTable \<circ> ksArchState);
        asidTable' \<leftarrow> return ( asidTable aLU [(asidHighBitsOf base, Just ptr)]);
        modify (\<lambda> s. s \<lparr>
            ksArchState := (ksArchState s) \<lparr> x64KSASIDTable := asidTable' \<rparr>\<rparr>)
    od);
    return cap
  od)
  else undefined
  )"

defs hasRecycleRights_def:
"hasRecycleRights x0\<equiv> (case x0 of
    (PageCap _ rights _ _ _ _) \<Rightarrow>    rights = VMReadWrite
  | _ \<Rightarrow>    True
  )"

defs sameRegionAs_def:
"sameRegionAs x0 x1\<equiv> (let (a,b) = (x0, x1) in
  if isPageCap a \<and> isPageCap b
  then 
    let
        botA = capVPBasePtr a;
        botB = capVPBasePtr b;
        topA = botA + bit (pageBitsForSize $ capVPSize a) - 1;
        topB = botB + bit (pageBitsForSize $ capVPSize b) - 1
    in
    
    (botA \<le> botB) \<and> (topA \<ge> topB) \<and> (botB \<le> topB)
  else if isPageTableCap a \<and> isPageTableCap b
  then  
    capPTBasePtr a = capPTBasePtr b
  else if isPageDirectoryCap a \<and> isPageDirectoryCap b
  then  
    capPDBasePtr a = capPDBasePtr b
  else if isPDPointerTableCap a \<and> isPDPointerTableCap b
  then  
    capPDPTBasePtr a = capPDPTBasePtr b
  else if isPML4Cap a \<and> isPML4Cap b
  then  
    capPML4BasePtr a = capPML4BasePtr b
  else if isASIDControlCap a \<and> isASIDControlCap b
  then   True
  else if isIOPortCap a \<and> isIOPortCap b
  then  
    capASIDPool a = capASIDPool b
  else if isIOSpaceCap a \<and> isIOSpaceCap b
  then   True
  else if isIOPageTableCap a \<and> isIOPageTableCap b
  then  
    capIOPCIDevice a = capIOPCIDevice b
  else  
    capIOPTBasePtr a = capIOPTBasePtr b
  )"

defs isPhysicalCap_def:
"isPhysicalCap x0\<equiv> (case x0 of
    ASIDControlCap \<Rightarrow>    False
  | _ \<Rightarrow>    True
  )"

defs sameObjectAs_def:
"sameObjectAs x0 x1\<equiv> (let (a, b) = (x0, x1) in
  if isPageCap a \<and> isPageCap b
  then let ptrA = capVPBasePtr a
  in  
    (ptrA = capVPBasePtr b) \<and> (capVPSize a = capVPSize b)
        \<and> (ptrA \<le> ptrA + bit (pageBitsForSize $ capVPSize a) - 1)
  else   sameRegionAs a b
  )"

definition
"createPageObject ptr numPages\<equiv> (do
    addrs \<leftarrow> placeNewObject ptr UserData numPages;
    doMachineOp $ initMemory (PPtr $ fromPPtr ptr) (1 `~shiftL~` (pageBits + numPages) );
    return addrs
od)"

defs createObject_def:
"createObject t regionBase arg3 isDevice \<equiv>
    let funupd = (\<lambda> f x v y. if y = x then v else f y) in
    let pointerCast = PPtr \<circ> fromPPtr
    in (let t = t in
        case t of
        APIObjectType _ => 
            haskell_fail []
        | SmallPageObject =>  (do
            createPageObject regionBase 0;
            modify (\<lambda> ks. ks \<lparr> gsUserPages :=
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just X64SmallPage)\<rparr>);
            return $ PageCap (pointerCast regionBase)
                  VMReadWrite VMVSpaceMap X64SmallPage isDevice Nothing
        od)
        | LargePageObject =>  (do
            createPageObject regionBase ptTranslationBits;
            modify (\<lambda> ks. ks \<lparr> gsUserPages :=
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just X64LargePage)\<rparr>);
            return $ PageCap (pointerCast regionBase)
                  VMReadWrite VMVSpaceMap X64LargePage isDevice Nothing
        od)
        | HugePageObject =>  (do
            createPageObject regionBase (ptTranslationBits + ptTranslationBits);
            modify (\<lambda> ks. ks \<lparr> gsUserPages :=
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just X64HugePage)\<rparr>);
            return $ PageCap (pointerCast regionBase)
                  VMReadWrite VMVSpaceMap X64HugePage isDevice Nothing
        od)
        | PageTableObject =>  (do
            ptSize \<leftarrow> return ( ptBits - objBits (makeObject ::pte));
            placeNewObject regionBase (makeObject ::pte) ptSize;
            return $ PageTableCap (pointerCast regionBase) Nothing
        od)
        | PageDirectoryObject =>  (do
            pdSize \<leftarrow> return ( pdBits - objBits (makeObject ::pde));
            placeNewObject regionBase (makeObject ::pde) pdSize;
            return $ PageDirectoryCap (pointerCast regionBase) Nothing
        od)
        | PDPointerTableObject =>  (do
            pdptSize \<leftarrow> return ( pdptBits - objBits (makeObject ::pdpte));
            placeNewObject regionBase (makeObject ::pdpte) pdptSize;
            return $ PDPointerTableCap (pointerCast regionBase) Nothing
        od)
        | PML4Object =>  (do
            pml4Size \<leftarrow> return ( pml4Bits - objBits (makeObject ::pml4e));
            placeNewObject regionBase (makeObject ::pml4e) pml4Size;
            copyGlobalMappings (pointerCast regionBase);
            return $ PML4Cap (pointerCast regionBase) Nothing
        od)
        )"

defs isIOCap_def:
"isIOCap c\<equiv> (case c of
           (IOPortCap _ _) \<Rightarrow>   True
         | (IOSpaceCap _ _) \<Rightarrow>   True
         | _ \<Rightarrow>   False
         )"

defs decodeInvocation_def:
"decodeInvocation label args capIndex slot cap extraCaps \<equiv>
    if isIOCap cap
     then decodeX64PortInvocation label args capIndex slot cap extraCaps
     else decodeX64MMUInvocation label args capIndex slot cap extraCaps"

defs performInvocation_def:
"performInvocation x0\<equiv> (let oper = x0 in
  case oper of
  InvokeIOPort _ =>   performX64PortInvocation oper
  | _ =>   performX64MMUInvocation oper
  )"

defs capUntypedPtr_def:
"capUntypedPtr x0\<equiv> (case x0 of
    (PageCap ((* PPtr *) p) _ _ _ _ _) \<Rightarrow>    PPtr p
  | (PageTableCap ((* PPtr *) p) _) \<Rightarrow>    PPtr p
  | (PageDirectoryCap ((* PPtr *) p) _) \<Rightarrow>    PPtr p
  | (PDPointerTableCap ((* PPtr *) p) _) \<Rightarrow>    PPtr p
  | (PML4Cap ((* PPtr *) p) _) \<Rightarrow>    PPtr p
  | ASIDControlCap \<Rightarrow>    error []
  | (ASIDPoolCap ((* PPtr *) p) _) \<Rightarrow>    PPtr p
  | (IOPortCap _ _) \<Rightarrow>    error []
  | (IOSpaceCap _ _) \<Rightarrow>    error []
  | (IOPageTableCap ((* PPtr *) p) _ _) \<Rightarrow>    PPtr p
  )"

defs capUntypedSize_def:
"capUntypedSize x0\<equiv> (case x0 of
    (PageCap _ _ _ sz _ _) \<Rightarrow>    1 `~shiftL~` pageBitsForSize sz
  | (PageTableCap _ _) \<Rightarrow>    1 `~shiftL~` 12
  | (PageDirectoryCap _ _) \<Rightarrow>    1 `~shiftL~` 12
  | (PDPointerTableCap _ _) \<Rightarrow>    1 `~shiftL~` 12
  | (PML4Cap _ _) \<Rightarrow>    1 `~shiftL~` 12
  | (ASIDControlCap ) \<Rightarrow>    0
  | (ASIDPoolCap _ _) \<Rightarrow>    1 `~shiftL~` (asidLowBits + 3)
  | (IOPortCap _ _) \<Rightarrow>    0
  | (IOSpaceCap _ _) \<Rightarrow>    0
  | (IOPageTableCap _ _ _) \<Rightarrow>    1 `~shiftL~` 12
  )"


end (* context X64 *)
end
