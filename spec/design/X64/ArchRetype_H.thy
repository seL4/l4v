(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchRetype_H.thy *)
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

context Arch begin global_naming X64_H

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
  then   returnOk c
  else if isPML4Cap c \<and> capPML4MappedASID c = None
  then   throw IllegalOperation
  else if isPageCap c
  then   returnOk $ c \<lparr> capVPMappedAddress := Nothing, capVPMapType := VMNoMap \<rparr>
  else if isASIDControlCap c
  then   returnOk c
  else if isASIDPoolCap c
  then   returnOk c
  else if isIOPortCap c
  then   returnOk c
  else undefined
  )"

defs ioPortGetFirstPort_def:
"ioPortGetFirstPort arg1 \<equiv> error []"

defs ioPortGetLastPort_def:
"ioPortGetLastPort arg1 \<equiv> error []"

defs updateCapData_def:
"updateCapData arg1 arg2 c \<equiv> ArchObjectCap c"

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
  | ((PageCap ptr _ _ s _ (Some (a, v))), _) \<Rightarrow>    (do
    unmapPage s a v ptr;
    return NullCap
  od)
  | (_, _) \<Rightarrow>    return NullCap
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
  else if isASIDPoolCap a \<and> isASIDPoolCap b
  then
    capASIDPool a = capASIDPool b
  else if isIOPortCap a \<and> isIOPortCap b
  then
    let
        fA = capIOPortFirstPort a;
        fB = capIOPortFirstPort b;
        lA = capIOPortLastPort a;
        lB = capIOPortLastPort b
    in

    (fA \<le> fB) \<and> (lB \<le> lA) \<and> (fB \<le> lB)
  else   False
  )"

defs isPhysicalCap_def:
"isPhysicalCap x0\<equiv> (case x0 of
    ASIDControlCap \<Rightarrow>    False
  | (IOPortCap _ _) \<Rightarrow>    False
  | _ \<Rightarrow>    True
  )"

defs sameObjectAs_def:
"sameObjectAs x0 x1\<equiv> (let (a, b) = (x0, x1) in
  if isPageCap a \<and> isPageCap b
  then let ptrA = capVPBasePtr a
  in  
    (ptrA = capVPBasePtr b) \<and> (capVPSize a = capVPSize b)
        \<and> (ptrA \<le> ptrA + bit (pageBitsForSize $ capVPSize a) - 1)
        \<and> (capVPIsDevice a = capVPIsDevice b)
  else if isIOPortCap a \<and> isIOPortCap b
  then let fA = capIOPortFirstPort a
  in
    (fA = capIOPortFirstPort b) \<and> (capIOPortLastPort a = capIOPortLastPort b)
        \<and> (fA \<le> capIOPortLastPort a)
  else   sameRegionAs a b
  )"

defs placeNewDataObject_def:
"placeNewDataObject regionBase sz isDevice \<equiv> if isDevice
    then placeNewObject regionBase UserDataDevice sz
    else placeNewObject regionBase UserData sz"

defs createObject_def:
"createObject t regionBase arg3 isDevice \<equiv>
    let funupd = (\<lambda> f x v y. if y = x then v else f y) in
    let pointerCast = PPtr \<circ> fromPPtr
    in (let t = t in
        case t of
        APIObjectType _ => 
            haskell_fail []
        | SmallPageObject =>  (do
            placeNewDataObject regionBase 0 isDevice;
            modify (\<lambda> ks. ks \<lparr> gsUserPages :=
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just X64SmallPage)\<rparr>);
            return $ PageCap (pointerCast regionBase)
                  VMReadWrite VMVSpaceMap X64SmallPage isDevice Nothing
        od)
        | LargePageObject =>  (do
            placeNewDataObject regionBase ptTranslationBits isDevice;
            modify (\<lambda> ks. ks \<lparr> gsUserPages :=
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just X64LargePage)\<rparr>);
            return $ PageCap (pointerCast regionBase)
                  VMReadWrite VMVSpaceMap X64LargePage isDevice Nothing
        od)
        | HugePageObject =>  (do
            placeNewDataObject regionBase (ptTranslationBits + ptTranslationBits) isDevice;
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
         | _ \<Rightarrow>   False
         )"

defs decodeInvocation_def:
"decodeInvocation label args capIndex slot cap extraCaps \<equiv>
    if isIOCap cap
     then decodeX64PortInvocation label args cap
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
  )"

defs prepareThreadDelete_def:
"prepareThreadDelete arg1 \<equiv> return ()"


end (* context X64 *)
end
