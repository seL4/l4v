(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchStructures_H
imports
  "../../../lib/Lib"
  "../Types_H"
  Hardware_H
begin

context X64 begin

type_synonym ioasid = "word16"

definition
  IOASID :: "ioasid \<Rightarrow> ioasid"
where IOASID_def[simp]:
 "IOASID \<equiv> id"

type_synonym asid = "word64"

definition
  ASID :: "asid \<Rightarrow> asid"
where ASID_def[simp]:
 "ASID \<equiv> id"

datatype arch_capability =
    ASIDPoolCap machine_word asid
  | ASIDControlCap
  | IOPortCap ioport ioport
  | IOSpaceCap word16 "ioasid option"
  | IOPageTableCap machine_word nat "(ioasid * vptr) option"
  | PageCap machine_word vmrights vmmap_type vmpage_size bool "(asid * vptr) option"
  | PageTableCap machine_word "(asid * vptr) option"
  | PageDirectoryCap machine_word "(asid * vptr) option"
  | PDPointerTableCap machine_word "(asid * vptr) option"
  | PML4Cap machine_word "asid option"

primrec
  capVPIsDevice :: "arch_capability \<Rightarrow> bool"
where
  "capVPIsDevice (PageCap v0 v1 v2 v3 v4 v5) = v4"

primrec
  capVPRights :: "arch_capability \<Rightarrow> vmrights"
where
  "capVPRights (PageCap v0 v1 v2 v3 v4 v5) = v1"

primrec
  capPTMappedAddress :: "arch_capability \<Rightarrow> (asid * vptr) option"
where
  "capPTMappedAddress (PageTableCap v0 v1) = v1"

primrec
  capIODomainID :: "arch_capability \<Rightarrow> word16"
where
  "capIODomainID (IOSpaceCap v0 v1) = v0"

primrec
  capPTBasePtr :: "arch_capability \<Rightarrow> machine_word"
where
  "capPTBasePtr (PageTableCap v0 v1) = v0"

primrec
  capVPMapType :: "arch_capability \<Rightarrow> vmmap_type"
where
  "capVPMapType (PageCap v0 v1 v2 v3 v4 v5) = v2"

primrec
  capVPBasePtr :: "arch_capability \<Rightarrow> machine_word"
where
  "capVPBasePtr (PageCap v0 v1 v2 v3 v4 v5) = v0"

primrec
  capASIDPool :: "arch_capability \<Rightarrow> machine_word"
where
  "capASIDPool (ASIDPoolCap v0 v1) = v0"

primrec
  capIOPTBasePtr :: "arch_capability \<Rightarrow> machine_word"
where
  "capIOPTBasePtr (IOPageTableCap v0 v1 v2) = v0"

primrec
  capPML4MappedASID :: "arch_capability \<Rightarrow> asid option"
where
  "capPML4MappedASID (PML4Cap v0 v1) = v1"

primrec
  capPDBasePtr :: "arch_capability \<Rightarrow> machine_word"
where
  "capPDBasePtr (PageDirectoryCap v0 v1) = v0"

primrec
  capPML4BasePtr :: "arch_capability \<Rightarrow> machine_word"
where
  "capPML4BasePtr (PML4Cap v0 v1) = v0"

primrec
  capASIDBase :: "arch_capability \<Rightarrow> asid"
where
  "capASIDBase (ASIDPoolCap v0 v1) = v1"

primrec
  capPDPTBasePtr :: "arch_capability \<Rightarrow> machine_word"
where
  "capPDPTBasePtr (PDPointerTableCap v0 v1) = v0"

primrec
  capIOPTMappedAddress :: "arch_capability \<Rightarrow> (ioasid * vptr) option"
where
  "capIOPTMappedAddress (IOPageTableCap v0 v1 v2) = v2"

primrec
  capIOPCIDevice :: "arch_capability \<Rightarrow> ioasid option"
where
  "capIOPCIDevice (IOSpaceCap v0 v1) = v1"

primrec
  capIOPTLevel :: "arch_capability \<Rightarrow> nat"
where
  "capIOPTLevel (IOPageTableCap v0 v1 v2) = v1"

primrec
  capVPSize :: "arch_capability \<Rightarrow> vmpage_size"
where
  "capVPSize (PageCap v0 v1 v2 v3 v4 v5) = v3"

primrec
  capIOPortFirstPort :: "arch_capability \<Rightarrow> ioport"
where
  "capIOPortFirstPort (IOPortCap v0 v1) = v0"

primrec
  capPDPTMappedAddress :: "arch_capability \<Rightarrow> (asid * vptr) option"
where
  "capPDPTMappedAddress (PDPointerTableCap v0 v1) = v1"

primrec
  capIOPortLastPort :: "arch_capability \<Rightarrow> ioport"
where
  "capIOPortLastPort (IOPortCap v0 v1) = v1"

primrec
  capPDMappedAddress :: "arch_capability \<Rightarrow> (asid * vptr) option"
where
  "capPDMappedAddress (PageDirectoryCap v0 v1) = v1"

primrec
  capVPMappedAddress :: "arch_capability \<Rightarrow> (asid * vptr) option"
where
  "capVPMappedAddress (PageCap v0 v1 v2 v3 v4 v5) = v5"

primrec
  capVPIsDevice_update :: "(bool \<Rightarrow> bool) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capVPIsDevice_update f (PageCap v0 v1 v2 v3 v4 v5) = PageCap v0 v1 v2 v3 (f v4) v5"

primrec
  capVPRights_update :: "(vmrights \<Rightarrow> vmrights) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capVPRights_update f (PageCap v0 v1 v2 v3 v4 v5) = PageCap v0 (f v1) v2 v3 v4 v5"

primrec
  capPTMappedAddress_update :: "(((asid * vptr) option) \<Rightarrow> ((asid * vptr) option)) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPTMappedAddress_update f (PageTableCap v0 v1) = PageTableCap v0 (f v1)"

primrec
  capIODomainID_update :: "(word16 \<Rightarrow> word16) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capIODomainID_update f (IOSpaceCap v0 v1) = IOSpaceCap (f v0) v1"

primrec
  capPTBasePtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPTBasePtr_update f (PageTableCap v0 v1) = PageTableCap (f v0) v1"

primrec
  capVPMapType_update :: "(vmmap_type \<Rightarrow> vmmap_type) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capVPMapType_update f (PageCap v0 v1 v2 v3 v4 v5) = PageCap v0 v1 (f v2) v3 v4 v5"

primrec
  capVPBasePtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capVPBasePtr_update f (PageCap v0 v1 v2 v3 v4 v5) = PageCap (f v0) v1 v2 v3 v4 v5"

primrec
  capASIDPool_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capASIDPool_update f (ASIDPoolCap v0 v1) = ASIDPoolCap (f v0) v1"

primrec
  capIOPTBasePtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capIOPTBasePtr_update f (IOPageTableCap v0 v1 v2) = IOPageTableCap (f v0) v1 v2"

primrec
  capPML4MappedASID_update :: "((asid option) \<Rightarrow> (asid option)) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPML4MappedASID_update f (PML4Cap v0 v1) = PML4Cap v0 (f v1)"

primrec
  capPDBasePtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPDBasePtr_update f (PageDirectoryCap v0 v1) = PageDirectoryCap (f v0) v1"

primrec
  capPML4BasePtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPML4BasePtr_update f (PML4Cap v0 v1) = PML4Cap (f v0) v1"

primrec
  capASIDBase_update :: "(asid \<Rightarrow> asid) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capASIDBase_update f (ASIDPoolCap v0 v1) = ASIDPoolCap v0 (f v1)"

primrec
  capPDPTBasePtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPDPTBasePtr_update f (PDPointerTableCap v0 v1) = PDPointerTableCap (f v0) v1"

primrec
  capIOPTMappedAddress_update :: "(((ioasid * vptr) option) \<Rightarrow> ((ioasid * vptr) option)) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capIOPTMappedAddress_update f (IOPageTableCap v0 v1 v2) = IOPageTableCap v0 v1 (f v2)"

primrec
  capIOPCIDevice_update :: "((ioasid option) \<Rightarrow> (ioasid option)) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capIOPCIDevice_update f (IOSpaceCap v0 v1) = IOSpaceCap v0 (f v1)"

primrec
  capIOPTLevel_update :: "(nat \<Rightarrow> nat) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capIOPTLevel_update f (IOPageTableCap v0 v1 v2) = IOPageTableCap v0 (f v1) v2"

primrec
  capVPSize_update :: "(vmpage_size \<Rightarrow> vmpage_size) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capVPSize_update f (PageCap v0 v1 v2 v3 v4 v5) = PageCap v0 v1 v2 (f v3) v4 v5"

primrec
  capIOPortFirstPort_update :: "(ioport \<Rightarrow> ioport) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capIOPortFirstPort_update f (IOPortCap v0 v1) = IOPortCap (f v0) v1"

primrec
  capPDPTMappedAddress_update :: "(((asid * vptr) option) \<Rightarrow> ((asid * vptr) option)) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPDPTMappedAddress_update f (PDPointerTableCap v0 v1) = PDPointerTableCap v0 (f v1)"

primrec
  capIOPortLastPort_update :: "(ioport \<Rightarrow> ioport) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capIOPortLastPort_update f (IOPortCap v0 v1) = IOPortCap v0 (f v1)"

primrec
  capPDMappedAddress_update :: "(((asid * vptr) option) \<Rightarrow> ((asid * vptr) option)) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPDMappedAddress_update f (PageDirectoryCap v0 v1) = PageDirectoryCap v0 (f v1)"

primrec
  capVPMappedAddress_update :: "(((asid * vptr) option) \<Rightarrow> ((asid * vptr) option)) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capVPMappedAddress_update f (PageCap v0 v1 v2 v3 v4 v5) = PageCap v0 v1 v2 v3 v4 (f v5)"

abbreviation (input)
  ASIDPoolCap_trans :: "(machine_word) \<Rightarrow> (asid) \<Rightarrow> arch_capability" ("ASIDPoolCap'_ \<lparr> capASIDPool= _, capASIDBase= _ \<rparr>")
where
  "ASIDPoolCap_ \<lparr> capASIDPool= v0, capASIDBase= v1 \<rparr> == ASIDPoolCap v0 v1"

abbreviation (input)
  IOPortCap_trans :: "(ioport) \<Rightarrow> (ioport) \<Rightarrow> arch_capability" ("IOPortCap'_ \<lparr> capIOPortFirstPort= _, capIOPortLastPort= _ \<rparr>")
where
  "IOPortCap_ \<lparr> capIOPortFirstPort= v0, capIOPortLastPort= v1 \<rparr> == IOPortCap v0 v1"

abbreviation (input)
  IOSpaceCap_trans :: "(word16) \<Rightarrow> (ioasid option) \<Rightarrow> arch_capability" ("IOSpaceCap'_ \<lparr> capIODomainID= _, capIOPCIDevice= _ \<rparr>")
where
  "IOSpaceCap_ \<lparr> capIODomainID= v0, capIOPCIDevice= v1 \<rparr> == IOSpaceCap v0 v1"

abbreviation (input)
  IOPageTableCap_trans :: "(machine_word) \<Rightarrow> (nat) \<Rightarrow> ((ioasid * vptr) option) \<Rightarrow> arch_capability" ("IOPageTableCap'_ \<lparr> capIOPTBasePtr= _, capIOPTLevel= _, capIOPTMappedAddress= _ \<rparr>")
where
  "IOPageTableCap_ \<lparr> capIOPTBasePtr= v0, capIOPTLevel= v1, capIOPTMappedAddress= v2 \<rparr> == IOPageTableCap v0 v1 v2"

abbreviation (input)
  PageCap_trans :: "(machine_word) \<Rightarrow> (vmrights) \<Rightarrow> (vmmap_type) \<Rightarrow> (vmpage_size) \<Rightarrow> (bool) \<Rightarrow> ((asid * vptr) option) \<Rightarrow> arch_capability" ("PageCap'_ \<lparr> capVPBasePtr= _, capVPRights= _, capVPMapType= _, capVPSize= _, capVPIsDevice= _, capVPMappedAddress= _ \<rparr>")
where
  "PageCap_ \<lparr> capVPBasePtr= v0, capVPRights= v1, capVPMapType= v2, capVPSize= v3, capVPIsDevice= v4, capVPMappedAddress= v5 \<rparr> == PageCap v0 v1 v2 v3 v4 v5"

abbreviation (input)
  PageTableCap_trans :: "(machine_word) \<Rightarrow> ((asid * vptr) option) \<Rightarrow> arch_capability" ("PageTableCap'_ \<lparr> capPTBasePtr= _, capPTMappedAddress= _ \<rparr>")
where
  "PageTableCap_ \<lparr> capPTBasePtr= v0, capPTMappedAddress= v1 \<rparr> == PageTableCap v0 v1"

abbreviation (input)
  PageDirectoryCap_trans :: "(machine_word) \<Rightarrow> ((asid * vptr) option) \<Rightarrow> arch_capability" ("PageDirectoryCap'_ \<lparr> capPDBasePtr= _, capPDMappedAddress= _ \<rparr>")
where
  "PageDirectoryCap_ \<lparr> capPDBasePtr= v0, capPDMappedAddress= v1 \<rparr> == PageDirectoryCap v0 v1"

abbreviation (input)
  PDPointerTableCap_trans :: "(machine_word) \<Rightarrow> ((asid * vptr) option) \<Rightarrow> arch_capability" ("PDPointerTableCap'_ \<lparr> capPDPTBasePtr= _, capPDPTMappedAddress= _ \<rparr>")
where
  "PDPointerTableCap_ \<lparr> capPDPTBasePtr= v0, capPDPTMappedAddress= v1 \<rparr> == PDPointerTableCap v0 v1"

abbreviation (input)
  PML4Cap_trans :: "(machine_word) \<Rightarrow> (asid option) \<Rightarrow> arch_capability" ("PML4Cap'_ \<lparr> capPML4BasePtr= _, capPML4MappedASID= _ \<rparr>")
where
  "PML4Cap_ \<lparr> capPML4BasePtr= v0, capPML4MappedASID= v1 \<rparr> == PML4Cap v0 v1"

definition
  isASIDPoolCap :: "arch_capability \<Rightarrow> bool"
where
 "isASIDPoolCap v \<equiv> case v of
    ASIDPoolCap v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isASIDControlCap :: "arch_capability \<Rightarrow> bool"
where
 "isASIDControlCap v \<equiv> case v of
    ASIDControlCap \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isIOPortCap :: "arch_capability \<Rightarrow> bool"
where
 "isIOPortCap v \<equiv> case v of
    IOPortCap v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isIOSpaceCap :: "arch_capability \<Rightarrow> bool"
where
 "isIOSpaceCap v \<equiv> case v of
    IOSpaceCap v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isIOPageTableCap :: "arch_capability \<Rightarrow> bool"
where
 "isIOPageTableCap v \<equiv> case v of
    IOPageTableCap v0 v1 v2 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPageCap :: "arch_capability \<Rightarrow> bool"
where
 "isPageCap v \<equiv> case v of
    PageCap v0 v1 v2 v3 v4 v5 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPageTableCap :: "arch_capability \<Rightarrow> bool"
where
 "isPageTableCap v \<equiv> case v of
    PageTableCap v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPageDirectoryCap :: "arch_capability \<Rightarrow> bool"
where
 "isPageDirectoryCap v \<equiv> case v of
    PageDirectoryCap v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPDPointerTableCap :: "arch_capability \<Rightarrow> bool"
where
 "isPDPointerTableCap v \<equiv> case v of
    PDPointerTableCap v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPML4Cap :: "arch_capability \<Rightarrow> bool"
where
 "isPML4Cap v \<equiv> case v of
    PML4Cap v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype asidpool =
    ASIDPool "asid \<Rightarrow> ((machine_word) option)"

datatype arch_kernel_object =
    KOASIDPool asidpool
  | KOPTE pte
  | KOPDE pde
  | KOPDPTE pdpte
  | KOPML4E pml4e
  | KOIOPTE iopte
  | KOIORTE iorte
  | KOIOCTE iocte

consts'
archObjSize :: "arch_kernel_object \<Rightarrow> nat"

consts'
asidHighBits :: "nat"

consts'
asidLowBits :: "nat"

consts'
asidBits :: "nat"

consts'
asidRange :: "(asid * asid)"

consts'
asidHighBitsOf :: "asid \<Rightarrow> asid"

defs archObjSize_def:
"archObjSize a\<equiv> (case a of
                  KOASIDPool v25 \<Rightarrow>   pageBits
                | KOPTE v26 \<Rightarrow>   3
                | KOPDE v27 \<Rightarrow>   3
                | KOPDPTE v28 \<Rightarrow>   3
                | KOPML4E v29 \<Rightarrow>   3
                | KOIOPTE v30 \<Rightarrow>   3
                | KOIOCTE v31 \<Rightarrow>   3
                | KOIORTE v32 \<Rightarrow>   3
                )"

defs asidHighBits_def:
"asidHighBits \<equiv> 3"

defs asidLowBits_def:
"asidLowBits \<equiv> 9"

defs asidBits_def:
"asidBits \<equiv> asidHighBits + asidLowBits"

defs asidRange_def:
"asidRange\<equiv> (0, (1 `~shiftL~` asidBits) - 1)"

defs asidHighBitsOf_def:
"asidHighBitsOf asid\<equiv> (asid `~shiftR~` asidLowBits) && mask asidHighBits"


datatype arch_kernel_object_type =
    PDET
  | PTET
  | PDPTET
  | PML4ET
  | ASIDPoolT
  | IOPTET

primrec
  archTypeOf :: "arch_kernel_object \<Rightarrow> arch_kernel_object_type"
where
  "archTypeOf (KOPDE e) = PDET"
| "archTypeOf (KOPTE e) = PTET"
| "archTypeOf (KOPDPTE e) = PDPTET"
| "archTypeOf (KOPML4E e) = PML4ET"
| "archTypeOf (KOASIDPool e) = ASIDPoolT"
| "archTypeOf (KOIOPTE e) = IOPTET"


end (* context X64 *)

end
