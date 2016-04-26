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
context Arch begin global_naming ARM_H

type_synonym asid = "word32"

definition
  ASID :: "asid \<Rightarrow> asid"
where ASID_def[simp]:
 "ASID \<equiv> id"

datatype arch_capability =
    ASIDPoolCap machine_word asid
  | ASIDControlCap
  | PageCap machine_word vmrights vmpage_size "(asid * vptr) option"
  | PageTableCap machine_word "(asid * vptr) option"
  | PageDirectoryCap machine_word "asid option"

primrec
  capVPBasePtr :: "arch_capability \<Rightarrow> machine_word"
where
  "capVPBasePtr (PageCap v0 v1 v2 v3) = v0"

primrec
  capASIDPool :: "arch_capability \<Rightarrow> machine_word"
where
  "capASIDPool (ASIDPoolCap v0 v1) = v0"

primrec
  capPDBasePtr :: "arch_capability \<Rightarrow> machine_word"
where
  "capPDBasePtr (PageDirectoryCap v0 v1) = v0"

primrec
  capVPRights :: "arch_capability \<Rightarrow> vmrights"
where
  "capVPRights (PageCap v0 v1 v2 v3) = v1"

primrec
  capPTMappedAddress :: "arch_capability \<Rightarrow> (asid * vptr) option"
where
  "capPTMappedAddress (PageTableCap v0 v1) = v1"

primrec
  capPDMappedASID :: "arch_capability \<Rightarrow> asid option"
where
  "capPDMappedASID (PageDirectoryCap v0 v1) = v1"

primrec
  capASIDBase :: "arch_capability \<Rightarrow> asid"
where
  "capASIDBase (ASIDPoolCap v0 v1) = v1"

primrec
  capVPSize :: "arch_capability \<Rightarrow> vmpage_size"
where
  "capVPSize (PageCap v0 v1 v2 v3) = v2"

primrec
  capPTBasePtr :: "arch_capability \<Rightarrow> machine_word"
where
  "capPTBasePtr (PageTableCap v0 v1) = v0"

primrec
  capVPMappedAddress :: "arch_capability \<Rightarrow> (asid * vptr) option"
where
  "capVPMappedAddress (PageCap v0 v1 v2 v3) = v3"

primrec
  capVPBasePtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capVPBasePtr_update f (PageCap v0 v1 v2 v3) = PageCap (f v0) v1 v2 v3"

primrec
  capASIDPool_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capASIDPool_update f (ASIDPoolCap v0 v1) = ASIDPoolCap (f v0) v1"

primrec
  capPDBasePtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPDBasePtr_update f (PageDirectoryCap v0 v1) = PageDirectoryCap (f v0) v1"

primrec
  capVPRights_update :: "(vmrights \<Rightarrow> vmrights) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capVPRights_update f (PageCap v0 v1 v2 v3) = PageCap v0 (f v1) v2 v3"

primrec
  capPTMappedAddress_update :: "(((asid * vptr) option) \<Rightarrow> ((asid * vptr) option)) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPTMappedAddress_update f (PageTableCap v0 v1) = PageTableCap v0 (f v1)"

primrec
  capPDMappedASID_update :: "((asid option) \<Rightarrow> (asid option)) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPDMappedASID_update f (PageDirectoryCap v0 v1) = PageDirectoryCap v0 (f v1)"

primrec
  capASIDBase_update :: "(asid \<Rightarrow> asid) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capASIDBase_update f (ASIDPoolCap v0 v1) = ASIDPoolCap v0 (f v1)"

primrec
  capVPSize_update :: "(vmpage_size \<Rightarrow> vmpage_size) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capVPSize_update f (PageCap v0 v1 v2 v3) = PageCap v0 v1 (f v2) v3"

primrec
  capPTBasePtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capPTBasePtr_update f (PageTableCap v0 v1) = PageTableCap (f v0) v1"

primrec
  capVPMappedAddress_update :: "(((asid * vptr) option) \<Rightarrow> ((asid * vptr) option)) \<Rightarrow> arch_capability \<Rightarrow> arch_capability"
where
  "capVPMappedAddress_update f (PageCap v0 v1 v2 v3) = PageCap v0 v1 v2 (f v3)"

abbreviation (input)
  ASIDPoolCap_trans :: "(machine_word) \<Rightarrow> (asid) \<Rightarrow> arch_capability" ("ASIDPoolCap'_ \<lparr> capASIDPool= _, capASIDBase= _ \<rparr>")
where
  "ASIDPoolCap_ \<lparr> capASIDPool= v0, capASIDBase= v1 \<rparr> == ASIDPoolCap v0 v1"

abbreviation (input)
  PageCap_trans :: "(machine_word) \<Rightarrow> (vmrights) \<Rightarrow> (vmpage_size) \<Rightarrow> ((asid * vptr) option) \<Rightarrow> arch_capability" ("PageCap'_ \<lparr> capVPBasePtr= _, capVPRights= _, capVPSize= _, capVPMappedAddress= _ \<rparr>")
where
  "PageCap_ \<lparr> capVPBasePtr= v0, capVPRights= v1, capVPSize= v2, capVPMappedAddress= v3 \<rparr> == PageCap v0 v1 v2 v3"

abbreviation (input)
  PageTableCap_trans :: "(machine_word) \<Rightarrow> ((asid * vptr) option) \<Rightarrow> arch_capability" ("PageTableCap'_ \<lparr> capPTBasePtr= _, capPTMappedAddress= _ \<rparr>")
where
  "PageTableCap_ \<lparr> capPTBasePtr= v0, capPTMappedAddress= v1 \<rparr> == PageTableCap v0 v1"

abbreviation (input)
  PageDirectoryCap_trans :: "(machine_word) \<Rightarrow> (asid option) \<Rightarrow> arch_capability" ("PageDirectoryCap'_ \<lparr> capPDBasePtr= _, capPDMappedASID= _ \<rparr>")
where
  "PageDirectoryCap_ \<lparr> capPDBasePtr= v0, capPDMappedASID= v1 \<rparr> == PageDirectoryCap v0 v1"

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
  isPageCap :: "arch_capability \<Rightarrow> bool"
where
 "isPageCap v \<equiv> case v of
    PageCap v0 v1 v2 v3 \<Rightarrow> True
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

datatype asidpool =
    ASIDPool "asid \<Rightarrow> ((machine_word) option)"

datatype arch_kernel_object =
    KOASIDPool asidpool
  | KOPTE pte
  | KOPDE pde

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
                  KOASIDPool v10 \<Rightarrow>   pageBits
                | KOPTE v11 \<Rightarrow>   2
                | KOPDE v12 \<Rightarrow>   2
                )"

defs asidHighBits_def:
"asidHighBits \<equiv> 8"

defs asidLowBits_def:
"asidLowBits \<equiv> 10"

defs asidBits_def:
"asidBits \<equiv> asidHighBits + asidLowBits"

defs asidRange_def:
"asidRange\<equiv> (0, (1 `~shiftL~` asidBits) - 1)"

defs asidHighBitsOf_def:
"asidHighBitsOf asid\<equiv> (asid `~shiftR~` asidLowBits) && mask asidHighBits"


datatype arch_kernel_object_type =
    PDET
  | PTET
  | ASIDPoolT

primrec
  archTypeOf :: "arch_kernel_object \<Rightarrow> arch_kernel_object_type"
where
  "archTypeOf (KOPDE e) = PDET"
| "archTypeOf (KOPTE e) = PTET"
| "archTypeOf (KOASIDPool e) = ASIDPoolT"

end
end
