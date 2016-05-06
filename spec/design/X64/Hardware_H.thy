(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Hardware_H
imports
  "../../machine/X64/MachineOps"
  State_H
begin


context X64 begin

type_synonym irq = "Platform.irq"

type_synonym cr3 = "Platform.cr3"

type_synonym ioport = "word16"

type_synonym paddr = "Platform.paddr"

datatype vmrights =
    VMKernelOnly
  | VMReadOnly
  | VMReadWrite
  | VMWriteOnly

datatype pml4e =
    InvalidPML4E
  | PDPointerTablePML4E paddr bool bool bool bool vmrights

primrec
  pml4eWriteThrough :: "pml4e \<Rightarrow> bool"
where
  "pml4eWriteThrough (PDPointerTablePML4E v0 v1 v2 v3 v4 v5) = v3"

primrec
  pml4eTable :: "pml4e \<Rightarrow> paddr"
where
  "pml4eTable (PDPointerTablePML4E v0 v1 v2 v3 v4 v5) = v0"

primrec
  pml4eExecuteDisable :: "pml4e \<Rightarrow> bool"
where
  "pml4eExecuteDisable (PDPointerTablePML4E v0 v1 v2 v3 v4 v5) = v4"

primrec
  pml4eCacheDisabled :: "pml4e \<Rightarrow> bool"
where
  "pml4eCacheDisabled (PDPointerTablePML4E v0 v1 v2 v3 v4 v5) = v2"

primrec
  pml4eAccessed :: "pml4e \<Rightarrow> bool"
where
  "pml4eAccessed (PDPointerTablePML4E v0 v1 v2 v3 v4 v5) = v1"

primrec
  pml4eRights :: "pml4e \<Rightarrow> vmrights"
where
  "pml4eRights (PDPointerTablePML4E v0 v1 v2 v3 v4 v5) = v5"

primrec
  pml4eWriteThrough_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pml4e \<Rightarrow> pml4e"
where
  "pml4eWriteThrough_update f (PDPointerTablePML4E v0 v1 v2 v3 v4 v5) = PDPointerTablePML4E v0 v1 v2 (f v3) v4 v5"

primrec
  pml4eTable_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> pml4e \<Rightarrow> pml4e"
where
  "pml4eTable_update f (PDPointerTablePML4E v0 v1 v2 v3 v4 v5) = PDPointerTablePML4E (f v0) v1 v2 v3 v4 v5"

primrec
  pml4eExecuteDisable_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pml4e \<Rightarrow> pml4e"
where
  "pml4eExecuteDisable_update f (PDPointerTablePML4E v0 v1 v2 v3 v4 v5) = PDPointerTablePML4E v0 v1 v2 v3 (f v4) v5"

primrec
  pml4eCacheDisabled_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pml4e \<Rightarrow> pml4e"
where
  "pml4eCacheDisabled_update f (PDPointerTablePML4E v0 v1 v2 v3 v4 v5) = PDPointerTablePML4E v0 v1 (f v2) v3 v4 v5"

primrec
  pml4eAccessed_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pml4e \<Rightarrow> pml4e"
where
  "pml4eAccessed_update f (PDPointerTablePML4E v0 v1 v2 v3 v4 v5) = PDPointerTablePML4E v0 (f v1) v2 v3 v4 v5"

primrec
  pml4eRights_update :: "(vmrights \<Rightarrow> vmrights) \<Rightarrow> pml4e \<Rightarrow> pml4e"
where
  "pml4eRights_update f (PDPointerTablePML4E v0 v1 v2 v3 v4 v5) = PDPointerTablePML4E v0 v1 v2 v3 v4 (f v5)"

abbreviation (input)
  PDPointerTablePML4E_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pml4e" ("PDPointerTablePML4E'_ \<lparr> pml4eTable= _, pml4eAccessed= _, pml4eCacheDisabled= _, pml4eWriteThrough= _, pml4eExecuteDisable= _, pml4eRights= _ \<rparr>")
where
  "PDPointerTablePML4E_ \<lparr> pml4eTable= v0, pml4eAccessed= v1, pml4eCacheDisabled= v2, pml4eWriteThrough= v3, pml4eExecuteDisable= v4, pml4eRights= v5 \<rparr> == PDPointerTablePML4E v0 v1 v2 v3 v4 v5"

definition
  isInvalidPML4E :: "pml4e \<Rightarrow> bool"
where
 "isInvalidPML4E v \<equiv> case v of
    InvalidPML4E \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPDPointerTablePML4E :: "pml4e \<Rightarrow> bool"
where
 "isPDPointerTablePML4E v \<equiv> case v of
    PDPointerTablePML4E v0 v1 v2 v3 v4 v5 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype pdpte =
    InvalidPDPTE
  | PageDirectoryPDPTE paddr bool bool bool bool vmrights
  | HugePagePDPTE paddr bool bool bool bool bool bool bool vmrights

primrec
  pdpteAccessed :: "pdpte \<Rightarrow> bool"
where
  "pdpteAccessed (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v4"
| "pdpteAccessed (PageDirectoryPDPTE v0 v1 v2 v3 v4 v5) = v1"

primrec
  pdpteGlobal :: "pdpte \<Rightarrow> bool"
where
  "pdpteGlobal (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v1"

primrec
  pdpteWriteThrough :: "pdpte \<Rightarrow> bool"
where
  "pdpteWriteThrough (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v6"
| "pdpteWriteThrough (PageDirectoryPDPTE v0 v1 v2 v3 v4 v5) = v3"

primrec
  pdpteExecuteDisable :: "pdpte \<Rightarrow> bool"
where
  "pdpteExecuteDisable (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v7"
| "pdpteExecuteDisable (PageDirectoryPDPTE v0 v1 v2 v3 v4 v5) = v4"

primrec
  pdpteTable :: "pdpte \<Rightarrow> paddr"
where
  "pdpteTable (PageDirectoryPDPTE v0 v1 v2 v3 v4 v5) = v0"

primrec
  pdpteCacheDisabled :: "pdpte \<Rightarrow> bool"
where
  "pdpteCacheDisabled (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v5"
| "pdpteCacheDisabled (PageDirectoryPDPTE v0 v1 v2 v3 v4 v5) = v2"

primrec
  pdpteFrame :: "pdpte \<Rightarrow> paddr"
where
  "pdpteFrame (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v0"

primrec
  pdpteRights :: "pdpte \<Rightarrow> vmrights"
where
  "pdpteRights (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v8"
| "pdpteRights (PageDirectoryPDPTE v0 v1 v2 v3 v4 v5) = v5"

primrec
  pdptePAT :: "pdpte \<Rightarrow> bool"
where
  "pdptePAT (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v2"

primrec
  pdpteDirty :: "pdpte \<Rightarrow> bool"
where
  "pdpteDirty (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v3"

primrec
  pdpteAccessed_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pdpte \<Rightarrow> pdpte"
where
  "pdpteAccessed_update f (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = HugePagePDPTE v0 v1 v2 v3 (f v4) v5 v6 v7 v8"
| "pdpteAccessed_update f (PageDirectoryPDPTE v0 v1 v2 v3 v4 v5) = PageDirectoryPDPTE v0 (f v1) v2 v3 v4 v5"

primrec
  pdpteGlobal_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pdpte \<Rightarrow> pdpte"
where
  "pdpteGlobal_update f (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = HugePagePDPTE v0 (f v1) v2 v3 v4 v5 v6 v7 v8"

primrec
  pdpteWriteThrough_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pdpte \<Rightarrow> pdpte"
where
  "pdpteWriteThrough_update f (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = HugePagePDPTE v0 v1 v2 v3 v4 v5 (f v6) v7 v8"
| "pdpteWriteThrough_update f (PageDirectoryPDPTE v0 v1 v2 v3 v4 v5) = PageDirectoryPDPTE v0 v1 v2 (f v3) v4 v5"

primrec
  pdpteExecuteDisable_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pdpte \<Rightarrow> pdpte"
where
  "pdpteExecuteDisable_update f (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 (f v7) v8"
| "pdpteExecuteDisable_update f (PageDirectoryPDPTE v0 v1 v2 v3 v4 v5) = PageDirectoryPDPTE v0 v1 v2 v3 (f v4) v5"

primrec
  pdpteTable_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> pdpte \<Rightarrow> pdpte"
where
  "pdpteTable_update f (PageDirectoryPDPTE v0 v1 v2 v3 v4 v5) = PageDirectoryPDPTE (f v0) v1 v2 v3 v4 v5"

primrec
  pdpteCacheDisabled_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pdpte \<Rightarrow> pdpte"
where
  "pdpteCacheDisabled_update f (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = HugePagePDPTE v0 v1 v2 v3 v4 (f v5) v6 v7 v8"
| "pdpteCacheDisabled_update f (PageDirectoryPDPTE v0 v1 v2 v3 v4 v5) = PageDirectoryPDPTE v0 v1 (f v2) v3 v4 v5"

primrec
  pdpteFrame_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> pdpte \<Rightarrow> pdpte"
where
  "pdpteFrame_update f (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = HugePagePDPTE (f v0) v1 v2 v3 v4 v5 v6 v7 v8"

primrec
  pdpteRights_update :: "(vmrights \<Rightarrow> vmrights) \<Rightarrow> pdpte \<Rightarrow> pdpte"
where
  "pdpteRights_update f (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 (f v8)"
| "pdpteRights_update f (PageDirectoryPDPTE v0 v1 v2 v3 v4 v5) = PageDirectoryPDPTE v0 v1 v2 v3 v4 (f v5)"

primrec
  pdptePAT_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pdpte \<Rightarrow> pdpte"
where
  "pdptePAT_update f (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = HugePagePDPTE v0 v1 (f v2) v3 v4 v5 v6 v7 v8"

primrec
  pdpteDirty_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pdpte \<Rightarrow> pdpte"
where
  "pdpteDirty_update f (HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = HugePagePDPTE v0 v1 v2 (f v3) v4 v5 v6 v7 v8"

abbreviation (input)
  PageDirectoryPDPTE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pdpte" ("PageDirectoryPDPTE'_ \<lparr> pdpteTable= _, pdpteAccessed= _, pdpteCacheDisabled= _, pdpteWriteThrough= _, pdpteExecuteDisable= _, pdpteRights= _ \<rparr>")
where
  "PageDirectoryPDPTE_ \<lparr> pdpteTable= v0, pdpteAccessed= v1, pdpteCacheDisabled= v2, pdpteWriteThrough= v3, pdpteExecuteDisable= v4, pdpteRights= v5 \<rparr> == PageDirectoryPDPTE v0 v1 v2 v3 v4 v5"

abbreviation (input)
  HugePagePDPTE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pdpte" ("HugePagePDPTE'_ \<lparr> pdpteFrame= _, pdpteGlobal= _, pdptePAT= _, pdpteDirty= _, pdpteAccessed= _, pdpteCacheDisabled= _, pdpteWriteThrough= _, pdpteExecuteDisable= _, pdpteRights= _ \<rparr>")
where
  "HugePagePDPTE_ \<lparr> pdpteFrame= v0, pdpteGlobal= v1, pdptePAT= v2, pdpteDirty= v3, pdpteAccessed= v4, pdpteCacheDisabled= v5, pdpteWriteThrough= v6, pdpteExecuteDisable= v7, pdpteRights= v8 \<rparr> == HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8"

definition
  isInvalidPDPTE :: "pdpte \<Rightarrow> bool"
where
 "isInvalidPDPTE v \<equiv> case v of
    InvalidPDPTE \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPageDirectoryPDPTE :: "pdpte \<Rightarrow> bool"
where
 "isPageDirectoryPDPTE v \<equiv> case v of
    PageDirectoryPDPTE v0 v1 v2 v3 v4 v5 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isHugePagePDPTE :: "pdpte \<Rightarrow> bool"
where
 "isHugePagePDPTE v \<equiv> case v of
    HugePagePDPTE v0 v1 v2 v3 v4 v5 v6 v7 v8 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype pde =
    InvalidPDE
  | PageTablePDE paddr bool bool bool bool vmrights
  | LargePagePDE paddr bool bool bool bool bool bool bool vmrights

primrec
  pdePAT :: "pde \<Rightarrow> bool"
where
  "pdePAT (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v2"

primrec
  pdeExecuteDisable :: "pde \<Rightarrow> bool"
where
  "pdeExecuteDisable (PageTablePDE v0 v1 v2 v3 v4 v5) = v4"
| "pdeExecuteDisable (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v7"

primrec
  pdeRights :: "pde \<Rightarrow> vmrights"
where
  "pdeRights (PageTablePDE v0 v1 v2 v3 v4 v5) = v5"
| "pdeRights (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v8"

primrec
  pdeTable :: "pde \<Rightarrow> paddr"
where
  "pdeTable (PageTablePDE v0 v1 v2 v3 v4 v5) = v0"

primrec
  pdeFrame :: "pde \<Rightarrow> paddr"
where
  "pdeFrame (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v0"

primrec
  pdeAccessed :: "pde \<Rightarrow> bool"
where
  "pdeAccessed (PageTablePDE v0 v1 v2 v3 v4 v5) = v1"
| "pdeAccessed (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v4"

primrec
  pdeCacheDisabled :: "pde \<Rightarrow> bool"
where
  "pdeCacheDisabled (PageTablePDE v0 v1 v2 v3 v4 v5) = v2"
| "pdeCacheDisabled (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v5"

primrec
  pdeGlobal :: "pde \<Rightarrow> bool"
where
  "pdeGlobal (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v1"

primrec
  pdeWriteThrough :: "pde \<Rightarrow> bool"
where
  "pdeWriteThrough (PageTablePDE v0 v1 v2 v3 v4 v5) = v3"
| "pdeWriteThrough (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v6"

primrec
  pdeDirty :: "pde \<Rightarrow> bool"
where
  "pdeDirty (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v3"

primrec
  pdePAT_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdePAT_update f (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = LargePagePDE v0 v1 (f v2) v3 v4 v5 v6 v7 v8"

primrec
  pdeExecuteDisable_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeExecuteDisable_update f (PageTablePDE v0 v1 v2 v3 v4 v5) = PageTablePDE v0 v1 v2 v3 (f v4) v5"
| "pdeExecuteDisable_update f (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = LargePagePDE v0 v1 v2 v3 v4 v5 v6 (f v7) v8"

primrec
  pdeRights_update :: "(vmrights \<Rightarrow> vmrights) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeRights_update f (PageTablePDE v0 v1 v2 v3 v4 v5) = PageTablePDE v0 v1 v2 v3 v4 (f v5)"
| "pdeRights_update f (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 (f v8)"

primrec
  pdeTable_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeTable_update f (PageTablePDE v0 v1 v2 v3 v4 v5) = PageTablePDE (f v0) v1 v2 v3 v4 v5"

primrec
  pdeFrame_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeFrame_update f (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = LargePagePDE (f v0) v1 v2 v3 v4 v5 v6 v7 v8"

primrec
  pdeAccessed_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeAccessed_update f (PageTablePDE v0 v1 v2 v3 v4 v5) = PageTablePDE v0 (f v1) v2 v3 v4 v5"
| "pdeAccessed_update f (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = LargePagePDE v0 v1 v2 v3 (f v4) v5 v6 v7 v8"

primrec
  pdeCacheDisabled_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeCacheDisabled_update f (PageTablePDE v0 v1 v2 v3 v4 v5) = PageTablePDE v0 v1 (f v2) v3 v4 v5"
| "pdeCacheDisabled_update f (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = LargePagePDE v0 v1 v2 v3 v4 (f v5) v6 v7 v8"

primrec
  pdeGlobal_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeGlobal_update f (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = LargePagePDE v0 (f v1) v2 v3 v4 v5 v6 v7 v8"

primrec
  pdeWriteThrough_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeWriteThrough_update f (PageTablePDE v0 v1 v2 v3 v4 v5) = PageTablePDE v0 v1 v2 (f v3) v4 v5"
| "pdeWriteThrough_update f (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = LargePagePDE v0 v1 v2 v3 v4 v5 (f v6) v7 v8"

primrec
  pdeDirty_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeDirty_update f (LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8) = LargePagePDE v0 v1 v2 (f v3) v4 v5 v6 v7 v8"

abbreviation (input)
  PageTablePDE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pde" ("PageTablePDE'_ \<lparr> pdeTable= _, pdeAccessed= _, pdeCacheDisabled= _, pdeWriteThrough= _, pdeExecuteDisable= _, pdeRights= _ \<rparr>")
where
  "PageTablePDE_ \<lparr> pdeTable= v0, pdeAccessed= v1, pdeCacheDisabled= v2, pdeWriteThrough= v3, pdeExecuteDisable= v4, pdeRights= v5 \<rparr> == PageTablePDE v0 v1 v2 v3 v4 v5"

abbreviation (input)
  LargePagePDE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pde" ("LargePagePDE'_ \<lparr> pdeFrame= _, pdeGlobal= _, pdePAT= _, pdeDirty= _, pdeAccessed= _, pdeCacheDisabled= _, pdeWriteThrough= _, pdeExecuteDisable= _, pdeRights= _ \<rparr>")
where
  "LargePagePDE_ \<lparr> pdeFrame= v0, pdeGlobal= v1, pdePAT= v2, pdeDirty= v3, pdeAccessed= v4, pdeCacheDisabled= v5, pdeWriteThrough= v6, pdeExecuteDisable= v7, pdeRights= v8 \<rparr> == LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8"

definition
  isInvalidPDE :: "pde \<Rightarrow> bool"
where
 "isInvalidPDE v \<equiv> case v of
    InvalidPDE \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPageTablePDE :: "pde \<Rightarrow> bool"
where
 "isPageTablePDE v \<equiv> case v of
    PageTablePDE v0 v1 v2 v3 v4 v5 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isLargePagePDE :: "pde \<Rightarrow> bool"
where
 "isLargePagePDE v \<equiv> case v of
    LargePagePDE v0 v1 v2 v3 v4 v5 v6 v7 v8 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype pte =
    InvalidPTE
  | SmallPagePTE paddr bool bool bool bool bool bool bool vmrights

primrec
  pteAccessed :: "pte \<Rightarrow> bool"
where
  "pteAccessed (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v4"

primrec
  pteCacheDisabled :: "pte \<Rightarrow> bool"
where
  "pteCacheDisabled (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v5"

primrec
  pteGlobal :: "pte \<Rightarrow> bool"
where
  "pteGlobal (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v1"

primrec
  pteWriteThrough :: "pte \<Rightarrow> bool"
where
  "pteWriteThrough (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v6"

primrec
  pteDirty :: "pte \<Rightarrow> bool"
where
  "pteDirty (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v3"

primrec
  ptePAT :: "pte \<Rightarrow> bool"
where
  "ptePAT (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v2"

primrec
  pteExecuteDisable :: "pte \<Rightarrow> bool"
where
  "pteExecuteDisable (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v7"

primrec
  pteRights :: "pte \<Rightarrow> vmrights"
where
  "pteRights (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v8"

primrec
  pteFrame :: "pte \<Rightarrow> paddr"
where
  "pteFrame (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = v0"

primrec
  pteAccessed_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteAccessed_update f (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = SmallPagePTE v0 v1 v2 v3 (f v4) v5 v6 v7 v8"

primrec
  pteCacheDisabled_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteCacheDisabled_update f (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = SmallPagePTE v0 v1 v2 v3 v4 (f v5) v6 v7 v8"

primrec
  pteGlobal_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteGlobal_update f (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = SmallPagePTE v0 (f v1) v2 v3 v4 v5 v6 v7 v8"

primrec
  pteWriteThrough_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteWriteThrough_update f (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = SmallPagePTE v0 v1 v2 v3 v4 v5 (f v6) v7 v8"

primrec
  pteDirty_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteDirty_update f (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = SmallPagePTE v0 v1 v2 (f v3) v4 v5 v6 v7 v8"

primrec
  ptePAT_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pte \<Rightarrow> pte"
where
  "ptePAT_update f (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = SmallPagePTE v0 v1 (f v2) v3 v4 v5 v6 v7 v8"

primrec
  pteExecuteDisable_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteExecuteDisable_update f (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = SmallPagePTE v0 v1 v2 v3 v4 v5 v6 (f v7) v8"

primrec
  pteRights_update :: "(vmrights \<Rightarrow> vmrights) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteRights_update f (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 (f v8)"

primrec
  pteFrame_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteFrame_update f (SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8) = SmallPagePTE (f v0) v1 v2 v3 v4 v5 v6 v7 v8"

abbreviation (input)
  SmallPagePTE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pte" ("SmallPagePTE'_ \<lparr> pteFrame= _, pteGlobal= _, ptePAT= _, pteDirty= _, pteAccessed= _, pteCacheDisabled= _, pteWriteThrough= _, pteExecuteDisable= _, pteRights= _ \<rparr>")
where
  "SmallPagePTE_ \<lparr> pteFrame= v0, pteGlobal= v1, ptePAT= v2, pteDirty= v3, pteAccessed= v4, pteCacheDisabled= v5, pteWriteThrough= v6, pteExecuteDisable= v7, pteRights= v8 \<rparr> == SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8"

definition
  isInvalidPTE :: "pte \<Rightarrow> bool"
where
 "isInvalidPTE v \<equiv> case v of
    InvalidPTE \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isSmallPagePTE :: "pte \<Rightarrow> bool"
where
 "isSmallPagePTE v \<equiv> case v of
    SmallPagePTE v0 v1 v2 v3 v4 v5 v6 v7 v8 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype translation_type =
    NotTranslatedRequest
  | TranslatedRequest

datatype iocte =
    InvalidIOCTE
  | VTDCTE word16 bool nat paddr translation_type bool

primrec
  domainId :: "iocte \<Rightarrow> word16"
where
  "domainId (VTDCTE v0 v1 v2 v3 v4 v5) = v0"

primrec
  addressWidth :: "iocte \<Rightarrow> nat"
where
  "addressWidth (VTDCTE v0 v1 v2 v3 v4 v5) = v2"

primrec
  reservedMemReg :: "iocte \<Rightarrow> bool"
where
  "reservedMemReg (VTDCTE v0 v1 v2 v3 v4 v5) = v1"

primrec
  nxtLevelPtr :: "iocte \<Rightarrow> paddr"
where
  "nxtLevelPtr (VTDCTE v0 v1 v2 v3 v4 v5) = v3"

primrec
  translationType :: "iocte \<Rightarrow> translation_type"
where
  "translationType (VTDCTE v0 v1 v2 v3 v4 v5) = v4"

primrec
  ctePresent :: "iocte \<Rightarrow> bool"
where
  "ctePresent (VTDCTE v0 v1 v2 v3 v4 v5) = v5"

primrec
  domainId_update :: "(word16 \<Rightarrow> word16) \<Rightarrow> iocte \<Rightarrow> iocte"
where
  "domainId_update f (VTDCTE v0 v1 v2 v3 v4 v5) = VTDCTE (f v0) v1 v2 v3 v4 v5"

primrec
  addressWidth_update :: "(nat \<Rightarrow> nat) \<Rightarrow> iocte \<Rightarrow> iocte"
where
  "addressWidth_update f (VTDCTE v0 v1 v2 v3 v4 v5) = VTDCTE v0 v1 (f v2) v3 v4 v5"

primrec
  reservedMemReg_update :: "(bool \<Rightarrow> bool) \<Rightarrow> iocte \<Rightarrow> iocte"
where
  "reservedMemReg_update f (VTDCTE v0 v1 v2 v3 v4 v5) = VTDCTE v0 (f v1) v2 v3 v4 v5"

primrec
  nxtLevelPtr_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> iocte \<Rightarrow> iocte"
where
  "nxtLevelPtr_update f (VTDCTE v0 v1 v2 v3 v4 v5) = VTDCTE v0 v1 v2 (f v3) v4 v5"

primrec
  translationType_update :: "(translation_type \<Rightarrow> translation_type) \<Rightarrow> iocte \<Rightarrow> iocte"
where
  "translationType_update f (VTDCTE v0 v1 v2 v3 v4 v5) = VTDCTE v0 v1 v2 v3 (f v4) v5"

primrec
  ctePresent_update :: "(bool \<Rightarrow> bool) \<Rightarrow> iocte \<Rightarrow> iocte"
where
  "ctePresent_update f (VTDCTE v0 v1 v2 v3 v4 v5) = VTDCTE v0 v1 v2 v3 v4 (f v5)"

abbreviation (input)
  VTDCTE_trans :: "(word16) \<Rightarrow> (bool) \<Rightarrow> (nat) \<Rightarrow> (paddr) \<Rightarrow> (translation_type) \<Rightarrow> (bool) \<Rightarrow> iocte" ("VTDCTE'_ \<lparr> domainId= _, reservedMemReg= _, addressWidth= _, nxtLevelPtr= _, translationType= _, ctePresent= _ \<rparr>")
where
  "VTDCTE_ \<lparr> domainId= v0, reservedMemReg= v1, addressWidth= v2, nxtLevelPtr= v3, translationType= v4, ctePresent= v5 \<rparr> == VTDCTE v0 v1 v2 v3 v4 v5"

definition
  isInvalidIOCTE :: "iocte \<Rightarrow> bool"
where
 "isInvalidIOCTE v \<equiv> case v of
    InvalidIOCTE \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isVTDCTE :: "iocte \<Rightarrow> bool"
where
 "isVTDCTE v \<equiv> case v of
    VTDCTE v0 v1 v2 v3 v4 v5 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype iopte =
    InvalidIOPTE
  | VTDPTE paddr vmrights

primrec
  framePtr :: "iopte \<Rightarrow> paddr"
where
  "framePtr (VTDPTE v0 v1) = v0"

primrec
  rw :: "iopte \<Rightarrow> vmrights"
where
  "rw (VTDPTE v0 v1) = v1"

primrec
  framePtr_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> iopte \<Rightarrow> iopte"
where
  "framePtr_update f (VTDPTE v0 v1) = VTDPTE (f v0) v1"

primrec
  rw_update :: "(vmrights \<Rightarrow> vmrights) \<Rightarrow> iopte \<Rightarrow> iopte"
where
  "rw_update f (VTDPTE v0 v1) = VTDPTE v0 (f v1)"

abbreviation (input)
  VTDPTE_trans :: "(paddr) \<Rightarrow> (vmrights) \<Rightarrow> iopte" ("VTDPTE'_ \<lparr> framePtr= _, rw= _ \<rparr>")
where
  "VTDPTE_ \<lparr> framePtr= v0, rw= v1 \<rparr> == VTDPTE v0 v1"

definition
  isInvalidIOPTE :: "iopte \<Rightarrow> bool"
where
 "isInvalidIOPTE v \<equiv> case v of
    InvalidIOPTE \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isVTDPTE :: "iopte \<Rightarrow> bool"
where
 "isVTDPTE v \<equiv> case v of
    VTDPTE v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype iorte =
    InvalidIORTE
  | VTDRTE paddr bool

primrec
  cxtTablePtr :: "iorte \<Rightarrow> paddr"
where
  "cxtTablePtr (VTDRTE v0 v1) = v0"

primrec
  rtePresent :: "iorte \<Rightarrow> bool"
where
  "rtePresent (VTDRTE v0 v1) = v1"

primrec
  cxtTablePtr_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> iorte \<Rightarrow> iorte"
where
  "cxtTablePtr_update f (VTDRTE v0 v1) = VTDRTE (f v0) v1"

primrec
  rtePresent_update :: "(bool \<Rightarrow> bool) \<Rightarrow> iorte \<Rightarrow> iorte"
where
  "rtePresent_update f (VTDRTE v0 v1) = VTDRTE v0 (f v1)"

abbreviation (input)
  VTDRTE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> iorte" ("VTDRTE'_ \<lparr> cxtTablePtr= _, rtePresent= _ \<rparr>")
where
  "VTDRTE_ \<lparr> cxtTablePtr= v0, rtePresent= v1 \<rparr> == VTDRTE v0 v1"

definition
  isInvalidIORTE :: "iorte \<Rightarrow> bool"
where
 "isInvalidIORTE v \<equiv> case v of
    InvalidIORTE \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isVTDRTE :: "iorte \<Rightarrow> bool"
where
 "isVTDRTE v \<equiv> case v of
    VTDRTE v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype vmpage_entry =
    VMPTE pte
  | VMPDE pde
  | VMPDPTE pdpte

datatype vmpage_entry_ptr =
    VMPTEPtr machine_word
  | VMPDEPtr machine_word
  | VMPDPTEPtr machine_word

datatype vmmap_type =
    VMNoMap
  | VMVSpaceMap
  | VMIOSpaceMap

datatype vmattributes =
    VMAttributes bool bool bool

primrec
  x64CacheDisabled :: "vmattributes \<Rightarrow> bool"
where
  "x64CacheDisabled (VMAttributes v0 v1 v2) = v2"

primrec
  x64WriteThrough :: "vmattributes \<Rightarrow> bool"
where
  "x64WriteThrough (VMAttributes v0 v1 v2) = v0"

primrec
  x64PAT :: "vmattributes \<Rightarrow> bool"
where
  "x64PAT (VMAttributes v0 v1 v2) = v1"

primrec
  x64CacheDisabled_update :: "(bool \<Rightarrow> bool) \<Rightarrow> vmattributes \<Rightarrow> vmattributes"
where
  "x64CacheDisabled_update f (VMAttributes v0 v1 v2) = VMAttributes v0 v1 (f v2)"

primrec
  x64WriteThrough_update :: "(bool \<Rightarrow> bool) \<Rightarrow> vmattributes \<Rightarrow> vmattributes"
where
  "x64WriteThrough_update f (VMAttributes v0 v1 v2) = VMAttributes (f v0) v1 v2"

primrec
  x64PAT_update :: "(bool \<Rightarrow> bool) \<Rightarrow> vmattributes \<Rightarrow> vmattributes"
where
  "x64PAT_update f (VMAttributes v0 v1 v2) = VMAttributes v0 (f v1) v2"

abbreviation (input)
  VMAttributes_trans :: "(bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> vmattributes" ("VMAttributes'_ \<lparr> x64WriteThrough= _, x64PAT= _, x64CacheDisabled= _ \<rparr>")
where
  "VMAttributes_ \<lparr> x64WriteThrough= v0, x64PAT= v1, x64CacheDisabled= v2 \<rparr> == VMAttributes v0 v1 v2"

lemma x64CacheDisabled_x64CacheDisabled_update [simp]:
  "x64CacheDisabled (x64CacheDisabled_update f v) = f (x64CacheDisabled v)"
  by (cases v) simp

lemma x64CacheDisabled_x64WriteThrough_update [simp]:
  "x64CacheDisabled (x64WriteThrough_update f v) = x64CacheDisabled v"
  by (cases v) simp

lemma x64CacheDisabled_x64PAT_update [simp]:
  "x64CacheDisabled (x64PAT_update f v) = x64CacheDisabled v"
  by (cases v) simp

lemma x64WriteThrough_x64CacheDisabled_update [simp]:
  "x64WriteThrough (x64CacheDisabled_update f v) = x64WriteThrough v"
  by (cases v) simp

lemma x64WriteThrough_x64WriteThrough_update [simp]:
  "x64WriteThrough (x64WriteThrough_update f v) = f (x64WriteThrough v)"
  by (cases v) simp

lemma x64WriteThrough_x64PAT_update [simp]:
  "x64WriteThrough (x64PAT_update f v) = x64WriteThrough v"
  by (cases v) simp

lemma x64PAT_x64CacheDisabled_update [simp]:
  "x64PAT (x64CacheDisabled_update f v) = x64PAT v"
  by (cases v) simp

lemma x64PAT_x64WriteThrough_update [simp]:
  "x64PAT (x64WriteThrough_update f v) = x64PAT v"
  by (cases v) simp

lemma x64PAT_x64PAT_update [simp]:
  "x64PAT (x64PAT_update f v) = f (x64PAT v)"
  by (cases v) simp

definition
addrFromKPPtr :: "machine_word \<Rightarrow> paddr"
where
"addrFromKPPtr \<equiv> Platform.addrFromKPPtr"

definition
fromPAddr :: "paddr \<Rightarrow> machine_word"
where
"fromPAddr \<equiv> Platform.fromPAddr"

definition
ptTranslationBits :: "nat"
where
"ptTranslationBits \<equiv> 9"

definition
ptBits :: "nat"
where
"ptBits \<equiv> ptTranslationBits + 3"

definition
pdBits :: "nat"
where
"pdBits \<equiv> ptTranslationBits + 3"

definition
pdptBits :: "nat"
where
"pdptBits \<equiv> ptTranslationBits + 3"

definition
pml4Bits :: "nat"
where
"pml4Bits \<equiv> ptTranslationBits + 3"

definition
ioptBits :: "nat"
where
"ioptBits \<equiv> ptTranslationBits + 3"

definition
pageColourBits :: "nat"
where
"pageColourBits \<equiv> error []"

definition
setInterruptMode :: "irq \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> unit machine_monad"
where
"setInterruptMode arg1 arg2 arg3 \<equiv> return ()"

definition
archSetCurrentVSpaceRoot :: "paddr \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
where
"archSetCurrentVSpaceRoot pd asid \<equiv>
  setCurrentCR3 $ Platform.X64CR3 pd asid"

definition
"resetCR3 \<equiv> error []"

definition
invalidatePageStructureCache :: "unit machine_monad"
where
"invalidatePageStructureCache \<equiv> invalidateTLBEntry 0"

definition
vtdCTBits :: "nat"
where
"vtdCTBits \<equiv> 9"

definition
"vtdCTESizeBits \<equiv> 3"

definition
"vtdCTSizeBits \<equiv> vtdCTBits + vtdCTESizeBits"

definition
vtdPTBits :: "nat"
where
"vtdPTBits \<equiv> 9"

definition
"vtdPTESizeBits \<equiv> 3"

definition
"vtdPTSizeBits \<equiv> vtdCTBits + vtdPTESizeBits"

definition
wordFromIOCTE :: "iocte \<Rightarrow> (machine_word * machine_word)"
where
"wordFromIOCTE x0\<equiv> (case x0 of
    InvalidIOCTE \<Rightarrow>    (0,0)
  | (VTDCTE did rmr aw nxtptr tt present) \<Rightarrow>    (((fromIntegral $ did) `~shiftL~` 4) &&
    (if rmr then (1 << 3) else 0) || ((fromIntegral aw) && 0x7),
    ((fromIntegral nxtptr) && 0xfffff000) || (if present then 1 else 0))
  )"

definition
wordFromIOPTE :: "iopte \<Rightarrow> machine_word"
where
"wordFromIOPTE x0\<equiv> (case x0 of
    InvalidIOPTE \<Rightarrow>    0
  | (VTDPTE pteFrame rw) \<Rightarrow>    ((fromIntegral $ pteFrame) && 0xfffff000) || (vmRightsToBits rw)
  )"

definition
wordFromIORTE :: "iorte \<Rightarrow> machine_word"
where
"wordFromIORTE x0\<equiv> (case x0 of
    InvalidIORTE \<Rightarrow>    0
  | (VTDRTE ptr present) \<Rightarrow>    ((fromIntegral $ ptr) && 0xfffff000) || (if present then 1 else 0)
  )"

definition
getPTIndex :: "vptr \<Rightarrow> machine_word"
where
"getPTIndex vptr \<equiv>
    let shiftBits = pageBits
    in fromVPtr $ vptr `~shiftR~` shiftBits && mask ptTranslationBits"

definition
getPDIndex :: "vptr \<Rightarrow> machine_word"
where
"getPDIndex vptr \<equiv>
    let shiftBits = pageBits + ptTranslationBits
    in fromVPtr $ vptr `~shiftR~` shiftBits && mask ptTranslationBits"

definition
getPDPTIndex :: "vptr \<Rightarrow> machine_word"
where
"getPDPTIndex vptr \<equiv>
    let shiftBits = pageBits + ptTranslationBits + ptTranslationBits
    in fromVPtr $ vptr `~shiftR~` shiftBits && mask ptTranslationBits"

definition
getPML4Index :: "vptr \<Rightarrow> machine_word"
where
"getPML4Index vptr \<equiv>
    let shiftBits = pageBits + ptTranslationBits + ptTranslationBits + ptTranslationBits
    in fromVPtr $ vptr `~shiftR~` shiftBits && mask ptTranslationBits"

definition
vmRightsToBits :: "vmrights \<Rightarrow> machine_word"
where
"vmRightsToBits x0\<equiv> (case x0 of
    VMKernelOnly \<Rightarrow>    0x1
  | VMReadOnly \<Rightarrow>    0x10
  | VMWriteOnly \<Rightarrow>    0x01
  | VMReadWrite \<Rightarrow>    0x11
  )"

definition
allowWrite :: "vmrights \<Rightarrow> bool"
where
"allowWrite x0\<equiv> (case x0 of
    VMKernelOnly \<Rightarrow>    False
  | VMReadOnly \<Rightarrow>    False
  | VMReadWrite \<Rightarrow>    True
  | VMWriteOnly \<Rightarrow>    True
  )"

definition
allowRead :: "vmrights \<Rightarrow> bool"
where
"allowRead x0\<equiv> (case x0 of
    VMKernelOnly \<Rightarrow>    False
  | VMReadOnly \<Rightarrow>    False
  | VMReadWrite \<Rightarrow>    True
  | VMWriteOnly \<Rightarrow>    False
  )"

definition
getVMRights :: "bool \<Rightarrow> bool \<Rightarrow> vmrights"
where
"getVMRights x0 x1\<equiv> (case (x0, x1) of
    (True, True) \<Rightarrow>    VMReadWrite
  | (True, False) \<Rightarrow>    VMReadOnly
  | (False, True) \<Rightarrow>    VMWriteOnly
  | (False, False) \<Rightarrow>    VMKernelOnly
  )"

definition
vmRightsFromBits :: "machine_word \<Rightarrow> vmrights"
where
"vmRightsFromBits rw\<equiv> getVMRights (testBit rw 1) (testBit rw 0)"

definition
pptrBase :: "vptr"
where
"pptrBase \<equiv> Platform.pptrBase"

definition
physBase :: "paddr"
where
"physBase \<equiv> toPAddr Platform.physBase"

definition
initIRQController :: "unit machine_monad"
where
"initIRQController \<equiv> error []"


end
qualify X64 (in Arch) 
(* translation_type instance proofs *)
(*<*)
instantiation translation_type :: enum begin
interpretation Arch .
definition
  enum_translation_type: "enum_class.enum \<equiv> 
    [ 
      NotTranslatedRequest,
      TranslatedRequest
    ]"


definition
  "enum_class.enum_all (P :: translation_type \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: translation_type \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_translation_type enum_all_translation_type_def enum_ex_translation_type_def)
  by fast+
end

instantiation translation_type :: enum_alt
begin
interpretation Arch .
definition
  enum_alt_translation_type: "enum_alt \<equiv> 
    alt_from_ord (enum :: translation_type list)"
instance ..
end

instantiation translation_type :: enumeration_both
begin
interpretation Arch .
instance by (intro_classes, simp add: enum_alt_translation_type)
end

(*>*)
end_qualify
context Arch begin global_naming X64

end
qualify X64 (in Arch) 
(* vmmap_type instance proofs *)
(*<*)
instantiation vmmap_type :: enum begin
interpretation Arch .
definition
  enum_vmmap_type: "enum_class.enum \<equiv> 
    [ 
      VMNoMap,
      VMVSpaceMap,
      VMIOSpaceMap
    ]"


definition
  "enum_class.enum_all (P :: vmmap_type \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: vmmap_type \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_vmmap_type enum_all_vmmap_type_def enum_ex_vmmap_type_def)
  by fast+
end

instantiation vmmap_type :: enum_alt
begin
interpretation Arch .
definition
  enum_alt_vmmap_type: "enum_alt \<equiv> 
    alt_from_ord (enum :: vmmap_type list)"
instance ..
end

instantiation vmmap_type :: enumeration_both
begin
interpretation Arch .
instance by (intro_classes, simp add: enum_alt_vmmap_type)
end

(*>*)
end_qualify
context Arch begin global_naming X64


definition
wordFromPML4E :: "pml4e \<Rightarrow> machine_word"
where
"wordFromPML4E x0\<equiv> (case x0 of
    InvalidPML4E \<Rightarrow>    0
  | (PDPointerTablePML4E table accessed cd wt xd rights) \<Rightarrow>    1 ||
    (if xd then (1 << 63) else 0) ||
    (fromIntegral table && 0x7fffffffff000) ||
    (if accessed then (1 << 5) else 0) ||
    (if cd then (1 << 4) else 0) ||
    (if wt then (1 << 3) else 0) ||
    (fromIntegral $ vmRightsToBits rights `~shiftL~` 1)
  )"

definition
wordFromPDPTE :: "pdpte \<Rightarrow> machine_word"
where
"wordFromPDPTE x0\<equiv> (case x0 of
    InvalidPDPTE \<Rightarrow>    0
  | (PageDirectoryPDPTE table accessed cd wt xd rights) \<Rightarrow>    1 ||
    (if xd then (1 << 63) else 0) ||
    (fromIntegral table && 0x7fffffffff000) ||
    (if accessed then (1 << 5) else 0) ||
    (if cd then (1 << 4) else 0) ||
    (if wt then (1 << 3) else 0) ||
    (fromIntegral $ vmRightsToBits rights `~shiftL~` 1)
  | (HugePagePDPTE frame global pat dirty accessed cd wt xd rights) \<Rightarrow>    1 || (1 << 7) ||
    (if xd then (1 << 63) else 0) ||
    (fromIntegral frame && 0x7ffffc0000000) ||
    (if global then (1 << 8) else 0) ||
    (if pat then (1 << 12) else 0) ||
    (if dirty then (1 << 6) else 0) ||
    (if accessed then (1 << 5) else 0) ||
    (if cd then (1 << 4) else 0) ||
    (if wt then (1 << 3) else 0) ||
    (fromIntegral $ vmRightsToBits rights `~shiftL~` 1)
  )"

definition
wordFromPDE :: "pde \<Rightarrow> machine_word"
where
"wordFromPDE x0\<equiv> (case x0 of
    InvalidPDE \<Rightarrow>    0
  | (PageTablePDE table accessed cd wt xd rights) \<Rightarrow>    1 ||
    (if xd then (1 << 63) else 0) ||
    (fromIntegral table && 0x7fffffffff000) ||
    (if accessed then (1 << 5) else 0) ||
    (if cd then (1 << 4) else 0) ||
    (if wt then (1 << 3) else 0) ||
    (fromIntegral $ vmRightsToBits rights `~shiftL~` 1)
  | (LargePagePDE frame global pat dirty accessed cd wt xd rights) \<Rightarrow>    1 || (1 << 7) ||
    (if xd then (1 << 63) else 0) ||
    (fromIntegral frame && 0x7ffffffe00000) ||
    (if global then (1 << 8) else 0) ||
    (if pat then (1 << 12) else 0) ||
    (if dirty then (1 << 6) else 0) ||
    (if accessed then (1 << 5) else 0) ||
    (if cd then (1 << 4) else 0) ||
    (if wt then (1 << 3) else 0) ||
    (fromIntegral $ vmRightsToBits rights `~shiftL~` 1)
  )"

definition
wordFromPTE :: "pte \<Rightarrow> machine_word"
where
"wordFromPTE x0\<equiv> (case x0 of
    InvalidPTE \<Rightarrow>    0
  | (SmallPagePTE frame global pat dirty accessed cd wt xd rights) \<Rightarrow>    1 ||
    (if xd then (1 << 63) else 0) ||
    (fromIntegral frame && 0x7fffffffffe000) ||
    (if global then (1 << 8) else 0) ||
    (if pat then (1 << 7) else 0) ||
    (if dirty then (1 << 6) else 0) ||
    (if accessed then (1 << 5) else 0) ||
    (if cd then (1 << 4) else 0) ||
    (if wt then (1 << 3) else 0) ||
    (fromIntegral $ vmRightsToBits rights `~shiftL~` 1)
  )"


end (* context X64 *)

end
