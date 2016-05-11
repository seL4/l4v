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

theory ArchRetypeDecls_H
imports
  ArchLabelFuns_H
  "../FaultMonad_H"
  "../EndpointDecls_H"
  "../KernelInitMonad_H"
  "../PSpaceFuns_H"
  ArchObjInsts_H
begin
context Arch begin global_naming ARM_H

datatype page_table_invocation =
    PageTableUnmap arch_capability machine_word
  | PageTableMap capability machine_word pde machine_word

primrec
  ptMapPDSlot :: "page_table_invocation \<Rightarrow> machine_word"
where
  "ptMapPDSlot (PageTableMap v0 v1 v2 v3) = v3"

primrec
  ptUnmapCapSlot :: "page_table_invocation \<Rightarrow> machine_word"
where
  "ptUnmapCapSlot (PageTableUnmap v0 v1) = v1"

primrec
  ptMapCTSlot :: "page_table_invocation \<Rightarrow> machine_word"
where
  "ptMapCTSlot (PageTableMap v0 v1 v2 v3) = v1"

primrec
  ptUnmapCap :: "page_table_invocation \<Rightarrow> arch_capability"
where
  "ptUnmapCap (PageTableUnmap v0 v1) = v0"

primrec
  ptMapPDE :: "page_table_invocation \<Rightarrow> pde"
where
  "ptMapPDE (PageTableMap v0 v1 v2 v3) = v2"

primrec
  ptMapCap :: "page_table_invocation \<Rightarrow> capability"
where
  "ptMapCap (PageTableMap v0 v1 v2 v3) = v0"

primrec
  ptMapPDSlot_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> page_table_invocation \<Rightarrow> page_table_invocation"
where
  "ptMapPDSlot_update f (PageTableMap v0 v1 v2 v3) = PageTableMap v0 v1 v2 (f v3)"

primrec
  ptUnmapCapSlot_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> page_table_invocation \<Rightarrow> page_table_invocation"
where
  "ptUnmapCapSlot_update f (PageTableUnmap v0 v1) = PageTableUnmap v0 (f v1)"

primrec
  ptMapCTSlot_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> page_table_invocation \<Rightarrow> page_table_invocation"
where
  "ptMapCTSlot_update f (PageTableMap v0 v1 v2 v3) = PageTableMap v0 (f v1) v2 v3"

primrec
  ptUnmapCap_update :: "(arch_capability \<Rightarrow> arch_capability) \<Rightarrow> page_table_invocation \<Rightarrow> page_table_invocation"
where
  "ptUnmapCap_update f (PageTableUnmap v0 v1) = PageTableUnmap (f v0) v1"

primrec
  ptMapPDE_update :: "(pde \<Rightarrow> pde) \<Rightarrow> page_table_invocation \<Rightarrow> page_table_invocation"
where
  "ptMapPDE_update f (PageTableMap v0 v1 v2 v3) = PageTableMap v0 v1 (f v2) v3"

primrec
  ptMapCap_update :: "(capability \<Rightarrow> capability) \<Rightarrow> page_table_invocation \<Rightarrow> page_table_invocation"
where
  "ptMapCap_update f (PageTableMap v0 v1 v2 v3) = PageTableMap (f v0) v1 v2 v3"

abbreviation (input)
  PageTableUnmap_trans :: "(arch_capability) \<Rightarrow> (machine_word) \<Rightarrow> page_table_invocation" ("PageTableUnmap'_ \<lparr> ptUnmapCap= _, ptUnmapCapSlot= _ \<rparr>")
where
  "PageTableUnmap_ \<lparr> ptUnmapCap= v0, ptUnmapCapSlot= v1 \<rparr> == PageTableUnmap v0 v1"

abbreviation (input)
  PageTableMap_trans :: "(capability) \<Rightarrow> (machine_word) \<Rightarrow> (pde) \<Rightarrow> (machine_word) \<Rightarrow> page_table_invocation" ("PageTableMap'_ \<lparr> ptMapCap= _, ptMapCTSlot= _, ptMapPDE= _, ptMapPDSlot= _ \<rparr>")
where
  "PageTableMap_ \<lparr> ptMapCap= v0, ptMapCTSlot= v1, ptMapPDE= v2, ptMapPDSlot= v3 \<rparr> == PageTableMap v0 v1 v2 v3"

definition
  isPageTableUnmap :: "page_table_invocation \<Rightarrow> bool"
where
 "isPageTableUnmap v \<equiv> case v of
    PageTableUnmap v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPageTableMap :: "page_table_invocation \<Rightarrow> bool"
where
 "isPageTableMap v \<equiv> case v of
    PageTableMap v0 v1 v2 v3 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype flush_type =
    Clean
  | Invalidate
  | CleanInvalidate
  | Unify

datatype page_directory_invocation =
    PageDirectoryNothing
  | PageDirectoryFlush flush_type vptr vptr paddr machine_word asid

primrec
  pdFlushEnd :: "page_directory_invocation \<Rightarrow> vptr"
where
  "pdFlushEnd (PageDirectoryFlush v0 v1 v2 v3 v4 v5) = v2"

primrec
  pdFlushType :: "page_directory_invocation \<Rightarrow> flush_type"
where
  "pdFlushType (PageDirectoryFlush v0 v1 v2 v3 v4 v5) = v0"

primrec
  pdFlushStart :: "page_directory_invocation \<Rightarrow> vptr"
where
  "pdFlushStart (PageDirectoryFlush v0 v1 v2 v3 v4 v5) = v1"

primrec
  pdFlushASID :: "page_directory_invocation \<Rightarrow> asid"
where
  "pdFlushASID (PageDirectoryFlush v0 v1 v2 v3 v4 v5) = v5"

primrec
  pdFlushPD :: "page_directory_invocation \<Rightarrow> machine_word"
where
  "pdFlushPD (PageDirectoryFlush v0 v1 v2 v3 v4 v5) = v4"

primrec
  pdFlushPStart :: "page_directory_invocation \<Rightarrow> paddr"
where
  "pdFlushPStart (PageDirectoryFlush v0 v1 v2 v3 v4 v5) = v3"

primrec
  pdFlushEnd_update :: "(vptr \<Rightarrow> vptr) \<Rightarrow> page_directory_invocation \<Rightarrow> page_directory_invocation"
where
  "pdFlushEnd_update f (PageDirectoryFlush v0 v1 v2 v3 v4 v5) = PageDirectoryFlush v0 v1 (f v2) v3 v4 v5"

primrec
  pdFlushType_update :: "(flush_type \<Rightarrow> flush_type) \<Rightarrow> page_directory_invocation \<Rightarrow> page_directory_invocation"
where
  "pdFlushType_update f (PageDirectoryFlush v0 v1 v2 v3 v4 v5) = PageDirectoryFlush (f v0) v1 v2 v3 v4 v5"

primrec
  pdFlushStart_update :: "(vptr \<Rightarrow> vptr) \<Rightarrow> page_directory_invocation \<Rightarrow> page_directory_invocation"
where
  "pdFlushStart_update f (PageDirectoryFlush v0 v1 v2 v3 v4 v5) = PageDirectoryFlush v0 (f v1) v2 v3 v4 v5"

primrec
  pdFlushASID_update :: "(asid \<Rightarrow> asid) \<Rightarrow> page_directory_invocation \<Rightarrow> page_directory_invocation"
where
  "pdFlushASID_update f (PageDirectoryFlush v0 v1 v2 v3 v4 v5) = PageDirectoryFlush v0 v1 v2 v3 v4 (f v5)"

primrec
  pdFlushPD_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> page_directory_invocation \<Rightarrow> page_directory_invocation"
where
  "pdFlushPD_update f (PageDirectoryFlush v0 v1 v2 v3 v4 v5) = PageDirectoryFlush v0 v1 v2 v3 (f v4) v5"

primrec
  pdFlushPStart_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> page_directory_invocation \<Rightarrow> page_directory_invocation"
where
  "pdFlushPStart_update f (PageDirectoryFlush v0 v1 v2 v3 v4 v5) = PageDirectoryFlush v0 v1 v2 (f v3) v4 v5"

abbreviation (input)
  PageDirectoryFlush_trans :: "(flush_type) \<Rightarrow> (vptr) \<Rightarrow> (vptr) \<Rightarrow> (paddr) \<Rightarrow> (machine_word) \<Rightarrow> (asid) \<Rightarrow> page_directory_invocation" ("PageDirectoryFlush'_ \<lparr> pdFlushType= _, pdFlushStart= _, pdFlushEnd= _, pdFlushPStart= _, pdFlushPD= _, pdFlushASID= _ \<rparr>")
where
  "PageDirectoryFlush_ \<lparr> pdFlushType= v0, pdFlushStart= v1, pdFlushEnd= v2, pdFlushPStart= v3, pdFlushPD= v4, pdFlushASID= v5 \<rparr> == PageDirectoryFlush v0 v1 v2 v3 v4 v5"

definition
  isPageDirectoryNothing :: "page_directory_invocation \<Rightarrow> bool"
where
 "isPageDirectoryNothing v \<equiv> case v of
    PageDirectoryNothing \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPageDirectoryFlush :: "page_directory_invocation \<Rightarrow> bool"
where
 "isPageDirectoryFlush v \<equiv> case v of
    PageDirectoryFlush v0 v1 v2 v3 v4 v5 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype page_invocation =
    PageGetAddr machine_word
  | PageFlush flush_type vptr vptr paddr machine_word asid
  | PageRemap asid "(pte * machine_word list) + (pde * machine_word list)"
  | PageMap asid capability machine_word "(pte * machine_word list) + (pde * machine_word list)"
  | PageUnmap arch_capability machine_word

primrec
  pageMapCap :: "page_invocation \<Rightarrow> capability"
where
  "pageMapCap (PageMap v0 v1 v2 v3) = v1"

primrec
  pageUnmapCapSlot :: "page_invocation \<Rightarrow> machine_word"
where
  "pageUnmapCapSlot (PageUnmap v0 v1) = v1"

primrec
  pageFlushStart :: "page_invocation \<Rightarrow> vptr"
where
  "pageFlushStart (PageFlush v0 v1 v2 v3 v4 v5) = v1"

primrec
  pageUnmapCap :: "page_invocation \<Rightarrow> arch_capability"
where
  "pageUnmapCap (PageUnmap v0 v1) = v0"

primrec
  pageFlushPD :: "page_invocation \<Rightarrow> machine_word"
where
  "pageFlushPD (PageFlush v0 v1 v2 v3 v4 v5) = v4"

primrec
  pageFlushASID :: "page_invocation \<Rightarrow> asid"
where
  "pageFlushASID (PageFlush v0 v1 v2 v3 v4 v5) = v5"

primrec
  pageFlushType :: "page_invocation \<Rightarrow> flush_type"
where
  "pageFlushType (PageFlush v0 v1 v2 v3 v4 v5) = v0"

primrec
  pageFlushEnd :: "page_invocation \<Rightarrow> vptr"
where
  "pageFlushEnd (PageFlush v0 v1 v2 v3 v4 v5) = v2"

primrec
  pageFlushPStart :: "page_invocation \<Rightarrow> paddr"
where
  "pageFlushPStart (PageFlush v0 v1 v2 v3 v4 v5) = v3"

primrec
  pageRemapEntries :: "page_invocation \<Rightarrow> (pte * machine_word list) + (pde * machine_word list)"
where
  "pageRemapEntries (PageRemap v0 v1) = v1"

primrec
  pageMapASID :: "page_invocation \<Rightarrow> asid"
where
  "pageMapASID (PageMap v0 v1 v2 v3) = v0"

primrec
  pageGetBasePtr :: "page_invocation \<Rightarrow> machine_word"
where
  "pageGetBasePtr (PageGetAddr v0) = v0"

primrec
  pageMapEntries :: "page_invocation \<Rightarrow> (pte * machine_word list) + (pde * machine_word list)"
where
  "pageMapEntries (PageMap v0 v1 v2 v3) = v3"

primrec
  pageRemapASID :: "page_invocation \<Rightarrow> asid"
where
  "pageRemapASID (PageRemap v0 v1) = v0"

primrec
  pageMapCTSlot :: "page_invocation \<Rightarrow> machine_word"
where
  "pageMapCTSlot (PageMap v0 v1 v2 v3) = v2"

primrec
  pageMapCap_update :: "(capability \<Rightarrow> capability) \<Rightarrow> page_invocation \<Rightarrow> page_invocation"
where
  "pageMapCap_update f (PageMap v0 v1 v2 v3) = PageMap v0 (f v1) v2 v3"

primrec
  pageUnmapCapSlot_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> page_invocation \<Rightarrow> page_invocation"
where
  "pageUnmapCapSlot_update f (PageUnmap v0 v1) = PageUnmap v0 (f v1)"

primrec
  pageFlushStart_update :: "(vptr \<Rightarrow> vptr) \<Rightarrow> page_invocation \<Rightarrow> page_invocation"
where
  "pageFlushStart_update f (PageFlush v0 v1 v2 v3 v4 v5) = PageFlush v0 (f v1) v2 v3 v4 v5"

primrec
  pageUnmapCap_update :: "(arch_capability \<Rightarrow> arch_capability) \<Rightarrow> page_invocation \<Rightarrow> page_invocation"
where
  "pageUnmapCap_update f (PageUnmap v0 v1) = PageUnmap (f v0) v1"

primrec
  pageFlushPD_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> page_invocation \<Rightarrow> page_invocation"
where
  "pageFlushPD_update f (PageFlush v0 v1 v2 v3 v4 v5) = PageFlush v0 v1 v2 v3 (f v4) v5"

primrec
  pageFlushASID_update :: "(asid \<Rightarrow> asid) \<Rightarrow> page_invocation \<Rightarrow> page_invocation"
where
  "pageFlushASID_update f (PageFlush v0 v1 v2 v3 v4 v5) = PageFlush v0 v1 v2 v3 v4 (f v5)"

primrec
  pageFlushType_update :: "(flush_type \<Rightarrow> flush_type) \<Rightarrow> page_invocation \<Rightarrow> page_invocation"
where
  "pageFlushType_update f (PageFlush v0 v1 v2 v3 v4 v5) = PageFlush (f v0) v1 v2 v3 v4 v5"

primrec
  pageFlushEnd_update :: "(vptr \<Rightarrow> vptr) \<Rightarrow> page_invocation \<Rightarrow> page_invocation"
where
  "pageFlushEnd_update f (PageFlush v0 v1 v2 v3 v4 v5) = PageFlush v0 v1 (f v2) v3 v4 v5"

primrec
  pageFlushPStart_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> page_invocation \<Rightarrow> page_invocation"
where
  "pageFlushPStart_update f (PageFlush v0 v1 v2 v3 v4 v5) = PageFlush v0 v1 v2 (f v3) v4 v5"

primrec
  pageRemapEntries_update :: "(((pte * machine_word list) + (pde * machine_word list)) \<Rightarrow> ((pte * machine_word list) + (pde * machine_word list))) \<Rightarrow> page_invocation \<Rightarrow> page_invocation"
where
  "pageRemapEntries_update f (PageRemap v0 v1) = PageRemap v0 (f v1)"

primrec
  pageMapASID_update :: "(asid \<Rightarrow> asid) \<Rightarrow> page_invocation \<Rightarrow> page_invocation"
where
  "pageMapASID_update f (PageMap v0 v1 v2 v3) = PageMap (f v0) v1 v2 v3"

primrec
  pageGetBasePtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> page_invocation \<Rightarrow> page_invocation"
where
  "pageGetBasePtr_update f (PageGetAddr v0) = PageGetAddr (f v0)"

primrec
  pageMapEntries_update :: "(((pte * machine_word list) + (pde * machine_word list)) \<Rightarrow> ((pte * machine_word list) + (pde * machine_word list))) \<Rightarrow> page_invocation \<Rightarrow> page_invocation"
where
  "pageMapEntries_update f (PageMap v0 v1 v2 v3) = PageMap v0 v1 v2 (f v3)"

primrec
  pageRemapASID_update :: "(asid \<Rightarrow> asid) \<Rightarrow> page_invocation \<Rightarrow> page_invocation"
where
  "pageRemapASID_update f (PageRemap v0 v1) = PageRemap (f v0) v1"

primrec
  pageMapCTSlot_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> page_invocation \<Rightarrow> page_invocation"
where
  "pageMapCTSlot_update f (PageMap v0 v1 v2 v3) = PageMap v0 v1 (f v2) v3"

abbreviation (input)
  PageGetAddr_trans :: "(machine_word) \<Rightarrow> page_invocation" ("PageGetAddr'_ \<lparr> pageGetBasePtr= _ \<rparr>")
where
  "PageGetAddr_ \<lparr> pageGetBasePtr= v0 \<rparr> == PageGetAddr v0"

abbreviation (input)
  PageFlush_trans :: "(flush_type) \<Rightarrow> (vptr) \<Rightarrow> (vptr) \<Rightarrow> (paddr) \<Rightarrow> (machine_word) \<Rightarrow> (asid) \<Rightarrow> page_invocation" ("PageFlush'_ \<lparr> pageFlushType= _, pageFlushStart= _, pageFlushEnd= _, pageFlushPStart= _, pageFlushPD= _, pageFlushASID= _ \<rparr>")
where
  "PageFlush_ \<lparr> pageFlushType= v0, pageFlushStart= v1, pageFlushEnd= v2, pageFlushPStart= v3, pageFlushPD= v4, pageFlushASID= v5 \<rparr> == PageFlush v0 v1 v2 v3 v4 v5"

abbreviation (input)
  PageRemap_trans :: "(asid) \<Rightarrow> ((pte * machine_word list) + (pde * machine_word list)) \<Rightarrow> page_invocation" ("PageRemap'_ \<lparr> pageRemapASID= _, pageRemapEntries= _ \<rparr>")
where
  "PageRemap_ \<lparr> pageRemapASID= v0, pageRemapEntries= v1 \<rparr> == PageRemap v0 v1"

abbreviation (input)
  PageMap_trans :: "(asid) \<Rightarrow> (capability) \<Rightarrow> (machine_word) \<Rightarrow> ((pte * machine_word list) + (pde * machine_word list)) \<Rightarrow> page_invocation" ("PageMap'_ \<lparr> pageMapASID= _, pageMapCap= _, pageMapCTSlot= _, pageMapEntries= _ \<rparr>")
where
  "PageMap_ \<lparr> pageMapASID= v0, pageMapCap= v1, pageMapCTSlot= v2, pageMapEntries= v3 \<rparr> == PageMap v0 v1 v2 v3"

abbreviation (input)
  PageUnmap_trans :: "(arch_capability) \<Rightarrow> (machine_word) \<Rightarrow> page_invocation" ("PageUnmap'_ \<lparr> pageUnmapCap= _, pageUnmapCapSlot= _ \<rparr>")
where
  "PageUnmap_ \<lparr> pageUnmapCap= v0, pageUnmapCapSlot= v1 \<rparr> == PageUnmap v0 v1"

definition
  isPageGetAddr :: "page_invocation \<Rightarrow> bool"
where
 "isPageGetAddr v \<equiv> case v of
    PageGetAddr v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPageFlush :: "page_invocation \<Rightarrow> bool"
where
 "isPageFlush v \<equiv> case v of
    PageFlush v0 v1 v2 v3 v4 v5 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPageRemap :: "page_invocation \<Rightarrow> bool"
where
 "isPageRemap v \<equiv> case v of
    PageRemap v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPageMap :: "page_invocation \<Rightarrow> bool"
where
 "isPageMap v \<equiv> case v of
    PageMap v0 v1 v2 v3 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPageUnmap :: "page_invocation \<Rightarrow> bool"
where
 "isPageUnmap v \<equiv> case v of
    PageUnmap v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype asidcontrol_invocation =
    MakePool machine_word machine_word machine_word asid

primrec
  makePoolSlot :: "asidcontrol_invocation \<Rightarrow> machine_word"
where
  "makePoolSlot (MakePool v0 v1 v2 v3) = v1"

primrec
  makePoolFrame :: "asidcontrol_invocation \<Rightarrow> machine_word"
where
  "makePoolFrame (MakePool v0 v1 v2 v3) = v0"

primrec
  makePoolBase :: "asidcontrol_invocation \<Rightarrow> asid"
where
  "makePoolBase (MakePool v0 v1 v2 v3) = v3"

primrec
  makePoolParent :: "asidcontrol_invocation \<Rightarrow> machine_word"
where
  "makePoolParent (MakePool v0 v1 v2 v3) = v2"

primrec
  makePoolSlot_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> asidcontrol_invocation \<Rightarrow> asidcontrol_invocation"
where
  "makePoolSlot_update f (MakePool v0 v1 v2 v3) = MakePool v0 (f v1) v2 v3"

primrec
  makePoolFrame_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> asidcontrol_invocation \<Rightarrow> asidcontrol_invocation"
where
  "makePoolFrame_update f (MakePool v0 v1 v2 v3) = MakePool (f v0) v1 v2 v3"

primrec
  makePoolBase_update :: "(asid \<Rightarrow> asid) \<Rightarrow> asidcontrol_invocation \<Rightarrow> asidcontrol_invocation"
where
  "makePoolBase_update f (MakePool v0 v1 v2 v3) = MakePool v0 v1 v2 (f v3)"

primrec
  makePoolParent_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> asidcontrol_invocation \<Rightarrow> asidcontrol_invocation"
where
  "makePoolParent_update f (MakePool v0 v1 v2 v3) = MakePool v0 v1 (f v2) v3"

abbreviation (input)
  MakePool_trans :: "(machine_word) \<Rightarrow> (machine_word) \<Rightarrow> (machine_word) \<Rightarrow> (asid) \<Rightarrow> asidcontrol_invocation" ("MakePool'_ \<lparr> makePoolFrame= _, makePoolSlot= _, makePoolParent= _, makePoolBase= _ \<rparr>")
where
  "MakePool_ \<lparr> makePoolFrame= v0, makePoolSlot= v1, makePoolParent= v2, makePoolBase= v3 \<rparr> == MakePool v0 v1 v2 v3"

lemma makePoolSlot_makePoolSlot_update [simp]:
  "makePoolSlot (makePoolSlot_update f v) = f (makePoolSlot v)"
  by (cases v) simp

lemma makePoolSlot_makePoolFrame_update [simp]:
  "makePoolSlot (makePoolFrame_update f v) = makePoolSlot v"
  by (cases v) simp

lemma makePoolSlot_makePoolBase_update [simp]:
  "makePoolSlot (makePoolBase_update f v) = makePoolSlot v"
  by (cases v) simp

lemma makePoolSlot_makePoolParent_update [simp]:
  "makePoolSlot (makePoolParent_update f v) = makePoolSlot v"
  by (cases v) simp

lemma makePoolFrame_makePoolSlot_update [simp]:
  "makePoolFrame (makePoolSlot_update f v) = makePoolFrame v"
  by (cases v) simp

lemma makePoolFrame_makePoolFrame_update [simp]:
  "makePoolFrame (makePoolFrame_update f v) = f (makePoolFrame v)"
  by (cases v) simp

lemma makePoolFrame_makePoolBase_update [simp]:
  "makePoolFrame (makePoolBase_update f v) = makePoolFrame v"
  by (cases v) simp

lemma makePoolFrame_makePoolParent_update [simp]:
  "makePoolFrame (makePoolParent_update f v) = makePoolFrame v"
  by (cases v) simp

lemma makePoolBase_makePoolSlot_update [simp]:
  "makePoolBase (makePoolSlot_update f v) = makePoolBase v"
  by (cases v) simp

lemma makePoolBase_makePoolFrame_update [simp]:
  "makePoolBase (makePoolFrame_update f v) = makePoolBase v"
  by (cases v) simp

lemma makePoolBase_makePoolBase_update [simp]:
  "makePoolBase (makePoolBase_update f v) = f (makePoolBase v)"
  by (cases v) simp

lemma makePoolBase_makePoolParent_update [simp]:
  "makePoolBase (makePoolParent_update f v) = makePoolBase v"
  by (cases v) simp

lemma makePoolParent_makePoolSlot_update [simp]:
  "makePoolParent (makePoolSlot_update f v) = makePoolParent v"
  by (cases v) simp

lemma makePoolParent_makePoolFrame_update [simp]:
  "makePoolParent (makePoolFrame_update f v) = makePoolParent v"
  by (cases v) simp

lemma makePoolParent_makePoolBase_update [simp]:
  "makePoolParent (makePoolBase_update f v) = makePoolParent v"
  by (cases v) simp

lemma makePoolParent_makePoolParent_update [simp]:
  "makePoolParent (makePoolParent_update f v) = f (makePoolParent v)"
  by (cases v) simp

datatype asidpool_invocation =
    Assign asid machine_word machine_word

primrec
  assignASIDPool :: "asidpool_invocation \<Rightarrow> machine_word"
where
  "assignASIDPool (Assign v0 v1 v2) = v1"

primrec
  assignASIDCTSlot :: "asidpool_invocation \<Rightarrow> machine_word"
where
  "assignASIDCTSlot (Assign v0 v1 v2) = v2"

primrec
  assignASID :: "asidpool_invocation \<Rightarrow> asid"
where
  "assignASID (Assign v0 v1 v2) = v0"

primrec
  assignASIDPool_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> asidpool_invocation \<Rightarrow> asidpool_invocation"
where
  "assignASIDPool_update f (Assign v0 v1 v2) = Assign v0 (f v1) v2"

primrec
  assignASIDCTSlot_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> asidpool_invocation \<Rightarrow> asidpool_invocation"
where
  "assignASIDCTSlot_update f (Assign v0 v1 v2) = Assign v0 v1 (f v2)"

primrec
  assignASID_update :: "(asid \<Rightarrow> asid) \<Rightarrow> asidpool_invocation \<Rightarrow> asidpool_invocation"
where
  "assignASID_update f (Assign v0 v1 v2) = Assign (f v0) v1 v2"

abbreviation (input)
  Assign_trans :: "(asid) \<Rightarrow> (machine_word) \<Rightarrow> (machine_word) \<Rightarrow> asidpool_invocation" ("Assign'_ \<lparr> assignASID= _, assignASIDPool= _, assignASIDCTSlot= _ \<rparr>")
where
  "Assign_ \<lparr> assignASID= v0, assignASIDPool= v1, assignASIDCTSlot= v2 \<rparr> == Assign v0 v1 v2"

lemma assignASIDPool_assignASIDPool_update [simp]:
  "assignASIDPool (assignASIDPool_update f v) = f (assignASIDPool v)"
  by (cases v) simp

lemma assignASIDPool_assignASIDCTSlot_update [simp]:
  "assignASIDPool (assignASIDCTSlot_update f v) = assignASIDPool v"
  by (cases v) simp

lemma assignASIDPool_assignASID_update [simp]:
  "assignASIDPool (assignASID_update f v) = assignASIDPool v"
  by (cases v) simp

lemma assignASIDCTSlot_assignASIDPool_update [simp]:
  "assignASIDCTSlot (assignASIDPool_update f v) = assignASIDCTSlot v"
  by (cases v) simp

lemma assignASIDCTSlot_assignASIDCTSlot_update [simp]:
  "assignASIDCTSlot (assignASIDCTSlot_update f v) = f (assignASIDCTSlot v)"
  by (cases v) simp

lemma assignASIDCTSlot_assignASID_update [simp]:
  "assignASIDCTSlot (assignASID_update f v) = assignASIDCTSlot v"
  by (cases v) simp

lemma assignASID_assignASIDPool_update [simp]:
  "assignASID (assignASIDPool_update f v) = assignASID v"
  by (cases v) simp

lemma assignASID_assignASIDCTSlot_update [simp]:
  "assignASID (assignASIDCTSlot_update f v) = assignASID v"
  by (cases v) simp

lemma assignASID_assignASID_update [simp]:
  "assignASID (assignASID_update f v) = f (assignASID v)"
  by (cases v) simp


datatype invocation =
    InvokePageTable page_table_invocation
  | InvokePageDirectory page_directory_invocation
  | InvokePage page_invocation
  | InvokeASIDControl asidcontrol_invocation
  | InvokeASIDPool asidpool_invocation

datatype irqcontrol_invocation =
    ARMNoArchIRQControl

datatype copy_register_sets =
    ARMNoExtraRegisters


consts'
deriveCap :: "machine_word \<Rightarrow> arch_capability \<Rightarrow> ( syscall_error , arch_capability ) kernel_f"

consts'
updateCapData :: "bool \<Rightarrow> machine_word \<Rightarrow> arch_capability \<Rightarrow> capability"

consts'
maskCapRights :: "cap_rights \<Rightarrow> arch_capability \<Rightarrow> capability"

consts'
finaliseCap :: "arch_capability \<Rightarrow> bool \<Rightarrow> capability kernel"

consts'
resetMemMapping :: "arch_capability \<Rightarrow> arch_capability"

consts'
recycleCap :: "bool \<Rightarrow> arch_capability \<Rightarrow> arch_capability kernel"

consts'
hasRecycleRights :: "arch_capability \<Rightarrow> bool"

consts'
sameRegionAs :: "arch_capability \<Rightarrow> arch_capability \<Rightarrow> bool"

consts'
isPhysicalCap :: "arch_capability \<Rightarrow> bool"

consts'
sameObjectAs :: "arch_capability \<Rightarrow> arch_capability \<Rightarrow> bool"

consts'
createObject :: "object_type \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> arch_capability kernel"

consts'
decodeInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> cptr \<Rightarrow> machine_word \<Rightarrow> arch_capability \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , invocation ) kernel_f"

consts'
performInvocation :: "invocation \<Rightarrow> machine_word list kernel_p"

consts'
capUntypedPtr :: "arch_capability \<Rightarrow> machine_word"

consts'
capUntypedSize :: "arch_capability \<Rightarrow> machine_word"


end
end
