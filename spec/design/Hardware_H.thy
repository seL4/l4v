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
  "../machine/MachineOps"
  State_H
begin

type_synonym irq = "Platform.irq"

type_synonym paddr = "Platform.paddr"

datatype vmrights =
    VMNoAccess
  | VMKernelOnly
  | VMReadOnly
  | VMReadWrite

datatype pde =
    InvalidPDE
  | PageTablePDE paddr bool machine_word
  | SectionPDE paddr bool machine_word bool bool vmrights
  | SuperSectionPDE paddr bool bool bool vmrights

primrec
  pdeCacheable :: "pde \<Rightarrow> bool"
where
  "pdeCacheable (SuperSectionPDE v0 v1 v2 v3 v4) = v2"
| "pdeCacheable (SectionPDE v0 v1 v2 v3 v4 v5) = v3"

primrec
  pdeTable :: "pde \<Rightarrow> paddr"
where
  "pdeTable (PageTablePDE v0 v1 v2) = v0"

primrec
  pdeFrame :: "pde \<Rightarrow> paddr"
where
  "pdeFrame (SuperSectionPDE v0 v1 v2 v3 v4) = v0"
| "pdeFrame (SectionPDE v0 v1 v2 v3 v4 v5) = v0"

primrec
  pdeGlobal :: "pde \<Rightarrow> bool"
where
  "pdeGlobal (SuperSectionPDE v0 v1 v2 v3 v4) = v3"
| "pdeGlobal (SectionPDE v0 v1 v2 v3 v4 v5) = v4"

primrec
  pdeParity :: "pde \<Rightarrow> bool"
where
  "pdeParity (PageTablePDE v0 v1 v2) = v1"
| "pdeParity (SuperSectionPDE v0 v1 v2 v3 v4) = v1"
| "pdeParity (SectionPDE v0 v1 v2 v3 v4 v5) = v1"

primrec
  pdeDomain :: "pde \<Rightarrow> machine_word"
where
  "pdeDomain (PageTablePDE v0 v1 v2) = v2"
| "pdeDomain (SectionPDE v0 v1 v2 v3 v4 v5) = v2"

primrec
  pdeRights :: "pde \<Rightarrow> vmrights"
where
  "pdeRights (SuperSectionPDE v0 v1 v2 v3 v4) = v4"
| "pdeRights (SectionPDE v0 v1 v2 v3 v4 v5) = v5"

primrec
  pdeCacheable_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeCacheable_update f (SuperSectionPDE v0 v1 v2 v3 v4) = SuperSectionPDE v0 v1 (f v2) v3 v4"
| "pdeCacheable_update f (SectionPDE v0 v1 v2 v3 v4 v5) = SectionPDE v0 v1 v2 (f v3) v4 v5"

primrec
  pdeTable_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeTable_update f (PageTablePDE v0 v1 v2) = PageTablePDE (f v0) v1 v2"

primrec
  pdeFrame_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeFrame_update f (SuperSectionPDE v0 v1 v2 v3 v4) = SuperSectionPDE (f v0) v1 v2 v3 v4"
| "pdeFrame_update f (SectionPDE v0 v1 v2 v3 v4 v5) = SectionPDE (f v0) v1 v2 v3 v4 v5"

primrec
  pdeGlobal_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeGlobal_update f (SuperSectionPDE v0 v1 v2 v3 v4) = SuperSectionPDE v0 v1 v2 (f v3) v4"
| "pdeGlobal_update f (SectionPDE v0 v1 v2 v3 v4 v5) = SectionPDE v0 v1 v2 v3 (f v4) v5"

primrec
  pdeParity_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeParity_update f (PageTablePDE v0 v1 v2) = PageTablePDE v0 (f v1) v2"
| "pdeParity_update f (SuperSectionPDE v0 v1 v2 v3 v4) = SuperSectionPDE v0 (f v1) v2 v3 v4"
| "pdeParity_update f (SectionPDE v0 v1 v2 v3 v4 v5) = SectionPDE v0 (f v1) v2 v3 v4 v5"

primrec
  pdeDomain_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeDomain_update f (PageTablePDE v0 v1 v2) = PageTablePDE v0 v1 (f v2)"
| "pdeDomain_update f (SectionPDE v0 v1 v2 v3 v4 v5) = SectionPDE v0 v1 (f v2) v3 v4 v5"

primrec
  pdeRights_update :: "(vmrights \<Rightarrow> vmrights) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeRights_update f (SuperSectionPDE v0 v1 v2 v3 v4) = SuperSectionPDE v0 v1 v2 v3 (f v4)"
| "pdeRights_update f (SectionPDE v0 v1 v2 v3 v4 v5) = SectionPDE v0 v1 v2 v3 v4 (f v5)"

abbreviation (input)
  PageTablePDE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (machine_word) \<Rightarrow> pde" ("PageTablePDE'_ \<lparr> pdeTable= _, pdeParity= _, pdeDomain= _ \<rparr>")
where
  "PageTablePDE_ \<lparr> pdeTable= v0, pdeParity= v1, pdeDomain= v2 \<rparr> == PageTablePDE v0 v1 v2"

abbreviation (input)
  SectionPDE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (machine_word) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pde" ("SectionPDE'_ \<lparr> pdeFrame= _, pdeParity= _, pdeDomain= _, pdeCacheable= _, pdeGlobal= _, pdeRights= _ \<rparr>")
where
  "SectionPDE_ \<lparr> pdeFrame= v0, pdeParity= v1, pdeDomain= v2, pdeCacheable= v3, pdeGlobal= v4, pdeRights= v5 \<rparr> == SectionPDE v0 v1 v2 v3 v4 v5"

abbreviation (input)
  SuperSectionPDE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pde" ("SuperSectionPDE'_ \<lparr> pdeFrame= _, pdeParity= _, pdeCacheable= _, pdeGlobal= _, pdeRights= _ \<rparr>")
where
  "SuperSectionPDE_ \<lparr> pdeFrame= v0, pdeParity= v1, pdeCacheable= v2, pdeGlobal= v3, pdeRights= v4 \<rparr> == SuperSectionPDE v0 v1 v2 v3 v4"

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
    PageTablePDE v0 v1 v2 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isSectionPDE :: "pde \<Rightarrow> bool"
where
 "isSectionPDE v \<equiv> case v of
    SectionPDE v0 v1 v2 v3 v4 v5 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isSuperSectionPDE :: "pde \<Rightarrow> bool"
where
 "isSuperSectionPDE v \<equiv> case v of
    SuperSectionPDE v0 v1 v2 v3 v4 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype pte =
    InvalidPTE
  | LargePagePTE paddr bool bool vmrights
  | SmallPagePTE paddr bool bool vmrights

primrec
  pteFrame :: "pte \<Rightarrow> paddr"
where
  "pteFrame (LargePagePTE v0 v1 v2 v3) = v0"
| "pteFrame (SmallPagePTE v0 v1 v2 v3) = v0"

primrec
  pteGlobal :: "pte \<Rightarrow> bool"
where
  "pteGlobal (LargePagePTE v0 v1 v2 v3) = v2"
| "pteGlobal (SmallPagePTE v0 v1 v2 v3) = v2"

primrec
  pteCacheable :: "pte \<Rightarrow> bool"
where
  "pteCacheable (LargePagePTE v0 v1 v2 v3) = v1"
| "pteCacheable (SmallPagePTE v0 v1 v2 v3) = v1"

primrec
  pteRights :: "pte \<Rightarrow> vmrights"
where
  "pteRights (LargePagePTE v0 v1 v2 v3) = v3"
| "pteRights (SmallPagePTE v0 v1 v2 v3) = v3"

primrec
  pteFrame_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteFrame_update f (LargePagePTE v0 v1 v2 v3) = LargePagePTE (f v0) v1 v2 v3"
| "pteFrame_update f (SmallPagePTE v0 v1 v2 v3) = SmallPagePTE (f v0) v1 v2 v3"

primrec
  pteGlobal_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteGlobal_update f (LargePagePTE v0 v1 v2 v3) = LargePagePTE v0 v1 (f v2) v3"
| "pteGlobal_update f (SmallPagePTE v0 v1 v2 v3) = SmallPagePTE v0 v1 (f v2) v3"

primrec
  pteCacheable_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteCacheable_update f (LargePagePTE v0 v1 v2 v3) = LargePagePTE v0 (f v1) v2 v3"
| "pteCacheable_update f (SmallPagePTE v0 v1 v2 v3) = SmallPagePTE v0 (f v1) v2 v3"

primrec
  pteRights_update :: "(vmrights \<Rightarrow> vmrights) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteRights_update f (LargePagePTE v0 v1 v2 v3) = LargePagePTE v0 v1 v2 (f v3)"
| "pteRights_update f (SmallPagePTE v0 v1 v2 v3) = SmallPagePTE v0 v1 v2 (f v3)"

abbreviation (input)
  LargePagePTE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pte" ("LargePagePTE'_ \<lparr> pteFrame= _, pteCacheable= _, pteGlobal= _, pteRights= _ \<rparr>")
where
  "LargePagePTE_ \<lparr> pteFrame= v0, pteCacheable= v1, pteGlobal= v2, pteRights= v3 \<rparr> == LargePagePTE v0 v1 v2 v3"

abbreviation (input)
  SmallPagePTE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pte" ("SmallPagePTE'_ \<lparr> pteFrame= _, pteCacheable= _, pteGlobal= _, pteRights= _ \<rparr>")
where
  "SmallPagePTE_ \<lparr> pteFrame= v0, pteCacheable= v1, pteGlobal= v2, pteRights= v3 \<rparr> == SmallPagePTE v0 v1 v2 v3"

definition
  isInvalidPTE :: "pte \<Rightarrow> bool"
where
 "isInvalidPTE v \<equiv> case v of
    InvalidPTE \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isLargePagePTE :: "pte \<Rightarrow> bool"
where
 "isLargePagePTE v \<equiv> case v of
    LargePagePTE v0 v1 v2 v3 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isSmallPagePTE :: "pte \<Rightarrow> bool"
where
 "isSmallPagePTE v \<equiv> case v of
    SmallPagePTE v0 v1 v2 v3 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype vmattributes =
    VMAttributes bool bool

primrec
  armParityEnabled :: "vmattributes \<Rightarrow> bool"
where
  "armParityEnabled (VMAttributes v0 v1) = v1"

primrec
  armPageCacheable :: "vmattributes \<Rightarrow> bool"
where
  "armPageCacheable (VMAttributes v0 v1) = v0"

primrec
  armParityEnabled_update :: "(bool \<Rightarrow> bool) \<Rightarrow> vmattributes \<Rightarrow> vmattributes"
where
  "armParityEnabled_update f (VMAttributes v0 v1) = VMAttributes v0 (f v1)"

primrec
  armPageCacheable_update :: "(bool \<Rightarrow> bool) \<Rightarrow> vmattributes \<Rightarrow> vmattributes"
where
  "armPageCacheable_update f (VMAttributes v0 v1) = VMAttributes (f v0) v1"

abbreviation (input)
  VMAttributes_trans :: "(bool) \<Rightarrow> (bool) \<Rightarrow> vmattributes" ("VMAttributes'_ \<lparr> armPageCacheable= _, armParityEnabled= _ \<rparr>")
where
  "VMAttributes_ \<lparr> armPageCacheable= v0, armParityEnabled= v1 \<rparr> == VMAttributes v0 v1"

lemma armParityEnabled_armParityEnabled_update [simp]:
  "armParityEnabled (armParityEnabled_update f v) = f (armParityEnabled v)"
  by (cases v) simp

lemma armParityEnabled_armPageCacheable_update [simp]:
  "armParityEnabled (armPageCacheable_update f v) = armParityEnabled v"
  by (cases v) simp

lemma armPageCacheable_armParityEnabled_update [simp]:
  "armPageCacheable (armParityEnabled_update f v) = armPageCacheable v"
  by (cases v) simp

lemma armPageCacheable_armPageCacheable_update [simp]:
  "armPageCacheable (armPageCacheable_update f v) = f (armPageCacheable v)"
  by (cases v) simp

definition
fromPAddr :: "paddr \<Rightarrow> machine_word"
where
"fromPAddr \<equiv> Platform.fromPAddr"

definition
pageColourBits :: "nat"
where
"pageColourBits \<equiv> Platform.pageColourBits"

definition
setInterruptMode :: "irq \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> unit machine_monad"
where
"setInterruptMode arg1 arg2 arg3 \<equiv> return ()"

definition
clearExMonitor :: "unit machine_monad"
where
"clearExMonitor\<equiv> return ()"

definition
pdBits :: "nat"
where
"pdBits \<equiv> pageBits + 2"

definition
ptBits :: "nat"
where
"ptBits \<equiv> pageBits - 2"


(* vmrights instance proofs *)
(*<*)
instantiation vmrights :: enum begin
definition
  enum_vmrights: "enum_class.enum \<equiv> 
    [ 
      VMNoAccess,
      VMKernelOnly,
      VMReadOnly,
      VMReadWrite
    ]"

definition
  "enum_class.enum_all (P :: vmrights \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: vmrights \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_vmrights enum_all_vmrights_def enum_ex_vmrights_def)
  apply fast
  done
end

instantiation vmrights :: enum_alt
begin
definition
  enum_alt_vmrights: "enum_alt \<equiv> 
    alt_from_ord (enum :: vmrights list)"
instance ..
end

instantiation vmrights :: enumeration_both
begin
instance by (intro_classes, simp add: enum_alt_vmrights)
end

(*>*)


definition
wordFromPDE :: "pde \<Rightarrow> machine_word"
where
"wordFromPDE x0\<equiv> (case x0 of
    InvalidPDE \<Rightarrow>    0
  | (PageTablePDE table parity domain) \<Rightarrow>    1 ||
    (fromIntegral table && 0xfffffc00) ||
    (if parity then (1 << 9) else 0) ||
    ((domain && 0xf) `~shiftL~` 5)
  | (SectionPDE frame parity domain cacheable global rights) \<Rightarrow>    2 ||
    (fromIntegral frame && 0xfff00000) ||
    (if parity then (1 << 9) else 0) ||
    (if cacheable then (1 << 2) || (1 << 3) else 0) ||
    ((domain && 0xf) `~shiftL~` 5) ||
    (if global then 0 else bit 17) ||
    (fromIntegral $ fromEnum rights `~shiftL~` 10)
  | (SuperSectionPDE frame parity cacheable global rights) \<Rightarrow>    2 ||
    (1 << 18) ||
    (fromIntegral frame && 0xff000000) ||
    (if parity then (1 << 9) else 0) ||
    (if cacheable then (1 << 2) || (1 << 3) else 0) ||
    (if global then 0 else bit 17) ||
    (fromIntegral $ fromEnum rights `~shiftL~` 10)
  )"

definition
wordFromPTE :: "pte \<Rightarrow> machine_word"
where
"wordFromPTE x0\<equiv> (case x0 of
    InvalidPTE \<Rightarrow>    0
  | (LargePagePTE frame cacheable _ rights) \<Rightarrow>    1 ||
    (fromIntegral frame && 0xffff0000) ||
    (if cacheable then (1 << 2) || (1 << 3) else 0) ||
    (fromIntegral $ fromEnum rights * 0x55 `~shiftL~` 4)
  | (SmallPagePTE frame cacheable _ rights) \<Rightarrow>    2 ||
    (fromIntegral frame && 0xfffff000) ||
    (if cacheable then (1 << 2) || (1 << 3) else 0) ||
    (fromIntegral $ fromEnum rights * 0x55 `~shiftL~` 4)
  )"


end
