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
  "../../machine/ARM/MachineOps"
  State_H
begin
context Arch begin global_naming ARM_H

type_synonym irq = "Platform.ARM.irq"

type_synonym paddr = "Platform.ARM.paddr"

datatype vmrights =
    VMNoAccess
  | VMKernelOnly
  | VMReadOnly
  | VMReadWrite

datatype pde =
    InvalidPDE
  | PageTablePDE paddr bool machine_word
  | SectionPDE paddr bool machine_word bool bool bool vmrights
  | SuperSectionPDE paddr bool bool bool bool vmrights

primrec
  pdeCacheable :: "pde \<Rightarrow> bool"
where
  "pdeCacheable (SuperSectionPDE v0 v1 v2 v3 v4 v5) = v2"
| "pdeCacheable (SectionPDE v0 v1 v2 v3 v4 v5 v6) = v3"

primrec
  pdeTable :: "pde \<Rightarrow> paddr"
where
  "pdeTable (PageTablePDE v0 v1 v2) = v0"

primrec
  pdeFrame :: "pde \<Rightarrow> paddr"
where
  "pdeFrame (SuperSectionPDE v0 v1 v2 v3 v4 v5) = v0"
| "pdeFrame (SectionPDE v0 v1 v2 v3 v4 v5 v6) = v0"

primrec
  pdeExecuteNever :: "pde \<Rightarrow> bool"
where
  "pdeExecuteNever (SuperSectionPDE v0 v1 v2 v3 v4 v5) = v4"
| "pdeExecuteNever (SectionPDE v0 v1 v2 v3 v4 v5 v6) = v5"

primrec
  pdeGlobal :: "pde \<Rightarrow> bool"
where
  "pdeGlobal (SuperSectionPDE v0 v1 v2 v3 v4 v5) = v3"
| "pdeGlobal (SectionPDE v0 v1 v2 v3 v4 v5 v6) = v4"

primrec
  pdeParity :: "pde \<Rightarrow> bool"
where
  "pdeParity (PageTablePDE v0 v1 v2) = v1"
| "pdeParity (SuperSectionPDE v0 v1 v2 v3 v4 v5) = v1"
| "pdeParity (SectionPDE v0 v1 v2 v3 v4 v5 v6) = v1"

primrec
  pdeDomain :: "pde \<Rightarrow> machine_word"
where
  "pdeDomain (PageTablePDE v0 v1 v2) = v2"
| "pdeDomain (SectionPDE v0 v1 v2 v3 v4 v5 v6) = v2"

primrec
  pdeRights :: "pde \<Rightarrow> vmrights"
where
  "pdeRights (SuperSectionPDE v0 v1 v2 v3 v4 v5) = v5"
| "pdeRights (SectionPDE v0 v1 v2 v3 v4 v5 v6) = v6"

primrec
  pdeCacheable_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeCacheable_update f (SuperSectionPDE v0 v1 v2 v3 v4 v5) = SuperSectionPDE v0 v1 (f v2) v3 v4 v5"
| "pdeCacheable_update f (SectionPDE v0 v1 v2 v3 v4 v5 v6) = SectionPDE v0 v1 v2 (f v3) v4 v5 v6"

primrec
  pdeTable_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeTable_update f (PageTablePDE v0 v1 v2) = PageTablePDE (f v0) v1 v2"

primrec
  pdeFrame_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeFrame_update f (SuperSectionPDE v0 v1 v2 v3 v4 v5) = SuperSectionPDE (f v0) v1 v2 v3 v4 v5"
| "pdeFrame_update f (SectionPDE v0 v1 v2 v3 v4 v5 v6) = SectionPDE (f v0) v1 v2 v3 v4 v5 v6"

primrec
  pdeExecuteNever_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeExecuteNever_update f (SuperSectionPDE v0 v1 v2 v3 v4 v5) = SuperSectionPDE v0 v1 v2 v3 (f v4) v5"
| "pdeExecuteNever_update f (SectionPDE v0 v1 v2 v3 v4 v5 v6) = SectionPDE v0 v1 v2 v3 v4 (f v5) v6"

primrec
  pdeGlobal_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeGlobal_update f (SuperSectionPDE v0 v1 v2 v3 v4 v5) = SuperSectionPDE v0 v1 v2 (f v3) v4 v5"
| "pdeGlobal_update f (SectionPDE v0 v1 v2 v3 v4 v5 v6) = SectionPDE v0 v1 v2 v3 (f v4) v5 v6"

primrec
  pdeParity_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeParity_update f (PageTablePDE v0 v1 v2) = PageTablePDE v0 (f v1) v2"
| "pdeParity_update f (SuperSectionPDE v0 v1 v2 v3 v4 v5) = SuperSectionPDE v0 (f v1) v2 v3 v4 v5"
| "pdeParity_update f (SectionPDE v0 v1 v2 v3 v4 v5 v6) = SectionPDE v0 (f v1) v2 v3 v4 v5 v6"

primrec
  pdeDomain_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeDomain_update f (PageTablePDE v0 v1 v2) = PageTablePDE v0 v1 (f v2)"
| "pdeDomain_update f (SectionPDE v0 v1 v2 v3 v4 v5 v6) = SectionPDE v0 v1 (f v2) v3 v4 v5 v6"

primrec
  pdeRights_update :: "(vmrights \<Rightarrow> vmrights) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeRights_update f (SuperSectionPDE v0 v1 v2 v3 v4 v5) = SuperSectionPDE v0 v1 v2 v3 v4 (f v5)"
| "pdeRights_update f (SectionPDE v0 v1 v2 v3 v4 v5 v6) = SectionPDE v0 v1 v2 v3 v4 v5 (f v6)"

abbreviation (input)
  PageTablePDE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (machine_word) \<Rightarrow> pde" ("PageTablePDE'_ \<lparr> pdeTable= _, pdeParity= _, pdeDomain= _ \<rparr>")
where
  "PageTablePDE_ \<lparr> pdeTable= v0, pdeParity= v1, pdeDomain= v2 \<rparr> == PageTablePDE v0 v1 v2"

abbreviation (input)
  SectionPDE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (machine_word) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pde" ("SectionPDE'_ \<lparr> pdeFrame= _, pdeParity= _, pdeDomain= _, pdeCacheable= _, pdeGlobal= _, pdeExecuteNever= _, pdeRights= _ \<rparr>")
where
  "SectionPDE_ \<lparr> pdeFrame= v0, pdeParity= v1, pdeDomain= v2, pdeCacheable= v3, pdeGlobal= v4, pdeExecuteNever= v5, pdeRights= v6 \<rparr> == SectionPDE v0 v1 v2 v3 v4 v5 v6"

abbreviation (input)
  SuperSectionPDE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pde" ("SuperSectionPDE'_ \<lparr> pdeFrame= _, pdeParity= _, pdeCacheable= _, pdeGlobal= _, pdeExecuteNever= _, pdeRights= _ \<rparr>")
where
  "SuperSectionPDE_ \<lparr> pdeFrame= v0, pdeParity= v1, pdeCacheable= v2, pdeGlobal= v3, pdeExecuteNever= v4, pdeRights= v5 \<rparr> == SuperSectionPDE v0 v1 v2 v3 v4 v5"

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
    SectionPDE v0 v1 v2 v3 v4 v5 v6 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isSuperSectionPDE :: "pde \<Rightarrow> bool"
where
 "isSuperSectionPDE v \<equiv> case v of
    SuperSectionPDE v0 v1 v2 v3 v4 v5 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype pte =
    InvalidPTE
  | LargePagePTE paddr bool bool bool vmrights
  | SmallPagePTE paddr bool bool bool vmrights

primrec
  pteFrame :: "pte \<Rightarrow> paddr"
where
  "pteFrame (LargePagePTE v0 v1 v2 v3 v4) = v0"
| "pteFrame (SmallPagePTE v0 v1 v2 v3 v4) = v0"

primrec
  pteGlobal :: "pte \<Rightarrow> bool"
where
  "pteGlobal (LargePagePTE v0 v1 v2 v3 v4) = v2"
| "pteGlobal (SmallPagePTE v0 v1 v2 v3 v4) = v2"

primrec
  pteRights :: "pte \<Rightarrow> vmrights"
where
  "pteRights (LargePagePTE v0 v1 v2 v3 v4) = v4"
| "pteRights (SmallPagePTE v0 v1 v2 v3 v4) = v4"

primrec
  pteCacheable :: "pte \<Rightarrow> bool"
where
  "pteCacheable (LargePagePTE v0 v1 v2 v3 v4) = v1"
| "pteCacheable (SmallPagePTE v0 v1 v2 v3 v4) = v1"

primrec
  pteExecuteNever :: "pte \<Rightarrow> bool"
where
  "pteExecuteNever (LargePagePTE v0 v1 v2 v3 v4) = v3"
| "pteExecuteNever (SmallPagePTE v0 v1 v2 v3 v4) = v3"

primrec
  pteFrame_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteFrame_update f (LargePagePTE v0 v1 v2 v3 v4) = LargePagePTE (f v0) v1 v2 v3 v4"
| "pteFrame_update f (SmallPagePTE v0 v1 v2 v3 v4) = SmallPagePTE (f v0) v1 v2 v3 v4"

primrec
  pteGlobal_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteGlobal_update f (LargePagePTE v0 v1 v2 v3 v4) = LargePagePTE v0 v1 (f v2) v3 v4"
| "pteGlobal_update f (SmallPagePTE v0 v1 v2 v3 v4) = SmallPagePTE v0 v1 (f v2) v3 v4"

primrec
  pteRights_update :: "(vmrights \<Rightarrow> vmrights) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteRights_update f (LargePagePTE v0 v1 v2 v3 v4) = LargePagePTE v0 v1 v2 v3 (f v4)"
| "pteRights_update f (SmallPagePTE v0 v1 v2 v3 v4) = SmallPagePTE v0 v1 v2 v3 (f v4)"

primrec
  pteCacheable_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteCacheable_update f (LargePagePTE v0 v1 v2 v3 v4) = LargePagePTE v0 (f v1) v2 v3 v4"
| "pteCacheable_update f (SmallPagePTE v0 v1 v2 v3 v4) = SmallPagePTE v0 (f v1) v2 v3 v4"

primrec
  pteExecuteNever_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteExecuteNever_update f (LargePagePTE v0 v1 v2 v3 v4) = LargePagePTE v0 v1 v2 (f v3) v4"
| "pteExecuteNever_update f (SmallPagePTE v0 v1 v2 v3 v4) = SmallPagePTE v0 v1 v2 (f v3) v4"

abbreviation (input)
  LargePagePTE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pte" ("LargePagePTE'_ \<lparr> pteFrame= _, pteCacheable= _, pteGlobal= _, pteExecuteNever= _, pteRights= _ \<rparr>")
where
  "LargePagePTE_ \<lparr> pteFrame= v0, pteCacheable= v1, pteGlobal= v2, pteExecuteNever= v3, pteRights= v4 \<rparr> == LargePagePTE v0 v1 v2 v3 v4"

abbreviation (input)
  SmallPagePTE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pte" ("SmallPagePTE'_ \<lparr> pteFrame= _, pteCacheable= _, pteGlobal= _, pteExecuteNever= _, pteRights= _ \<rparr>")
where
  "SmallPagePTE_ \<lparr> pteFrame= v0, pteCacheable= v1, pteGlobal= v2, pteExecuteNever= v3, pteRights= v4 \<rparr> == SmallPagePTE v0 v1 v2 v3 v4"

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
    LargePagePTE v0 v1 v2 v3 v4 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isSmallPagePTE :: "pte \<Rightarrow> bool"
where
 "isSmallPagePTE v \<equiv> case v of
    SmallPagePTE v0 v1 v2 v3 v4 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype vmattributes =
    VMAttributes bool bool bool

primrec
  armParityEnabled :: "vmattributes \<Rightarrow> bool"
where
  "armParityEnabled (VMAttributes v0 v1 v2) = v1"

primrec
  armExecuteNever :: "vmattributes \<Rightarrow> bool"
where
  "armExecuteNever (VMAttributes v0 v1 v2) = v2"

primrec
  armPageCacheable :: "vmattributes \<Rightarrow> bool"
where
  "armPageCacheable (VMAttributes v0 v1 v2) = v0"

primrec
  armParityEnabled_update :: "(bool \<Rightarrow> bool) \<Rightarrow> vmattributes \<Rightarrow> vmattributes"
where
  "armParityEnabled_update f (VMAttributes v0 v1 v2) = VMAttributes v0 (f v1) v2"

primrec
  armExecuteNever_update :: "(bool \<Rightarrow> bool) \<Rightarrow> vmattributes \<Rightarrow> vmattributes"
where
  "armExecuteNever_update f (VMAttributes v0 v1 v2) = VMAttributes v0 v1 (f v2)"

primrec
  armPageCacheable_update :: "(bool \<Rightarrow> bool) \<Rightarrow> vmattributes \<Rightarrow> vmattributes"
where
  "armPageCacheable_update f (VMAttributes v0 v1 v2) = VMAttributes (f v0) v1 v2"

abbreviation (input)
  VMAttributes_trans :: "(bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> vmattributes" ("VMAttributes'_ \<lparr> armPageCacheable= _, armParityEnabled= _, armExecuteNever= _ \<rparr>")
where
  "VMAttributes_ \<lparr> armPageCacheable= v0, armParityEnabled= v1, armExecuteNever= v2 \<rparr> == VMAttributes v0 v1 v2"

lemma armParityEnabled_armParityEnabled_update [simp]:
  "armParityEnabled (armParityEnabled_update f v) = f (armParityEnabled v)"
  by (cases v) simp

lemma armParityEnabled_armExecuteNever_update [simp]:
  "armParityEnabled (armExecuteNever_update f v) = armParityEnabled v"
  by (cases v) simp

lemma armParityEnabled_armPageCacheable_update [simp]:
  "armParityEnabled (armPageCacheable_update f v) = armParityEnabled v"
  by (cases v) simp

lemma armExecuteNever_armParityEnabled_update [simp]:
  "armExecuteNever (armParityEnabled_update f v) = armExecuteNever v"
  by (cases v) simp

lemma armExecuteNever_armExecuteNever_update [simp]:
  "armExecuteNever (armExecuteNever_update f v) = f (armExecuteNever v)"
  by (cases v) simp

lemma armExecuteNever_armPageCacheable_update [simp]:
  "armExecuteNever (armPageCacheable_update f v) = armExecuteNever v"
  by (cases v) simp

lemma armPageCacheable_armParityEnabled_update [simp]:
  "armPageCacheable (armParityEnabled_update f v) = armPageCacheable v"
  by (cases v) simp

lemma armPageCacheable_armExecuteNever_update [simp]:
  "armPageCacheable (armExecuteNever_update f v) = armPageCacheable v"
  by (cases v) simp

lemma armPageCacheable_armPageCacheable_update [simp]:
  "armPageCacheable (armPageCacheable_update f v) = f (armPageCacheable v)"
  by (cases v) simp

definition
fromPAddr :: "paddr \<Rightarrow> machine_word"
where
"fromPAddr \<equiv> Platform.ARM.fromPAddr"

definition
pageColourBits :: "nat"
where
"pageColourBits \<equiv> Platform.ARM.pageColourBits"

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

definition
physBase :: "paddr"
where
"physBase \<equiv> toPAddr Platform.ARM.physBase"

definition
kernelBase :: "vptr"
where
"kernelBase \<equiv> Platform.ARM.kernelBase"


end

context begin interpretation Arch .
requalify_types vmrights
end

context Arch begin global_naming ARM_H

end
qualify ARM_H (in Arch) 
(* vmrights instance proofs *)
(*<*)
instantiation vmrights :: enum begin
interpretation Arch .
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
  by fast+
end

instantiation vmrights :: enum_alt
begin
interpretation Arch .
definition
  enum_alt_vmrights: "enum_alt \<equiv> 
    alt_from_ord (enum :: vmrights list)"
instance ..
end

instantiation vmrights :: enumeration_both
begin
interpretation Arch .
instance by (intro_classes, simp add: enum_alt_vmrights)
end

(*>*)
end_qualify
context Arch begin global_naming ARM_H


definition
wordFromPDE :: "pde \<Rightarrow> machine_word"
where
"wordFromPDE x0\<equiv> (case x0 of
    InvalidPDE \<Rightarrow>    0
  | (PageTablePDE table parity domain) \<Rightarrow>    1 ||
    (fromIntegral table && 0xfffffc00) ||
    (if parity then (1 << 9) else 0) ||
    ((domain && 0xf) `~shiftL~` 5)
  | (SectionPDE frame parity domain cacheable global xn rights) \<Rightarrow>    2 ||
    (fromIntegral frame && 0xfff00000) ||
    (if parity then (1 << 9) else 0) ||
    (if cacheable then (1 << 2) || (1 << 3) else 0) ||
    (if xn then (1 << 4) else 0) ||
    ((domain && 0xf) `~shiftL~` 5) ||
    (if global then 0 else bit 17) ||
    (fromIntegral $ fromEnum rights `~shiftL~` 10)
  | (SuperSectionPDE frame parity cacheable global xn rights) \<Rightarrow>    2 ||
    (1 << 18) ||
    (fromIntegral frame && 0xff000000) ||
    (if parity then (1 << 9) else 0) ||
    (if cacheable then (1 << 2) || (1 << 3) else 0) ||
    (if xn then (1 << 4) else 0) ||
    (if global then 0 else bit 17) ||
    (fromIntegral $ fromEnum rights `~shiftL~` 10)
  )"

definition
wordFromPTE :: "pte \<Rightarrow> machine_word"
where
"wordFromPTE x0\<equiv> (case x0 of
    InvalidPTE \<Rightarrow>    0
  | (LargePagePTE frame cacheable global xn rights) \<Rightarrow>    1 ||
    (fromIntegral frame && 0xffff0000) ||
    (if cacheable then (1 << 2) || (1 << 3) else 0) ||
    (if global then 0 else bit 11) ||
    (if xn then (1 << 15) else 0) ||
    (fromIntegral $ fromEnum rights `~shiftL~` 4)
  | (SmallPagePTE frame cacheable global xn rights) \<Rightarrow>    2 ||
    (fromIntegral frame && 0xfffff000) ||
    (if xn then 1 else 0) ||
    (if cacheable then (1 << 2) || (1 << 3) else 0) ||
    (if global then 0 else bit 11) ||
    (fromIntegral $ fromEnum rights `~shiftL~` 4)
  )"


end
end
