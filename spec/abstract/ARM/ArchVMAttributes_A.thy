(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Definition of architecture-dependent VM attributes. *)

theory ArchVMAttributes_A
imports
  ExecSpec.MachineExports
begin

context Arch begin global_naming ARM_A

(* Union of attributes and non-seL4 rights that the kernel uses on pages and page tables,
   including kernel-only attributes. Not all are reachable via attribs_from_word. *)
datatype vm_attribute = ParityEnabled | PageCacheable | Global | XNever
type_synonym vm_attributes = "vm_attribute set"

type_synonym arch_raw_vmattrs = word32

definition
  attribs_from_word :: "word32 \<Rightarrow> vm_attributes" where
  "attribs_from_word w \<equiv>
    let V = (if w !!0 then {PageCacheable} else {});
      V' = (if w!!1 then insert ParityEnabled V else V)
    in if w!!2 then insert XNever V' else V'"

definition
  attribs_to_word :: "vm_attributes \<Rightarrow> word32" where
  "attribs_to_word attribs \<equiv>
    let V = (if PageCacheable \<in> attribs then 1 else 0);
      V' = (if ParityEnabled \<in> attribs then V + 2 else V)
    in if XNever \<in> attribs then V' + 4 else V' "

definition
  validate_vm_attributes :: "word32 \<Rightarrow> vmpage_size \<Rightarrow> word32"  where
  "validate_vm_attributes attr sz \<equiv> case sz of
    ARM.ARMSmallPage \<Rightarrow> attribs_to_word (attribs_from_word attr - {Global, ParityEnabled})
  | ARM.ARMLargePage \<Rightarrow> attribs_to_word (attribs_from_word attr - {Global, ParityEnabled})
  | ARM.ARMSection \<Rightarrow> attribs_to_word (attribs_from_word attr - {Global})
  | ARM.ARMSuperSection \<Rightarrow> attribs_to_word (attribs_from_word attr - {Global})"

definition
  validate_pt_vm_attributes :: "word32 \<Rightarrow> word32"  where
  "validate_pt_vm_attributes attr \<equiv> attribs_to_word (attribs_from_word attr \<inter> {ParityEnabled})"

definition default_vmattrs :: "word32" where "default_vmattrs \<equiv> 3"

end
end