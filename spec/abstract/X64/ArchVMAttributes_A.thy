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

context Arch begin arch_global_naming (A)

datatype table_attr = Accessed | CacheDisabled | WriteThrough | ExecuteDisable
type_synonym table_attrs = "table_attr set"

(* Union of attributes and non-seL4 rights that the kernel uses on pages and page tables,
   including kernel-only attributes. Not all are reachable via attribs_from_word. *)
datatype vm_attribute = PTAttr table_attr | Global | PAT | Dirty
type_synonym vm_attributes = "vm_attribute set"

type_synonym arch_raw_vmattrs = word32

text \<open>Decode a user argument word describing the kind of VM attributes a mapping is to have.\<close>
definition attribs_from_word :: "machine_word \<Rightarrow> vm_attributes" where
  "attribs_from_word w \<equiv>
     let V = (if w !! 0 then {PTAttr WriteThrough} else {});
         V' = (if w !! 1 then insert (PTAttr CacheDisabled) V else V)
     in if w !! 2 then insert PAT V' else V'"

definition attribs_to_word :: "vm_attributes \<Rightarrow> machine_word" where
  "attribs_to_word attribs \<equiv>
     let V = (if PTAttr WriteThrough \<in> attribs then 1 else 0);
         V' = (if PTAttr CacheDisabled \<in> attribs then V + 2 else V)
     in if PAT \<in> attribs then V' + 4 else V'"

end

end