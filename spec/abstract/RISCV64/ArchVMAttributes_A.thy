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

(* Union of attributes and non-seL4 rights that the kernel uses on pages and page tables,
   including kernel-only attributes. Not all are reachable via attribs_from_word. *)
datatype vm_attribute = Global | Execute | User
type_synonym vm_attributes = "vm_attribute set"

type_synonym arch_raw_vmattrs = machine_word

definition attribs_from_word :: "machine_word \<Rightarrow> vm_attributes" where
  "attribs_from_word w \<equiv> if \<not> w !! 0 then {Execute} else {}"

definition attribs_to_word :: "vm_attributes \<Rightarrow> machine_word" where
  "attribs_to_word attribs \<equiv> if Execute \<in> attribs then 0 else 1"

(* sanity check *)
lemma attribs_from_to_word:
  "attribs_from_word (attribs_to_word A) = A - {Global, User}"
  unfolding attribs_from_word_def attribs_to_word_def
  using vm_attribute.exhaust
  by clarsimp
     blast

end

end