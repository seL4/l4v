(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Definition of architecture-dependent VM attribute validation. *)

theory ArchVMAttributes_D
imports
  ASpec.ArchVMAttributes_A
begin

context Arch begin arch_global_naming (A)

(* attribs_from_word/attribs_to_word do not check for Global, hence this definition will remove
   Global, as intended, including any other unused bits that might be set. *)
definition validate_vm_attributes :: "machine_word \<Rightarrow> vmpage_size \<Rightarrow> machine_word"  where
  "validate_vm_attributes attr sz \<equiv> attribs_to_word (attribs_from_word attr)"

definition validate_pt_vm_attributes :: "machine_word \<Rightarrow> machine_word"  where
  "validate_pt_vm_attributes attr \<equiv> attr"

lemma validate_vm_attributes_0[simp]:
  "validate_vm_attributes 0 vmsz = 0"
  unfolding validate_vm_attributes_def
  by (clarsimp simp: attribs_from_word_def attribs_to_word_def)

lemma validate_pt_vm_attributes_0[simp]:
  "validate_pt_vm_attributes 0 = 0"
  unfolding validate_pt_vm_attributes_def
  by (simp add: attribs_from_word_def attribs_to_word_def)

end

end
