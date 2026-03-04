(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Definition of architecture-dependent VM attribute validation. *)

theory ArchVMAttributes_D
imports
  ASpec.ArchVMAttributes_A
begin

context Arch begin arch_global_naming (A)

definition validate_vm_attributes :: "machine_word \<Rightarrow> vmpage_size \<Rightarrow> machine_word"  where
  "validate_vm_attributes attr sz \<equiv> case sz of
     ARMSmallPage \<Rightarrow> attribs_to_word (attribs_from_word attr - {Global, ParityEnabled})
   | ARMLargePage \<Rightarrow> attribs_to_word (attribs_from_word attr - {Global, ParityEnabled})
   | ARMSection \<Rightarrow> attribs_to_word (attribs_from_word attr - {Global})
   | ARMSuperSection \<Rightarrow> attribs_to_word (attribs_from_word attr - {Global})"

definition validate_pt_vm_attributes :: "machine_word \<Rightarrow> machine_word"  where
  "validate_pt_vm_attributes attr \<equiv> attribs_to_word (attribs_from_word attr \<inter> {ParityEnabled})"

lemma validate_vm_attributes_0[simp]:
  "validate_vm_attributes 0 vmsz = 0"
  unfolding validate_vm_attributes_def
  by (clarsimp simp: attribs_from_word_def attribs_to_word_def split: vmpage_size.splits)

lemma validate_pt_vm_attributes_0[simp]:
  "validate_pt_vm_attributes 0 = 0"
  unfolding validate_pt_vm_attributes_def
  by (simp add: attribs_from_word_def attribs_to_word_def)

end
end