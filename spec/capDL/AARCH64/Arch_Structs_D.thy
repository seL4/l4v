(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Arch_Structs_D
imports
  ExecSpec.MachineTypes
begin

context Arch begin arch_global_naming (D)

(* Sizes are duplicated from ASpec and must be kept in sync *)

definition slot_bits_cdl :: nat where
  "slot_bits_cdl \<equiv> 5"

definition endpoint_bits_cdl :: nat where
  "endpoint_bits_cdl \<equiv> 4"

definition tcb_bits_cdl :: nat where
  "tcb_bits_cdl \<equiv> 11"

definition ntfn_bits_cdl :: nat where
  "ntfn_bits_cdl \<equiv> 5"

definition pageBits_cdl :: "nat" where
  "pageBits_cdl \<equiv> pageBits"

end

(* Machine-level base names *)
context Arch begin arch_global_naming

lemmas vmpage_size_simps = vmpage_size.simps

definition pageForPageBits :: "nat \<Rightarrow> vmpage_size" where
  "pageForPageBits bits \<equiv>
     if bits = pageBits then ARMSmallPage
     else if bits = pageBits + ptTranslationBits NormalPT_T then ARMLargePage
     else if bits = pageBits + 2 * ptTranslationBits NormalPT_T then ARMHugePage
     else undefined"

lemma pageForPageBits_pageBitsForSize[simp]:
  "pageForPageBits (pageBitsForSize sz) = sz"
  unfolding pageForPageBits_def pageBitsForSize_def
  by (cases sz; simp add: ptTranslationBits_def)

definition pt_size_index :: nat where
  "pt_size_index \<equiv> 9"

(* These names are expected by other architectures, but unused for AARCH64 *)

definition pd_size_index :: nat where
  "pd_size_index \<equiv> undefined"

definition smallPageBits :: nat where
  "smallPageBits = undefined"

definition largePageBits :: nat where
  "largePageBits = undefined"

definition sectionBits :: nat where
  "sectionBits = undefined"

definition superSectionBits :: nat where
  "superSectionBits = undefined"

definition pt_slot_vaddr_mask :: machine_word where
  "pt_slot_vaddr_mask = undefined"

end
end
