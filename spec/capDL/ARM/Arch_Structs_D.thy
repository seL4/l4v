(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Arch_Structs_D
  imports
    Setup_D
    ExecSpec.MachineTypes
begin

context Arch begin arch_global_naming (D)

(* Sizes are duplicated from ASpec and must be kept in sync *)

definition slot_bits_cdl :: nat where
  "slot_bits_cdl \<equiv> 4"

definition endpoint_bits_cdl :: nat where
  "endpoint_bits_cdl \<equiv> 4"

definition tcb_bits_cdl :: nat where
  "tcb_bits_cdl \<equiv> 9"

definition ntfn_bits_cdl :: nat where
  "ntfn_bits_cdl \<equiv> 4"

definition pageBits_cdl :: "nat" where
  "pageBits_cdl \<equiv> smallPageBits"

lemma pageForPageBits_pageBitsForSize[simp]:
  "pageForPageBits (pageBitsForSize pgsz) = pgsz"
  unfolding pageForPageBits_def pageBitsForSize_def
  by (cases pgsz; simp)

end

(* For capDL proofs that only work on AARCH32. This lemma only exists on ARM/ARM_HYP, but must be
   visible outside the Arch context, because many of the existing capDL proofs are currently not
   inside an Arch context. *)
lemma cdl_ARCH_AARCH32:
  "cdl_ARCH = AARCH32"
  by (simp add: cdl_ARCH_all_defs)

end