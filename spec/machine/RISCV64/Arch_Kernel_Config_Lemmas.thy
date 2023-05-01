(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Architecture-specific lemmas constraining Kernel_Config definitions *)

theory Arch_Kernel_Config_Lemmas
imports
  Kernel_Config_Lemmas
  Platform
begin

context Arch begin global_naming RISCV64

lemma pptrBase_kernelELFBase:
  "pptrBase < kernelELFBase"
  by (simp add: pptrBase_def canonical_bit_def kernelELFBase_def kernelELFPAddrBase_def pptrTop_def
                Kernel_Config.physBase_def mask_def)

(* 12 in this lemma and below is pageBits, which is not yet defined in this theory.
   Definition will be folded and the lemmas shadowed in AInvs. *)
lemma is_page_aligned_physBase:
  "is_aligned physBase 12"
  by (simp add: Kernel_Config.physBase_def is_aligned_def)

(* 22 is kernel_window_bits, defined in Init_A. To be folded in AInvs. *)
lemma kernel_window_sufficient:
  "pptrBase + (1 << 22) \<le> kernelELFBase"
  unfolding pptrBase_def canonical_bit_def kernelELFBase_def kernelELFPAddrBase_def pptrTop_def
  by (simp add: mask_def Kernel_Config.physBase_def)

lemma kernel_elf_window_at_least_page:
  "kernelELFBase + 2 ^ 12 \<le> kdevBase"
  unfolding kernelELFBase_def kernelELFPAddrBase_def kdevBase_def pptrTop_def
  by (simp add: mask_def Kernel_Config.physBase_def)

(* This doesn't follow from alignment, because we need <, not \<le> *)
lemma kernelELFBase_no_overflow:
  "kernelELFBase < kernelELFBase + 2 ^ 12"
  unfolding kernelELFBase_def kernelELFPAddrBase_def pptrTop_def
  by (simp add: mask_def Kernel_Config.physBase_def)

end
end
