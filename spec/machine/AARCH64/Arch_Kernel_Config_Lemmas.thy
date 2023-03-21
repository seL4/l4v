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

context Arch begin global_naming AARCH64

lemma pptrBase_kernelELFBase:
  "pptrBase < kernelELFBase"
  by (simp add: pptrBase_def canonical_bit_def kernelELFBase_def kernelELFPAddrBase_def pptrTop_def
                Kernel_Config.physBase_def mask_def)

end
end
