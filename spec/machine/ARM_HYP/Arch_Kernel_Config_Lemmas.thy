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

context Arch begin global_naming ARM_HYP

(* note: 25 = pageBitsForSize ARMSuperSection, we do not have access to ASpec at this point *)
lemma physBase_aligned:
  "is_aligned physBase 25"
  by (simp add: is_aligned_def Kernel_Config.physBase_def)

end
end
