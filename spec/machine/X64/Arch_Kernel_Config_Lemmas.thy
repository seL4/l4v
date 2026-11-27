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

context Arch begin global_naming X64

(* Make sure that ioapicIRQLines_def inside Arch later takes precedence over Kernel_C.ioapicIRQLines_def *)
lemmas ioapicIRQLines_def = ioapicIRQLines_def

end

end
