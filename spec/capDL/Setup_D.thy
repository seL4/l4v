(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Setup_D
  imports
    ExecSpec.Kernel_Config
begin

(* Basic type setup for the rest of capDL *)

(* The architecture that we are modelling. *)
datatype cdl_arch = AARCH32 | AARCH64 | RISCV32 | RISCV64 | IA32 | X64

(* Older capDL versions use ARM11 instead of AARCH32. Provide an abbreviation for compatibility. *)
abbreviation (input) "ARM11 \<equiv> AARCH32"

(* Extract capDL arch from background kernel config. This is not the architecture of the capDL
   specification object presented to the system initialiser as input, but the architecture of
   the underlying capDL semantics in the current proof run. *)
definition cdl_ARCH :: cdl_arch where
  "cdl_ARCH \<equiv>
     if config_ARCH_AARCH32 then AARCH32
     else if config_ARCH_AARCH64 then AARCH64
     else if config_ARCH_RISCV32 then RISCV32
     else if config_ARCH_RISCV64 then RISCV64
     else if config_ARCH_X86_64 then X64
     else IA32"

lemmas cdl_ARCH_all_defs =
  cdl_ARCH_def
  Kernel_Config.config_ARCH_AARCH32_def
  Kernel_Config.config_ARCH_AARCH64_def
  Kernel_Config.config_ARCH_RISCV32_def
  Kernel_Config.config_ARCH_RISCV64_def
  Kernel_Config.config_ARCH_X86_64_def

end
