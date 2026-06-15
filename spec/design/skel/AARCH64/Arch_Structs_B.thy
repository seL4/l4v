(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Architecture-specific data types shared by design and abstract specs. *)

chapter "Common, Architecture-Specific Data Types"

theory Arch_Structs_B
imports
  Setup_Locale
  Lib.HaskellLib_H
  MachineExports
begin

context Arch begin arch_global_naming (H)

abbreviation (input) usToTicks :: "word64 \<Rightarrow> word64" where
  "usToTicks \<equiv> us_to_ticks"

#INCLUDE_HASKELL SEL4/Model/StateData/AARCH64.hs CONTEXT AARCH64_H ONLY ArmVSpaceRegionUse

#INCLUDE_HASKELL SEL4/API/Invocation/AARCH64.hs CONTEXT AARCH64_H ONLY FlushType

#INCLUDE_HASKELL SEL4/Machine/Hardware/AARCH64.hs CONTEXT AARCH64_H ONLY timerPrecision

end

arch_requalify_consts (H)
  timerPrecision

end
