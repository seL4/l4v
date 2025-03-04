(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Architecture-specific data types shared by spec and abstract. *)

chapter "Common, Architecture-Specific Data Types"

theory Arch_Structs_B
imports Main Setup_Locale MachineExports
begin
context Arch begin arch_global_naming (H)

definition usToTicks :: "word64 \<Rightarrow> word64" where
  "usToTicks \<equiv> us_to_ticks"

#INCLUDE_HASKELL SEL4/Model/StateData/ARM.lhs CONTEXT ARM_H ONLY ArmVSpaceRegionUse
#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM.lhs CONTEXT ARM_H ONLY timerPrecision

end

arch_requalify_consts (H)
  timerPrecision

end
