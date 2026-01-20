(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Architecture-specific data types shared by design and abstract specs. *)

chapter "Common, Architecture-Specific Data Types"

theory Arch_Structs_B
imports
  Structs_B
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Model/StateData/ARM.lhs CONTEXT ARM_HYP_H ONLY ArmVSpaceRegionUse
#INCLUDE_HASKELL SEL4/Object/Structures/ARM.lhs ONLY parseTimeArg

end
end
