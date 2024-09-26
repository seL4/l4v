(*
 * Copyright 2014, General Dynamics C4 Systems
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

#INCLUDE_HASKELL SEL4/Model/StateData/ARM.lhs CONTEXT ARM_H ONLY ArmVSpaceRegionUse

#INCLUDE_HASKELL SEL4/Object/Structures/ARM.lhs CONTEXT ARM_H ONLY ArchTcbFlag archTcbFlagToWord

end
end
