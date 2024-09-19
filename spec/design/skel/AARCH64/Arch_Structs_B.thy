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
  MachineExports
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Model/StateData/AARCH64.hs CONTEXT AARCH64_H ONLY ArmVSpaceRegionUse

#INCLUDE_HASKELL SEL4/API/Invocation/AARCH64.hs CONTEXT AARCH64_H ONLY FlushType

#INCLUDE_HASKELL SEL4/Object/Structures/AARCH64.hs CONTEXT AARCH64_H ONLY ArchTcbFlag archTcbFlagToWord

end

end
