(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Physical Memory Structure"

theory PSpaceStruct_H
imports
  Structures_H
  "Lib.DataMap"
begin

text \<open>Helper Functions\<close>

definition
  ptrBits_def[simp]:
 "ptrBits \<equiv> to_bl"

#INCLUDE_HASKELL SEL4/Model/PSpace.lhs ONLY ptrBitsForSize

text \<open>Physical Memory Structures\<close>

#INCLUDE_HASKELL SEL4/Model/PSpace.lhs Data.Map=DataMap ONLY PSpace

end
