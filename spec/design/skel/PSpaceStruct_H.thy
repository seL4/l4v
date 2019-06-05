(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
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
