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
  "../../lib/DataMap"
begin

text {* Helper Functions *}

definition
  ptrBits_def[simp]:
 "ptrBits \<equiv> to_bl"

#INCLUDE_HASKELL SEL4/Model/PSpace.lhs ONLY ptrBitsForSize

text {* Physical Memory Structures *}

#INCLUDE_HASKELL SEL4/Model/PSpace.lhs Data.Map=DataMap ONLY PSpace

end
