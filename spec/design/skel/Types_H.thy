(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
   Types visible in the API. 
*)

chapter "Types visible in the API"

theory Types_H
imports
  "./$L4V_ARCH/State_H"
  "../../lib/Lib"
  "./$L4V_ARCH/ArchTypes_H"
begin

context begin interpretation Arch .
requalify_types
  object_type
  machine_word
  paddr
  vptr

requalify_consts
  getObjectSize
  fromAPIType
  toAPIType
  isFrameType
  pageType
  ptrFromPAddr
end

#INCLUDE_HASKELL SEL4/API/Types.lhs all_bits NOT wordsFromBootInfo messageInfoFromWord wordFromMessageInfo ObjectType getObjectSize fromAPIType toAPIType isFrameType pageType
#INCLUDE_HASKELL SEL4/API/Types.lhs all_bits ONLY wordsFromBootInfo messageInfoFromWord wordFromMessageInfo

end
