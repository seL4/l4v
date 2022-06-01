(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   Types visible in the API.
*)

chapter "Types visible in the API"

theory Types_H
imports
  ArchTypes_H
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
  tcbBlockSizeBits

requalify_facts
  tcbBlockSizeBits_def
end

#INCLUDE_HASKELL SEL4/API/Types.lhs all_bits NOT wordsFromBootInfo messageInfoFromWord wordFromMessageInfo ObjectType getObjectSize fromAPIType toAPIType isFrameType pageType
#INCLUDE_HASKELL SEL4/API/Types.lhs all_bits ONLY wordsFromBootInfo messageInfoFromWord wordFromMessageInfo

end
