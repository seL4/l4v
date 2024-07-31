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
  MachineExports
  ArchTypes_H
begin

arch_requalify_types (H)
  object_type
  paddr
  vptr

arch_requalify_consts (H)
  getObjectSize
  fromAPIType
  toAPIType
  isFrameType
  pageType
  tcbBlockSizeBits

arch_requalify_facts (H)
  tcbBlockSizeBits_def

#INCLUDE_HASKELL SEL4/API/Types.lhs all_bits NOT wordsFromBootInfo messageInfoFromWord wordFromMessageInfo ObjectType getObjectSize fromAPIType toAPIType isFrameType pageType
#INCLUDE_HASKELL SEL4/API/Types.lhs all_bits ONLY wordsFromBootInfo messageInfoFromWord wordFromMessageInfo

end
