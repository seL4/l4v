(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Retyping Objects"

theory ArchVSpaceDecls_H
imports ArchRetypeDecls_H InvocationLabels_H
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs CONTEXT AARCH64_H
#INCLUDE_HASKELL_PREPARSE SEL4/API/InvocationLabels/AARCH64.hs CONTEXT AARCH64
#INCLUDE_HASKELL SEL4/Kernel/VSpace/AARCH64.hs CONTEXT AARCH64_H decls_only ArchInv= \
  NOT lookupPTSlotFromLevel lookupPTFromLevel pageBase

(* no "wordlike" class with a direct translation available, use more constrained spec *)
consts'
pageBase :: "('a :: len word) \<Rightarrow> nat \<Rightarrow> 'a word"

end (* context AARCH64 *)

end
