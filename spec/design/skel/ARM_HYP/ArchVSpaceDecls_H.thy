(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Retyping Objects"

theory ArchVSpaceDecls_H
imports ArchRetypeDecls_H InvocationLabels_H
begin
context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs CONTEXT ARM_HYP_H
#INCLUDE_HASKELL SEL4/Kernel/VSpace/ARM.lhs CONTEXT ARM_HYP_H decls_only NOT pageBase ArchInv=

(* no "wordlike" class with a direct translation available, use more constrained spec *)
consts'
pageBase :: "('a :: len word) \<Rightarrow> vmpage_size \<Rightarrow> 'a word"

end
end
