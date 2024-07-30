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

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs CONTEXT X64_H
#INCLUDE_HASKELL_PREPARSE SEL4/API/InvocationLabels/X64.lhs CONTEXT X64
#INCLUDE_HASKELL SEL4/Kernel/VSpace/X64.lhs CONTEXT X64_H decls_only ArchInv=
#INCLUDE_HASKELL SEL4/Object/IOPort/X64.lhs CONTEXT X64_H decls_only ArchInv=

end (* context X64 *)

end
