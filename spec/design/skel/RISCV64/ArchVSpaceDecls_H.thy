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

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs CONTEXT RISCV64_H
#INCLUDE_HASKELL_PREPARSE SEL4/API/InvocationLabels/RISCV64.hs CONTEXT RISCV64
#INCLUDE_HASKELL SEL4/Kernel/VSpace/RISCV64.hs CONTEXT RISCV64_H decls_only ArchInv= NOT lookupPTSlotFromLevel lookupPTFromLevel

end (* context RISCV64 *)

end
