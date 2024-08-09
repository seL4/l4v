(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInterruptDecls_H
imports RetypeDecls_H CNode_H
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Object/Interrupt/AARCH64.hs CONTEXT AARCH64_H decls_only ArchInv= Arch=MachineOps NOT plic_complete_claim

end (* context AARCH64 *)

end
