(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  Hypervisor stub for X64
*)

theory ArchHypervisor_H
imports
  CNode_H
  KI_Decls_H
  InterruptDecls_H
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Kernel/Hypervisor/X64.lhs Arch= CONTEXT X64_H decls_only ArchInv= ArchLabels=
#INCLUDE_HASKELL SEL4/Kernel/Hypervisor/X64.lhs Arch= CONTEXT X64_H bodies_only ArchInv= ArchLabels=

end
end
