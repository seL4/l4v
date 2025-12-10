(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInterruptDecls_H
imports RetypeDecls_H CNode_H
begin

(* performSGISignalGenerate in Haskell expects Arch.sgisignal_invocation *)
requalify_types (in Arch)
  sgisignal_invocation

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Object/Interrupt/AARCH64.hs CONTEXT AARCH64_H decls_only ArchInv=Arch Arch=MachineOps

end (* context AARCH64_H *)

end
