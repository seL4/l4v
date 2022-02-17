(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  Hypervisor stub for AARCH64
*)

(* FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
   with minimal text substitution! Remove this comment after updating,
   check copyright. *)
theory ArchHypervisor_H
imports
  CNode_H
  KI_Decls_H
  InterruptDecls_H
begin
context Arch begin global_naming AARCH64_H


#INCLUDE_HASKELL SEL4/Kernel/Hypervisor/AARCH64.hs Arch= CONTEXT AARCH64_H decls_only ArchInv= ArchLabels=
#INCLUDE_HASKELL SEL4/Kernel/Hypervisor/AARCH64.hs Arch= CONTEXT AARCH64_H bodies_only ArchInv= ArchLabels=

end
end
