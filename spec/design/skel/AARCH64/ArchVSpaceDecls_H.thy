(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Retyping Objects"

(* FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
   with minimal text substitution! Remove this comment after updating,
   check copyright. *)
theory ArchVSpaceDecls_H
imports ArchRetypeDecls_H InvocationLabels_H
begin

context Arch begin global_naming AARCH64_H

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs CONTEXT AARCH64_H
#INCLUDE_HASKELL_PREPARSE SEL4/API/InvocationLabels/AARCH64.hs CONTEXT AARCH64
#INCLUDE_HASKELL SEL4/Kernel/VSpace/AARCH64.hs CONTEXT AARCH64_H decls_only ArchInv= NOT lookupPTSlotFromLevel lookupPTFromLevel

end (* context AARCH64 *)

end
