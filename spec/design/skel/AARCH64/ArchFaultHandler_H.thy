(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Fault Handlers"

(* FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
   with minimal text substitution! Remove this comment after updating,
   check copyright. *)
theory ArchFaultHandler_H
imports TCB_H Structures_H
begin

context Arch begin global_naming AARCH64_H

#INCLUDE_HASKELL_PREPARSE SEL4/API/Failures/AARCH64.hs

#INCLUDE_HASKELL SEL4/API/Faults/AARCH64.hs decls_only
#INCLUDE_HASKELL SEL4/API/Faults/AARCH64.hs bodies_only

end

end
