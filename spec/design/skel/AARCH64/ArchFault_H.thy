(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  VSpace lookup code.
*)

(* FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
   with minimal text substitution! Remove this comment after updating,
   check copyright. *)
theory ArchFault_H
imports Types_H
begin

context Arch begin global_naming AARCH64_H

#INCLUDE_HASKELL SEL4/API/Failures/AARCH64.hs CONTEXT AARCH64_H decls_only
#INCLUDE_HASKELL SEL4/API/Failures/AARCH64.hs CONTEXT AARCH64_H bodies_only

end
end
