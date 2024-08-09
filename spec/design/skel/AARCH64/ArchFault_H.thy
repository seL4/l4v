(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  VSpace lookup code.
*)

theory ArchFault_H
imports Types_H
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/API/Failures/AARCH64.hs CONTEXT AARCH64_H decls_only
#INCLUDE_HASKELL SEL4/API/Failures/AARCH64.hs CONTEXT AARCH64_H bodies_only

end
end
