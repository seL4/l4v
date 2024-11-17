(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
    The fault datatype.
*)

chapter "Fault Structures"

theory Fault_H
imports ArchFault_H
begin

arch_requalify_types (H)
  arch_fault

#INCLUDE_HASKELL_PREPARSE SEL4/API/Types.lhs
#INCLUDE_HASKELL SEL4/API/Failures.lhs decls_only
#INCLUDE_HASKELL SEL4/API/Failures.lhs bodies_only

end
