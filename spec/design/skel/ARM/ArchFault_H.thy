(*
 * Copyright 2014, General Dynamics C4 Systems
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


#INCLUDE_HASKELL SEL4/API/Failures/ARM.lhs CONTEXT ARM_H decls_only
#INCLUDE_HASKELL SEL4/API/Failures/ARM.lhs CONTEXT ARM_H bodies_only


end
end
