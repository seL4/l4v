(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
    Declarations from SEL4.Kernel.FaultHandler
*)

chapter "Function Declarations for Fault Handlers"

theory FaultHandlerDecls_H
imports Structures_H FaultMonad_H
begin

#INCLUDE_HASKELL SEL4/Kernel/FaultHandler.lhs decls_only

end
