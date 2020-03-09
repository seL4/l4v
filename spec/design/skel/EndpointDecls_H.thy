(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Function Declarations for Endpoints"

theory EndpointDecls_H
imports FaultMonad_H
begin

#INCLUDE_HASKELL SEL4/Object/Endpoint.lhs decls_only

end
