(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Endpoints"

theory Endpoint_H
imports
  EndpointDecls_H
  TCB_H
  ThreadDecls_H
  CSpaceDecls_H
  FaultHandlerDecls_H
  Notification_H
begin

#INCLUDE_HASKELL SEL4/Object/Endpoint.lhs bodies_only

end
