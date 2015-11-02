(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
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
