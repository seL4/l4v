(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Retyping Objects"

theory Retype_H
imports
  RetypeDecls_H
  Endpoint_H
  Untyped_H
  Interrupt_H
begin

context Arch begin

(* match Haskell, expects these under Arch. *)
requalify_consts
  cteRightsBits cteGuardBits

(* disambiguate name clash between Arch and non-arch consts with same names *)
requalify_consts (aliasing)
  deriveCap finaliseCap postCapDeletion isCapRevocable
  hasCancelSendRights sameRegionAs isPhysicalCap
  sameObjectAs updateCapData maskCapRights
  createObject capUntypedPtr capUntypedSize
  performInvocation decodeInvocation prepareThreadDelete prepareSetDomain
  isIRQControlCapDescendant

context begin global_naming global

requalify_consts (aliasing)
  RetypeDecls_H.deriveCap RetypeDecls_H.finaliseCap RetypeDecls_H.postCapDeletion
  RetypeDecls_H.isCapRevocable
  RetypeDecls_H.hasCancelSendRights RetypeDecls_H.sameRegionAs RetypeDecls_H.isPhysicalCap
  RetypeDecls_H.sameObjectAs RetypeDecls_H.updateCapData RetypeDecls_H.maskCapRights
  RetypeDecls_H.createObject RetypeDecls_H.capUntypedPtr RetypeDecls_H.capUntypedSize
  RetypeDecls_H.performInvocation RetypeDecls_H.decodeInvocation
end

end

#INCLUDE_HASKELL SEL4/Object/ObjectType.lhs Arch=Arch bodies_only

end
