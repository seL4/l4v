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
requalify_consts
  deriveCap finaliseCap postCapDeletion isCapRevocable
  hasCancelSendRights sameRegionAs isPhysicalCap
  sameObjectAs updateCapData maskCapRights
  createObject capUntypedPtr capUntypedSize
  performInvocation decodeInvocation prepareThreadDelete
  cteRightsBits cteGuardBits

context begin global_naming global

requalify_consts
  RetypeDecls_H.deriveCap RetypeDecls_H.finaliseCap RetypeDecls_H.postCapDeletion
  RetypeDecls_H.hasCancelSendRights RetypeDecls_H.sameRegionAs RetypeDecls_H.isPhysicalCap
  RetypeDecls_H.sameObjectAs RetypeDecls_H.updateCapData RetypeDecls_H.maskCapRights
  RetypeDecls_H.createObject RetypeDecls_H.capUntypedPtr RetypeDecls_H.capUntypedSize
  RetypeDecls_H.performInvocation RetypeDecls_H.decodeInvocation RetypeDecls_H.isCapRevocable
end

end

#INCLUDE_HASKELL SEL4/Object/ObjectType.lhs Arch=Arch bodies_only

end
