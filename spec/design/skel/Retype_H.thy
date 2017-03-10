(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
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
  deriveCap finaliseCap 
  hasCancelSendRights sameRegionAs isPhysicalCap
  sameObjectAs updateCapData maskCapRights
  createObject capUntypedPtr capUntypedSize
  performInvocation decodeInvocation prepareThreadDelete

context begin global_naming global

requalify_consts
  RetypeDecls_H.deriveCap RetypeDecls_H.finaliseCap 
  RetypeDecls_H.hasCancelSendRights RetypeDecls_H.sameRegionAs RetypeDecls_H.isPhysicalCap
  RetypeDecls_H.sameObjectAs RetypeDecls_H.updateCapData RetypeDecls_H.maskCapRights
  RetypeDecls_H.createObject RetypeDecls_H.capUntypedPtr RetypeDecls_H.capUntypedSize
  RetypeDecls_H.performInvocation RetypeDecls_H.decodeInvocation
end

end

#INCLUDE_HASKELL SEL4/Object/ObjectType.lhs Arch=Arch bodies_only

end
