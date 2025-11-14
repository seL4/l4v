(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "CNodes"

theory CNode_H
imports
  FaultMonad_H
  ThreadDecls_H
  ArchRetypeDecls_H
  RetypeDecls_H
  TCBDecls_H
  CSpaceDecls_H
  EndpointDecls_H
  PSpaceFuns_H
  SchedContextDecls_H
begin

arch_requalify_consts (H) isArchMDBParentOf

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs

#INCLUDE_HASKELL SEL4/Object/CNode.lhs decls_only NOT cteRevoke

function
  cteRevoke :: "machine_word \<Rightarrow> unit kernel_p"
where
 "cteRevoke p s =

#INCLUDE_HASKELL SEL4/Object/CNode.lhs BODY cteRevoke

  p s"
by auto

#INCLUDE_HASKELL SEL4/Object/CNode.lhs bodies_only NOT finaliseSlot cteRevoke \
  cteDeleteOne noReplyCapsFor archMDBAssertions

end
