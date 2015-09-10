(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "CNodes"

theory CNode_H
imports
  FaultMonad_H
  ThreadDecls_H
  RetypeDecls_H
  TCBDecls_H
  CSpaceDecls_H
  EndpointDecls_H
  PSpaceFuns_H
begin

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs

#INCLUDE_HASKELL SEL4/Object/CNode.lhs decls_only NOT cteRevoke

function
  cteRevoke :: "machine_word \<Rightarrow> unit kernel_p"
where
 "cteRevoke p s = 

#INCLUDE_HASKELL SEL4/Object/CNode.lhs BODY cteRevoke

  p s"
by auto

#INCLUDE_HASKELL SEL4/Object/CNode.lhs bodies_only NOT finaliseSlot cteRevoke cteDeleteOne noReplyCapsFor

end
