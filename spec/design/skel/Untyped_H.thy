(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Untyped Objects"

theory Untyped_H
imports
  RetypeDecls_H
  CSpaceDecls_H
  CNode_H
  Invocations_H
  InvocationLabels_H
  Config_H
begin

arch_requalify_consts (H)
  minUntypedSizeBits
  maxUntypedSizeBits

consts
  cNodeOverlap :: "(machine_word \<Rightarrow> nat option) \<Rightarrow> (machine_word \<Rightarrow> bool) \<Rightarrow> bool"

#INCLUDE_HASKELL SEL4/Object/Untyped.lhs decls_only ONLY archOverlap

#INCLUDE_HASKELL SEL4/Object/Untyped.lhs NOT cNodeOverlap canonicalAddressAssert archOverlap

end
