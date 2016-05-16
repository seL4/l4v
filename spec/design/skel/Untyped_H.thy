(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
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
  "../machine/MachineExports"
begin

consts
  cNodeOverlap :: "(machine_word \<Rightarrow> nat option) \<Rightarrow> (machine_word \<Rightarrow> bool) \<Rightarrow> bool"

#INCLUDE_HASKELL SEL4/Object/Untyped.lhs NOT cNodeOverlap

end
