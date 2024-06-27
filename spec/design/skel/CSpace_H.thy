(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "CSpace"

theory CSpace_H
imports CSpaceDecls_H Object_H
begin

#INCLUDE_HASKELL SEL4/Kernel/CSpace.lhs bodies_only NOT resolveAddressBits


function
  resolveAddressBits ::
  "capability \<Rightarrow> cptr \<Rightarrow> nat \<Rightarrow>
   (lookup_failure, (machine_word * nat)) kernel_f"
where
 "resolveAddressBits a b c =
#INCLUDE_HASKELL SEL4/Kernel/CSpace.lhs BODY resolveAddressBits
a b c"
  by auto

termination
  apply (relation "measure (snd o snd)")
  apply (auto simp add: in_monad split: if_split_asm)
  done

defs
  resolveAddressBits_decl_def:
  "CSpaceDecls_H.resolveAddressBits \<equiv> resolveAddressBits"
declare resolveAddressBits_decl_def[simp]

end
