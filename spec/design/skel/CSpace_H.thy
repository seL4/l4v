(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
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
  resolveAddressBits_decl_def [simp]:
  "CSpaceDecls_H.resolveAddressBits \<equiv> resolveAddressBits"

end
