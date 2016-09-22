(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file PSpaceStruct_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Physical Memory Structure"

theory PSpaceStruct_H
imports
  Structures_H
  "../../lib/DataMap"
begin

text {* Helper Functions *}

definition
  ptrBits_def[simp]:
 "ptrBits \<equiv> to_bl"


text {* Physical Memory Structures *}

type_synonym pspace = "( machine_word , kernel_object ) DataMap.map"

definition
  PSpace :: "pspace \<Rightarrow> pspace"
where PSpace_def[simp]:
 "PSpace \<equiv> id"

definition
  psMap :: "pspace \<Rightarrow> pspace"
where
  psMap_def[simp]:
 "psMap \<equiv> id"

definition  psMap_update :: "(pspace \<Rightarrow> pspace) \<Rightarrow> pspace \<Rightarrow> pspace"
where
  psMap_update_def[simp]:
 "psMap_update f y \<equiv> f y"

abbreviation (input)
  PSpace_trans :: "(( machine_word , kernel_object ) DataMap.map) \<Rightarrow> pspace" ("PSpace'_ \<lparr> psMap= _ \<rparr>")
where
  "PSpace_ \<lparr> psMap= v0 \<rparr> == PSpace v0"


end
