(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   Requirements for definition of architecture-specific refinement relation between abstract and
   concrete states.
*)

theory StateRelationPre
imports ArchInvariantUpdates_H
begin

(* required for construction of generic instances of object_type *)
arch_requalify_consts (H) APIObjectType

text \<open>
  A pspace and a tree are related if every object in the pspace
  corresponds to an object in the tree. Some abstract objects
  like CapTables correspond to multiple concrete ones, thus we
  have to make cuts.\<close>
type_synonym obj_relation_cut = "Structures_A.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool"
type_synonym obj_relation_cuts = "(machine_word \<times> obj_relation_cut) set"

text \<open>Arch object projection for predicates that depend on arch objects only.\<close>
definition aobj_of':: "kernel_object \<Rightarrow> arch_kernel_object option" where
  "aobj_of' ko \<equiv> case ko of KOArch ako \<Rightarrow> Some ako | _ \<Rightarrow> None"

lemmas aobj_of'_simps[simp] = aobj_of'_def[split_simps kernel_object.split]

lemma aobj_of'_Some[iff]:
  "(aobj_of' a = Some ao) = (a = KOArch ao)"
  by (simp add: aobj_of'_def split: kernel_object.splits)

abbreviation aobjs_of' :: "kernel_state \<Rightarrow> obj_ref \<rightharpoonup> arch_kernel_object" where
  "aobjs_of' \<equiv> \<lambda>s. ksPSpace s |> aobj_of'"

end
