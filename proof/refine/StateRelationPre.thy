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

text \<open>
  An analogue of cmap_relation in CRefine, used to formulate predicates stating that all kernel
  objects of some type are in a particular relation, in the case where for every abstract kernel
  object, there is exactly one associated concrete kernel object.\<close>
definition map_relation :: "(obj_ref \<rightharpoonup> 'a) \<Rightarrow> (obj_ref \<rightharpoonup> 'b) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "map_relation ah ch rel \<equiv>
     dom ah = dom ch
     \<and> (\<forall>p obj obj'. ah p = Some obj \<and> ch p = Some obj' \<longrightarrow> rel obj obj')"

end
