(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Author: Andrew Boyton, 2012
   Maintainers: Gerwin Klein <kleing at cse.unsw.edu.au>
                Rafal Kolanski <rafal.kolanski at nicta.com.au>
*)

chapter "Defining some separation logic maps-to predicates on top of the instantiation."

theory Separation_D
imports Abstract_Separation_D
begin

type_synonym sep_pred = "sep_state \<Rightarrow> bool"

definition
  state_sep_projection :: "cdl_state \<Rightarrow> sep_state"
where
  "state_sep_projection \<equiv> \<lambda>s. SepState (cdl_objects s) (cdl_ghost_state s)"

(* This turns a separation logic predicate into a predicate on the capDL state. *)
abbreviation
  lift' :: "(sep_state \<Rightarrow> 'a) \<Rightarrow> cdl_state \<Rightarrow> 'a" ("<_>")
where
  "<P> s \<equiv> P (state_sep_projection s)"

(* The generalisation of the maps to operator for separation logic. *)
definition
  sep_map_general :: "cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> cdl_components \<Rightarrow> sep_pred"
where
  "sep_map_general p obj gs \<equiv> \<lambda>s. sep_heap s = [p \<mapsto> obj] \<and> sep_ghost_state s p = gs"

(* Alternate definition without the [p \<mapsto> obj] notation. *)
lemma sep_map_general_def2:
  "sep_map_general p obj gs s =
   (dom (sep_heap s) = {p} \<and> ko_at obj p (sep_heap s) \<and> sep_ghost_state s p = gs)"
  apply (clarsimp simp: sep_map_general_def object_at_def)
  apply (rule)
   apply clarsimp
  apply (clarsimp simp: fun_upd_def)
  apply (rule ext)
  apply (fastforce simp: dom_def split:if_split)
  done

(* There is an object there. *)
definition
  sep_map_i :: "cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> sep_pred" ("_ \<mapsto>i _" [76,71] 76)
where
  "p \<mapsto>i obj \<equiv> sep_map_general p obj UNIV"

(* The fields are there (and there are no caps). *)
definition
  sep_map_f :: "cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> sep_pred" ("_ \<mapsto>f _" [76,71] 76)
where
  "p \<mapsto>f obj \<equiv> sep_map_general p (update_slots empty obj) {None}"

(* There is that cap there. *)
definition
  sep_map_c :: "cdl_cap_ref \<Rightarrow> cdl_cap \<Rightarrow> sep_pred" ("_ \<mapsto>c _" [76,71] 76)
where
  "p \<mapsto>c cap \<equiv> \<lambda>s. let (obj_id, slot) = p; heap = sep_heap s in
  \<exists>obj. sep_map_general obj_id obj {Some slot} s \<and> object_slots obj = [slot \<mapsto> cap]"

definition
  sep_any :: "('a \<Rightarrow> 'b \<Rightarrow> sep_pred) \<Rightarrow> ('a \<Rightarrow> sep_pred)" where
  "sep_any m \<equiv> (\<lambda>p s. \<exists>v. (m p v) s)"

abbreviation "sep_any_map_i \<equiv> sep_any sep_map_i"
notation sep_any_map_i ("_ \<mapsto>i -" 76)

abbreviation "sep_any_map_c \<equiv> sep_any sep_map_c"
notation sep_any_map_c ("_ \<mapsto>c -" 76)

end
