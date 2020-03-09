(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AbstractSeparation_SD
imports
  AbstractSeparationHelpers_SD
  "Sep_Algebra.Map_Extra"
  "DSpec.Types_D"
begin

datatype cdl_component_id = Fields | Slot nat
type_synonym cdl_component_ids = "cdl_component_id set"

translations
  (type) "cdl_component_ids" <=(type) "cdl_component_id set"

(* The cdl_component are the pieces of capDL objects that we are interested in our lifted heap.
 * These components are either objects without capabilities or capabilities.
 *)
datatype cdl_component = CDL_Object cdl_object | CDL_Cap "cdl_cap option"

(* The state for separation logic is an option map
 * from (obj_id,component) to sep_entities
 *)
type_synonym sep_state_heap = "(cdl_object_id \<times> cdl_component_id) \<Rightarrow> cdl_component option"
type_synonym sep_state_irq_map = "cdl_irq \<Rightarrow> cdl_object_id option"

translations
  (type) "sep_state_heap" <=(type) "32 word \<times> cdl_component_id \<Rightarrow> cdl_component option"


(* Our lifted state contains sep_entities and the IRQ table.
 *)
datatype sep_state =
  SepState "(cdl_object_id \<times> cdl_component_id) \<Rightarrow> cdl_component option"
           "cdl_irq \<Rightarrow> cdl_object_id option"

(* Functions to get the object heap and the irq table from the sep_state. *)
primrec sep_heap :: "sep_state \<Rightarrow> sep_state_heap"
where "sep_heap (SepState heap irqs) = heap"

primrec sep_irq_node :: "sep_state \<Rightarrow> sep_state_irq_map"
where "sep_irq_node (SepState heap irqs) = irqs"

(* Adding states adds the separation entity heap and the IRQ table.
 *)
definition
  sep_state_add :: "sep_state \<Rightarrow> sep_state \<Rightarrow> sep_state"
where
  "sep_state_add state_a state_b \<equiv>
  SepState ((sep_heap state_a) ++ (sep_heap state_b))
           ((sep_irq_node state_a) ++ sep_irq_node state_b)"


(* State are disjoint the separation entity heaps and the IRQ tables are dijoint.
 *)
definition
  sep_state_disj :: "sep_state \<Rightarrow> sep_state \<Rightarrow> bool"
where
  "sep_state_disj state_a state_b \<equiv>
   (sep_heap state_a) \<bottom> (sep_heap state_b) \<and>
   (sep_irq_node state_a) \<bottom> (sep_irq_node state_b)"

lemma sep_state_add_comm:
  "sep_state_disj x y \<Longrightarrow> sep_state_add x y = sep_state_add y x"
  by (fastforce simp: sep_state_add_def sep_state_disj_def intro!:map_add_com)

(*********************************************)
(* Definition of separation logic for capDL. *)
(*********************************************)

instantiation "sep_state" :: zero
begin
  definition "0 \<equiv> SepState (\<lambda>p. None) Map.empty"
  instance ..
end

instantiation "sep_state" :: stronger_sep_algebra
begin

definition "(##) \<equiv> sep_state_disj"
definition "(+) \<equiv> sep_state_add"



(************************************************
 * The proof that this is a separation algebra. *
 ************************************************)

instance
  apply standard
(* x ## 0 *)
       apply (simp add: sep_disj_sep_state_def sep_state_disj_def zero_sep_state_def)
(* x ## y \<Longrightarrow> y ## x *)
      apply (clarsimp simp: sep_disj_sep_state_def sep_state_disj_def Let_unfold
                            map_disj_com Int_commute)
(* x + 0 = x *)
     apply (simp add: plus_sep_state_def sep_state_add_def zero_sep_state_def)
     apply (case_tac x,simp)
(* x ## y \<Longrightarrow> x + y = y + x *)
    apply (clarsimp simp: plus_sep_state_def sep_disj_sep_state_def)
    apply (erule sep_state_add_comm)
(* (x + y) + z = x + (y + z) *)
   apply (simp add: plus_sep_state_def sep_state_add_def)+
(* x ## y + z = (x ## y \<and> x ## z) *)
   apply (clarsimp simp: sep_disj_sep_state_def)
   apply (auto simp: map_disj_def sep_state_disj_def)
  done
end

(*************************************************************
 * The proof that this is a cancellative separation algebra. *
 *************************************************************)

instantiation "sep_state" :: cancellative_sep_algebra
begin

instance
  apply (standard; simp add: sep_disj_sep_state_def sep_state_disj_def zero_sep_state_def
                   plus_sep_state_def sep_state_add_def)
  apply (metis map_add_subsumed1 map_le_refl sep_heap.simps sep_irq_node.simps sep_state.exhaust)
  by (metis map_add_left_eq sep_heap.simps sep_irq_node.simps sep_state.exhaust)
end

end

