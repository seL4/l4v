(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Object predicates.
 *
 * This file contains the definitions of the state of the objects created
 * by the initialiser - when they are empty, initialised and the states in between.
 * It also contains the decompositions of these predicates.
 *)

theory ObjectInitialised_SI
imports WellFormed_SI
begin

(************************************************************
 * Definitions about the state of objects,
 * when an object is newly created, completely set up, etc.
 * Non-separation style definitions are labeled "classical".
 ************************************************************)

(* Translates the object_ids in a cap for a given transformation.
 * If the object_id is not in the mapping, it is transformed to undefined.
 *)
definition
  cap_transform :: "(cdl_object_id \<rightharpoonup> cdl_object_id) \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap"
where
  "cap_transform t cap \<equiv>
  let
    t' = \<lambda> obj. case t obj of None \<Rightarrow> undefined | Some obj' \<Rightarrow> obj'
  in
   if is_untyped_cap cap
   then update_cap_objects (t' ` (cap_objects cap)) cap
   else update_cap_object (t' (cap_object cap)) cap"

(* Translates the object_ids in an object for a given transformation.
 * This does *not* translate the cdl_tcb_fault_endpoint.
 * The cdl_tcb_fault_endpoint specifies a cap pointer,
 * which should be the same in the spec and the kernel
 * (as both are looked up in the same way).
 *)
definition
  spec2s :: "(cdl_object_id \<rightharpoonup> cdl_object_id) \<Rightarrow> cdl_object \<Rightarrow> cdl_object"
where
  "spec2s t object \<equiv> update_slots (cap_transform t \<circ>\<^sub>M object_slots object) object"

(* This is used to define object_empty, object_initialised (and others).
 * Since we pass in the spec object cap transformation, we can specify
 * objects with no caps, all their caps (or anything else).
 *)
definition
  object_initialised_general :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow>
                         (cdl_object \<Rightarrow> cdl_object) \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> sep_pred) \<Rightarrow>
                          cdl_object_id \<Rightarrow> sep_pred"
where
  "object_initialised_general spec t obj_trans arrow spec_object_id \<equiv> \<lambda>s.
   let spec_objects = cdl_objects spec
   in
     \<exists>kernel_object_id. \<exists>spec_object.
     t spec_object_id = Some kernel_object_id \<and>
     (arrow kernel_object_id (obj_trans spec_object)) s \<and>
     spec_objects spec_object_id = Some spec_object"

(* The object is set up (as per the spec). *)
definition
  object_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "object_initialised spec t spec_object_id \<equiv>
  object_initialised_general spec t (spec2s t) sep_map_o spec_object_id"

(* The object is created and in it's default state. *)
definition
  object_empty :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "object_empty spec t spec_object_id \<equiv>
  object_initialised_general spec t object_default_state sep_map_o spec_object_id"

definition
  objects_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id set \<Rightarrow> sep_pred"
where
  "objects_initialised spec t obj_ids \<equiv> \<And>* obj_id \<in> obj_ids. object_initialised spec t obj_id"

definition
  objects_empty :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id set \<Rightarrow> sep_pred"
where
  "objects_empty spec t obj_ids \<equiv> \<And>* obj_id \<in> obj_ids. object_empty spec t obj_id"

(* The object's fields are set up (as per the spec). *)
definition
  object_fields_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "object_fields_initialised spec t spec_object_id \<equiv>
  object_initialised_general spec t (spec2s t) sep_map_f spec_object_id"

(* The object's slots are set up (as per the spec). *)
definition
  object_slots_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "object_slots_initialised spec t spec_object_id \<equiv>
  object_initialised_general spec t (spec2s t) sep_map_S spec_object_id"

definition
  object_empty_slots_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "object_empty_slots_initialised spec t spec_object_id \<equiv>
  object_initialised_general spec t (spec2s t) sep_map_E spec_object_id"

(* A particular slot of an object is set up (as per the spec). *)
definition
  object_slot_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> cdl_cnode_index \<Rightarrow> sep_pred"
where
  "object_slot_initialised spec t spec_object_id slot \<equiv>
  object_initialised_general spec t (spec2s t) (\<lambda>p. sep_map_s (p, slot)) spec_object_id"

(* The object's fields are in their default state. *)
definition
  object_fields_empty :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "object_fields_empty spec t spec_object_id \<equiv>
  object_initialised_general spec t object_default_state sep_map_f spec_object_id"

(* The object's slots are in their default state. *)
definition
  object_slots_empty :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "object_slots_empty spec t spec_object_id \<equiv>
  object_initialised_general spec t object_default_state sep_map_S spec_object_id"

(* A particular slot of an object is set up (as per the spec). *)
definition
  object_slot_empty :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> cdl_cnode_index \<Rightarrow> sep_pred"
where
  "object_slot_empty spec t spec_object_id slot \<equiv>
  object_initialised_general spec t object_default_state (\<lambda>p. sep_map_s (p, slot)) spec_object_id"

definition
  object_empty_slots_empty :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "object_empty_slots_empty spec t spec_object_id \<equiv>
  object_initialised_general spec t object_default_state sep_map_E spec_object_id"

definition slots_in_object_empty ::
  "(cdl_cap \<Rightarrow> bool) \<Rightarrow> cdl_object_id \<Rightarrow> cdl_state \<Rightarrow>
   (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> sep_pred" where
  "slots_in_object_empty P obj_id spec t \<equiv>
     sep_map_set_conj (object_empty spec t)
                      {obj. \<exists>slot. slot \<in> dom (slots_of obj_id spec)
                                   \<and> cap_at P (obj_id, slot) spec
                                   \<and> obj = cap_ref_object (obj_id, slot) spec}"

definition slots_in_object_init ::
  "(cdl_cap \<Rightarrow> bool) \<Rightarrow> cdl_object_id \<Rightarrow> cdl_state \<Rightarrow>
   (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> sep_pred" where
  "slots_in_object_init P obj_id spec t \<equiv>
     sep_map_set_conj (object_initialised spec t)
                      {obj. \<exists>slot. slot \<in> dom (slots_of obj_id spec)
                                   \<and> cap_at P (obj_id, slot) spec
                                   \<and> obj = cap_ref_object (obj_id, slot) spec}"

(**********************************************
 * Predicates about CNodes being initialised. *
 **********************************************)

(* A cnode that has the original caps in it set to NullCap *)
definition
  cnode_half :: "cdl_state \<Rightarrow> cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> cdl_object"
where
  "cnode_half spec obj_id obj = update_slots (\<lambda>slot.
     if original_cap_at (obj_id,slot) spec \<and> object_slots obj slot \<noteq> None
     then Some NullCap else object_slots obj slot) obj"

definition
  cnode_half_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "cnode_half_initialised spec t spec_object_id \<equiv>
  object_initialised_general spec t (spec2s t \<circ> cnode_half spec spec_object_id) sep_map_o spec_object_id"

definition
  cnodes_half_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id set \<Rightarrow> sep_pred"
where
  "cnodes_half_initialised spec t obj_ids \<equiv> \<And>* obj_id \<in> obj_ids. cnode_half_initialised spec t obj_id"

(* The cnode's fields are half done (as per the spec). *)
definition
  cnode_fields_half_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "cnode_fields_half_initialised spec t spec_object_id \<equiv>
  object_initialised_general spec t (spec2s t \<circ> cnode_half spec spec_object_id) sep_map_f spec_object_id"

(* The cnode's slots are half done (as per the spec). *)
definition
  cnode_slots_half_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "cnode_slots_half_initialised spec t spec_object_id \<equiv>
  object_initialised_general spec t (spec2s t \<circ> cnode_half spec spec_object_id) sep_map_S spec_object_id"

(* A particular slot of an object is set up (as per the spec). *)
definition
  cnode_slot_half_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> cdl_cnode_index \<Rightarrow> sep_pred"
where
  "cnode_slot_half_initialised spec t spec_object_id slot \<equiv>
  object_initialised_general spec t (spec2s t \<circ> cnode_half spec spec_object_id) (\<lambda>p. sep_map_s (p, slot)) spec_object_id"

definition
  cnode_empty_slots_half_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "cnode_empty_slots_half_initialised spec t spec_object_id \<equiv>
  object_initialised_general spec t (spec2s t \<circ> cnode_half spec spec_object_id) sep_map_E spec_object_id"


(**********************************************
 * Predicates about CNodes being initialised. *
 **********************************************)

(* A TCB that isn't set to be schedulable. *)
definition
  tcb_half :: "cdl_state \<Rightarrow> cdl_object \<Rightarrow> cdl_object"
where
  "tcb_half spec obj = update_slots (\<lambda>slot.
     if (slot = tcb_pending_op_slot \<or> slot = tcb_replycap_slot \<or> slot = tcb_boundntfn_slot) \<and>
         object_slots obj slot \<noteq> None
     then Some NullCap else object_slots obj slot) obj"

definition
  tcb_half_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "tcb_half_initialised spec t spec_object_id \<equiv>
  object_initialised_general spec t (spec2s t \<circ> tcb_half spec) sep_map_o spec_object_id"

definition
  tcbs_half_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id set \<Rightarrow> sep_pred"
where
  "tcbs_half_initialised spec t obj_ids \<equiv> \<And>* obj_id \<in> obj_ids. tcb_half_initialised spec t obj_id"

(* The cnode's fields are half done (as per the spec). *)
definition
  tcb_fields_half_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "tcb_fields_half_initialised spec t spec_object_id \<equiv>
  object_initialised_general spec t (spec2s t \<circ> tcb_half spec) sep_map_f spec_object_id"

(* The cnode's slots are half done (as per the spec). *)
definition
  tcb_slots_half_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "tcb_slots_half_initialised spec t spec_object_id \<equiv>
  object_initialised_general spec t (spec2s t \<circ> tcb_half spec) sep_map_S spec_object_id"

(* A particular slot of an object is set up (as per the spec). *)
definition
  tcb_slot_half_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> cdl_cnode_index \<Rightarrow> sep_pred"
where
  "tcb_slot_half_initialised spec t spec_object_id slot \<equiv>
  object_initialised_general spec t (spec2s t \<circ> tcb_half spec) (\<lambda>p. sep_map_s (p, slot)) spec_object_id"

definition
  tcb_empty_slots_half_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred"
where
  "tcb_empty_slots_half_initialised spec t spec_object_id \<equiv>
  object_initialised_general spec t (spec2s t \<circ> tcb_half spec) sep_map_E spec_object_id"

(********************************************
 * Predicates about IRQs being initialised. *
 ********************************************)

definition
  irq_initialised_general :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow>
                      (cdl_object \<Rightarrow> cdl_object) \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> sep_pred) \<Rightarrow>
                       cdl_irq \<Rightarrow> sep_pred"
where
  "irq_initialised_general spec t obj_trans arrow irq \<equiv> \<lambda>s.
   \<exists>kernel_irq_id spec_irq_node spec_irq_id.
     t spec_irq_id = Some kernel_irq_id \<and>
     (irq \<mapsto>irq kernel_irq_id \<and>*
      arrow kernel_irq_id (obj_trans spec_irq_node)) s \<and>
     cdl_irq_node spec irq = spec_irq_id \<and>
     cdl_objects spec spec_irq_id = Some spec_irq_node"

lemma irq_initialised_general_def2:
  "irq_initialised_general spec t obj_trans arrow irq s =
  (\<exists>kernel_irq_id spec_irq_id.
     (object_initialised_general spec t obj_trans arrow spec_irq_id \<and>*
      irq \<mapsto>irq kernel_irq_id) s \<and>
     cdl_irq_node spec irq = spec_irq_id \<and>
     t spec_irq_id = Some kernel_irq_id)"
  by (fastforce simp: irq_initialised_general_def object_initialised_general_def
                      sep_conj_exists sep_conj_ac)

(* The irq is set up (as per the spec). *)
definition
  irq_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_irq \<Rightarrow> sep_pred"
where
  "irq_initialised spec t irq \<equiv>
  irq_initialised_general spec t (spec2s t) sep_map_o irq"

(* The irq is created and in it's default state. *)
definition
  irq_empty :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_irq \<Rightarrow> sep_pred"
where
  "irq_empty spec t irq \<equiv>
  irq_initialised_general spec t object_default_state sep_map_o irq"

definition
  irqs_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_irq set \<Rightarrow> sep_pred"
where
  "irqs_initialised spec t irqs \<equiv> \<And>* irq \<in> irqs. irq_initialised spec t irq"

definition
  irqs_empty :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_irq set \<Rightarrow> sep_pred"
where
  "irqs_empty spec t irqs \<equiv> \<And>* irq \<in> irqs. irq_empty spec t irq"

(* The object's fields are set up (as per the spec). *)
definition
  irq_fields_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_irq \<Rightarrow> sep_pred"
where
  "irq_fields_initialised spec t irq \<equiv>
  irq_initialised_general spec t (spec2s t) sep_map_f irq"

(* The object's slots are set up (as per the spec). *)
definition
  irq_slots_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_irq \<Rightarrow> sep_pred"
where
  "irq_slots_initialised spec t irq \<equiv>
  irq_initialised_general spec t (spec2s t) sep_map_S irq"

definition
  irq_slot_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_irq \<Rightarrow> cdl_cnode_index \<Rightarrow> sep_pred"
where
  "irq_slot_initialised spec t irq slot \<equiv>
  irq_initialised_general spec t (spec2s t) (\<lambda>p. sep_map_s (p, slot)) irq"

definition
  irq_empty_slots_initialised :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_irq \<Rightarrow> sep_pred"
where
  "irq_empty_slots_initialised spec t irq \<equiv>
  irq_initialised_general spec t (spec2s t) sep_map_E irq"

(* The object's fields are set up (as per the spec). *)
definition
  irq_fields_empty :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_irq \<Rightarrow> sep_pred"
where
  "irq_fields_empty spec t irq \<equiv>
  irq_initialised_general spec t object_default_state sep_map_f irq"

(* The object's slots are set up (as per the spec). *)
definition
  irq_slots_empty :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_irq \<Rightarrow> sep_pred"
where
  "irq_slots_empty spec t irq \<equiv>
  irq_initialised_general spec t object_default_state sep_map_S irq"

definition
  irq_slot_empty :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_irq \<Rightarrow> cdl_cnode_index \<Rightarrow> sep_pred"
where
  "irq_slot_empty spec t irq slot \<equiv>
  irq_initialised_general spec t object_default_state (\<lambda>p. sep_map_s (p, slot)) irq"

definition
  irq_empty_slots_empty :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> cdl_irq \<Rightarrow> sep_pred"
where
  "irq_empty_slots_empty spec t irq \<equiv>
  irq_initialised_general spec t object_default_state sep_map_E irq"

(*********************************************************************
 * Introduction, destruction, and elimination rules for object_initialised. *
 *********************************************************************)


lemma object_slot_initialisedI:
  "\<lbrakk>t obj_id = Some kernel_object_id; cdl_objects spec obj_id = Some spec_object;
   ((kernel_object_id, slot) \<mapsto>s (spec2s t spec_object)) s\<rbrakk>
  \<Longrightarrow> object_slot_initialised spec t obj_id slot s"
  by (fastforce simp: object_slot_initialised_def object_initialised_general_def)

lemma object_slot_emptyI:
  "\<lbrakk>well_formed spec; t obj_id = Some kernel_object_id;
    cdl_objects spec obj_id = Some spec_object;
   ((kernel_object_id, slot) \<mapsto>s (object_default_state spec_object)) s\<rbrakk>
  \<Longrightarrow> object_slot_empty spec t obj_id slot s"
  apply (drule (1) well_formed_object_slots)
  apply (fastforce simp: object_slot_empty_def object_initialised_general_def)
  done

lemma object_slot_initialisedD:
  "object_slot_initialised spec t obj_id slot s \<Longrightarrow>
   \<exists>kernel_object_id spec_object.
       t obj_id = Some kernel_object_id \<and>
       ((kernel_object_id, slot) \<mapsto>s (spec2s t spec_object)) s \<and>
       cdl_objects spec obj_id = Some spec_object"
  by (clarsimp simp: object_slot_initialised_def object_initialised_general_def)

lemma object_slot_emptyD:
  "object_slot_empty spec t obj_id slot s \<Longrightarrow>
   \<exists>kernel_object_id kernel_object spec_object.
       t obj_id = Some kernel_object_id \<and>
       ((kernel_object_id, slot) \<mapsto>s (object_default_state spec_object)) s \<and>
       cdl_objects spec obj_id = Some spec_object"
  by (clarsimp simp: object_slot_empty_def object_initialised_general_def)

lemma object_slot_initialisedE:
  "\<lbrakk>object_slot_initialised spec t obj_id slot s;
   \<And>kernel_object_id spec_object.
      \<lbrakk>t obj_id = Some kernel_object_id \<and>
       ((kernel_object_id, slot) \<mapsto>s (spec2s t spec_object)) s \<and>
       cdl_objects spec obj_id = Some spec_object\<rbrakk> \<Longrightarrow> X\<rbrakk> \<Longrightarrow> X"
  by (fastforce simp: object_slot_initialised_def object_initialised_general_def)

lemma object_slot_emptyE:
  "\<lbrakk>object_slot_empty spec t obj_id slot s;
   \<And>kernel_object_id spec_object.
      \<lbrakk>t obj_id = Some kernel_object_id \<and>
       ((kernel_object_id, slot) \<mapsto>s (object_default_state spec_object)) s \<and>
       cdl_objects spec obj_id = Some spec_object\<rbrakk> \<Longrightarrow> X\<rbrakk> \<Longrightarrow> X"
  by (fastforce simp: object_slot_empty_def object_initialised_general_def)

(********************************************
 * Decomposition of object_initialised into parts. *
 ********************************************)

lemma spec2s_objects [simp]:
 "spec2s t Untyped = Untyped"
 "spec2s t Endpoint = Endpoint"
 "spec2s t Notification = Notification"
 "spec2s t (Frame f) = Frame f"
  by (clarsimp simp: spec2s_def update_slots_def)+

lemma object_initialised_general_decomp:
  "\<forall>p v. ((arrowL p v) \<and>* (arrowR p v)) = (arrow p v)
  \<Longrightarrow> object_initialised_general spec t obj_trans arrow spec_object_id
   = (object_initialised_general spec t obj_trans arrowL spec_object_id \<and>*
      object_initialised_general spec t obj_trans arrowR spec_object_id)"
  by (fastforce simp: object_initialised_general_def sep_conj_exists)

(* This is slightly different, as irq_initialised consumes ownership of the IRQ mapping. *)
lemma irq_initialised_general_decomp:
  "\<forall>p v. ((arrowL p v) \<and>* (arrowR p v)) = (arrow p v)
  \<Longrightarrow> irq_initialised_general spec t obj_trans arrow irq
   = (irq_initialised_general spec t obj_trans arrowL irq \<and>*
      object_initialised_general spec t obj_trans arrowR (cdl_irq_node spec irq))"
  by (fastforce simp: irq_initialised_general_def object_initialised_general_def
                      sep_conj_exists sep_conj_assoc)

lemma cap_transform_nullcap [simp]:
  "cap_transform t NullCap = NullCap"
  by (clarsimp simp: cap_transform_def cap_has_object_def
                     update_cap_object_def)

lemma cap_transform_pt_simp [simp]:
  "cap_transform t (PageTableCap x y z) = PageTableCap (the (t x)) y z"
  by (clarsimp simp: option.the_def cap_transform_def update_cap_object_def cap_object_def
               split: option.splits)

lemma cap_transform_frame [simp]:
  "cap_transform t (FrameCap x ptr rights n y z) = FrameCap x (the (t ptr)) rights n y z"
  by (clarsimp simp: option.the_def cap_transform_def update_cap_object_def cap_object_def
               split: option.splits)

lemma cap_type_cap_transform [simp]:
  "cap_type (cap_transform t cap) = cap_type cap"
  by (clarsimp simp: cap_transform_def cap_has_object_def)

lemma cap_has_object_cap_transform [simp]:
  "cap_has_object (cap_transform t cap) = cap_has_object cap"
  by (clarsimp simp: cap_transform_def)

lemma well_formed_cap_cap_transform [simp]:
  "well_formed_cap (cap_transform t cap) = well_formed_cap cap"
  by (clarsimp simp: cap_transform_def)

lemma is_default_cap_cap_transform [simp]:
  "well_formed_cap cap \<Longrightarrow> is_default_cap (cap_transform t cap) = is_default_cap cap"
  apply (clarsimp simp: is_default_cap_def well_formed_cap_def cap_type_def default_cap_def
                        cap_transform_def cap_has_object_def)
  apply (cases cap, simp_all add: update_cap_object_def cnode_cap_size_def)
  done

lemma default_cap_cap_transform:
  "\<lbrakk>is_default_cap cap; well_formed_cap cap; t (cap_object cap) = Some obj_id;
    cap_type cap = Some type; type \<noteq> IRQNodeType\<rbrakk>
  \<Longrightarrow> default_cap type {obj_id} (cnode_cap_size cap) (is_device_cap cap) = cap_transform t cap"
  by (clarsimp simp: is_default_cap_def default_cap_def cap_transform_def cap_type_def
                     well_formed_cap_def cap_has_object_def
                     update_cap_object_def split: cdl_cap.splits)+

lemma cap_transform_update_cap_object:
  "\<lbrakk>t obj_id = Some k_obj_id; cap_object cap = obj_id; cap_type cap \<noteq> Some UntypedType\<rbrakk>
  \<Longrightarrow> cap_transform t cap = update_cap_object k_obj_id cap"
  by (clarsimp simp: update_cap_object_def cap_transform_def
                     cap_object_def cap_has_object_def
              split: cdl_cap.splits)

lemma is_default_cap_def2:
  "is_default_cap cap =
  ((\<exists>type. cap_type cap = Some type \<and> cap = default_cap type (cap_objects cap) (cnode_cap_size cap) (is_device_cap cap)) \<or>
  is_irqhandler_cap cap)"
  apply (clarsimp simp:is_default_cap_def)
  apply (case_tac cap)
  apply (auto simp: default_cap_def cap_type_def)
  done

lemma default_cap_update_cap_object:
  "\<lbrakk>is_default_cap cap; cap_type cap = Some type; cnode_cap_size cap \<le> 32;
    type \<noteq> UntypedType; type \<noteq> AsidPoolType; type \<noteq> IRQNodeType\<rbrakk>
  \<Longrightarrow> default_cap type {obj_id} (cnode_cap_size cap) (is_device_cap cap) = update_cap_object obj_id cap"
  apply (subst default_cap_cap_transform, simp_all)
   apply (frule (1) default_cap_well_formed_cap2 [where obj_ids="cap_objects cap"
     and sz = "(cnode_cap_size cap)" and dev = "is_device_cap cap"], simp+)
   apply (fastforce simp: is_default_cap_def2)
  apply (subst cap_transform_update_cap_object, simp_all)
  done

lemma default_cap_update_cap_object_pd:
  "\<lbrakk>is_pd_cap cap; \<not> vm_cap_has_asid cap; \<not> is_fake_vm_cap cap\<rbrakk>
  \<Longrightarrow> default_cap PageDirectoryType {obj_id} (cnode_cap_size cap) dev = update_cap_object obj_id cap"
  by (clarsimp simp: default_cap_def update_cap_object_def cap_type_def
                     vm_cap_has_asid_def is_fake_vm_cap_def not_Some_eq_tuple
              split: cdl_cap.splits cdl_frame_cap_type.splits)

lemma object_type_spec2s [simp]:
  "object_type (spec2s t obj) = object_type obj"
  by (clarsimp simp: spec2s_def)

lemma dom_object_slots_spec2s [simp]:
  "dom (object_slots (spec2s t spec_object)) = dom (object_slots spec_object)"
  by (fastforce simp: spec2s_def update_slots_def object_slots_def
               split: cdl_object.splits option.splits)

lemma object_slots_spec2s:
  "\<lbrakk>has_slots obj; object_slots obj slot = Some cap;
    t (cap_object cap) = Some cap_object_id;
    cap_has_object cap; \<not>is_untyped_cap cap\<rbrakk>
  \<Longrightarrow> object_slots (spec2s t obj) slot = Some (update_cap_object cap_object_id cap)"
  apply (clarsimp simp: spec2s_def)
  apply (clarsimp simp: cap_transform_def)
  done

lemma object_slots_spec2s':
  "object_slots obj slot = Some spec_cap
  \<Longrightarrow> object_slots (spec2s t obj) slot = Some (cap_transform t spec_cap)"
  by (auto simp: spec2s_def object_slots_def update_slots_def
          split: cdl_object.splits)

lemma object_slots_spec2s_NullCap [simp]:
  "object_slots obj slot = Some NullCap
  \<Longrightarrow> object_slots (spec2s t obj) slot = Some NullCap"
  apply (case_tac "has_slots obj")
   apply (clarsimp simp: spec2s_def)+
  done

lemma update_cap_object_irqhandler_cap [simp]:
  "is_irqhandler_cap cap \<Longrightarrow> update_cap_object obj_id cap = cap"
  by (clarsimp simp: update_cap_object_def cap_type_def split: cdl_cap.splits)

lemma cap_transform_irqhandler_cap [simp]:
  "is_irqhandler_cap cap \<Longrightarrow> cap_transform t cap = cap"
  by (clarsimp simp: cap_transform_def)

lemma object_slots_spec2s_irqhandler_cap [simp]:
  "\<lbrakk>object_slots obj slot = Some cap; is_irqhandler_cap cap\<rbrakk>
  \<Longrightarrow> object_slots (spec2s t obj) slot = Some cap"
  apply (case_tac "has_slots obj")
   apply (clarsimp simp: spec2s_def)+
  done

lemma update_slots_empty_spec2s [simp]:
  "update_slots Map.empty (spec2s t obj)
   = update_slots Map.empty obj"
  by (clarsimp simp: spec2s_def)

lemma object_to_sep_state_fields_spec2s [simp]:
  "object_to_sep_state obj_id (spec2s t obj) {Fields}
  = object_to_sep_state obj_id obj {Fields}"
  apply (rule ext)
  apply (clarsimp simp: object_to_sep_state_def object_project_def object_clean_def
                        asid_reset_def spec2s_def object_wipe_slots_def)
  done

lemma sep_map_f_spec2s [simp]:
  "obj_id \<mapsto>f spec2s t obj = obj_id \<mapsto>f obj"
  by (auto simp: sep_map_f_def sep_map_general_def)

lemma object_type_cnode_half [simp]:
  "object_type (cnode_half spec obj_id obj) = object_type obj"
  by (clarsimp simp: cnode_half_def)

lemma object_type_tcb_half [simp]:
  "object_type (tcb_half spec tcb) = object_type tcb"
  by (simp add: tcb_half_def)

lemma dom_object_slots_cnode_half [simp]:
  "dom (object_slots (cnode_half spec obj_id obj)) = dom (object_slots obj)"
  apply (clarsimp simp: cnode_half_def)
  apply (case_tac "has_slots obj")
   apply (auto simp: dom_def)
  done

lemma dom_object_slots_tcb_half [simp]:
  "dom (object_slots (tcb_half spec tcb)) =
   dom (object_slots tcb)"
  apply (clarsimp simp: tcb_half_def)
  apply (case_tac "has_slots tcb")
   apply (auto simp: dom_def)
  done

lemma object_slots_tcb_half:
  "object_slots (tcb_half spec obj) =
   (\<lambda>slot. if (slot = tcb_pending_op_slot \<or> slot = tcb_replycap_slot \<or> slot = tcb_boundntfn_slot) \<and> object_slots obj slot \<noteq> None
     then Some NullCap else object_slots obj slot)"
  by (case_tac "has_slots obj", auto simp: tcb_half_def split: if_split_asm)

lemma intent_reset_object_type:
  "intent_reset obj = intent_reset obj' \<Longrightarrow> object_type obj = object_type obj'"
  by (clarsimp simp: intent_reset_def object_type_def split: cdl_object.splits)

lemma intent_reset_object_slots:
  "intent_reset obj = intent_reset obj' \<Longrightarrow> object_slots obj = object_slots obj'"
  by (clarsimp simp: intent_reset_def object_slots_def cdl_tcb.splits split: cdl_object.splits)

lemma intent_reset_object_size_bits:
  "intent_reset obj = intent_reset obj' \<Longrightarrow> object_size_bits obj = object_size_bits obj'"
  by (clarsimp simp: intent_reset_def object_size_bits_def split: cdl_object.splits)

lemma intent_reset_cnode:
  "\<lbrakk>intent_reset obj = intent_reset obj'; object_type obj = CNodeType\<rbrakk>
  \<Longrightarrow> obj = obj'"
  by (clarsimp simp: intent_reset_def object_type_def split: cdl_object.splits)

lemma zero_in_tcb_slots[simp]:
  "0 \<in> tcb_slots"
  by (simp add: tcb_slot_defs)

lemma intent_reset_object_slots_NullCap:
  "\<lbrakk>intent_reset (object_default_state obj) = intent_reset obj';
   slot < 2 ^ object_size_bits obj; has_slots obj\<rbrakk>
  \<Longrightarrow> object_slots obj' slot = Some NullCap"
  apply (frule intent_reset_object_slots [THEN sym])
  apply (clarsimp simp: object_default_state_def2 object_type_def has_slots_def
                        object_size_bits_def object_slots_def default_tcb_def
                        empty_cnode_def empty_irq_node_def empty_cap_map_def pt_size_def pd_size_def
                 split: cdl_object.splits)
  done

lemma object_slots_object_default_state_NullCap':
  "\<lbrakk>slot < 2 ^ object_size_bits obj; has_slots obj\<rbrakk>
  \<Longrightarrow> object_slots (object_default_state obj) slot = Some NullCap"
  by (clarsimp simp: object_default_state_def2 object_type_def has_slots_def
                     object_size_bits_def object_slots_def default_tcb_def
                     empty_cnode_def empty_irq_node_def empty_cap_map_def pt_size_def pd_size_def
              split: cdl_object.splits)

lemma dom_range_upper:
  "\<lbrakk>dom f = {0..<n}; f x = Some y\<rbrakk> \<Longrightarrow> x < n"
  by fastforce

lemma object_slots_object_default_state_NullCap:
  "\<lbrakk>well_formed spec; \<not>tcb_at obj_id spec; opt_cap (obj_id, slot) spec = Some cap;
    cdl_objects spec obj_id = Some spec_object\<rbrakk>
  \<Longrightarrow> object_slots (object_default_state spec_object) slot = Some NullCap"
  apply (drule (1) well_formed_object_slots)
  apply (clarsimp simp: object_default_state_def2
                 split: cdl_object.splits,
       (fastforce simp: object_at_def is_cnode_def object_size_bits_def object_slots_def
                        empty_cnode_def empty_irq_node_def empty_cap_map_def
                        opt_cap_def slots_of_def
                 dest!: dom_range_upper)+)
  done

lemma intent_reset_remove:
  "obj = obj' \<Longrightarrow> intent_reset obj = intent_reset obj'"
  by (rule arg_cong)

lemma sep_map_E_eq:
  "\<lbrakk>object_type obj = object_type obj'; dom (object_slots obj) = dom (object_slots obj')\<rbrakk>
  \<Longrightarrow> (p \<mapsto>E obj) = (p \<mapsto>E obj')"
  apply (clarsimp simp: sep_map_E_def sep_map_S'_def sep_map_general_def)
  apply (rule ext)
  apply (subgoal_tac "object_to_sep_state p obj (Slot ` (UNIV - dom (object_slots obj')))
    = object_to_sep_state p obj' (Slot ` (UNIV - dom (object_slots obj')))")
   apply simp
  apply (fastforce simp: object_to_sep_state_def split_def
                         object_project_def object_slots_object_clean
                  split: option.splits)
  done

lemma sep_map_E_object_default_state:
  "dom (object_slots (object_default_state obj)) = dom (object_slots obj)
  \<Longrightarrow> (p \<mapsto>E object_default_state obj) = (p \<mapsto>E obj)"
  using sep_map_E_eq [where obj="object_default_state obj" and obj'=obj]
  by simp

lemma sep_map_E_intent_reset:
  "\<lbrakk>intent_reset obj = intent_reset obj'\<rbrakk>
  \<Longrightarrow> (p \<mapsto>E obj) = (p \<mapsto>E obj')"
  apply (cut_tac obj=obj and obj'=obj' in sep_map_E_eq)
    apply (erule intent_reset_object_type)
   apply (drule intent_reset_object_slots, simp)
  apply simp
  done

lemma sep_map_E_spec2s [simp]:
  "(p \<mapsto>E spec2s t obj) = (p \<mapsto>E obj)"
  apply (cut_tac obj="spec2s t obj" and obj'=obj in sep_map_E_eq, simp)
   apply (clarsimp simp: spec2s_def)
   apply (case_tac "has_slots obj")
    apply simp+
  done

lemma sep_map_E_tcb_half [simp]:
  "obj_id \<mapsto>E tcb_half spec tcb = obj_id \<mapsto>E tcb"
  by (rule sep_map_E_eq, simp+)

lemma object_to_sep_state_fields_tcb_eq:
  "\<lbrakk>cdl_tcb_fault_endpoint tcb = cdl_tcb_fault_endpoint tcb';
    cdl_tcb_has_fault tcb = cdl_tcb_has_fault tcb';
    cdl_tcb_domain tcb = cdl_tcb_domain tcb'\<rbrakk>
  \<Longrightarrow> object_to_sep_state obj_id (Tcb tcb) {Fields}
  = object_to_sep_state obj_id (Tcb tcb') {Fields}"
  apply (rule ext)
  apply (clarsimp simp: object_to_sep_state_def object_project_def object_clean_def
                        asid_reset_def spec2s_def object_wipe_slots_def
                        update_slots_def intent_reset_def cdl_tcb.splits)
  done

lemma sep_map_f_eq_tcb:
  "\<lbrakk>cdl_tcb_fault_endpoint tcb = cdl_tcb_fault_endpoint tcb';
    cdl_tcb_has_fault tcb = cdl_tcb_has_fault tcb';
    cdl_tcb_domain tcb = cdl_tcb_domain tcb'\<rbrakk>
  \<Longrightarrow> obj_id \<mapsto>f Tcb tcb = obj_id \<mapsto>f Tcb tcb'"
  apply (clarsimp simp: sep_map_f_def sep_map_general_def object_slots_def
                      object_clean_def intent_reset_def asid_reset_def update_slots_def)
  apply (subst object_to_sep_state_fields_tcb_eq [where tcb'=tcb'], simp_all)
  done

lemma sep_map_f_intent_reset_cnode:
  "\<lbrakk>object_type obj = CNodeType; intent_reset obj = intent_reset obj'\<rbrakk>
  \<Longrightarrow> obj_id \<mapsto>f obj = obj_id \<mapsto>f obj'"
  apply (clarsimp simp: sep_map_f_def sep_map_general_def split: sep_state.splits)
  apply (rule ext)
  apply (clarsimp simp: intent_reset_def object_type_def
                 split: cdl_object.splits)
  done

lemma sep_map_f_empty_cnode:
  "obj_id \<mapsto>f CNode (empty_cnode sz) =
   obj_id \<mapsto>f CNode \<lparr>cdl_cnode_caps = Map.empty, cdl_cnode_size_bits = sz\<rparr>"
  apply (rule ext, rename_tac s)
  apply (clarsimp simp: sep_map_f_def sep_map_general_def split: sep_state.splits)
  apply (intro iffI ext |
         clarsimp simp: object_to_sep_state_def object_clean_def
                        object_project_def object_slots_object_clean asid_reset_def
                        intent_reset_def object_wipe_slots_def
                        update_slots_def empty_cnode_def)+
  done

lemma empty_cnode_object_size_bits:
  "object_type obj = CNodeType \<Longrightarrow> obj_id \<mapsto>f CNode (empty_cnode (object_size_bits obj)) = obj_id \<mapsto>f obj"
  apply (subst sep_map_f_empty_cnode)
  apply (rule ext)
  apply (clarsimp simp: sep_map_f_def sep_map_general_def split: sep_state.splits)
apply (intro iffI ext |
       clarsimp simp: object_type_def object_size_bits_def
                      object_clean_def reset_cap_asid_def asid_reset_def
                      object_to_sep_state_def object_project_def intent_reset_def
                      object_wipe_slots_def update_slots_def cdl_cnode.splits
               split: cdl_object.splits)+
  done

lemma sep_map_f_object_size_bits_cnode:
  "\<lbrakk>object_type obj = CNodeType; object_type obj' = CNodeType;
    object_size_bits obj = object_size_bits obj'\<rbrakk>
  \<Longrightarrow> obj_id \<mapsto>f obj = obj_id \<mapsto>f obj'"
  apply (clarsimp simp: sep_map_f_def sep_map_general_def split: sep_state.splits)
  apply (rule ext)
  apply (intro iffI ext |
         clarsimp simp: object_type_def object_size_bits_def
                        object_to_sep_state_def object_project_def intent_reset_def
                        object_wipe_slots_def update_slots_def
                        cdl_cnode.splits object_clean_def asid_reset_def
                 split: cdl_object.splits)+
  done

lemma sep_map_f_object_size_bits_pt:
  "\<lbrakk>object_type obj = PageTableType; object_type obj' = PageTableType\<rbrakk>
  \<Longrightarrow> obj_id \<mapsto>f obj = obj_id \<mapsto>f obj'"
  apply (clarsimp simp: sep_map_f_def sep_map_general_def split: sep_state.splits)
  apply (rule ext)
  apply (intro iffI ext |
         clarsimp simp: object_type_def object_size_bits_def
                        object_to_sep_state_def object_project_def intent_reset_def
                        object_wipe_slots_def update_slots_def object_clean_def asid_reset_def
                 split: cdl_object.splits)+
  done

lemma sep_map_f_object_size_bits_pd:
  "\<lbrakk>object_type obj = PageDirectoryType; object_type obj' = PageDirectoryType\<rbrakk>
  \<Longrightarrow> obj_id \<mapsto>f obj = obj_id \<mapsto>f obj'"
  apply (clarsimp simp: sep_map_f_def sep_map_general_def split: sep_state.splits)
  apply (rule ext)
apply (intro iffI ext |
       clarsimp simp: object_type_def object_size_bits_def
                      object_to_sep_state_def object_project_def intent_reset_def
                      object_wipe_slots_def update_slots_def object_clean_def asid_reset_def
               split: cdl_object.splits)+
  done

(********************************************************
 * Object done, and other such predicate decompositions *
 ********************************************************)

lemma object_initialised_decomp:
  "object_initialised spec t spec_object_id =
   (object_fields_initialised spec t spec_object_id \<and>*
    object_slots_initialised spec t spec_object_id)"
  apply (clarsimp simp: object_initialised_def object_fields_initialised_def object_slots_initialised_def)
  apply (rule object_initialised_general_decomp)
  apply (clarsimp simp: sep_map_o_decomp)
  done

lemma object_empty_decomp:
  "object_empty spec t spec_object_id =
   (object_fields_empty spec t spec_object_id \<and>*
    object_slots_empty spec t spec_object_id)"
  apply (clarsimp simp: object_empty_def object_fields_empty_def object_slots_empty_def)
  apply (rule object_initialised_general_decomp)
  apply (clarsimp simp: sep_map_o_decomp)
  done

lemma cnode_half_initialised_decomp:
  "cnode_half_initialised spec t spec_object_id =
   (cnode_fields_half_initialised spec t spec_object_id \<and>*
    cnode_slots_half_initialised spec t spec_object_id)"
  apply (clarsimp simp: cnode_half_initialised_def cnode_fields_half_initialised_def cnode_slots_half_initialised_def)
  apply (rule object_initialised_general_decomp)
  apply (clarsimp simp: sep_map_o_decomp)
  done

lemma irq_initialised_decomp:
  "irq_initialised spec t irq =
   (irq_slots_initialised spec t irq \<and>*
   object_fields_initialised spec t (cdl_irq_node spec irq))"
  apply (clarsimp simp: irq_initialised_def object_fields_initialised_def irq_slots_initialised_def)
  apply (rule irq_initialised_general_decomp)
  apply (clarsimp simp: sep_map_o_decomp sep_conj_ac)
  done

lemma irq_empty_decomp:
  "irq_empty spec t irq =
   (irq_slots_empty spec t irq \<and>*
   object_fields_empty spec t (cdl_irq_node spec irq))"
  apply (clarsimp simp: irq_empty_def object_fields_empty_def irq_slots_empty_def)
  apply (rule irq_initialised_general_decomp)
  apply (clarsimp simp: sep_map_o_decomp sep_conj_ac)
  done

(************************************
 * object_slots_initialised rewrite rules. *
 ************************************)

lemma object_slot_initialised_eq:
  "\<lbrakk>t obj_id = Some kernel_object_id; cdl_objects spec obj_id = Some spec_object\<rbrakk>
  \<Longrightarrow> object_slot_initialised spec t obj_id slot
      = (kernel_object_id, slot) \<mapsto>s (spec2s t spec_object)"
  apply (rule ext, rename_tac s)
  apply (fastforce simp: object_slot_initialised_def object_initialised_general_def)
  done

lemma object_slot_empty_eq:
  "\<lbrakk>well_formed spec; t obj_id = Some kernel_object_id;
    cdl_objects spec obj_id = Some spec_object\<rbrakk>
  \<Longrightarrow> object_slot_empty spec t obj_id slot
      = (kernel_object_id, slot) \<mapsto>s (object_default_state spec_object)"
  apply (rule ext, rename_tac s)
  apply (drule (1) well_formed_object_slots)
  apply (fastforce simp: object_slot_empty_def object_initialised_general_def)
  done

(****************************************************************************
 * Lemmas decomposing object_slots_initialised.                                    *
 * These show that initialising an objects slots can be done slot by slot.  *
 ****************************************************************************)

lemma object_slots_initialised_decomp_helper:
  "\<lbrakk>slots \<noteq> {}; slots \<noteq> UNIV\<rbrakk>
  \<Longrightarrow> object_slots_initialised spec t obj_id =
  (object_initialised_general spec t (spec2s t) (\<lambda>obj_id. sep_map_S' (obj_id, slots)) obj_id \<and>*
   object_initialised_general spec t (spec2s t) (\<lambda>obj_id. sep_map_S' (obj_id, UNIV-slots)) obj_id)"
  apply (clarsimp simp: object_slots_initialised_def)
  apply (rule object_initialised_general_decomp)
  apply (clarsimp simp: sep_map_S_decomp')
  done

lemma object_slots_empty_decomp_helper:
  "\<lbrakk>slots \<noteq> {}; slots \<noteq> UNIV\<rbrakk>
  \<Longrightarrow> object_slots_empty spec t obj_id =
  (object_initialised_general spec t object_default_state (\<lambda>obj_id. sep_map_S' (obj_id, slots)) obj_id \<and>*
   object_initialised_general spec t object_default_state (\<lambda>obj_id. sep_map_S' (obj_id, UNIV-slots)) obj_id)"
  apply (clarsimp simp: object_slots_empty_def)
  apply (rule object_initialised_general_decomp)
  apply (clarsimp simp: sep_map_S_decomp')
  done

lemma cnode_slots_half_initialised_decomp_helper:
  "\<lbrakk>slots \<noteq> {}; slots \<noteq> UNIV\<rbrakk>
  \<Longrightarrow> cnode_slots_half_initialised spec t obj_id =
  (object_initialised_general spec t (spec2s t \<circ> cnode_half spec obj_id) (\<lambda>obj_id. sep_map_S' (obj_id, slots)) obj_id \<and>*
   object_initialised_general spec t (spec2s t \<circ> cnode_half spec obj_id) (\<lambda>obj_id. sep_map_S' (obj_id, UNIV-slots)) obj_id)"
  apply (clarsimp simp: cnode_slots_half_initialised_def)
  apply (rule object_initialised_general_decomp)
  apply (clarsimp simp: sep_map_S_decomp')
  done

lemma sep_map_exists_rewrite':
  "\<lbrakk>((obj_id, slots) \<mapsto>S' obj') s; intent_reset obj' = intent_reset obj\<rbrakk>
  \<Longrightarrow> ((obj_id, slots) \<mapsto>S' obj) s"
  apply (clarsimp simp: intent_reset_def sep_map_S'_def sep_map_general_def
    split: cdl_object.splits)
  apply (rename_tac cdl_tcb cdl_tcb')
  apply (rule ext)
  apply (clarsimp simp: sep_map_S'_def sep_map_general_def intent_reset_def
                        object_slots_object_clean object_to_sep_state_def object_project_def
                 split: if_split_asm)
  apply (case_tac cdl_tcb,clarsimp)
  apply (case_tac cdl_tcb',clarsimp simp:object_slots_def)
  apply (intro conjI |
        clarsimp simp: object_slots_object_clean |
        clarsimp simp: object_slots_def)+
  done

lemma sep_map_exists_rewrite:
  "(\<lambda>s. \<exists>obj'. ((obj_id, slots) \<mapsto>S' obj') s \<and> intent_reset obj = intent_reset obj') =
    (obj_id, slots) \<mapsto>S' obj"
  apply (rule ext)
  apply (rule iffI)
   apply clarsimp
   apply (erule sep_map_exists_rewrite', simp)
  apply fastforce
  done

lemma object_slots_general_decomp_list:
  "\<lbrakk>distinct slots; slots \<noteq> []\<rbrakk>
  \<Longrightarrow> (object_initialised_general spec t obj_trans (\<lambda>obj_id. sep_map_S' (obj_id, set slots)) obj_id) =
  (\<And>* map (\<lambda>slot. object_initialised_general spec t obj_trans (\<lambda>p. sep_map_s (p, slot)) obj_id) slots)"
  apply (induct slots)
   apply clarsimp
  apply (atomize)
  apply (case_tac "slots = []")
   apply (clarsimp simp: object_initialised_general_def sep_map_S'_def sep_map_s_def)
  apply (clarsimp simp: object_initialised_general_def)
  apply (rule ext)
  apply (rule iffI)
   apply clarsimp
   apply (drule_tac obj_id=kernel_object_id and obj="obj_trans spec_object" in sep_map_S'_decomp', simp)
   apply (fastforce simp: sep_conj_exists sep_conj_ac)
  apply (clarsimp simp: sep_conj_exists)
  apply (drule_tac obj_id=kernel_object_id and obj="obj_trans spec_object" in sep_map_S'_decomp', simp)
  apply (fastforce simp: sep_conj_exists sep_conj_ac)
  done

lemma object_slots_general_decomp_set:
  "\<lbrakk>finite slots; slots \<noteq> {}\<rbrakk>
  \<Longrightarrow> (object_initialised_general spec t obj_trans (\<lambda>obj_id. sep_map_S' (obj_id, slots)) obj_id) =
  (\<And>* slot \<in> slots. object_initialised_general spec t obj_trans (\<lambda>p. sep_map_s (p, slot)) obj_id)"
  apply (drule sep_map_set_conj_sep_list_conj [where
           P="\<lambda>slot. object_initialised_general spec t obj_trans (\<lambda>p. sep_map_s (p, slot)) obj_id"])
  apply (elim exE conjE)
  apply simp
  apply (subst object_slots_general_decomp_list [symmetric], clarsimp+)
  done

lemma object_slots_initialised_decomp':
  "\<lbrakk>finite slots; slots \<noteq> {}\<rbrakk>
  \<Longrightarrow> (object_initialised_general spec t (spec2s t) (\<lambda>obj_id. sep_map_S' (obj_id, slots)) obj_id) =
  (\<And>* slot \<in> slots. object_slot_initialised spec t obj_id slot)"
  apply (clarsimp simp: object_slot_initialised_def [abs_def])
  apply (erule (1) object_slots_general_decomp_set)
  done

lemma object_slots_empty_decomp':
  "\<lbrakk>finite slots; slots \<noteq> {}\<rbrakk>
  \<Longrightarrow> (object_initialised_general spec t object_default_state (\<lambda>obj_id. sep_map_S' (obj_id, slots)) obj_id) =
  (\<And>* slot \<in> slots. object_slot_empty spec t obj_id slot)"
  apply (clarsimp simp: object_slot_empty_def [abs_def])
  apply (erule (1) object_slots_general_decomp_set)
  done

lemma cnode_slots_half_initialised_decomp':
  "\<lbrakk>finite slots; slots \<noteq> {}\<rbrakk>
  \<Longrightarrow> (object_initialised_general spec t (spec2s t \<circ> cnode_half spec obj_id) (\<lambda>obj_id. sep_map_S' (obj_id, slots)) obj_id) =
  (\<And>* slot \<in> slots. cnode_slot_half_initialised spec t obj_id slot)"
  apply (clarsimp simp: cnode_slot_half_initialised_def [abs_def])
  apply (erule (1) object_slots_general_decomp_set)
  done

lemma empty_slots_object_slots_initialised_object_empty_slots_initialised:
  "dom (slots_of obj_id spec) = {} \<Longrightarrow> object_empty_slots_initialised spec t obj_id = object_slots_initialised spec t obj_id"
  apply (rule ext, rename_tac s)
  apply (clarsimp simp: object_slots_initialised_def object_empty_slots_initialised_def object_initialised_general_def)
  apply (rule iffI)
   apply clarsimp
   apply (clarsimp simp: sep_map_S_def sep_map_S'_def sep_map_E_def slots_of_def
                  split: option.splits)
   apply (fastforce simp: intent_reset_def spec2s_def object_slots_def cdl_tcb.splits
                   split: cdl_object.splits)
  apply clarsimp
  apply (clarsimp simp: sep_map_S_def sep_map_S'_def sep_map_E_def slots_of_def
                 split: option.splits)
  apply (fastforce simp: intent_reset_def spec2s_def object_slots_def cdl_tcb.splits
                  split: cdl_object.splits)
  done

lemma object_empty_slots_initialised_def2:
  "object_empty_slots_initialised spec t obj_id =
   object_initialised_general spec t (spec2s t) (\<lambda>obj_id'. sep_map_S' (obj_id', UNIV - dom (slots_of obj_id spec))) obj_id"
  apply (clarsimp simp: object_empty_slots_initialised_def object_initialised_general_def sep_map_E_def)
  apply (fastforce simp: slots_of_def
                  split: option.splits)
  done

lemma object_slots_initialised_decomp:
  "well_formed spec \<Longrightarrow>
  object_slots_initialised spec t obj_id =
  ((\<And>* slot \<in> dom (slots_of obj_id spec). (object_slot_initialised spec t obj_id) slot) \<and>*
    object_empty_slots_initialised spec t obj_id)"
  apply (drule well_formed_finite [where obj_id=obj_id])
  apply (case_tac "dom (slots_of obj_id spec) = {}")
   apply clarsimp
   apply (rule empty_slots_object_slots_initialised_object_empty_slots_initialised [THEN sym], simp)
  apply (subst object_slots_initialised_decomp_helper, assumption)
   apply clarsimp
  apply (clarsimp simp: object_empty_slots_initialised_def2)
  apply (drule_tac obj_id=obj_id and spec=spec and t=t in object_slots_initialised_decomp', simp)
  apply clarsimp
  done

lemma object_initialised_decomp_total:
  "\<lbrakk>well_formed spec\<rbrakk>
    \<Longrightarrow> object_initialised spec t obj_id =
        (object_fields_initialised spec t obj_id \<and>*
        (\<And>* slot \<in> dom (slots_of obj_id spec). object_slot_initialised spec t obj_id slot) \<and>*
         object_empty_slots_initialised spec t obj_id)"
  by (clarsimp simp: object_initialised_decomp object_slots_initialised_decomp sep_conj_assoc)

lemma object_slot_empty_initialised_NullCap:
  "\<lbrakk>well_formed spec; \<not>tcb_at obj_id spec; opt_cap (obj_id, slot) spec = Some NullCap\<rbrakk> \<Longrightarrow>
  object_slot_empty spec t obj_id slot = object_slot_initialised spec t obj_id slot"
  apply (clarsimp simp: object_slot_empty_def object_slot_initialised_def object_initialised_general_def)
  apply (rule ext)
  apply (rule iffI)
   apply (clarsimp simp: sep_conj_exists)
   apply (cut_tac obj="object_default_state spec_object" and obj_id=kernel_object_id and
                  obj'="spec2s t spec_object" and slot=slot
               in sep_map_s_object_slots_equal)
     apply (clarsimp simp: object_slots_opt_cap)
     apply (drule (3) object_slots_object_default_state_NullCap, simp)
    apply clarsimp
   apply clarsimp
  apply (clarsimp simp: sep_conj_exists)
  apply (cut_tac obj="spec2s t spec_object" and obj_id=kernel_object_id and
                 obj'="object_default_state spec_object" and slot=slot
              in sep_map_s_object_slots_equal)
    apply (drule (3) object_slots_object_default_state_NullCap)
    apply (clarsimp simp: object_slots_opt_cap)
   apply clarsimp
  apply clarsimp
  done

lemma object_empty_slots_empty_initialised:
  "well_formed spec
  \<Longrightarrow> object_empty_slots_empty spec t spec_object_id =
      object_empty_slots_initialised spec t spec_object_id"
  apply (clarsimp simp: object_empty_slots_initialised_def object_empty_slots_empty_def
                        object_initialised_general_def)
  apply (rule ext)
  apply (rule iffI)
   apply clarsimp
   apply (frule (1) well_formed_object_slots)
   apply (clarsimp simp: well_formed_def)
   apply (erule_tac x=spec_object_id in allE)
   apply (clarsimp simp: sep_map_E_object_default_state
                  split: option.splits)
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=spec_object_id in allE)
  apply (clarsimp split: option.splits)
  apply (drule_tac obj=spec_object and p=kernel_object_id in sep_map_E_object_default_state, simp)
  done

lemma cnode_empty_slots_half_initialised_object_empty_slots_initialised:
  "cnode_empty_slots_half_initialised spec t spec_object_id =
   object_empty_slots_initialised spec t spec_object_id"
  apply (clarsimp simp: object_empty_slots_initialised_def cnode_empty_slots_half_initialised_def
                        object_initialised_general_def)
  apply (rule ext)
  apply (rule iffI)
   apply (clarsimp split: option.splits)
   apply (cut_tac p=kernel_object_id and obj=spec_object and
                  obj'="cnode_half spec spec_object_id spec_object" in
                  sep_map_E_eq [OF sym], simp+)
  apply (clarsimp split: option.splits)
  apply (cut_tac p=kernel_object_id and obj="cnode_half spec spec_object_id spec_object" and
                 obj'="spec_object" in
                 sep_map_E_eq [OF sym], simp+)
  done

lemma object_default_state_has_slots_not_empty:
  "has_slots obj \<Longrightarrow> dom (object_slots (object_default_state obj)) \<noteq> {}"
  apply (clarsimp simp: object_default_state_def2 has_slots_def object_slots_def
                        default_tcb_def tcb_pending_op_slot_def
                        empty_cnode_def empty_irq_node_def empty_cap_map_def
                 split: cdl_object.splits)
  apply (clarsimp simp: fun_eq_iff, erule_tac x=0 in allE, simp)+
  done

lemma well_formed_has_slots:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some obj; object_slots obj = Map.empty; has_slots obj \<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp split: option.splits)
  apply (drule object_default_state_has_slots_not_empty, simp)
  done

lemma sep_map_S_object_default_state_no_slots:
  "\<not> has_slots obj \<Longrightarrow> (obj_id \<mapsto>S object_default_state obj) = (obj_id \<mapsto>S obj)"
  apply (clarsimp simp: sep_map_S_def sep_map_general_def)
  apply (intro ext conjI iffI |
         clarsimp simp: object_to_sep_state_def object_project_def
                        update_slots_def empty_cnode_def
                        object_slots_object_clean
                        object_default_state_def default_object_def
                        object_type_def has_slots_def
                 split: cdl_component_id.splits option.splits cdl_object.splits)+
  done

lemma sep_map_s_object_default_state_no_slots:
  "\<not> has_slots obj \<Longrightarrow> (obj_id, slot) \<mapsto>s object_default_state obj = (obj_id, slot) \<mapsto>s obj"
  apply (clarsimp simp: sep_map_s_def sep_map_general_def)
  apply (intro ext conjI iffI |
         clarsimp simp: object_to_sep_state_def object_project_def
                        update_slots_def empty_cnode_def
                        object_slots_object_clean
                        object_default_state_def default_object_def
                        object_type_def has_slots_def
                 split: cdl_component_id.splits option.splits cdl_object.splits)+
  done

lemma object_slots_empty_initialised_no_slots:
  "\<lbrakk>well_formed spec; slots_of obj_id spec = Map.empty\<rbrakk>
  \<Longrightarrow> object_slots_empty spec t obj_id = object_slots_initialised spec t obj_id"
  apply (clarsimp simp: slots_of_def split: option.splits)
   apply (clarsimp simp: object_slots_empty_def object_slots_initialised_def object_initialised_general_def)
  apply (rename_tac obj)
  apply (case_tac "has_slots obj")
   apply (drule (3) well_formed_has_slots, simp)
  apply (frule (1) well_formed_object_slots)
  apply (clarsimp simp: object_slots_empty_def object_slots_initialised_def object_initialised_general_def)
  apply (rule ext, rule iffI)
   apply (clarsimp simp: spec2s_def)
   apply (drule_tac obj_id=kernel_object_id in sep_map_S_object_default_state_no_slots, simp)
  apply clarsimp
  apply (clarsimp simp: spec2s_def)
  apply (drule_tac obj_id=kernel_object_id in sep_map_S_object_default_state_no_slots, simp)
  done

lemma object_empty_slots_empty_def2:
  "well_formed spec
  \<Longrightarrow> object_empty_slots_empty spec t obj_id =
      object_initialised_general spec t object_default_state (\<lambda>obj_id'. sep_map_S' (obj_id', UNIV - dom (slots_of obj_id spec))) obj_id"
  apply (clarsimp simp: object_empty_slots_empty_def object_initialised_general_def sep_map_E_def)
  apply (rule ext)
  apply (rule iffI)
   apply (clarsimp simp: well_formed_def)
   apply (erule_tac x=obj_id in allE)
   apply (clarsimp split: option.splits)
   apply (fastforce simp: slots_of_def split: option.splits)
  apply (clarsimp simp: well_formed_def)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp split: option.splits)
  apply (fastforce simp: slots_of_def split: option.splits)
  done

lemma cnode_empty_slots_half_initialised_def2:
  "cnode_empty_slots_half_initialised spec t obj_id =
      object_initialised_general spec t (spec2s t \<circ> cnode_half spec obj_id)
      (\<lambda>obj_id'. sep_map_S' (obj_id', UNIV - dom (slots_of obj_id spec))) obj_id"
  apply (clarsimp simp: object_empty_slots_initialised_def cnode_empty_slots_half_initialised_def
                        object_initialised_general_def)
  apply (rule ext)
  apply (rule iffI)
   apply (clarsimp split: option.splits)
   apply (cut_tac p=kernel_object_id and
                  obj="cnode_half spec obj_id spec_object" and
                  obj'="spec2s t (cnode_half spec obj_id spec_object)" in
          sep_map_E_eq, simp, simp)
   apply (clarsimp simp: sep_map_E_def slots_of_def split: option.splits)
  apply clarsimp
  apply (cut_tac p=kernel_object_id and
                 obj="spec2s t (cnode_half spec obj_id spec_object)" and
                 obj'="cnode_half spec obj_id spec_object" in
         sep_map_E_eq, simp, simp)
  apply (clarsimp simp: sep_map_E_def slots_of_def)
  done

lemma object_slots_empty_decomp:
  "\<lbrakk>well_formed spec\<rbrakk>
  \<Longrightarrow> object_slots_empty spec t obj_id =
  ((\<And>* slot \<in> dom (slots_of obj_id spec).  object_slot_empty spec t obj_id slot) \<and>*
    object_empty_slots_empty spec t obj_id)"
  apply (frule well_formed_finite [where obj_id=obj_id])
  apply (case_tac "dom (slots_of obj_id spec) = {}")
   apply clarsimp
   apply (subst object_empty_slots_empty_initialised, simp)
   apply (subst empty_slots_object_slots_initialised_object_empty_slots_initialised, simp)
   apply (clarsimp simp: object_slots_empty_initialised_no_slots)
  apply (subst object_slots_empty_decomp_helper, assumption)
   apply clarsimp
  apply (clarsimp simp: object_empty_slots_empty_def2)
  apply (drule_tac obj_id=obj_id and spec=spec and t=t in object_slots_empty_decomp', simp)
  apply clarsimp
  done

lemma well_formed_cnode_not_empty:
  "\<lbrakk>well_formed spec; slots_of obj_id spec = Map.empty; cnode_at obj_id spec\<rbrakk> \<Longrightarrow> P"
  apply (clarsimp simp: slots_of_def object_at_def
                 split: option.splits)
  apply (rename_tac obj)
  apply (case_tac "has_slots obj")
   apply (drule (3) well_formed_has_slots, simp)
  apply (clarsimp simp: is_cnode_def has_slots_def split: cdl_object.splits)
  done

lemma cnode_slots_half_initialised_decomp:
  "\<lbrakk>well_formed spec; cnode_at obj_id spec\<rbrakk>
  \<Longrightarrow> cnode_slots_half_initialised spec t obj_id =
  ((\<And>* slot \<in> dom (slots_of obj_id spec). cnode_slot_half_initialised spec t obj_id slot) \<and>*
    cnode_empty_slots_half_initialised spec t obj_id)"
  apply (frule well_formed_finite [where obj_id=obj_id])
  apply (case_tac "dom (slots_of obj_id spec) = {}")
   apply clarsimp
   apply (erule (2) well_formed_cnode_not_empty)
  apply (subst cnode_slots_half_initialised_decomp_helper, assumption)
   apply clarsimp
   apply (drule_tac obj_id=obj_id in well_formed_finite, clarsimp)
  apply (subst cnode_slots_half_initialised_decomp', simp+)
  apply (clarsimp simp: cnode_empty_slots_half_initialised_def2)
  done



lemma distinct_singleton_set:
  "\<lbrakk>distinct xs; set xs = {x}\<rbrakk> \<Longrightarrow> xs = [x]"
  by (metis set_simps(2) distinct.simps(2) distinct_singleton
            insert_iff insert_not_empty list.exhaust set_empty2)



lemma irq_slots_initialised_decomp_helper:
  "well_formed spec
  \<Longrightarrow> irq_slots_initialised spec t irq =
  ((\<And>* slot \<in> dom (slots_of (cdl_irq_node spec irq) spec). irq_slot_initialised spec t irq slot) \<and>*
    object_empty_slots_initialised spec t (cdl_irq_node spec irq))"
  apply (clarsimp simp: irq_slots_initialised_def irq_slot_initialised_def [abs_def]
                        irq_initialised_general_def [abs_def]
                        object_empty_slots_initialised_def object_initialised_general_def
                        sep_conj_exists slots_of_def
                 split: option.splits)
  apply (subst sep_map_S_decomp, simp+)
   apply (erule (1) well_formed_finite_object_slots)
  apply (subst well_formed_object_slots_irq_node, assumption+)+
  apply (fastforce simp: sep_conj_ac)
  done

lemma irq_slots_empty_decomp_helper:
  "well_formed spec
  \<Longrightarrow> irq_slots_empty spec t irq =
  ((\<And>* slot \<in> dom (slots_of (cdl_irq_node spec irq) spec). irq_slot_empty spec t irq slot) \<and>*
    object_empty_slots_empty spec t (cdl_irq_node spec irq))"
  apply (clarsimp simp: irq_slots_empty_def irq_slot_empty_def [abs_def]
                        irq_initialised_general_def [abs_def]
                        object_empty_slots_empty_def object_initialised_general_def
                        sep_conj_exists slots_of_def
                 split: option.splits)
  apply (frule (1) well_formed_object_slots_default_irq_node)
  apply (subst sep_map_S_decomp, simp+)
  apply (subst well_formed_object_slots_irq_node, assumption+)+
  apply (fastforce simp: sep_conj_ac)
  done

(* This rule uses object_empty_slots_initialised, to make it easier to cancel. *)
lemma irq_slots_initialised_decomp:
  "\<lbrakk>well_formed spec; irq \<in> used_irqs spec\<rbrakk>
  \<Longrightarrow> irq_slots_initialised spec t irq = (irq_slot_initialised spec t irq 0 \<and>* object_empty_slots_initialised spec t (cdl_irq_node spec irq))"
  apply (subst irq_slots_initialised_decomp_helper, assumption)
  apply (subst well_formed_slots_of_used_irq_node, assumption+)
  apply clarsimp
  done

lemma irq_slots_empty_decomp:
  "\<lbrakk>well_formed spec; irq \<in> used_irqs spec\<rbrakk>
  \<Longrightarrow> irq_slots_empty spec t irq = (irq_slot_empty spec t irq 0 \<and>* object_empty_slots_initialised spec t (cdl_irq_node spec irq))"
  apply (subst irq_slots_empty_decomp_helper, assumption)
  apply (subst well_formed_slots_of_used_irq_node, assumption+)
  apply (subst object_empty_slots_empty_initialised, assumption)
  apply clarsimp
  done

lemma irq_initialised_decomp_total:
  "\<lbrakk>well_formed spec; irq \<in> used_irqs spec\<rbrakk>
  \<Longrightarrow> irq_initialised spec t irq =
     (irq_slot_initialised spec t irq 0 \<and>*
      object_empty_slots_initialised spec t (cdl_irq_node spec irq) \<and>*
      object_fields_initialised spec t (cdl_irq_node spec irq))"
  apply (subst irq_initialised_decomp)
  apply (subst irq_slots_initialised_decomp, assumption+)
  apply (clarsimp simp: sep_conj_assoc)
  done

lemma irq_empty_decomp_total:
  "\<lbrakk>well_formed spec; irq \<in> used_irqs spec\<rbrakk>
  \<Longrightarrow> irq_empty spec t irq =
     (irq_slot_empty spec t irq 0 \<and>*
      object_empty_slots_initialised spec t (cdl_irq_node spec irq) \<and>*
      object_fields_empty spec t (cdl_irq_node spec irq))"
  apply (subst irq_empty_decomp)
  apply (subst irq_slots_empty_decomp, assumption+)
  apply (clarsimp simp: sep_conj_assoc)
  done

(****************************************************************************
 * Lemmas proving equality between object_fields predicates.                *
 * These show that the fields of a CNode are already initialised correctly. *
 ****************************************************************************)

lemma sep_map_f_object_default_state_cnode [simp]:
  "object_type obj = CNodeType \<Longrightarrow> obj_id \<mapsto>f object_default_state obj = obj_id \<mapsto>f obj"
  apply (clarsimp simp: sep_map_f_def sep_map_general_def split: sep_state.splits)
  apply (rule ext)
  apply (clarsimp simp: object_type_def split: cdl_object.splits)
  apply (intro ext conjI iffI |
         clarsimp simp: object_to_sep_state_def object_project_def
                        intent_reset_def object_wipe_slots_def
                        object_default_state_def default_object_def
                        asid_reset_def object_type_def update_slots_def
                        empty_cnode_def object_size_bits_def object_clean_def)+
  done

lemma sep_map_f_object_default_state_irq_node [simp]:
  "object_type obj = IRQNodeType \<Longrightarrow> obj_id \<mapsto>f object_default_state obj = obj_id \<mapsto>f obj"
  apply (clarsimp simp: sep_map_f_def sep_map_general_def split: sep_state.splits)
  apply (rule ext)
  apply (clarsimp simp: object_type_def split: cdl_object.splits)
  apply (intro ext conjI iffI |
         clarsimp simp: object_to_sep_state_def object_project_def
                        intent_reset_def object_wipe_slots_def
                        object_default_state_def default_object_def
                        asid_reset_def object_type_def update_slots_def
                        empty_cnode_def object_size_bits_def object_clean_def)+
  done

lemma object_to_sep_state_fields[simp]:
  "object_to_sep_state obj_id (update_slots slot obj) {Fields} = object_to_sep_state obj_id obj {Fields}"
  apply (rule ext)
  apply (case_tac obj,
    simp_all add:object_to_sep_state_def update_slots_def split_def
    object_project_def object_clean_def asid_reset_def
    object_wipe_slots_def intent_reset_def object_slots_def)
  done

lemma sep_map_f_cnode_half [simp]:
  "obj_id \<mapsto>f cnode_half spec obj_id' obj = obj_id \<mapsto>f obj "
  apply (rule ext)
  apply (clarsimp simp: cnode_half_def sep_map_f_def sep_map_general_def)
  done

lemma sep_map_f_tcb_half [simp]:
  "obj_id \<mapsto>f tcb_half spec tcb = obj_id \<mapsto>f tcb"
  by (clarsimp simp: tcb_half_def sep_map_f_def sep_map_general_def)

lemma irq_node_fields_empty_initialised:
  "irq_node_at obj_id spec
  \<Longrightarrow> object_fields_empty spec spec2s_ids obj_id = object_fields_initialised spec spec2s_ids obj_id"
  by (clarsimp simp: object_fields_empty_def object_fields_initialised_def
                     object_initialised_general_def object_at_def object_type_is_object)

lemma cnode_fields_empty_initialised:
  "cnode_at obj_id spec
  \<Longrightarrow> object_fields_empty spec t obj_id = object_fields_initialised spec t obj_id"
  by (clarsimp simp: object_fields_empty_def object_fields_initialised_def
                     object_initialised_general_def object_at_def object_type_is_object)


lemma cnode_fields_half_initialised_object_fields_initialised:
  "cnode_at obj_id spec
  \<Longrightarrow> cnode_fields_half_initialised spec t obj_id = object_fields_initialised spec t obj_id"
  by (clarsimp simp: cnode_fields_half_initialised_def object_fields_initialised_def object_initialised_general_def)


lemma object_fields_empty_half_initialised:
  "cnode_at obj_id spec
  \<Longrightarrow> cnode_fields_half_initialised spec t obj_id = object_fields_empty spec t obj_id"
  by (clarsimp simp: cnode_fields_half_initialised_object_fields_initialised cnode_fields_empty_initialised)

lemma object_default_state_frame [simp]:
  "is_frame object \<Longrightarrow> object_default_state object = object"
  by (clarsimp simp: object_default_state_def default_object_def
                     object_type_is_object object_type_def
              split: cdl_object.splits)

end
