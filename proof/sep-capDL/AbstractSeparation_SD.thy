(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory AbstractSeparation_SD
imports
  AbstractSeparationHelpers_SD
  "../../lib/sep_algebra/Map_Extra"
  "../../spec/capDL/Types_D"
begin

(**************************************
 * Start of lemmas to move elsewhere. *
 **************************************)

lemma inter_empty_not_both:
"\<lbrakk>x \<in> A; A \<inter> B = {}\<rbrakk> \<Longrightarrow> x \<notin> B"
  by fastforce

lemma union_intersection:
  "A \<inter> (A \<union> B) = A"
  "B \<inter> (A \<union> B) = B"
  "(A \<union> B) \<inter> A = A"
  "(A \<union> B) \<inter> B = B"
  by fastforce+

lemma union_intersection1: "A \<inter> (A \<union> B) = A"
  by (rule inf_sup_absorb)
lemma union_intersection2: "B \<inter> (A \<union> B) = B"
  by fastforce

(* This lemma is strictly weaker than restrict_map_disj. *)
lemma restrict_map_disj':
  "S \<inter> T = {} \<Longrightarrow> h |` S \<bottom> h' |` T"
  by (auto simp: map_disj_def restrict_map_def dom_def)

lemma map_add_restrict_comm:
  "S \<inter> T = {} \<Longrightarrow> h |` S ++ h' |` T = h' |` T ++ h |` S"
  apply (drule restrict_map_disj')
  apply (erule map_add_com)
  done

lemma restrict_map_not_self_UNIV [simp]:
  "h |` (UNIV - dom h) = empty"
  by (rule ext, clarsimp simp: restrict_map_def)

(************************************
 * End of lemmas to move elsewhere. *
 ************************************)

definition
  the_set :: "cdl_component set \<Rightarrow> nat set"
where
  "the_set xs = {x. Slot x \<in> xs}"

lemma in_the_set [simp]:
  "(x \<in> the_set xs) = (Slot x \<in> xs)"
  by (clarsimp simp: the_set_def)

lemma the_set_union [simp]:
  "the_set (A \<union> B) = the_set A \<union> the_set B"
  by (fastforce simp: the_set_def)

lemma the_set_inter [simp]:
  "the_set (A \<inter> B) = the_set A \<inter> the_set B"
  by (fastforce simp: the_set_def)

lemma the_set_inter_empty:
  "A \<inter> B = {} \<Longrightarrow> the_set A \<inter> the_set B = {}"
  by (fastforce simp: the_set_def)

lemma the_set_empty[simp]: "the_set {} = {}"
  by (simp add: the_set_def)

lemma the_set_UNIV [simp]:
  "the_set UNIV = UNIV"
  by (clarsimp simp: the_set_def)

lemma the_set_slot [simp]:
  "the_set (Slot ` xs) = xs"
  by (fastforce simp: the_set_def)

lemma the_set_singleton_slot [simp]:
  "the_set {Slot x} = {x}"
  by (clarsimp simp: the_set_def)

lemma the_set_singleton_fields [simp]:
  "the_set {Fields} = {}"
  by (clarsimp simp: the_set_def)

(* The sep_entitys are the entities we are interested in sep_capdl,
   and it includes objects and caps
*)
datatype sep_entity = CDL_Object cdl_object | CDL_Cap "cdl_cap option"

(* "Cleans" slots to conform with the compontents. *)
definition
  clean_slots :: "cdl_cap_map \<Rightarrow> cdl_components \<Rightarrow> cdl_cap_map"
where
  "clean_slots slots cmp \<equiv> slots |` the_set cmp"

(* Sets the fields of an object to a "clean" state.
   Because a frame's size is part of it's type, we don't reset it. *)
definition
  object_clean_fields :: "cdl_object \<Rightarrow> cdl_components \<Rightarrow> cdl_object"
where
  "object_clean_fields obj cmp \<equiv> if Fields \<in> cmp then obj else case obj of
    Tcb x \<Rightarrow> Tcb (x\<lparr>cdl_tcb_fault_endpoint := undefined,
                   cdl_tcb_intent := undefined,
                   cdl_tcb_has_fault := undefined,
                   cdl_tcb_domain := undefined\<rparr>)
  | CNode x \<Rightarrow> CNode (x\<lparr>cdl_cnode_size_bits := undefined \<rparr>)
  | _ \<Rightarrow> obj"

(* Sets the slots of an object to a "clean" state. *)
definition
  object_clean_slots :: "cdl_object \<Rightarrow> cdl_components \<Rightarrow> cdl_object"
where
  "object_clean_slots obj cmp \<equiv> update_slots (clean_slots (object_slots obj) cmp) obj"

(* Sets an object to a "clean" state. *)
definition
  object_clean :: "cdl_object \<Rightarrow> cdl_components \<Rightarrow> cdl_object"
where
  "object_clean obj cmps \<equiv> object_clean_slots (object_clean_fields obj cmps) cmps"

(* The state for separation logic is an option map
   from (ptr,component) to sep_entities
 *)

type_synonym sep_state_heap = "(cdl_object_id \<times> cdl_component) \<Rightarrow> sep_entity option"
type_synonym sep_state_irq_map = "cdl_irq \<Rightarrow> cdl_object_id option"

translations
  (type) "sep_state_heap" <=(type) "32 word \<times> cdl_component \<Rightarrow> sep_entity option"
  (type) "sep_state_irq_map" <=(type) "8 word \<Rightarrow> 32 word option"

datatype sep_state =
  SepState "(cdl_object_id \<times> cdl_component) \<Rightarrow> sep_entity option"
           "cdl_irq \<Rightarrow> cdl_object_id option"

(* Functions to get the object heap and the irq table from the sep_state. *)
primrec sep_heap :: "sep_state \<Rightarrow> sep_state_heap"
where "sep_heap (SepState heap irqs) = heap"

primrec sep_irq_node :: "sep_state \<Rightarrow> sep_state_irq_map"
where "sep_irq_node (SepState heap irqs) = irqs"

definition
  sep_caps :: "sep_state_heap \<Rightarrow> 32 word \<Rightarrow> cdl_cap_map"
where
  "sep_caps s ptr \<equiv> \<lambda>slot. case s (ptr, Slot slot) of
      Some (CDL_Cap x ) \<Rightarrow> x
    | _ \<Rightarrow> None"

definition
  sep_objects :: "sep_state_heap \<Rightarrow> cdl_heap"
where
  "sep_objects s \<equiv> \<lambda>ptr. case s (ptr,Fields) of
      Some (CDL_Object obj) \<Rightarrow> Some (update_slots (sep_caps s ptr) obj)
    | _ \<Rightarrow> None"

(* Adding states adds the objects an their ownerships.
 *)
definition
  sep_state_add :: "sep_state \<Rightarrow> sep_state \<Rightarrow> sep_state"
where
  "sep_state_add state_a state_b \<equiv>
  SepState ((sep_heap state_a) ++ (sep_heap state_b))
           ((sep_irq_node state_a) ++ sep_irq_node state_b)"


(* Heaps are disjoint if for all of their objects:
   * the caps of their respective objects are disjoint,
   * their respective objects don't conflict,
   * they don't both own any of the same fields.
*)
definition
  sep_state_disj :: "sep_state \<Rightarrow> sep_state \<Rightarrow> bool"
where
  "sep_state_disj state_a state_b \<equiv>
   (sep_heap state_a) \<bottom> (sep_heap state_b) \<and>
   (sep_irq_node state_a) \<bottom> (sep_irq_node state_b)"

lemma map_add_emptyE [elim!]:
  "\<lbrakk>a ++ b = empty; \<lbrakk>a = empty; b = empty\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (metis map_add_None)

lemma clean_slots_Fields [simp]:
  "clean_slots slots {Fields} = empty"
  by (clarsimp simp: clean_slots_def the_set_def)

lemma clean_slots_empty [simp]:
  "clean_slots empty cmp = empty"
  by (clarsimp simp: clean_slots_def)

lemma clean_slots_singleton [simp]:
  "clean_slots [slot \<mapsto> cap] {Slot slot} = [slot \<mapsto> cap]"
  by (clarsimp simp: clean_slots_def)

lemma object_type_update_slots [simp]:
  "object_type (update_slots slots x) = object_type x"
  by (clarsimp simp: object_type_def update_slots_def split: cdl_object.splits)

lemma object_type_object_clean_slots [simp]:
  "object_type (object_clean_slots x cmp) = object_type x"
  by (clarsimp simp: object_clean_slots_def)

lemma object_type_object_clean_fields [simp]:
  "object_type (object_clean_fields x cmp) = object_type x"
  by (clarsimp simp: object_clean_fields_def object_type_def split: cdl_object.splits)

lemma object_type_object_clean [simp]:
  "object_type (object_clean x cmp) = object_type x"
  by (clarsimp simp: object_clean_def)

lemma object_slots_empty [simp]:
  "\<not> has_slots obj \<Longrightarrow> object_slots obj = empty"
  by (clarsimp simp: object_slots_def has_slots_def split: cdl_object.splits)

lemma object_slots_update_slots [simp]:
  "has_slots obj \<Longrightarrow> object_slots (update_slots slots obj) = slots"
  by (clarsimp simp: object_slots_def update_slots_def has_slots_def
              split: cdl_object.splits)

lemma object_slots_update_slots_empty [simp]:
  "\<not>has_slots obj \<Longrightarrow> object_slots (update_slots slots obj) = empty"
  by (clarsimp simp: object_slots_def update_slots_def has_slots_def
                 split: cdl_object.splits)

lemma update_slots_no_slots [simp]:
  "\<not>has_slots obj \<Longrightarrow> update_slots slots obj = obj"
  by (clarsimp simp: update_slots_def has_slots_def split: cdl_object.splits)

lemma update_slots_update_slots [simp]:
  "update_slots slots (update_slots slots' obj) = update_slots slots obj"
  by (clarsimp simp: update_slots_def split: cdl_object.splits)

lemma update_slots_same_object:
  "a = b \<Longrightarrow> update_slots a obj = update_slots b obj"
  by (erule arg_cong)

lemma update_slots_eq_slots:
  "\<lbrakk>has_slots obj; update_slots slots obj = update_slots slots' obj'\<rbrakk> \<Longrightarrow> slots = slots'"
  by (clarsimp simp: update_slots_def has_slots_def cdl_tcb.splits cdl_cnode.splits
                     cdl_asid_pool.splits cdl_page_table.splits cdl_page_directory.splits
              split: cdl_object.splits)

lemma has_slots_object_type_has_slots:
  "\<lbrakk>has_slots x; object_type x = object_type y\<rbrakk> \<Longrightarrow> has_slots y"
  by (clarsimp simp: object_type_def has_slots_def split: cdl_object.splits)

lemma object_type_has_slots_eq:
  "object_type y = object_type x \<Longrightarrow> has_slots x = has_slots y"
  by (clarsimp simp: object_type_def has_slots_def split: cdl_object.splits)

lemma object_slots_object_clean_fields [simp]:
  "object_slots (object_clean_fields obj cmp) = object_slots obj"
  by (clarsimp simp: object_slots_def object_clean_fields_def split: cdl_object.splits)

lemma object_slots_object_clean_slots [simp]:
  "object_slots (object_clean_slots obj cmp) = clean_slots (object_slots obj) cmp"
  by (clarsimp simp: object_clean_slots_def object_slots_def update_slots_def split: cdl_object.splits)

lemma object_slots_object_clean [simp]:
  "object_slots (object_clean obj cmp) = clean_slots (object_slots obj) cmp"
  by (clarsimp simp: object_clean_def)


lemma update_slots_object_clean_slots [simp]:
  "update_slots slots (object_clean_slots obj cmp) = update_slots slots obj"
  by (clarsimp simp: object_clean_slots_def)

lemma object_clean_fields_idem [simp]:
  "object_clean_fields (object_clean_fields obj cmp) cmp = object_clean_fields obj cmp"
  by (clarsimp simp: object_clean_fields_def split: cdl_object.splits)

lemma object_clean_slots_idem [simp]:
  "object_clean_slots (object_clean_slots obj cmp) cmp = object_clean_slots obj cmp"
  apply (case_tac  "has_slots obj")
  apply (clarsimp simp: object_clean_slots_def clean_slots_def)+
  done

lemma object_clean_fields_object_clean_slots [simp]:
  "object_clean_fields (object_clean_slots obj cmps) cmps = object_clean_slots (object_clean_fields obj cmps) cmps"
  by (clarsimp simp: object_clean_fields_def object_clean_slots_def
                     clean_slots_def object_slots_def update_slots_def
              split: cdl_object.splits)

lemma object_clean_idem [simp]:
  "object_clean (object_clean obj cmp) cmp = object_clean obj cmp"
  by (clarsimp simp: object_clean_def)

lemma has_slots_object_clean_slots:
 "has_slots (object_clean_slots obj cmp) = has_slots obj"
  by (clarsimp simp: has_slots_def object_clean_slots_def update_slots_def split: cdl_object.splits)

lemma has_slots_object_clean_fields:
 "has_slots (object_clean_fields obj cmp) = has_slots obj"
  by (clarsimp simp: has_slots_def object_clean_fields_def split: cdl_object.splits)

lemma has_slots_object_clean:
 "has_slots (object_clean obj cmp) = has_slots obj"
  by (clarsimp simp: object_clean_def has_slots_object_clean_slots has_slots_object_clean_fields)

lemma object_slots_update_slots_object_clean_fields [simp]:
  "object_slots (update_slots slots (object_clean_fields obj cmp)) = object_slots (update_slots slots obj)"
  apply (case_tac "has_slots obj")
   apply (clarsimp simp: has_slots_object_clean_fields)+
  done

lemma object_clean_fields_update_slots [simp]:
 "object_clean_fields (update_slots slots obj) cmp = update_slots slots (object_clean_fields obj cmp)"
  by (clarsimp simp: object_clean_fields_def update_slots_def split: cdl_object.splits)

lemma object_clean_fields_twice [simp]:
  "(object_clean_fields (object_clean_fields obj cmp') cmp) = object_clean_fields obj (cmp \<inter> cmp')"
  by (clarsimp simp: object_clean_fields_def split: cdl_object.splits)

lemma object_clean_fields_slot [simp]:
  "object_clean_fields obj (Slot ` slots) = object_clean_fields obj {}"
  by (clarsimp simp: object_clean_fields_def)

lemma object_clean_fields_slot' [simp]:
  "object_clean_fields obj {Slot slot} = object_clean_fields obj {}"
  by (clarsimp simp: object_clean_fields_def)

lemma object_clean_slots_empty_slots:
  "object_clean_slots obj (Slot ` (UNIV - dom (object_slots obj))) = object_clean_slots obj {}"
  by (clarsimp simp: object_clean_slots_def clean_slots_def)

lemma object_clean_empty_slots [simp]:
  "object_clean obj (Slot ` (UNIV - dom (object_slots obj))) = object_clean obj {}"
  by (clarsimp simp: object_clean_def object_clean_slots_def clean_slots_def)

lemma update_slots_object_clean_fields:
  "\<lbrakk>Fields \<notin> cmps; Fields \<notin> cmps'; object_type obj = object_type obj'\<rbrakk>
    \<Longrightarrow> update_slots slots (object_clean_fields obj cmps) =
        update_slots slots (object_clean_fields obj' cmps')"
  by (fastforce simp: update_slots_def object_clean_fields_def object_type_def split: cdl_object.splits)

lemma object_clean_fields_no_slots:
  "\<lbrakk>Fields \<notin> cmps; Fields \<notin> cmps'; object_type obj = object_type obj'; \<not> has_slots obj\<rbrakk>
    \<Longrightarrow> object_clean_fields obj cmps = object_clean_fields obj' cmps'"
  by (fastforce simp: object_clean_fields_def object_type_def has_slots_def split: cdl_object.splits)

lemma update_slots_object_clean:
  "\<lbrakk>Fields \<notin> cmps; Fields \<notin> cmps'; object_type obj = object_type obj'\<rbrakk>
   \<Longrightarrow> update_slots slots (object_clean obj cmps) = update_slots slots (object_clean obj' cmps')"
  apply (clarsimp simp: object_clean_def object_clean_slots_def)
  apply (erule (2) update_slots_object_clean_fields)
  done

lemma clean_slots_slot_same:
  "\<lbrakk>object_slots obj slot = object_slots obj' slot\<rbrakk>
  \<Longrightarrow> clean_slots (object_slots obj) {Slot slot} = clean_slots (object_slots obj') {Slot slot}"
  by (fastforce simp: clean_slots_def restrict_map_def)

lemma object_clean_single_slot_equal:
  "\<lbrakk>object_slots obj slot = object_slots obj' slot; object_type obj = object_type obj'\<rbrakk>
  \<Longrightarrow> object_clean obj {Slot slot} = object_clean obj' {Slot slot}"
  apply (clarsimp simp: object_clean_def object_clean_slots_def)
  apply (drule clean_slots_slot_same, simp)
  apply (clarsimp simp: update_slots_def object_clean_fields_def object_type_def
                 split: cdl_object.splits)
  done

lemma clean_slots_map_add_comm:
  "cmps_a \<inter> cmps_b = {}
  \<Longrightarrow> clean_slots slots_a cmps_a ++ clean_slots slots_b cmps_b =
      clean_slots slots_b cmps_b ++ clean_slots slots_a cmps_a"
  apply (clarsimp simp: clean_slots_def)
  apply (drule the_set_inter_empty)
  apply (erule map_add_restrict_comm)
  done

lemma object_clean_all:
  "object_type obj_a = object_type obj_b \<Longrightarrow> object_clean obj_b {} = object_clean obj_a {}"
  apply (clarsimp simp: object_clean_def object_clean_slots_def clean_slots_def)
  apply (rule_tac cmps'1="{}" and obj'1="obj_a" in trans [OF update_slots_object_clean_fields], fastforce+)
  done

lemma sep_state_add_comm:
  "sep_state_disj x y \<Longrightarrow> sep_state_add x y = sep_state_add y x"
  by (fastforce simp: sep_state_add_def sep_state_disj_def intro!:map_add_com)

lemma sep_state_add_disjL:
  "\<lbrakk>sep_state_disj y z; sep_state_disj x (sep_state_add y z)\<rbrakk>
  \<Longrightarrow> sep_state_disj x y"
  by (fastforce simp: sep_state_disj_def
    sep_state_add_def map_disj_def)

lemma sep_state_add_disjR:
  "\<lbrakk>sep_state_disj y z; sep_state_disj x (sep_state_add y z)\<rbrakk> \<Longrightarrow> sep_state_disj x z"
  by (fastforce simp: sep_state_disj_def sep_state_add_def map_disj_def )

lemma sep_state_add_disj:
  "\<lbrakk>sep_state_disj y z; sep_state_disj x y; sep_state_disj x z\<rbrakk> \<Longrightarrow> sep_state_disj x (sep_state_add y z)"
  by (fastforce simp: sep_state_disj_def sep_state_add_def map_disj_def )



(*********************************************)
(* Definition of separation logic for capDL. *)
(*********************************************)

instantiation "sep_state" :: zero
begin
  definition "0 \<equiv> SepState (\<lambda>p. None) empty"
  instance ..
end

instantiation "sep_state" :: stronger_sep_algebra
begin

definition "(op ##) \<equiv> sep_state_disj"
definition "(op +) \<equiv> sep_state_add"



(**********************************************
 * The proof that this is a separation logic. *
 **********************************************)

instance
  apply default
(* x ## 0 *)
       apply (simp add: sep_disj_sep_state_def sep_state_disj_def zero_sep_state_def)
(* x ## y \<Longrightarrow> y ## x *)
      apply (clarsimp simp: sep_disj_sep_state_def sep_state_disj_def Let_unfold
                            map_disj_com  Int_commute)
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
   apply (auto simp:map_disj_def sep_state_disj_def)
  done
end

end
