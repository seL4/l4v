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

chapter "Instantiating capDL as a separation algebra."

theory Abstract_Separation_D
imports
  "../../Sep_Tactics"
  Types_D
  "../../Map_Extra"
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

(************************************
 * End of lemmas to move elsewhere. *
 ************************************)



(* The state for separation logic has:
   * The memory heap.
   * A function for which objects own which fields.
     In capDL, we say that an object either owns all of its fields, or none of them.
   These are both taken from the cdl_state.
 *)

datatype sep_state = SepState cdl_heap cdl_ghost_state

(* Functions to get the heap and the ghost_state from the sep_state. *)
primrec sep_heap :: "sep_state \<Rightarrow> cdl_heap"
where  "sep_heap (SepState h gs) = h"

primrec sep_ghost_state :: "sep_state \<Rightarrow> cdl_ghost_state"
where  "sep_ghost_state (SepState h gs) = gs"

definition
  the_set :: "'a option set \<Rightarrow> 'a set"
where
  "the_set xs = {x. Some x \<in> xs}"

lemma the_set_union [simp]:
  "the_set (A \<union> B) = the_set A \<union> the_set B"
  by (fastforce simp: the_set_def)

lemma the_set_inter [simp]:
  "the_set (A \<inter> B) = the_set A \<inter> the_set B"
  by (fastforce simp: the_set_def)

lemma the_set_inter_empty:
  "A \<inter> B = {} \<Longrightarrow> the_set A \<inter> the_set B = {}"
  by (fastforce simp: the_set_def)


(* As the capDL operations mostly take the state (rather than the heap)
 * we need to redefine some of them again to take just the heap.
 *)
definition
  slots_of_heap :: "cdl_heap \<Rightarrow> cdl_object_id \<Rightarrow> cdl_cap_map"
where
  "slots_of_heap h \<equiv> \<lambda>obj_id. 
  case h obj_id of 
    None \<Rightarrow> empty 
  | Some obj \<Rightarrow> object_slots obj"

(* Adds new caps to an object. It won't overwrite on a collision. *)
definition
  add_to_slots :: "cdl_cap_map \<Rightarrow> cdl_object \<Rightarrow> cdl_object"
where
  "add_to_slots new_val obj \<equiv> update_slots (new_val ++ (object_slots obj)) obj"

lemma add_to_slots_assoc:
  "add_to_slots x (add_to_slots (y ++ z) obj) = 
   add_to_slots (x ++ y) (add_to_slots z obj)"
  apply (clarsimp simp: add_to_slots_def update_slots_def object_slots_def)
  apply (fastforce simp: cdl_tcb.splits cdl_cnode.splits
                 split: cdl_object.splits)
  done

(* Lemmas about add_to_slots, update_slots and object_slots. *)
lemma add_to_slots_twice [simp]:
  "add_to_slots x (add_to_slots y a) = add_to_slots (x ++ y) a"
  by (fastforce simp: add_to_slots_def update_slots_def object_slots_def
              split: cdl_object.splits)

lemma slots_of_heap_empty [simp]: "slots_of_heap empty object_id = empty"
  by (simp add: slots_of_heap_def)

lemma slots_of_heap_empty2 [simp]:
  "h obj_id = None \<Longrightarrow> slots_of_heap h obj_id = empty"
  by (simp add: slots_of_heap_def)

lemma update_slots_add_to_slots_empty [simp]:
  "update_slots empty (add_to_slots new obj) = update_slots empty obj"
  by (clarsimp simp: update_slots_def add_to_slots_def split:cdl_object.splits)

lemma update_object_slots_id [simp]: "update_slots (object_slots a) a = a"
  by (clarsimp simp: update_slots_def object_slots_def
              split: cdl_object.splits)

lemma update_slots_of_heap_id [simp]:
  "h obj_id = Some obj \<Longrightarrow> update_slots (slots_of_heap h obj_id) obj = obj"
  by (clarsimp simp: update_slots_def slots_of_heap_def object_slots_def
              split: cdl_object.splits)

lemma add_to_slots_empty [simp]: "add_to_slots empty h = h"
  by (simp add: add_to_slots_def)

lemma update_slots_eq:
  "update_slots a o1 = update_slots a o2 \<Longrightarrow> update_slots b o1 = update_slots b o2"
  by (fastforce simp: update_slots_def cdl_tcb.splits cdl_cnode.splits
              split: cdl_object.splits)



(* If there are not two conflicting objects at a position in two states.
 * Objects conflict if their types are different or their ghost_states collide.
 *)
definition
  not_conflicting_objects :: "sep_state \<Rightarrow> sep_state \<Rightarrow> cdl_object_id \<Rightarrow> bool"
where
  "not_conflicting_objects state_a state_b = (\<lambda>obj_id.
 let heap_a = sep_heap state_a;
     heap_b = sep_heap state_b;
     gs_a = sep_ghost_state state_a;
     gs_b = sep_ghost_state state_b
 in case (heap_a obj_id, heap_b obj_id) of 
    (Some o1, Some o2) \<Rightarrow> object_type o1 = object_type o2 \<and> gs_a obj_id \<inter> gs_b obj_id = {}
   | _ \<Rightarrow> True)"


(* "Cleans" slots to conform with the components. *)
definition
  clean_slots :: "cdl_cap_map \<Rightarrow> cdl_components \<Rightarrow> cdl_cap_map"
where
  "clean_slots slots cmp \<equiv> slots |` the_set cmp"

(* Sets the fields of an object to a "clean" state.
   Because a frame's size is part of it's type, we don't reset it. *)
definition
  object_clean_fields :: "cdl_object \<Rightarrow> cdl_components \<Rightarrow> cdl_object"
where
  "object_clean_fields obj cmp \<equiv> if None \<in> cmp then obj else case obj of
    Tcb x \<Rightarrow> Tcb (x\<lparr>cdl_tcb_fault_endpoint := undefined\<rparr>)
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
  "object_clean obj gs \<equiv> object_clean_slots (object_clean_fields obj gs) gs"

(* Overrides the left object with the attributes of the right, as specified by the ghost state.
   If the components for an object are empty, then this object is treated as empty, and thus ignored.
 *)
definition
  object_add :: "cdl_object \<Rightarrow> cdl_object \<Rightarrow> cdl_components \<Rightarrow> cdl_components \<Rightarrow> cdl_object"
where
  "object_add obj_a obj_b cmps_a cmps_b \<equiv>
  let clean_obj_a = object_clean obj_a cmps_a;
      clean_obj_b = object_clean obj_b cmps_b
  in if (cmps_a = {})
     then clean_obj_b
     else if (cmps_b = {})
     then clean_obj_a
     else if (None \<in> cmps_b)
     then (update_slots (object_slots clean_obj_a ++ object_slots clean_obj_b) clean_obj_b)
     else (update_slots (object_slots clean_obj_a ++ object_slots clean_obj_b) clean_obj_a)"

(* Heaps are added by adding their respective objects.
 * The ghost state tells us which object's fields should be taken.
 * Adding objects of the same type adds their caps
 *   (overwrites the left with the right).
 *)
definition
  cdl_heap_add :: "sep_state \<Rightarrow> sep_state \<Rightarrow> cdl_heap"
where
  "cdl_heap_add state_a state_b \<equiv> \<lambda>obj_id.
  let
    heap_a = sep_heap state_a;
    heap_b = sep_heap state_b;
    gs_a = sep_ghost_state state_a;
    gs_b = sep_ghost_state state_b
  in
    case heap_b obj_id of
      None \<Rightarrow> heap_a obj_id
    | Some obj_b \<Rightarrow> 
        (case heap_a obj_id of
           None \<Rightarrow> heap_b obj_id
         | Some obj_a \<Rightarrow> Some (object_add obj_a obj_b (gs_a obj_id) (gs_b obj_id)))"

(* Heaps are added by adding their repsective objects.
 * The ghost state tells us which object's fields should be taken.
 * Adding objects of the same type adds their caps
 *   (overwrites the left with the right).
 *)
definition
  cdl_ghost_state_add :: "sep_state \<Rightarrow> sep_state \<Rightarrow> cdl_ghost_state"
where
  "cdl_ghost_state_add state_a state_b \<equiv> \<lambda>obj_id.
 let heap_a = sep_heap state_a;
     heap_b = sep_heap state_b;
     gs_a = sep_ghost_state state_a;
     gs_b = sep_ghost_state state_b
 in      if heap_a obj_id = None \<and> heap_b obj_id \<noteq> None then gs_b obj_id
    else if heap_b obj_id = None \<and> heap_a obj_id \<noteq> None then gs_a obj_id
    else gs_a obj_id \<union> gs_b obj_id"


(* Adding states adds their heaps,
 *  and each objects owns whichever fields it owned in either heap.
 *)
definition
  sep_state_add :: "sep_state \<Rightarrow> sep_state \<Rightarrow> sep_state"
where
  "sep_state_add state_a state_b \<equiv>
  let
    heap_a = sep_heap state_a;
    heap_b = sep_heap state_b;
    gs_a = sep_ghost_state state_a;
    gs_b = sep_ghost_state state_b
  in
    SepState (cdl_heap_add state_a state_b) (cdl_ghost_state_add state_a state_b)"


(* Heaps are disjoint if for all of their objects:
   * the caps of their respective objects are disjoint,
   * their respective objects don't conflict,
   * they don't both own any of the same fields.
*)
definition
  sep_state_disj :: "sep_state \<Rightarrow> sep_state \<Rightarrow> bool"
where
  "sep_state_disj state_a state_b \<equiv>
  let
    heap_a = sep_heap state_a;
    heap_b = sep_heap state_b;
    gs_a = sep_ghost_state state_a;
    gs_b = sep_ghost_state state_b
  in
    \<forall>obj_id. not_conflicting_objects state_a state_b obj_id"

lemma not_conflicting_objects_comm:
  "not_conflicting_objects h1 h2 obj = not_conflicting_objects h2 h1 obj"
  apply (clarsimp simp: not_conflicting_objects_def split:option.splits)
  apply (fastforce simp: update_slots_def cdl_tcb.splits cdl_cnode.splits
              split: cdl_object.splits)
  done

lemma object_clean_comm:
  "\<lbrakk>object_type obj_a = object_type obj_b;
    object_slots obj_a ++ object_slots obj_b = object_slots obj_b ++ object_slots obj_a; None \<notin> cmp\<rbrakk>
  \<Longrightarrow> object_clean (add_to_slots (object_slots obj_a) obj_b) cmp =
      object_clean (add_to_slots (object_slots obj_b) obj_a) cmp"
  apply (clarsimp simp: object_type_def split: cdl_object.splits)
  apply (clarsimp simp: object_clean_def object_clean_slots_def object_clean_fields_def
                        add_to_slots_def object_slots_def update_slots_def
                        cdl_tcb.splits cdl_cnode.splits
                 split: cdl_object.splits)+
  done

lemma add_to_slots_object_slots:
  "object_type y = object_type z
 \<Longrightarrow> add_to_slots (object_slots (add_to_slots (x) y)) z =
     add_to_slots (x ++ object_slots y) z"
  apply (clarsimp simp: add_to_slots_def update_slots_def object_slots_def)
  apply (fastforce simp: object_type_def cdl_tcb.splits cdl_cnode.splits
                 split: cdl_object.splits)
  done

lemma not_conflicting_objects_empty [simp]:
  "not_conflicting_objects s (SepState empty (\<lambda>obj_id. {})) obj_id"
  by (clarsimp simp: not_conflicting_objects_def split:option.splits)

lemma empty_not_conflicting_objects [simp]:
  "not_conflicting_objects (SepState empty (\<lambda>obj_id. {})) s obj_id"
  by (clarsimp simp: not_conflicting_objects_def split:option.splits)

lemma not_conflicting_objects_empty_object [elim!]:
  "(sep_heap x) obj_id = None \<Longrightarrow> not_conflicting_objects x y obj_id"
  by (clarsimp simp: not_conflicting_objects_def)

lemma empty_object_not_conflicting_objects [elim!]:
  "(sep_heap y) obj_id = None \<Longrightarrow> not_conflicting_objects x y obj_id"
  apply (drule not_conflicting_objects_empty_object [where y=x])
  apply (clarsimp simp: not_conflicting_objects_comm)
  done

lemma cdl_heap_add_empty [simp]:
 "cdl_heap_add (SepState h gs) (SepState empty (\<lambda>obj_id. {})) = h"
  by (simp add: cdl_heap_add_def)

lemma empty_cdl_heap_add [simp]:
  "cdl_heap_add (SepState empty (\<lambda>obj_id. {})) (SepState h gs)= h"
  apply (simp add: cdl_heap_add_def)
  apply (rule ext)
  apply (clarsimp split: option.splits)
  done

lemma map_add_result_empty1: "a ++ b = empty \<Longrightarrow> a = empty"
  apply (subgoal_tac "dom (a++b) = {}")
   apply (subgoal_tac "dom (a) = {}")
    apply clarsimp
   apply (unfold dom_map_add)[1]
   apply clarsimp
  apply clarsimp
  done

lemma map_add_result_empty2: "a ++ b = empty \<Longrightarrow> b = empty"
  apply (subgoal_tac "dom (a++b) = {}")
   apply (subgoal_tac "dom (a) = {}")
    apply clarsimp
   apply (unfold dom_map_add)[1]
   apply clarsimp
  apply clarsimp
  done

lemma map_add_emptyE [elim!]: "\<lbrakk>a ++ b = empty; \<lbrakk>a = empty; b = empty\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  apply (frule map_add_result_empty1)
  apply (frule map_add_result_empty2)
  apply clarsimp
  done

lemma clean_slots_empty [simp]:
  "clean_slots empty cmp = empty"
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

lemma object_type_add_to_slots [simp]:
  "object_type (add_to_slots slots x) = object_type x"
  by (clarsimp simp: object_type_def add_to_slots_def update_slots_def split: cdl_object.splits)

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

lemma object_type_has_slots:
  "\<lbrakk>has_slots x; object_type x = object_type y\<rbrakk> \<Longrightarrow> has_slots y"
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

lemma object_slots_add_to_slots [simp]:
  "object_type y = object_type z \<Longrightarrow> object_slots (add_to_slots (object_slots y) z) = object_slots y ++ object_slots z"
  by (clarsimp simp: object_slots_def add_to_slots_def update_slots_def object_type_def split: cdl_object.splits)

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
  "object_clean_fields (object_clean_slots obj gs) gs = object_clean_slots (object_clean_fields obj gs) gs"
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

lemma update_slots_object_clean_fields:
  "\<lbrakk>None \<notin> cmps; None \<notin> cmps'; object_type obj = object_type obj'\<rbrakk>
    \<Longrightarrow> update_slots slots (object_clean_fields obj cmps) =
        update_slots slots (object_clean_fields obj' cmps')"
  by (fastforce simp: update_slots_def object_clean_fields_def object_type_def split: cdl_object.splits)

lemma object_clean_fields_no_slots:
  "\<lbrakk>None \<notin> cmps; None \<notin> cmps'; object_type obj = object_type obj'; \<not> has_slots obj; \<not> has_slots obj'\<rbrakk>
    \<Longrightarrow> object_clean_fields obj cmps = object_clean_fields obj' cmps'"
  by (fastforce simp: object_clean_fields_def object_type_def has_slots_def split: cdl_object.splits)

lemma update_slots_object_clean:
  "\<lbrakk>None \<notin> cmps; None \<notin> cmps'; object_type obj = object_type obj'\<rbrakk>
   \<Longrightarrow> update_slots slots (object_clean obj cmps) = update_slots slots (object_clean obj' cmps')"
  apply (clarsimp simp: object_clean_def object_clean_slots_def)
  apply (erule (2) update_slots_object_clean_fields)
  done

lemma cdl_heap_add_assoc':
  "\<forall>obj_id. not_conflicting_objects x z obj_id \<and>
            not_conflicting_objects y z obj_id \<and>
            not_conflicting_objects x z obj_id \<Longrightarrow>
   cdl_heap_add (SepState (cdl_heap_add x y) (cdl_ghost_state_add x y)) z =
   cdl_heap_add x (SepState (cdl_heap_add y z) (cdl_ghost_state_add y z))"
  apply (rule ext)
  apply (rename_tac obj_id)
  apply (erule_tac x=obj_id in allE)
  apply (clarsimp simp: cdl_heap_add_def cdl_ghost_state_add_def not_conflicting_objects_def)
  apply (simp add: Let_unfold split: option.splits)
  apply (rename_tac obj_y obj_x obj_z)
  apply (clarsimp simp: object_add_def clean_slots_def object_clean_def object_clean_slots_def Let_unfold)
  apply (case_tac "has_slots obj_z")
   apply (subgoal_tac "has_slots obj_y")
    apply (subgoal_tac "has_slots obj_x")
     apply ((clarsimp simp: has_slots_object_clean_fields has_slots_object_clean_slots has_slots_object_clean
                           map_add_restrict union_intersection | 
            drule inter_empty_not_both | 
            erule update_slots_object_clean_fields |
            erule object_type_has_slots, simp |
            simp | safe)+)[3]
   apply (subgoal_tac "\<not> has_slots obj_y")
    apply (subgoal_tac "\<not> has_slots obj_x")
     apply ((clarsimp simp: has_slots_object_clean_fields has_slots_object_clean_slots has_slots_object_clean
                           map_add_restrict union_intersection | 
            drule inter_empty_not_both | 
            erule object_clean_fields_no_slots |
            erule object_type_has_slots, simp |
            simp | safe)+)
   apply (fastforce simp: object_type_has_slots)+
  done

lemma cdl_heap_add_assoc:
  "\<lbrakk>sep_state_disj x y; sep_state_disj y z; sep_state_disj x z\<rbrakk>
  \<Longrightarrow> cdl_heap_add (SepState (cdl_heap_add x y) (cdl_ghost_state_add x y)) z =
      cdl_heap_add x (SepState (cdl_heap_add y z) (cdl_ghost_state_add y z))"
  apply (clarsimp simp: sep_state_disj_def)
  apply (cut_tac cdl_heap_add_assoc')
   apply fast
  apply fastforce
  done

lemma cdl_ghost_state_add_assoc:
  "cdl_ghost_state_add (SepState (cdl_heap_add x y) (cdl_ghost_state_add x y)) z =
   cdl_ghost_state_add x (SepState (cdl_heap_add y z) (cdl_ghost_state_add y z))"
  apply (rule ext)
  apply (fastforce simp: cdl_heap_add_def cdl_ghost_state_add_def Let_unfold)
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
  apply (clarsimp simp: object_clean_def object_clean_slots_def clean_slots_def the_set_def)
  apply (rule_tac cmps'1="{}" and obj'1="obj_a" in trans [OF update_slots_object_clean_fields], fastforce+)
  done

lemma object_add_comm:
  "\<lbrakk>object_type obj_a = object_type obj_b; cmps_a \<inter> cmps_b = {}\<rbrakk>
  \<Longrightarrow> object_add obj_a obj_b cmps_a cmps_b = object_add obj_b obj_a cmps_b cmps_a"
  apply (clarsimp simp: object_add_def Let_unfold)
  apply (rule conjI | clarsimp)+
    apply fastforce
  apply (rule conjI | clarsimp)+
   apply (drule_tac slots_a = "object_slots obj_a" and slots_b = "object_slots obj_b" in clean_slots_map_add_comm)
   apply fastforce
  apply (rule conjI | clarsimp)+
   apply (drule_tac slots_a = "object_slots obj_a" and slots_b = "object_slots obj_b" in clean_slots_map_add_comm)
   apply fastforce
  apply (rule conjI | clarsimp)+
   apply (erule object_clean_all)
  apply (clarsimp)
  apply (rule_tac cmps'1=cmps_b and obj'1=obj_b in trans [OF update_slots_object_clean], assumption+)
  apply (drule_tac slots_a = "object_slots obj_a" and slots_b = "object_slots obj_b" in clean_slots_map_add_comm)
  apply fastforce
  done

lemma sep_state_add_comm:
  "sep_state_disj x y \<Longrightarrow> sep_state_add x y = sep_state_add y x"
  apply (clarsimp simp: sep_state_add_def sep_state_disj_def)
  apply (rule conjI)
   apply (case_tac x, case_tac y, clarsimp)
   apply (rename_tac heap_a gs_a heap_b gs_b)
   apply (clarsimp simp: cdl_heap_add_def Let_unfold)
   apply (rule ext)
   apply (case_tac "heap_a obj_id")
    apply (case_tac "heap_b obj_id", simp_all add: slots_of_heap_def)
   apply (case_tac "heap_b obj_id", simp_all add: slots_of_heap_def)
   apply (rename_tac obj_a obj_b)
   apply (erule_tac x=obj_id in allE)
   apply (rule object_add_comm)
    apply (clarsimp simp: not_conflicting_objects_def)
   apply (clarsimp simp: not_conflicting_objects_def)
  apply (rule ext, fastforce simp: cdl_ghost_state_add_def Let_unfold Un_commute)
  done

lemma add_to_slots_comm:
  "\<lbrakk>object_slots y_obj \<bottom> object_slots z_obj; update_slots empty y_obj = update_slots empty z_obj \<rbrakk>
  \<Longrightarrow> add_to_slots (object_slots z_obj) y_obj = add_to_slots (object_slots y_obj) z_obj"
  by (fastforce simp: add_to_slots_def update_slots_def object_slots_def
                     cdl_tcb.splits cdl_cnode.splits
              dest!: map_add_com
              split: cdl_object.splits)

lemma cdl_heap_add_none1:
  "cdl_heap_add x y obj_id = None \<Longrightarrow> (sep_heap x) obj_id = None"
  by (clarsimp simp: cdl_heap_add_def Let_unfold split:option.splits if_split_asm)

lemma cdl_heap_add_none2:
  "cdl_heap_add x y obj_id = None \<Longrightarrow> (sep_heap y) obj_id = None"
  by (clarsimp simp: cdl_heap_add_def Let_unfold split:option.splits if_split_asm)

lemma object_type_object_addL:
  "object_type obj = object_type obj'
  \<Longrightarrow> object_type (object_add obj obj' cmp cmp') = object_type obj"
  by (clarsimp simp: object_add_def Let_unfold)

lemma object_type_object_addR:
  "object_type obj = object_type obj'
  \<Longrightarrow> object_type (object_add obj obj' cmp cmp') = object_type obj'"
  by (clarsimp simp: object_add_def Let_unfold)

lemma sep_state_add_disjL:
  "\<lbrakk>sep_state_disj y z; sep_state_disj x (sep_state_add y z)\<rbrakk> \<Longrightarrow> sep_state_disj x y"
  apply (clarsimp simp: sep_state_disj_def sep_state_add_def)
  apply (rename_tac obj_id)
  apply (clarsimp simp: not_conflicting_objects_def)
  apply (erule_tac x=obj_id in allE)+
  apply (fastforce simp: cdl_heap_add_def cdl_ghost_state_add_def object_type_object_addR
                 split: option.splits)
  done

lemma sep_state_add_disjR:
  "\<lbrakk>sep_state_disj y z; sep_state_disj x (sep_state_add y z)\<rbrakk> \<Longrightarrow> sep_state_disj x z"
  apply (clarsimp simp: sep_state_disj_def sep_state_add_def)
  apply (rename_tac obj_id)
  apply (clarsimp simp: not_conflicting_objects_def)
  apply (erule_tac x=obj_id in allE)+
  apply (fastforce simp: cdl_heap_add_def cdl_ghost_state_add_def object_type_object_addR
                 split: option.splits)
  done

lemma sep_state_add_disj:
  "\<lbrakk>sep_state_disj y z; sep_state_disj x y; sep_state_disj x z\<rbrakk> \<Longrightarrow> sep_state_disj x (sep_state_add y z)"
  apply (clarsimp simp: sep_state_disj_def sep_state_add_def)
  apply (rename_tac obj_id)
  apply (clarsimp simp: not_conflicting_objects_def)
  apply (erule_tac x=obj_id in allE)+
  apply (fastforce simp: cdl_heap_add_def cdl_ghost_state_add_def object_type_object_addR
                 split: option.splits)
  done




(*********************************************)
(* Definition of separation logic for capDL. *)
(*********************************************)

instantiation "sep_state" :: zero
begin
  definition "0 \<equiv> SepState empty (\<lambda>obj_id. {})"
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
  apply intro_classes
(* x ## 0 *)
       apply (simp add: sep_disj_sep_state_def sep_state_disj_def zero_sep_state_def)
(* x ## y \<Longrightarrow> y ## x *)
      apply (clarsimp simp: not_conflicting_objects_comm sep_disj_sep_state_def sep_state_disj_def Let_unfold
                            map_disj_com Int_commute)
(* x + 0 = x *)
     apply (simp add: plus_sep_state_def sep_state_add_def zero_sep_state_def)
     apply (case_tac x)
     apply (clarsimp simp: cdl_heap_add_def)
     apply (rule ext)
     apply (clarsimp simp: cdl_ghost_state_add_def split:if_split_asm)
(* x ## y \<Longrightarrow> x + y = y + x *)
    apply (clarsimp simp: plus_sep_state_def sep_disj_sep_state_def)
    apply (erule sep_state_add_comm)
(* (x + y) + z = x + (y + z) *)
   apply (simp add: plus_sep_state_def sep_state_add_def)
   apply (rule conjI)
   apply (clarsimp simp: sep_disj_sep_state_def)
    apply (erule (2) cdl_heap_add_assoc)
   apply (rule cdl_ghost_state_add_assoc)
(* x ## y + z = (x ## y \<and> x ## z) *)
  apply (clarsimp simp: plus_sep_state_def sep_disj_sep_state_def)
  apply (rule iffI)
   (* x ## y + z \<Longrightarrow> (x ## y \<and> x ## z) *)
   apply (rule conjI)
    (* x ## y + z \<Longrightarrow> (x ## y) *)
    apply (erule (1) sep_state_add_disjL)
   (* x ## y + z \<Longrightarrow> (x ## z) *)
   apply (erule (1) sep_state_add_disjR)
  (* x ## y + z \<Longleftarrow> (x ## y \<and> x ## z) *)
  apply clarsimp
  apply (erule (2) sep_state_add_disj)
  done

end


end
