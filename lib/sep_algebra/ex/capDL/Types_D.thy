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

chapter "A simplified version of the actual capDL specification."

theory Types_D
imports "~~/src/HOL/Word/Word"
begin

(*
 * Objects are named by 32 bit words. 
 * This name may correspond to the memory address of the object.
 *)
type_synonym cdl_object_id = "32 word"

type_synonym cdl_object_set = "cdl_object_id set"

(* The type we use to represent object sizes. *)
type_synonym cdl_size_bits = nat

(* An index into a CNode, TCB, or other kernel object that contains caps. *)
type_synonym cdl_cnode_index = nat

(* A reference to a capability slot. *)
type_synonym cdl_cap_ref = "cdl_object_id \<times> cdl_cnode_index"

(* The possible access-control rights that exist in the system. *)
datatype cdl_right = AllowRead | AllowWrite | AllowGrant


(*
 * Kernel capabilities.
 *
 * Such capabilities (or "caps") give the holder particular rights to
 * a kernel object or system hardware.
 *
 * Caps have attributes such as the object they point to, the rights
 * they give the holder, or how the holder is allowed to interact with
 * the target object.
 *
 * This is a simplified, cut-down version of this datatype for 
 * demonstration purposes.
 *)
datatype cdl_cap =
    NullCap
  | EndpointCap cdl_object_id "cdl_right set"
  | CNodeCap cdl_object_id
  | TcbCap cdl_object_id

(* A mapping from capability identifiers to capabilities. *)
type_synonym cdl_cap_map = "cdl_cnode_index \<Rightarrow> cdl_cap option"

translations
  (type) "cdl_cap_map" <= (type) "nat \<Rightarrow> cdl_cap option"
  (type) "cdl_cap_ref" <= (type) "cdl_object_id \<times> nat"

(* A user cap pointer. *)
type_synonym cdl_cptr = "32 word"

(* Kernel objects *)
record cdl_tcb =
  cdl_tcb_caps :: cdl_cap_map
  cdl_tcb_fault_endpoint :: cdl_cptr

record cdl_cnode =
  cdl_cnode_caps :: cdl_cap_map
  cdl_cnode_size_bits :: cdl_size_bits

(*
 * Kernel objects.
 *
 * These are in-memory objects that may, over the course of the system
 * execution, be created or deleted by users.
 *
 * Again, a simplified version of the real datatype.
 *)
datatype cdl_object =
    Endpoint
  | Tcb cdl_tcb
  | CNode cdl_cnode

(*
 * The current state of the system.
 *
 * The state record contains the following primary pieces of information:
 *
 * objects:
 *   The objects that currently exist in the system.
 *
 * current_thread:
 *   The currently running thread. Operations will always be performed
 *   on behalf of this thread.
 *
 * ghost_state: (Used for separation logic)
 *   Which fields are owned by an object.
 *   In capDL this is all of the fields (or none of them).
 *   In any concrete state, this will be all of the fields.
 *)


(* The ghost state tracks which components (fields and slots) are owned by an object.
 * Fields + slots are encoded as None + Some nat.
 *)
type_synonym cdl_heap = "cdl_object_id \<Rightarrow> cdl_object option"
type_synonym cdl_component  = "nat option"
type_synonym cdl_components = "cdl_component set"
type_synonym cdl_ghost_state = "cdl_object_id \<Rightarrow> cdl_components"

translations
  (type) "cdl_heap" <= (type) "cdl_object_id \<Rightarrow> cdl_object option"
  (type) "cdl_ghost_state" <= (type) "cdl_object_id \<Rightarrow> nat option set"

record cdl_state =
  cdl_objects :: "cdl_heap"
  cdl_current_thread :: "cdl_object_id option"
  cdl_ghost_state :: "cdl_ghost_state"


(* Kernel objects types. *)
datatype cdl_object_type =
    EndpointType
  | TcbType
  | CNodeType

(* Return the type of an object. *)
definition
  object_type :: "cdl_object \<Rightarrow> cdl_object_type"
where
  "object_type x \<equiv>
    case x of
        Endpoint \<Rightarrow> EndpointType
      | Tcb _ \<Rightarrow> TcbType
      | CNode _ \<Rightarrow> CNodeType"

(*
 * Getters and setters for various data types.
 *)

(* Capability getters / setters *)

definition cap_objects :: "cdl_cap \<Rightarrow> cdl_object_id set"
where
    "cap_objects cap \<equiv> 
       case cap of
           TcbCap x \<Rightarrow> {x}
         | CNodeCap x \<Rightarrow> {x}
         | EndpointCap x _ \<Rightarrow> {x}"

definition cap_has_object :: "cdl_cap \<Rightarrow> bool"
where
    "cap_has_object cap \<equiv> 
       case cap of
           NullCap          \<Rightarrow> False
         | _                \<Rightarrow> True"

definition cap_object :: "cdl_cap \<Rightarrow> cdl_object_id"
where
    "cap_object cap \<equiv> 
       if cap_has_object cap 
         then THE obj_id. cap_objects cap = {obj_id}
         else undefined "

lemma cap_object_simps:
  "cap_object (TcbCap x) = x"
  "cap_object (CNodeCap x) = x"
  "cap_object (EndpointCap x j) = x"
  by (simp_all add:cap_object_def cap_objects_def cap_has_object_def)

definition
  cap_rights :: "cdl_cap \<Rightarrow> cdl_right set"
where
  "cap_rights c \<equiv> case c of
      EndpointCap _ x \<Rightarrow> x
    | _ \<Rightarrow> UNIV"

definition
  update_cap_rights :: "cdl_right set \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap"
where
  "update_cap_rights r c \<equiv> case c of
      EndpointCap f1 _ \<Rightarrow> EndpointCap f1 r
    | _ \<Rightarrow> c"

(* Kernel object getters / setters *)
definition
  object_slots :: "cdl_object \<Rightarrow> cdl_cap_map"
where
  "object_slots obj \<equiv> case obj of
    CNode x \<Rightarrow> cdl_cnode_caps x
  | Tcb x \<Rightarrow> cdl_tcb_caps x
  | _ \<Rightarrow> empty"

definition
  update_slots :: "cdl_cap_map \<Rightarrow> cdl_object \<Rightarrow> cdl_object"
where
  "update_slots new_val obj \<equiv> case obj of
    CNode x \<Rightarrow> CNode (x\<lparr>cdl_cnode_caps := new_val\<rparr>)
  | Tcb x \<Rightarrow> Tcb (x\<lparr>cdl_tcb_caps := new_val\<rparr>)
  | _ \<Rightarrow> obj"

(* Adds new caps to an object. It won't overwrite on a collision. *)
definition
  add_to_slots :: "cdl_cap_map \<Rightarrow> cdl_object \<Rightarrow> cdl_object"
where
  "add_to_slots new_val obj \<equiv> update_slots (new_val ++ (object_slots obj)) obj"

definition
  slots_of :: "cdl_heap \<Rightarrow> cdl_object_id \<Rightarrow> cdl_cap_map"
where
  "slots_of h \<equiv> \<lambda>obj_id. 
  case h obj_id of 
    None \<Rightarrow> empty 
  | Some obj \<Rightarrow> object_slots obj"


definition
  has_slots :: "cdl_object \<Rightarrow> bool"
where
  "has_slots obj \<equiv> case obj of
    CNode _ \<Rightarrow> True
  | Tcb _ \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  object_at :: "(cdl_object \<Rightarrow> bool) \<Rightarrow> cdl_object_id \<Rightarrow> cdl_heap \<Rightarrow> bool"
where
  "object_at P p s \<equiv> \<exists>object. s p = Some object \<and> P object"

abbreviation
  "ko_at k \<equiv> object_at (op = k)"

end
