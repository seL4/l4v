(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Accessor functions for objects and caps.
 *)

theory KHeap_D
imports Monads_D
begin

(* Return an item from the heap. Fail if no such object exists. *)
abbreviation
  get_object :: "cdl_object_id \<Rightarrow> cdl_object k_monad"
where
  "get_object p \<equiv> gets_the (\<lambda>s. cdl_objects s p)"

(* Set an item on the heap to the given object. *)
definition
  set_object :: "cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> unit k_monad"
where
  "set_object p obj \<equiv>
    modify (\<lambda>s. s \<lparr> cdl_objects := (cdl_objects s) (p \<mapsto> obj) \<rparr> )"

(* Get a thread from the given pointer. *)
definition
  get_thread :: "cdl_object_id \<Rightarrow> cdl_tcb k_monad"
where
  "get_thread p \<equiv>
    do
      t \<leftarrow> get_object p;
      case t of
          Tcb tcb \<Rightarrow> return tcb
        | _ \<Rightarrow> fail
    od"

(* Get a thread from the given pointer. *)
definition
  get_thread_fault :: "cdl_object_id \<Rightarrow> bool k_monad"
where
  "get_thread_fault p \<equiv>
    do
      t \<leftarrow> get_object p;
      case t of
          Tcb tcb \<Rightarrow> return (cdl_tcb_has_fault tcb)
        | _ \<Rightarrow> fail
    od"

(* Update a thread on the heap. *)
definition
  update_thread :: "cdl_object_id \<Rightarrow> (cdl_tcb \<Rightarrow> cdl_tcb) \<Rightarrow> unit k_monad"
where
  "update_thread p f \<equiv>
     do
       t \<leftarrow> get_object p;
       case t of
          Tcb tcb \<Rightarrow> set_object p (Tcb (f tcb))
       | _ \<Rightarrow> fail
     od"

(* Update a thread on the heap. *)
definition
  update_thread_fault :: "cdl_object_id \<Rightarrow> (bool\<Rightarrow>bool) \<Rightarrow> unit k_monad"
where
  "update_thread_fault p f \<equiv>
     do
       t \<leftarrow> get_object p;
       case t of
          Tcb tcb \<Rightarrow> set_object p (Tcb (tcb\<lparr>cdl_tcb_has_fault := f (cdl_tcb_has_fault tcb)\<rparr>))
       | _ \<Rightarrow> fail
     od"

(* Get a CNode from the given pointer. *)
definition
  get_cnode :: "cdl_object_id \<Rightarrow> cdl_cnode k_monad"
where
  "get_cnode p \<equiv>
    do
      t \<leftarrow> get_object p;
      case t of
          CNode cnode \<Rightarrow> return cnode
        | _ \<Rightarrow> fail
    od"

(*
 * Get the index out of the given list, returning None if it
 * doesn't exist.
 *)
definition
  get_index :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option"
where
  "get_index a b \<equiv>
     if b < length a then
       Some (a ! b)
     else
       None"

(* --- caps --- *)

(* The slots of an object, returns an empty map for non-existing objects
   or objects that do not have caps *)
definition
  slots_of :: "cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> cdl_cap_map"
where
  "slots_of obj_id \<equiv> \<lambda>s.
  case cdl_objects s obj_id of
    None \<Rightarrow> Map.empty
  | Some obj \<Rightarrow> object_slots obj"

(* The cap at the given cap_ref. None if object or cap does not exist *)
definition
  opt_cap :: "cdl_cap_ref \<Rightarrow> cdl_state \<Rightarrow> cdl_cap option"
where
  "opt_cap \<equiv> \<lambda>(obj_id, slot) s. slots_of obj_id s slot"

(* monad version of opt_cap *)
abbreviation
  get_cap :: "cdl_cap_ref \<Rightarrow> cdl_cap k_monad" where
  "get_cap p \<equiv> gets_the (opt_cap p)"


(* Setting a cap at specific cap_ref. Object must exist and have cap slots. *)
definition
  set_cap :: "cdl_cap_ref \<Rightarrow> cdl_cap \<Rightarrow> unit k_monad"
where
  "set_cap \<equiv> \<lambda>(obj_id, slot) cap. do
    obj \<leftarrow> get_object obj_id;
    assert (has_slots obj);
    slots \<leftarrow> return $ object_slots obj;
    obj' \<leftarrow> return $ update_slots (slots (slot \<mapsto> cap)) obj;
    obj'' \<leftarrow> case obj' of
              Tcb t \<Rightarrow> if slot = tcb_ipcbuffer_slot \<and> slots slot \<noteq> Some cap then do
                   intent' \<leftarrow> select UNIV;
                   return $ Tcb (t \<lparr> cdl_tcb_intent := intent' \<rparr>)
                 od
                 else return obj'
             | _ \<Rightarrow> return obj';
    set_object obj_id obj''
  od"



(* looking up the parent of a cap in the cdt *)
definition
  opt_parent :: "cdl_cap_ref \<Rightarrow> cdl_state \<Rightarrow> cdl_cap_ref option" where
  "opt_parent p \<equiv> \<lambda>s. cdl_cdt s p"

abbreviation
  get_parent :: "cdl_cap_ref \<Rightarrow> cdl_cap_ref k_monad" where
  "get_parent p \<equiv> gets_the (opt_parent p)"

(* setting a cap derivation of a specific cap_ref  *)
definition
  set_parent :: "cdl_cap_ref \<Rightarrow> cdl_cap_ref \<Rightarrow> unit k_monad" where
  "set_parent child parent \<equiv> do
    cdt \<leftarrow> gets cdl_cdt;
    assert (cdt child = None);
    modify (\<lambda>s. s \<lparr> cdl_cdt := (cdl_cdt s) (child \<mapsto> parent) \<rparr> )
   od"

(* Removes a cap slot from the cdt, and points all its children to their grandparent *)
definition
  remove_parent :: "cdl_cap_ref \<Rightarrow> unit k_monad" where
  "remove_parent parent \<equiv>
   modify (\<lambda>s. s \<lparr>cdl_cdt := (\<lambda> x. if x = parent
                                 then None
                                 else (if cdl_cdt s x = Some parent
                                     then cdl_cdt s parent
                                     else cdl_cdt s x )) \<rparr>)"

(* Swaps the parents of two cap_refs *)
definition
  swap_parents :: "cdl_cap_ref \<Rightarrow> cdl_cap_ref \<Rightarrow> unit k_monad" where
  "swap_parents p p' = modify (cdl_cdt_update
     (\<lambda>cd. Fun.swap p p'
          (\<lambda>x. if cd x = Some p then Some p' else
              if cd x = Some p' then Some p else cd x)))"

definition
  is_cdt_parent :: "cdl_state \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap_ref \<Rightarrow> bool" where
  "is_cdt_parent s p c \<equiv> cdl_cdt s c = Some p"

definition
  cdt_parent_rel :: "cdl_state \<Rightarrow> (cdl_cap_ref \<times> cdl_cap_ref) set" where
  "cdt_parent_rel \<equiv> \<lambda>s. {(p,c). is_cdt_parent s p c}"

abbreviation
  parent_of :: "cdl_state \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap_ref \<Rightarrow> bool"
  ("_ \<turnstile> _ cdt'_parent'_of _" [60,0,60] 61)
where
  "s \<turnstile> p cdt_parent_of c \<equiv> (p,c) \<in> cdt_parent_rel s"

abbreviation
  parent_of_trancl :: "cdl_state \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap_ref \<Rightarrow> bool"
  ("_ \<turnstile> _ cdt'_parent'_of\<^sup>+ _" [60,0,60] 61)
where
  "s \<turnstile> x cdt_parent_of\<^sup>+ y \<equiv> (x, y) \<in> (cdt_parent_rel s)\<^sup>+"

abbreviation
  parent_of_rtrancl :: "cdl_state \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap_ref \<Rightarrow> bool"
  ("_ \<turnstile> _ cdt'_parent'_of\<^sup>* _" [60,0,60] 61)
where
  "s \<turnstile> x cdt_parent_of\<^sup>* y \<equiv> (x, y) \<in> (cdt_parent_rel s)\<^sup>*"

\<comment> \<open>descendants of a slot\<close>
definition
  descendants_of :: "cdl_cap_ref \<Rightarrow> cdl_state \<Rightarrow> cdl_cap_ref set" where
  "descendants_of p s \<equiv> {q. (p,q) \<in> (cdt_parent_rel s)\<^sup>+}"



definition
  tcb_ipcframe_id :: "cdl_tcb \<Rightarrow> cdl_object_id option"
where
  "tcb_ipcframe_id tcb \<equiv> case (cdl_tcb_caps tcb tcb_ipcbuffer_slot) of
                              Some (FrameCap _ oid _ _ _ _) \<Rightarrow> Some oid
                              | _                       \<Rightarrow> None"

(*
 * Dealing with writes to message registers or other locations that
 * may have an effect on how intents are interpreted.
 *)
definition
  corrupt_intents ::"(word32 \<Rightarrow> cdl_full_intent) \<Rightarrow> cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> cdl_state"
where
  "corrupt_intents f bufp s \<equiv>
  let changed = (\<lambda>ptr. case cdl_objects s ptr of
    Some (Tcb tcb)
      \<Rightarrow> if tcb_ipcframe_id tcb = Some bufp then Some (Tcb (tcb\<lparr> cdl_tcb_intent := f ptr \<rparr> ) ) else None
  | _ \<Rightarrow> None)
  in
  s\<lparr>cdl_objects := cdl_objects s ++ changed\<rparr>"

(* When a memory frame has been corrupted,
 * we need to change all the intents of tcbs
 * whose ipc_buffer is located within that frame
 *)
definition
  corrupt_frame :: "cdl_object_id \<Rightarrow> unit k_monad"
  where
  "corrupt_frame bufp \<equiv> do
      f \<leftarrow> select UNIV;
      modify (corrupt_intents f bufp)
    od"

end
