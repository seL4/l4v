(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

(*
 * Operations on untyped memory objects.
 *)

theory Untyped_D
imports Invocations_D CSpace_D
begin

definition
  decode_untyped_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
      cdl_untyped_intent \<Rightarrow> cdl_untyped_invocation except_monad"
where
  "decode_untyped_invocation untyped_cap untyped_ref caps intent \<equiv> case intent of
     UntypedRetypeIntent type size_bits node_index node_depth node_offset node_window \<Rightarrow>
       doE
         (root_cap, root_slot) \<leftarrow> throw_on_none $ get_index caps 0;

         (* Lookup the destination slots. *)
         target_node \<leftarrow> if node_depth = 0 then
             returnOk root_cap
           else
             doE
               target_slot \<leftarrow> lookup_slot_for_cnode_op root_cap node_index (unat node_depth);
               liftE $ get_cap target_slot
             odE;

         (* Ensure it is a CNode cap. *)
         unlessE (is_cnode_cap target_node) throw;

         (* Find our target slots. *)
         slots \<leftarrow> returnOk $ map (\<lambda>n. (cap_object target_node, n))
               [unat node_offset ..< unat node_offset + unat node_window];
         mapME_x ensure_empty slots;

         (* Work out what names are available. If we haven't haven't already been typed into something we can reuse our names. *)
         s \<leftarrow> liftE $ get;
         has_kids \<leftarrow> returnOk $ has_children untyped_ref s;

         returnOk $ Retype  untyped_ref type (unat size_bits) slots has_kids (unat node_window)
       odE \<sqinter> throw"

(* Zero out a set of addresses. *)
definition
  detype :: "cdl_object_id set \<Rightarrow> cdl_state \<Rightarrow> cdl_state"
where
  "detype detype_set s \<equiv>
     (s\<lparr> cdl_objects :=
         (\<lambda>x. if x \<in> detype_set then
           Some Untyped
         else cdl_objects s x)\<rparr>)"

(*
 * Retype the given untyped object into a new object type,
 * and return a list of pointers to the newly constructed items.
 *)

definition
  generate_object_ids :: "nat \<Rightarrow> cdl_object_type \<Rightarrow> cdl_object_id set \<Rightarrow>  ((cdl_object_id set) list) k_monad"
  where "generate_object_ids num_objects type object_range
  \<equiv> do
    s \<leftarrow> get;
    available_names \<leftarrow> return $ (cdl_objects s) -` {Some Untyped};
    setlist \<leftarrow> select {x. distinct  x \<and> (\<forall>a\<in> set x. \<forall>b \<in> set x. a \<noteq> b \<longrightarrow> a \<inter> b = {})
           \<and> (\<forall>y \<in> set x. y \<noteq> {} \<and> y \<subseteq> object_range \<inter> available_names)
           \<and> (num_objects = (size x)) };
    if (type \<noteq> UntypedType) then (return $ map (\<lambda>x. {pick x}) setlist)
    else return setlist
    od"

definition create_objects :: "(cdl_object_id set) list \<Rightarrow> cdl_object option \<Rightarrow> unit k_monad"
where
  "create_objects target_object_ids object \<equiv>
    (modify (\<lambda>s. s\<lparr>cdl_objects := (\<lambda>x.
     if {x} \<in> set target_object_ids then
      object
     else
      cdl_objects s x)\<rparr>))"


(* Insert a cap for a new object in the given location. *)
(* FIXME: we do not do update_untyped_as_full here for refinedment ? *)
definition
  create_cap :: "cdl_object_type \<Rightarrow> nat \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap_ref \<times> cdl_object_id set) \<Rightarrow> unit k_monad"
where
  "create_cap new_type sz parent_slot \<equiv> \<lambda>(dest_slot, obj_refs).
  do
    old_cap \<leftarrow> get_cap dest_slot;
    assert (old_cap = NullCap);
    set_cap dest_slot (default_cap new_type obj_refs sz);
    set_parent dest_slot parent_slot
  od"


definition
  update_available_range :: "(cdl_object_id set) => (cdl_object_id list) \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap \<Rightarrow> unit k_monad"
where "update_available_range orange newids cap_ref cap \<equiv>
  do
     new_range  \<leftarrow> select {x. x \<subseteq> orange - set newids};
     set_cap cap_ref $ set_avaiable_range cap new_range
  od"


definition
  retype_region :: "nat \<Rightarrow> cdl_object_type \<Rightarrow> (cdl_object_id set list)
  \<Rightarrow> ((cdl_object_id set) list) k_monad"
where
  "retype_region target_bits target_type target_object_ids \<equiv>
    do
      (* Get a list of target locations. We are happy with any unused name
         within the target range. *)

      if (target_type \<noteq> UntypedType) then
       do
         current_domain \<leftarrow> gets cdl_current_domain;
         create_objects target_object_ids (default_object target_type target_bits current_domain)
       od
      else return ();

      (* Return the list of new objects. *)
      return target_object_ids
    od"



definition
  invoke_untyped :: "cdl_untyped_invocation \<Rightarrow> unit k_monad"
where
  "invoke_untyped params \<equiv> case params of
     Retype untyped_ref new_type type_size target_slots has_kids num_objects \<Rightarrow>
       do
         untyped_cap \<leftarrow> get_cap untyped_ref;

         (* If the untyped hasn't already been typed into something we reuse our names. *)
         unless has_kids $ modify (detype (cap_objects untyped_cap));

         new_range \<leftarrow> return $ if has_kids then (avaiable_range untyped_cap) else (cap_objects untyped_cap);
         new_obj_refs \<leftarrow> generate_object_ids num_objects new_type new_range;

         update_available_range new_range (map (\<lambda>s. pick s) new_obj_refs) untyped_ref untyped_cap;

         (* Construct new objects within the covered range. *)
         retype_region type_size new_type new_obj_refs;

         (* Construct caps for the new objects. *)
         mapM_x (create_cap new_type type_size untyped_ref) (zip target_slots new_obj_refs);

         (* Ideally, we should return back to the user how many
          * objects were created. *)


         return ()
       od"
end
