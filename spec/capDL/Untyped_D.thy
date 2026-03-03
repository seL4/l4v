(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Operations on untyped memory objects.
 *)

theory Untyped_D
imports Invocations_D CSpace_D Structures_D
begin

definition
  decode_untyped_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
      cdl_untyped_intent \<Rightarrow> cdl_untyped_invocation except_monad"
where
  "decode_untyped_invocation untyped_cap untyped_ref caps intent \<equiv> case intent of
     UntypedRetypeIntent type size_bits node_index node_depth node_offset node_window \<Rightarrow>
       doE
         (root_cap, root_slot) \<leftarrow> throw_on_none $ get_index caps 0;

         \<comment> \<open>Lookup the destination slots.\<close>
         target_node \<leftarrow> if node_depth = 0 then
             returnOk root_cap
           else
             doE
               target_slot \<leftarrow> lookup_slot_for_cnode_op root_cap node_index (unat node_depth);
               liftE $ get_cap target_slot
             odE;

         \<comment> \<open>Ensure it is a CNode cap.\<close>
         unlessE (is_cnode_cap target_node) throw;

         \<comment> \<open>Find our target slots.\<close>
         slots \<leftarrow> returnOk $ map (\<lambda>n. (cap_object target_node, n))
               [unat node_offset ..< unat node_offset + unat node_window];
         mapME_x ensure_empty slots;

         \<comment> \<open>Work out what names are available. If we haven't haven't already been typed into something we can reuse our names.\<close>
         s \<leftarrow> liftE $ get;
         has_kids \<leftarrow> returnOk $ has_children untyped_ref s;

         returnOk $ Retype untyped_ref type (unat size_bits) slots has_kids (unat node_window)
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

(* Return a list of num_objects sets for requested the request number of objects;
   if the object type is not UntypedType, the sets contain a singleton ptr for the
   new objects, otherwise, the sets represent the valid ptrs in each untyped. *)
definition generate_range ::
  "cdl_object_id \<Rightarrow> cdl_object_type \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> cdl_object_id set list"
  where
  "generate_range start type sz num_objects \<equiv>
     map (\<lambda>ptr. if type = UntypedType then {ptr .. ptr + 2 ^ sz - 1} else {ptr}) $
         map (\<lambda>x. ptr_add start (x * 2 ^ sz))
             [0 ..< num_objects]"

definition create_objects :: "(cdl_object_id set) list \<Rightarrow> cdl_object option \<Rightarrow> unit k_monad"
where
  "create_objects target_object_ids object \<equiv>
    (modify (\<lambda>s. s\<lparr>cdl_objects := (\<lambda>x.
     if {x} \<in> set target_object_ids then
      object
     else
      cdl_objects s x)\<rparr>))"


(* Insert a cap for a new object in the given location. *)
definition
  create_cap :: "cdl_object_type \<Rightarrow> nat \<Rightarrow> cdl_cap_ref \<Rightarrow> bool \<Rightarrow> (cdl_cap_ref \<times> cdl_object_id set) \<Rightarrow> unit k_monad"
where
  "create_cap new_type sz parent_slot dev \<equiv> \<lambda>(dest_slot, obj_refs).
  do
    old_cap \<leftarrow> get_cap dest_slot;
    assert (old_cap = NullCap);
    set_cap dest_slot (default_cap new_type obj_refs sz dev);
    set_parent dest_slot parent_slot
  od"

(* This returns the set of unused ptrs while explicitly checking for overflow *)
definition update_range :: "cdl_object_id set \<Rightarrow> cdl_object_id \<Rightarrow> nat \<Rightarrow> cdl_object_id set" where
  "update_range old_range ptr idx \<equiv>
     if idx = 0
     then old_range
     else if (ptr \<le> ptr + of_nat idx)
       then old_range - {..<ptr + of_nat idx}
       else {}"

definition update_available_range ::
  "cdl_object_id \<Rightarrow> nat \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap \<Rightarrow> unit k_monad"
  where
  "update_available_range ptr idx cap_ref cap \<equiv>
     let cap_range = untyped_cap_range cap;
         new_range = update_range cap_range ptr idx
     in set_cap cap_ref $ set_available_range cap new_range"

definition retype_region ::
  "nat \<Rightarrow> cdl_object_type \<Rightarrow> (cdl_object_id set list) \<Rightarrow> ((cdl_object_id set) list) k_monad"
  where
  "retype_region target_bits target_type target_object_ids \<equiv>
    do
      \<comment> \<open>Get a list of target locations. We are happy with any unused name
         within the target range.\<close>

      if (target_type \<noteq> UntypedType) then
       do
         current_domain \<leftarrow> gets cdl_current_domain;
         create_objects target_object_ids (default_object target_type target_bits current_domain)
       od
      else return ();

      \<comment> \<open>Get a list of target locations. We are happy with any unused name
         within the target range.\<close>
      return target_object_ids
    od"

primrec (nonexhaustive)
  untyped_is_device :: "cdl_cap \<Rightarrow> bool"
where
    "untyped_is_device (UntypedCap d _ _) = d"

definition
  reset_untyped_cap :: "cdl_cap_ref \<Rightarrow> unit preempt_monad"
where
  "reset_untyped_cap cref \<equiv> doE
    cap \<leftarrow> liftE $ get_cap cref;
    whenE (available_range cap \<noteq> cap_objects cap) $ doE
      liftE $ modify (detype (cap_objects cap));
      new_rans \<leftarrow> liftE $ select {xs. (\<forall>S \<in> set xs.
              S \<subseteq> cap_objects cap \<and> available_range cap \<subset> S)
          \<and> xs \<noteq> [] \<and> List.last xs = cap_objects cap};
      mapME_x (\<lambda>r. doE
        liftE $ set_cap cref $ set_available_range cap r;
        returnOk () \<sqinter> throw
      odE) new_rans
    odE
  odE"

definition pte_bits :: nat where
  "pte_bits \<equiv> if word_bits = 32 then 2 else 3"

definition obj_bits_cdl :: "cdl_object_type \<Rightarrow> nat \<Rightarrow> nat" where
  "obj_bits_cdl type obj_size_bits \<equiv>
     case type of
       UntypedType \<Rightarrow> obj_size_bits
     | TcbType \<Rightarrow> tcb_bits_cdl
     | EndpointType \<Rightarrow> endpoint_bits_cdl
     | NotificationType \<Rightarrow> ntfn_bits_cdl
     | CNodeType \<Rightarrow> obj_size_bits + slot_bits_cdl
     | FrameType sz \<Rightarrow> sz
     | PageTableType \<Rightarrow> pt_size_index + pte_bits
     | PageDirectoryType \<Rightarrow> pd_size_index + pte_bits
     | AsidPoolType \<Rightarrow> pageBits_cdl"

(* This definition mostly just wraps "If" so that if-splitting can be controlled separately. *)
definition keep_if :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "keep_if P a b \<equiv> if P a then a else b"

(* Pick the minimum/smallest element of the first set if that set is not empty, otherwise of the
   second set *)
abbreviation min_of_range :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a::linorder" where
  "min_of_range r1 r2 \<equiv> Min (keep_if ((\<noteq>) {}) r1 r2)"

definition
  invoke_untyped :: "cdl_untyped_invocation \<Rightarrow> unit preempt_monad"
where
  "invoke_untyped params \<equiv> case params of
     Retype untyped_ref new_type type_size target_slots has_kids num_objects \<Rightarrow>
   doE
     unlessE has_kids $ reset_untyped_cap untyped_ref;
       liftE $ do
         untyped_cap  \<leftarrow> get_cap untyped_ref;

         base_ptr     \<leftarrow> return $ Min (untyped_cap_range untyped_cap);

         \<comment> \<open>If we have overflow, then the available range will be empty,
            but the index is considered to have wrapped back around to zero.\<close>
         next_ptr     \<leftarrow> return $ min_of_range (available_range untyped_cap)
                                               (untyped_cap_range untyped_cap);

         \<comment> \<open> Check if the ptr needs aligning \<close>
         aligned_ptr  \<leftarrow> return $ if has_kids then alignUp next_ptr (obj_bits_cdl new_type type_size) else next_ptr;

         new_obj_refs \<leftarrow> return $ generate_range (aligned_ptr) new_type (obj_bits_cdl new_type type_size) num_objects;
         new_idx      \<leftarrow> return $ aligned_ptr + (of_nat num_objects << (obj_bits_cdl new_type type_size)) - base_ptr;

         update_available_range base_ptr (unat (new_idx)) untyped_ref untyped_cap;

         \<comment> \<open>Construct new objects within the covered range.\<close>
         retype_region type_size new_type new_obj_refs;

         \<comment> \<open>Construct caps for the new objects.\<close>
         mapM_x (create_cap new_type type_size untyped_ref (untyped_is_device untyped_cap)) (zip target_slots new_obj_refs);

         \<comment> \<open>Ideally, we should return back to the user how many
            objects were created.\<close>

         return ()
       od
    odE"

end
