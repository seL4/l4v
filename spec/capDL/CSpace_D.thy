(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Operations on CSpace *)

theory CSpace_D
  imports
    PageTableUnmap_D
begin

(* Does the given cap have any children? *)
definition has_children :: "cdl_cap_ref \<Rightarrow> cdl_state \<Rightarrow> bool" where
  "has_children parent s = (\<exists>child. is_cdt_parent s parent child)"

definition ensure_no_children :: "cdl_cap_ref \<Rightarrow> unit except_monad" where
  "ensure_no_children x \<equiv> doE
     c \<leftarrow> liftE $ gets (has_children x);
     whenE c $ throw
   odE"

(* Ensure that the given cap slot is empty. *)
definition ensure_empty :: "cdl_cap_ref \<Rightarrow> unit except_monad" where
  "ensure_empty cap_ref \<equiv> doE
     cap \<leftarrow> liftE $ get_cap cap_ref;
     unlessE (cap = NullCap) $ throw
   odE"

(* Insert a new cap into an object. The cap will have no parent. *)
definition insert_cap_orphan :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> unit k_monad" where
  "insert_cap_orphan new_cap dest_slot \<equiv> do
     old_cap \<leftarrow> get_cap dest_slot;
     assert (old_cap = NullCap);
     set_cap dest_slot new_cap
   od"

primrec (nonexhaustive) untyped_cap_range :: "cdl_cap \<Rightarrow> cdl_object_id set" where
  "untyped_cap_range (UntypedCap _ r available) = r"

primrec (nonexhaustive) available_range :: "cdl_cap \<Rightarrow> cdl_object_id set" where
  "available_range (UntypedCap _ r available) = available"

definition set_available_range :: "cdl_cap \<Rightarrow> cdl_object_id set \<Rightarrow> cdl_cap" where
  "set_available_range cap nrange \<equiv>
     case cap of UntypedCap d r available \<Rightarrow> UntypedCap d r nrange | _ \<Rightarrow> cap"

lemmas set_avaiable_range_simps[simp] = set_available_range_def[split_simps cdl_cap.split]

definition set_untyped_cap_as_full :: "cdl_cap \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> unit k_monad" where
  "set_untyped_cap_as_full src_cap new_cap src_slot \<equiv>
     if is_untyped_cap src_cap \<and> is_untyped_cap new_cap \<and> cap_objects src_cap = cap_objects new_cap
     then set_cap src_slot (set_available_range src_cap {})
     else return ()"

(* Insert a new cap into an object. The cap will be a sibling. *)
definition insert_cap_sibling :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap_ref \<Rightarrow> unit k_monad" where
  "insert_cap_sibling new_cap src_slot dest_slot \<equiv> do
     src_cap \<leftarrow> get_cap src_slot;
     old_cap \<leftarrow> get_cap dest_slot;
     assert (old_cap = NullCap);
     set_untyped_cap_as_full src_cap new_cap src_slot;
     set_cap dest_slot new_cap;
     p \<leftarrow> gets $ opt_parent src_slot;
     case p of
       None \<Rightarrow> return ()
     | Some parent \<Rightarrow> set_parent dest_slot parent
   od"

(* Insert a new cap into an object. The cap will be a child. *)
definition insert_cap_child :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap_ref \<Rightarrow> unit k_monad" where
  "insert_cap_child new_cap src_slot dest_slot \<equiv> do
     src_cap \<leftarrow> get_cap src_slot;
     old_cap \<leftarrow> get_cap dest_slot;
     assert (old_cap = NullCap);
     set_untyped_cap_as_full src_cap new_cap src_slot;
     set_cap dest_slot new_cap;
     set_parent dest_slot src_slot
   od"

definition get_irq_slot :: "cdl_irq \<Rightarrow> cdl_state \<Rightarrow> cdl_cap_ref" where
  "get_irq_slot irq s \<equiv> (cdl_irq_node s irq, 0)"

(* Move the given cap from one location to another, possibly modifying it along the way. *)
definition move_cap :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap_ref \<Rightarrow> unit k_monad" where
  "move_cap cap src_slot dest_slot \<equiv> do
     insert_cap_orphan cap dest_slot;
     set_cap src_slot NullCap;
     swap_parents src_slot dest_slot
   od"

(* Actions that must be taken when a capability is deleted in a single step. *)
fun finalise_cap :: "cdl_cap \<Rightarrow> unit k_monad" where
    "finalise_cap (FrameCap dev ptr _ s Real (Some asid)) = unmap_page asid ptr s"
  | "finalise_cap _ = return ()"

text \<open>
  System initialisers only ever delete untyped and frame caps. Deleting these is a single
  non-preemptible step. Deleting any other cap can recurse through Zombie caps and is left
  unspecified.\<close>
definition can_fast_delete :: "cdl_cap \<Rightarrow> bool" where
  "can_fast_delete cap \<equiv>
     case cap of
       NullCap \<Rightarrow> True
     | UntypedCap _ _ _ \<Rightarrow> True
     | FrameCap _ _ _ _ _ _ \<Rightarrow> True
     | _ \<Rightarrow> False"

definition delete_cap :: "cdl_cap_ref \<Rightarrow> unit preempt_monad" where
  "delete_cap victim \<equiv> doE
     cap \<leftarrow> liftE $ get_cap victim;
     if can_fast_delete cap
     then liftE $ do
       finalise_cap cap;
       empty_slot victim
     od
     else chaos
   odE"

definition obj_tcb :: "cdl_object \<Rightarrow> cdl_tcb" where
  "obj_tcb obj \<equiv> case obj of Tcb tcb \<Rightarrow> tcb"

fun reset_mem_mapping :: "cdl_cap \<Rightarrow> cdl_cap" where
    "reset_mem_mapping (FrameCap dev p rts sz b mp) = FrameCap dev p rts sz b None"
  | "reset_mem_mapping (PageTableCap l ptr b mp) = PageTableCap l ptr b None"
  | "reset_mem_mapping cap = cap"


(* Walk a user's CSpace to convert a user's CPTR into a cap slot. *)
function resolve_address_bits ::
  "cdl_cap \<Rightarrow> cdl_cptr \<Rightarrow> nat \<Rightarrow> (cdl_cap_ref \<times> nat) fault_monad"
  where
  "resolve_address_bits cnode_cap cap_ptr remaining_size = doE
     unlessE (is_cnode_cap cnode_cap) $ throw;

     \<comment> \<open>Fetch the next level CNode.\<close>
     cnode \<leftarrow> liftE $ get_cnode $ cap_object cnode_cap;
     radix_size \<leftarrow> returnOk $ cdl_cnode_size_bits cnode;
     guard_size \<leftarrow> returnOk $ cap_guard_size cnode_cap;
     cap_guard  \<leftarrow> returnOk $ cap_guard cnode_cap;
     level_size \<leftarrow> returnOk (radix_size + guard_size);
     assertE (level_size \<noteq> 0);

     \<comment> \<open>Ensure the guard matches up.\<close>
     guard \<leftarrow> returnOk $ (cap_ptr >> (remaining_size-guard_size)) && (mask guard_size);
     unlessE (guard_size \<le> remaining_size \<and> guard = cap_guard) $ throw;

     \<comment> \<open>Ensure we still enough unresolved bits left in our CPTR.\<close>
     whenE (level_size > remaining_size) $ throw;

     \<comment> \<open>Find the next slot.\<close>
     offset \<leftarrow> returnOk $ (cap_ptr >> (remaining_size-level_size)) && (mask radix_size);
      slot \<leftarrow> returnOk (cap_object cnode_cap, unat offset);
     size_left \<leftarrow> returnOk (remaining_size - level_size);
     if size_left = 0 then
       returnOk (slot, 0)
     else doE
       next_cap \<leftarrow> liftE $ get_cap (slot);
       if is_cnode_cap next_cap
       then resolve_address_bits next_cap cap_ptr size_left
       else returnOk (slot, size_left)
     odE
   odE"
  by fastforce+

termination resolve_address_bits
  by (relation "measure (\<lambda>(a,b,c). c)") (auto simp: in_monad)

definition lookup_slot :: "cdl_object_id \<Rightarrow> cdl_cptr \<Rightarrow> cdl_cap_ref fault_monad" where
  "lookup_slot thread cptr \<equiv> doE
     cspace_root \<leftarrow> liftE $ get_cap (thread, tcb_cspace_slot);
     (slot, _) \<leftarrow> resolve_address_bits cspace_root cptr word_bits;
     returnOk slot
   odE"

definition lookup_cap :: "cdl_object_id \<Rightarrow> cdl_cptr \<Rightarrow> cdl_cap fault_monad" where
  "lookup_cap thread cptr \<equiv> doE
     slot \<leftarrow> lookup_slot thread cptr;
     liftE $ get_cap slot
   odE"

definition lookup_cap_and_slot ::
  "cdl_object_id \<Rightarrow> cdl_cptr \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) fault_monad"
  where
  "lookup_cap_and_slot thread cptr \<equiv> doE
     slot \<leftarrow> lookup_slot thread cptr;
     cap \<leftarrow> liftE $ get_cap slot;
     returnOk (cap, slot)
   odE"

definition lookup_slot_for_cnode_op :: "cdl_cap \<Rightarrow> cdl_cptr \<Rightarrow> nat \<Rightarrow> cdl_cap_ref except_monad"
  where
  "lookup_slot_for_cnode_op croot cptr depth \<equiv> doE
     whenE (depth < 1 \<or> depth > word_bits) throw;
     (slot, rem) \<leftarrow> fault_to_except $ resolve_address_bits croot cptr depth;
     if rem = 0 then returnOk slot else throw
   odE"


(* Update the badge of a badged cap. For notification and endpoint caps, mask off bits the kernel
   is unable to store for implementation reasons. *)
definition badge_update :: "machine_word \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap" where
  "badge_update data cap \<equiv>
     let
       data' = if is_ep_cap cap \<or> is_ntfn_cap cap then data && mask badge_bits else data
     in
       update_cap_badge data' cap"

(* Transform a capability based on a request from the user.

   The "data" word is interpreted differently for different cap types.

   We return a set of possible caps to allow for non-deterministic
   implementations, to avoid messy implementation details of the CDT
   in lower-level models. *)
definition update_cap_data :: "bool \<Rightarrow> machine_word \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap k_monad" where
  "update_cap_data preserve data cap \<equiv>
     return $ case cap of
       EndpointCap _ b _ \<Rightarrow> if b = 0 \<and> \<not> preserve then badge_update data cap else NullCap
     | NotificationCap _ b _ \<Rightarrow> if b = 0 \<and> \<not> preserve then badge_update data cap else NullCap
     | CNodeCap object guard guard_size sz \<Rightarrow>
         let
           reserved_bits = 3;
           guard_bits = 18;
           guard_size_bits = 5;
           new_guard_size = unat ((data >> reserved_bits) && mask guard_size_bits);
           new_guard = (data >> (reserved_bits + guard_size_bits)) &&
                       mask (min (unat ((data >> reserved_bits) && mask guard_size_bits)) guard_bits)
         in
           if new_guard_size + sz > word_bits
           then NullCap
           else CNodeCap object new_guard new_guard_size sz
     | SMCCap b \<Rightarrow> if b = 0 \<and> \<not> preserve then badge_update data cap else NullCap
     | _ \<Rightarrow> cap"

(* Some caps may not be copied/minted. In this case the following function
   returns NullCap or throws.

   PageTable and PageDirectory caps may not be copied if already mapped. This is
   left out here and modelled by nondeterminism. *)
definition derive_cap :: "cdl_cap_ref \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap except_monad" where
  "derive_cap slot cap \<equiv>
     case cap of
       UntypedCap _ _ _        \<Rightarrow> doE ensure_no_children slot; returnOk cap odE
     | ReplyCap _ _            \<Rightarrow> returnOk NullCap
     | MasterReplyCap oref     \<Rightarrow> returnOk NullCap
     | IrqControlCap           \<Rightarrow> returnOk NullCap
     | ZombieCap _             \<Rightarrow> returnOk NullCap
     | FrameCap dev p r sz b x \<Rightarrow> returnOk (FrameCap dev p r sz b None)
     | PageTableCap _ _ _ _    \<Rightarrow> throw \<sqinter> returnOk cap
     | _                       \<Rightarrow> returnOk cap"


(* This function is here to make it available in both Tcb_D and PageTable_D *)

(* Modify the TCB's IpcBuffer or Registers in an arbitrary fashion. *)
definition corrupt_tcb_intent :: "cdl_object_id \<Rightarrow> unit k_monad" where
  "corrupt_tcb_intent target_tcb \<equiv> do
     new_intent \<leftarrow> select UNIV;
     update_thread target_tcb (\<lambda>t. t\<lparr>cdl_tcb_intent := new_intent\<rparr>)
   od"

end
