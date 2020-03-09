(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Operations on CNodes.
 *)

theory CNode_D
imports Invocations_D CSpace_D
begin

definition
  has_cancel_send_rights :: "cdl_cap \<Rightarrow> bool" where
  "has_cancel_send_rights cap \<equiv> case cap of
   EndpointCap _ _ R \<Rightarrow> R = UNIV
   | _ \<Rightarrow> False"

definition
  decode_cnode_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
      cdl_cnode_intent \<Rightarrow> cdl_cnode_invocation except_monad"
where
  "decode_cnode_invocation target target_ref caps intent \<equiv> case intent of
       \<comment> \<open>Copy a cap to anther capslot, without modifying the cap.\<close>
       CNodeCopyIntent dest_index dest_depth src_index src_depth rights \<Rightarrow>
         doE
           (src_root, _) \<leftarrow> throw_on_none $ get_index caps 0;
           dest_slot \<leftarrow> lookup_slot_for_cnode_op target dest_index (unat dest_depth);
           ensure_empty dest_slot;
           src_slot \<leftarrow> lookup_slot_for_cnode_op src_root src_index (unat src_depth);
           src_cap \<leftarrow> liftE $ get_cap src_slot;
           new_cap \<leftarrow> returnOk $ update_cap_rights (cap_rights src_cap \<inter> rights) src_cap;
           cap \<leftarrow> derive_cap src_slot new_cap;
           whenE (cap = cdl_cap.NullCap) throw;

           returnOk $ InsertCall cap src_slot dest_slot
         odE

     \<comment> \<open>Copy a cap to another capslot, possibly modifying the cap.\<close>
     | CNodeMintIntent dest_index dest_depth src_index src_depth rights badge \<Rightarrow>
         doE
           (src_root, _) \<leftarrow> throw_on_none $ get_index caps 0;
           dest_slot \<leftarrow> lookup_slot_for_cnode_op target dest_index (unat dest_depth);
           ensure_empty dest_slot;
           src_slot \<leftarrow> lookup_slot_for_cnode_op src_root src_index (unat src_depth);
           src_cap \<leftarrow> liftE $ get_cap src_slot;

           \<comment> \<open>Munge the caps rights/data.\<close>
           new_cap \<leftarrow> returnOk $ update_cap_rights (cap_rights src_cap \<inter> rights) src_cap;
           new_cap' \<leftarrow> liftE $ update_cap_data False badge new_cap;

           cap \<leftarrow> derive_cap src_slot new_cap';
           whenE (cap = cdl_cap.NullCap) throw;

           returnOk $ InsertCall cap src_slot dest_slot
         odE

     \<comment> \<open>Move a cap to another capslot, without modifying the cap.\<close>
     | CNodeMoveIntent dest_index dest_depth src_index src_depth \<Rightarrow>
         doE
           (src_root, _) \<leftarrow> throw_on_none $ get_index caps 0;
           dest_slot \<leftarrow> lookup_slot_for_cnode_op target dest_index (unat dest_depth);
           ensure_empty dest_slot;
           src_slot \<leftarrow> lookup_slot_for_cnode_op src_root src_index (unat src_depth);
           src_cap \<leftarrow> liftE $ get_cap src_slot;
           whenE (src_cap = NullCap) throw;
           returnOk $ MoveCall src_cap src_slot dest_slot
         odE

     \<comment> \<open>Move a cap to another capslot, possibly modifying the cap.\<close>
     | CNodeMutateIntent dest_index dest_depth src_index src_depth badge \<Rightarrow>
         doE
           (src_root, _) \<leftarrow> throw_on_none $ get_index caps 0;
           dest_slot \<leftarrow> lookup_slot_for_cnode_op target dest_index (unat dest_depth);
           ensure_empty dest_slot;
           src_slot \<leftarrow> lookup_slot_for_cnode_op src_root src_index (unat src_depth);
           src_cap \<leftarrow> liftE $ get_cap src_slot;

           \<comment> \<open>Munge the caps rights/data.\<close>
           cap \<leftarrow> liftE $ update_cap_data True badge src_cap;
           whenE (cap = NullCap) throw;

           returnOk $ MoveCall cap src_slot dest_slot
         odE

     \<comment> \<open>Revoke all CDT children of the given cap.\<close>
     | CNodeRevokeIntent index depth \<Rightarrow>
         doE
           target_slot \<leftarrow> lookup_slot_for_cnode_op target index (unat depth);
           returnOk $ RevokeCall target_slot
         odE

     \<comment> \<open>Delete the given cap, but not its children.\<close>
     | CNodeDeleteIntent index depth \<Rightarrow>
         doE
           target_slot \<leftarrow> lookup_slot_for_cnode_op target index (unat depth);
           returnOk $ DeleteCall target_slot
         odE

     \<comment> \<open>Save the current thread's reply cap into the target slot.\<close>
     | CNodeSaveCallerIntent index depth \<Rightarrow>
         doE
           target_slot \<leftarrow> lookup_slot_for_cnode_op target index (unat depth);
           ensure_empty target_slot;
           returnOk $ SaveCall target_slot
         odE

     \<comment> \<open>Recycle the target cap.\<close>
     | CNodeCancelBadgedSendsIntent index depth \<Rightarrow>
         doE
           target_slot \<leftarrow> lookup_slot_for_cnode_op target index (unat depth);
           cap \<leftarrow> liftE $ get_cap target_slot;
           unlessE (has_cancel_send_rights cap) throw;
           returnOk $ CancelBadgedSendsCall cap
         odE

     \<comment> \<open>Atomically move several caps.\<close>
     | CNodeRotateIntent dest_index dest_depth pivot_index pivot_depth pivot_badge src_index src_depth src_badge \<Rightarrow>
         doE
           pivot_root \<leftarrow> throw_on_none $ get_index caps 0;
           src_root \<leftarrow> throw_on_none $ get_index caps 1;

           dest_root \<leftarrow> returnOk $ target;
           pivot_root \<leftarrow> returnOk $ fst pivot_root;
           src_root \<leftarrow> returnOk $ fst src_root;

           dest_slot \<leftarrow> lookup_slot_for_cnode_op dest_root dest_index (unat dest_depth);
           src_slot \<leftarrow> lookup_slot_for_cnode_op src_root src_index (unat src_depth);
           pivot_slot \<leftarrow> lookup_slot_for_cnode_op pivot_root pivot_index (unat pivot_depth);

           whenE (pivot_slot = src_slot \<or> pivot_slot = dest_slot) throw;

           unlessE (src_slot = dest_slot) $ ensure_empty dest_slot;

           src_cap \<leftarrow> liftE $ get_cap src_slot;
           whenE (src_cap = NullCap) throw;

           pivot_cap \<leftarrow> liftE $ get_cap pivot_slot;
           whenE (pivot_cap = NullCap) throw;

           \<comment> \<open>Munge caps.\<close>
           new_src \<leftarrow> liftE $ update_cap_data True src_badge src_cap;
           new_pivot \<leftarrow> liftE $ update_cap_data True pivot_badge pivot_cap;

           whenE (new_src = NullCap) throw;
           whenE (new_pivot = NullCap) throw;

           returnOk $ RotateCall new_src new_pivot src_slot pivot_slot dest_slot
         odE
   "

definition
  invoke_cnode :: "cdl_cnode_invocation \<Rightarrow> unit preempt_monad"
where
  "invoke_cnode params \<equiv> case params of
    \<comment> \<open>Insert a new cap.\<close>
      InsertCall cap src_slot dest_slot \<Rightarrow>
        liftE $
          insert_cap_sibling cap src_slot dest_slot
          \<sqinter>
          insert_cap_child cap src_slot dest_slot

    \<comment> \<open>Move a cap, possibly modifying it in the process.\<close>
    | MoveCall cap src_slot dest_slot \<Rightarrow>
        liftE $ move_cap cap src_slot dest_slot

    \<comment> \<open>Revoke a cap.\<close>
    | RevokeCall src_slot \<Rightarrow>
        revoke_cap src_slot

    \<comment> \<open>Delete a cap.\<close>
    | DeleteCall src_slot \<Rightarrow>
        delete_cap src_slot

    \<comment> \<open>Atomically move two capabilities.\<close>
    | RotateCall cap1 cap2 slot1 slot2 slot3 \<Rightarrow>
        liftE $ if slot1 = slot3 then
          swap_cap cap1 slot1 cap2 slot2
        else
          do
            move_cap cap2 slot2 slot3;
            move_cap cap1 slot1 slot2
          od

    \<comment> \<open>Save a reply cap from the caller's TCB into this CNode.\<close>
    | SaveCall dest_slot \<Rightarrow>
        liftE $ do
          current \<leftarrow> gets_the cdl_current_thread;
          replycap \<leftarrow> get_cap (current, tcb_caller_slot);
          when (replycap \<noteq> NullCap)
            $ move_cap replycap (current, tcb_caller_slot) dest_slot
        od

    \<comment> \<open>Reset an object into its original state.\<close>
    | CancelBadgedSendsCall (EndpointCap ep b _) \<Rightarrow> liftE $ when (b \<noteq> 0) $ cancel_badged_sends ep b
    | CancelBadgedSendsCall _ \<Rightarrow> fail
  "

end
