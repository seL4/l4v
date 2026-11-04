(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Operations on CNodes. *)

theory CNode_D
  imports CSpace_D
begin

definition decode_cnode_invocation ::
  "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow> cdl_cnode_intent \<Rightarrow>
   cdl_cnode_invocation except_monad"
  where
  "decode_cnode_invocation target target_ref caps intent \<equiv>
     case intent of
       \<comment> \<open>Copy a cap to anther capslot, without modifying the cap.\<close>
       CNodeCopyIntent dest_index dest_depth src_index src_depth rights \<Rightarrow> doE
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
     | CNodeMintIntent dest_index dest_depth src_index src_depth rights badge \<Rightarrow> doE
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
     | CNodeMoveIntent dest_index dest_depth src_index src_depth \<Rightarrow> doE
         (src_root, _) \<leftarrow> throw_on_none $ get_index caps 0;
         dest_slot \<leftarrow> lookup_slot_for_cnode_op target dest_index (unat dest_depth);
         ensure_empty dest_slot;
         src_slot \<leftarrow> lookup_slot_for_cnode_op src_root src_index (unat src_depth);
         src_cap \<leftarrow> liftE $ get_cap src_slot;
         whenE (src_cap = NullCap) throw;
         returnOk $ MoveCall src_cap src_slot dest_slot
       odE

     \<comment> \<open>Move a cap to another capslot, possibly modifying the cap.\<close>
     | CNodeMutateIntent dest_index dest_depth src_index src_depth badge \<Rightarrow> doE
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

     \<comment> \<open>Delete the given cap, but not its children.\<close>
     | CNodeDeleteIntent index depth \<Rightarrow> doE
         target_slot \<leftarrow> lookup_slot_for_cnode_op target index (unat depth);
         returnOk $ DeleteCall target_slot
       odE"

definition invoke_cnode :: "cdl_cnode_invocation \<Rightarrow> unit preempt_monad" where
  "invoke_cnode params \<equiv>
     case params of
        \<comment> \<open>Insert a new cap.\<close>
        InsertCall cap src_slot dest_slot \<Rightarrow>
          liftE $
            insert_cap_sibling cap src_slot dest_slot \<sqinter>
            insert_cap_child cap src_slot dest_slot

      \<comment> \<open>Move a cap, possibly modifying it in the process.\<close>
      | MoveCall cap src_slot dest_slot \<Rightarrow>
          liftE $ move_cap cap src_slot dest_slot

      \<comment> \<open>Delete a cap.\<close>
      | DeleteCall src_slot \<Rightarrow>
          delete_cap src_slot"

end
