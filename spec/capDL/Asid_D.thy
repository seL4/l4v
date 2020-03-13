(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Operations on page table objects and frames.
 *)

theory Asid_D
imports
  Invocations_D
  CSpace_D
  Untyped_D
begin

definition
  decode_asid_control_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
      cdl_asid_control_intent \<Rightarrow> cdl_asid_control_invocation except_monad"
where
  "decode_asid_control_invocation target target_ref caps intent \<equiv> case intent of
     AsidControlMakePoolIntent index depth \<Rightarrow>
       doE
         base \<leftarrow> liftE $ select {x. x < 2 ^ asid_high_bits};

         \<comment> \<open>Fetch the untyped item, and ensure it is valid.\<close>
         (untyped_cap, untyped_cap_ref) \<leftarrow> throw_on_none $ get_index caps 0;
         (case untyped_cap of
             UntypedCap _ s _ \<Rightarrow> returnOk ()
           | _ \<Rightarrow> throw);
         ensure_no_children untyped_cap_ref;

         \<comment> \<open>Fetch the slot we plan to put the generated cap into.\<close>
         (cspace_cap, _) \<leftarrow> throw_on_none $ get_index caps 1;
         target_slot \<leftarrow> lookup_slot_for_cnode_op cspace_cap index (unat depth);
         ensure_empty target_slot;

         returnOk $ MakePool (set_available_range untyped_cap {}) untyped_cap_ref
           (cap_objects untyped_cap) target_slot base
       odE \<sqinter> throw"

definition
  decode_asid_pool_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
      cdl_asid_pool_intent \<Rightarrow> cdl_asid_pool_invocation except_monad"
where
  "decode_asid_pool_invocation target target_ref caps intent \<equiv> case intent of
     AsidPoolAssignIntent \<Rightarrow>
       doE
         (pd_cap, pd_cap_ref) \<leftarrow> throw_on_none $ get_index caps 0;
         (case pd_cap of
             PageDirectoryCap _ _ _ \<Rightarrow> returnOk ()
           | _ \<Rightarrow> throw);

         base \<leftarrow> (case target of
             AsidPoolCap p base \<Rightarrow> returnOk $ base
           | _ \<Rightarrow> throw);
         offset \<leftarrow> liftE $ select {x. x < 2 ^ asid_low_bits};
         returnOk $ Assign (base, offset) pd_cap_ref (cap_object target, offset)
       odE \<sqinter> throw"

definition
  invoke_asid_control :: "cdl_asid_control_invocation \<Rightarrow> unit k_monad"
where
  "invoke_asid_control params \<equiv>
    case params of
        MakePool untyped_cap untyped_cap_ref untyped_covers target_slot base \<Rightarrow>
          do
            \<comment> \<open>Untype the region. A choice may be made about whether to detype
               objects with Untyped addresses.\<close>
            modify (detype untyped_covers);
            set_cap untyped_cap_ref untyped_cap;
            targets \<leftarrow> generate_object_ids 1 AsidPoolType untyped_covers;

            \<comment> \<open>Retype the region.\<close>
            retype_region 0 AsidPoolType targets;
            assert (targets \<noteq> []);

            \<comment> \<open>Insert the cap.\<close>
            frame \<leftarrow> return $ pick (hd targets);
            insert_cap_child (AsidPoolCap frame base) untyped_cap_ref target_slot;

            \<comment> \<open>Update the asid table.\<close>
            asid_table \<leftarrow> gets cdl_asid_table;
            asid_table' \<leftarrow> return $ asid_table (base \<mapsto> AsidPoolCap frame 0);
            modify (\<lambda>s. s \<lparr>cdl_asid_table := asid_table'\<rparr>)

          od"

definition
  invoke_asid_pool :: "cdl_asid_pool_invocation \<Rightarrow> unit k_monad"
where
  "invoke_asid_pool params \<equiv>
     case params of
       Assign asid pd_cap_ref ap_target_slot \<Rightarrow> do
         pd_cap \<leftarrow> get_cap pd_cap_ref;
         case pd_cap of
           PageDirectoryCap pd_id _ _ \<Rightarrow> do
             set_cap pd_cap_ref (PageDirectoryCap pd_id Real (Some asid));
             set_cap ap_target_slot (PageDirectoryCap pd_id Fake None)
           od
         | _ \<Rightarrow> fail
       od"

end
