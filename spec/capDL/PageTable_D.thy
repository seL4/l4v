(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Operations on page table objects and frames.
 *)

theory PageTable_D
imports Invocations_D CSpace_D
begin

(* Return the set of free PD slots in the given PD. *)
definition
  free_pd_slots :: "cdl_object \<Rightarrow> cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> cdl_cap_ref set"
where
  "free_pd_slots pd pd_id state \<equiv> {(pd_id, y). (object_slots pd) y = Some NullCap}"

(* Return the set of all PD/PT slots in the given PD. *)
definition
  all_pd_pt_slots :: "cdl_object \<Rightarrow> cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> cdl_cap_ref set"
where
  "all_pd_pt_slots pd pd_id state \<equiv> {(pd_id, y). y \<in> dom (object_slots pd)}
     \<union> {(x, y). \<exists> a b c. (object_slots pd) a = Some (PageTableCap x b c) \<and> x \<in> dom (cdl_objects state)}"

definition
  "cdl_get_pt_mapped_addr cap \<equiv>
    case cap of PageTableCap pid ctype maddr \<Rightarrow>  maddr
    | _ \<Rightarrow> None"

(* Decode a page table intent into an invocation. *)
definition
  decode_page_table_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
      cdl_page_table_intent \<Rightarrow> cdl_page_table_invocation except_monad"
where
  "decode_page_table_invocation target target_ref caps intent \<equiv> case intent of
    \<comment> \<open>
      Map the given PageTable into the given PageDirectory at the given
      virtual address.

      The concrete implementation only allows a PageTable to be mapped
      once at any point in time, but we don't enforce that here.
     \<close>
    PageTableMapIntent vaddr attr \<Rightarrow>
      doE
        case cdl_get_pt_mapped_addr target of Some a \<Rightarrow> throw
        | None \<Rightarrow> returnOk ();
        \<comment> \<open>Ensure that a PD was passed in.\<close>
        pd \<leftarrow> throw_on_none $ get_index caps 0;
        (pd_object_id, asid) \<leftarrow>
          case (fst pd) of
              PageDirectoryCap x _ (Some asid) \<Rightarrow> returnOk (x, asid)
            | _ \<Rightarrow> throw;

        target_slot \<leftarrow> returnOk $ cdl_lookup_pd_slot pd_object_id vaddr;

        returnOk $ PageTableMap (PageTableCap (cap_object target) Real (Some (asid,vaddr && ~~ mask 20)))
          (PageTableCap (cap_object target) Fake None) target_ref target_slot
      odE \<sqinter> throw
    \<comment> \<open>Unmap this PageTable.\<close>
    | PageTableUnmapIntent \<Rightarrow> (
        case target of PageTableCap pid ctype maddr \<Rightarrow>
        (returnOk $ PageTableUnmap maddr pid target_ref)
        | _ \<Rightarrow> throw
      ) \<sqinter> throw
  "

(* Decode a page table intent into an invocation. *)
definition
  decode_page_directory_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
      cdl_page_directory_intent \<Rightarrow> cdl_page_directory_invocation except_monad"
where
  "decode_page_directory_invocation target target_ref caps intent \<equiv>
      (returnOk $ PageDirectoryNothing) \<sqinter>
      (returnOk $ PageDirectoryFlush Unify)  \<sqinter>  (returnOk $ PageDirectoryFlush Clean)  \<sqinter>
      (returnOk $ PageDirectoryFlush CleanInvalidate )  \<sqinter> (returnOk $ PageDirectoryFlush Invalidate)
      \<sqinter> throw "




(* Decode a page intent into an invocation. *)

definition
  decode_page_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
      cdl_page_intent \<Rightarrow> cdl_page_invocation except_monad"
where
  "decode_page_invocation target target_ref caps intent \<equiv> case intent of
      \<comment> \<open>
        Map the given Page into the given PageDirectory or PageTable at
        the given virtual address.

        The concrete implementation only allows a Page to be mapped
        once at any point in time, but we don't enforce that here.
       \<close>
      PageMapIntent vaddr rights attr \<Rightarrow>
        doE
          \<comment> \<open>Ensure that a PD was passed in.\<close>
          pd \<leftarrow> throw_on_none $ get_index caps 0;
          (pd_object_id, asid) \<leftarrow>
            case (fst pd) of
                PageDirectoryCap x _ (Some asid) \<Rightarrow> returnOk (x, asid)
              | _ \<Rightarrow> throw;

          \<comment> \<open>Collect mapping from target cap.\<close>
          (frame,sz,dev) \<leftarrow> returnOk $ (case target of FrameCap dev p R sz m mp \<Rightarrow> (p,sz,dev));

          target_slots \<leftarrow> cdl_page_mapping_entries vaddr sz pd_object_id;

          \<comment> \<open>Calculate rights.\<close>
          new_rights \<leftarrow> returnOk $ validate_vm_rights $ cap_rights target \<inter> rights;

          \<comment> \<open>Return the map intent.\<close>
          returnOk $ PageMap (FrameCap dev frame (cap_rights target) sz Real (Some (asid,vaddr)))
            (FrameCap False frame new_rights sz Fake None) target_ref target_slots
        odE \<sqinter> throw

    \<comment> \<open>Unmap this PageTable.\<close>
    | PageUnmapIntent \<Rightarrow> doE
        (frame, asid, sz) \<leftarrow> (case target of
           FrameCap _ p R sz m mp \<Rightarrow> returnOk (p, mp , sz)
        | _ \<Rightarrow> throw);
      (returnOk $ PageUnmap asid frame target_ref sz) \<sqinter> throw
      odE

    \<comment> \<open>Flush the caches associated with this page.\<close>
    | PageFlushCachesIntent \<Rightarrow>
       (returnOk $ PageFlushCaches Unify)  \<sqinter>  (returnOk $ PageFlushCaches Clean)  \<sqinter>
      (returnOk $ PageFlushCaches CleanInvalidate )  \<sqinter> (returnOk $ PageFlushCaches Invalidate)
      \<sqinter> throw

    | PageGetAddressIntent \<Rightarrow> returnOk PageGetAddress

  "

(* Invoke a page table. *)
definition
  invoke_page_directory :: "cdl_page_directory_invocation \<Rightarrow> unit k_monad"
where
  "invoke_page_directory params \<equiv> case params of
      PageDirectoryFlush flush  => return ()
    | PageDirectoryNothing => return ()
  "

definition "option_exec f \<equiv> \<lambda>x. case x of Some a \<Rightarrow> f a | None \<Rightarrow> return ()"

(* Invoke a page table. *)
definition
  invoke_page_table :: "cdl_page_table_invocation \<Rightarrow> unit k_monad"
where
  "invoke_page_table params \<equiv> case params of
      PageTableMap real_pt_cap pt_cap pt_cap_ref pd_target_slot \<Rightarrow>
        do set_cap pt_cap_ref real_pt_cap;
           \<comment> \<open>
             We install the Page Table into the Page Directory.  The
             concrete kernel uses hardware-defined PDEs (Page Directory
             Entries). Our abstract spec just uses caps.
            \<close>
           insert_cap_orphan pt_cap pd_target_slot
        od
    | PageTableUnmap mapped_addr pt_id pt_cap_ref \<Rightarrow> do
        (case mapped_addr of Some maddr \<Rightarrow> do
                 unmap_page_table maddr pt_id;
                 clear_object_caps pt_id \<sqinter> return ()
               od
          | _ \<Rightarrow> return ());
        cap \<leftarrow> get_cap pt_cap_ref;
        set_cap pt_cap_ref (reset_mem_mapping cap)
        od

  "

(* Invoke a page. *)
definition
  invoke_page :: "cdl_page_invocation \<Rightarrow> unit k_monad"
where
  "invoke_page params \<equiv> case params of
      PageMap frame_cap pseudo_frame_cap frame_cap_ref target_slots \<Rightarrow>
          \<comment> \<open>Clear out the target slots.\<close>
        do
          set_cap frame_cap_ref frame_cap;
          mapM_x (swp set_cap pseudo_frame_cap) target_slots
        od

    | PageUnmap mapped_addr frame_id frame_cap_ref pgsz \<Rightarrow> do
        (case mapped_addr of
          Some maddr \<Rightarrow> unmap_page maddr frame_id pgsz
        | _ \<Rightarrow> return ());
        cap \<leftarrow> get_cap frame_cap_ref;
        set_cap frame_cap_ref (reset_mem_mapping cap)
      od

    | PageFlushCaches flush \<Rightarrow> return ()

    | PageGetAddress \<Rightarrow> return ()

  "

end
