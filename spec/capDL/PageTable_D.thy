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

definition cdl_get_pde :: "(word32 \<times> nat)\<Rightarrow> cdl_cap k_monad"
where "cdl_get_pde ptr \<equiv> 
  KHeap_D.get_cap ptr"

definition cdl_lookup_pd_slot :: "word32 \<Rightarrow> word32 \<Rightarrow> word32 \<times> nat "
  where "cdl_lookup_pd_slot pd vptr \<equiv> (pd, unat (vptr >> 20))"

definition cdl_lookup_pt_slot :: "word32 \<Rightarrow> word32 \<Rightarrow> (word32 \<times> nat) except_monad"
  where "cdl_lookup_pt_slot pd vptr \<equiv> 
    doE pd_slot \<leftarrow> returnOk (cdl_lookup_pd_slot pd vptr);
        pdcap \<leftarrow> liftE $ cdl_get_pde pd_slot;
        (case pdcap of cdl_cap.PageTableCap ref Fake None
         \<Rightarrow> ( doE pt \<leftarrow> returnOk ref;
              pt_index \<leftarrow> returnOk ((vptr >> 12) && 0xFF);
              returnOk (pt,unat pt_index)
         odE)
        | _ \<Rightarrow> Monads_D.throw)
    odE"

definition cdl_create_mapping_entries :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word 
                                       \<Rightarrow> ((32 word \<times> nat) list) except_monad"
  where "cdl_create_mapping_entries vptr pgsz pd \<equiv> 
  if pgsz = 12 then doE
    p \<leftarrow> cdl_lookup_pt_slot pd vptr;
         returnOk [p]
    odE

  else if pgsz = 16 then doE
    p \<leftarrow> cdl_lookup_pt_slot pd vptr;
         returnOk [p]
    odE
  else if pgsz = 20 then doE
    p \<leftarrow> returnOk $ (cdl_lookup_pd_slot pd vptr);
         returnOk [p]
    odE
  else if pgsz = 24 then doE
    p \<leftarrow> returnOk $ (cdl_lookup_pd_slot pd vptr);
         returnOk [p]
    odE
  else throw"


(* Decode a page table intent into an invocation. *)
definition
  decode_page_table_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
      cdl_page_table_intent \<Rightarrow> cdl_page_table_invocation except_monad"
where
  "decode_page_table_invocation target target_ref caps intent \<equiv> case intent of
    (*
     * Map the given PageTable into the given PageDirectory at the given
     * virtual address.
     *
     * The concrete implementation only allows a PageTable to be mapped
     * once at any point in time, but we don't enforce that here.
     *)
    PageTableMapIntent vaddr attr \<Rightarrow>
      doE
        (* Ensure that a PD was passed in. *)
        pd \<leftarrow> throw_on_none $ get_index caps 0;
        (pd_object_id, asid) \<leftarrow>
          case (fst pd) of
              PageDirectoryCap x _ asid \<Rightarrow> returnOk (x, asid)
            | _ \<Rightarrow> throw;

        target_slot \<leftarrow> returnOk $ cdl_lookup_pd_slot pd_object_id vaddr;

        returnOk $ PageTableMap (PageTableCap (cap_object target) Real asid)
          (PageTableCap (cap_object target) Fake None) target_ref target_slot
      odE \<sqinter> throw

    (* Unmap this PageTable. *)
    | PageTableUnmapIntent \<Rightarrow>
      (returnOk $ PageTableUnmap (cap_object target) target_ref) \<sqinter> throw
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
      (*
       * Map the given Page into the given PageDirectory or PageTable at
       * the given virtual address.
       *
       * The concrete implementation only allows a Page to be mapped
       * once at any point in time, but we don't enforce that here.
       *)
      PageMapIntent vaddr rights attr \<Rightarrow>
        doE
          (* Ensure that a PD was passed in. *)
          pd \<leftarrow> throw_on_none $ get_index caps 0;
          (pd_object_id, asid) \<leftarrow>
            case (fst pd) of
                PageDirectoryCap x _ asid \<Rightarrow> returnOk (x, asid)
              | _ \<Rightarrow> throw;

          (* Collect mapping from target cap. *)
          (frame, sz) \<leftarrow> returnOk $ (case target of FrameCap p R sz m mp \<Rightarrow> (p,sz));

          target_slots \<leftarrow> cdl_create_mapping_entries vaddr sz pd_object_id;

          (* Calculate rights. *)
          new_rights \<leftarrow> returnOk $ validate_vm_rights $ cap_rights target \<inter> rights;

          (* Return the map intent. *)
          returnOk $ PageMap (FrameCap frame (cap_rights target) sz Real asid)
            (FrameCap frame new_rights sz Fake None) target_ref target_slots
        odE \<sqinter> throw

    (* Unmap this PageTable. *)
    | PageUnmapIntent \<Rightarrow>
      (returnOk $ PageUnmap (cap_object target) target_ref) \<sqinter> throw

    (* Change the rights on a given mapping. *)
    | PageRemapIntent rights attrs \<Rightarrow>
        doE
          (* Ensure user has a right to the PD. *)
          pd \<leftarrow> throw_on_none $ get_index caps 0;
          pd_object_id \<leftarrow>
            case (fst pd) of
                PageDirectoryCap x _ _ \<Rightarrow> returnOk x
              | _ \<Rightarrow> throw;

          pd_object \<leftarrow> liftE $ get_object pd_object_id;

          (* Find all of our children caps. *)
          pd_slots \<leftarrow> liftE $ gets $ all_pd_pt_slots pd_object pd_object_id;
          target_slots \<leftarrow> liftE $ select {M. set M \<subseteq> pd_slots \<and> distinct M};

          (* Calculate rights. *)
          new_rights \<leftarrow> returnOk $ validate_vm_rights $ cap_rights target \<inter> rights;

          (* Collect mapping from target cap. *)
          (frame, sz) \<leftarrow> returnOk $ (case target of FrameCap p R sz m mp \<Rightarrow> (p,sz));

          returnOk $ PageRemap (FrameCap frame new_rights sz Fake None) target_slots
        odE \<sqinter> throw

    (* Flush the caches associated with this page. *)
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


(* Invoke a page table. *)
definition
  invoke_page_table :: "cdl_page_table_invocation \<Rightarrow> unit k_monad"
where
  "invoke_page_table params \<equiv> case params of
      PageTableMap real_pt_cap pt_cap pt_cap_ref pd_target_slot \<Rightarrow>
        do set_cap pt_cap_ref real_pt_cap;
           (*
            * We install the Page Table into the Page Directory.  The
            * concrete kernel uses hardware-defined PDEs (Page Directory
            * Entries). Our abstract spec just uses caps.
            *)
           insert_cap_orphan pt_cap pd_target_slot
        od
    | PageTableUnmap obj pt_cap_ref \<Rightarrow>
        do unmap_page_table obj;
           clear_object_caps obj \<sqinter> return ();
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
          (* Clear out the target slots. *)
        do
          set_cap frame_cap_ref frame_cap;
          mapM_x (swp set_cap pseudo_frame_cap) target_slots
        od

    | PageRemap pseudo_frame_cap target_slots \<Rightarrow>
          mapM_x (swp set_cap pseudo_frame_cap) target_slots

    | PageUnmap obj frame_cap_ref \<Rightarrow>
        do
          unmap_page obj \<sqinter> return ();
          cap \<leftarrow> get_cap frame_cap_ref;
          set_cap frame_cap_ref (reset_mem_mapping cap)
        od

    | PageFlushCaches flush \<Rightarrow> return ()
    
    | PageGetAddress \<Rightarrow> 
        do
          ct \<leftarrow> gets_the cdl_current_thread;
          corrupt_tcb_intent ct
        od
  "

end
