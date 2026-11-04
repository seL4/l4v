(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Unmapping pages and what is needed for it: short cut delete and finalisation of caps.
   This theory is for AArch32 only. Other architectures do not model unmapping. *)

theory PageTableUnmap_D
  imports
    Invocations_D
    KHeap_D
begin

context
  notes [[function_internals =true]]
begin

fun fast_finalise :: "cdl_cap \<Rightarrow> unit k_monad" where
    "fast_finalise NullCap = return ()"
  | "fast_finalise RestartCap = return ()"
  | "fast_finalise RunningCap = return ()"
  | "fast_finalise (MasterReplyCap r) = return ()"
  | "fast_finalise (PendingSyncSendCap r _ _ _ _ _) = return ()"
  | "fast_finalise (PendingSyncRecvCap r _ _) = return ()"
  | "fast_finalise (PendingNtfnRecvCap r) = return ()"
  | "fast_finalise DomainCap = return ()"
  | "fast_finalise (PageTableCap _ _ x _) = (if x = Real then fail else return ())"
  | "fast_finalise (FrameCap _ _ _ _ x _) = (if x = Real then fail else return ())"
  | "fast_finalise _ = fail"

end

definition ep_related_cap :: "cdl_cap \<Rightarrow> bool" where
  "ep_related_cap cap \<equiv>
     case cap of
       EndpointCap o_id badge rights \<Rightarrow> True
     | NotificationCap o_id badge rights \<Rightarrow> True
     | ReplyCap o_id rights \<Rightarrow> True
     \<comment> \<open>these are like EP caps in the sense that their syscall has no intent argument or label:\<close>
     | SGISignalCap irq target \<Rightarrow> True
     | _ \<Rightarrow> False"

definition cdl_cap_irq :: "cdl_cap \<Rightarrow> cdl_irq option" where
  "cdl_cap_irq cap \<equiv> case cap of IrqHandlerCap irq \<Rightarrow> Some irq | _ \<Rightarrow> None"

definition always_empty_slot :: "cdl_cap_ref \<Rightarrow> unit k_monad" where
  "always_empty_slot slot = do
     remove_parent slot;
     set_cap slot NullCap
   od"

definition empty_slot :: "cdl_cap_ref \<Rightarrow> unit k_monad"  where
  "empty_slot slot = do
     cap \<leftarrow> get_cap slot;
     if cap = NullCap
     then return ()
     else do
       remove_parent slot;
       set_cap slot NullCap
     od
   od"

text \<open>
  Non-premptable delete.

  Should only be used on deletes guaranteed not to preempt (and you are happy to prove this).
  In particular, it is useful for deleting caps that exist at the CapDL level  but not at lower
  levels. Deleting endpoint-related caps is not needed during system initialisation.\<close>
definition delete_cap_simple :: "cdl_cap_ref \<Rightarrow> unit k_monad" where
  "delete_cap_simple cap_ref \<equiv> do
     cap \<leftarrow> get_cap cap_ref;
     if ep_related_cap cap
     then chaos
     else unless (cap = NullCap) $ do
       fast_finalise cap;
       always_empty_slot cap_ref
     od
   od"

definition cdl_get_pde :: "cdl_cap_ref \<Rightarrow> cdl_cap k_monad" where
  "cdl_get_pde ptr \<equiv> get_cap ptr"

definition cdl_lookup_pd_slot :: "cdl_object_id \<Rightarrow> vptr \<Rightarrow> cdl_cap_ref" where
  "cdl_lookup_pd_slot pd vptr \<equiv> (pd, unat (vptr >> sectionBits))"

definition cdl_lookup_pt_slot :: "cdl_object_id \<Rightarrow> vptr \<Rightarrow> cdl_cap_ref except_monad" where
  "cdl_lookup_pt_slot pd vptr \<equiv> doE
     pd_slot \<leftarrow> returnOk (cdl_lookup_pd_slot pd vptr);
     pdcap \<leftarrow> liftE $ cdl_get_pde pd_slot;
     case pdcap of cdl_cap.PageTableCap PT ref (Fake _)
       None \<Rightarrow> doE pt \<leftarrow> returnOk ref;
                   pt_index \<leftarrow> returnOk ((vptr >> 12) && pt_slot_vaddr_mask);
                   returnOk (pt, unat pt_index)
               odE
     | _ \<Rightarrow> throw
   odE"

definition cdl_find_pd_for_asid :: "cdl_mapped_addr \<Rightarrow> cdl_object_id except_monad" where
  "cdl_find_pd_for_asid maddr \<equiv> doE
     asid_table \<leftarrow> liftE $ gets cdl_asid_table;
     asid_pool \<leftarrow> returnOk $ asid_table (fst (fst maddr));
     pd_cap_ref \<leftarrow> case asid_pool of
                     Some (AsidPoolCap ptr _) \<Rightarrow> returnOk (ptr, (snd \<circ> fst) maddr)
                   | _ \<Rightarrow> throw;
     pd_cap \<leftarrow> liftE $ get_cap pd_cap_ref;
     case pd_cap of PageTableCap PD pd _ _ \<Rightarrow> returnOk pd | _ \<Rightarrow> throw
   odE"

definition cdl_page_mapping_entries ::
  "vptr \<Rightarrow> nat \<Rightarrow> cdl_object_id \<Rightarrow> cdl_cap_ref except_monad"
  where
  "cdl_page_mapping_entries vptr pgsz pd \<equiv>
     if pgsz = 12 then doE
       p \<leftarrow> cdl_lookup_pt_slot pd vptr;
            returnOk p
     odE
     else if pgsz = 16 then doE
       p \<leftarrow> cdl_lookup_pt_slot pd vptr;
            returnOk p
       odE
     else if pgsz = sectionBits then doE
       p \<leftarrow> returnOk $ cdl_lookup_pd_slot pd vptr;
            returnOk p
     odE
     else if pgsz = superSectionBits then doE
       p \<leftarrow> returnOk $ cdl_lookup_pd_slot pd vptr;
            returnOk p
     odE
     else throw"

text \<open>Unmap a frame.\<close>

definition might_throw :: "('a + unit) k_monad" where
   "might_throw \<equiv> returnOk () \<sqinter> throw"

definition unmap_page :: "cdl_mapped_addr  \<Rightarrow> cdl_object_id \<Rightarrow> nat \<Rightarrow> unit k_monad" where
  "unmap_page maddr frame_id pgsz \<equiv> doE
     pd \<leftarrow> cdl_find_pd_for_asid maddr;
     pslot \<leftarrow> cdl_page_mapping_entries (snd maddr) pgsz pd;
     might_throw;
     liftE $ delete_cap_simple pslot;
     returnOk ()
   odE <catch> (K $ return ())"

end
