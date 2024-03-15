(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Unmapping pages and page tables and what is needed for it:
 * short cut delete, revoke and finale of caps, ipc cancelling.
 *)

theory PageTableUnmap_D
imports
  Invocations_D
  KHeap_D
begin

\<comment> \<open>Return all slots in the system containing a cap with the given property.\<close>
definition
  slots_with :: "(cdl_cap \<Rightarrow> bool) \<Rightarrow> cdl_state \<Rightarrow> cdl_cap_ref set"
where
  "slots_with P s \<equiv> {(obj, slot). \<exists>x c. cdl_objects s obj = Some x \<and>
                                        has_slots x \<and>
                                        object_slots x slot = Some c \<and> P c}"


\<comment> \<open>Remove a pending operation from the given TCB.\<close>
definition
  remove_pending_operation :: "cdl_tcb \<Rightarrow> cdl_cap \<Rightarrow> cdl_tcb"
where
  "remove_pending_operation t cap \<equiv> t\<lparr>cdl_tcb_caps := (cdl_tcb_caps t)(tcb_pending_op_slot \<mapsto> cap)\<rparr>"


\<comment> \<open>Is the given thread pending on the given endpoint?\<close>
definition
  is_thread_blocked_on_endpoint :: "cdl_tcb \<Rightarrow> cdl_object_id \<Rightarrow> bool"
where
  "is_thread_blocked_on_endpoint t ep \<equiv>
    case (cdl_tcb_caps t tcb_pending_op_slot) of
        Some (PendingSyncSendCap p _ _ _ _ _) \<Rightarrow> p = ep
      | Some (PendingSyncRecvCap p is_reply _) \<Rightarrow> p = ep \<and> \<not> is_reply
      | Some (PendingNtfnRecvCap p) \<Rightarrow> p = ep
      | _ \<Rightarrow> False"


\<comment> \<open>Cancel all pending IPCs currently blocked on this endpoint.\<close>
definition
  cancel_all_ipc :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "cancel_all_ipc ep \<equiv>
    modify (\<lambda>s. s\<lparr>cdl_objects :=  map_option
        (\<lambda>obj. case obj of
            Tcb t \<Rightarrow>
              if (is_thread_blocked_on_endpoint t ep) then
                Tcb (remove_pending_operation t RestartCap)
              else
                Tcb t
           | _ \<Rightarrow> obj)
          \<circ> (cdl_objects s)\<rparr>)"

\<comment> \<open>Is the given thread bound to the given ntfn?\<close>
definition
  is_thread_bound_to_ntfn :: "cdl_tcb \<Rightarrow> cdl_object_id \<Rightarrow> bool"
where
  "is_thread_bound_to_ntfn t ntfn \<equiv>
    case (cdl_tcb_caps t tcb_boundntfn_slot) of
        Some (BoundNotificationCap a) \<Rightarrow> a = ntfn
      | _ \<Rightarrow> False"

\<comment> \<open>find all tcbs that are bound to a given ntfn\<close>
definition
  get_bound_notification_threads :: "cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> cdl_object_id set"
where
  "get_bound_notification_threads ntfn_id state \<equiv>
     {x. \<exists>a. (cdl_objects state) x = Some (Tcb a) \<and>
         (((cdl_tcb_caps a) tcb_boundntfn_slot) = Some (BoundNotificationCap ntfn_id))}"

definition
  modify_bound_ntfn :: "cdl_tcb \<Rightarrow> cdl_cap \<Rightarrow> cdl_tcb"
where
  "modify_bound_ntfn t cap \<equiv> t \<lparr> cdl_tcb_caps := (cdl_tcb_caps t)(tcb_boundntfn_slot \<mapsto> cap)\<rparr>"


abbreviation
  do_unbind_notification :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "do_unbind_notification tcb \<equiv> set_cap (tcb, tcb_boundntfn_slot) NullCap"

definition
  unbind_notification :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "unbind_notification tcb \<equiv> do
     cap \<leftarrow> KHeap_D.get_cap (tcb, tcb_boundntfn_slot);
     (case cap of
      BoundNotificationCap _ \<Rightarrow> do_unbind_notification tcb
    | _ \<Rightarrow> return ())
   od"

definition
  unbind_maybe_notification :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "unbind_maybe_notification ntfn_id \<equiv> do
     bound_tcbs \<leftarrow> gets $ get_bound_notification_threads ntfn_id;
     t \<leftarrow> option_select bound_tcbs;
     (case t of
       None \<Rightarrow> return ()
     | Some tcb \<Rightarrow> do_unbind_notification tcb)
  od"

definition
  can_fast_finalise :: "cdl_cap \<Rightarrow> bool" where
 "can_fast_finalise cap \<equiv> case cap of ReplyCap r R \<Rightarrow> True
                       | MasterReplyCap r \<Rightarrow> True
                       | EndpointCap r b R \<Rightarrow> True
                       | NotificationCap r b R \<Rightarrow> True
                       | NullCap \<Rightarrow> True
                       | RestartCap \<Rightarrow> True
                       | RunningCap \<Rightarrow> True
                       | PendingSyncSendCap r _ _ _ _ _ \<Rightarrow> True
                       | PendingSyncRecvCap r _ _ \<Rightarrow> True
                       | PendingNtfnRecvCap r \<Rightarrow> True
                       | DomainCap \<Rightarrow> True
                       | PageDirectoryCap _ x _ \<Rightarrow> \<not>(x = Real)
                       | PageTableCap _ x _ \<Rightarrow> \<not>(x = Real)
                       | FrameCap _ _ _ _ x _ \<Rightarrow> \<not>(x = Real)
                       | _ \<Rightarrow> False"

context
notes [[function_internals =true]]
begin

fun
  fast_finalise :: "cdl_cap \<Rightarrow> bool \<Rightarrow> unit k_monad"
where
  "fast_finalise NullCap                  final = return ()"
| "fast_finalise (RestartCap)             final = return ()"
| "fast_finalise (RunningCap)             final = return ()"
| "fast_finalise (ReplyCap r R)           final = return ()"
| "fast_finalise (MasterReplyCap r)       final = return ()"
| "fast_finalise (EndpointCap r b R)      final =
      (when final $ cancel_all_ipc r)"
| "fast_finalise (NotificationCap r b R) final =
      (when final $ do
            unbind_maybe_notification r;
            cancel_all_ipc r
          od)"
| "fast_finalise (PendingSyncSendCap r _ _ _ _ _) final = return()"
| "fast_finalise (PendingSyncRecvCap r _ _) final = return()"
| "fast_finalise  (PendingNtfnRecvCap r) final = return()"
| "fast_finalise DomainCap final = return ()"
| "fast_finalise (PageDirectoryCap _ x _) _ = (if x = Real then fail else return())"
| "fast_finalise (PageTableCap _ x _) _ = (if x = Real then fail else return())"
| "fast_finalise (FrameCap _ _ _ _ x _) _ = (if x = Real then fail else return())"
| "fast_finalise _ _ = fail"

end

\<comment> \<open>These caps don't count when determining if an entity should be deleted or not\<close>
definition
  cap_counts :: "cdl_cap \<Rightarrow> bool" where
 "cap_counts cap \<equiv> (case cap of
    cdl_cap.NullCap \<Rightarrow> False
  | UntypedCap _ _ _ \<Rightarrow> False
  | ReplyCap _ _ \<Rightarrow> False
  | MasterReplyCap _ \<Rightarrow> False
  | RestartCap \<Rightarrow> False
  | RunningCap \<Rightarrow> False
  | PendingSyncSendCap _ _ _ _ _ _ \<Rightarrow> False
  | PendingSyncRecvCap _ _ _ \<Rightarrow> False
  | PendingNtfnRecvCap _ \<Rightarrow> False
  | DomainCap \<Rightarrow> False
  | BoundNotificationCap _ \<Rightarrow> False
  | IrqControlCap  \<Rightarrow> False
  | SGISignalCap _ _ \<Rightarrow> False
  | AsidControlCap \<Rightarrow> False
  | IOSpaceMasterCap \<Rightarrow> False
  | FrameCap _ _ _ _ c _ \<Rightarrow> c = Real
  | PageTableCap _ c _ \<Rightarrow> c = Real
  | PageDirectoryCap _ c _ \<Rightarrow> c = Real
  | _ \<Rightarrow> True)"

definition
  cdl_cap_irq :: "cdl_cap \<Rightarrow> cdl_irq option" where
 "cdl_cap_irq cap \<equiv> (case cap of IrqHandlerCap irq \<Rightarrow> Some irq | _ \<Rightarrow> None)"

\<comment> \<open>Some caps don't count when determining if an entity should be deleted or not\<close>
definition
  is_final_cap' :: "cdl_cap \<Rightarrow> cdl_state \<Rightarrow> bool" where
 "is_final_cap' cap s \<equiv> ((cap_counts cap) \<and>
  (\<exists>cref. {cref. \<exists>cap'. opt_cap cref s = Some cap'
                       \<and> (cap_object cap = cap_object cap'
                             \<and> cdl_cap_irq cap = cdl_cap_irq cap')
                       \<and> cap_counts cap'}
         = {cref}))"


definition
  is_final_cap :: "cdl_cap \<Rightarrow> bool k_monad" where
  "is_final_cap cap \<equiv> gets (is_final_cap' cap)"


definition
  always_empty_slot :: "cdl_cap_ref \<Rightarrow> unit k_monad"
where
 "always_empty_slot slot = do
    remove_parent slot;
    set_cap slot NullCap
  od"

definition
  empty_slot :: "cdl_cap_ref \<Rightarrow> unit k_monad"
where
 "empty_slot slot = do
  cap \<leftarrow> get_cap slot;
  if cap = NullCap then
    return ()
  else do
    remove_parent slot;
    set_cap slot NullCap
    od
  od"


text \<open>
 Non-premptable delete.

 Should only be used on deletes guaranteed not to preempt
 (and you are happy to prove this). In particular, it is
 useful for deleting caps that exist at the CapDL level
 but not at lower levels.
\<close>
definition
  delete_cap_simple :: "cdl_cap_ref \<Rightarrow> unit k_monad"
where
  "delete_cap_simple cap_ref \<equiv> do
    cap \<leftarrow> get_cap cap_ref;
    unless (cap = NullCap) $ do
      final \<leftarrow> is_final_cap cap;
      fast_finalise cap final;
      always_empty_slot cap_ref
    od
  od"


text \<open>
  Non-preemptable revoke.

  Should only be used on bounded revokes.
   * PageTableUnmap pt_cap_ref
   * PageUnmap frame_cap_ref \<Rightarrow>
   * revoke_cap_simple (target_tcb, tcb_replycap_slot)
\<close>
function
  revoke_cap_simple :: "cdl_cap_ref \<Rightarrow> unit k_monad"
where
  "revoke_cap_simple victim s = (do
    descendants \<leftarrow> gets $ KHeap_D.descendants_of victim;
    assert (finite descendants);
    non_null \<leftarrow> gets (\<lambda>s. {slot. opt_cap slot s \<noteq> Some NullCap \<and> opt_cap slot s \<noteq> None});
    non_null_descendants \<leftarrow> return (descendants \<inter> non_null);
    if (non_null_descendants \<noteq> {}) then do
      a \<leftarrow> select non_null_descendants;
      delete_cap_simple a;
      revoke_cap_simple victim
    od else return ()
  od) s"
  by auto


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

definition
  cdl_find_pd_for_asid :: "cdl_mapped_addr \<Rightarrow> cdl_object_id except_monad"
where
  "cdl_find_pd_for_asid maddr \<equiv> doE
     asid_table \<leftarrow> liftE $ gets cdl_asid_table;
     asid_pool \<leftarrow> returnOk $ asid_table (fst (fst maddr));
     pd_cap_ref \<leftarrow> (case asid_pool of Some (AsidPoolCap ptr _) \<Rightarrow> returnOk (ptr, (snd \<circ> fst) maddr)
              | _ \<Rightarrow> throw );
     pd_cap \<leftarrow> liftE $ get_cap pd_cap_ref;
     case pd_cap of (PageDirectoryCap pd _ _) \<Rightarrow> returnOk pd
     | _ \<Rightarrow> throw
   odE "

definition cdl_page_mapping_entries :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word
                                       \<Rightarrow> ((32 word \<times> nat) list) except_monad"
  where "cdl_page_mapping_entries vptr pgsz pd \<equiv>
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

definition
  cdl_page_table_mapped :: "cdl_mapped_addr \<Rightarrow> cdl_object_id \<Rightarrow> (cdl_cap_ref option) k_monad"
where
  "cdl_page_table_mapped maddr pt_id \<equiv> doE
     pd \<leftarrow> cdl_find_pd_for_asid maddr;
     pd_slot \<leftarrow> returnOk (cdl_lookup_pd_slot pd (snd maddr));
     pdcap \<leftarrow> liftE $ cdl_get_pde pd_slot;
     (case pdcap of
       cdl_cap.PageTableCap ref Fake None \<Rightarrow>
         (returnOk $ if ref = pt_id then Some pd_slot else None)
     | _ \<Rightarrow> returnOk None )
   odE <catch> (K (return None))"

text \<open>
  Unmap a frame.
\<close>

definition
 "might_throw \<equiv> (returnOk ()) \<sqinter> throw"

definition
  unmap_page :: "cdl_mapped_addr  \<Rightarrow> cdl_object_id \<Rightarrow> nat \<Rightarrow> unit k_monad"
where
  "unmap_page maddr frame_id pgsz \<equiv>
    doE
      pd \<leftarrow> cdl_find_pd_for_asid maddr;
      pslots \<leftarrow> cdl_page_mapping_entries (snd maddr) pgsz pd;
      might_throw;
      liftE $ mapM_x delete_cap_simple pslots;
      returnOk ()
    odE <catch> (K $ return ())"


text \<open>
  Unmap a page table.

  This hits the same problems as 'unmap_page', so we also
  non-deterministically choose a bunch of page-tables to unmap.
\<close>
definition
  unmap_page_table  :: "cdl_mapped_addr \<Rightarrow> cdl_object_id  \<Rightarrow> unit k_monad"
where
  "unmap_page_table maddr pt_id\<equiv>
    do
      pt_slot \<leftarrow> cdl_page_table_mapped maddr pt_id;
      case pt_slot of (Some slot) \<Rightarrow> delete_cap_simple slot
      | None \<Rightarrow> return ()
    od"


end
