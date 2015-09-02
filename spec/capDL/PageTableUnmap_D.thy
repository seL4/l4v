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
 * Unmapping pages and page tables and what is needed for it:
 * short cut delete, revoke and finale of caps, ipc cancelling. 
 *)

theory PageTableUnmap_D
imports
  Invocations_D
  KHeap_D
  "../../lib/wp/NonDetMonadLemmas"
begin

-- "Return all slots in the system containing a cap with the given property."
definition
  slots_with :: "(cdl_cap \<Rightarrow> bool) \<Rightarrow> cdl_state \<Rightarrow> cdl_cap_ref set"
where
  "slots_with P s \<equiv> {(obj, slot). \<exists>x c. cdl_objects s obj = Some x \<and> 
                                        has_slots x \<and> 
                                        object_slots x slot = Some c \<and> P c}"


-- "Remove a pending operation from the given TCB."
definition
  remove_pending_operation :: "cdl_tcb \<Rightarrow> cdl_cap \<Rightarrow> cdl_tcb"
where
  "remove_pending_operation t cap \<equiv> t\<lparr>cdl_tcb_caps := (cdl_tcb_caps t)(tcb_pending_op_slot \<mapsto> cap)\<rparr>"


-- "Is the given thread pending on the given endpoint?"
definition
  is_thread_blocked_on_endpoint :: "cdl_tcb \<Rightarrow> cdl_object_id \<Rightarrow> bool"
where
  "is_thread_blocked_on_endpoint t ep \<equiv>
    case (cdl_tcb_caps t tcb_pending_op_slot) of
        Some (PendingSyncSendCap p _ _ _ _) \<Rightarrow> p = ep
      | Some (PendingSyncRecvCap p is_reply ) \<Rightarrow> p = ep \<and> \<not> is_reply
      | Some (PendingAsyncRecvCap p) \<Rightarrow> p = ep
      | _ \<Rightarrow> False"


-- "Cancel all pending IPCs currently blocked on this endpoint."
definition
  ep_cancel_all :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "ep_cancel_all ep \<equiv>
    modify (\<lambda>s. s\<lparr>cdl_objects :=  Option.map
        (\<lambda>obj. case obj of
            Tcb t \<Rightarrow>
              if (is_thread_blocked_on_endpoint t ep) then
                Tcb (remove_pending_operation t RestartCap)
              else
                Tcb t
           | _ \<Rightarrow> obj)
          \<circ> (cdl_objects s)\<rparr>)"

-- "Is the given thread bound to the given aep?"
definition
  is_thread_bound_to_aep :: "cdl_tcb \<Rightarrow> cdl_object_id \<Rightarrow> bool"
where
  "is_thread_bound_to_aep t aep \<equiv>
    case (cdl_tcb_caps t tcb_boundaep_slot) of
        Some (BoundAsyncCap a) \<Rightarrow> a = aep
      | _ \<Rightarrow> False"

-- "find all tcbs that are bound to a given aep"
definition
  get_bound_aep_threads :: "cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> cdl_object_id set"
where
  "get_bound_aep_threads aep_id state \<equiv>
     {x. \<exists>a. (cdl_objects state) x = Some (Tcb a) \<and>
         (((cdl_tcb_caps a) tcb_boundaep_slot) = Some (BoundAsyncCap aep_id))}"

definition
  modify_bound_aep :: "cdl_tcb \<Rightarrow> cdl_cap \<Rightarrow> cdl_tcb"
where
  "modify_bound_aep t cap \<equiv> t \<lparr> cdl_tcb_caps := (cdl_tcb_caps t)(tcb_boundaep_slot \<mapsto> cap)\<rparr>"
 

abbreviation
  do_unbind_aep :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "do_unbind_aep tcb \<equiv> set_cap (tcb, tcb_boundaep_slot) NullCap"

definition
  unbind_async_endpoint :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "unbind_async_endpoint tcb \<equiv> do
     cap \<leftarrow> KHeap_D.get_cap (tcb, tcb_boundaep_slot);
     (case cap of
      BoundAsyncCap _ \<Rightarrow> do_unbind_aep tcb
    | _ \<Rightarrow> return ())
   od"
  
definition
  unbind_maybe_aep :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "unbind_maybe_aep aep_id \<equiv> do
     bound_tcbs \<leftarrow> gets $ get_bound_aep_threads aep_id;
     t \<leftarrow> option_select bound_tcbs;
     (case t of
       None \<Rightarrow> return ()
     | Some tcb \<Rightarrow> do_unbind_aep tcb)
  od"

definition
  can_fast_finalise :: "cdl_cap \<Rightarrow> bool" where
 "can_fast_finalise cap \<equiv> case cap of ReplyCap r \<Rightarrow> True
                       | MasterReplyCap r \<Rightarrow> True
                       | EndpointCap r b R \<Rightarrow> True
                       | AsyncEndpointCap r b R \<Rightarrow> True
                       | NullCap \<Rightarrow> True
                       | RestartCap \<Rightarrow> True
                       | RunningCap \<Rightarrow> True
                       | PendingSyncSendCap r _ _ _ _ \<Rightarrow> True
                       | PendingSyncRecvCap r _ \<Rightarrow> True
                       | PendingAsyncRecvCap r \<Rightarrow> True
                       | DomainCap \<Rightarrow> True
                       | PageDirectoryCap _ x _ \<Rightarrow> \<not>(x = Real)
                       | PageTableCap _ x _ \<Rightarrow> \<not>(x = Real)
                       | FrameCap _ _ _ x _ \<Rightarrow> \<not>(x = Real)
                       | _ \<Rightarrow> False"

fun
  fast_finalise :: "cdl_cap \<Rightarrow> bool \<Rightarrow> unit k_monad"
where
  "fast_finalise NullCap                  final = return ()"
| "fast_finalise (RestartCap)             final = return ()"
| "fast_finalise (RunningCap)             final = return ()"
| "fast_finalise (ReplyCap r)             final = return ()"
| "fast_finalise (MasterReplyCap r)       final = return ()"
| "fast_finalise (EndpointCap r b R)      final =
      (when final $ ep_cancel_all r)"
| "fast_finalise (AsyncEndpointCap r b R) final =
      (when final $ do
            unbind_maybe_aep r;
            ep_cancel_all r
          od)"
| "fast_finalise (PendingSyncSendCap r _ _ _ _) final =  return()"
| "fast_finalise (PendingSyncRecvCap r _)   final = return()"
| "fast_finalise  (PendingAsyncRecvCap r) final = return()"
| "fast_finalise DomainCap final = return ()"
| "fast_finalise (PageDirectoryCap _ x _) _ = (if x = Real then fail else return())"
| "fast_finalise (PageTableCap _ x _) _ = (if x = Real then fail else return())"
| "fast_finalise (FrameCap _ _ _ x _) _ = (if x = Real then fail else return())"
| "fast_finalise _ _ = fail"


-- "These caps don't count when determining if an entity should be deleted or not"
definition
  cap_counts :: "cdl_cap \<Rightarrow> bool" where
 "cap_counts cap \<equiv> (case cap of
    cdl_cap.NullCap \<Rightarrow> False
  | UntypedCap _ _ \<Rightarrow> False
  | ReplyCap _ \<Rightarrow> False
  | MasterReplyCap _ \<Rightarrow> False
  | RestartCap \<Rightarrow> False
  | RunningCap \<Rightarrow> False
  | PendingSyncSendCap _ _ _ _ _ \<Rightarrow> False
  | PendingSyncRecvCap _ _ \<Rightarrow> False
  | PendingAsyncRecvCap _ \<Rightarrow> False
  | DomainCap \<Rightarrow> False
  | BoundAsyncCap _ \<Rightarrow> False
  | IrqControlCap  \<Rightarrow> False
  | AsidControlCap \<Rightarrow> False
  | IOSpaceMasterCap \<Rightarrow> False
  | FrameCap _ _ _ c _ \<Rightarrow> c = Real
  | PageTableCap _ c _ \<Rightarrow> c = Real
  | PageDirectoryCap _ c _ \<Rightarrow> c = Real
  | _ \<Rightarrow> True)"

definition
  cdl_cap_irq :: "cdl_cap \<Rightarrow> cdl_irq option" where
 "cdl_cap_irq cap \<equiv> (case cap of IrqHandlerCap irq \<Rightarrow> Some irq | _ \<Rightarrow> None)"

-- "Some caps don't count when determining if an entity should be deleted or not"
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


text {*
 Non-premptable delete.
 
 Should only be used on deletes guaranteed not to preempt
 (and you are happy to prove this). In particular, it is
 useful for deleting caps that exist at the CapDL level
 but not at lower levels.
*}
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


text {*
  Non-preemptable revoke.
 
  Should only be used on bounded revokes.
   * PageTableUnmap pt_cap_ref
   * PageRemap _ frame_cap_ref _
   * PageUnmap frame_cap_ref \<Rightarrow>
   * revoke_cap_simple (target_tcb, tcb_replycap_slot)
*}
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

  

text {*
  Unmap a frame.
 
  We can't deterministically calculate what will be unmapped without
  modelling the complexities of ASIDs and keeping track in each frame
  cap which ASID/slot it was used to provide a mapping in.
 
  Instead, we just non-deterministically choose a bunch of mappings
  to remove. This is painful, but less painful than forcing users to
  deal with the complexities of ASIDs.
*}
definition
  unmap_page :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "unmap_page frame_id \<equiv>
    do
      all_mappings \<leftarrow> gets $ slots_with (\<lambda>x. \<exists>rights sz asid.
                           x = FrameCap frame_id rights sz Fake asid);
      y \<leftarrow> select {M. set M \<subseteq> all_mappings \<and> distinct M};
      mapM_x delete_cap_simple y
    od"


text {*
  Unmap a page table.
 
  This hits the same problems as 'unmap_page', so we also
  non-deterministically choose a bunch of page-tables to unmap.
*}
definition
  unmap_page_table :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "unmap_page_table pt_id \<equiv>
    do
      all_mappings \<leftarrow> gets $ slots_with (\<lambda>x. \<exists>rights.
                           x = PageTableCap pt_id Fake rights);
      y \<leftarrow> select {M. set M \<subseteq> all_mappings \<and> distinct M};
      mapM_x delete_cap_simple y
    od"


end
