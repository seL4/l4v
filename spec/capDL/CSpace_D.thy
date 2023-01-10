(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Operations on CSpace
 *)

theory CSpace_D
imports
  PageTableUnmap_D
begin

(* Does the given cap have any children? *)
definition
  has_children :: "cdl_cap_ref \<Rightarrow> cdl_state \<Rightarrow> bool"
where
  "has_children parent s = (\<exists>child. is_cdt_parent s parent child)"

(*
 * Ensure that the given cap does not contain any children
 * in the CDT.
 *)
definition
  ensure_no_children :: "cdl_cap_ref \<Rightarrow> unit except_monad"
where
  "ensure_no_children x \<equiv> doE
     c \<leftarrow> liftE $ gets (has_children x);
     whenE c $ throw
   odE"

(* Ensure that the given cap slot is empty. *)
definition
  ensure_empty :: "cdl_cap_ref \<Rightarrow> unit except_monad"
where
  "ensure_empty cap_ref \<equiv> doE
     cap \<leftarrow> liftE $ get_cap cap_ref;
     unlessE (cap = NullCap) $ throw
  odE"

(* Insert a new cap into an object. The cap will have no parent. *)
definition
  insert_cap_orphan :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> unit k_monad"
where
  "insert_cap_orphan new_cap dest_slot \<equiv> do
     old_cap \<leftarrow> get_cap dest_slot;
     assert (old_cap = NullCap);
     set_cap dest_slot new_cap
   od"



primrec (nonexhaustive)
  available_range :: "cdl_cap \<Rightarrow> cdl_object_id set"
where
  "available_range (UntypedCap _ r available) = available"

definition
  set_available_range :: "cdl_cap \<Rightarrow> cdl_object_id set \<Rightarrow> cdl_cap"
where
  "set_available_range cap nrange \<equiv>
    case cap of UntypedCap d r available \<Rightarrow> UntypedCap d r nrange | _ \<Rightarrow> cap"

lemmas set_avaiable_range_simps[simp] = set_available_range_def[split_simps cdl_cap.split]

definition
  set_untyped_cap_as_full :: "cdl_cap \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> unit k_monad"
where
  "set_untyped_cap_as_full src_cap new_cap src_slot \<equiv>
  if (is_untyped_cap src_cap \<and> is_untyped_cap new_cap
     \<and> cap_objects src_cap = cap_objects new_cap) then
     (set_cap src_slot (set_available_range src_cap {}))
     else return ()"

(* Insert a new cap into an object. The cap will be a sibling. *)
definition
  insert_cap_sibling :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap_ref \<Rightarrow> unit k_monad"
where
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
definition
  insert_cap_child :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap_ref \<Rightarrow> unit k_monad"
where
  "insert_cap_child new_cap src_slot dest_slot \<equiv> do
    src_cap \<leftarrow> get_cap src_slot;
    old_cap \<leftarrow> get_cap dest_slot;
    assert (old_cap = NullCap);
    set_untyped_cap_as_full src_cap new_cap src_slot;
    set_cap dest_slot new_cap;
    set_parent dest_slot src_slot
  od"

(*
 * Delete an ASID pool.
 *)
definition
  delete_asid_pool :: "cdl_cnode_index \<Rightarrow> cdl_object_id \<Rightarrow> unit k_monad"
where
  "delete_asid_pool base ptr \<equiv> do
    asid_table \<leftarrow> gets cdl_asid_table;
    asid_table' \<leftarrow> return $ asid_table (base \<mapsto> NullCap);
    modify (\<lambda>s. s \<lparr>cdl_asid_table := asid_table'\<rparr>)
  od \<sqinter> return ()"

(*
 * Delete a particular ASID, decactivating the PD using it
 * in the process.
 *)
definition
  delete_asid :: "cdl_asid \<Rightarrow> cdl_object_id \<Rightarrow> unit k_monad"
where
  "delete_asid asid pd \<equiv> do
    asid_table \<leftarrow> gets cdl_asid_table;
    case asid_table (fst asid) of
       Some NullCap \<Rightarrow> return ()
     | Some (AsidPoolCap p _) \<Rightarrow> set_cap (p, (snd asid)) NullCap
     | _ \<Rightarrow> fail
  od \<sqinter> return ()"

definition
  get_irq_slot :: "cdl_irq \<Rightarrow> cdl_state \<Rightarrow> cdl_cap_ref"
where
  "get_irq_slot irq s \<equiv> (cdl_irq_node s irq, 0)"

text \<open>Actions to be taken after deleting an IRQ Handler capability.\<close>
definition
  deleting_irq_handler :: "cdl_irq \<Rightarrow> unit k_monad"
where
 "deleting_irq_handler irq \<equiv>
    gets (get_irq_slot irq) >>= delete_cap_simple"

definition
  cancel_ipc ::"cdl_object_id \<Rightarrow> unit k_monad"
  where "cancel_ipc ptr \<equiv>
  do cap \<leftarrow> KHeap_D.get_cap (ptr,tcb_pending_op_slot);
   (case cap of
    PendingSyncRecvCap _ is_reply _ \<Rightarrow> ( do
     when is_reply $ update_thread_fault ptr (\<lambda>x. False);
     revoke_cap_simple (ptr,tcb_replycap_slot);
     when (\<not> is_reply) $ set_cap (ptr,tcb_pending_op_slot) NullCap
     od )
   | PendingSyncSendCap _ _ _ _ _ _ \<Rightarrow> (do
     revoke_cap_simple (ptr,tcb_replycap_slot);
     set_cap (ptr,tcb_pending_op_slot) NullCap
     od)
   | PendingNtfnRecvCap _ \<Rightarrow> (do
     revoke_cap_simple (ptr,tcb_replycap_slot);
     set_cap (ptr, tcb_pending_op_slot) NullCap
     od)
   | _ \<Rightarrow> return ())
  od"

definition
  prepare_thread_delete ::"cdl_object_id \<Rightarrow> unit k_monad"
  where "prepare_thread_delete ptr \<equiv> return ()" (* for ARM it does nothing *)

text \<open>Actions that must be taken when a capability is deleted. Returns a
Zombie capability if deletion requires a long-running operation and also a
possible IRQ to be cleared.\<close>
fun
  finalise_cap :: "cdl_cap \<Rightarrow> bool \<Rightarrow> (cdl_cap \<times> cdl_cap) k_monad"
where
  "finalise_cap NullCap                  final = return (NullCap, NullCap)"
| "finalise_cap RestartCap               final = return (NullCap, NullCap)"
| "finalise_cap (UntypedCap dev r a)           final = return (NullCap, NullCap)"
| "finalise_cap (EndpointCap r b R)      final =
      (liftM (K (NullCap, NullCap)) $ when  final $ cancel_all_ipc r)"
| "finalise_cap (NotificationCap r b R) final =
      (liftM (K (NullCap, NullCap)) $ when  final $
       do
         unbind_maybe_notification r;
         cancel_all_ipc r
       od)"
| "finalise_cap (ReplyCap r R)           final = return (NullCap, NullCap)"
| "finalise_cap (MasterReplyCap r)       final = return (NullCap, NullCap)"
| "finalise_cap (CNodeCap r bits g sz)   final =
      (return (if final then ZombieCap r else NullCap, NullCap))"
| "finalise_cap (TcbCap r)               final =
      (do
         when final $ (do unbind_notification r;
         cancel_ipc r;
         KHeap_D.set_cap (r, tcb_pending_op_slot) cdl_cap.NullCap;
         prepare_thread_delete r od);
         return (if final then (ZombieCap r) else NullCap, NullCap)
       od)"
| "finalise_cap (PendingSyncSendCap r _ _ _ _ _) final = return (NullCap, NullCap)"
| "finalise_cap (PendingSyncRecvCap r _ _) final = return (NullCap, NullCap)"
| "finalise_cap (PendingNtfnRecvCap r)  final = return (NullCap, NullCap)"
| "finalise_cap IrqControlCap            final = return (NullCap, NullCap)"
| "finalise_cap (IrqHandlerCap irq)      final = (
       if final then do
         deleting_irq_handler irq;
         return (NullCap, (IrqHandlerCap irq))
       od
       else return (NullCap, NullCap))"
| "finalise_cap (ZombieCap r)            final =
      (do assert final; return (ZombieCap r, NullCap) od)"
| "finalise_cap (AsidPoolCap ptr asid)        final = (
       if final then do
         delete_asid_pool asid ptr;
         return (NullCap, NullCap)
       od
       else return (NullCap, NullCap))"
| "finalise_cap AsidControlCap           final = return (NullCap,NullCap)"
| "finalise_cap (PageDirectoryCap ptr x (Some asid))   final = (
       if final \<and> x = Real then do
         delete_asid asid ptr;
         return (NullCap, NullCap)
       od
       else return (NullCap, NullCap))"
| "finalise_cap (PageTableCap ptr x (Some asid))     final = (
       if (final \<and> x = Real) then do
         unmap_page_table asid ptr;
         return (NullCap, NullCap)
       od
       else return (NullCap, NullCap))"
| "finalise_cap (FrameCap dev ptr _ s x (Some asid))       final = (
       if x = Real then do
         unmap_page asid ptr s;
         return (NullCap, NullCap)
       od
       else return (NullCap, NullCap))"
| "finalise_cap _ final = return (NullCap, NullCap)"


text \<open>The fast_finalise operation is used to delete a capability when it is
known that a long-running operation is impossible. It is equivalent to calling
the regular finalise operation. It cannot be defined in that way as doing so
would create a circular definition.\<close>
lemma fast_finalise_def2:
  "fast_finalise cap final = do
     assert (can_fast_finalise cap);
     result \<leftarrow> finalise_cap cap final;
     assert (result = (NullCap, NullCap))
   od"
  unfolding can_fast_finalise_def
  by (rule finalise_cap.cases[of "(cap,final)"]; simp add: assert_def liftM_def)

(*
 * Atomically swap the two given caps.
 *)

definition
  swap_cap :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> unit k_monad"
where
  "swap_cap cap1 slot1 cap2 slot2 \<equiv> do
     set_cap slot1 cap2;
     set_cap slot2 cap1;
     swap_parents slot1 slot2
  od"

(*
 * Move the given cap from one location to another,
 * possibly modifying it along the way.
 *)
definition
  move_cap :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap_ref \<Rightarrow> unit k_monad"
where
  "move_cap cap src_slot dest_slot \<equiv> do
     insert_cap_orphan cap dest_slot;
     set_cap src_slot NullCap;
     swap_parents src_slot dest_slot
  od"

definition
  monadic_rel_optionation_form :: "('a \<Rightarrow> ('s, 'b) nondet_monad)
      \<Rightarrow> (('a \<times> 's) option \<times> ('b \<times> 's) option) set"
where
 "monadic_rel_optionation_form f =
    {(x, y). (x \<noteq> None \<and> y \<noteq> None \<and> the y \<in> fst (case_prod f (the x)))
           \<or> (x \<noteq> None \<and> y = None \<and> snd (case_prod f (the x)))
           \<or> (x = None \<and> y = None)}"

definition
  monadic_option_dest :: "('a \<times> 's) option set \<Rightarrow> (('a \<times> 's) set \<times> bool)"
where
 "monadic_option_dest S = (Some -` S, None \<in> S)"

lemma use_option_form:
  "f x = (\<lambda>s. monadic_option_dest  (monadic_rel_optionation_form f `` {Some (x, s)}))"
  by (simp add: monadic_rel_optionation_form_def monadic_option_dest_def)

lemma ex_option: " (\<exists>x. P x) = ((\<exists>y. P (Some y)) \<or> P None)"
  apply safe
  apply (case_tac x, auto)
  done

lemma use_option_form_bind:
  "f x >>= g = (\<lambda>s. monadic_option_dest
       ((monadic_rel_optionation_form f O monadic_rel_optionation_form g) `` {Some (x, s)}))"
  apply (rule ext)
  apply (simp add: monadic_rel_optionation_form_def monadic_option_dest_def
                   bind_def split_def)
  apply (simp add: relcomp_unfold ex_option image_def prod_eq_iff Bex_def)
  apply fastforce
  done

definition
  monadic_trancl :: "('a \<Rightarrow> ('s, 'a) nondet_monad)
       \<Rightarrow> 'a \<Rightarrow> ('s, 'a) nondet_monad"
where
 "monadic_trancl f x = (\<lambda>s. monadic_option_dest ((monadic_rel_optionation_form f)\<^sup>* `` {Some (x, s)}))"

definition
  monadic_trancl_preemptible ::
     "('a \<Rightarrow> ('s, 'e + 'a) nondet_monad)
         \<Rightarrow> ('a \<Rightarrow> ('s, 'e + 'a) nondet_monad)"
where
 "monadic_trancl_preemptible f x
    = monadic_trancl (lift f) (Inr x)"

definition
  cap_removeable :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_state \<Rightarrow> bool"
where
 "cap_removeable cap slot s =
   (cap = NullCap
      \<or> (\<exists>p. cap = ZombieCap p \<and> swp opt_cap s ` (({p} \<times> UNIV) - {slot})
              \<subseteq> {Some NullCap, None}))"

definition
  finalise_slot_inner1 :: "cdl_cap_ref \<Rightarrow> (cdl_cap \<times> bool) k_monad"
where
 "finalise_slot_inner1 victim = do
    cap \<leftarrow> get_cap victim;
    final \<leftarrow> is_final_cap cap;
    (cap', irqopt) \<leftarrow> finalise_cap cap final;
    removeable \<leftarrow> gets $ cap_removeable cap' victim;
    when (\<not> removeable) (set_cap victim cap')
        \<sqinter> set_cap victim cap';
    return (cap', removeable)
  od"

definition
  get_zombie_range :: "cdl_cap \<Rightarrow> cdl_state \<Rightarrow> cdl_cap_ref set"
where
 "get_zombie_range cap =
    (\<lambda>s. case cap of ZombieCap p \<Rightarrow> dom (swp opt_cap s) \<inter> ({p} \<times> UNIV)
               | _ \<Rightarrow> {})"

definition
  swap_for_delete :: "cdl_cap_ref \<Rightarrow> cdl_cap_ref \<Rightarrow> unit k_monad"
where
 "swap_for_delete ptr1 ptr2 = do
    cap1 \<leftarrow> get_cap ptr1;
    cap2 \<leftarrow> get_cap ptr2;
    swap_cap cap1 ptr1 cap2 ptr2
  od"

definition
 "finalise_slot_inner2 =
      (\<lambda>(region, finalised).
        liftE (do (victim', remove) \<leftarrow> select region;
          (cap', removeable) \<leftarrow> finalise_slot_inner1 victim';
          region' \<leftarrow> gets $ get_zombie_range cap';
          return (region \<union> (region' \<times> {True}), if removeable then {(victim', remove)} else {})
        od) \<sqinter>
        liftE (do (slot, slot') \<leftarrow> select {(x, y). (x, True) \<in> region \<and> (y, True) \<in> region \<and> x \<noteq> y};
          swap_for_delete slot slot';
          return (region, {})
        od) \<sqinter>
        liftE (do victim' \<leftarrow> select {x. (x, True) \<in> finalised};
          empty_slot victim';
          return (region, {})
        od) \<sqinter>
        throw
      )"

definition
  finalise_slot :: "cdl_cap_ref \<Rightarrow> unit preempt_monad"
where
 "finalise_slot victim = doE
    (region, finalised) \<leftarrow>
      monadic_trancl_preemptible finalise_slot_inner2
        ({(victim, False)}, {});
    whenE (victim \<notin> fst ` finalised) throw
  odE"

definition
  delete_cap :: "cdl_cap_ref \<Rightarrow> unit preempt_monad"
where
 "delete_cap victim = doE
    finalise_slot victim;
    liftE $ empty_slot victim
  odE"


(*
 * Revoke all the descendants of the given cap.
 *
 * If the CDT is being modelled, this will delete all the
 * descendants of the given cap. Wonderful things happen
 * if we happen to, in this process, delete something
 * that contains the cap we are trying to revoke.
 *)
definition
  revoke_cap :: "cdl_cap_ref \<Rightarrow> unit preempt_monad"
where
  "revoke_cap victim = doE
     fin \<leftarrow> monadic_trancl_preemptible (K (doE
          S \<leftarrow> liftE $ gets $ descendants_of victim;
          if S = {} then returnOk True
          else doE
            child \<leftarrow> liftE $ select S;
            cap \<leftarrow> liftE $ get_cap child;
            assertE (cap \<noteq> NullCap);
            delete_cap child;
            Monads_D.throw \<sqinter> returnOk False
          odE
       odE)) False;
     unlessE fin throw
   odE"

(*
 * Get the badge the given thread object is using to
 * perform its IPC send operation.
 *)
definition
  get_tcb_ep_badge :: "cdl_tcb \<Rightarrow> cdl_badge option"
where
  "get_tcb_ep_badge t \<equiv>
    case (cdl_tcb_caps t tcb_pending_op_slot) of
      Some (PendingSyncSendCap _ badge _ _ _ _) \<Rightarrow> Some badge
    | _ \<Rightarrow> None"

(*
 * Cancel all pending send operations to the given endpoint
 * that are using the given badge.
 *)
definition
  cancel_badged_sends :: "cdl_object_id \<Rightarrow> cdl_badge \<Rightarrow> unit k_monad"
where
  "cancel_badged_sends ep badge \<equiv>
    modify (\<lambda>s. s\<lparr>cdl_objects := map_option
        (\<lambda>obj. case obj of
            Tcb t \<Rightarrow>
              if (is_thread_blocked_on_endpoint t ep
                  \<and> get_tcb_ep_badge t = Some badge) then
                    Tcb (remove_pending_operation t cdl_cap.RestartCap)
              else
                Tcb t
          | _ \<Rightarrow> obj) \<circ> (cdl_objects s)\<rparr>)"


(*
 * Regenerate the target object.
 *
 * Any children of the cap are first revoked. The object
 * is then reset into its original (as-if just created)
 * state. But maybe not. It's complex.
 *
 * In the C implementation, attempting to recycle a
 * non-master cap may do something that is not
 * a recycle. (Should be perhaps return an error?)
 *)
definition
  clear_object_caps :: "cdl_object_id \<Rightarrow> unit k_monad"
where
 "clear_object_caps ptr = do
    ptrs \<leftarrow> gets (\<lambda>s. {cptr. fst cptr = ptr \<and> opt_cap cptr s \<noteq> None});
    ptrlist \<leftarrow> select {xs. set xs = ptrs \<and> distinct xs};
    mapM_x empty_slot ptrlist
  od"

definition cdl_default_tcb :: "cdl_object"
where "cdl_default_tcb \<equiv>  Tcb \<lparr>cdl_tcb_caps =
           [tcb_cspace_slot \<mapsto> cdl_cap.NullCap, tcb_vspace_slot \<mapsto> cdl_cap.NullCap, tcb_replycap_slot \<mapsto>
            cdl_cap.NullCap, tcb_caller_slot \<mapsto> cdl_cap.NullCap, tcb_ipcbuffer_slot \<mapsto> cdl_cap.NullCap,
            tcb_pending_op_slot \<mapsto> cdl_cap.NullCap, tcb_boundntfn_slot \<mapsto> cdl_cap.NullCap],
           cdl_tcb_fault_endpoint = 0,
           cdl_tcb_intent =
             \<lparr>cdl_intent_op = None, cdl_intent_error = False,cdl_intent_cap = 0, cdl_intent_extras = [],
                cdl_intent_recv_slot = None\<rparr>, cdl_tcb_has_fault = False, cdl_tcb_domain = minBound\<rparr>"

definition obj_tcb :: "cdl_object \<Rightarrow> cdl_tcb"
where "obj_tcb obj \<equiv> case obj of Tcb tcb \<Rightarrow> tcb"

definition tcb_caps_merge :: "cdl_tcb \<Rightarrow> cdl_tcb \<Rightarrow> cdl_tcb"
  where "tcb_caps_merge regtcb captcb \<equiv> regtcb\<lparr>cdl_tcb_caps
  := (cdl_tcb_caps captcb)(tcb_pending_op_slot \<mapsto> the (cdl_tcb_caps regtcb tcb_pending_op_slot), tcb_boundntfn_slot \<mapsto> the (cdl_tcb_caps regtcb tcb_boundntfn_slot))\<rparr>"

definition merge_with_dft_tcb :: "cdl_object_id \<Rightarrow> unit k_monad"
where "merge_with_dft_tcb o_id \<equiv>
 do
  new_intent \<leftarrow> select UNIV;
  KHeap_D.update_thread o_id (cdl_tcb_intent_update (\<lambda>x. new_intent) \<circ> (tcb_caps_merge (obj_tcb cdl_default_tcb)))
 od"

fun
  reset_mem_mapping :: "cdl_cap \<Rightarrow> cdl_cap"
where
  "reset_mem_mapping (FrameCap dev p rts sz b mp) = FrameCap dev p rts sz b None"
| "reset_mem_mapping (PageTableCap ptr b mp) = PageTableCap ptr b None"
| "reset_mem_mapping (PageDirectoryCap ptr b ma) = PageDirectoryCap ptr b None"
| "reset_mem_mapping cap = cap"


(*
 * Walk a user's CSpace to convert a user's CPTR into a cap slot.
 *)
function
  resolve_address_bits ::
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
    if (size_left = 0) then
      returnOk (slot, 0)
    else
      doE
        next_cap \<leftarrow> liftE $ get_cap (slot);
        if is_cnode_cap next_cap then
          resolve_address_bits next_cap cap_ptr size_left
        else
          returnOk (slot, size_left)
      odE
  odE"
  by fastforce+

termination resolve_address_bits
  apply (relation "measure (\<lambda>(a,b,c). c)")
  apply (auto simp: in_monad)
  done

definition
  lookup_slot :: "cdl_object_id \<Rightarrow> cdl_cptr \<Rightarrow> cdl_cap_ref fault_monad"
where
  "lookup_slot thread cptr \<equiv>
    doE
      cspace_root \<leftarrow> liftE $ get_cap (thread, tcb_cspace_slot);
      (slot, _) \<leftarrow> resolve_address_bits cspace_root cptr word_bits;
      returnOk slot
    odE"

definition
  lookup_cap :: "cdl_object_id \<Rightarrow> cdl_cptr \<Rightarrow> cdl_cap fault_monad"
where
  "lookup_cap thread cptr \<equiv>
    doE
      slot \<leftarrow> lookup_slot thread cptr;
      liftE $ get_cap slot
    odE"

definition
  lookup_cap_and_slot :: "cdl_object_id \<Rightarrow> cdl_cptr \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) fault_monad"
where
  "lookup_cap_and_slot thread cptr \<equiv>
    doE
      slot \<leftarrow> lookup_slot thread cptr;
      cap \<leftarrow> liftE $ get_cap slot;
      returnOk (cap, slot)
    odE"

definition
  lookup_slot_for_cnode_op :: "cdl_cap \<Rightarrow> cdl_cptr \<Rightarrow> nat \<Rightarrow> cdl_cap_ref except_monad"
where
  "lookup_slot_for_cnode_op croot cptr depth \<equiv>
    doE
      whenE (depth < 1 \<or> depth > word_bits) throw;
      (slot, rem) \<leftarrow> fault_to_except $ resolve_address_bits croot cptr depth;
      if rem = 0 then returnOk slot else throw
    odE"


(*
 * Update the badge of a cap, masking off bits the lower specs are unable
 * to store for implementation reasons.
 *)
definition
  badge_update :: "word32 \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap"
where
  "badge_update data cap \<equiv> update_cap_badge (data && mask badge_bits) cap"

(*
 * Transform a capability based on a request from the user.
 *
 * The "data" word is interpreted differently for different cap types.
 *
 * We return a set of possible caps to allow for non-deterministic
 * implementations, to avoid messy implementation details of the CDT
 * in lower-level models.
 *)


definition
  update_cap_data :: "bool \<Rightarrow> word32 \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap k_monad"
where
  "update_cap_data preserve data cap \<equiv>
    return $ case cap of
        EndpointCap _ b _ \<Rightarrow>
          if b = 0 \<and> \<not> preserve then
            badge_update data cap
          else
            NullCap
      | NotificationCap _ b _ \<Rightarrow>
          if b = 0 \<and> \<not> preserve then
            badge_update data cap
          else
            NullCap
      | CNodeCap object guard guard_size sz \<Rightarrow>
          let
            reserved_bits = 3;
            guard_bits = 18;
            guard_size_bits = 5;

            new_guard_size = unat ((data >> reserved_bits) && mask guard_size_bits);
            new_guard = (data >> (reserved_bits + guard_size_bits)) && mask (min (unat ((data >> reserved_bits) && mask guard_size_bits)) guard_bits)
          in
            if new_guard_size + sz > word_bits then NullCap else
            (CNodeCap object new_guard new_guard_size sz)
      | _ \<Rightarrow> cap"

(*
 * Some caps may not be copied/minted. In this case the following function
 * returns NullCap or throws.
 *
 * PageTable and PageDirectory caps may not be copied if already mapped. This is
 * left out here and modelled by nondeterminism.
 *)
definition
  derive_cap :: "cdl_cap_ref \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap except_monad"
where
  "derive_cap slot cap \<equiv> case cap of
     UntypedCap _ _ _ \<Rightarrow> doE ensure_no_children slot; returnOk cap odE
   | ReplyCap _ _ \<Rightarrow> returnOk NullCap
   | MasterReplyCap oref \<Rightarrow> returnOk NullCap
   | IrqControlCap \<Rightarrow> returnOk NullCap
   | ZombieCap _ \<Rightarrow> returnOk NullCap
   | FrameCap dev p r sz b x \<Rightarrow> returnOk (FrameCap dev p r sz b None)
   | PageTableCap _ _ _ \<Rightarrow> throw \<sqinter> returnOk cap
   | PageDirectoryCap _ _ _ \<Rightarrow> throw \<sqinter> returnOk cap
   | _ \<Rightarrow> returnOk cap"


(* This function is here to make it available in both Tcb_D and
   PageTable_D *)

(* Modify the TCB's IpcBuffer or Registers in an arbitrary fashion. *)
definition
  corrupt_tcb_intent :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "corrupt_tcb_intent target_tcb \<equiv>
    do
      new_intent \<leftarrow> select UNIV;
      update_thread target_tcb (\<lambda>t. t\<lparr>cdl_tcb_intent := new_intent\<rparr>)
    od"

end
