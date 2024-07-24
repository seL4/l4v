(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Functions for cancelling IPC.
*)

chapter "IPC Cancelling"

theory IpcCancel_A
imports ArchIpcCancel_A
begin

arch_requalify_consts (A)
  arch_post_cap_deletion
  arch_gen_obj_refs
  arch_cap_cleanup_opt

arch_requalify_consts
  faultRegister
  nextInstructionRegister

arch_requalify_types (A)
  arch_gen_obj_ref

text \<open>Getting and setting endpoint queues.\<close>
definition
  get_ep_queue :: "endpoint \<Rightarrow> (obj_ref list,'z::state_ext) s_monad"
where
 "get_ep_queue ep \<equiv> case ep of SendEP q \<Rightarrow> return q
                              | RecvEP q \<Rightarrow> return q
                              | _ \<Rightarrow> fail"

primrec (nonexhaustive)
  update_ep_queue :: "endpoint \<Rightarrow> obj_ref list \<Rightarrow> endpoint"
where
  "update_ep_queue (RecvEP q) q' = RecvEP q'"
| "update_ep_queue (SendEP q) q' = SendEP q'"


text \<open>Cancel all message operations on threads currently queued within this
synchronous message endpoint. Threads so queued are placed in the Restart state.
Once scheduled they will reattempt the operation that previously caused them
to be queued here.\<close>
definition
  cancel_all_ipc :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "cancel_all_ipc epptr \<equiv> do
     ep \<leftarrow> get_endpoint epptr;
     case ep of IdleEP \<Rightarrow> return ()
               | _ \<Rightarrow> do
                        queue \<leftarrow> get_ep_queue ep;
                        set_endpoint epptr IdleEP;
                        mapM_x (\<lambda>t. do set_thread_state t Restart;
                                       do_extended_op (tcb_sched_action (tcb_sched_enqueue) t) od) $ queue;
                        do_extended_op (reschedule_required)
                     od
   od"

text \<open>The badge stored by thread waiting on a message send operation.\<close>
primrec (nonexhaustive)
  blocking_ipc_badge :: "thread_state \<Rightarrow> badge"
where
  "blocking_ipc_badge (BlockedOnSend t payload) = sender_badge payload"

text \<open>Cancel all message send operations on threads queued in this endpoint
and using a particular badge.\<close>
definition
  cancel_badged_sends :: "obj_ref \<Rightarrow> badge \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "cancel_badged_sends epptr badge \<equiv> do
    ep \<leftarrow> get_endpoint epptr;
    case ep of
          IdleEP \<Rightarrow> return ()
        | RecvEP _ \<Rightarrow>  return ()
        | SendEP queue \<Rightarrow>  do
            set_endpoint epptr IdleEP;
            queue' \<leftarrow> (swp filterM queue) (\<lambda> t. do
                st \<leftarrow> get_thread_state t;
                if blocking_ipc_badge st = badge then do
                  set_thread_state t Restart;
                  do_extended_op (tcb_sched_action (tcb_sched_enqueue) t);
                  return False od
                else return True
            od);
            ep' \<leftarrow> return (case queue' of
                           [] \<Rightarrow> IdleEP
                         | _ \<Rightarrow> SendEP queue');
            set_endpoint epptr ep';
            do_extended_op (reschedule_required)
        od
  od"

text \<open>Cancel all message operations on threads queued in a notification
endpoint.\<close>

abbreviation
  do_unbind_notification :: "obj_ref \<Rightarrow> notification \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "do_unbind_notification ntfnptr ntfn tcbptr \<equiv> do
      ntfn' \<leftarrow> return $ ntfn_set_bound_tcb ntfn None;
      set_notification ntfnptr ntfn';
      set_bound_notification tcbptr None
    od"

definition
  unbind_notification :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "unbind_notification tcb \<equiv> do
     ntfnptr \<leftarrow> get_bound_notification tcb;
     case ntfnptr of
         Some ntfnptr' \<Rightarrow> do
             ntfn \<leftarrow> get_notification ntfnptr';
             do_unbind_notification ntfnptr' ntfn tcb
          od
       | None \<Rightarrow> return ()
   od"

definition
  unbind_maybe_notification :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "unbind_maybe_notification ntfnptr \<equiv> do
     ntfn \<leftarrow> get_notification ntfnptr;
     (case ntfn_bound_tcb ntfn of
       Some t \<Rightarrow> do_unbind_notification ntfnptr ntfn t
     | None \<Rightarrow> return ())
   od"

definition
  cancel_all_signals :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "cancel_all_signals ntfnptr \<equiv> do
     ntfn \<leftarrow> get_notification ntfnptr;
     case ntfn_obj ntfn of WaitingNtfn queue \<Rightarrow> do
                      _ \<leftarrow> set_notification ntfnptr $ ntfn_set_obj ntfn IdleNtfn;
                      mapM_x (\<lambda>t. do set_thread_state t Restart;
                                     do_extended_op (tcb_sched_action tcb_sched_enqueue t) od) queue;
                      do_extended_op (reschedule_required)
                     od
               | _ \<Rightarrow> return ()
   od"

text \<open>The endpoint pointer stored by a thread waiting for a message to be
transferred in either direction.\<close>
definition
  get_blocking_object :: "thread_state \<Rightarrow> (obj_ref,'z::state_ext) s_monad"
where
 "get_blocking_object state \<equiv>
       case state of BlockedOnReceive epptr x \<Rightarrow> return epptr
                    | BlockedOnSend epptr x \<Rightarrow> return epptr
                    | _ \<Rightarrow> fail"


text \<open>Cancel whatever IPC operation a thread is engaged in.\<close>
definition
  blocked_cancel_ipc :: "thread_state \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "blocked_cancel_ipc state tptr \<equiv> do
     epptr \<leftarrow> get_blocking_object state;
     ep \<leftarrow> get_endpoint epptr;
     queue \<leftarrow> get_ep_queue ep;
     queue' \<leftarrow> return $ remove1 tptr queue;
     ep' \<leftarrow> return (case queue' of [] \<Rightarrow> IdleEP
                                |  _ \<Rightarrow> update_ep_queue ep queue');
     set_endpoint epptr ep';
     set_thread_state tptr Inactive
   od"

text \<open>Finalise a capability if the capability is known to be of the kind
which can be finalised immediately. This is a simplified version of the
@{text finalise_cap} operation.\<close>
fun
  fast_finalise :: "cap \<Rightarrow> bool \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "fast_finalise NullCap                  final = return ()"
| "fast_finalise (ReplyCap r m R)         final = return ()"
| "fast_finalise (EndpointCap r b R)      final =
      (when final $ cancel_all_ipc r)"
| "fast_finalise (NotificationCap r b R) final =
      (when final $ do
          unbind_maybe_notification r;
          cancel_all_signals r
       od)"
| "fast_finalise (CNodeCap r bits g)      final = fail"
| "fast_finalise (ThreadCap r)            final = fail"
| "fast_finalise DomainCap                final = fail"
| "fast_finalise (Zombie r b n)           final = fail"
| "fast_finalise IRQControlCap            final = fail"
| "fast_finalise (IRQHandlerCap irq)      final = fail"
| "fast_finalise (UntypedCap dev r n f)       final = fail"
| "fast_finalise (ArchObjectCap a)        final = fail"

text \<open>The optional IRQ stored in a capability, presented either as an optional
value or a set.\<close>
definition
  cap_irq_opt :: "cap \<Rightarrow> irq option" where
 "cap_irq_opt cap \<equiv> case cap of IRQHandlerCap irq \<Rightarrow> Some irq | _ \<Rightarrow> None"

definition
  cap_irqs :: "cap \<Rightarrow> irq set" where
 "cap_irqs cap \<equiv> set_option (cap_irq_opt cap)"

text \<open>A generic reference to an object. Used for the purposes of finalisation,
where we want to be able to compare caps to decide if they refer to the "same object",
which can be determined in several ways\<close>
datatype gen_obj_ref =
    ObjRef obj_ref
  | IRQRef irq
  | ArchRef arch_gen_obj_ref

definition
  arch_cap_set_map :: "(arch_cap \<Rightarrow> 'a set) \<Rightarrow> cap \<Rightarrow> 'a set"
where
  "arch_cap_set_map f cap \<equiv> case cap of
       ArchObjectCap acap \<Rightarrow> f acap
     | _ \<Rightarrow> {}"

abbreviation
  arch_gen_refs :: "cap \<Rightarrow> arch_gen_obj_ref set"
where
  "arch_gen_refs \<equiv> arch_cap_set_map arch_gen_obj_refs"

definition
  gen_obj_refs :: "cap \<Rightarrow> gen_obj_ref set"
where
  "gen_obj_refs c \<equiv> ObjRef ` (obj_refs c)
                      \<union> IRQRef ` (cap_irqs c)
                      \<union> ArchRef ` (arch_gen_refs c)"

definition
  cap_cleanup_opt :: "cap \<Rightarrow> cap"
where
  "cap_cleanup_opt c \<equiv> case c of
      IRQHandlerCap _ \<Rightarrow> c
    | ArchObjectCap acap \<Rightarrow> arch_cap_cleanup_opt acap
    | _ \<Rightarrow> NullCap"


text \<open>Detect whether a capability is the final capability to a given object
remaining in the system. Finalisation actions need to be taken when the final
capability to the object is deleted.\<close>
definition
  is_final_cap' :: "cap \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
 "is_final_cap' cap s \<equiv>
    \<exists>cref. {cref. \<exists>cap'. fst (get_cap cref s) = {(cap', s)}
                       \<and> (gen_obj_refs cap \<inter> gen_obj_refs cap' \<noteq> {})}
         = {cref}"

definition
  is_final_cap :: "cap \<Rightarrow> (bool,'z::state_ext) s_monad" where
  "is_final_cap cap \<equiv> gets (is_final_cap' cap)"

text \<open>Actions to be taken after an IRQ handler capability is deleted.\<close>
definition
  deleted_irq_handler :: "irq \<Rightarrow> (unit,'z::state_ext) s_monad"
where
 "deleted_irq_handler irq \<equiv> set_irq_state IRQInactive irq"

text \<open>Actions to be taken after a cap is deleted\<close>
definition
  post_cap_deletion :: "cap \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "post_cap_deletion cap \<equiv> case cap of
       IRQHandlerCap irq \<Rightarrow> deleted_irq_handler irq
     | ArchObjectCap acap \<Rightarrow> arch_post_cap_deletion acap
     | _ \<Rightarrow> return ()"

text \<open>Empty a capability slot assuming that the capability in it has been
finalised already.\<close>

definition
  empty_slot :: "cslot_ptr \<Rightarrow> cap \<Rightarrow> (unit,'z::state_ext) s_monad"
where
 "empty_slot slot cleanup_info \<equiv> do
      cap \<leftarrow> get_cap slot;
      if cap = NullCap then
        return ()
      else do
        slot_p \<leftarrow> gets (\<lambda>s. cdt s slot);
        cdt \<leftarrow> gets cdt;
        parent \<leftarrow> return $ cdt slot;
        set_cdt ((\<lambda>p. if cdt p = Some slot
                     then parent
                     else cdt p) (slot := None));
        do_extended_op (empty_slot_ext slot slot_p);
        set_original slot False;
        set_cap NullCap slot;

        post_cap_deletion cleanup_info
      od
  od"

text \<open>Delete a capability with the assumption that the fast finalisation
process will be sufficient.\<close>
definition
  cap_delete_one :: "cslot_ptr \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "cap_delete_one slot \<equiv> do
    cap \<leftarrow> get_cap slot;
    unless (cap = NullCap) $ do
      final \<leftarrow> is_final_cap cap;
      fast_finalise cap final;
      empty_slot slot NullCap
    od
  od"

text \<open>Cancel the message receive operation of a thread waiting for a Reply
capability it has issued to be invoked.\<close>
definition
  reply_cancel_ipc :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
 "reply_cancel_ipc tptr \<equiv> do
    thread_set (\<lambda>tcb. tcb \<lparr> tcb_fault := None \<rparr>) tptr;
    cap \<leftarrow> get_cap (tptr, tcb_cnode_index 2);
    descs \<leftarrow> gets (descendants_of (tptr, tcb_cnode_index 2) o cdt);
    when (descs \<noteq> {}) $ do
      assert (\<exists>cslot_ptr. descs = {cslot_ptr});
      cslot_ptr \<leftarrow> select descs;
      cap_delete_one cslot_ptr
    od
  od"

text \<open>Cancel the message receive operation of a thread queued in an
notification object.\<close>
definition
  cancel_signal :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "cancel_signal threadptr ntfnptr \<equiv> do
     ntfn \<leftarrow> get_notification ntfnptr;
     queue \<leftarrow> (case ntfn_obj ntfn of WaitingNtfn queue \<Rightarrow> return queue
                        | _ \<Rightarrow> fail);
     queue' \<leftarrow> return $ remove1 threadptr queue;
     newNTFN \<leftarrow> return $ ntfn_set_obj ntfn (case queue' of [] \<Rightarrow> IdleNtfn
                                                      | _  \<Rightarrow> WaitingNtfn queue');
     set_notification ntfnptr newNTFN;
     set_thread_state threadptr Inactive
   od"

text \<open>Cancel any message operations a given thread is waiting on.\<close>
definition
  cancel_ipc :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "cancel_ipc tptr \<equiv> do
     state \<leftarrow> get_thread_state tptr;
     case state
       of
          BlockedOnSend x y \<Rightarrow> blocked_cancel_ipc state tptr
        | BlockedOnReceive x y \<Rightarrow> blocked_cancel_ipc state tptr
        | BlockedOnNotification event \<Rightarrow> cancel_signal tptr event
        | BlockedOnReply \<Rightarrow> reply_cancel_ipc tptr
        | _ \<Rightarrow> return ()
   od"

text \<open>Currently, @{text update_restart_pc} can be defined generically up to
the actual register numbers.\<close>
definition
  update_restart_pc :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "update_restart_pc thread_ptr =
        as_user thread_ptr (getRegister nextInstructionRegister
                            >>= setRegister faultRegister)"

text \<open>Suspend a thread, cancelling any pending operations and preventing it
from further execution by setting it to the Inactive state.\<close>
definition
  suspend :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "suspend thread \<equiv> do
     cancel_ipc thread;
     state \<leftarrow> get_thread_state thread;
     (if state = Running then update_restart_pc thread else return ());
     set_thread_state thread Inactive;
     do_extended_op (tcb_sched_action (tcb_sched_dequeue) thread)
   od"

end
