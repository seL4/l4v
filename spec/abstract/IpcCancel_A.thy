(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
Functions for cancelling IPC.
*)

chapter "IPC Cancelling"


theory IpcCancel_A
imports "./$L4V_ARCH/ArchIpcCancel_A"
begin

context begin interpretation Arch .

requalify_consts
  arch_post_cap_deletion
  arch_gen_obj_refs
  arch_cap_cleanup_opt

requalify_types
  arch_gen_obj_ref

end

definition
  sched_context_bind_ntfn :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_bind_ntfn sc ntfn = do
    n \<leftarrow> get_notification ntfn;
    set_notification ntfn (n\<lparr>ntfn_sc:= Some sc\<rparr>);
    s \<leftarrow> get_sched_context sc;
    set_sched_context sc (s\<lparr>sc_ntfn:= Some ntfn\<rparr>)
  od"

definition
  sched_context_unbind_ntfn :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_unbind_ntfn sc_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    return (sc_ntfn sc) >>=
    maybeM (\<lambda>ntfn. do
      set_sched_context sc_ptr (sc\<lparr>sc_ntfn:= None\<rparr>);
      n \<leftarrow> get_notification ntfn;
      set_notification ntfn (n\<lparr>ntfn_sc:= None\<rparr>)
    od)
  od"

definition
  sched_context_maybe_unbind_ntfn :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_maybe_unbind_ntfn ntfn_ptr = do
    sc_opt \<leftarrow> liftM ntfn_sc $ get_notification ntfn_ptr;
    maybeM sched_context_unbind_ntfn sc_opt
  od"

text \<open>
  Unbind a TCB from its scheduling context. If the TCB is runnable,
  remove from the scheduler.
\<close>
definition
  sched_context_unbind_tcb :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_unbind_tcb sc_ptr = do
     sc \<leftarrow> get_sched_context sc_ptr;
     tptr \<leftarrow> assert_opt $ sc_tcb sc;
     do_extended_op $ tcb_sched_action tcb_sched_dequeue tptr;
     do_extended_op $ tcb_release_remove tptr;
     thread_set (\<lambda>tcb. tcb \<lparr> tcb_sched_context := None \<rparr>) tptr;
     cur \<leftarrow> gets $ cur_thread;
     when (tptr = cur) $ do_extended_op reschedule_required
  od"

text \<open>Donate a scheduling context.\<close>
definition
  sched_context_donate :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> unit det_ext_monad"
where
  "sched_context_donate sc_ptr tcb_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    from_opt \<leftarrow> return $ sc_tcb sc;
    when (from_opt \<noteq> None) $ sched_context_unbind_tcb sc_ptr;
    set_sched_context sc_ptr (sc\<lparr>sc_tcb := Some tcb_ptr\<rparr>);
    thread_set (\<lambda>tcb. tcb\<lparr>tcb_sched_context := Some sc_ptr\<rparr>) tcb_ptr
  od"

text \<open>Unbind a reply from the corresponding scheduling context.\<close>
definition
  reply_unbind_sc :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> unit det_ext_monad"
where
  "reply_unbind_sc sc_ptr reply_ptr = do
     sc \<leftarrow> get_sched_context sc_ptr;
     reply \<leftarrow> get_reply reply_ptr;
     set_reply reply_ptr (reply\<lparr>reply_sc:= None\<rparr>);
     set_sched_context sc_ptr (sc\<lparr>sc_replies := remove1 reply_ptr (sc_replies sc)\<rparr>)
  od"

text \<open>Unbind a reply from the corresponding TCB.\<close>
definition
  reply_unbind_caller :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> unit det_ext_monad"
where
  "reply_unbind_caller tcb_ptr reply_ptr = do
     reply \<leftarrow> get_reply reply_ptr;
     set_reply reply_ptr (reply\<lparr>reply_caller:= None\<rparr>);
     thread_set (tcb_reply_update $ K None) tcb_ptr
  od"

text \<open>Unbind all replies from a scheduling context.\<close>
definition
  sched_context_clear_replies :: "obj_ref \<Rightarrow> unit det_ext_monad"
where
  "sched_context_clear_replies sc_ptr = do
     replies \<leftarrow> liftM sc_replies $ get_sched_context sc_ptr;
     mapM_x (reply_unbind_sc sc_ptr) replies
  od"

text {* Remove a reply object from the call stack. *}
definition
  reply_remove :: "obj_ref \<Rightarrow> unit det_ext_monad"
where
  "reply_remove r = do
    reply \<leftarrow> get_reply r;
    caller \<leftarrow> assert_opt $ reply_caller reply;
    sc_ptr \<leftarrow> assert_opt $ reply_sc reply;
    replies \<leftarrow> liftM sc_replies $ get_sched_context sc_ptr;
    reply_unbind_caller caller r;
    reply_unbind_sc sc_ptr r;
    when (hd replies = r) $ sched_context_donate sc_ptr caller
  od"

text {* Push a reply object to the call stack. *}
definition
  reply_push :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> bool \<Rightarrow> unit det_ext_monad"
where
  "reply_push caller callee reply_ptr can_donate = do
    sc_opt \<leftarrow> thread_get tcb_sched_context caller;
    sc_callee \<leftarrow> thread_get tcb_sched_context callee;

    reply_caller_opt \<leftarrow> get_reply_caller reply_ptr;
    when (reply_caller_opt \<noteq> None) $ reply_remove reply_ptr;

    can_donate \<leftarrow> return (if (sc_callee = None) then can_donate else False);

    reply \<leftarrow> get_reply reply_ptr;
    assert (reply_caller reply = None);
    tcb_reply_opt \<leftarrow> thread_get tcb_reply caller;
    assert (tcb_reply_opt = None);

    reply' \<leftarrow> return $ reply\<lparr>reply_caller := Some caller\<rparr>;
    set_reply reply_ptr reply';
    thread_set (tcb_reply_update $ K (Some reply_ptr)) caller;

    when (sc_opt \<noteq> None \<and> can_donate) $ do
      sc \<leftarrow> get_sched_context (the sc_opt);
      set_sched_context (the sc_opt) (sc\<lparr>sc_replies := reply_ptr#sc_replies sc\<rparr>);
      set_reply reply_ptr (reply'\<lparr>reply_sc := sc_opt\<rparr>);
      sched_context_donate (the sc_opt) callee
    od
  od"

text {* Getting and setting endpoint queues. *}
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


text {* The endpoint a TCB is blocked on *}
definition
  ep_blocked :: "thread_state \<Rightarrow> obj_ref option"
where
  "ep_blocked ts \<equiv> case ts of
     BlockedOnReceive r _ \<Rightarrow> Some r
   | BlockedOnSend r _ \<Rightarrow> Some r
   | _ \<Rightarrow> None"

text {* The notification a TCB is blocked on *}
definition
  ntfn_blocked :: "thread_state \<Rightarrow> obj_ref option"
where
  "ntfn_blocked ts \<equiv> case ts of
    BlockedOnNotification r \<Rightarrow> Some r
  | _ \<Rightarrow> None"

text {*
  Sort a list of TCB refs by priority, otherwise keeping order stable.
  In the implementation, there will only ever be one element out of order
  or be inserted. Here, we just require a sorted result.
*}
definition
  sort_queue :: "obj_ref list \<Rightarrow> obj_ref list det_ext_monad"
where
  "sort_queue qs = do
     prios \<leftarrow> mapM (ethread_get tcb_priority) qs;
     return $ map snd $ sort_key fst (zip prios qs)
   od"

text {* Bring endpoint queue back into priority order *}
definition
  reorder_ep :: "obj_ref \<Rightarrow> unit det_ext_monad"
where
  "reorder_ep ep_ptr = do
    ep \<leftarrow> get_endpoint ep_ptr;
    qs \<leftarrow> get_ep_queue ep;
    qs' \<leftarrow> sort_queue qs;
    set_endpoint ep_ptr (update_ep_queue ep qs')
  od"

text {* Extract list of TCBs waiting on this notification *}
definition
  ntfn_queue :: "notification \<Rightarrow> obj_ref list option"
where
  "ntfn_queue ntfn \<equiv> case ntfn_obj ntfn of
     WaitingNtfn qs \<Rightarrow> Some qs
   | _ \<Rightarrow> None"

text {* Bring notification queue back into priority order *}
definition
  reorder_ntfn :: "obj_ref \<Rightarrow> unit det_ext_monad"
where
  "reorder_ntfn ntfn_ptr = do
    ntfn \<leftarrow> get_notification ntfn_ptr;
    qs \<leftarrow> assert_opt $ ntfn_queue ntfn;
    qs' \<leftarrow> sort_queue qs;
    set_notification ntfn_ptr (ntfn \<lparr> ntfn_obj := WaitingNtfn qs' \<rparr>)
  od"

text {* Set new priority for a TCB *}
definition
  set_priority :: "obj_ref \<Rightarrow> priority \<Rightarrow> unit det_ext_monad" where
  "set_priority tptr prio \<equiv> do
     tcb_sched_action tcb_sched_dequeue tptr;
     thread_set_priority tptr prio;
     ts \<leftarrow> get_thread_state tptr;
     when (runnable ts) $ do
       tcb_sched_action tcb_sched_enqueue tptr;
       cur \<leftarrow> gets cur_thread;
       when (tptr = cur) reschedule_required
     od;
     maybeM reorder_ep (ep_blocked ts);
     maybeM reorder_ntfn (ntfn_blocked ts)
   od"

definition
  possible_switch_to :: "obj_ref \<Rightarrow> bool \<Rightarrow> unit det_ext_monad" where
  "possible_switch_to target on_same_prio \<equiv> do
     sc_opt \<leftarrow> thread_get tcb_sched_context target;
     inq \<leftarrow> gets $ in_release_queue target;
     when (sc_opt \<noteq> None \<and> \<not>inq) $ do
       cur \<leftarrow> gets cur_thread;
       cur_dom \<leftarrow> gets cur_domain;
       cur_prio \<leftarrow> ethread_get tcb_priority cur;
       target_dom \<leftarrow> ethread_get tcb_domain target;
       target_prio \<leftarrow> ethread_get tcb_priority target;
       action \<leftarrow> gets scheduler_action;
       if (target_dom \<noteq> cur_dom) then tcb_sched_action tcb_sched_enqueue target
       else do
         if (target_prio > cur_prio \<or> (target_prio = cur_prio \<and> on_same_prio))
                \<and> action = resume_cur_thread then set_scheduler_action $ switch_thread target
           else tcb_sched_action tcb_sched_enqueue target;
         case action of switch_thread _ \<Rightarrow> reschedule_required | _ \<Rightarrow> return ()
       od
     od
   od"

definition
  attempt_switch_to :: "obj_ref \<Rightarrow> unit det_ext_monad" where
  "attempt_switch_to target \<equiv> possible_switch_to target True"

definition
  switch_if_required_to :: "obj_ref \<Rightarrow> unit det_ext_monad" where
  "switch_if_required_to target \<equiv> possible_switch_to target False"

text {* Cancel all message operations on threads currently queued within this
synchronous message endpoint. Threads so queued are placed in the Restart state.
Once scheduled they will reattempt the operation that previously caused them
to be queued here. *}
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

text {* The badge stored by thread waiting on a message send operation. *}
primrec (nonexhaustive)
  blocking_ipc_badge :: "thread_state \<Rightarrow> badge"
where
  "blocking_ipc_badge (BlockedOnSend t payload) = sender_badge payload"

text {* Cancel all message send operations on threads queued in this endpoint
and using a particular badge. *}
definition
  cancel_badged_sends :: "obj_ref \<Rightarrow> badge \<Rightarrow> unit det_ext_monad"
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
                  switch_if_required_to t;
                  return False
                od
                else return True
            od);
            ep' \<leftarrow> return (case queue' of
                           [] \<Rightarrow> IdleEP
                         | _ \<Rightarrow> SendEP queue');
            set_endpoint epptr ep';
            do_extended_op (reschedule_required)
        od
  od"

text {* Cancel all message operations on threads queued in a notification
endpoint. *}

text {* Notification accessors. *}
abbreviation 
  ntfn_set_bound_tcb :: "notification \<Rightarrow> obj_ref option \<Rightarrow> notification"
where
  "ntfn_set_bound_tcb ntfn t \<equiv> ntfn \<lparr> ntfn_bound_tcb := t \<rparr>"

abbreviation
  ntfn_set_obj :: "notification \<Rightarrow> ntfn \<Rightarrow> notification"
where
  "ntfn_set_obj ntfn a \<equiv> ntfn \<lparr> ntfn_obj := a \<rparr>"


text {* Remove the binding between a notification and a TCB. *}
abbreviation
  do_unbind_notification :: "obj_ref \<Rightarrow> notification \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "do_unbind_notification ntfnptr ntfn tcbptr \<equiv> do
      ntfn' \<leftarrow> return $ ntfn_set_bound_tcb ntfn None;
      set_notification ntfnptr ntfn';
      set_bound_notification tcbptr None
    od"


text {* Remove bound notification from a TCB in bound state. *}
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

text {* Remove bound notification from a TCB if such notification exists. *}
definition
  unbind_maybe_notification :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "unbind_maybe_notification ntfnptr \<equiv> do
     ntfn \<leftarrow> get_notification ntfnptr;
     (case ntfn_bound_tcb ntfn of
       Some t \<Rightarrow> do_unbind_notification ntfnptr ntfn t
     | None \<Rightarrow> return ())
   od"



text {* Cancel all message operations on threads queued in a notification endpoint. *}

definition
  cancel_all_signals :: "obj_ref \<Rightarrow> unit det_ext_monad"
where
  "cancel_all_signals ntfnptr \<equiv> do
     ntfn \<leftarrow> get_notification ntfnptr;
     case ntfn_obj ntfn of WaitingNtfn queue \<Rightarrow> do
                      _ \<leftarrow> set_notification ntfnptr $ ntfn_set_obj ntfn IdleNtfn;
                      mapM_x (\<lambda>t. do set_thread_state t Restart;
                                     switch_if_required_to t od) queue;
                      do_extended_op (reschedule_required)
                     od
               | _ \<Rightarrow> return ()
   od"

text {* The endpoint pointer stored by a thread waiting for a message to be
transferred in either direction. *}
definition
  get_blocking_object :: "thread_state \<Rightarrow> (obj_ref,'z::state_ext) s_monad"
where
 "get_blocking_object state \<equiv> assert_opt $ ep_blocked state"


text {* Cancel whatever IPC operation a thread is engaged in. *}
definition
  blocked_cancel_ipc :: "thread_state \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow> unit det_ext_monad"
where
  "blocked_cancel_ipc state tptr reply_opt \<equiv> do
     epptr \<leftarrow> get_blocking_object state;
     ep \<leftarrow> get_endpoint epptr;
     queue \<leftarrow> get_ep_queue ep;
     queue' \<leftarrow> return $ remove1 tptr queue;
     ep' \<leftarrow> return (case queue' of [] \<Rightarrow> IdleEP
                                |  _ \<Rightarrow> update_ep_queue ep queue');
     set_endpoint epptr ep';
     maybeM reply_remove reply_opt;
     set_thread_state tptr Inactive
   od"

text \<open> Unbind TCB, if there is one bound. \<close>
definition
  sched_context_unbind_all_tcbs :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_unbind_all_tcbs sc_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    when (sc_tcb sc \<noteq> None) $ sched_context_unbind_tcb sc_ptr
  od"

text {* Finalise a capability if the capability is known to be of the kind
which can be finalised immediately. This is a simplified version of the
@{text finalise_cap} operation. *}
fun
  fast_finalise :: "cap \<Rightarrow> bool \<Rightarrow> unit det_ext_monad"
where
  "fast_finalise NullCap                 final = return ()"
| "fast_finalise (ReplyCap r)            final =
      (when final $ reply_remove r)"
| "fast_finalise (EndpointCap r b R)     final =
      (when final $ cancel_all_ipc r)"
| "fast_finalise (NotificationCap r b R) final =
      (when final $ do
          sched_context_maybe_unbind_ntfn r;
          unbind_maybe_notification r;
          cancel_all_signals r
       od)"
| "fast_finalise (SchedContextCap sc b)    final =
      (when final $ do
          sched_context_unbind_all_tcbs sc;
          sched_context_unbind_ntfn sc;
          sched_context_clear_replies sc
      od)"
| "fast_finalise _ _ = fail"

text {* The optional IRQ stored in a capability, presented either as an optional
value or a set. *}
definition
  cap_irq_opt :: "cap \<Rightarrow> irq option" where
 "cap_irq_opt cap \<equiv> case cap of IRQHandlerCap irq \<Rightarrow> Some irq | _ \<Rightarrow> None"

definition
  cap_irqs :: "cap \<Rightarrow> irq set" where
 "cap_irqs cap \<equiv> set_option (cap_irq_opt cap)"

text {* A generic reference to an object. Used for the purposes of finalisation,
where we want to be able to compare caps to decide if they refer to the "same object",
which can be determined in several ways *}
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


text {* Detect whether a capability is the final capability to a given object
remaining in the system. Finalisation actions need to be taken when the final
capability to the object is deleted. *}
definition
  is_final_cap' :: "cap \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
 "is_final_cap' cap s \<equiv>
    \<exists>cref. {cref. \<exists>cap'. fst (get_cap cref s) = {(cap', s)}
                       \<and> (gen_obj_refs cap \<inter> gen_obj_refs cap' \<noteq> {})}
         = {cref}"

definition
  is_final_cap :: "cap \<Rightarrow> (bool,'z::state_ext) s_monad" where
  "is_final_cap cap \<equiv> gets (is_final_cap' cap)"

text {* Actions to be taken after an IRQ handler capability is deleted. *}
definition
  deleted_irq_handler :: "irq \<Rightarrow> (unit,'z::state_ext) s_monad"
where
 "deleted_irq_handler irq \<equiv> set_irq_state IRQInactive irq"

text {* Actions to be taken after a cap is deleted *}
definition
  post_cap_deletion :: "cap \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "post_cap_deletion cap \<equiv> case cap of
       IRQHandlerCap irq \<Rightarrow> deleted_irq_handler irq
     | ArchObjectCap acap \<Rightarrow> arch_post_cap_deletion acap
     | _ \<Rightarrow> return ()"

text {* Empty a capability slot assuming that the capability in it has been
finalised already. *}

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

text {* Delete a capability with the assumption that the fast finalisation
process will be sufficient. *}
definition
  cap_delete_one :: "cslot_ptr \<Rightarrow> unit det_ext_monad" where
 "cap_delete_one slot \<equiv> do
    cap \<leftarrow> get_cap slot;
    unless (cap = NullCap) $ do
      final \<leftarrow> is_final_cap cap;
      fast_finalise cap final;
      empty_slot slot NullCap
    od
  od"

text {* Cancel the message receive operation of a thread waiting for a Reply
capability it has issued to be invoked. *}
definition
  reply_cancel_ipc :: "obj_ref \<Rightarrow> unit det_ext_monad"
where
 "reply_cancel_ipc tptr \<equiv> do
    thread_set (\<lambda>tcb. tcb \<lparr> tcb_fault := None \<rparr>) tptr;
    reply_opt \<leftarrow> thread_get tcb_reply tptr;
    maybeM reply_remove reply_opt
  od"

text {* Cancel the message receive operation of a thread queued in an
notification object. *}
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

text {* Cancel any message operations a given thread is waiting on. *}
definition
  cancel_ipc :: "obj_ref \<Rightarrow> unit det_ext_monad"
where
  "cancel_ipc tptr \<equiv> do
     state \<leftarrow> get_thread_state tptr;
     case state
       of
          BlockedOnSend x y \<Rightarrow> blocked_cancel_ipc state tptr None
        | BlockedOnReceive x reply \<Rightarrow> blocked_cancel_ipc state tptr reply
        | BlockedOnNotification event \<Rightarrow> cancel_signal tptr event
        | BlockedOnReply \<Rightarrow> reply_cancel_ipc tptr
        | _ \<Rightarrow> return ()
   od"

text {* Suspend a thread, cancelling any pending operations and preventing it
from further execution by setting it to the Inactive state. *}
definition
  suspend :: "obj_ref \<Rightarrow> unit det_ext_monad"
where
  "suspend thread \<equiv> do
     cancel_ipc thread;
     set_thread_state thread Inactive;
     do_extended_op (tcb_sched_action (tcb_sched_dequeue) thread)
   od"

end
