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

text {* Scheduling context accessors. *}
definition
  sched_context_bind_ntfn :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_bind_ntfn sc ntfn = do
    set_ntfn_obj_ref ntfn_sc_update ntfn (Some sc);
    set_sc_obj_ref sc_ntfn_update sc (Some ntfn)
  od"

text {* Remove the binding between a notification and a scheduling context.
        This is avoids double reads when calling sched_context_unbind_ntfn
        from sched_context_maybe_unbind_ntfn (which has infoflow repercussions) *}
abbreviation
  do_unbind_ntfn_sc :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "do_unbind_ntfn_sc ntfnptr scptr \<equiv> do
      set_ntfn_obj_ref ntfn_sc_update ntfnptr None;
      set_sc_obj_ref sc_ntfn_update scptr None
    od"

definition
  sched_context_unbind_ntfn :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_unbind_ntfn sc_ptr = do
    ntfn_opt \<leftarrow> get_sc_obj_ref sc_ntfn sc_ptr;
    maybeM (\<lambda>ntfn. do_unbind_ntfn_sc ntfn sc_ptr) ntfn_opt
  od"

definition
  sched_context_maybe_unbind_ntfn :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_maybe_unbind_ntfn ntfn_ptr = do
    sc_opt \<leftarrow> get_ntfn_obj_ref ntfn_sc ntfn_ptr;
    maybeM (\<lambda>sc. do_unbind_ntfn_sc ntfn_ptr sc) sc_opt
  od"

definition
  sched_context_unbind_reply :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_unbind_reply sc_ptr = do
    replies \<leftarrow> liftM sc_replies $ get_sched_context sc_ptr;
    mapM_x (\<lambda>r. set_reply_obj_ref reply_sc_update r None) replies;
    set_sc_obj_ref sc_replies_update sc_ptr []
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
     cur \<leftarrow> gets $ cur_thread;
     when (tptr = cur) $ reschedule_required;
     tcb_sched_action tcb_sched_dequeue tptr;
     tcb_release_remove tptr;
     set_tcb_obj_ref tcb_sched_context_update tptr None;
     set_sc_obj_ref sc_tcb_update sc_ptr None
  od"

text \<open>Donate a scheduling context.\<close>

definition
  test_reschedule :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "test_reschedule from_tptr = do
    cur \<leftarrow> gets $ cur_thread;
    action \<leftarrow> gets scheduler_action;
    flag \<leftarrow> return (case action of switch_thread p \<Rightarrow> from_tptr = p | _ \<Rightarrow> False);
    when (from_tptr = cur \<or> flag) $ reschedule_required
  od"

definition
  sched_context_donate :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_donate sc_ptr tcb_ptr = do
    from_opt \<leftarrow> get_sc_obj_ref sc_tcb sc_ptr;
    when (from_opt \<noteq> None) $ do
      from_tptr \<leftarrow> assert_opt $ from_opt;
      tcb_sched_action tcb_sched_dequeue from_tptr;
      tcb_release_remove from_tptr;
      set_tcb_obj_ref tcb_sched_context_update from_tptr None;
      test_reschedule from_tptr
    od;
    set_sc_obj_ref sc_tcb_update sc_ptr (Some tcb_ptr);
    set_tcb_obj_ref tcb_sched_context_update tcb_ptr (Some sc_ptr)
  od"

text \<open>Unbind a reply from the corresponding scheduling context.\<close>
definition
  reply_unlink_sc :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "reply_unlink_sc sc_ptr reply_ptr = do
     sc_replies \<leftarrow> liftM sc_replies $ get_sched_context sc_ptr;
     reply \<leftarrow> get_reply reply_ptr;
     assert (reply_sc reply = Some sc_ptr);
     set_reply reply_ptr (reply_sc_update (K None) reply);
     set_sc_obj_ref sc_replies_update sc_ptr (remove1 reply_ptr sc_replies)
  od"

text \<open>Unbind a reply from the corresponding TCB.\<close>
definition
  reply_unbind_caller :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where (* called from reply_remove; in BlockedOnReply *)
  "reply_unbind_caller tcb_ptr reply_ptr = do
     reply \<leftarrow> get_reply reply_ptr;
     set_reply reply_ptr (reply\<lparr>reply_tcb:= None\<rparr>);
     set_thread_state tcb_ptr (BlockedOnReply None) (* does this make sense? *)
  od"

definition reply_unlink_tcb :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "reply_unlink_tcb r = do
     reply \<leftarrow> get_reply r;
     tptr \<leftarrow> assert_opt $ reply_tcb reply;
     ts \<leftarrow> get_thread_state tptr;
     assert (ts = BlockedOnReply (Some r) \<or> (\<exists>ep. ts = BlockedOnReceive ep (Some r)));
     set_reply r (reply_tcb_update (K None) reply);
     set_thread_state tptr Inactive
   od"

text \<open>Unbind all replies from a scheduling context.\<close>
definition
  sched_context_clear_replies :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_clear_replies sc_ptr = do
     replies \<leftarrow> liftM sc_replies $ get_sched_context sc_ptr;
     mapM_x (reply_unlink_sc sc_ptr) replies
  od"

text {* Remove a reply object from the call stack. *}
definition
  reply_remove :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where (* reply_tcb must be in BlockedOnReply *)
  "reply_remove r = do

    reply \<leftarrow> get_reply r;
    caller \<leftarrow> assert_opt $ reply_tcb reply;
    r_sc_opt \<leftarrow> return $ reply_sc reply;
    case r_sc_opt of None \<Rightarrow> return ()
      | Some sc_ptr \<Rightarrow> do
         replies \<leftarrow> liftM sc_replies $ get_sched_context sc_ptr;
         caller_sc \<leftarrow> get_tcb_obj_ref tcb_sched_context caller;
         reply_unlink_sc sc_ptr r;
         when (hd replies = r \<and> caller_sc = None) $ sched_context_donate sc_ptr caller
      od;
    reply_unlink_tcb r  (* FIXME check the c code ! *)
   od" (* the r.caller is in Inactive on return *)

text {* Remove a specific tcb, and the reply it is blocking on, from the call stack. *}
definition
  reply_remove_tcb :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where (* tptr must be in BlockedOnReply *)
  "reply_remove_tcb tptr = do
    ts \<leftarrow> get_thread_state tptr;
    case ts of
      BlockedOnReply r \<Rightarrow> do
        rptr \<leftarrow> assert_opt r;
        reply_remove rptr
      od
    | _ \<Rightarrow> fail
  od" (* the r.caller is in Inactive on return *)

definition
  unbind_from_reply :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where (* called from finalise_cap *)
  "unbind_from_reply tptr \<equiv> do
    st \<leftarrow> get_thread_state tptr;
    case st of BlockedOnReceive _ r \<Rightarrow>
              when (r \<noteq> None) $ do
                   reply \<leftarrow> get_reply (the r);
                   set_reply (the r) (reply\<lparr>reply_tcb := None\<rparr>)
                 od
            | BlockedOnReply r \<Rightarrow> maybeM reply_remove r
            | _ \<Rightarrow> return ()
  od" (* set_thread_state? *)
(*
definition
  reply_clear_tcb :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "reply_clear_tcb rptr \<equiv> do
    reply \<leftarrow> get_reply rptr;
    tptr \<leftarrow> assert_opt $ (reply_tcb reply);
    st \<leftarrow> get_thread_state tptr;
    case st of BlockedOnReceive x r \<Rightarrow> maybeM reply_unlink_tcb r
          | BlockedOnReply r \<Rightarrow> maybeM reply_remove r
          | _ \<Rightarrow> fail
  od"
*)
definition
  unbind_reply_in_ts :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "unbind_reply_in_ts tptr \<equiv> do
      st \<leftarrow> get_thread_state tptr;
      case st of BlockedOnReceive x r \<Rightarrow>
            set_thread_state tptr (BlockedOnReceive x None)
            | BlockedOnReply r \<Rightarrow>
            set_thread_state tptr (BlockedOnReply None)
            | _ \<Rightarrow> return ()
  od"

definition
  no_reply_in_ts :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "no_reply_in_ts tptr \<equiv> do
      st \<leftarrow> get_thread_state tptr;
      case st of BlockedOnReceive x r \<Rightarrow> return (r = None)
            | BlockedOnReply r \<Rightarrow> return (r = None)
            | _ \<Rightarrow> return True
  od"

text {* Push a reply object to the call stack. *}
definition
  reply_push :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> bool \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "reply_push caller callee reply_ptr can_donate = do
    sc_caller \<leftarrow> get_tcb_obj_ref tcb_sched_context caller;

    reply_tcb_opt \<leftarrow> get_reply_tcb reply_ptr; (* this is supposed to be None *)
    assert (reply_tcb_opt = None);

    sc_callee \<leftarrow> get_tcb_obj_ref tcb_sched_context callee;
    can_donate \<leftarrow> return (if (sc_callee = None) then can_donate else False);

    ts_reply \<leftarrow> no_reply_in_ts caller;
    assert (ts_reply);
    unbind_reply_in_ts callee;

    (* link reply and tcb *)
    set_reply_obj_ref reply_tcb_update reply_ptr (Some caller);
    set_thread_state caller (BlockedOnReply (Some reply_ptr));

    when (sc_caller \<noteq> None \<and> can_donate) $ do
      sc_callee \<leftarrow> get_tcb_obj_ref tcb_sched_context callee;
      assert (sc_callee = None);
      sc_replies \<leftarrow> liftM sc_replies $ get_sched_context (the sc_caller); (* maybe define a function to add a reply to the queue? *)
      case sc_replies of
          [] \<Rightarrow> assert True
        | (r#_) \<Rightarrow> do reply \<leftarrow> get_reply r; assert (reply_sc reply = sc_caller) od;
      set_sc_obj_ref sc_replies_update (the sc_caller) (reply_ptr#sc_replies);
      set_reply_obj_ref reply_sc_update reply_ptr sc_caller;
      sched_context_donate (the sc_caller) callee
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
  sort_queue :: "obj_ref list \<Rightarrow> (obj_ref list, 'z::state_ext) s_monad"
where
  "sort_queue qs = do
     prios \<leftarrow> mapM (thread_get tcb_priority) qs;
     return $ map snd $ sort_key (\<lambda>x.255 - (fst x)) (zip prios qs) (* 0 \<le> priority < 256 *)
   od"

text {* Bring endpoint queue back into priority order *}
definition
  reorder_ep :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
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
  reorder_ntfn :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "reorder_ntfn ntfn_ptr = do
    ntfn \<leftarrow> get_notification ntfn_ptr;
    qs \<leftarrow> assert_opt $ ntfn_queue ntfn;
    qs' \<leftarrow> sort_queue qs;
    set_notification ntfn_ptr (ntfn \<lparr> ntfn_obj := WaitingNtfn qs' \<rparr>)
  od"

text {* Set new priority for a TCB *}
definition
  set_priority :: "obj_ref \<Rightarrow> priority \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "set_priority tptr prio \<equiv> do
     ts \<leftarrow> get_thread_state tptr;
     in_release_q \<leftarrow> gets $ in_release_queue tptr;
     sched \<leftarrow> is_schedulable tptr in_release_q;
     tcb_sched_action tcb_sched_dequeue tptr;
     thread_set_priority tptr prio;
       when sched $ do
         tcb_sched_action tcb_sched_enqueue tptr; (* schedulable & dequeued *)
         cur \<leftarrow> gets cur_thread;
         when (tptr = cur) $ reschedule_required
     od;
     maybeM (reorder_ep) (ep_blocked ts);
     maybeM (reorder_ntfn) (ntfn_blocked ts)
   od"

definition
  possible_switch_to :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "possible_switch_to target \<equiv> do
     sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context target;
     inq \<leftarrow> gets $ in_release_queue target;
     when (sc_opt \<noteq> None \<and> \<not>inq) $ do
     cur_dom \<leftarrow> gets cur_domain;
     target_dom \<leftarrow> thread_get tcb_domain target;
     action \<leftarrow> gets scheduler_action;
     (* not in release queue & active_sc *)
     if (target_dom \<noteq> cur_dom) then
       tcb_sched_action tcb_sched_enqueue target (* not in cur_domain *)
     else if (action \<noteq> resume_cur_thread) then
       do
         reschedule_required;
         tcb_sched_action tcb_sched_enqueue target
       od
     else
       set_scheduler_action $ switch_thread target
   od
   od"

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
         mapM_x (\<lambda>t.
           do st \<leftarrow> get_thread_state t;
              reply_opt \<leftarrow> case st of BlockedOnReceive _ r_opt \<Rightarrow> return r_opt
                                    | _ \<Rightarrow> return None;
              when (reply_opt \<noteq> None) $
                   reply_unlink_tcb (the reply_opt);
              set_thread_state t Restart;
              possible_switch_to t
            od) $ queue;
         reschedule_required
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
  cancel_badged_sends :: "obj_ref \<Rightarrow> badge \<Rightarrow> (unit, 'z::state_ext) s_monad"
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
                  possible_switch_to t;
                  return False
                od
                else return True
            od);
            ep' \<leftarrow> return (case queue' of
                           [] \<Rightarrow> IdleEP
                         | _ \<Rightarrow> SendEP queue');
            set_endpoint epptr ep';
            reschedule_required
        od
  od"

text {* Remove the binding between a notification and a TCB. This is avoids double reads
        when calling unbind_notification from unbind_maybe_notification (which has infoflow
        repercussions *}
abbreviation
  do_unbind_notification :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "do_unbind_notification ntfnptr tcbptr \<equiv> do
      set_ntfn_obj_ref ntfn_bound_tcb_update ntfnptr None;
      set_tcb_obj_ref tcb_bound_notification_update tcbptr None
    od"


text {* Remove bound notification from a TCB in bound state. *}
definition
  unbind_notification :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "unbind_notification tcb \<equiv> do
     ntfnptr \<leftarrow> get_tcb_obj_ref tcb_bound_notification tcb;
     maybeM (\<lambda>nptr. do_unbind_notification nptr tcb) ntfnptr
   od"

text {* Remove bound notification from a TCB if such notification exists. *}
definition
  unbind_maybe_notification :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "unbind_maybe_notification ntfnptr \<equiv> do
     tptr \<leftarrow> get_ntfn_obj_ref ntfn_bound_tcb ntfnptr;
     maybeM (\<lambda>t. do_unbind_notification ntfnptr t) tptr
   od"


text {* Cancel all message operations on threads queued in a notification endpoint. *}

definition
  cancel_all_signals :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "cancel_all_signals ntfnptr \<equiv> do
     ntfn \<leftarrow> get_notification ntfnptr;
     case ntfn_obj ntfn of WaitingNtfn queue \<Rightarrow> do
                      _ \<leftarrow> set_notification ntfnptr $ ntfn_obj_update (K IdleNtfn) ntfn;
                      mapM_x (\<lambda>t. do set_thread_state t Restart;
                                     possible_switch_to t od) queue;
                      reschedule_required
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
  blocked_cancel_ipc :: "thread_state \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "blocked_cancel_ipc state tptr reply_opt \<equiv> do
     epptr \<leftarrow> get_blocking_object state;
     ep \<leftarrow> get_endpoint epptr;
     queue \<leftarrow> get_ep_queue ep;
     queue' \<leftarrow> return $ remove1 tptr queue;
     ep' \<leftarrow> return (case queue' of [] \<Rightarrow> IdleEP
                                |  _ \<Rightarrow> update_ep_queue ep queue');
     set_endpoint epptr ep';
     case reply_opt of
         None \<Rightarrow> return ()
       | Some r \<Rightarrow> do
             reply \<leftarrow> get_reply r;
             assert (reply_sc reply = None);
             reply_unlink_tcb r
         od;
     set_thread_state tptr Inactive
   od"

text \<open> Unbind TCB, if there is one bound. \<close>
definition
  sched_context_unbind_all_tcbs :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_unbind_all_tcbs sc_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    when (sc_tcb sc \<noteq> None \<and> sc_ptr \<noteq> idle_sc_ptr) $ sched_context_unbind_tcb sc_ptr
  od"

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

text {* Cancel the message receive operation of a thread waiting for a Reply
capability it has issued to be invoked. *}
definition
  reply_cancel_ipc :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where (* called when tptr is in BlocedOnReply *)
 "reply_cancel_ipc tptr \<equiv> do
    thread_set (\<lambda>tcb. tcb \<lparr> tcb_fault := None \<rparr>) tptr;
    reply_remove_tcb tptr
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
     newNTFN \<leftarrow> return $ ntfn_obj_update (K (case queue' of [] \<Rightarrow> IdleNtfn
                                                      | _  \<Rightarrow> WaitingNtfn queue')) ntfn;
     set_notification ntfnptr newNTFN;
     set_thread_state threadptr Inactive
   od"

text {* Cancel any message operations a given thread is waiting on. *}
definition
  cancel_ipc :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "cancel_ipc tptr \<equiv> do
     state \<leftarrow> get_thread_state tptr;
     case state
       of
          BlockedOnSend x y \<Rightarrow> blocked_cancel_ipc state tptr None
        | BlockedOnReceive x reply \<Rightarrow> blocked_cancel_ipc state tptr reply
        | BlockedOnNotification event \<Rightarrow> cancel_signal tptr event
        | BlockedOnReply (Some reply) \<Rightarrow> reply_cancel_ipc tptr
        | BlockedOnReply None \<Rightarrow> fail
        | _ \<Rightarrow> return ()
   od"

end
