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
imports "./$L4V_ARCH/ArchIpcCancel_A"
begin

context begin interpretation Arch .

requalify_consts
  arch_post_cap_deletion
  arch_gen_obj_refs
  arch_cap_cleanup_opt
  faultRegister
  nextInstructionRegister

requalify_types
  arch_gen_obj_ref

end

text \<open>Scheduling context accessors.\<close>
definition
  sched_context_bind_ntfn :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_bind_ntfn sc ntfn = do
    set_ntfn_obj_ref ntfn_sc_update ntfn (Some sc);
    set_sc_obj_ref sc_ntfn_update sc (Some ntfn)
  od"

text \<open>Remove the binding between a notification and a scheduling context.
        This is avoids double reads when calling @{text sched_context_unbind_ntfn}
        from @{text sched_context_maybe_unbind_ntfn} (which has infoflow repercussions)\<close>
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
    \<comment> \<open>Only the head reply will be pointing to this scheduling context,
        so there is no need to worry about the others.\<close>
    unless (replies = []) $ do
      set_reply_obj_ref reply_sc_update (hd replies) None;
      set_sc_obj_ref sc_replies_update sc_ptr []
    od
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

text \<open>
  Unbind a TCB from its scheduling context.
  Takes the TCB as argument and calls @{text sched_context_unbind_tcb}.
\<close>
definition
  maybe_sched_context_unbind_tcb :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "maybe_sched_context_unbind_tcb target = do
     sc_ptr_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context target;
     maybeM sched_context_unbind_tcb sc_ptr_opt
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

     if hd sc_replies = reply_ptr
     then do  \<comment> \<open>if it is the head\<close>
       assert (reply_sc reply = Some sc_ptr); \<comment> \<open>only the head of the list should point to the sc\<close>
       update_sched_context sc_ptr (sc_replies_update tl); \<comment> \<open>pop the head\<close>
       case tl sc_replies of
           [] \<Rightarrow> return ()
         | r'#_ \<Rightarrow> set_reply_obj_ref reply_sc_update r' (Some sc_ptr); \<comment> \<open>fix up the refs\<close>
       set_reply_obj_ref reply_sc_update reply_ptr None \<comment> \<open>set @{text reply_sc} to None\<close>
     od
     else do
       assert (reply_sc reply = None); \<comment> \<open>only the head of the list should point to the sc\<close>
       update_sched_context sc_ptr (sc_replies_update (takeWhile (\<lambda>r. r \<noteq> reply_ptr)))
                                     \<comment> \<open>take until the (first and only) occurrence of @{text reply_ptr}\<close>
     od
  od"

text \<open>Unbind a reply from the corresponding TCB.\<close>

definition reply_unlink_tcb :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "reply_unlink_tcb t r = do
     reply \<leftarrow> get_reply r;
     assert (reply_tcb reply = Some t);
     ts \<leftarrow> get_thread_state t;
     assert (ts = BlockedOnReply r \<or> (\<exists>ep d. ts = BlockedOnReceive ep (Some r) d));
     set_reply_obj_ref reply_tcb_update r None;
     set_thread_state t Inactive
   od"

text \<open>Remove a reply object from the call stack.\<close>

definition sc_with_reply :: "obj_ref \<Rightarrow> 'z::state_ext state => obj_ref option"
  where
  "sc_with_reply r s \<equiv> the_pred_option (\<lambda>sc_ptr. \<exists>sc n. kheap s sc_ptr = Some (SchedContext sc n)
                                                         \<and> r \<in> set (sc_replies sc))"

lemmas sc_with_reply_def2 = sc_with_reply_def[unfolded the_pred_option_def]

definition
  reply_remove :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where (* reply_tcb/caller must be in BlockedOnReply *)
  "reply_remove caller r = do
    reply \<leftarrow> get_reply r;
    assert (reply_tcb reply = Some caller);
    r_sc_opt \<leftarrow> gets $ sc_with_reply r;
    case r_sc_opt of
      None \<Rightarrow> return ()
    | Some sc_ptr \<Rightarrow> do
        replies \<leftarrow> liftM sc_replies $ get_sched_context sc_ptr;
        caller_sc \<leftarrow> get_tcb_obj_ref tcb_sched_context caller;
        \<comment> \<open>drop the head or cut off the stack\<close>
        reply_unlink_sc sc_ptr r;
        when (hd replies = r \<and> caller_sc = None) $ sched_context_donate sc_ptr caller
      od;
    \<comment> \<open>FIXME RT: check the C code!\<close>
    reply_unlink_tcb caller r
   od" (* the r.caller is in Inactive on return *)

text \<open>Remove a specific thread, and the reply it is blocking on, from the call stack.
        The thread must be @{const BlockedOnReply}.\<close>
definition
  reply_remove_tcb :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "reply_remove_tcb tptr rptr = do
    ts \<leftarrow> get_thread_state tptr;
    assert (ts = BlockedOnReply rptr);
    sc_ptr_opt \<leftarrow> gets $ sc_with_reply rptr;
    case sc_ptr_opt of
      None \<Rightarrow> return ()
    | Some sc_ptr \<Rightarrow> do
        sc_replies \<leftarrow> liftM sc_replies $ get_sched_context sc_ptr;
        \<comment> \<open>The reply only has a reference to the scheduling context if it is
            at the head of the reply queue.\<close>
        reply_sc \<leftarrow> get_reply_obj_ref reply_sc rptr;
        assert (if hd sc_replies = rptr then reply_sc = Some sc_ptr else reply_sc = None);
        \<comment> \<open>Drop this reply and all subsequent replies from the call stack.
            All the associated caller threads become stuck.\<close>
        update_sched_context sc_ptr (sc_replies_update (takeWhile (\<lambda>r. r \<noteq> rptr)));
        \<comment> \<open>This will be a no-op if the reply is not at the head of the queue.\<close>
        set_reply_obj_ref reply_sc_update rptr None
      od;
    \<comment> \<open>This leaves the caller thread Inactive.\<close>
    reply_unlink_tcb tptr rptr
  od"

definition
  no_reply_in_ts :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "no_reply_in_ts tptr \<equiv> do
      st \<leftarrow> get_thread_state tptr;
      case st of BlockedOnReceive _ r _ \<Rightarrow> return (r = None)
               | BlockedOnReply r \<Rightarrow> return False
               | _ \<Rightarrow> return True
  od"

definition
  bind_sc_reply :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "bind_sc_reply sc_ptr reply_ptr = do
      sc_replies \<leftarrow> liftM sc_replies $ get_sched_context (sc_ptr);
      \<comment> \<open>unlink head reply and sc before pushing\<close>
      case sc_replies of
          [] \<Rightarrow> return ()
        | r#_ \<Rightarrow> set_reply_obj_ref reply_sc_update r None;
      \<comment> \<open>push new head reply\<close>
      set_sc_obj_ref sc_replies_update sc_ptr (reply_ptr#sc_replies);
      \<comment> \<open>link new head reply to sc\<close>
      set_reply_obj_ref reply_sc_update reply_ptr (Some sc_ptr)
  od"

text \<open>Push a reply object to the call stack.\<close>
definition
  reply_push :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> bool \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "reply_push caller callee reply_ptr can_donate = do
    sc_caller \<leftarrow> get_tcb_obj_ref tcb_sched_context caller;
    sc_callee \<leftarrow> get_tcb_obj_ref tcb_sched_context callee;

    \<comment> \<open>link reply and tcb\<close>
    set_reply_obj_ref reply_tcb_update reply_ptr (Some caller);
    set_thread_state caller (BlockedOnReply reply_ptr);

    when (sc_caller \<noteq> None \<and> sc_callee = None \<and> can_donate) $ do
      bind_sc_reply (the sc_caller) reply_ptr;
      sched_context_donate (the sc_caller) callee
    od
  od"

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


text \<open>The endpoint a TCB is blocked on\<close>
definition
  ep_blocked :: "thread_state \<Rightarrow> obj_ref option"
where
  "ep_blocked ts \<equiv> case ts of
     BlockedOnReceive r _ _ \<Rightarrow> Some r
   | BlockedOnSend r _ \<Rightarrow> Some r
   | _ \<Rightarrow> None"

text \<open>The notification a TCB is blocked on\<close>
definition
  ntfn_blocked :: "thread_state \<Rightarrow> obj_ref option"
where
  "ntfn_blocked ts \<equiv> case ts of
    BlockedOnNotification r \<Rightarrow> Some r
  | _ \<Rightarrow> None"

fun
  tcb_ep_find_index :: "obj_ref \<Rightarrow> obj_ref list \<Rightarrow> nat \<Rightarrow> (nat, 'z::state_ext) s_monad"
where
  "tcb_ep_find_index tptr qs curindex = do
     prio \<leftarrow> thread_get tcb_priority tptr;
     curprio \<leftarrow> thread_get tcb_priority (qs ! curindex);
     if prio > curprio then
       if curindex = 0 then return 0
       else tcb_ep_find_index tptr qs (curindex - 1)
     else return (curindex + 1)
   od"

declare tcb_ep_find_index.simps[simp del]

definition
  tcb_ep_dequeue :: "obj_ref \<Rightarrow> obj_ref list \<Rightarrow> (obj_ref list, 'z::state_ext) s_monad"
where
  "tcb_ep_dequeue tptr qs = do
     index \<leftarrow> return $ the $ findIndex (\<lambda>x. x = tptr) qs;
     return $ take index qs @ drop (index + 1) qs
   od"

definition
  tcb_ep_append :: "obj_ref \<Rightarrow> obj_ref list \<Rightarrow> (obj_ref list, 'z::state_ext) s_monad"
where
  "tcb_ep_append tptr qs \<equiv>
     if qs = [] then return [tptr]
     else do index \<leftarrow> tcb_ep_find_index tptr qs (length qs - 1);
             return $ take index qs @ tptr # drop index qs
     od"

text \<open>Bring endpoint queue back into priority order\<close>
definition
  reorder_ep :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "reorder_ep ep_ptr tptr = do
    ep \<leftarrow> get_endpoint ep_ptr;
    qs \<leftarrow> get_ep_queue ep;
    qs' \<leftarrow> tcb_ep_dequeue tptr qs;
    qs'' \<leftarrow> tcb_ep_append tptr qs';
    set_endpoint ep_ptr (update_ep_queue ep qs'')
  od"

text \<open>Extract list of TCBs waiting on this notification\<close>
definition
  get_ntfn_queue :: "notification \<Rightarrow> obj_ref list option"
where
  "get_ntfn_queue ntfn \<equiv> case ntfn_obj ntfn of
     WaitingNtfn qs \<Rightarrow> Some qs
   | _ \<Rightarrow> None"

text \<open>Bring notification queue back into priority order\<close>
definition
  reorder_ntfn :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "reorder_ntfn ntfn_ptr tptr = do
    ntfn \<leftarrow> get_notification ntfn_ptr;
    qs \<leftarrow> assert_opt $ get_ntfn_queue ntfn;
    qs' \<leftarrow> tcb_ep_dequeue tptr qs;
    qs'' \<leftarrow> tcb_ep_append tptr qs';
    set_notification ntfn_ptr (ntfn \<lparr> ntfn_obj := WaitingNtfn qs'' \<rparr>)
  od"

text \<open>Set new priority for a TCB\<close>
definition
  set_priority :: "obj_ref \<Rightarrow> priority \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "set_priority tptr prio \<equiv> do
     ts \<leftarrow> get_thread_state tptr;
     if runnable ts then do
       d \<leftarrow> thread_get tcb_domain tptr;
       p \<leftarrow> thread_get tcb_priority tptr;
       queue \<leftarrow> get_tcb_queue d p;
       cur \<leftarrow> gets cur_thread;
       if tptr \<in> set queue \<or> tptr = cur then do
           tcb_sched_action tcb_sched_dequeue tptr;
           thread_set_priority tptr prio;
           tcb_sched_action tcb_sched_enqueue tptr;
           reschedule_required
         od
       else
         thread_set_priority tptr prio
       od
     else do
       thread_set_priority tptr prio;
       maybeM (\<lambda>ep. reorder_ep ep tptr) (ep_blocked ts);
       maybeM (\<lambda>ntfn. reorder_ntfn ntfn tptr) (ntfn_blocked ts)
     od
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
       \<comment> \<open>not in @{text \<open>release queue & active_sc\<close>}\<close>
       if target_dom \<noteq> cur_dom then
         tcb_sched_action tcb_sched_enqueue target \<comment> \<open>not @{text \<open>in cur_domain\<close>}\<close>
       else if action \<noteq> resume_cur_thread then do
           reschedule_required;
           tcb_sched_action tcb_sched_enqueue target
         od
       else set_scheduler_action $ switch_thread target
     od
   od"

definition
  restart_thread_if_no_fault :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "restart_thread_if_no_fault t \<equiv> do
     fault \<leftarrow> thread_get tcb_fault t;
     if fault = None
     then do
       set_thread_state t Restart;
       sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context t;
       if_sporadic_cur_sc_assert_refill_unblock_check sc_opt;
       possible_switch_to t
     od
     else set_thread_state t Inactive
   od"

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
         mapM_x (\<lambda>t.
           do st \<leftarrow> get_thread_state t;
              reply_opt \<leftarrow> case st of BlockedOnReceive _ r_opt _ \<Rightarrow> return r_opt
                                    | _ \<Rightarrow> return None;
              when (reply_opt \<noteq> None) $ reply_unlink_tcb t (the reply_opt);
              restart_thread_if_no_fault t
            od) $ queue;
         reschedule_required
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
                  restart_thread_if_no_fault t;
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

text \<open>Remove the binding between a notification and a TCB. This is avoids double reads
      when calling @{text unbind_notification} from @{text unbind_maybe_notification}
      (which would have infoflow repercussions).\<close>
abbreviation
  do_unbind_notification :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "do_unbind_notification ntfnptr tcbptr \<equiv> do
      set_ntfn_obj_ref ntfn_bound_tcb_update ntfnptr None;
      set_tcb_obj_ref tcb_bound_notification_update tcbptr None
    od"


text \<open>Remove bound notification from a TCB in bound state.\<close>
definition
  unbind_notification :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "unbind_notification tcb \<equiv> do
     ntfnptr \<leftarrow> get_tcb_obj_ref tcb_bound_notification tcb;
     maybeM (\<lambda>nptr. do_unbind_notification nptr tcb) ntfnptr
   od"

text \<open>Remove bound notification from a TCB if such notification exists.\<close>
definition
  unbind_maybe_notification :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "unbind_maybe_notification ntfnptr \<equiv> do
     tptr \<leftarrow> get_ntfn_obj_ref ntfn_bound_tcb ntfnptr;
     maybeM (\<lambda>t. do_unbind_notification ntfnptr t) tptr
   od"


text \<open>Cancel all message operations on threads queued in a notification endpoint.\<close>

definition
  cancel_all_signals :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "cancel_all_signals ntfnptr \<equiv> do
     ntfn \<leftarrow> get_notification ntfnptr;
     case ntfn_obj ntfn of WaitingNtfn queue \<Rightarrow> do
                      _ \<leftarrow> set_notification ntfnptr $ ntfn_obj_update (K IdleNtfn) ntfn;
                      mapM_x (\<lambda>t. do set_thread_state t Restart;
                                     sc_ptr \<leftarrow> get_tcb_obj_ref tcb_sched_context t;
                                     if_sporadic_cur_sc_assert_refill_unblock_check sc_ptr;
                                     possible_switch_to t od) queue;
                      reschedule_required
                     od
               | _ \<Rightarrow> return ()
   od"

text \<open>The endpoint pointer stored by a thread waiting for a message to be
transferred in either direction.\<close>
definition
  get_blocking_object :: "thread_state \<Rightarrow> (obj_ref,'z::state_ext) s_monad"
where
 "get_blocking_object state \<equiv> assert_opt $ ep_blocked state"


text \<open>Cancel whatever IPC operation a thread is engaged in.\<close>
definition blocked_cancel_ipc ::
  "thread_state \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow> (unit, 'z::state_ext) s_monad"
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
       | Some r \<Rightarrow> reply_unlink_tcb tptr r;
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
     newNTFN \<leftarrow> return $ ntfn_obj_update (K (case queue' of [] \<Rightarrow> IdleNtfn
                                                      | _  \<Rightarrow> WaitingNtfn queue')) ntfn;
     set_notification ntfnptr newNTFN;
     set_thread_state threadptr Inactive
   od"

text \<open>Cancel any message operations a given thread is waiting on.\<close>
definition
  cancel_ipc :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "cancel_ipc tptr \<equiv> do
     state \<leftarrow> get_thread_state tptr;
     thread_set (\<lambda>tcb. tcb \<lparr> tcb_fault := None \<rparr>) tptr;
     case state
       of
          BlockedOnSend x y \<Rightarrow> blocked_cancel_ipc state tptr None
        | BlockedOnReceive x reply _ \<Rightarrow> blocked_cancel_ipc state tptr reply
        | BlockedOnNotification event \<Rightarrow> cancel_signal tptr event
        | BlockedOnReply reply \<Rightarrow> reply_remove_tcb tptr reply
        | _ \<Rightarrow> return ()
   od"

end
