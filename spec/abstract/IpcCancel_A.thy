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

text {* Notification accessors. *}
definition
  get_ntfn_obj_ref :: "(notification => obj_ref option) \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad"
where
  "get_ntfn_obj_ref f ref \<equiv> do
     ntfn \<leftarrow> get_notification ref;
     return $ f ntfn
   od"

definition
  set_ntfn_obj_ref :: "((obj_ref option \<Rightarrow> obj_ref option) \<Rightarrow> notification \<Rightarrow> notification) \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_ntfn_obj_ref f ref new \<equiv> do
     ntfn \<leftarrow> get_notification ref;
     set_object ref (Notification (f (K new) ntfn))
   od"

abbreviation
  ntfn_set_obj :: "notification \<Rightarrow> ntfn \<Rightarrow> notification"
where
  "ntfn_set_obj ntfn a \<equiv> ntfn \<lparr> ntfn_obj := a \<rparr>"

definition
  sched_context_bind_ntfn :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_bind_ntfn sc ntfn = do
    set_ntfn_obj_ref ntfn_sc_update ntfn (Some sc);
    set_sc_obj_ref sc_ntfn_update sc (Some ntfn)
  od"

definition
  sched_context_unbind_ntfn :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_unbind_ntfn sc_ptr = do
    ntfn_opt \<leftarrow> get_sc_obj_ref sc_ntfn sc_ptr;
    maybeM (\<lambda>ntfn. do
      set_sc_obj_ref sc_ntfn_update sc_ptr None;
      set_ntfn_obj_ref ntfn_sc_update ntfn None
    od) ntfn_opt
  od"

definition
  sched_context_maybe_unbind_ntfn :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_maybe_unbind_ntfn ntfn_ptr = do
    sc_opt \<leftarrow> get_ntfn_obj_ref ntfn_sc ntfn_ptr;
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
     set_tcb_obj_ref tcb_sched_context_update tptr None;
     cur \<leftarrow> gets $ cur_thread;
     when (tptr = cur) $ do_extended_op reschedule_required
  od"

text \<open>Donate a scheduling context.\<close>
definition
  sched_context_donate :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_donate sc_ptr tcb_ptr = do
    from_opt \<leftarrow> get_sc_obj_ref sc_tcb sc_ptr;
    when (from_opt \<noteq> None) $ sched_context_unbind_tcb sc_ptr;
    set_sc_obj_ref sc_tcb_update sc_ptr (Some tcb_ptr);
    set_tcb_obj_ref tcb_sched_context_update tcb_ptr (Some sc_ptr)
  od"

text \<open>Unbind a reply from the corresponding scheduling context.\<close>
definition
  reply_unbind_sc :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "reply_unbind_sc sc_ptr reply_ptr = do
     sc \<leftarrow> get_sched_context sc_ptr;
     reply \<leftarrow> get_reply reply_ptr;
     set_reply reply_ptr (reply\<lparr>reply_sc:= None\<rparr>);
     set_sched_context sc_ptr (sc\<lparr>sc_replies := remove1 reply_ptr (sc_replies sc)\<rparr>)
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

text \<open>Unbind all replies from a scheduling context.\<close>
definition
  sched_context_clear_replies :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_clear_replies sc_ptr = do
     replies \<leftarrow> liftM sc_replies $ get_sched_context sc_ptr;
     mapM_x (reply_unbind_sc sc_ptr) replies
  od"

text {* Remove a reply object from the call stack. *}
definition
  reply_remove :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where (* must be in BlockedOnReply *)
  "reply_remove r = do
    reply \<leftarrow> get_reply r;
    caller \<leftarrow> assert_opt $ reply_tcb reply;
    sc_ptr \<leftarrow> assert_opt $ reply_sc reply;
    replies \<leftarrow> liftM sc_replies $ get_sched_context sc_ptr;
    reply_unbind_caller caller r;
    reply_unbind_sc sc_ptr r;
    when (hd replies = r) $ sched_context_donate sc_ptr caller;
    set_thread_state caller (BlockedOnReply None)
  od" (* the r.caller is in BlockedOnReply on return *)

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

definition
  unbind_reply_tcb :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "unbind_reply_tcb rptr \<equiv> do
    reply \<leftarrow> get_reply rptr;
    tptr \<leftarrow> return (reply_tcb reply);
    when (tptr \<noteq> None) $ do
      st \<leftarrow> get_thread_state (the tptr);
      case st of BlockedOnReceive x r \<Rightarrow> do
            set_thread_state (the tptr) (BlockedOnReceive x None);
            set_reply rptr (reply\<lparr>reply_tcb := None\<rparr>)
                 od
            | BlockedOnReply r \<Rightarrow> do
            set_thread_state (the tptr) (BlockedOnReply None);
            maybeM reply_remove r
          od
            | _ \<Rightarrow> return ()
    od
  od" (* set_thread_state? *)

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
    sc_callee \<leftarrow> get_tcb_obj_ref tcb_sched_context callee;

    reply_tcb_opt \<leftarrow> get_reply_tcb reply_ptr;
    when (reply_tcb_opt \<noteq> None \<and> reply_tcb_opt \<noteq> Some callee) $ do
         ts \<leftarrow> get_thread_state (the reply_tcb_opt);
         case ts of BlockedOnReply r \<Rightarrow> reply_remove reply_ptr (* r must be reply_ptr *)
             (* the PR claims that reply_remove changes the TS, but it actually doesn't *)
                  | BlockedOnReceive _ _ \<Rightarrow> return ()  (* _otherwise_ case described in the C *)
                  | _ \<Rightarrow> fail
    od;

    can_donate \<leftarrow> return (if (sc_callee = None) then can_donate else False);

    ts_reply \<leftarrow> no_reply_in_ts caller;
    assert (ts_reply);
    unbind_reply_in_ts callee;


    (* link reply and tcb *)
    reply \<leftarrow> get_reply reply_ptr;
    reply' \<leftarrow> return $ reply\<lparr>reply_tcb := Some caller\<rparr>;
    set_reply reply_ptr (reply\<lparr>reply_tcb := Some caller\<rparr>);
    set_thread_state caller (BlockedOnReply (Some reply_ptr)); (* setting of ST is not in C yet *)

    when (sc_caller \<noteq> None \<and> can_donate) $ do
      sc \<leftarrow> get_sched_context (the sc_caller);
      set_sched_context (the sc_caller) (sc\<lparr>sc_replies := reply_ptr#sc_replies sc\<rparr>);
      set_reply reply_ptr (reply'\<lparr>reply_sc := sc_caller\<rparr>);
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
  sort_queue :: "obj_ref list \<Rightarrow> obj_ref list det_ext_monad"
where
  "sort_queue qs = do
     prios \<leftarrow> mapM (ethread_get tcb_priority) qs;
     return $ map snd $ sort_key (\<lambda>x.255 - (fst x)) (zip prios qs) (* 0 \<le> priority < 256 *)
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
  set_priority :: "obj_ref \<Rightarrow> priority \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "set_priority tptr prio \<equiv> do
     do_extended_op $ tcb_sched_action tcb_sched_dequeue tptr;
     do_extended_op $ thread_set_priority tptr prio;
     ts \<leftarrow> get_thread_state tptr;
     when (runnable ts) $ do
       do_extended_op $ tcb_sched_action tcb_sched_enqueue tptr;
       cur \<leftarrow> gets cur_thread;
       when (tptr = cur) (do_extended_op reschedule_required)
     od;
     maybeM (do_extended_op o reorder_ep) (ep_blocked ts);
     maybeM (do_extended_op o reorder_ntfn) (ntfn_blocked ts)
   od"

definition
  possible_switch_to :: "obj_ref \<Rightarrow> unit det_ext_monad" where
  "possible_switch_to target \<equiv> do
     sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context target;
     inq \<leftarrow> gets $ in_release_queue target;
     when (sc_opt \<noteq> None \<and> \<not>inq) $ do
     cur_dom \<leftarrow> gets cur_domain;
     target_dom \<leftarrow> ethread_get tcb_domain target;
     action \<leftarrow> gets scheduler_action;

     if (target_dom \<noteq> cur_dom) then
       tcb_sched_action tcb_sched_enqueue target
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
              when (reply_opt \<noteq> None) $ do
                   reply \<leftarrow> get_reply (the reply_opt);
                   set_reply (the reply_opt) (reply\<lparr>reply_tcb := None\<rparr>)
                 od;
              set_thread_state t Restart;
              do_extended_op (possible_switch_to t)
            od) $ queue;
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
                  do_extended_op $ possible_switch_to t;
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

oo many now)
text {* Remove the binding between a notification and a TCB. *}
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
                      _ \<leftarrow> set_notification ntfnptr $ ntfn_set_obj ntfn IdleNtfn;
                      mapM_x (\<lambda>t. do set_thread_state t Restart;
                                     do_extended_op $ possible_switch_to t od) queue;
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
     when (reply_opt \<noteq> None) $ do
                           reply \<leftarrow>get_reply (the reply_opt);
                           set_reply (the reply_opt) (reply\<lparr>reply_tcb:= None\<rparr>)
                         od;
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
  reply_cancel_ipc :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> (unit, 'z::state_ext) s_monad"
where (* called when tptr is in BlocedOnReply *)
 "reply_cancel_ipc tptr reply_opt \<equiv> do
    thread_set (\<lambda>tcb. tcb \<lparr> tcb_fault := None \<rparr>) tptr;
    maybeM reply_remove reply_opt;
   set_thread_state tptr Inactive
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
  cancel_ipc :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "cancel_ipc tptr \<equiv> do
     state \<leftarrow> get_thread_state tptr;
     case state
       of
          BlockedOnSend x y \<Rightarrow> blocked_cancel_ipc state tptr None
        | BlockedOnReceive x reply \<Rightarrow> blocked_cancel_ipc state tptr reply
        | BlockedOnNotification event \<Rightarrow> cancel_signal tptr event
        | BlockedOnReply reply \<Rightarrow> reply_cancel_ipc tptr reply
        | _ \<Rightarrow> return ()
   od"

end
