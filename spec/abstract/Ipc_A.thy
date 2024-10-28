(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Specification of Inter-Process Communication.
*)

chapter "IPC"

theory Ipc_A
imports Tcb_A ArchFault_A
begin

arch_requalify_consts (A)
  lookup_ipc_buffer
  make_arch_fault_msg
  handle_arch_fault_reply

section \<open>Getting and setting the message info register.\<close>

definition
  get_message_info :: "obj_ref \<Rightarrow> (message_info,'z::state_ext) s_monad"
where
  "get_message_info thread \<equiv> do
     x \<leftarrow> as_user thread $ getRegister msg_info_register;
     return $ data_to_message_info x
   od"

section \<open>IPC Capability Transfers\<close>

definition
  remove_rights :: "cap_rights \<Rightarrow> cap \<Rightarrow> cap"
where
 "remove_rights rights cap \<equiv> cap_rights_update (cap_rights cap - rights) cap"

text \<open>In addition to the data payload a message may also contain capabilities.
When a thread requests additional capabilities be transferred the identities of
those capabilities are retreived from the thread's IPC buffer.\<close>
definition
  buffer_cptr_index :: nat
where
 "buffer_cptr_index \<equiv> (msg_max_length + 2)"

primrec
  get_extra_cptrs :: "obj_ref option \<Rightarrow> message_info \<Rightarrow> (cap_ref list,'z::state_ext) s_monad"
where
  "get_extra_cptrs (Some buf) mi =
    (liftM (map data_to_cptr) $ mapM (load_word_offs buf)
        [buffer_cptr_index ..< buffer_cptr_index + (unat (mi_extra_caps mi))])"
| "get_extra_cptrs None mi = return []"

definition
  get_extra_cptr :: "obj_ref \<Rightarrow> nat \<Rightarrow> (cap_ref,'z::state_ext) s_monad"
where
  "get_extra_cptr buffer n \<equiv> liftM data_to_cptr
      (load_word_offs buffer (n + buffer_cptr_index))"

text \<open>This function both looks up the addresses of the additional capabilities
and retreives them from the sender's CSpace.\<close>
definition
  lookup_extra_caps :: "obj_ref \<Rightarrow> data option \<Rightarrow> message_info \<Rightarrow> ((cap \<times> cslot_ptr) list,'z::state_ext) f_monad" where
  "lookup_extra_caps thread buffer mi \<equiv> doE
       cptrs \<leftarrow> liftE $ get_extra_cptrs buffer mi;
       mapME (\<lambda>cptr. cap_fault_on_failure (of_bl cptr) False $ lookup_cap_and_slot thread cptr) cptrs
  odE"

text \<open>Capability transfers. Capabilities passed along with a message are split
into two groups. Capabilities to the same endpoint as the message is passed
through are not copied. Their badges are unwrapped and stored in the receiver's
message buffer instead. Other capabilities are copied into the given slots.

Capability unwrapping allows a client to efficiently demonstrate to a server
that it possesses authority to two or more services that server provides.
\<close>
definition
  set_extra_badge :: "obj_ref \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_extra_badge buffer badge n \<equiv>
      store_word_offs buffer (buffer_cptr_index + n) badge"

type_synonym transfer_caps_data = "(cap \<times> cslot_ptr) list \<times> cslot_ptr list"

fun
  transfer_caps_loop :: "obj_ref option \<Rightarrow> obj_ref \<Rightarrow> nat
                          \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> cslot_ptr list
                          \<Rightarrow> message_info \<Rightarrow> (message_info,'z::state_ext) s_monad"
where
  "transfer_caps_loop ep rcv_buffer n [] slots
      mi = return (MI (mi_length mi) (of_nat n) (mi_caps_unwrapped mi)
                        (mi_label mi))"
| "transfer_caps_loop ep rcv_buffer n ((cap, slot) # morecaps)
         slots mi =
  const_on_failure (MI (mi_length mi) (of_nat n) (mi_caps_unwrapped mi)
                       (mi_label mi)) (doE
    transfer_rest \<leftarrow> returnOk $ transfer_caps_loop ep
         rcv_buffer (n + 1) morecaps;
    if (is_ep_cap cap \<and> ep = Some (obj_ref_of cap))
    then doE
       liftE $ set_extra_badge rcv_buffer (cap_ep_badge cap) n;
       liftE $ transfer_rest slots (MI (mi_length mi) (mi_extra_caps mi)
         (mi_caps_unwrapped mi || (1 << n)) (mi_label mi))
    odE
    else if slots \<noteq> []
    then doE
      cap' \<leftarrow> derive_cap slot cap;
      whenE (cap' = NullCap) $ throwError undefined;
      liftE $ cap_insert cap' slot (hd slots);
      liftE $ transfer_rest (tl slots) mi
    odE
    else returnOk (MI (mi_length mi) (of_nat n) (mi_caps_unwrapped mi)
                       (mi_label mi))
  odE)"

definition
  transfer_caps :: "message_info \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
                   obj_ref option \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow>
                   (message_info,'z::state_ext) s_monad"
where
  "transfer_caps info caps endpoint receiver recv_buffer \<equiv> do
     dest_slots \<leftarrow> get_receive_slots receiver recv_buffer;
     mi' \<leftarrow> return $ MI (mi_length info) 0 0 (mi_label info);
     case recv_buffer of
       None \<Rightarrow> return mi'
     | Some receive_buffer \<Rightarrow>
         transfer_caps_loop endpoint receive_buffer 0 caps dest_slots mi'
   od"

section \<open>Fault Handling\<close>

text \<open>Threads fault when they attempt to access services that are not backed
by any resources. Such a thread is then blocked and a fault messages is sent to
its supervisor. When a reply to that message is sent the thread is reactivated.
\<close>

text \<open>Format a message for a given fault type.\<close>
fun
  make_fault_msg :: "fault \<Rightarrow> obj_ref \<Rightarrow> (data \<times> data list,'z::state_ext) s_monad"
where
  "make_fault_msg (CapFault cptr rp lf) thread = (do
     pc \<leftarrow> as_user thread getRestartPC;
     return (1, pc # cptr # (if rp then 1 else 0) # msg_from_lookup_failure lf)
   od)"
| "make_fault_msg (UnknownSyscallException n) thread = (do
     msg \<leftarrow> as_user thread $ mapM getRegister syscallMessage;
     return (2, msg @ [n])
   od)"
| "make_fault_msg (UserException exception code) thread = (do
     msg \<leftarrow> as_user thread $ mapM getRegister exceptionMessage;
     return (3, msg @ [exception, code])
   od)"
| "make_fault_msg (ArchFault af) thread = make_arch_fault_msg af thread " (* arch_fault *)

text \<open>React to a fault reply. The reply message is interpreted in a manner
that depends on the type of the original fault. For some fault types a thread
reconfiguration is performed. This is done entirely to save the fault message
recipient an additional system call. This function returns a boolean indicating
whether the thread should now be restarted.\<close>
fun
  handle_fault_reply :: "fault \<Rightarrow> obj_ref \<Rightarrow>
                         data \<Rightarrow> data list \<Rightarrow> (bool,'z::state_ext) s_monad"
where
  "handle_fault_reply (CapFault cptr rp lf) thread x y = return True"
| "handle_fault_reply (UnknownSyscallException n) thread label msg = do
     t \<leftarrow> arch_get_sanitise_register_info thread;
     as_user thread $ zipWithM_x
         (\<lambda>r v. setRegister r $ sanitise_register t r v)
         syscallMessage msg;
     return (label = 0)
   od"
| "handle_fault_reply (UserException exception code) thread label msg = do
     t \<leftarrow> arch_get_sanitise_register_info thread;
     as_user thread $ zipWithM_x
         (\<lambda>r v. setRegister r $ sanitise_register t r v)
         exceptionMessage msg;
     return (label = 0)
   od"
| " handle_fault_reply (ArchFault af) thread label msg =
    handle_arch_fault_reply af thread label msg" (* arch_fault *)

text \<open>Transfer a fault message from a faulting thread to its supervisor.\<close>
definition
  do_fault_transfer :: "data \<Rightarrow> obj_ref \<Rightarrow> obj_ref
                             \<Rightarrow> obj_ref option \<Rightarrow> (unit,'z::state_ext) s_monad"
where
 "do_fault_transfer badge sender receiver buf \<equiv> do
    fault \<leftarrow> thread_get tcb_fault sender;
    f \<leftarrow> (case fault of
         Some f \<Rightarrow> return f
       | None \<Rightarrow> fail);
    (label, msg) \<leftarrow> make_fault_msg f sender;
    sent \<leftarrow> set_mrs receiver buf msg;
    set_message_info receiver $ MI sent 0 0 label;
    as_user receiver $ setRegister badge_register badge
  od"

section \<open>Synchronous Message Transfers\<close>

text \<open>Transfer a non-fault message.\<close>
definition
  do_normal_transfer :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> obj_ref option
                                    \<Rightarrow> data \<Rightarrow> bool \<Rightarrow> obj_ref
                                    \<Rightarrow> obj_ref option
                                    \<Rightarrow> (unit,'z::state_ext) s_monad"
where
 "do_normal_transfer sender sbuf endpoint badge grant
                     receiver rbuf  \<equiv>
  do
    mi \<leftarrow> get_message_info sender;
    caps \<leftarrow> if grant then lookup_extra_caps sender sbuf mi <catch> K (return [])
      else return [];
    mrs_transferred \<leftarrow> copy_mrs sender sbuf receiver rbuf (mi_length mi);
    mi' \<leftarrow> transfer_caps mi caps endpoint receiver rbuf;
    set_message_info receiver $ MI mrs_transferred (mi_extra_caps mi')
                                   (mi_caps_unwrapped mi') (mi_label mi);
    as_user receiver $ setRegister badge_register badge
  od"

text \<open>Transfer a message either involving a fault or not.\<close>
definition
  do_ipc_transfer :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow>
                       badge \<Rightarrow> bool \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "do_ipc_transfer sender ep badge grant
     receiver \<equiv> do

     recv_buffer \<leftarrow> lookup_ipc_buffer True receiver;
     fault \<leftarrow> thread_get tcb_fault sender;

     case fault
        of None \<Rightarrow> do
            send_buffer \<leftarrow> lookup_ipc_buffer False sender;
            do_normal_transfer sender send_buffer ep badge grant
                           receiver recv_buffer
            od
         | Some f \<Rightarrow> do_fault_transfer badge sender receiver recv_buffer
   od"

text \<open>Transfer a reply message and delete the one-use Reply capability.\<close>
definition
  do_reply_transfer :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> cslot_ptr \<Rightarrow> bool \<Rightarrow> (unit,'z::state_ext) s_monad"
where
 "do_reply_transfer sender receiver slot grant \<equiv> do
    state \<leftarrow> get_thread_state receiver;
    assert (state = BlockedOnReply);
    fault \<leftarrow> thread_get tcb_fault receiver;
    case fault of
      None \<Rightarrow> do
         do_ipc_transfer sender None 0 grant receiver;
         cap_delete_one slot;
         set_thread_state receiver Running;
         possible_switch_to receiver
      od
    | Some f \<Rightarrow> do
         cap_delete_one slot;
         mi \<leftarrow> get_message_info sender;
         buf \<leftarrow> lookup_ipc_buffer False sender;
         mrs \<leftarrow> get_mrs sender buf mi;
         restart \<leftarrow> handle_fault_reply f receiver (mi_label mi) mrs;
         thread_set (\<lambda>tcb. tcb \<lparr> tcb_fault := None \<rparr>) receiver;
         set_thread_state receiver (if restart then Restart else Inactive);
         when restart $ possible_switch_to receiver;
         return ()
       od
  od"

text \<open>This function transfers a reply message to a thread when that message
is generated by a kernel service.\<close>
definition
  reply_from_kernel :: "obj_ref \<Rightarrow> (data \<times> data list) \<Rightarrow> (unit,'z::state_ext) s_monad"
where
 "reply_from_kernel thread x \<equiv> do
    (label, msg) \<leftarrow> return x;
    buf \<leftarrow> lookup_ipc_buffer True thread;
    as_user thread $ setRegister badge_register 0;
    len \<leftarrow> set_mrs thread buf msg;
    set_message_info thread $ MI len 0 0 label
  od"

text \<open>Install a one-use Reply capability.\<close>
definition
  setup_caller_cap :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> bool \<Rightarrow> (unit,'z::state_ext) s_monad"
where
 "setup_caller_cap sender receiver grant \<equiv> do
    set_thread_state sender BlockedOnReply;
    cap_insert (ReplyCap sender False (if grant then {AllowGrant, AllowWrite} else {AllowWrite}))
               (sender, tcb_cnode_index 2)
      (receiver, tcb_cnode_index 3)
  od"

text \<open>Handle a message send operation performed on an endpoint by a thread.
If a receiver is waiting then transfer the message. If no receiver is available
and the thread is willing to block waiting to send then put it in the endpoint
sending queue.\<close>
definition
  send_ipc :: "bool \<Rightarrow> bool \<Rightarrow> badge \<Rightarrow> bool \<Rightarrow> bool
                \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "send_ipc block call badge can_grant can_grant_reply thread epptr \<equiv> do
     ep \<leftarrow> get_endpoint epptr;
     case (ep, block) of
         (IdleEP, True) \<Rightarrow> do
               set_thread_state thread (BlockedOnSend epptr
                                   \<lparr> sender_badge = badge,
                                     sender_can_grant = can_grant,
                                     sender_can_grant_reply = can_grant_reply,
                                     sender_is_call = call \<rparr>);
               set_endpoint epptr $ SendEP [thread]
             od
       | (SendEP queue, True) \<Rightarrow> do
               set_thread_state thread (BlockedOnSend epptr
                                   \<lparr> sender_badge = badge,
                                     sender_can_grant = can_grant,
                                     sender_can_grant_reply = can_grant_reply,
                                     sender_is_call = call\<rparr>);
               set_endpoint epptr $ SendEP (queue @ [thread])
             od
       | (IdleEP, False) \<Rightarrow> return ()
       | (SendEP queue, False) \<Rightarrow> return ()
       | (RecvEP (dest # queue), _) \<Rightarrow> do
                set_endpoint epptr $ (case queue of [] \<Rightarrow> IdleEP
                                                     | _ \<Rightarrow> RecvEP queue);
                recv_state \<leftarrow> get_thread_state dest;
                reply_can_grant \<leftarrow> case recv_state
                  of (BlockedOnReceive x data) \<Rightarrow> do
                           do_ipc_transfer thread (Some epptr) badge can_grant dest;
                           return (receiver_can_grant data)
                           od
                  | _ \<Rightarrow> fail;
                set_thread_state dest Running;
                possible_switch_to dest;
                when call $
                  if (can_grant \<or> can_grant_reply)
                  then setup_caller_cap thread dest reply_can_grant
                  else set_thread_state thread Inactive
                od

       | (RecvEP [], _) \<Rightarrow> fail
   od"

text \<open>Handle a message receive operation performed on an endpoint by a thread.
If a sender is waiting then transfer the message, otherwise put the thread in
the endpoint receiving queue.\<close>
definition
  isActive :: "notification \<Rightarrow> bool"
where
  "isActive ntfn \<equiv> case ntfn_obj ntfn
     of ActiveNtfn _ \<Rightarrow> True
      | _ \<Rightarrow> False"


text\<open>Helper function for performing \emph{signal} when receiving on a normal
endpoint\<close>
definition
  complete_signal :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "complete_signal ntfnptr tcb \<equiv> do
     ntfn \<leftarrow> get_notification ntfnptr;
     case ntfn_obj ntfn of
       ActiveNtfn badge \<Rightarrow> do
           as_user tcb $ setRegister badge_register badge;
           set_notification ntfnptr $ ntfn_set_obj ntfn IdleNtfn
         od
     | _ \<Rightarrow> fail
   od"

definition
  do_nbrecv_failed_transfer :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "do_nbrecv_failed_transfer thread = do as_user thread $ setRegister badge_register 0; return () od"

definition
  receive_ipc :: "obj_ref \<Rightarrow> cap \<Rightarrow> bool \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "receive_ipc thread cap is_blocking \<equiv> do
     (epptr,rights) \<leftarrow> (case cap
                       of EndpointCap ref badge rights \<Rightarrow> return (ref,rights)
                        | _ \<Rightarrow> fail);
     ep \<leftarrow> get_endpoint epptr;
     ntfnptr \<leftarrow> get_bound_notification thread;
     ntfn \<leftarrow> case_option (return default_notification) get_notification ntfnptr;
     if (ntfnptr \<noteq> None \<and> isActive ntfn)
     then
       complete_signal (the ntfnptr) thread
     else
       case ep
         of IdleEP \<Rightarrow> (case is_blocking of
              True \<Rightarrow> do
                  set_thread_state thread (BlockedOnReceive epptr
                                           \<lparr>receiver_can_grant = (AllowGrant \<in> rights)\<rparr>);
                  set_endpoint epptr (RecvEP [thread])
                od
              | False \<Rightarrow> do_nbrecv_failed_transfer thread)
            | RecvEP queue \<Rightarrow> (case is_blocking of
              True \<Rightarrow> do
                  set_thread_state thread (BlockedOnReceive epptr
                                           \<lparr>receiver_can_grant = (AllowGrant \<in> rights)\<rparr>);
                  set_endpoint epptr (RecvEP (queue @ [thread]))
                od
              | False \<Rightarrow> do_nbrecv_failed_transfer thread)
          | SendEP q \<Rightarrow> do
              assert (q \<noteq> []);
              queue \<leftarrow> return $ tl q;
              sender \<leftarrow> return $ hd q;
              set_endpoint epptr $
                (case queue of [] \<Rightarrow> IdleEP | _ \<Rightarrow> SendEP queue);
              sender_state \<leftarrow> get_thread_state sender;
              data \<leftarrow> (case sender_state
                       of BlockedOnSend ref data \<Rightarrow> return data
                        | _ \<Rightarrow> fail);
              do_ipc_transfer sender (Some epptr)
                        (sender_badge data) (sender_can_grant data)
                        thread;
              if (sender_is_call data)
              then
                if (sender_can_grant data \<or> sender_can_grant_reply data)
                then setup_caller_cap sender thread (AllowGrant \<in> rights)
                else set_thread_state sender Inactive
              else do
                set_thread_state sender Running;
                possible_switch_to sender
              od
            od
   od"

section \<open>Asynchronous Message Transfers\<close>

text \<open>Helper function to handle a signal operation in the case
where a receiver is waiting.\<close>
definition
  update_waiting_ntfn :: "obj_ref \<Rightarrow> obj_ref list \<Rightarrow> obj_ref option \<Rightarrow> badge \<Rightarrow>
                         (unit,'z::state_ext) s_monad"
where
  "update_waiting_ntfn ntfnptr queue bound_tcb badge \<equiv> do
     assert (queue \<noteq> []);
     (dest,rest) \<leftarrow> return $ (hd queue, tl queue);
     set_notification ntfnptr $ \<lparr>
         ntfn_obj = (case rest of [] \<Rightarrow> IdleNtfn | _ \<Rightarrow> WaitingNtfn rest),
         ntfn_bound_tcb = bound_tcb \<rparr>;
     set_thread_state dest Running;
     as_user dest $ setRegister badge_register badge;
     possible_switch_to dest

   od"

text \<open>Handle a message send operation performed on a notification object.
If a receiver is waiting then transfer the message, otherwise combine the new
message with whatever message is currently waiting.\<close>

(* helper function for checking if thread is blocked *)
definition
  receive_blocked :: "thread_state \<Rightarrow> bool"
where
  "receive_blocked st \<equiv> case st of
       BlockedOnReceive _ _ \<Rightarrow> True
     | _ \<Rightarrow> False"

definition
  send_signal :: "obj_ref \<Rightarrow> badge \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "send_signal ntfnptr badge \<equiv> do
    ntfn \<leftarrow> get_notification ntfnptr;
    case (ntfn_obj ntfn, ntfn_bound_tcb ntfn) of
          (IdleNtfn, Some tcb) \<Rightarrow> do
                  st \<leftarrow> get_thread_state tcb;
                  if (receive_blocked st)
                  then do
                      cancel_ipc tcb;
                      set_thread_state tcb Running;
                      as_user tcb $ setRegister badge_register badge;
                      possible_switch_to tcb
                    od
                  else set_notification ntfnptr $ ntfn_set_obj ntfn (ActiveNtfn badge)
            od
       | (IdleNtfn, None) \<Rightarrow> set_notification ntfnptr $ ntfn_set_obj ntfn (ActiveNtfn badge)
       | (WaitingNtfn queue, bound_tcb) \<Rightarrow> update_waiting_ntfn ntfnptr queue bound_tcb badge
       | (ActiveNtfn badge', _) \<Rightarrow>
           set_notification ntfnptr $ ntfn_set_obj ntfn $
             ActiveNtfn (combine_ntfn_badges badge badge')
   od"


text \<open>Handle a receive operation performed on a notification object by a
thread. If a message is waiting then perform the transfer, otherwise put the
thread in the endpoint's receiving queue.\<close>
definition
  receive_signal :: "obj_ref \<Rightarrow> cap \<Rightarrow> bool \<Rightarrow> (unit,'z::state_ext) s_monad"
where
   "receive_signal thread cap is_blocking \<equiv> do
    ntfnptr \<leftarrow>
      case cap
        of NotificationCap ntfnptr badge rights \<Rightarrow> return ntfnptr
         | _ \<Rightarrow> fail;
    ntfn \<leftarrow> get_notification ntfnptr;
    case ntfn_obj ntfn
      of IdleNtfn \<Rightarrow>
                   (case is_blocking of
                     True \<Rightarrow> do
                          set_thread_state thread (BlockedOnNotification ntfnptr);
                          set_notification ntfnptr $ ntfn_set_obj ntfn $ WaitingNtfn [thread]
                        od
                   | False \<Rightarrow> do_nbrecv_failed_transfer thread)
       | WaitingNtfn queue \<Rightarrow>
                   (case is_blocking of
                     True \<Rightarrow> do
                          set_thread_state thread (BlockedOnNotification ntfnptr);
                          set_notification ntfnptr $ ntfn_set_obj ntfn $ WaitingNtfn (queue @ [thread])
                        od
                   | False \<Rightarrow> do_nbrecv_failed_transfer thread)
       | ActiveNtfn badge \<Rightarrow> do
                     as_user thread $ setRegister badge_register badge;
                     set_notification ntfnptr $ ntfn_set_obj ntfn IdleNtfn
                   od
    od"

section \<open>Sending Fault Messages\<close>

text \<open>When a thread encounters a fault, retreive its fault handler capability
and send a fault message.\<close>
definition
  send_fault_ipc :: "obj_ref \<Rightarrow> fault \<Rightarrow> (unit,'z::state_ext) f_monad"
where
  "send_fault_ipc tptr fault \<equiv> doE
     handler_cptr \<leftarrow> liftE $ thread_get tcb_fault_handler tptr;
     handler_cap \<leftarrow> cap_fault_on_failure (of_bl handler_cptr) False $
         lookup_cap tptr handler_cptr;

     let f = CapFault (of_bl handler_cptr) False (MissingCapability 0)
     in
     (case handler_cap
       of EndpointCap ref badge rights \<Rightarrow>
           if AllowSend \<in> rights \<and> (AllowGrant \<in> rights \<or> AllowGrantReply \<in> rights)
           then liftE $ (do
               thread_set (\<lambda>tcb. tcb \<lparr> tcb_fault := Some fault \<rparr>) tptr;
               send_ipc True True (cap_ep_badge handler_cap)
                        (AllowGrant \<in> rights) True tptr (cap_ep_ptr handler_cap)
             od)
           else throwError f
        | _ \<Rightarrow> throwError f)
   odE"

text \<open>If a fault message cannot be sent then leave the thread inactive.\<close>
definition
  handle_double_fault :: "obj_ref \<Rightarrow> fault \<Rightarrow> fault \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "handle_double_fault tptr ex1 ex2 \<equiv> set_thread_state tptr Inactive"

text \<open>Handle a thread fault by sending a fault message if possible.\<close>
definition
  handle_fault :: "obj_ref \<Rightarrow> fault \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "handle_fault thread ex \<equiv> do
     _ \<leftarrow> gets_the $ get_tcb thread;
     send_fault_ipc thread ex
          <catch> handle_double_fault thread ex;
     return ()
   od"

end
