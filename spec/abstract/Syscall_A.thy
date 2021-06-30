(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Top-level system call interface.
*)

chapter "System Calls"

theory Syscall_A
imports
  "ExecSpec.Event_H"
  Decode_A
  "./$L4V_ARCH/Init_A"
  "./$L4V_ARCH/Hypervisor_A"
begin

context begin interpretation Arch .

requalify_consts
  arch_perform_invocation
  handle_vm_fault
  handle_hypervisor_fault
end


text\<open>
\label{c:syscall}

This theory defines the entry point to the kernel, @{term
call_kernel}, which is called by the assembly stubs after
switching into kernel mode and saving registers.
There are five kinds of events that end up in a switch to
kernel mode. These events are described by the enumerated type @{term
event}, defined in \autoref{sec:Event_H}. One of the five events is an
actual system call by the user, the other four are related to faults
and interrupts. There are seven different kinds of user system calls,
described by the enumerated type @{term syscall}, also defined in
\autoref{sec:Event_H}.

The @{text call_kernel} function delegates the event-specific behaviour
to @{text handle_event} which in turn further dispatches to system-call
specific handler functions.

In particular, two of the system calls, namely @{term SysSend} and
@{term SysCall}, correspond to a method invocation on capabilities.
They are handled in the @{term handle_invocation} operation, which is
made up of
three phases: first checking if the caller has the capabilities to
perform the operation, then decoding the arguments received from the
user (using the @{term decode_invocation} operation), and finally
actually performing the invocation (using the @{term
perform_invocation}).  These three phases are wrapped into a more
generic @{term syscall} framework function described below.
\<close>


section \<open>Generic system call structure\label{s:spec_syscall}\<close>


text\<open>The @{term syscall} operation generically describes the usual
execution of system calls in three phases, where the first phase may
result in a fault, the second phase may result in an error and the third
phase may be interrupted. The first two phases are used for argument decoding
and checking. The last phase commits and executes the system call.

The @{term syscall} operation has five arguments:
\begin{itemize}
\item the first operation @{text m_fault} to execute, that may
result in a fault;
\item the fault handler @{text h_fault} to execute if the first
operation resulted in a fault;
\item the second operation @{text m_error} to execute (if no fault
occurred in the first operation); this second operation may result in
an error;
\item the error handler @{text h_error} to execute if the second
operation resulted in an error;
\item the third and last operation @{text m_finalise} to execute (if
no error occurred in the second operation); this operation may be
interrupted.
\end{itemize}
\<close>

definition
  syscall :: "('a,'z::state_ext) f_monad
                  \<Rightarrow> (fault \<Rightarrow> ('c,'z::state_ext) s_monad)
                  \<Rightarrow> ('a \<Rightarrow> ('b,'z::state_ext) se_monad)
                  \<Rightarrow> (syscall_error \<Rightarrow> ('c,'z::state_ext) s_monad)
               \<Rightarrow> ('b \<Rightarrow> ('c,'z::state_ext) p_monad) \<Rightarrow> ('c,'z::state_ext) p_monad"
where
"syscall m_fault h_fault m_error h_error m_finalise \<equiv> doE
    r_fault \<leftarrow> without_preemption $ m_fault;
    case r_fault of
          Inl f \<Rightarrow>   without_preemption $ h_fault f
        | Inr a \<Rightarrow>   doE
            r_error \<leftarrow> without_preemption $ m_error a;
            case r_error of
                  Inl e \<Rightarrow>   without_preemption $ h_error e
                | Inr b \<Rightarrow>   m_finalise b
        odE
odE"


section \<open>System call entry point\<close>

text\<open>The kernel user can perform seven kinds of system calls,
described by the enumerated type @{term syscall}, defined in \autoref{s:spec_syscall}.
These seven system calls can be categorised into two broad
families: sending messages and receiving messages, the two main
services provided by the kernel.

The usual case for sending messages (@{text Send} event) consists of the user
sending a message to an object, without expecting any answer. The sender is
blocked until the receiver is waiting to receive. In case the
receiver is not trusted, an explicit non-blocking send operation can
be used (@{text NBSend} event). If a reply is requested from the
receiver, the Call operation can be used (@{text Call} event). The Call operation
will automatically provide a @{text Reply} capability to the receiver.

All three sending operations are handled by the @{text
handle_invocation} operation, which takes two boolean arguments, one
to indicate if a reply is requested and the other to indicate if the
send is blocking or not.

The other direction is the reception of messages. This is done by
performing a Recv operation on an endpoint kernel object. The receiver
is then blocked until a sender performs a Send operation on the
endpoint object, resulting in a message transfer between the sender
and the receiver. The receiver may also perform a Reply operation
(@{text Reply} event) in response to a @{text Call}, which is always
non-blocking. When the receiver is a user-level server, it generally
runs a loop waiting for messages. On handling a received message, the
server will send a reply and then return to waiting. To avoid
excessive switching between user and kernel mode, the kernel provides
a ReplyRecv operation, which is simply a Reply followed by Recv.

Finally, the last event, @{text Yield}, enables the user to donate its
remaining timeslice.\<close>

text\<open>The invocation is made up of three phases. The first phase
corresponds to a lookup of capabilities to check that the invocation
is valid. This phase can result in a fault if a given CSpace address
is invalid (see the function @{text "resolve_address_bits"}). The
second phase is the decoding of the arguments given by the user. This
is handled by the @{text decode_invocation} operation. This operation
can result in an error if, for example, the number of arguments is
less than required by the operation, or if some argument capability
has the wrong type. Finally, the actual invocation is performed, using
the @{text perform_invocation} function. Note that this last phase is
preemptable.
\<close>

fun
  perform_invocation :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> invocation \<Rightarrow> (data list, 'z::state_ext) p_monad"
where
  "perform_invocation _ _ _ (InvokeUntyped i) =
    doE
      invoke_untyped i;
      returnOk []
    odE"

| "perform_invocation block call can_donate (InvokeEndpoint ep badge can_grant can_grant_reply) =
    (without_preemption $ do
       thread \<leftarrow> gets cur_thread;
       send_ipc block call badge can_grant can_grant_reply can_donate thread ep;
       return []
     od)"

| "perform_invocation _ _ _ (InvokeNotification ep badge) =
    doE
      without_preemption $ send_signal ep badge;
      returnOk []
    odE"

| "perform_invocation _ _ _ (InvokeTCB i) = invoke_tcb i"

| "perform_invocation _ _ _ (InvokeDomain tptr d) = invoke_domain tptr d"

| "perform_invocation _ _ _ (InvokeReply reply grant) =
    liftE (do
      sender \<leftarrow> gets cur_thread;
      do_reply_transfer sender reply grant;
      return []
    od)"

| "perform_invocation _ _ _ (InvokeCNode i) =
    doE
      invoke_cnode i;
      returnOk []
    odE"

| "perform_invocation _ _ _ (InvokeIRQControl i) =
   doE
     invoke_irq_control i;
     returnOk []
   odE"

| "perform_invocation _ _ _ (InvokeIRQHandler i) =
   doE
     liftE $ invoke_irq_handler i;
     returnOk []
   odE"

| "perform_invocation _ _ _ (InvokeSchedContext i) =
   doE
     liftE $ invoke_sched_context i;
     returnOk []
   odE"

| "perform_invocation _ _ _ (InvokeSchedControl i) =
   doE
     liftE $ invoke_sched_control_configure_flags i;
     returnOk []
   odE"

| "perform_invocation _ _ _ (InvokeArchObject i) =
    arch_perform_invocation i"

definition
  get_cap_reg :: "register \<Rightarrow> (cap_ref, 'z::state_ext) s_monad"
where
  "get_cap_reg reg = do
    ct \<leftarrow> gets cur_thread;
    liftM data_to_cptr $ as_user ct $ getRegister reg
  od"

definition
  handle_invocation :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> cap_ref \<Rightarrow> (unit, 'z::state_ext) p_monad"
where
  "handle_invocation calling blocking can_donate first_phase cptr \<equiv> doE
    thread \<leftarrow> liftE $ gets cur_thread;
    info \<leftarrow> without_preemption $ get_message_info thread;
    syscall
      (doE
         (cap, slot) \<leftarrow> cap_fault_on_failure (of_bl cptr) False $
                           lookup_cap_and_slot thread cptr;
         buffer \<leftarrow> liftE $ lookup_ipc_buffer False thread;
         extracaps \<leftarrow> lookup_extra_caps thread buffer info;
         returnOk (slot, cap, extracaps, buffer)
       odE)
      (\<lambda>fault. when blocking $ handle_fault thread fault)
      (\<lambda>(slot,cap,extracaps,buffer). doE
            args \<leftarrow> liftE $ get_mrs thread buffer info;
            decode_invocation first_phase (mi_label info) args cptr slot cap extracaps buffer
       odE)
      (\<lambda>err. when calling $
            reply_from_kernel thread $ msg_from_syscall_error err)
      (\<lambda>oper. doE
            without_preemption $ set_thread_state thread Restart;
            reply \<leftarrow> perform_invocation blocking calling can_donate oper;
            without_preemption $ do
                state \<leftarrow> get_thread_state thread;
                case state of
                      Restart \<Rightarrow> do
                          when calling $
                              reply_from_kernel thread (0, reply);
                          set_thread_state thread Running
                      od
                    | _ \<Rightarrow>  return ()
            od
       odE)
  odE"


definition
  handle_yield :: "(unit, 'z::state_ext) s_monad" where
  "handle_yield \<equiv> do
     cur_sc \<leftarrow> gets cur_sc;
     sc \<leftarrow> get_sched_context cur_sc;
     sc_consumed \<leftarrow> return (sc_consumed sc);
     refills \<leftarrow> get_refills cur_sc;
     charge_budget (r_amount (hd refills)) False;
     set_sc_obj_ref sc_consumed_update cur_sc sc_consumed
 od"

definition
  handle_send :: "bool \<Rightarrow> (unit, 'z::state_ext) p_monad" where
  "handle_send bl \<equiv> doE
    cptr \<leftarrow> liftE $ get_cap_reg cap_register;
    handle_invocation False bl False False cptr
  odE"

definition
  handle_call :: "(unit, 'z::state_ext) p_monad" where
 "handle_call \<equiv>  doE
    cptr \<leftarrow> liftE $ get_cap_reg cap_register;
    handle_invocation True True True False cptr
  odE"

definition
  lookup_reply :: "(cap, 'z::state_ext) f_monad"
where
  "lookup_reply = doE
    cref \<leftarrow> liftE $ get_cap_reg replyRegister;
    ct \<leftarrow> liftE $ gets cur_thread;
    cap \<leftarrow> cap_fault_on_failure (of_bl cref) True $ lookup_cap ct cref;
    if is_reply_cap cap
    then returnOk cap
    else throwError $ CapFault (of_bl cref) True (MissingCapability 0)
  odE"

definition
  handle_recv :: "bool \<Rightarrow> bool \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "handle_recv is_blocking can_reply \<equiv> do
     thread \<leftarrow> gets cur_thread;

     ep_cptr \<leftarrow> liftM data_to_cptr $ as_user thread $
                 getRegister cap_register;

     doE
        ep_cap \<leftarrow> cap_fault_on_failure (of_bl ep_cptr) True (lookup_cap thread ep_cptr);

        let flt = throwError $ CapFault (of_bl ep_cptr) True (MissingCapability 0)
        in
        case ep_cap
          of EndpointCap ref badge rights \<Rightarrow> doE
               whenE (AllowRecv \<notin> rights) flt;
               reply_cap \<leftarrow> if can_reply then lookup_reply else returnOk NullCap;
               liftE $ receive_ipc thread ep_cap is_blocking reply_cap
             odE
           | NotificationCap ref badge rights \<Rightarrow>
             (if AllowRecv \<in> rights
              then doE
                boundTCB \<leftarrow> liftE $ get_ntfn_obj_ref ntfn_bound_tcb ref;
                if boundTCB = Some thread \<or> boundTCB = None
                then liftE $ receive_signal thread ep_cap is_blocking
                else flt
               odE
              else flt)
           | _ \<Rightarrow> flt
      odE
      <catch> handle_fault thread
   od"

section \<open>Top-level event handling\<close>

fun
  handle_event :: "event \<Rightarrow> (unit, 'z::state_ext) p_monad"
where
  "handle_event (SyscallEvent call) = doE
    liftE $ update_time_stamp;
    restart \<leftarrow> liftE $ check_budget_restart;
    whenE restart (case call of
          SysSend \<Rightarrow> handle_send True
        | SysNBSend \<Rightarrow> handle_send False
        | SysCall \<Rightarrow> handle_call
        | SysRecv \<Rightarrow> without_preemption $ handle_recv True True
        | SysYield \<Rightarrow> without_preemption handle_yield
        | SysReplyRecv \<Rightarrow> doE
            reply_cptr \<leftarrow> without_preemption $ get_cap_reg replyRegister;
            handle_invocation False False True True reply_cptr;
            without_preemption $ handle_recv True True
          odE
        | SysNBSendRecv \<Rightarrow> doE
            dest \<leftarrow> without_preemption $ get_cap_reg nbsendRecvDest;
            handle_invocation False False True True dest;
            without_preemption $ handle_recv True True
          odE
        | SysNBSendWait \<Rightarrow> doE
            reply_cptr \<leftarrow> without_preemption $ get_cap_reg replyRegister;
            handle_invocation False False True True reply_cptr;
            without_preemption $ handle_recv True False
          odE
        | SysWait \<Rightarrow> without_preemption $ handle_recv True False
        | SysNBWait \<Rightarrow> without_preemption $ handle_recv False False
        | SysNBRecv \<Rightarrow> without_preemption $ handle_recv False True)
  odE"

| "handle_event (UnknownSyscall n) = (without_preemption $ do
    update_time_stamp;
    restart \<leftarrow> check_budget_restart;
    when restart $ do
      thread \<leftarrow> gets cur_thread;
      handle_fault thread $ UnknownSyscallException $ of_nat n
    od
  od)"

| "handle_event (UserLevelFault w1 w2) = (without_preemption $ do
    update_time_stamp;
    restart \<leftarrow> check_budget_restart;
    when restart $ do
      thread \<leftarrow> gets cur_thread;
      handle_fault thread $ UserException (w1 && mask 32) (w2 && mask 28)
    od
  od)"

| "handle_event Interrupt = (without_preemption $ do
    active \<leftarrow> do_machine_op $ getActiveIRQ False;
    update_time_stamp;
    check_budget;
    case active of
       Some irq \<Rightarrow> handle_interrupt irq
     | None \<Rightarrow> return ()
  od)"

| "handle_event (VMFaultEvent fault_type) = (without_preemption $ do
    update_time_stamp;
    restart \<leftarrow> check_budget_restart;
    when restart $ do
      thread \<leftarrow> gets cur_thread;
      handle_vm_fault thread fault_type <catch> handle_fault thread
    od
  od)"

| "handle_event (HypervisorEvent hypfault_type) = (without_preemption $ do
    thread \<leftarrow> gets cur_thread;
    handle_hypervisor_fault thread hypfault_type
  od)"


section \<open>Kernel entry point\<close>

text \<open>
  This function is the main kernel entry point. The main event loop of the
  kernel handles events, handles a potential preemption interrupt, schedules
  and switches back to the active thread.
\<close>

definition preemption_path where
  "preemption_path \<equiv> do
      irq \<leftarrow> do_machine_op (getActiveIRQ True);
      when (irq = Some timerIRQ) update_time_stamp;
      ct \<leftarrow> gets cur_thread;
      schedulable \<leftarrow> is_schedulable ct;
      if schedulable then do check_budget;
                             return ()
                          od
      else do csc \<leftarrow> gets cur_sc;
              active \<leftarrow> get_sc_active csc;
              when active (do consumed \<leftarrow> gets consumed_time;
                              charge_budget consumed False
                           od)
           od;
      when (irq \<noteq> None) (handle_interrupt (the irq))
   od"

definition
  call_kernel :: "event \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "call_kernel ev \<equiv> do
       handle_event ev <handle> (\<lambda>_. without_preemption preemption_path);
       schedule;
       activate_thread
   od"

end