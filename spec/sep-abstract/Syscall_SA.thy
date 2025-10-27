(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  Top-level system call interface of reduced kernel API.
*)

chapter "Separation Kernel Abstract Specification"

theory Syscall_SA
imports Decode_SA
begin

section "Introduction"

text \<open>

  The Separation Kernel maintains separation between processes by limiting the capabilities that are
  present in the system. We call these the "restricted capabilities" in the documentation that
  follows.

  The specification described here, the Separation Kernel Abstract Specification (abbreviated
  \texttt{sep-abstract} from here on in), is identical to the Abstract Specification
  (aka. \texttt{abstract}), except that the following system calls have been overridden to
  provide reduced (fully static) functionality only.

  \begin{itemize}
  \item{handle_fault}
  \item{invoke_irq_handler}
  \item{decode_invocation}
  \item{perform_invocation}
  \item{handle_invocation}
  \item{handle_reply}
  \item{handle_event}
  \item{call_kernel}
  \end{itemize}

  The resulting kernel API is simplified significantly compared to full seL4.
  The changes to the original abstract specification are minimal, except that it contains
  much fewer system calls.

  We achieve this by modifying the cases distinctions that determine which API call is
  to by executed. The new case distinctions
  on capabilities only provide code for the restricted capabilities in our reduced setup,
  otherwise they fail (i.e. throw an exception).

  We then prove that \texttt{sep-abstract} and \texttt{abstract} have the same behaviour under the
  restricted capabilities of the separation kernel via bi-simulation. This simply requires that we
  prove refinement in both directions. This proof implies that the missing (failing) code branches
  in the reduced specification can never be executed.

  It is clear that the behaviour will be the same for the "mostly identical" overridden
  definitions. In a few cases, which are documented below, the definitions have bigger differencess.
  We provide ab informal explanation at the site of the overriden definition in each of these
  cases. (The bi-simulation proof provides the formal demonstration.)

\<close>

section \<open>Generic system call structure\label{s:spec_syscall}\<close>

section \<open>System call entry point\<close>

fun
  perform_invocation :: "bool \<Rightarrow> bool \<Rightarrow> invocation \<Rightarrow> (data list,'z::state_ext) p_monad"
where
  "perform_invocation block call (InvokeNotification ep badge) =
    doE
      without_preemption $ send_signal ep badge;
      returnOk []
    odE"
| "perform_invocation _ _ _ = fail"

definition
  handle_invocation :: "bool \<Rightarrow> bool \<Rightarrow> (unit,'z::state_ext) p_monad"
where
  "handle_invocation calling blocking \<equiv> doE
    thread \<leftarrow> liftE $ gets cur_thread;
    info \<leftarrow> without_preemption $ get_message_info thread;
    ptr \<leftarrow> without_preemption $ liftM data_to_cptr $
          as_user thread $ getRegister cap_register;
    syscall
      (doE
         (cap, slot) \<leftarrow> cap_fault_on_failure (of_bl ptr) False $ lookup_cap_and_slot thread ptr;
         buffer \<leftarrow> liftE $ lookup_ipc_buffer False thread;
         extracaps \<leftarrow> lookup_extra_caps thread buffer info;
         returnOk (slot, cap, extracaps, buffer)
       odE)
      (\<lambda>fault. when blocking $ handle_fault thread fault)
      (\<lambda>(slot,cap,extracaps,buffer). doE
            args \<leftarrow> liftE $ get_mrs thread buffer info;
            decode_invocation (mi_label info) args ptr slot cap extracaps
       odE)
      (\<lambda>err. when calling $
            reply_from_kernel thread $ msg_from_syscall_error err)
      (\<lambda>oper. doE
            without_preemption $ set_thread_state thread Restart;
            reply \<leftarrow> perform_invocation blocking calling oper;
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
  handle_yield :: "(unit,'z::state_ext) s_monad" where
  "handle_yield \<equiv> do
     thread \<leftarrow> gets cur_thread;
     tcb_sched_action (tcb_sched_dequeue) thread;
     tcb_sched_action (tcb_sched_append) thread;
     reschedule_required
   od"

definition
  handle_send :: "bool \<Rightarrow> (unit,'z::state_ext) p_monad" where
  "handle_send bl \<equiv> handle_invocation False bl"

definition
  handle_call :: "(unit,'z::state_ext) p_monad" where
 "handle_call \<equiv> handle_invocation True True"

text \<open>

  This definition of \texttt{handle_recv} is almost identical to the abstract specification's definition
  for the restricted capabilities. Also, a call to \texttt{delete_caller_cap} has been removed. They have
  the same behaviour under the restricted capabilities since there are no caller capabilities in
  \texttt{sep-abstract}.

\<close>

definition
  handle_recv :: "bool \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "handle_recv is_blocking \<equiv> do
     thread \<leftarrow> gets cur_thread;

     ep_cptr \<leftarrow> liftM data_to_cptr $ as_user thread $
                 getRegister cap_register;

     (cap_fault_on_failure (of_bl ep_cptr) True $ doE
        ep_cap \<leftarrow> lookup_cap thread ep_cptr;

        let flt = (throwError $ MissingCapability 0)
        in
        case ep_cap
          of
            NotificationCap ref badge rights \<Rightarrow>
             (if AllowRecv \<in> rights
              then doE
                ntfn \<leftarrow> liftE $ get_notification ref;
                boundTCB \<leftarrow> returnOk $ ntfn_bound_tcb ntfn;
                if boundTCB = Some thread \<or> boundTCB = None
                then liftE $ receive_signal thread ep_cap is_blocking
                else flt
               odE
              else flt)
           | _ \<Rightarrow> flt
      odE)
      <catch> handle_fault thread
   od"

text \<open>

  The definition here has been specialised to \texttt{return ()}. The behaviour
  is identical with the abstract specification under restricted capabilities because there
  are no \texttt{Reply} capabilities in \texttt{sep-abstract}.

\<close>

definition
  handle_reply :: "(unit,'z::state_ext) s_monad" where
 "handle_reply \<equiv> return ()"

section \<open>Top-level event handling\<close>

text \<open>

  The definition here is almost identical to that of the abstract specification (for the restricted
  capablities), except that a call to \texttt{handle_reply} has been removed. Since there
  are no \texttt{Reply}s in the restricted capabilities the behaviour is the same.

\<close>


fun
  handle_event :: "event \<Rightarrow> (unit,'z::state_ext) p_monad"
where
  "handle_event (SyscallEvent call) =
   (case call of
          SysSend \<Rightarrow> handle_send True
        | SysNBSend \<Rightarrow> handle_send False
        | SysCall \<Rightarrow> handle_call
        | SysRecv \<Rightarrow> without_preemption $ handle_recv True
        | SysYield \<Rightarrow> without_preemption handle_yield
        | SysReply \<Rightarrow> without_preemption handle_reply
        | SysReplyRecv \<Rightarrow> without_preemption $ handle_recv True
        | SysNBRecv \<Rightarrow> without_preemption $ handle_recv False)"

| "handle_event (UnknownSyscall n) = (without_preemption $ do
    thread \<leftarrow> gets cur_thread;
    handle_fault thread $ UnknownSyscallException $ of_nat n;
    return ()
  od)"

| "handle_event (UserLevelFault w1 w2) = (without_preemption $ do
    thread \<leftarrow> gets cur_thread;
    handle_fault thread $ UserException w1 (w2 && mask 28);
    return ()
  od)"

| "handle_event Interrupt = (without_preemption $ do
    active \<leftarrow> do_machine_op (getActiveIRQ False);
    case active of
       Some irq \<Rightarrow> handle_interrupt irq
     | None \<Rightarrow> return ()
  od)"

| "handle_event (VMFaultEvent fault_type) = (without_preemption $ do
    thread \<leftarrow> gets cur_thread;
    handle_vm_fault thread fault_type <catch> handle_fault thread;
    return ()
  od)"

| "handle_event (HypervisorEvent fault_type) = (without_preemption $ do
    thread \<leftarrow> gets cur_thread;
    handle_hypervisor_fault thread fault_type;
    return ()
  od)"

section \<open>Kernel entry point\<close>

text \<open>
  This function is the main kernel entry point. The main event loop of the
  kernel handles events, handles a potential preemption interrupt, schedules
  and switches back to the active thread.
\<close>

definition
  call_kernel :: "event \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "call_kernel ev \<equiv> do
       handle_event ev <handle>
           (\<lambda>_. without_preemption $ do
                  irq \<leftarrow> do_machine_op (getActiveIRQ True);
                  when (irq \<noteq> None) $ handle_interrupt (the irq)
                od);
       schedule;
       activate_thread
   od"

end
