(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * System calls
 *)

theory Syscall_D
imports
  Schedule_D
  Decode_D
  "ExecSpec.Event_H"
begin

(*
 * Perform system calls.
 *
 * Each system call is broken into three stages:
 *
 *   (1) Cap validation, where we ensure that all caps passed
 *       into the system call are valid;
 *
 *   (2) Argument validation, where we ensure that the requested
 *       operation is valid and permitted; and
 *
 *   (3) Syscall execution, where we carry out the actual
 *       operation.
 *
 * For this function, the user passes us in 5 functions:
 *
 *   (1, 2) A cap validation function, and an error handler;
 *   (3, 4) A argument validation function, and an error handler;
 *   (5)    A syscall execution function.
 *
 * This function returns an item of type "'c", and may also
 * return an exception if operation (3) above was preempted
 * by an interrupt.
 *)

definition
syscall :: "
  ('a fault_monad) \<Rightarrow> (unit k_monad) \<Rightarrow>
  ('a \<Rightarrow> 'b except_monad) \<Rightarrow> (unit k_monad) \<Rightarrow>
  ('b \<Rightarrow> unit preempt_monad) \<Rightarrow> unit preempt_monad"
where
  "syscall
      cap_decoder_fn decode_error_handler_fn
      arg_decode_fn arg_error_handler_fn
      perform_syscall_fn \<equiv>
    cap_decoder_fn
    <handle>
      (\<lambda> _. liftE $ decode_error_handler_fn)
    <else>
      (\<lambda> a. ((arg_decode_fn a)
        <handle>
          (\<lambda> _. liftE $ arg_error_handler_fn)
        <else>
          perform_syscall_fn))
  "

fun
  perform_invocation :: "bool \<Rightarrow> bool \<Rightarrow> cdl_invocation \<Rightarrow> unit preempt_monad"
where
    "perform_invocation is_call can_block (InvokeUntyped untyped_params) = (invoke_untyped untyped_params)"
  | "perform_invocation is_call can_block (InvokeEndpoint endpoint_params) = liftE (invoke_endpoint is_call can_block endpoint_params)"
  | "perform_invocation is_call can_block (InvokeNotification ntfn_params) = liftE (invoke_notification ntfn_params)"
  | "perform_invocation is_call can_block (InvokeReply reply_params) = liftE (invoke_reply reply_params)"
  | "perform_invocation is_call can_block (InvokeTcb tcb_params) = (invoke_tcb tcb_params)"
  | "perform_invocation is_call can_block (InvokeDomain domain_params) = (invoke_domain domain_params)"
  | "perform_invocation is_call can_block (InvokeCNode cnode_params) = invoke_cnode cnode_params"
  | "perform_invocation is_call can_block (InvokeIrqControl irq_params) = liftE (invoke_irq_control irq_params)"
  | "perform_invocation is_call can_block (InvokeIrqHandler handler_params) = liftE (invoke_irq_handler handler_params)"
  | "perform_invocation is_call can_block (InvokePageTable page_table_params) = liftE (invoke_page_table page_table_params)"
  | "perform_invocation is_call can_block (InvokePage page_params) = liftE (invoke_page page_params)"
  | "perform_invocation is_call can_block (InvokeAsidControl asid_control_params) = liftE (invoke_asid_control asid_control_params)"
  | "perform_invocation is_call can_block (InvokeAsidPool asid_pool_params) = liftE (invoke_asid_pool asid_pool_params)"
  | "perform_invocation is_call can_block (InvokePageDirectory page_dir_params) = liftE (invoke_page_directory page_dir_params)"
  | "perform_invocation is_call can_block (InvokeSGISignal sig_params) = liftE (invoke_sgi_signal_generate sig_params)"

definition ep_related_cap :: "cdl_cap \<Rightarrow> bool"
where "ep_related_cap cap \<equiv> case cap of
 cdl_cap.EndpointCap o_id badge rights \<Rightarrow> True
| cdl_cap.NotificationCap o_id badge rights \<Rightarrow> True
| cdl_cap.ReplyCap o_id rights \<Rightarrow> True
\<comment> \<open>these are like EP caps in the sense that their syscall has no intent argument or label:\<close>
| cdl_cap.SGISignalCap irq target \<Rightarrow> True
| _ \<Rightarrow> False"

definition "has_restart_cap \<equiv> \<lambda>tcb_id. do
  t \<leftarrow> get_thread tcb_id;
  return ((cdl_tcb_caps t) tcb_pending_op_slot = Some cdl_cap.RestartCap)
  od"

definition
  handle_invocation :: "bool \<Rightarrow> bool \<Rightarrow> unit preempt_monad"
where
  "handle_invocation is_call can_block \<equiv>
    doE
      thread_ptr \<leftarrow> liftE $ gets_the cdl_current_thread;
      thread \<leftarrow> liftE $ get_thread thread_ptr;
      full_intent \<leftarrow> returnOk $ cdl_tcb_intent thread;

      intent \<leftarrow> returnOk $ cdl_intent_op full_intent;
      invoked_cptr \<leftarrow> returnOk $ cdl_intent_cap full_intent;
      extra_cap_cptrs \<leftarrow> returnOk $ cdl_intent_extras full_intent;

      syscall
        \<comment> \<open>Lookup all caps presented.\<close>
        (doE
          (cap, cap_ref) \<leftarrow> lookup_cap_and_slot thread_ptr invoked_cptr;
          extra_caps \<leftarrow> lookup_extra_caps thread_ptr extra_cap_cptrs;
          returnOk (cap, cap_ref, extra_caps)
        odE)
        \<comment> \<open>If that failed, send off a fault IPC (if we did a blocking operation).\<close>
        (when can_block $ handle_fault)

        \<comment> \<open>Decode the user's intent.\<close>
        (\<lambda> (cap, cap_ref, extra_caps).
          case intent of
              None \<Rightarrow> (if ep_related_cap cap then
                decode_invocation cap cap_ref extra_caps undefined
                else throw)
            | Some intent' \<Rightarrow>
                decode_invocation cap cap_ref extra_caps intent')

        \<comment> \<open>If that stuffed up, we do nothing more than corrupt the frames.\<close>
        (do corrupt_ipc_buffer thread_ptr True;
            when is_call (mark_tcb_intent_error thread_ptr True)
         od)

        \<comment> \<open>Invoke the system call.\<close>
        (\<lambda> inv. doE
            liftE $ set_cap (thread_ptr,tcb_pending_op_slot) RestartCap;
            perform_invocation is_call can_block inv;
            restart \<leftarrow> liftE $ has_restart_cap thread_ptr;
            whenE restart $ liftE (do
                       corrupt_ipc_buffer thread_ptr True;
                       when (is_call) (mark_tcb_intent_error thread_ptr False);
                       set_cap (thread_ptr,tcb_pending_op_slot) RunningCap
            od)
            odE)
  odE
  "

definition
  handle_recv :: "unit k_monad"
where
  "handle_recv \<equiv>
    do
      \<comment> \<open>Get the current thread.\<close>
      tcb_id \<leftarrow> gets_the cdl_current_thread;
      tcb \<leftarrow> get_thread tcb_id;
      \<comment> \<open>Get the endpoint it is trying to receive from.\<close>
      (doE
        ep_cptr \<leftarrow> returnOk $ cdl_intent_cap (cdl_tcb_intent tcb);
        ep_cap \<leftarrow> lookup_cap tcb_id ep_cptr;
        (case ep_cap of
          EndpointCap o_id badge rights \<Rightarrow>
            if Read \<in> rights then
              (liftE $ do
                   delete_cap_simple (tcb_id, tcb_caller_slot);
                   receive_ipc tcb_id (cap_object ep_cap) (Grant \<in> rights)
                od) \<sqinter> throw
            else
              throw
        | NotificationCap o_id badge rights \<Rightarrow>
            if Read \<in> rights then
              (liftE $ recv_signal tcb_id ep_cap) \<sqinter> throw
            else
              throw
        | _ \<Rightarrow>
            throw)
      odE)
      <catch>
        (\<lambda> _. handle_fault)
    od
  "

definition
  handle_reply :: "unit k_monad"
where
  "handle_reply \<equiv>
    do
      tcb_id \<leftarrow> gets_the cdl_current_thread;
      caller_cap \<leftarrow> get_cap (tcb_id, tcb_caller_slot);

      case caller_cap of
          ReplyCap target rights \<Rightarrow> do_reply_transfer tcb_id target (tcb_id, tcb_caller_slot) (Grant \<in> rights)
        | NullCap \<Rightarrow> return ()
        | _ \<Rightarrow> fail
    od
  "

definition handle_hypervisor_fault :: "unit k_monad"
where "handle_hypervisor_fault \<equiv> return ()"

definition
  handle_syscall :: "syscall \<Rightarrow> unit preempt_monad"
where
  "handle_syscall sys \<equiv>
    case sys of
      SysSend  \<Rightarrow> handle_invocation False True
    | SysNBSend \<Rightarrow> handle_invocation False False
    | SysCall \<Rightarrow> handle_invocation True True
    | SysRecv \<Rightarrow> liftE $ handle_recv
    | SysYield \<Rightarrow> returnOk ()
    | SysReply \<Rightarrow> liftE $ handle_reply
    | SysReplyRecv \<Rightarrow> liftE $ do
        handle_reply;
        handle_recv
      od
    | SysNBRecv \<Rightarrow> liftE $ handle_recv"

definition
  handle_event :: "event \<Rightarrow> unit preempt_monad"
where
  "handle_event ev \<equiv> case ev of
      SyscallEvent sys \<Rightarrow> handle_syscall sys
    | UnknownSyscall n \<Rightarrow> liftE $ handle_fault
    | UserLevelFault a b \<Rightarrow> liftE $ handle_fault
    | VMFaultEvent c \<Rightarrow> liftE $ handle_fault
    | Interrupt \<Rightarrow> liftE $ handle_pending_interrupts
    | HypervisorEvent w \<Rightarrow> liftE $ handle_hypervisor_fault
    "

definition
  call_kernel :: "event \<Rightarrow> unit k_monad"
where
  "call_kernel ev \<equiv>
    do
      \<comment> \<open>Deal with the event.\<close>
      handle_event ev
        <handle> (\<lambda> _. liftE handle_pending_interrupts);
      schedule;
      t \<leftarrow> gets cdl_current_thread;
      case t of Some thread \<Rightarrow> do
       restart \<leftarrow> has_restart_cap thread;
       when restart $ set_cap (thread, tcb_pending_op_slot) RunningCap
      od | None \<Rightarrow> return ()
    od"

end
