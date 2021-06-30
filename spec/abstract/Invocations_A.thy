(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Data types for syscall invocations
*)

chapter "Kernel Object Invocations"

theory Invocations_A
imports "./$L4V_ARCH/ArchInvocation_A"
begin

context begin interpretation Arch .

requalify_types
  arch_copy_register_sets
  arch_irq_control_invocation
  arch_invocation

end

text \<open>These datatypes encode the arguments to the available system calls.\<close>

datatype cnode_invocation =
    InsertCall cap cslot_ptr cslot_ptr
  | MoveCall cap cslot_ptr cslot_ptr
  | RevokeCall cslot_ptr
  | DeleteCall cslot_ptr
  | RotateCall cap cap cslot_ptr cslot_ptr cslot_ptr
  | CancelBadgedSendsCall cap

datatype untyped_invocation =
    Retype cslot_ptr bool obj_ref obj_ref apiobject_type nat "cslot_ptr list" bool

datatype tcb_invocation =
    WriteRegisters machine_word bool "machine_word list" arch_copy_register_sets
  | ReadRegisters machine_word bool machine_word arch_copy_register_sets
  | CopyRegisters machine_word machine_word bool bool bool bool arch_copy_register_sets
  | ThreadControlCaps machine_word cslot_ptr
                      (tc_new_fault_handler: "(cap * cslot_ptr) option")
                      (tc_new_timeout_handler: "(cap * cslot_ptr) option")
                      (tc_new_croot: "(cap * cslot_ptr) option")
                      (tc_new_vroot: "(cap * cslot_ptr) option")
                      (tc_new_buffer: "(vspace_ref * (cap * cslot_ptr) option) option")
  | ThreadControlSched machine_word cslot_ptr
                       (tc_new_fault_handler: "(cap * cslot_ptr) option")
                       (tc_new_mcpriority: "(word8 * obj_ref) option")
                       (tc_new_priority: "(word8 * obj_ref) option")
                       (tc_new_sc: "obj_ref option option")
  | Suspend "obj_ref"
  | Resume "obj_ref"
  | NotificationControl "obj_ref" "obj_ref option"
  | SetTLSBase obj_ref machine_word

datatype sched_context_invocation =
    InvokeSchedContextConsumed obj_ref "obj_ref option"
  | InvokeSchedContextBind obj_ref cap
  | InvokeSchedContextUnbindObject obj_ref cap
  | InvokeSchedContextUnbind obj_ref
  | InvokeSchedContextYieldTo obj_ref "obj_ref option"

datatype sched_control_invocation =
    InvokeSchedControlConfigureFlags obj_ref ticks ticks nat badge data

datatype irq_control_invocation =
    IRQControl irq cslot_ptr cslot_ptr
  | ArchIRQControl arch_irq_control_invocation

datatype irq_handler_invocation =
    ACKIrq irq
  | SetIRQHandler irq cap cslot_ptr
  | ClearIRQHandler irq

datatype invocation =
    InvokeUntyped untyped_invocation
  | InvokeEndpoint obj_ref machine_word bool bool
  | InvokeNotification obj_ref machine_word
  | InvokeReply obj_ref bool
  | InvokeTCB tcb_invocation
  | InvokeDomain obj_ref word8
  | InvokeSchedContext sched_context_invocation
  | InvokeSchedControl sched_control_invocation
  | InvokeCNode cnode_invocation
  | InvokeIRQControl irq_control_invocation
  | InvokeIRQHandler irq_handler_invocation
  | InvokeArchObject arch_invocation

end
