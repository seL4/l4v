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
imports ArchInvocation_A
begin

arch_requalify_types (A)
  arch_copy_register_sets
  arch_irq_control_invocation
  arch_invocation

text \<open>These datatypes encode the arguments to the available system calls.\<close>

datatype cnode_invocation =
    InsertCall cap cslot_ptr cslot_ptr
  | MoveCall cap cslot_ptr cslot_ptr
  | RevokeCall cslot_ptr
  | DeleteCall cslot_ptr
  | RotateCall cap cap cslot_ptr cslot_ptr cslot_ptr
  | SaveCall cslot_ptr
  | CancelBadgedSendsCall cap

datatype untyped_invocation =
    Retype cslot_ptr bool obj_ref obj_ref apiobject_type nat "cslot_ptr list" bool

datatype tcb_invocation =
    WriteRegisters machine_word bool "machine_word list" arch_copy_register_sets
  | ReadRegisters machine_word bool machine_word arch_copy_register_sets
  | CopyRegisters machine_word machine_word bool bool bool bool arch_copy_register_sets
  | ThreadControl (tc_target: machine_word) (tc_slot: cslot_ptr)
                  (tc_new_fault_ep: "cap_ref option")
                  (tc_new_mcpriority: "(word8 * obj_ref) option")
                  (tc_new_priority: "(word8 * obj_ref) option")
                  (tc_new_croot: "(cap * cslot_ptr) option")
                  (tc_new_vroot: "(cap * cslot_ptr) option")
                  (tc_new_buffer: "(vspace_ref * (cap * cslot_ptr) option) option")
  | Suspend "obj_ref"
  | Resume "obj_ref"
  | NotificationControl "obj_ref" "obj_ref option"
  | SetTLSBase obj_ref machine_word
  | SetFlags obj_ref tcb_flags tcb_flags

datatype irq_control_invocation =
    IRQControl irq cslot_ptr cslot_ptr
  | ArchIRQControl arch_irq_control_invocation

datatype irq_handler_invocation =
    ACKIrq irq
  | SetIRQHandler irq cap cslot_ptr
  | ClearIRQHandler irq

datatype domain_invocation =
    InvokeDomainSet (dom_thread : obj_ref) (dom_domain : domain)
  | InvokeDomainScheduleSetStart (dom_index : nat)
  | InvokeDomainScheduleConfigure (dom_index : nat)
                                  (dom_domain : domain)
                                  (dom_duration : domain_duration)

datatype invocation =
    InvokeUntyped untyped_invocation
  | InvokeEndpoint obj_ref machine_word bool bool
  | InvokeNotification obj_ref machine_word
  | InvokeReply obj_ref cslot_ptr bool
  | InvokeTCB tcb_invocation
  | InvokeDomain domain_invocation
  | InvokeCNode cnode_invocation
  | InvokeIRQControl irq_control_invocation
  | InvokeIRQHandler irq_handler_invocation
  | InvokeArchObject arch_invocation

end
