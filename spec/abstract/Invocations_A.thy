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
Data types for syscall invocations
*)

header "Kernel Object Invocations"

theory Invocations_A
imports ArchInvocation_A
begin

text {* These datatypes encode the arguments to the available system calls. *}

datatype cnode_invocation =
    InsertCall cap cslot_ptr cslot_ptr
  | MoveCall cap cslot_ptr cslot_ptr
  | RevokeCall cslot_ptr
  | DeleteCall cslot_ptr
  | RotateCall cap cap cslot_ptr cslot_ptr cslot_ptr
  | SaveCall cslot_ptr
  | RecycleCall cslot_ptr 

datatype untyped_invocation =
    Retype cslot_ptr obj_ref obj_ref apiobject_type nat "cslot_ptr list"

datatype arm_copy_register_sets =
    ARMNoExtraRegisters

datatype tcb_invocation =
    WriteRegisters word32 bool "word32 list" arm_copy_register_sets
  | ReadRegisters word32 bool word32 arm_copy_register_sets
  | CopyRegisters word32 word32 bool bool bool bool arm_copy_register_sets
  | ThreadControl word32 cslot_ptr "cap_ref option" "word8 option"
                  "(cap * cslot_ptr) option" "(cap * cslot_ptr) option"
                  "(vspace_ref * (cap * cslot_ptr) option) option"
  | Suspend "word32"
  | Resume "word32"

datatype irq_control_invocation =
    IRQControl irq cslot_ptr cslot_ptr
  | InterruptControl arch_interrupt_control

datatype irq_handler_invocation =
    ACKIrq irq
  | SetIRQHandler irq cap cslot_ptr
  | ClearIRQHandler irq
  | SetMode irq bool bool

datatype invocation =
    InvokeUntyped untyped_invocation
  | InvokeEndpoint obj_ref word32 bool
  | InvokeAsyncEndpoint obj_ref word32 word32
  | InvokeReply obj_ref cslot_ptr
  | InvokeTCB tcb_invocation
  | InvokeDomain obj_ref word8
  | InvokeCNode cnode_invocation
  | InvokeIRQControl irq_control_invocation
  | InvokeIRQHandler irq_handler_invocation
  | InvokeArchObject arch_invocation

end
