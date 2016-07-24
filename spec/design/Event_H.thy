(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file Event_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Kernel Events"

theory Event_H
imports "../machine/MachineExports"
begin

text {*
  \label{sec:Event_H}
 
  These are the user-level and machine generated events the kernel reacts to.
*}

datatype syscall =
    SysCall
  | SysReplyRecv
  | SysSend
  | SysNBSend
  | SysRecv
  | SysReply
  | SysYield
  | SysNBRecv

datatype event =
    SyscallEvent syscall
  | UnknownSyscall nat
  | UserLevelFault machine_word machine_word
  | Interrupt
  | VMFaultEvent vmfault_type
  | HypervisorEvent hyp_fault_type


end
