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
imports "../machine/$L4V_ARCH/MachineTypes"
begin

text {*
  \label{sec:Event_H}
 
  These are the user-level and machine generated events the kernel reacts to.
*}

datatype syscall =
    SysSend
  | SysNBSend
  | SysCall
  | SysRecv
  | SysReply
  | SysReplyRecv
  | SysYield
  | SysNBRecv

datatype event =
    SyscallEvent syscall
  | UnknownSyscall nat
  | UserLevelFault machine_word machine_word
  | Interrupt
  | VMFaultEvent vmfault_type


end
