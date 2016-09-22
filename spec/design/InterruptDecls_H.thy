(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file InterruptDecls_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory InterruptDecls_H
imports
  RetypeDecls_H
  Notification_H
  CNode_H
  KI_Decls_H
begin

consts'
decodeIRQControlInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> machine_word \<Rightarrow> capability list \<Rightarrow> ( syscall_error , irqcontrol_invocation ) kernel_f"

consts'
performIRQControl :: "irqcontrol_invocation \<Rightarrow> unit kernel_p"

consts'
decodeIRQHandlerInvocation :: "machine_word \<Rightarrow> irq \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , irqhandler_invocation ) kernel_f"

consts'
toBool :: "machine_word \<Rightarrow> bool"

consts'
invokeIRQHandler :: "irqhandler_invocation \<Rightarrow> unit kernel"

consts'
deletingIRQHandler :: "irq \<Rightarrow> unit kernel"

consts'
initInterruptController :: "capability \<Rightarrow> machine_word \<Rightarrow> capability kernel_init"

consts'
handleInterrupt :: "irq \<Rightarrow> unit kernel"

consts'
isIRQActive :: "irq \<Rightarrow> bool kernel"

consts'
setIRQState :: "irqstate \<Rightarrow> irq \<Rightarrow> unit kernel"

consts'
getIRQState :: "irq \<Rightarrow> irqstate kernel"

consts'
getIRQSlot :: "irq \<Rightarrow> (machine_word) kernel"


end
