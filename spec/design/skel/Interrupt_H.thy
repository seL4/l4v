(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Interrupt_H
imports
  RetypeDecls_H
  "./$L4V_ARCH/ArchInterrupt_H"
  Notification_H
  CNode_H
  KI_Decls_H
  InterruptDecls_H
begin

abbreviation (input)
  performIRQControl :: "Invocations_H.irqcontrol_invocation \<Rightarrow> unit kernel_p"
where
 "performIRQControl \<equiv> InterruptDecls_H.performIRQControl"

abbreviation (input)
  "decodeIRQControlInvocation"
  :: "32 word
      \<Rightarrow> 32 word list
         \<Rightarrow> 32 word
            \<Rightarrow> capability list
               \<Rightarrow> KernelStateData_H.kernel_state
                  \<Rightarrow> ((syscall_error + Invocations_H.irqcontrol_invocation) \<times> KernelStateData_H.kernel_state) set \<times> bool"
where
  "decodeIRQControlInvocation \<equiv> InterruptDecls_H.decodeIRQControlInvocation"

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs
#INCLUDE_HASKELL SEL4/Object/Interrupt.lhs Arch=ArchInterruptDecls_H bodies_only

end
