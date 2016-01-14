(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchInterrupt_H
imports RetypeDecls_H
begin

definition
decodeIRQControlInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> machine_word \<Rightarrow> capability list \<Rightarrow> ( syscall_error , ArchRetypeDecls_H.irqcontrol_invocation ) kernel_f"
where
"decodeIRQControlInvocation arg1 arg2 arg3 arg4 \<equiv> throw IllegalOperation"

definition
invokeIRQControl :: "ArchRetypeDecls_H.irqcontrol_invocation \<Rightarrow> unit kernel_p"
where
"invokeIRQControl arg1 \<equiv> haskell_fail []"


end
