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
decodeInterruptControl :: "machine_word list \<Rightarrow> capability list \<Rightarrow> ( syscall_error , interrupt_control ) kernel_f"
where
"decodeInterruptControl arg1 arg2 \<equiv> throw IllegalOperation"

definition
invokeInterruptControl :: "interrupt_control \<Rightarrow> unit kernel_p"
where
"invokeInterruptControl arg1 \<equiv> haskell_fail []"


end
