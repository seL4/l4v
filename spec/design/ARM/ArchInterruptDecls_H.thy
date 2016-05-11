(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchInterruptDecls_H
imports "../RetypeDecls_H" "../CNode_H" 
begin

context Arch begin global_naming ARM_H

consts'
decodeIRQControlInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> machine_word \<Rightarrow> capability list \<Rightarrow> ( syscall_error , irqcontrol_invocation ) kernel_f"

consts'
performIRQControl :: "irqcontrol_invocation \<Rightarrow> unit kernel_p"

consts'
checkIRQ :: "machine_word \<Rightarrow> ( syscall_error , unit ) kernel_f"


end

end
