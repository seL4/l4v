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
imports "../RetypeDecls_H" "../CNode_H" "../InterruptDecls_H" ArchInterruptDecls_H
begin

defs decodeIRQControlInvocation_def:
"decodeIRQControlInvocation arg1 arg2 arg3 arg4 \<equiv> throw IllegalOperation"

defs performIRQControl_def:
"performIRQControl arg1 \<equiv> haskell_fail []"


end
