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
	Declarations from SEL4.Kernel.Thread.
*)

chapter "Function Declarations for Threads"

theory ArchThreadDecls_H
imports
  "../Structures_H"
  "../FaultMonad_H"
  "../KernelInitMonad_H"
begin
(* FIXME: Clagged from ARM version *)

context X64 begin

#INCLUDE_HASKELL SEL4/Kernel/Thread/X64.lhs CONTEXT X64 decls_only

end (* context X64 *)

end
