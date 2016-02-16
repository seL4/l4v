(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Function Declarations for Threads"

theory ThreadDecls_H
imports
  Structures_H
  FaultMonad_H
  KernelInitMonad_H
  "./$L4V_ARCH/ArchThreadDecls_H"
begin

#INCLUDE_HASKELL SEL4/Kernel/Thread.lhs decls_only NOT transferCapsToSlots

end
