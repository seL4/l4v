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

context X64 begin

#INCLUDE_HASKELL SEL4/Object/Interrupt/X64.lhs CONTEXT X64 bodies_only ArchInv=ArchRetypeDecls_H Arch=MachineOps

end (* context X64 *)

end
