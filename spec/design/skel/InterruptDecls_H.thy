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

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs
#INCLUDE_HASKELL SEL4/Object/Interrupt.lhs Arch=ArchInterrupt_H decls_only NOT deletedIRQHandler

end
