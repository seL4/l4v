(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Function Declarations for Retyping Objects"

theory RetypeDecls_H
imports
  "./$L4V_ARCH/ArchRetypeDecls_H"
  Structures_H
  FaultMonad_H
  Invocations_H
begin

#INCLUDE_HASKELL SEL4/Object/ObjectType.lhs decls_only

#INCLUDE_HASKELL SEL4/Object/Interrupt.lhs decls_only ONLY deletedIRQHandler

end
