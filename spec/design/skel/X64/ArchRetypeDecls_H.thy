(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Retyping Objects"

theory ArchRetypeDecls_H
imports
  "../FaultMonad_H"
  "../EndpointDecls_H"
  "../KernelInitMonad_H"
  "../PSpaceFuns_H"
  ArchObjInsts_H
begin

context X64 begin

#INCLUDE_HASKELL SEL4/API/Invocation/X64.lhs CONTEXT X64 decls_only
#INCLUDE_HASKELL SEL4/Object/ObjectType/X64.lhs CONTEXT X64 Arch.Types=ArchTypes_H ArchInv=ArchRetypeDecls_H decls_only

end (context X64)

end
