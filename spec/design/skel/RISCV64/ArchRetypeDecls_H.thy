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

context Arch begin global_naming RISCV64_H

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures/RISCV64.hs

#INCLUDE_HASKELL SEL4/API/Invocation/RISCV64.hs CONTEXT RISCV64_H decls_only NOT Invocation IRQControlInvocation

#INCLUDE_HASKELL SEL4/API/Invocation/RISCV64.hs CONTEXT RISCV64_H decls_only ONLY Invocation IRQControlInvocation

#INCLUDE_HASKELL SEL4/Object/ObjectType/RISCV64.hs CONTEXT RISCV64_H Arch.Types=ArchTypes_H ArchInv= decls_only

end (*context RISCV64*)

end
