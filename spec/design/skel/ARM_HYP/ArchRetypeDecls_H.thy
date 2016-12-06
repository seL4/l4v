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
  ArchLabelFuns_H
  "../FaultMonad_H"
  "../EndpointDecls_H"
  "../KernelInitMonad_H"
  "../PSpaceFuns_H"
  ArchObjInsts_H
begin
context Arch begin global_naming ARM_HYP_H

#INCLUDE_HASKELL SEL4/API/Invocation/ARM_HYP.lhs CONTEXT ARM_HYP_H decls_only NOT isPageFlushLabel isPDFlushLabel Invocation IRQControlInvocation CopyRegisterSets

#INCLUDE_HASKELL SEL4/API/Invocation/ARM_HYP.lhs CONTEXT ARM_HYP_H decls_only ONLY Invocation IRQControlInvocation CopyRegisterSets

#INCLUDE_HASKELL SEL4/Object/ObjectType/ARM_HYP.lhs CONTEXT ARM_HYP_H Arch.Types=ArchTypes_H ArchInv= decls_only

end
end
