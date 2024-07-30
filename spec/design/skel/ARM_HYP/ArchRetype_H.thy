(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Retyping Objects"

theory ArchRetype_H
imports
  ArchRetypeDecls_H
  ArchVSpaceDecls_H
  Hardware_H
  VCPU_H
  KI_Decls_H
begin
context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Object/ObjectType/ARM.lhs CONTEXT ARM_HYP_H Arch.Types= ArchInv= bodies_only
#INCLUDE_HASKELL SEL4/API/Invocation/ARM.lhs bodies_only CONTEXT ARM_HYP_H NOT isPDFlushLabel isPageFlushLabel

end
end
