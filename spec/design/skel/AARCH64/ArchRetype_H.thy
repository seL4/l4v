(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Retyping Objects"

theory ArchRetype_H
imports
  ArchRetypeDecls_H
  ArchVSpaceDecls_H
  ArchInterruptDecls_H
  Hardware_H
  KI_Decls_H
  VCPU_H
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Object/ObjectType/AARCH64.hs CONTEXT AARCH64_H Arch.Types=ArchTypes_H ArchInv=ArchRetypeDecls_H NOT bodies_only
#INCLUDE_HASKELL SEL4/API/Invocation/AARCH64.hs CONTEXT AARCH64_H bodies_only \
  NOT isVSpaceFlushLabel isPageFlushLabel

end (* context AARCH64 *)
end
