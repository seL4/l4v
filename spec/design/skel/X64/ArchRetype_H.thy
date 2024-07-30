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
  KI_Decls_H
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Object/ObjectType/X64.lhs CONTEXT X64_H Arch.Types=ArchTypes_H ArchInv=ArchRetypeDecls_H NOT bodies_only
#INCLUDE_HASKELL SEL4/API/Invocation/X64.lhs CONTEXT X64_H bodies_only

end (* context X64 *)
end
