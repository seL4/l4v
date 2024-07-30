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

#INCLUDE_HASKELL SEL4/Object/ObjectType/RISCV64.hs CONTEXT RISCV64_H Arch.Types=ArchTypes_H ArchInv=ArchRetypeDecls_H NOT bodies_only
#INCLUDE_HASKELL SEL4/API/Invocation/RISCV64.hs CONTEXT RISCV64_H bodies_only

end (* context RISCV64 *)
end
