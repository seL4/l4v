(*
 * Copyright 2024, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "FPU"

theory FPU_H
imports
  Hardware_H
  TCBDecls_H
begin
context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Object/FPU/X64.hs CONTEXT X64_H decls_only ArchInv=Arch ONLY fpuOwner_asrt

#INCLUDE_HASKELL SEL4/Object/FPU/X64.hs CONTEXT X64_H ArchInv=Arch NOT fpuOwner_asrt

end
end
