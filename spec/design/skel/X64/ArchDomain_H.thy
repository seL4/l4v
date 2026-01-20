(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDomain_H
imports
  FPU_H
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Object/Domain/X64.hs

end
end
