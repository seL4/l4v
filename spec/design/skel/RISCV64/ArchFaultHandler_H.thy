(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Fault Handlers"

theory ArchFaultHandler_H
imports TCB_H Structures_H
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL_PREPARSE SEL4/API/Failures/RISCV64.hs

#INCLUDE_HASKELL SEL4/API/Faults/RISCV64.hs decls_only
#INCLUDE_HASKELL SEL4/API/Faults/RISCV64.hs bodies_only

end

end
