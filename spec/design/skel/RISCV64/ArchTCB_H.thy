(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchTCB_H
imports TCBDecls_H
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Object/TCB/RISCV64.hs RegisterSet= CONTEXT RISCV64_H

#INCLUDE_HASKELL SEL4/Object/TCB.lhs Arch= ONLY archThreadGet archThreadSet

end
end
