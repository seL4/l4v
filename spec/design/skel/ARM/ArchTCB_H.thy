(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchTCB_H
imports TCBDecls_H
begin
context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Object/TCB/ARM.lhs RegisterSet= CONTEXT ARM_H


#INCLUDE_HASKELL SEL4/Object/TCB.lhs Arch= ONLY archThreadGet archThreadSet

end
end
