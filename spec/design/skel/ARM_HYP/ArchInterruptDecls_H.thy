(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInterruptDecls_H
imports RetypeDecls_H CNode_H
begin

context Arch begin global_naming ARM_HYP_H

#INCLUDE_HASKELL SEL4/Object/Interrupt/ARM.lhs CONTEXT Arch decls_only ArchInv=

end

end
