(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Function Declarations for CSpace"

theory CSpaceDecls_H
imports FaultMonad_H
begin

#INCLUDE_HASKELL SEL4/Kernel/CSpace.lhs decls_only

end
