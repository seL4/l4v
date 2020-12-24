(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Function Declarations for SchedContexts"

theory SchedContextDecls_H

imports
  FaultMonad_H
  Invocations_H

begin

#INCLUDE_HASKELL SEL4/Object/SchedContext.lhs decls_only NOT refillsMergePrefix minBudgetMerge refillsBudgetCheck refillHeadOverlappingLoop headInsufficientLoop

end
