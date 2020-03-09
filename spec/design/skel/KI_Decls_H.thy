(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Initialisation"

theory KI_Decls_H
imports
  ThreadDecls_H
  KernelInitMonad_H
begin

#INCLUDE_HASKELL SEL4/Kernel/Init.lhs decls_only NOT isAligned funArray newKernelState distinct rangesBy doKernelOp runInit

end
