(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Domain Scheduler"

theory Domain_H
imports
  Invocations_H
  ThreadDecls_H
  ArchDomain_H
begin

arch_requalify_consts (H)
  prepareSetDomain
  parseTimeArg

#INCLUDE_HASKELL SEL4/Object/Domain.hs Arch= NOT listUpdate

end
