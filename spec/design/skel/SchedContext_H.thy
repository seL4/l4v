(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "SchedContexts"

theory SchedContext_H

imports
  SchedContextDecls_H
  TCBDecls_H
  ThreadDecls_H
  NotificationDecls_H
  Reply_H
  VSpace_H

begin

(* clobbers previously requalified abstract spec constants with design spec versions *)
arch_requalify_consts (aliasing, H)
  badgeRegister

context begin interpretation Arch .
requalify_consts
  kernelWCETTicks
  kernelWCETUs
  ticksToUs
  maxTicksToUs
  maxPeriodUs
end

#INCLUDE_HASKELL SEL4/Object/SchedContext.lhs bodies_only NOT workUnitsLimit

end
