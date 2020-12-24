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

context begin interpretation Arch .
requalify_consts
  kernelWCETTicks
  kernelWCETUs
  ticksToUs
  maxTicksToUs
  getCurrentTime
end

definition refillHeadOverlappingLoop_def:
"refillHeadOverlappingLoop scPtr = whileLoop (\<lambda>_ s. the (fun_of_m (refillHeadOverlapping scPtr) s)) (\<lambda>_. mergeRefills scPtr) ()"

definition headInsufficientLoop_def:
"headInsufficientLoop scPtr = whileLoop (\<lambda>_ s. the (fun_of_m (refillHdInsufficient scPtr) s)) (\<lambda>_. nonOverlappingMergeRefills scPtr) ()"

#INCLUDE_HASKELL SEL4/Object/SchedContext.lhs bodies_only NOT refillHeadOverlappingLoop headInsufficientLoop

end
