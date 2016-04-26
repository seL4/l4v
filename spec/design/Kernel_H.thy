(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Kernel"

theory Kernel_H
imports
  KernelInit_H
  Thread_H
  FaultHandler_H
  CSpace_H
begin

context Arch begin

requalify_types
  kernel_state

shadow_types
  kernel_state

shadow_facts
  deriveCap_def finaliseCap_def recycleCap_def
  hasRecycleRights_def sameRegionAs_def isPhysicalCap_def
  sameObjectAs_def updateCapData_def maskCapRights_def
  createObject_def capUntypedPtr_def capUntypedSize_def
  performInvocation_def decodeInvocation_def

end

end
