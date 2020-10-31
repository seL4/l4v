(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
    VSpace lookup code.
*)

theory VSpace_H
imports
  CNode_H
  ArchVSpace_H
  KernelInitMonad_H
begin

context begin interpretation Arch .
requalify_consts
  mapKernelWindow
  activateGlobalVSpace
  configureTimer
  initL2Cache
  initIRQController

  createIPCBufferFrame
  createBIFrame
  createFramesOfRegion
  createITPDPTs
  writeITPDPTs
  createITASIDPool
  writeITASIDPool
  createDeviceFrames
  handleVMFault
  isValidVTableRoot
  checkValidIPCBuffer
  lookupIPCBuffer
  vptrFromPPtr
end

#INCLUDE_HASKELL SEL4/Kernel/VSpace.lhs Arch= ONLY initKernelVM initPlatform initCPU

end
