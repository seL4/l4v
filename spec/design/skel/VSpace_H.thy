(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
	VSpace lookup code.
*)

theory VSpace_H
imports
  CNode_H
  "./$L4V_ARCH/ArchVSpace_H"
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
