(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  VSpace lookup code.
*)

theory ArchHypervisor_H
imports
  CNode_H
  FaultHandlerDecls_H
  InterruptDecls_H
begin
context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Object/VCPU/ARM.lhs CONTEXT ARM_HYP_H decls_only ONLY countTrailingZeros irqVPPIEventIndex
#INCLUDE_HASKELL SEL4/Object/VCPU/ARM.lhs CONTEXT ARM_HYP_H bodies_only ONLY countTrailingZeros irqVPPIEventIndex

#INCLUDE_HASKELL SEL4/Object/VCPU/ARM.lhs CONTEXT ARM_HYP_H ArchInv=Arch ONLY vcpuUpdate vgicUpdate vgicUpdateLR vcpuSaveReg vcpuRestoreReg vcpuSaveRegRange vcpuRestoreRegRange vcpuWriteReg vcpuReadReg saveVirtTimer restoreVirtTimer vcpuDisable vcpuEnable vcpuRestore armvVCPUSave vcpuSave vcpuSwitch vcpuInvalidateActive vcpuCleanInvalidateActive virqSetEOIIRQEN vgicMaintenance vppiEvent

#INCLUDE_HASKELL SEL4/Kernel/Hypervisor/ARM.lhs Arch= CONTEXT ARM_HYP_H decls_only
#INCLUDE_HASKELL SEL4/Kernel/Hypervisor/ARM.lhs Arch= CONTEXT ARM_HYP_H bodies_only

end
end
