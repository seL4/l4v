(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "VCPU"

theory VCPU_H
imports
  Hardware_H
  Structures_H
  Invocations_H
  TCB_H
begin
context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs CONTEXT ARM_HYP_H
#INCLUDE_HASKELL SEL4/Object/VCPU/ARM.lhs CONTEXT ARM_HYP_H ArchInv=Arch NOT vcpuUpdate vgicUpdate vgicUpdateLR vcpuSaveReg vcpuRestoreReg vcpuSaveRegRange vcpuRestoreRegRange vcpuWriteReg vcpuReadReg saveVirtTimer restoreVirtTimer vcpuDisable vcpuEnable vcpuRestore vcpuSave vcpuSwitch vcpuFlush vcpuInvalidateActive vcpuCleanInvalidateActive countTrailingZeros virqSetEOIIRQEN vgicMaintenance vppiEvent irqVPPIEventIndex armvVCPUSave

end
end
