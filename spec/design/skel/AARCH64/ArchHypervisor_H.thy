(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  Hypervisor function definitions for AARCH64
*)

theory ArchHypervisor_H
imports
  CNode_H
  FaultHandlerDecls_H
  InterruptDecls_H
begin
context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Object/VCPU/AARCH64.hs CONTEXT AARCH64_H decls_only \
  ONLY countTrailingZeros irqVPPIEventIndex virqTypeShift eoiirqenShift
#INCLUDE_HASKELL SEL4/Object/VCPU/AARCH64.hs CONTEXT AARCH64_H bodies_only \
  ONLY countTrailingZeros irqVPPIEventIndex virqTypeShift eoiirqenShift
#INCLUDE_HASKELL SEL4/Object/VCPU/AARCH64.hs CONTEXT AARCH64_H ArchInv=Arch \
  ONLY vcpuUpdate vgicUpdate vgicUpdateLR vcpuSaveReg vcpuRestoreReg \
    vcpuSaveRegRange vcpuRestoreRegRange vcpuWriteReg vcpuReadReg saveVirtTimer \
    restoreVirtTimer vcpuDisable vcpuEnable vcpuRestore armvVCPUSave \
    vcpuSave vcpuSwitch vcpuFlush vcpuInvalidateActive vcpuCleanInvalidateActive \
    virqType virqSetEOIIRQEN vgicMaintenance vppiEvent curVCPUActive

#INCLUDE_HASKELL SEL4/Kernel/Hypervisor/AARCH64.hs Arch= CONTEXT AARCH64_H decls_only ArchInv= ArchLabels=
#INCLUDE_HASKELL SEL4/Kernel/Hypervisor/AARCH64.hs Arch= CONTEXT AARCH64_H bodies_only ArchInv= ArchLabels=

end
end
