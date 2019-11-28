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

theory ArchHypervisor_H
imports
  "../CNode_H"
  "../FaultHandlerDecls_H"
  "../InterruptDecls_H"
begin
context Arch begin global_naming ARM_HYP_H

#INCLUDE_HASKELL SEL4/Object/VCPU/ARM.lhs CONTEXT ARM_HYP_H decls_only ONLY countTrailingZeros irqVPPIEventIndex
#INCLUDE_HASKELL SEL4/Object/VCPU/ARM.lhs CONTEXT ARM_HYP_H bodies_only ONLY countTrailingZeros irqVPPIEventIndex

#INCLUDE_HASKELL SEL4/Object/VCPU/ARM.lhs CONTEXT ARM_HYP_H ArchInv=Arch ONLY vcpuUpdate vgicUpdate vgicUpdateLR vcpuSaveReg vcpuRestoreReg vcpuSaveRegRange vcpuRestoreRegRange vcpuWriteReg vcpuReadReg saveVirtTimer restoreVirtTimer vcpuDisable vcpuEnable vcpuRestore armvVCPUSave vcpuSave vcpuSwitch vcpuInvalidateActive vcpuCleanInvalidateActive virqSetEOIIRQEN vgicMaintenance vppiEvent

#INCLUDE_HASKELL SEL4/Kernel/Hypervisor/ARM.lhs Arch= CONTEXT ARM_HYP_H decls_only
#INCLUDE_HASKELL SEL4/Kernel/Hypervisor/ARM.lhs Arch= CONTEXT ARM_HYP_H bodies_only

end
end
