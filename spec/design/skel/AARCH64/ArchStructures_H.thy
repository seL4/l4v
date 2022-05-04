(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchStructures_H
imports
  "Lib.Lib"
  Types_H
  Hardware_H
begin

context Arch begin global_naming AARCH64_H

#INCLUDE_SETTINGS keep_constructor=asidpool
#INCLUDE_SETTINGS keep_constructor=arch_tcb

#INCLUDE_HASKELL SEL4/Object/Structures/AARCH64.hs CONTEXT AARCH64_H decls_only \
  NOT VPPIEventIRQ VirtTimer
#INCLUDE_HASKELL SEL4/Object/Structures/AARCH64.hs CONTEXT AARCH64_H instanceproofs \
  NOT VPPIEventIRQ VirtTimer
#INCLUDE_HASKELL SEL4/Object/Structures/AARCH64.hs CONTEXT AARCH64_H bodies_only \
  NOT makeVCPUObject

(* we define makeVCPUObject_def manually because we want a total function vgicLR *)
defs makeVCPUObject_def:
"makeVCPUObject \<equiv>
    VCPUObj_ \<lparr>
          vcpuTCBPtr= Nothing
        , vcpuVGIC= VGICInterface_ \<lparr>
                          vgicHCR= vgicHCREN
                        , vgicVMCR= 0
                        , vgicAPR= 0
                        , vgicLR= (\<lambda>_. 0)
                        \<rparr>
        , vcpuRegs= funArray (const 0)  aLU  [(VCPURegSCTLR, sctlrDefault)]
        , vcpuVPPIMasked= (\<lambda>_. False)
        , vcpuVTimer= VirtTimer 0
        \<rparr>"

datatype arch_kernel_object_type =
    PTET
  | VCPUT
  | ASIDPoolT

primrec
  archTypeOf :: "arch_kernel_object \<Rightarrow> arch_kernel_object_type"
where
  "archTypeOf (KOPTE e) = PTET"
| "archTypeOf (KOVCPU e) = VCPUT"
| "archTypeOf (KOASIDPool e) = ASIDPoolT"

end

context begin interpretation Arch .

requalify_types
  vcpu

end
end
