(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Handle Hypervisor Fault Event"

theory Hypervisor_A
imports Ipc_A
begin

context Arch begin global_naming ARM_HYP_A

fun handle_hypervisor_fault :: "word32 \<Rightarrow> hyp_fault_type \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
"handle_hypervisor_fault thread (ARMVCPUFault hsr) =
   handle_fault thread (ArchFault $ VCPUFault hsr)"


end
end
