(*
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter \<open>Handle Hypervisor Fault Events\<close>

theory Hypervisor_A
imports Ipc_A
begin

context Arch begin global_naming AARCH64_A

fun handle_hypervisor_fault :: "machine_word \<Rightarrow> hyp_fault_type \<Rightarrow> (unit, 'z::state_ext) s_monad"
  where
  "handle_hypervisor_fault thread (ARMVCPUFault hsr) =
    handle_fault thread (ArchFault $ VCPUFault (ucast hsr))"

end
end
