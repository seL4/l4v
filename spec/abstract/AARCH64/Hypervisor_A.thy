(*
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter \<open>Handle Hypervisor Fault Events\<close>

theory Hypervisor_A
imports Ipc_A
begin

context Arch begin arch_global_naming (A)

fun handle_hypervisor_fault :: "machine_word \<Rightarrow> hyp_fault_type \<Rightarrow> (unit, 'z::state_ext) s_monad"
  where
  "handle_hypervisor_fault thread (ARMVCPUFault hsr) =
     (if hsr = 0x2000000 \<comment> \<open>@{text UNKNOWN_FAULT}\<close>
      then do
        esr \<leftarrow> do_machine_op getESR;
        handle_fault thread (UserException (esr && mask 32) 0)
      od
      else handle_fault thread (ArchFault $ VCPUFault (ucast hsr)))"

end
end
