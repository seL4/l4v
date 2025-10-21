(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter \<open>AARCH64 Object Invocations\<close>

theory ArchInvocation_A
imports Structures_A
begin

context Arch begin arch_global_naming (A)

text \<open>
  These datatypes encode the arguments to the various possible AARCH64-specific system calls.
  Selectors are defined for various fields for convenience elsewhere.
\<close>

datatype vspace_invocation =
    VSpaceNothing
  | VSpaceFlush
      (vs_flush_type : flush_type)
      (vs_flush_start : vspace_ref)
      (vs_flush_end : vspace_ref)
      (vs_flush_pstart : paddr)
      (vs_flush_space : obj_ref)
      (vs_flush_asid : asid)

datatype page_table_invocation =
    PageTableMap
      (pt_inv_cap : arch_cap)
      (pt_inv_cslot : cslot_ptr)
      (pt_map_pte : pte)
      (pt_map_slot : obj_ref)
      (pt_map_level : vm_level)
  | PageTableUnmap
      (pt_inv_cap : arch_cap)
      (pt_inv_cslot : cslot_ptr)

datatype asid_control_invocation =
    MakePool obj_ref cslot_ptr cslot_ptr asid

datatype asid_pool_invocation =
    Assign asid obj_ref cslot_ptr

datatype page_invocation =
    PageMap
      (pg_inv_cap : arch_cap)
      (pg_inv_cslot : cslot_ptr)
      (pg_inv_entries : "pte \<times> obj_ref \<times> vm_level")
  | PageUnmap
      (pg_inv_cap : arch_cap)
      (pg_inv_cslot : cslot_ptr)
  | PageGetAddr
      (pg_get_paddr : obj_ref)
  | PageFlush
      (pg_flush_type : flush_type)
      (pg_flush_start : vspace_ref)
      (pg_flush_end : vspace_ref)
      (pg_flush_pStart : paddr)
      (pg_flush_space : obj_ref)
      (pg_flush_asid : asid)

datatype vcpu_invocation =
    VCPUSetTCB
      (vcpu_inv_vcpu : obj_ref)
      (vcpu_inv_tcb : obj_ref)
  | VCPUInjectIRQ
      (vcpu_inv_vcpu : obj_ref)
      (vcpu_inv_idx : nat)
      (vcpu_inv_irq : virq)
  | VCPUReadRegister
      (vcpu_inv_vcpu : obj_ref)
      (vcpu_inv_reg : vcpureg)
  | VCPUWriteRegister
      (vcpu_inv_vcpu : obj_ref)
      (vcpu_inv_reg : vcpureg)
      (vcpu_inv_val : machine_word)
  | VCPUAckVPPI
      (vcpu_inv_vcpu : obj_ref)
      (vcpu_inv_eirq : vppievent_irq)

datatype sgi_signal_invocation =
    SGISignalGenerate (sgi_irq : sgi_irq) (sgi_target : sgi_target)

datatype smc_invocation =
    SMCCall (smc_args : "machine_word eight_tuple")

datatype arch_invocation =
    InvokeVSpace vspace_invocation
  | InvokePageTable page_table_invocation
  | InvokePage page_invocation
  | InvokeASIDControl asid_control_invocation
  | InvokeASIDPool asid_pool_invocation
  | InvokeVCPU vcpu_invocation
  | InvokeSGISignal sgi_signal_invocation
  | InvokeSMCCall smc_invocation

datatype arch_copy_register_sets =
    ARMNoExtraRegisters

definition ArchDefaultExtraRegisters :: arch_copy_register_sets where
  "ArchDefaultExtraRegisters = ARMNoExtraRegisters"

datatype arch_irq_control_invocation =
    ARMIRQControlInvocation irq cslot_ptr cslot_ptr bool
  | IssueSGISignal
      (issue_sgi_irq : sgi_irq)
      (issue_sgi_target : sgi_target)
      (issue_control_slot : cslot_ptr)
      (issue_sgi_slot : cslot_ptr)

end
end
