(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Invocations_D
imports Types_D
begin

datatype cdl_cnode_invocation =
    InsertCall cdl_cap cdl_cap_ref cdl_cap_ref
  | MoveCall cdl_cap cdl_cap_ref cdl_cap_ref
  | DeleteCall cdl_cap_ref

datatype cdl_untyped_invocation =
    Retype cdl_cap_ref cdl_object_type cdl_size_bits "cdl_cap_ref list" bool nat

datatype cdl_tcb_invocation =
    WriteRegisters cdl_object_id bool
  | ThreadControl
      cdl_object_id
      cdl_cap_ref
      "cdl_cptr option"
      "(cdl_cap \<times> cdl_cap_ref) option"
      "(cdl_cap \<times> cdl_cap_ref) option"
      "(cdl_cap \<times> cdl_cap_ref) option"
  | Suspend cdl_object_id
  | Resume cdl_object_id
  | NotificationControl cdl_object_id cdl_object_id
  | SetFlags cdl_object_id machine_word machine_word

datatype arch_cdl_irq_control_invocation =
    ARMIssueSGISignal sgi_irq sgi_target cdl_cap_ref cdl_cap_ref

datatype cdl_irq_control_invocation =
    IssueIrqHandler cdl_irq cdl_cap_ref cdl_cap_ref
  | ArchIssueIrqHandler arch_cdl_irq_control_invocation

datatype cdl_irq_handler_invocation =
    SetIrqHandler cdl_irq cdl_cap cdl_cap_ref

datatype cdl_page_table_invocation =
    (* PageTableMap <real_pt_cap> <pt_cap> <pt_cap_ref> <pd_target_slot> *)
    PageTableMap cdl_cap cdl_cap cdl_cap_ref cdl_cap_ref

datatype cdl_asid_control_invocation =
    MakePool cdl_cap cdl_cap_ref "cdl_object_id set" cdl_cap_ref nat

datatype cdl_asid_pool_invocation =
    Assign cdl_asid cdl_cap_ref cdl_cap_ref

datatype flush =
    Clean | Invalidate | CleanInvalidate | Unify

datatype cdl_page_invocation =
    PageMap cdl_cap cdl_cap cdl_cap_ref cdl_cap_ref
  | PageUnmap "cdl_mapped_addr option" cdl_object_id "cdl_cap_ref" nat
  | PageFlushCaches flush
  | PageGetAddress

datatype cdl_domain_invocation =
    InvokeSetDomain (dominv_thread : cdl_object_id)
                    (dominv_domain : domain)
  | InvokeDomainScheduleSetStart (dominv_index : nat)
  | InvokeDomainScheduleConfigure (dominv_index : nat)
                                  (dominv_domain : domain)
                                  (dominv_duration : domain_duration)

datatype cdl_vcpu_invocation =
    VCPUSetTCB (vcpu_inv_vcpu : cdl_object_id) (vcpu_inv_tcb : cdl_object_id)

datatype cdl_invocation =
    InvokeUntyped cdl_untyped_invocation
  | InvokeTcb cdl_tcb_invocation
  | InvokeDomain cdl_domain_invocation
  | InvokeCNode cdl_cnode_invocation
  | InvokeIrqControl cdl_irq_control_invocation
  | InvokeIrqHandler cdl_irq_handler_invocation
  | InvokePageTable cdl_page_table_invocation
  | InvokePage cdl_page_invocation
  | InvokeAsidControl cdl_asid_control_invocation
  | InvokeAsidPool cdl_asid_pool_invocation
  | InvokeVCPU cdl_vcpu_invocation
    (* Any invocation that is not needed for system initialisation *)
  | OtherInvocation

end
