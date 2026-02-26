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
  | RevokeCall cdl_cap_ref
  | DeleteCall cdl_cap_ref
  | RotateCall cdl_cap cdl_cap cdl_cap_ref cdl_cap_ref cdl_cap_ref
  | SaveCall cdl_cap_ref
  | CancelBadgedSendsCall cdl_cap

datatype cdl_untyped_invocation =
    Retype cdl_cap_ref
        cdl_object_type cdl_size_bits "cdl_cap_ref list" bool nat

datatype cdl_tcb_invocation =
    WriteRegisters cdl_object_id bool "word32 list" nat
  | ReadRegisters cdl_object_id bool word32 nat
  | CopyRegisters cdl_object_id cdl_object_id bool bool bool bool nat
  | ThreadControl cdl_object_id cdl_cap_ref
        "cdl_cptr option"
        "(cdl_cap \<times> cdl_cap_ref) option"
        "(cdl_cap \<times> cdl_cap_ref) option"
        "(cdl_cap \<times> cdl_cap_ref) option"
  | Suspend cdl_object_id
  | Resume cdl_object_id
  | NotificationControl cdl_object_id "cdl_object_id option"
  | SetTLSBase cdl_object_id
  | SetFlags cdl_object_id

datatype arch_cdl_irq_control_invocation =
    ARMIssueSGISignal sgi_irq sgi_target cdl_cap_ref cdl_cap_ref

datatype cdl_irq_control_invocation =
    IssueIrqHandler cdl_irq cdl_cap_ref cdl_cap_ref
  | ArchIssueIrqHandler arch_cdl_irq_control_invocation

datatype cdl_irq_handler_invocation =
    AckIrq cdl_irq
  | SetIrqHandler cdl_irq cdl_cap cdl_cap_ref
  | ClearIrqHandler cdl_irq

datatype cdl_endpoint_invocation =
    (* We need not track the "block" or "call" bits because they
       are handled separately in the top-level syscall interface. *)
    (* badge, grant, grant reply, ep *)
    SyncMessage cdl_badge bool bool cdl_object_id

datatype cdl_notification_invocation =
    (* badge (notification word) and notification object *)
    Signal cdl_badge cdl_object_id

datatype cdl_reply_invocation =
    ReplyMessage cdl_object_id cdl_cap_ref bool (* can grant *)

datatype cdl_page_table_invocation =
    (* PageTableMap <real_pt_cap> <pt_cap> <pt_cap_ref> <pd_target_slot> *)
    PageTableMap cdl_cap cdl_cap cdl_cap_ref cdl_cap_ref
    (* PageTableUnmap <mapped_addr option> <pt_obj_id> <pt_cap_ref> *)
  | PageTableUnmap "cdl_mapped_addr option"  cdl_object_id cdl_cap_ref

datatype cdl_asid_control_invocation =
    MakePool cdl_cap cdl_cap_ref "cdl_object_id set" cdl_cap_ref nat

datatype cdl_asid_pool_invocation =
    Assign cdl_asid cdl_cap_ref cdl_cap_ref

datatype flush =
   Clean | Invalidate | CleanInvalidate | Unify

datatype cdl_page_invocation =
    PageMap cdl_cap cdl_cap cdl_cap_ref "cdl_cap_ref list"
  | PageUnmap "cdl_mapped_addr option" cdl_object_id "cdl_cap_ref" nat
  | PageFlushCaches flush
  | PageGetAddress


datatype cdl_page_directory_invocation =
   PageDirectoryFlush  flush
 | PageDirectoryNothing


datatype cdl_domain_invocation =
    InvokeSetDomain (dominv_thread : cdl_object_id)
                    (dominv_domain : word8)
  | InvokeDomainScheduleSetStart (dominv_index : nat)
  | InvokeDomainScheduleConfigure (dominv_index : nat)
                                  (dominv_domain : word8)
                                  (dominv_duration : domain_duration)

datatype cdl_sgi_signal_invocation =
  SGISignalGenerate (* no params, machine op only *)

datatype cdl_invocation =
    InvokeUntyped cdl_untyped_invocation
  | InvokeEndpoint cdl_endpoint_invocation
  | InvokeNotification cdl_notification_invocation
  | InvokeReply cdl_reply_invocation
  | InvokeTcb cdl_tcb_invocation
  | InvokeDomain cdl_domain_invocation
  | InvokeCNode cdl_cnode_invocation
  | InvokeIrqControl cdl_irq_control_invocation
  | InvokeIrqHandler cdl_irq_handler_invocation
  | InvokePageTable cdl_page_table_invocation
  | InvokePage cdl_page_invocation
  | InvokePageDirectory cdl_page_directory_invocation
  | InvokeAsidControl cdl_asid_control_invocation
  | InvokeAsidPool cdl_asid_pool_invocation
  | InvokeSGISignal cdl_sgi_signal_invocation

end
