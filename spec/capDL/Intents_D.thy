(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * This file contains user "intents".
 *
 * Such intents attempt to capture the semantics of an operation the
 * user is attempting to perform, without having to worry about how the
 * operation is actually encoded within their message registers.
 *
 * There is a one-to-one mapping between the following intents and the
 * invocations made available to userspace. There is not quite
 * a one-to-one mapping between these intents and the invocations listed
 * in Invocations_D, as some of these intents are multiplexed onto
 * a single invocation when being validated.
 *
 * Caps required by the intents are not stored in the intent themselves,
 * but passed separately in when required. In some sense, the Intent
 * is the "data" part of an invocation, but not the "caps" part of it.
 *)

theory Intents_D
imports
  ASpec.CapRights_A
  VMAttributes_D
  Structures_D
begin

(*
 * Entities in seL4 have particular rights to kernel objects, which
 * affects how entities can interact with those particular objects.
 *)
type_synonym cdl_right = rights

(* A user cap pointer. *)
type_synonym cdl_cptr = machine_word

abbreviation (input) Read ::rights
  where "Read \<equiv> AllowRead"

abbreviation (input) Write::rights
  where "Write \<equiv> AllowWrite"

abbreviation (input) Grant::rights
  where "Grant \<equiv> AllowGrant"

abbreviation (input) GrantReply::rights
  where "GrantReply \<equiv> AllowGrantReply"

(* Capability data, such as guard information. *)
type_synonym cdl_raw_capdata = machine_word

(* VM Attributes, such as page cache attributes. *)
type_synonym cdl_raw_vmattrs = arch_raw_vmattrs

(* TCB context, for operations such as write to a thread's registers. *)
type_synonym cdl_raw_usercontext = "machine_word list"

(* Thread priorities *)
type_synonym prio = word8

(* Domains in the domain scheduler *)
type_synonym domain = word8

(* Kernel objects types. *)
datatype cdl_object_type =
    EndpointType
  | NotificationType
  | TcbType
  | CNodeType
  | IRQNodeType
  | UntypedType
  | AsidPoolType
  | PageTableType
  | PageDirectoryType
  | FrameType nat (* size in bits of desired page *)

datatype cdl_cnode_intent =
    (* Copy: (target), dest_index, dest_depth, (src_root), src_index, src_depth, rights *)
    CNodeCopyIntent machine_word machine_word machine_word machine_word "cdl_right set"
    (* Mint: (target), dest_index, dest_depth, (src_root), src_index, src_depth, rights, badge *)
 |  CNodeMintIntent machine_word machine_word machine_word machine_word "cdl_right set" cdl_raw_capdata
    (* Move: (target), dest_index, dest_depth, (src_root), src_index, src_depth *)
 |  CNodeMoveIntent machine_word machine_word machine_word machine_word
    (* Mutate: (target), dest_index, dest_depth, (src_root), src_index, src_depth, badge *)
 |  CNodeMutateIntent machine_word machine_word machine_word machine_word cdl_raw_capdata
    (* Revoke: (target), index, depth *)
 |  CNodeRevokeIntent machine_word machine_word
    (* Delete: (target), index, depth *)
 |  CNodeDeleteIntent machine_word machine_word
    (* SaveCaller: (target), index, depth *)
 |  CNodeSaveCallerIntent machine_word machine_word
    (* CancelBadgedSends: (target), index, depth *)
 |  CNodeCancelBadgedSendsIntent machine_word machine_word
    (* Rotate: (target), dest_index, dest_depth, (pivot_root), pivot_index, pivot_depth, pivot_badge,
               (src_root), src_index, src_depth, src_badge *)
 |  CNodeRotateIntent machine_word machine_word machine_word machine_word cdl_raw_capdata
                      machine_word machine_word cdl_raw_capdata

type_synonym arch_flags = word8 (* FIXME arch-split: check if used *)

datatype cdl_tcb_intent =
    (* ReadRegisters: (target), suspend_source, arch_flags, count *)
    TcbReadRegistersIntent bool arch_flags machine_word
    (* WriteRegisters: (target), resume_target, arch_flags, count, regs *)
 |  TcbWriteRegistersIntent bool arch_flags machine_word cdl_raw_usercontext
    (* CopyRegisters: (target), (source), suspend_source, resume_target, transfer_frame,
                      transfer_integer, arch_flags *)
 |  TcbCopyRegistersIntent bool bool bool bool arch_flags
    (* Suspend: (target) *)
 |  TcbSuspendIntent
    (* Resume: (target) *)
 |  TcbResumeIntent
    (* Configure: (target), fault_ep, (cspace_root), cspace_root_data, (vspace_root),
                  vspace_root_data, buffer, (bufferFrame) *)
 |  TcbConfigureIntent cdl_cptr cdl_raw_capdata cdl_raw_capdata machine_word
    (* SetMCPriority: (target), mcp *)
 |  TcbSetMCPriorityIntent prio
    (* SetPriority: (target), priority *)
 |  TcbSetPriorityIntent prio
    (* SetSchedParams: (target), mcp, priority *)
 |  TcbSetSchedParamsIntent prio prio
    (* SetIPCBuffer: (target), buffer, (bufferFrame) *)
 |  TcbSetIPCBufferIntent machine_word
    (* SetSpace: (target), fault_ep, (cspace_root), cspace_root_data, (vspace_root), vspace_root_data *)
 |  TcbSetSpaceIntent machine_word cdl_raw_capdata cdl_raw_capdata
    (* BindNTFN: (target), (ntfn) *)
 |  TcbBindNTFNIntent
    (* UnbindNTFN: (target) *)
 |  TcbUnbindNTFNIntent
    (* SetTLSBase: (target) *)
 |  TcbSetTLSBaseIntent
    (* SetFlags: (target) *)
 |  TcbSetFlagsIntent

datatype cdl_untyped_intent =
    (* Retype: (target), (do_reset), type, size_bits, (root), node_index, node_depth, node_offset,
               node_window, has_children *)
    UntypedRetypeIntent cdl_object_type machine_word machine_word machine_word machine_word
                        machine_word

datatype cdl_irq_handler_intent =
    (* Ack: (target) *)
    IrqHandlerAckIntent
    (* SetEndpoint: (target), (endpoint) *)
 |  IrqHandlerSetEndpointIntent
    (* Clear: (target) *)
 |  IrqHandlerClearIntent

datatype cdl_arch_irq_control_intent =
    (* ArchIssueIrqHandler: (target), irq, (root), index, depth *)
    ARMIrqControlIssueIrqHandlerIntent irq machine_word machine_word
    (* ARMIssueSGISignal: irq, target, index, depth, (cnode) *)
  | ARMIssueSGISignalIntent machine_word machine_word machine_word machine_word

datatype cdl_irq_control_intent =
    (* IssueIrqHandler: (target), irq, (root), index, depth *)
    IrqControlIssueIrqHandlerIntent irq machine_word machine_word
    (* InterruptControl *)
  | ArchIrqControlIssueIrqHandlerIntent cdl_arch_irq_control_intent

datatype cdl_page_table_intent =
    (* Map: (target), (pd), vaddr, attr *)
    PageTableMapIntent machine_word cdl_raw_vmattrs
 |  PageTableUnmapIntent

datatype cdl_page_intent =
    (* Map: (target), (pd), vaddr, rights, attr *)
    PageMapIntent machine_word "cdl_right set" cdl_raw_vmattrs
    (* Unmap: (target) *)
 |  PageUnmapIntent
    (* FlushCaches: (target) *)
 |  PageFlushCachesIntent
    (* GetAddress *)
 | PageGetAddressIntent


datatype cdl_page_directory_intent =
   PageDirectoryFlushIntent
 | PageDirectoryNothingIntent

datatype cdl_asid_control_intent =
    (* MakePool: (target), (untyped), (root), index, depth *)
    AsidControlMakePoolIntent machine_word machine_word

datatype cdl_asid_pool_intent =
    (* Assign: (target), (vroot) *)
    AsidPoolAssignIntent

datatype cdl_notification_intent =
    SendSignalIntent machine_word

(* Also used with reply caps *)
datatype cdl_endpoint_intent =
    SendMessageIntent "cdl_cptr list"

datatype cdl_domain_intent = DomainSetIntent domain

datatype cdl_intent =
    CNodeIntent cdl_cnode_intent
  | TcbIntent cdl_tcb_intent
  | UntypedIntent cdl_untyped_intent
  | IrqHandlerIntent cdl_irq_handler_intent
  | IrqControlIntent cdl_irq_control_intent
  | PageTableIntent cdl_page_table_intent
  | PageIntent cdl_page_intent
  | PageDirectoryIntent cdl_page_directory_intent
  | AsidControlIntent cdl_asid_control_intent
  | AsidPoolIntent cdl_asid_pool_intent
  | NotificationIntent cdl_notification_intent
  | EndpointIntent cdl_endpoint_intent
  | DomainIntent cdl_domain_intent

record cdl_full_intent =
  cdl_intent_op        :: "cdl_intent option"
  cdl_intent_error     :: bool
  cdl_intent_cap       :: cdl_cptr
  cdl_intent_extras    :: "cdl_cptr list"
  cdl_intent_recv_slot :: "(cdl_cptr \<times> machine_word \<times> nat) option"

end
