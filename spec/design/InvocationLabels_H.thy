(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file InvocationLabels_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Kernel Invocation Labels"

theory InvocationLabels_H
imports "$L4V_ARCH/ArchInvocationLabels_H"
begin

context begin interpretation Arch .
requalify_types
  arch_invocation_label
end

text {*
  An enumeration of all system call labels.
*}

datatype invocation_label =
    InvalidInvocation
  | UntypedRetype
  | TCBReadRegisters
  | TCBWriteRegisters
  | TCBCopyRegisters
  | TCBConfigure
  | TCBSetPriority
  | TCBSetMCPriority
  | TCBSetIPCBuffer
  | TCBSetSpace
  | TCBSuspend
  | TCBResume
  | TCBBindNotification
  | TCBUnbindNotification
  | CNodeRevoke
  | CNodeDelete
  | CNodeCancelBadgedSends
  | CNodeCopy
  | CNodeMint
  | CNodeMove
  | CNodeMutate
  | CNodeRotate
  | CNodeSaveCaller
  | IRQIssueIRQHandler
  | IRQAckIRQ
  | IRQSetIRQHandler
  | IRQClearIRQHandler
  | DomainSetSet
  | ArchInvocationLabel arch_invocation_label

(* invocation_label instance proofs *)
(*<*)
instantiation invocation_label :: enum begin
definition
  enum_invocation_label: "enum_class.enum \<equiv> 
    [ 
      InvalidInvocation,
      UntypedRetype,
      TCBReadRegisters,
      TCBWriteRegisters,
      TCBCopyRegisters,
      TCBConfigure,
      TCBSetPriority,
      TCBSetMCPriority,
      TCBSetIPCBuffer,
      TCBSetSpace,
      TCBSuspend,
      TCBResume,
      TCBBindNotification,
      TCBUnbindNotification,
      CNodeRevoke,
      CNodeDelete,
      CNodeCancelBadgedSends,
      CNodeCopy,
      CNodeMint,
      CNodeMove,
      CNodeMutate,
      CNodeRotate,
      CNodeSaveCaller,
      IRQIssueIRQHandler,
      IRQAckIRQ,
      IRQSetIRQHandler,
      IRQClearIRQHandler,
      DomainSetSet
    ]
    @ (map ArchInvocationLabel enum)"

lemma ArchInvocationLabel_map_distinct[simp]: "distinct (map ArchInvocationLabel enum)"
  apply (simp add: distinct_map)
  by (meson injI invocation_label.inject)

definition
  "enum_class.enum_all (P :: invocation_label \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: invocation_label \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_invocation_label enum_all_invocation_label_def enum_ex_invocation_label_def)
  by fast+
end

instantiation invocation_label :: enum_alt
begin
definition
  enum_alt_invocation_label: "enum_alt \<equiv> 
    alt_from_ord (enum :: invocation_label list)"
instance ..
end

instantiation invocation_label :: enumeration_both
begin
instance by (intro_classes, simp add: enum_alt_invocation_label)
end

(*>*)


end
