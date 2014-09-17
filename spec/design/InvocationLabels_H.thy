(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

header "Kernel Invocation Labels"

theory InvocationLabels_H
imports "../../lib/Enumeration"
begin

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
  | TCBSetIPCBuffer
  | TCBSetSpace
  | TCBSuspend
  | TCBResume
  | CNodeRevoke
  | CNodeDelete
  | CNodeRecycle
  | CNodeCopy
  | CNodeMint
  | CNodeMove
  | CNodeMutate
  | CNodeRotate
  | CNodeSaveCaller
  | IRQIssueIRQHandler
  | IRQInterruptControl
  | IRQAckIRQ
  | IRQSetIRQHandler
  | IRQClearIRQHandler
  | IRQSetMode
  | DomainSetSet
  | ARMPDClean_Data
  | ARMPDInvalidate_Data
  | ARMPDCleanInvalidate_Data
  | ARMPDUnify_Instruction
  | ARMPageTableMap
  | ARMPageTableUnmap
  | ARMPageMap
  | ARMPageRemap
  | ARMPageUnmap
  | ARMPageClean_Data
  | ARMPageInvalidate_Data
  | ARMPageCleanInvalidate_Data
  | ARMPageUnify_Instruction
  | ARMPageGetAddress
  | ARMASIDControlMakePool
  | ARMASIDPoolAssign

definition
isPDFlush :: "invocation_label \<Rightarrow> bool"
where
"isPDFlush x\<equiv> (case x of
        ARMPDClean_Data \<Rightarrow>   True
      | ARMPDInvalidate_Data \<Rightarrow>   True
      | ARMPDCleanInvalidate_Data \<Rightarrow>   True
      | ARMPDUnify_Instruction \<Rightarrow>   True
      | _ \<Rightarrow>   False
      )"

definition
isPageFlush :: "invocation_label \<Rightarrow> bool"
where
"isPageFlush x\<equiv> (case x of
        ARMPageClean_Data \<Rightarrow>   True
      | ARMPageInvalidate_Data \<Rightarrow>   True
      | ARMPageCleanInvalidate_Data \<Rightarrow>   True
      | ARMPageUnify_Instruction \<Rightarrow>   True
      | _ \<Rightarrow>   False
      )"

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
      TCBSetIPCBuffer,
      TCBSetSpace,
      TCBSuspend,
      TCBResume,
      CNodeRevoke,
      CNodeDelete,
      CNodeRecycle,
      CNodeCopy,
      CNodeMint,
      CNodeMove,
      CNodeMutate,
      CNodeRotate,
      CNodeSaveCaller,
      IRQIssueIRQHandler,
      IRQInterruptControl,
      IRQAckIRQ,
      IRQSetIRQHandler,
      IRQClearIRQHandler,
      IRQSetMode,
      DomainSetSet,
      ARMPDClean_Data,
      ARMPDInvalidate_Data,
      ARMPDCleanInvalidate_Data,
      ARMPDUnify_Instruction,
      ARMPageTableMap,
      ARMPageTableUnmap,
      ARMPageMap,
      ARMPageRemap,
      ARMPageUnmap,
      ARMPageClean_Data,
      ARMPageInvalidate_Data,
      ARMPageCleanInvalidate_Data,
      ARMPageUnify_Instruction,
      ARMPageGetAddress,
      ARMASIDControlMakePool,
      ARMASIDPoolAssign
    ]"

definition
  "enum_class.enum_all (P :: invocation_label \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: invocation_label \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_invocation_label enum_all_invocation_label_def enum_ex_invocation_label_def)
  apply fast
  done
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
