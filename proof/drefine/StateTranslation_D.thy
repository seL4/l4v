(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * State translation.
 *
 * Takes a state of the system as defined in the abstract seL4
 * specification, and returns an equivalent state of the system
 * defined in terms of the CapDL specification.
 *)

theory StateTranslation_D
imports Lemmas_D
begin

context begin interpretation Arch . (*FIXME: arch-split*)

type_synonym kernel_object = Structures_A.kernel_object
type_synonym tcb = Structures_A.tcb
type_synonym pte = ARM_A.pte

(* Transform an abstract-spec cap ptr to a capDL one. This is currently
 * a no-(;) however, it is conceivable that the capDL cptr representation could
 * be changed. Allowing for this potential change is the purpose of this
 * definition.
 *)
definition
  transform_cptr :: "word32 \<Rightarrow> cdl_cptr" where
  "transform_cptr w \<equiv> w"

(* transform an abstract-spec recv_slot description to a capDL one *)
definition
  transform_recv_slot :: "(word32 \<times> word32 \<times> word8) \<Rightarrow>
                          (cdl_cptr \<times> word32 \<times> word8)"
where
  "transform_recv_slot x \<equiv> let (cap,w32,w8) = x in (transform_cptr cap,w32,w8)"

(*
 * Convert a user value to a CDL type.
 *
 * We repeat "FrameType" multiple times because CapDL doesn't
 * treat the different frame sizes as different types.
 *)
definition
  transform_type :: "word32 \<Rightarrow> cdl_object_type option"
where
  "transform_type x \<equiv>
         if x = 0  then Some UntypedType
    else if x = 1  then Some TcbType
    else if x = 2  then Some EndpointType
    else if x = 3  then Some NotificationType
    else if x = 4  then Some CNodeType
    else if x = 5  then Some PageDirectoryType
    else if x = 6  then Some (FrameType 12)
    else if x = 7  then Some (FrameType 16)
    else if x = 8  then Some (FrameType 20)
    else if x = 9  then Some (FrameType 24)
    else if x = 10 then Some PageTableType
    else None"

definition
  transform_intent_untyped_retype :: "word32 list \<Rightarrow> cdl_untyped_intent option"
where
  "transform_intent_untyped_retype args =
    (case args of
      type#size_bits#index#depth#offset#window#_ \<Rightarrow>
        (case transform_type type of
             Some x \<Rightarrow>
               Some (UntypedRetypeIntent x size_bits index depth offset window)
           | _ \<Rightarrow>
               None)
      | _ \<Rightarrow> None)"

(* Arch flags always set to 0 here as they have no meaning on ARM. *)
definition
  transform_intent_tcb_read_registers :: "word32 list \<Rightarrow> cdl_tcb_intent option"
where
  "transform_intent_tcb_read_registers args =
  (case args of flags#n#_ \<Rightarrow>
    Some (TcbReadRegistersIntent (flags !! 0) 0 n)
   | _ \<Rightarrow> None)"

(* Arch flags always set to 0 here as they have no meaning on ARM. *)
definition
  transform_intent_tcb_write_registers :: "word32 list \<Rightarrow> cdl_tcb_intent option"
where
  "transform_intent_tcb_write_registers args =
  (case args of flags#n#values \<Rightarrow>
    Some (TcbWriteRegistersIntent (flags !! 0) 0 n values)
   | _ \<Rightarrow> None)"

(* Arch flags always set to 0 here as they have no meaning on ARM. *)
definition
  transform_intent_tcb_copy_registers :: "word32 list \<Rightarrow> cdl_tcb_intent option"
where
  "transform_intent_tcb_copy_registers args =
  (case args of flags#_ \<Rightarrow>
    Some (TcbCopyRegistersIntent (flags !! 0) (flags !! 1) (flags !! 2) (flags !! 3) 0)
   | _ \<Rightarrow> None)"

(* Priority always set to 0 here. This should change if priorities
 * are ever added to the capDL spec.
 *)
definition
  prio_from_arg :: "word32 \<Rightarrow> word8"
where
  "prio_from_arg _ = 0"

definition
  transform_intent_tcb_configure :: "word32 list \<Rightarrow> cdl_tcb_intent option"
where
  "transform_intent_tcb_configure args =
  (case args of fault_ep#croot_data#vroot_data#buffer#_ \<Rightarrow>
    Some (TcbConfigureIntent fault_ep
                             croot_data vroot_data buffer)
   | _ \<Rightarrow> None)"

definition
  transform_intent_tcb_set_priority :: "word32 list \<Rightarrow> cdl_tcb_intent option"
where
  "transform_intent_tcb_set_priority args =
  (case args of prio#_ \<Rightarrow>
    Some (TcbSetPriorityIntent (prio_from_arg prio))
   | _ \<Rightarrow> None)"

definition
  transform_intent_tcb_set_mcpriority :: "word32 list \<Rightarrow> cdl_tcb_intent option"
where
  "transform_intent_tcb_set_mcpriority args =
  (case args of mcp#_ \<Rightarrow>
    Some (TcbSetMCPriorityIntent (prio_from_arg mcp))
   | _ \<Rightarrow> None)"

definition
  transform_intent_tcb_set_sched_params :: "word32 list \<Rightarrow> cdl_tcb_intent option"
where
  "transform_intent_tcb_set_sched_params args =
  (case args of mcp#priority#_ \<Rightarrow>
    Some (TcbSetSchedParamsIntent (prio_from_arg mcp) (prio_from_arg priority))
   | _ \<Rightarrow> None)"

definition
  transform_intent_tcb_set_ipc_buffer :: "word32 list \<Rightarrow> cdl_tcb_intent option"
where
  "transform_intent_tcb_set_ipc_buffer args =
  (case args of buffer#_ \<Rightarrow>
    Some (TcbSetIPCBufferIntent buffer)
   | _ \<Rightarrow> None)"


definition
  transform_intent_tcb_set_space :: "word32 list \<Rightarrow> cdl_tcb_intent option"
where
  "transform_intent_tcb_set_space args =
  (case args of fault_ep#croot_data#vroot_data#_ \<Rightarrow>
    Some (TcbSetSpaceIntent fault_ep croot_data vroot_data)
   | _ \<Rightarrow> None)"

definition
  transform_cnode_index_and_depth :: "(word32 \<Rightarrow> word32 \<Rightarrow> 'a) \<Rightarrow> word32 list \<Rightarrow> 'a option"
where
  "transform_cnode_index_and_depth func args \<equiv>
  case args of index#depth#_ \<Rightarrow>
    Some (func index depth)
   | _ \<Rightarrow> None"


definition
  transform_intent_cnode_copy :: "word32 list \<Rightarrow> cdl_cnode_intent option"
where
  "transform_intent_cnode_copy args \<equiv>
  case args of destindex#destdepth#srcindex#srcdepth#rightsWord#_ \<Rightarrow>
     Some (CNodeCopyIntent destindex destdepth
                           srcindex srcdepth (data_to_rights rightsWord))
    | _ \<Rightarrow> Nothing"

definition
  transform_intent_cnode_mint :: "word32 list \<Rightarrow> cdl_cnode_intent option"
where
  "transform_intent_cnode_mint args \<equiv>
  case args of destindex#destdepth#srcindex#srcdepth#rightsWord#capData#_ \<Rightarrow>
     Some (CNodeMintIntent destindex destdepth
             srcindex srcdepth (data_to_rights rightsWord) capData)
    | _ \<Rightarrow> Nothing"

definition
  transform_intent_cnode_move :: "word32 list \<Rightarrow> cdl_cnode_intent option"
where
  "transform_intent_cnode_move args \<equiv>
  case args of destindex#destdepth#srcindex#srcdepth#rest \<Rightarrow>
     Some (CNodeMoveIntent destindex destdepth
                           srcindex srcdepth)
    | _ \<Rightarrow> Nothing"

definition
  transform_intent_cnode_mutate :: "word32 list \<Rightarrow> cdl_cnode_intent option"
where
  "transform_intent_cnode_mutate args \<equiv>
  case args of destindex#destdepth#srcindex#srcdepth#capData#_ \<Rightarrow>
     Some (CNodeMutateIntent destindex destdepth
                             srcindex srcdepth capData)
    | _ \<Rightarrow> Nothing"

definition
  transform_intent_cnode_rotate :: "word32 list \<Rightarrow> cdl_cnode_intent option"
where
  "transform_intent_cnode_rotate args \<equiv>
  case args of destindex#destdepth#pivotbadge#pivotindex#
               pivotdepth#srcbadge#srcindex#srcdepth#_ \<Rightarrow>
     Some (CNodeRotateIntent destindex destdepth
                             pivotindex pivotdepth pivotbadge
                             srcindex srcdepth srcbadge)
    | _ \<Rightarrow> Nothing"


definition
  transform_intent_issue_irq_handler :: "word32 list \<Rightarrow> cdl_irq_control_intent option"
where
  "transform_intent_issue_irq_handler args \<equiv>
   case args of
      irqW#index#depth#_ \<Rightarrow>
         Some (IrqControlIssueIrqHandlerIntent (ucast irqW :: irq) index depth)
    | _ \<Rightarrow> Nothing"

definition
  arch_transform_intent_issue_irq_handler :: "word32 list \<Rightarrow> cdl_irq_control_intent option"
where
  "arch_transform_intent_issue_irq_handler args \<equiv>
   case args of
      irqW#trigger#index#depth#_ \<Rightarrow>
         Some (IrqControlIssueIrqHandlerIntent (ucast irqW :: irq) index depth)
    | _ \<Rightarrow> Nothing"

definition
  transform_intent_page_table_map :: "word32 list \<Rightarrow> cdl_page_table_intent option"
where
  "transform_intent_page_table_map args =
    (case args of
      vaddr#attr#_ \<Rightarrow>
         Some (PageTableMapIntent vaddr attr)
    | _ \<Rightarrow> Nothing)"

definition
  transform_intent_page_map :: "word32 list \<Rightarrow> cdl_page_intent option"
where
  "transform_intent_page_map args =
    (case args of
      vaddr#rightsW#attr#_ \<Rightarrow>
         Some (PageMapIntent vaddr (data_to_rights rightsW) attr)
    | _ \<Rightarrow> Nothing)"

definition
  transform_intent_domain :: "word32 list \<Rightarrow> cdl_domain_intent option"
where
  "transform_intent_domain args =
     (case args of
         d#_ \<Rightarrow> Some (DomainSetIntent (ucast d :: word8))
       | _   \<Rightarrow> Nothing)"

(* Added for IOAPIC patch *)
definition
  to_bool :: "word32 \<Rightarrow> bool"
where
  "to_bool w \<equiv> w \<noteq> 0"

(* A dispatch function that converts the user's message label
 * and IPC buffer into an intent by dispatching on the message label.
 * For malformed messages etc., we return None.
*)

definition
  transform_intent :: "invocation_label \<Rightarrow> word32 list \<Rightarrow> cdl_intent option" where
  "transform_intent label args \<equiv>
    case label of
      GenInvocationLabel InvalidInvocation \<Rightarrow> None
    | GenInvocationLabel UntypedRetype \<Rightarrow>
        map_option UntypedIntent (transform_intent_untyped_retype args)
    | GenInvocationLabel TCBReadRegisters \<Rightarrow>
        map_option TcbIntent
                   (transform_intent_tcb_read_registers args)
    | GenInvocationLabel TCBWriteRegisters \<Rightarrow>
        map_option TcbIntent
                   (transform_intent_tcb_write_registers args)
    | GenInvocationLabel TCBCopyRegisters \<Rightarrow>
         map_option TcbIntent
                   (transform_intent_tcb_copy_registers args)
    | GenInvocationLabel TCBConfigure \<Rightarrow>
         map_option TcbIntent
                   (transform_intent_tcb_configure args)
    | GenInvocationLabel TCBSetPriority \<Rightarrow>
         map_option TcbIntent
                   (transform_intent_tcb_set_priority args)
    | GenInvocationLabel TCBSetMCPriority \<Rightarrow>
         map_option TcbIntent
                   (transform_intent_tcb_set_mcpriority args)
    | GenInvocationLabel TCBSetSchedParams \<Rightarrow>
         map_option TcbIntent
                   (transform_intent_tcb_set_sched_params args)
    | GenInvocationLabel TCBSetIPCBuffer \<Rightarrow>
          map_option TcbIntent
                   (transform_intent_tcb_set_ipc_buffer args)
    | GenInvocationLabel TCBSetSpace \<Rightarrow>
          map_option TcbIntent
                   (transform_intent_tcb_set_space args)
    | GenInvocationLabel TCBSuspend \<Rightarrow> Some (TcbIntent TcbSuspendIntent)
    | GenInvocationLabel TCBResume \<Rightarrow> Some (TcbIntent TcbResumeIntent)
    | GenInvocationLabel TCBBindNotification \<Rightarrow> Some (TcbIntent TcbBindNTFNIntent)
    | GenInvocationLabel TCBUnbindNotification \<Rightarrow> Some (TcbIntent TcbUnbindNTFNIntent)
    | GenInvocationLabel TCBSetTLSBase \<Rightarrow> Some (TcbIntent TcbSetTLSBaseIntent)
    | GenInvocationLabel CNodeRevoke \<Rightarrow>
          map_option CNodeIntent
                   (transform_cnode_index_and_depth CNodeRevokeIntent args)
    | GenInvocationLabel CNodeDelete \<Rightarrow>
          map_option CNodeIntent
                   (transform_cnode_index_and_depth CNodeDeleteIntent args)
    | GenInvocationLabel CNodeCancelBadgedSends \<Rightarrow>
          map_option CNodeIntent
                   (transform_cnode_index_and_depth CNodeCancelBadgedSendsIntent args)
    | GenInvocationLabel CNodeCopy \<Rightarrow>
          map_option CNodeIntent
                   (transform_intent_cnode_copy args)
    | GenInvocationLabel CNodeMint \<Rightarrow>
          map_option CNodeIntent
                   (transform_intent_cnode_mint args)
    | GenInvocationLabel CNodeMove \<Rightarrow>
          map_option CNodeIntent
                   (transform_intent_cnode_move args)
    | GenInvocationLabel CNodeMutate \<Rightarrow>
          map_option CNodeIntent
                   (transform_intent_cnode_mutate args)
    | GenInvocationLabel CNodeRotate \<Rightarrow>
          map_option CNodeIntent
                   (transform_intent_cnode_rotate args)
    | GenInvocationLabel CNodeSaveCaller \<Rightarrow>
          map_option CNodeIntent
                   (transform_cnode_index_and_depth CNodeSaveCallerIntent args)
    | GenInvocationLabel IRQIssueIRQHandler \<Rightarrow>
          map_option IrqControlIntent
                   (transform_intent_issue_irq_handler args)
    | GenInvocationLabel IRQAckIRQ \<Rightarrow> Some (IrqHandlerIntent IrqHandlerAckIntent)
    | GenInvocationLabel IRQSetIRQHandler \<Rightarrow> Some (IrqHandlerIntent IrqHandlerSetEndpointIntent)
    | GenInvocationLabel IRQClearIRQHandler \<Rightarrow> Some (IrqHandlerIntent IrqHandlerClearIntent)
    | ArchInvocationLabel ARMPageTableMap \<Rightarrow>
                          map_option PageTableIntent
                                   (transform_intent_page_table_map args)
    | ArchInvocationLabel ARMPageTableUnmap \<Rightarrow> Some (PageTableIntent PageTableUnmapIntent)
    | ArchInvocationLabel ARMPageMap \<Rightarrow>
                          map_option PageIntent
                                   (transform_intent_page_map args)
    | ArchInvocationLabel ARMPageUnmap \<Rightarrow> Some (PageIntent PageUnmapIntent)
    | ArchInvocationLabel ARMPageClean_Data \<Rightarrow> Some (PageIntent PageFlushCachesIntent )
    | ArchInvocationLabel ARMPageInvalidate_Data  \<Rightarrow> Some (PageIntent PageFlushCachesIntent )
    | ArchInvocationLabel ARMPageCleanInvalidate_Data \<Rightarrow> Some (PageIntent PageFlushCachesIntent )
    | ArchInvocationLabel ARMPageUnify_Instruction \<Rightarrow> Some (PageIntent PageFlushCachesIntent )
    | ArchInvocationLabel ARMPageGetAddress \<Rightarrow> Some (PageIntent PageGetAddressIntent )
    | ArchInvocationLabel ARMPDClean_Data \<Rightarrow> Some (PageDirectoryIntent PageDirectoryFlushIntent )
    | ArchInvocationLabel ARMPDInvalidate_Data \<Rightarrow>  Some (PageDirectoryIntent PageDirectoryFlushIntent )
    | ArchInvocationLabel ARMPDCleanInvalidate_Data \<Rightarrow>  Some (PageDirectoryIntent PageDirectoryFlushIntent)
    | ArchInvocationLabel ARMPDUnify_Instruction \<Rightarrow>  Some (PageDirectoryIntent PageDirectoryFlushIntent )
    | ArchInvocationLabel ARMASIDControlMakePool \<Rightarrow>
                          map_option AsidControlIntent
                                  (transform_cnode_index_and_depth AsidControlMakePoolIntent args)
    | ArchInvocationLabel ARMASIDPoolAssign \<Rightarrow> Some (AsidPoolIntent AsidPoolAssignIntent )
    | ArchInvocationLabel ARMIRQIssueIRQHandler \<Rightarrow>
                          map_option IrqControlIntent
                                   (arch_transform_intent_issue_irq_handler args)
    | GenInvocationLabel DomainSetSet \<Rightarrow> map_option DomainIntent (transform_intent_domain args)"

lemmas transform_intent_tcb_defs =
  transform_intent_tcb_read_registers_def
  transform_intent_tcb_write_registers_def
  transform_intent_tcb_copy_registers_def
  transform_intent_tcb_configure_def
  transform_intent_tcb_set_priority_def
  transform_intent_tcb_set_mcpriority_def
  transform_intent_tcb_set_sched_params_def
  transform_intent_tcb_set_ipc_buffer_def
  transform_intent_tcb_set_space_def

lemma transform_tcb_intent_invocation:
  "transform_intent label args = Some (TcbIntent ti)
   \<Longrightarrow>
   (
   ((label = GenInvocationLabel TCBReadRegisters) = (ti = (TcbReadRegistersIntent ((args ! 0)!!0) 0 (args ! 1)) \<and> length args \<ge> 2)) \<and>
   ((label = GenInvocationLabel TCBWriteRegisters) = (ti = (TcbWriteRegistersIntent ((args ! 0)!!0) 0 (args ! 1) (drop 2 args)) \<and> length args \<ge> 2)) \<and>
   ((label = GenInvocationLabel TCBCopyRegisters) = (ti = (TcbCopyRegistersIntent ((args ! 0)!!0) ((args ! 0)!!1) ((args ! 0)!!2) ((args ! 0)!!3) 0) \<and> length args \<ge> 1)) \<and>
   ((label = GenInvocationLabel TCBConfigure) = (ti = (TcbConfigureIntent (args ! 0) (args ! 1) (args ! 2) (args ! 3)) \<and> length args \<ge> 4)) \<and>
   ((label = GenInvocationLabel TCBSetPriority) = (ti = (TcbSetPriorityIntent (prio_from_arg (args ! 0))) \<and> length args \<ge> 1)) \<and>
   ((label = GenInvocationLabel TCBSetMCPriority) = (ti = (TcbSetMCPriorityIntent (prio_from_arg (args ! 0))) \<and> length args \<ge> 1)) \<and>
   ((label = GenInvocationLabel TCBSetSchedParams) = (ti = (TcbSetSchedParamsIntent (prio_from_arg (args ! 0)) (prio_from_arg (args ! 1))) \<and> length args \<ge> 2)) \<and>
   ((label = GenInvocationLabel TCBSetSpace) = (ti = (TcbSetSpaceIntent (args ! 0) (args ! 1) (args ! 2)) \<and> length args \<ge> 3)) \<and>
   ((label = GenInvocationLabel TCBSuspend) = (ti = TcbSuspendIntent)) \<and>
   ((label = GenInvocationLabel TCBResume) = (ti = TcbResumeIntent)) \<and>
   ((label = GenInvocationLabel TCBBindNotification) = (ti = TcbBindNTFNIntent)) \<and>
   ((label = GenInvocationLabel TCBUnbindNotification) = (ti = TcbUnbindNTFNIntent)) \<and>
   ((label = GenInvocationLabel TCBSetTLSBase) = (ti = TcbSetTLSBaseIntent))
   ) \<and>
   (
    label \<noteq> GenInvocationLabel InvalidInvocation \<and>
    label \<noteq> GenInvocationLabel UntypedRetype \<and>
    label \<noteq> GenInvocationLabel CNodeRevoke \<and>
    label \<noteq> GenInvocationLabel CNodeDelete \<and>
    label \<noteq> GenInvocationLabel CNodeCancelBadgedSends \<and>
    label \<noteq> GenInvocationLabel CNodeCopy \<and>
    label \<noteq> GenInvocationLabel CNodeMint \<and>
    label \<noteq> GenInvocationLabel CNodeMove \<and>
    label \<noteq> GenInvocationLabel CNodeMutate \<and>
    label \<noteq> GenInvocationLabel CNodeRotate \<and>
    label \<noteq> GenInvocationLabel CNodeSaveCaller \<and>
    label \<noteq> GenInvocationLabel IRQIssueIRQHandler \<and>
    label \<noteq> GenInvocationLabel IRQAckIRQ \<and>
    label \<noteq> GenInvocationLabel IRQSetIRQHandler \<and>
    label \<noteq> GenInvocationLabel IRQClearIRQHandler \<and>
    label \<noteq> ArchInvocationLabel ARMPageTableMap \<and>
    label \<noteq> ArchInvocationLabel ARMPageTableUnmap \<and>
    label \<noteq> ArchInvocationLabel ARMPageMap \<and>
    label \<noteq> ArchInvocationLabel ARMPageUnmap \<and>
    label \<noteq> ArchInvocationLabel ARMPageClean_Data \<and>
    label \<noteq> ArchInvocationLabel ARMPageInvalidate_Data \<and>
    label \<noteq> ArchInvocationLabel ARMPageCleanInvalidate_Data \<and>
    label \<noteq> ArchInvocationLabel ARMPageUnify_Instruction \<and>
    label \<noteq> ArchInvocationLabel ARMPageGetAddress \<and>
    label \<noteq> ArchInvocationLabel ARMPDClean_Data \<and>
    label \<noteq> ArchInvocationLabel ARMPDInvalidate_Data \<and>
    label \<noteq> ArchInvocationLabel ARMPDCleanInvalidate_Data \<and>
    label \<noteq> ArchInvocationLabel ARMPDUnify_Instruction \<and>
    label \<noteq> ArchInvocationLabel ARMASIDControlMakePool \<and>
    label \<noteq> GenInvocationLabel DomainSetSet)"
  apply(intro conjI)
   apply(rule iffI,
         simp add: transform_intent_def transform_intent_tcb_defs split: list.split_asm,
         simp add: transform_intent_def transform_intent_tcb_defs
              split: gen_invocation_labels.split_asm invocation_label.split_asm
                     arch_invocation_label.split_asm list.split_asm)+
                               (* 30 subgoals *)
                               apply(simp add: transform_intent_def transform_intent_tcb_defs
                                          split: gen_invocation_labels.split_asm invocation_label.split_asm
                                                 arch_invocation_label.split_asm)+
  done

lemma transform_intent_isnot_UntypedIntent:
      "(\<not> (\<exists> ui. Some (UntypedIntent ui) = transform_intent label args))
       = ((label \<noteq> GenInvocationLabel UntypedRetype) \<or>
           (label = GenInvocationLabel UntypedRetype \<and> length args < 6) \<or>
           (label = GenInvocationLabel UntypedRetype \<and> length args \<ge> 6 \<and> args ! 0 > 10))"
  apply(rule iffI)
   apply(erule contrapos_np)
   apply(clarsimp)
   apply(simp add: transform_intent_def)
   apply(unfold transform_intent_untyped_retype_def)
   apply (clarsimp split: list.split, safe, simp_all)[1]
   apply (clarsimp simp: transform_type_def)
   apply (simp add: unat_arith_simps)
   apply (simp add: eval_nat_numeral linorder_not_less le_Suc_eq)
  apply(erule disjE)
   apply(auto simp: transform_intent_def option_map_def
              split: gen_invocation_labels.split invocation_label.split arch_invocation_label.split
                     option.split_asm)[1]
  apply (erule disjE)
   apply (auto simp: transform_intent_def transform_intent_untyped_retype_def
         option_map_def split: invocation_label.split option.split_asm list.split)[1]
  apply clarsimp
  apply (clarsimp simp: transform_intent_def transform_type_def transform_intent_untyped_retype_def)
  apply (clarsimp simp: option_map_def
                  split: invocation_label.splits arch_invocation_label.splits option.splits list.splits)
  apply (clarsimp simp: transform_type_def split: if_split_asm)
  done

lemma transform_cnode_index_and_depth_success:
       "(\<exists>ci. Some (C ci) =
            map_option C
             (transform_cnode_index_and_depth C2 args)) =
       (\<not> length args < 2)"
apply(rule iffI)
 apply(unfold option_map_def transform_cnode_index_and_depth_def)
 apply(case_tac args)
 apply(auto split: list.split)
done

lemmas transform_intent_cnode_defs =
  transform_cnode_index_and_depth_def
  transform_intent_cnode_copy_def
  transform_intent_cnode_mint_def
  transform_intent_cnode_move_def
  transform_intent_cnode_mutate_def
  transform_intent_cnode_rotate_def

method case_labels for label :: invocation_label =
  (cases label,
   find_goal \<open>match premises in "label = GenInvocationLabel x" for x \<Rightarrow> \<open>cases x\<close>\<close>,
   find_goal \<open>match premises in "label = ArchInvocationLabel x" for x \<Rightarrow> \<open>cases x\<close>\<close>)

lemma transform_intent_isnot_CNodeIntent:
      "(\<not> (\<exists> ui. Some (CNodeIntent ui) = transform_intent label args))
       = ((label = GenInvocationLabel CNodeRevoke \<longrightarrow> length args < 2) \<and>
          (label = GenInvocationLabel CNodeDelete \<longrightarrow> length args < 2) \<and>
          (label = GenInvocationLabel CNodeCancelBadgedSends \<longrightarrow> length args < 2) \<and>
          (label = GenInvocationLabel CNodeCopy \<longrightarrow> length args < 5) \<and>
          (label = GenInvocationLabel CNodeMint \<longrightarrow> length args < 6) \<and>
          (label = GenInvocationLabel CNodeMove \<longrightarrow> length args < 4) \<and>
          (label = GenInvocationLabel CNodeMutate \<longrightarrow> length args < 5) \<and>
          (label = GenInvocationLabel CNodeRotate \<longrightarrow> length args < 8) \<and>
          (label = GenInvocationLabel CNodeSaveCaller \<longrightarrow> length args < 2))"
  apply(rule iffI)
   apply(erule contrapos_np)
   apply(clarsimp simp: transform_intent_def)
   apply(cases label; simp)
   apply(rename_tac gen_label, case_tac gen_label;
           simp add: transform_intent_cnode_defs option_map_def
                split: list.split)
           prefer 10
           apply(clarify)
           apply(case_labels label;
                   clarsimp simp: transform_intent_def option_map_def transform_intent_cnode_defs
                            split: list.split_asm option.split_asm)
          apply(auto)
  done

lemma transform_intent_isnot_TcbIntent:
      "(\<not> (\<exists> ti. Some (TcbIntent ti) = transform_intent label args))
       = ((label = GenInvocationLabel TCBReadRegisters \<longrightarrow> length args < 2) \<and>
          (label = GenInvocationLabel TCBWriteRegisters \<longrightarrow> length args < 2) \<and>
          (label = GenInvocationLabel TCBCopyRegisters \<longrightarrow> length args < 1) \<and>
          (label = GenInvocationLabel TCBConfigure \<longrightarrow> length args < 4) \<and>
          (label = GenInvocationLabel TCBSetPriority \<longrightarrow> length args < 1) \<and>
          (label = GenInvocationLabel TCBSetMCPriority \<longrightarrow> length args < 1) \<and>
          (label = GenInvocationLabel TCBSetSchedParams \<longrightarrow> length args < 2) \<and>
          (label = GenInvocationLabel TCBSetIPCBuffer \<longrightarrow> length args < 1) \<and>
          (label = GenInvocationLabel TCBSetSpace \<longrightarrow> length args < 3) \<and>
          (label \<noteq> GenInvocationLabel TCBSuspend) \<and>
          (label \<noteq> GenInvocationLabel TCBResume) \<and>
          (label \<noteq> GenInvocationLabel TCBBindNotification) \<and>
          (label \<noteq> GenInvocationLabel TCBUnbindNotification) \<and>
          (label \<noteq> GenInvocationLabel TCBSetTLSBase))"
  apply(rule iffI)
    subgoal
      apply(erule contrapos_np)
      apply(clarsimp simp: transform_intent_def)
      apply(case_labels label; simp)
              apply(fastforce simp: transform_intent_tcb_defs option_map_def
                             split: list.split)+
      done
    apply(unfold transform_intent_def)
    apply(case_labels label; simp add: option_map_def split: option.split)
            apply(auto simp: transform_intent_tcb_defs
                      split: list.splits arch_invocation_label.splits)
  done

(*
 * Convert a partial function of type "word \<Rightarrow> 'b" into
 * a partial function of type "nat \<Rightarrow> 'b".
 *
 * It would be nice if we could just use the original
 * partial function as "p (unat x)". Unfortunately, this
 * would mean that "p ((unat x) + 2^32)" would return
 * some non-None value, which isn't what we want.
 *
 * Instead, return a new function that performs a range
 * check prior to calling the original function.
 *)
definition
  unat_map :: "(('a :: len) word \<rightharpoonup> 'b) \<Rightarrow> (nat \<rightharpoonup> 'b)"
where
  "unat_map x z \<equiv>
    if z < 2^len_of(TYPE('a)) then
      x (of_nat z)
    else
      None"

lemma unat_map_unat [simp]: "(unat_map p) (unat x) = p x"
  by (clarsimp simp: unat_map_def)

(*
 * Convert a cslot_ptr into a cdl_cap_ref.
 *)
definition
  transform_cslot_ptr :: "cslot_ptr \<Rightarrow> cdl_cap_ref"
where
  "transform_cslot_ptr \<equiv>
       \<lambda> (a, b). (a, nat (bl_to_bin b))"

(*
 * Convert an asid into a cdl_asid with asid_low_bits
 * hardcoded.
 *)
definition
  transform_asid :: "asid \<Rightarrow> cdl_asid"
where
  "transform_asid asid = (unat (asid_high_bits_of asid), unat (ucast asid :: 10 word))"

definition
  transform_mapping :: "(asid \<times> vspace_ref) option \<Rightarrow> cdl_mapped_addr option"
where
  " transform_mapping mp = option_map (\<lambda>x. (transform_asid (fst x),snd x)) mp"

(*
 * Transform a cap in the abstract spec to an equivalent
 * CapDL cap.
 *)

definition "free_range_of_untyped \<equiv> (\<lambda>idx size_bits ptr.
  (if (idx \<le> 2^size_bits - 1) then {ptr + of_nat idx .. ptr + 2^size_bits - 1} else {}))"
definition
  transform_cap :: "cap \<Rightarrow> cdl_cap"
where
  "transform_cap c \<equiv> case c of
      Structures_A.NullCap \<Rightarrow>
        Types_D.NullCap
    | Structures_A.UntypedCap dev ptr size_bits idx \<Rightarrow>
        Types_D.UntypedCap dev {ptr .. ptr + 2^ size_bits - 1}
        (free_range_of_untyped idx size_bits ptr)
    | Structures_A.EndpointCap ptr badge cap_rights_ \<Rightarrow>
        Types_D.EndpointCap ptr badge cap_rights_
    | Structures_A.NotificationCap ptr badge cap_rights_ \<Rightarrow>
        Types_D.NotificationCap ptr badge cap_rights_
    | Structures_A.ReplyCap ptr is_master cap_rights_ \<Rightarrow>
        if is_master then Types_D.MasterReplyCap ptr else Types_D.ReplyCap ptr cap_rights_
    | Structures_A.CNodeCap ptr size_bits guard \<Rightarrow>
        Types_D.CNodeCap ptr (of_bl guard) (length guard) size_bits
    | Structures_A.ThreadCap ptr \<Rightarrow>
        Types_D.TcbCap ptr
    | Structures_A.DomainCap \<Rightarrow>
        Types_D.DomainCap
    | Structures_A.IRQControlCap \<Rightarrow>
        Types_D.IrqControlCap
    | Structures_A.IRQHandlerCap irq \<Rightarrow>
        Types_D.IrqHandlerCap irq
    | Structures_A.Zombie ptr _ _ \<Rightarrow>
        Types_D.ZombieCap ptr
    | Structures_A.ArchObjectCap arch_cap \<Rightarrow> (case arch_cap of
          ARM_A.ASIDControlCap \<Rightarrow>
            Types_D.AsidControlCap
        | ARM_A.ASIDPoolCap ptr asid \<Rightarrow>
            Types_D.AsidPoolCap ptr (fst $ (transform_asid asid))
        | ARM_A.PageCap dev ptr cap_rights_ sz mp \<Rightarrow>
            Types_D.FrameCap dev ptr cap_rights_ (pageBitsForSize sz) Real (transform_mapping mp)
        | ARM_A.PageTableCap ptr mp \<Rightarrow>
            Types_D.PageTableCap ptr Real (transform_mapping mp)
        | ARM_A.PageDirectoryCap ptr mp \<Rightarrow>
            Types_D.PageDirectoryCap ptr Real (option_map transform_asid mp)
        )
  "

(* Transform a list of (caps, refs) into CDL equivalents. *)
definition
  transform_cap_list :: "(cap \<times> cslot_ptr) list
      \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list"
where
  "transform_cap_list \<equiv>
     map (\<lambda>(cap, slot). (transform_cap cap, transform_cslot_ptr slot))"


\<comment> \<open>Convert a nat into a bool list of the given size.\<close>
definition
  nat_to_bl :: "nat \<Rightarrow> nat \<Rightarrow> bool list option"
where
  "nat_to_bl bits n \<equiv>
    if n \<ge> 2^bits then
      None
    else
      Some $ bin_to_bl bits (of_nat n)"

lemma nat_to_bl_id [simp]: "nat_to_bl (size (x :: (('a::len) word))) (unat x) = Some (to_bl x)"
  by (clarsimp simp: nat_to_bl_def to_bl_def le_def word_size)

(* FIXME: MOVE *)
definition
  option_join :: "'a option option \<Rightarrow> 'a option"
where
  "option_join x \<equiv> case x of
                      Some (Some y) \<Rightarrow> Some y
                    | _             \<Rightarrow> None"

definition
  option_map_join :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a option \<Rightarrow> 'b option"
where
  "option_map_join f x \<equiv> case x of
                      Some y        \<Rightarrow> f y
                    | _             \<Rightarrow> None"

lemmas option_map_join_simps = option_map_join_def [split_simps option.split]

(* Transform a CNode. *)

definition
  transform_cnode_contents :: "nat \<Rightarrow> cnode_contents \<Rightarrow> cdl_cap_map"
where
  "transform_cnode_contents sz c \<equiv> \<lambda>n. option_map transform_cap (option_map_join c (nat_to_bl sz n))"


(* Create a "TCB pending operation" cap based on the given thread's
 * current state. *)

definition
  infer_tcb_pending_op :: "obj_ref \<Rightarrow> Structures_A.thread_state \<Rightarrow> cdl_cap"
where
  "infer_tcb_pending_op ptr t \<equiv>
    case t of
        Structures_A.BlockedOnReceive ptr payload \<Rightarrow>
          PendingSyncRecvCap ptr False (receiver_can_grant payload)

      | Structures_A.BlockedOnReply \<Rightarrow>
          PendingSyncRecvCap ptr True False

      | Structures_A.BlockedOnSend ptr payload \<Rightarrow>
          PendingSyncSendCap ptr
              (sender_badge payload) (sender_is_call payload)
              (sender_can_grant payload) (sender_can_grant_reply payload)
              False

      | Structures_A.BlockedOnNotification ptr \<Rightarrow>
          PendingNtfnRecvCap ptr

      | Structures_A.Restart \<Rightarrow> RestartCap

      | Structures_A.Running \<Rightarrow> RunningCap

      | _ \<Rightarrow> Types_D.NullCap
   "

(* Create a "Bound NTFN" cap based on the given thread's
 * current state. *)

definition
  infer_tcb_bound_notification :: "obj_ref option \<Rightarrow> cdl_cap"
where
  "infer_tcb_bound_notification a \<equiv> case a of
      Some ntfn \<Rightarrow> BoundNotificationCap ntfn
    | _ \<Rightarrow> Types_D.NullCap"

definition
  evalMonad :: "('s, 'a) nondet_monad \<Rightarrow> 's \<Rightarrow> 'a option"
where
  "evalMonad m s = (if fst (m s) = {} then None else Some (SOME x. x \<in> fst ` (fst (m s))))"

(* The monad here avoids repeating the def of loadWord *)
definition
  get_ipc_buffer_words :: "machine_state \<Rightarrow> tcb \<Rightarrow> nat list \<Rightarrow> word32 list"
where
  "get_ipc_buffer_words ms tcb ns \<equiv>
    let
      p = tcb_ipc_buffer tcb;
      cap = tcb_ipcframe tcb;
      wordsM = case cap of
               cap.ArchObjectCap (arch_cap.PageCap dev buf rights sz mapdata) \<Rightarrow> if AllowRead \<in> rights then
                   mapM loadWord (map (\<lambda>n. buf + (p && mask(pageBitsForSize sz)) + (of_nat (n * word_size))) ns)
                   else return []
              | _ \<Rightarrow> return []
    in
      the (evalMonad wordsM ms)"

definition
  get_tcb_message_info :: "tcb \<Rightarrow> Structures_A.message_info"
where
  "get_tcb_message_info t \<equiv>
     data_to_message_info ((user_regs (arch_tcb_context_get (tcb_arch t))) msg_info_register)"

definition
  get_tcb_mrs :: "machine_state \<Rightarrow> tcb \<Rightarrow> word32 list"
where
  "get_tcb_mrs ms tcb \<equiv>
    let
      info = get_tcb_message_info tcb;
      cpu_mrs = map (user_regs (arch_tcb_context_get (tcb_arch tcb))) msg_registers;
      mem_mrs = get_ipc_buffer_words ms tcb [length msg_registers + 1 ..< Suc msg_max_length]
    in
      (take (unat (mi_length info)) (cpu_mrs @ mem_mrs))"

(* Convert contents of the user's IPC buffer into an intent. *)
definition "guess_error \<equiv> \<lambda>x. x \<noteq> (0::word32)"

definition
  transform_full_intent :: "machine_state \<Rightarrow> obj_ref \<Rightarrow> tcb \<Rightarrow> cdl_full_intent"
where
  "transform_full_intent ms r tcb \<equiv>
  let mi = get_tcb_message_info tcb;
      offset = msg_max_length + msg_max_extra_caps + 2
  in
  \<lparr> cdl_intent_op = (transform_intent
                     (invocation_type (mi_label mi))
                     (get_tcb_mrs ms tcb)),
    cdl_intent_error = guess_error (mi_label mi),
    cdl_intent_cap = user_regs (arch_tcb_context_get (tcb_arch tcb)) cap_register,
    cdl_intent_extras = get_ipc_buffer_words ms tcb [buffer_cptr_index ..< buffer_cptr_index + (unat (mi_extra_caps mi))],
    cdl_intent_recv_slot = case (get_ipc_buffer_words ms tcb [offset ..< offset + 3]) of
                                [croot, index, depth] \<Rightarrow> Some (croot, index, unat depth)
                              | _                    \<Rightarrow> None
  \<rparr>"

lemma invocation_type0:
  "invocation_type 0 = GenInvocationLabel InvalidInvocation"
  by (clarsimp simp: invocation_type_def toEnum_def enum_invocation_label enum_gen_invocation_labels)

(* Transform a TCB object. *)
abbreviation
  "tcb_has_fault \<equiv> \<lambda>tcb. tcb_fault tcb \<noteq> None"

definition
  transform_tcb :: "machine_state \<Rightarrow> obj_ref \<Rightarrow> tcb \<Rightarrow> cdl_object"
where
  "transform_tcb ms ptr tcb \<equiv>
    Types_D.Tcb \<lparr> cdl_tcb_caps = [
                   tcb_cspace_slot \<mapsto> (transform_cap $ tcb_ctable tcb),
                   tcb_vspace_slot \<mapsto> (transform_cap $ tcb_vtable tcb),
                   tcb_replycap_slot \<mapsto> (transform_cap $ tcb_reply tcb),
                   tcb_caller_slot \<mapsto> (transform_cap $ tcb_caller tcb),
                   tcb_ipcbuffer_slot \<mapsto> (transform_cap $ tcb_ipcframe tcb),
                   tcb_pending_op_slot \<mapsto> (infer_tcb_pending_op ptr (tcb_state tcb)),
                   tcb_boundntfn_slot \<mapsto> (infer_tcb_bound_notification (tcb_bound_notification tcb))
                 ],

                 cdl_tcb_fault_endpoint = (of_bl (tcb_fault_handler tcb)),

                 \<comment> \<open>Decode the thread's intent.\<close>
                 cdl_tcb_intent = transform_full_intent ms ptr tcb,
                 cdl_tcb_has_fault = (tcb_has_fault tcb),
                 cdl_tcb_domain = tcb_domain tcb
                \<rparr>"

definition
  transform_asid_pool_entry :: "obj_ref option \<Rightarrow> cdl_cap"
where
  "transform_asid_pool_entry p \<equiv> case p of
       None \<Rightarrow> Types_D.NullCap
     | Some p \<Rightarrow> Types_D.PageDirectoryCap p Fake None"

(*
 * Transform an AsidPool.
 *
 * This converts the object references into PageDirectory caps.
 *)
definition
  transform_asid_pool_contents :: "(10 word \<Rightarrow> obj_ref option) \<Rightarrow> cdl_cap_map"
where
  "transform_asid_pool_contents M \<equiv> unat_map (Some \<circ> transform_asid_pool_entry \<circ> M)"

definition
  transform_paddr :: "paddr \<Rightarrow> cdl_object_id"
where
 "transform_paddr = ptrFromPAddr"

declare transform_paddr_def[simp]

(*
 * Transform a PageTable, one entry(PTE) at a time.
 *
 * This transforms the references to frames into frame caps.
 *)
definition
  transform_pte :: "ARM_A.pte \<Rightarrow> cdl_cap"
where
  "transform_pte pte \<equiv> case pte of
           ARM_A.InvalidPTE \<Rightarrow> cdl_cap.NullCap
         | ARM_A.LargePagePTE ref _ rights_ \<Rightarrow>
             Types_D.FrameCap False (transform_paddr ref) rights_
                              (pageBitsForSize ARMLargePage) Fake None
         | ARM_A.SmallPagePTE ref _ rights_ \<Rightarrow>
             Types_D.FrameCap False (transform_paddr ref) rights_
                              (pageBitsForSize ARMSmallPage) Fake None"

definition
  transform_page_table_contents :: "(word8 \<Rightarrow> ARM_A.pte) \<Rightarrow> (nat \<Rightarrow> cdl_cap option)"
where
  "transform_page_table_contents M \<equiv> unat_map (Some o transform_pte o M)"

(*
 * Transform a PageDirectory, one entry(PDE) at a time.
 *
 * This transforms the references to frames into PageTable or Frame caps.
 *)
definition
  transform_pde :: "ARM_A.pde \<Rightarrow> cdl_cap"
where
  "transform_pde pde \<equiv> case pde of
           ARM_A.InvalidPDE \<Rightarrow> cdl_cap.NullCap
         | ARM_A.PageTablePDE ref _ _ \<Rightarrow>
             Types_D.PageTableCap (transform_paddr ref) Fake None
         | ARM_A.SectionPDE ref _ _ rights_ \<Rightarrow>
             Types_D.FrameCap False (transform_paddr ref) rights_
                              (pageBitsForSize ARMSection) Fake None
         | ARM_A.SuperSectionPDE ref _ rights_ \<Rightarrow>
             Types_D.FrameCap False (transform_paddr ref) rights_
                              (pageBitsForSize ARMSuperSection) Fake None"

definition
  kernel_pde_mask ::  "(12 word \<Rightarrow> ARM_A.pde) \<Rightarrow> (12 word \<Rightarrow> ARM_A.pde)"
where
  "kernel_pde_mask M \<equiv> \<lambda>x.
  if (ucast (kernel_base >> 20)) \<le> x then ARM_A.InvalidPDE else M x"

definition
  transform_page_directory_contents :: "(12 word \<Rightarrow> ARM_A.pde) \<Rightarrow> (nat \<Rightarrow> cdl_cap option)"
where
  "transform_page_directory_contents M \<equiv> unat_map (Some o transform_pde o kernel_pde_mask M)"

(* Transform a kernel object. *)
definition
  transform_object :: "machine_state \<Rightarrow> obj_ref \<Rightarrow> kernel_object \<Rightarrow> cdl_object"
  where
  "transform_object ms ref ko \<equiv> case ko of
           Structures_A.CNode 0 c \<Rightarrow>
              Types_D.IRQNode \<lparr>cdl_irq_node_caps = transform_cnode_contents 0 c\<rparr>
         | Structures_A.CNode sz c \<Rightarrow>
              Types_D.CNode \<lparr>
                cdl_cnode_caps = transform_cnode_contents sz c,
                cdl_cnode_size_bits = sz
                \<rparr>
         | Structures_A.TCB tcb \<Rightarrow> transform_tcb ms ref tcb
         | Structures_A.Endpoint _ \<Rightarrow> Types_D.Endpoint
         | Structures_A.Notification _ \<Rightarrow> Types_D.Notification
         | Structures_A.ArchObj (ARM_A.ASIDPool ap) \<Rightarrow>
                Types_D.AsidPool \<lparr>cdl_asid_pool_caps = (transform_asid_pool_contents ap)\<rparr>
         | Structures_A.ArchObj (ARM_A.PageTable ptx) \<Rightarrow>
                Types_D.PageTable \<lparr>cdl_page_table_caps = (transform_page_table_contents ptx)\<rparr>
         | Structures_A.ArchObj (ARM_A.PageDirectory pd) \<Rightarrow>
                Types_D.PageDirectory \<lparr>cdl_page_directory_caps = (transform_page_directory_contents pd)\<rparr>
         | Structures_A.ArchObj (ARM_A.DataPage dev sz) \<Rightarrow>
                Types_D.Frame \<lparr>cdl_frame_size_bits = pageBitsForSize sz\<rparr>"

lemmas transform_object_simps [simp] =
  transform_object_def [split_simps Structures_A.kernel_object.split ARM_A.arch_kernel_obj.split]

(* Lifts a map over a function, returning the empty map if that
   function would be insufficiently injective *)
definition
  map_lift_over :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<rightharpoonup> 'a) \<Rightarrow> ('b \<rightharpoonup> 'b)"
where
 "map_lift_over f m = (if inj_on f (dom m \<union> ran m)
    then (\<lambda>x. if \<exists>y. f y = x \<and> y \<in> dom m
              then map_option f (m (inv_into (dom m) f x)) else None)
    else Map.empty)"

(* Transform the CDT. *)
definition
  transform_cdt :: "'z::state_ext state \<Rightarrow> cdl_cdt"
where
  "transform_cdt s =
     map_lift_over transform_cslot_ptr (cdt s)"

definition
  get_obj :: "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> kernel_object option"
where
  "get_obj s r \<equiv> (kheap s) r"

definition
  cap_installed_at_irq :: "irq \<Rightarrow> 'z::state_ext state \<Rightarrow> cap option"
where
  "cap_installed_at_irq irq s \<equiv> caps_of_state s (interrupt_irq_node s irq, [])"

abbreviation
  option_map2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> 'c option"
where
  "option_map2 f opt_a opt_b \<equiv> case opt_a of
                                   None \<Rightarrow> None
                                 | Some a \<Rightarrow> (case opt_b of
                                                 None \<Rightarrow> None
                                               | Some b \<Rightarrow> Some (f a b))"





(* Transform objects in the abstract spec to CapDL.
   Empty memory is transformed into Untyped objects. *)
definition
  transform_objects :: "det_ext state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object option)"
where
   "transform_objects s = (\<lambda>ptr. Some Types_D.Untyped) |` (- {idle_thread s}) ++
                           (\<lambda>ptr. map_option (transform_object (machine_state s) ptr)
                                ((kheap s  |` (- {idle_thread s})) ptr))"

lemma evalMonad_return [simp]:
  "evalMonad (return x) s = Some x"
  by (simp add: evalMonad_def return_def)

definition
  "det_or_fail f \<equiv> \<forall>s. fst (f s) = {} \<or> (\<exists>r. fst (f s) = {r})"

lemma evalMonad_bind:
  assumes f: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  assumes det: "det_or_fail f"
  shows "evalMonad (f >>= g) s = (if evalMonad f s = None then None else evalMonad (g (the (evalMonad f s))) s)"
  apply (case_tac "evalMonad f s")
   apply (simp add: evalMonad_def split: if_split_asm)
   apply (simp add: bind_def)
  apply simp
  apply (simp add: evalMonad_def)
  apply (clarsimp simp: bind_def)
  apply (insert det)
  apply (clarsimp simp: det_or_fail_def split: if_split_asm)
  apply (erule_tac x=s in allE)
  apply clarsimp
  apply (subgoal_tac "b = s")
   apply simp
  apply (subgoal_tac "(a,b) \<in> fst (f s)")
   apply (drule use_valid, rule f [where P="(=) s"])
    apply (rule refl)
   apply simp
  apply simp
  done

lemma bind_dfI:
  "\<lbrakk> det_or_fail f; \<And>x. det_or_fail (g x) \<rbrakk> \<Longrightarrow> det_or_fail (f >>= g)"
  apply (auto simp: det_or_fail_def bind_def split_def)
  apply force
  done

lemma return_df:
  "det_or_fail (return x)"
  by (simp add: det_or_fail_def return_def)

lemma assert_df:
  "det_or_fail (assert P)"
  by (simp add: assert_def fail_def det_or_fail_def return_def)

lemma mapM_df:
  "(\<And>x. det_or_fail (f x)) \<Longrightarrow> det_or_fail (mapM f xs)"
  apply (induct xs)
   apply (simp add: mapM_Nil return_df)
  apply (simp add: mapM_Cons)
  apply (rule bind_dfI, assumption)
  apply (rule bind_dfI, assumption)
  apply (rule return_df)
  done

lemma df_loadWord: "det_or_fail (loadWord x)"
  apply (unfold loadWord_def)
  apply (rule bind_dfI)
   apply (simp add: simpler_gets_def det_or_fail_def)
  apply clarsimp
  apply (rule bind_dfI)
   apply (rule assert_df)
  apply (rule return_df)
  done

lemma evalMonad_loadWord_cong:
  "underlying_memory ms = underlying_memory ms' \<Longrightarrow>
  evalMonad (loadWord x) ms = evalMonad (loadWord x) ms'"
  by (simp add: loadWord_def bind_def simpler_gets_def assert_def
                return_def fail_def evalMonad_def)

lemma evalMonad_mapM_cong:
  assumes f: "\<And>x. evalMonad (f x) ms = evalMonad (f x) ms'"
  assumes P: "\<And>P x. \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>_. P\<rbrace>"
  assumes det: "\<And>x. det_or_fail (f x)"
  shows "evalMonad (mapM f xs) ms = evalMonad (mapM f xs) ms'"
  apply (induct xs)
   apply (simp add: mapM_Nil)
  apply (simp add: mapM_Cons)
  apply (subst evalMonad_bind [OF P det])
  apply (subst evalMonad_bind [OF P det])
  apply (clarsimp simp: f)
  apply (subst evalMonad_bind)
    apply (wp mapM_wp' P)
   apply (rule mapM_df, rule det)
  apply (subst evalMonad_bind)
    apply (wp mapM_wp' P)
   apply (rule mapM_df, rule det)
  apply simp
  done

lemma evalMonad_mapM_loadWord_cong:
  "underlying_memory ms = underlying_memory ms' \<Longrightarrow>
   evalMonad (mapM loadWord xs) ms = evalMonad (mapM loadWord xs) ms'"
  apply (rule evalMonad_mapM_cong)
    apply (simp cong: evalMonad_loadWord_cong)
   apply (wp loadWord_inv)
  apply (rule df_loadWord)
  done

lemma get_ipc_buffer_words_cong:
  "underlying_memory ms = underlying_memory ms' \<Longrightarrow>
   get_ipc_buffer_words ms = get_ipc_buffer_words ms'"
  apply (rule ext)+
  apply (simp add: get_ipc_buffer_words_def Let_def cong: evalMonad_mapM_loadWord_cong
              split: cap.splits arch_cap.splits)
  done

lemma get_tcb_mrs_cong:
  "underlying_memory ms = underlying_memory ms' \<Longrightarrow> get_tcb_mrs ms = get_tcb_mrs ms'"
  apply (rule ext)
  apply (simp add: get_tcb_mrs_def Let_def cong: get_ipc_buffer_words_cong)
  done

lemma transform_objects_ms_underlying_mem:
  "transform_objects s =
   transform_objects (s \<lparr> machine_state :=
     undefined \<lparr> underlying_memory := underlying_memory (machine_state s) \<rparr> \<rparr>)"
  supply option.case_cong[cong]
  apply (rule ext)
  apply (simp add: transform_objects_def map_add_def option_map_def
            split: option.split)
  apply (simp add: transform_object_def transform_tcb_def
                   transform_full_intent_def Let_def
            split: Structures_A.kernel_object.split)
  apply (clarsimp simp: transform_intent_def cong: get_tcb_mrs_cong get_ipc_buffer_words_cong)
  done

lemmas transform_objects_def2
    = trans [OF transform_objects_ms_underlying_mem
                transform_objects_def,
             simplified]

(*
 * Transform the current thread in the abstract spec to CapDL.
 *
 * We just return the thread's memory address, unless it happens
 * to be the idle thread, which CapDL maps as "None".
 *)
definition
  transform_current_thread :: "'z::state_ext state \<Rightarrow> cdl_object_id option"
where
  "transform_current_thread s \<equiv>
    if (cur_thread s \<noteq> idle_thread s) then
      Some (cur_thread s)
    else
      None"

definition
  transform_asid_table_entry :: "obj_ref option \<Rightarrow> cdl_cap"
where
  "transform_asid_table_entry p \<equiv> case p of
       None \<Rightarrow> Types_D.NullCap
     | Some p \<Rightarrow> Types_D.AsidPoolCap p 0"

definition
  transform_asid_table :: "'z::state_ext state \<Rightarrow> cdl_cap_map"
where
  "transform_asid_table s \<equiv>
    let asid_table = arm_asid_table $ arch_state s
    in unat_map (Some \<circ> transform_asid_table_entry \<circ> asid_table)"

definition
  transform_current_domain :: "det_ext state \<Rightarrow> word8"
where
  "transform_current_domain s = cur_domain s"

(*
 * Transform an abstract spec state into the corresponding
 * CDL state.
 *)
definition
  transform :: "det_ext state \<Rightarrow> cdl_state"
where
  "transform s \<equiv> \<lparr>
    cdl_arch           = ARM11,
    cdl_objects        = transform_objects s,
    cdl_cdt            = transform_cdt s,
    cdl_current_thread = transform_current_thread s,
    cdl_irq_node       = interrupt_irq_node s,
    cdl_asid_table     = transform_asid_table s,
    cdl_current_domain = transform_current_domain s
    \<rparr>"

end

end

