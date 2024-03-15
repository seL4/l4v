(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Operations on interrupt objects.
 *)

theory Interrupt_D
imports Endpoint_D "ExecSpec.Platform"
begin

context begin interpretation Arch .
requalify_types
  irq
end

(* Return the currently pending IRQ. *)
definition
  get_active_irq :: "(cdl_irq option) k_monad"
where
  "get_active_irq \<equiv>
    do
      irq \<leftarrow> select UNIV;
      return $ Some irq
    od \<sqinter> (return None)
  "

definition
  arch_decode_irq_control_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
      cdl_arch_irq_control_intent \<Rightarrow> cdl_irq_control_invocation except_monad"
where
  "arch_decode_irq_control_invocation target target_ref caps intent \<equiv> case intent of
     ARMIrqControlIssueIrqHandlerIntent irq index depth \<Rightarrow>
        doE
          root \<leftarrow> throw_on_none $ get_index caps 0;
          cnode_cap \<leftarrow> returnOk $ fst root;
          dest_slot_cap_ref \<leftarrow> lookup_slot_for_cnode_op cnode_cap index (unat depth);
          returnOk $ IssueIrqHandler irq target_ref dest_slot_cap_ref
        odE \<sqinter> throw
   | ARMIssueSGISignalIntent irq target index depth \<Rightarrow>
        doE
          root \<leftarrow> throw_on_none $ get_index caps 0;
          cnode_cap \<leftarrow> returnOk $ fst root;
          dest_slot_cap_ref \<leftarrow> lookup_slot_for_cnode_op cnode_cap index (unat depth);
          ensure_empty dest_slot_cap_ref;
          returnOk $ ArchIssueIrqHandler (ARMIssueSGISignal (ucast irq) (ucast target)
                                                            target_ref dest_slot_cap_ref)
        odE \<sqinter> throw"

definition
  decode_irq_control_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
      cdl_irq_control_intent \<Rightarrow> cdl_irq_control_invocation except_monad"
where
  "decode_irq_control_invocation target target_ref caps intent \<equiv> case intent of
      \<comment> \<open>Create an IRQ handler cap for the given IRQ, placing it
         in the specified CNode slot.\<close>
      IrqControlIssueIrqHandlerIntent irq index depth \<Rightarrow>
        doE
          root \<leftarrow> throw_on_none $ get_index caps 0;
          cnode_cap \<leftarrow> returnOk $ fst root;
          dest_slot_cap_ref \<leftarrow> lookup_slot_for_cnode_op cnode_cap index (unat depth);
          returnOk $ IssueIrqHandler irq target_ref dest_slot_cap_ref
        odE \<sqinter> throw
    | ArchIrqControlIssueIrqHandlerIntent arch_intent \<Rightarrow>
        arch_decode_irq_control_invocation target target_ref caps arch_intent"

definition
  decode_irq_handler_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
      cdl_irq_handler_intent \<Rightarrow> cdl_irq_handler_invocation except_monad"
where
  "decode_irq_handler_invocation target target_ref caps intent \<equiv> case intent of
    \<comment> \<open>Acknowledge an IRQ.\<close>
    IrqHandlerAckIntent \<Rightarrow>
      doE
        irq \<leftarrow> liftE $ assert_opt $ cdl_cap_irq target;
        returnOk $ AckIrq irq
      odE \<sqinter> throw

    \<comment> \<open>Modify the IRQ so that it no longer sends to an endpoint.\<close>
    | IrqHandlerClearIntent \<Rightarrow>
      doE
        irq \<leftarrow> liftE $ assert_opt $ cdl_cap_irq target;
        returnOk $ ClearIrqHandler irq
      odE \<sqinter> throw

    \<comment> \<open>Setup an IRQ to cause an endpoint to be sent to.\<close>
    | IrqHandlerSetEndpointIntent \<Rightarrow>
      doE
        endpoint \<leftarrow> throw_on_none $ get_index caps 0;
        endpoint_cap \<leftarrow> returnOk $ fst endpoint;
        endpoint_cap_ref \<leftarrow> returnOk $ snd endpoint;
        irq \<leftarrow> liftE $ assert_opt $ cdl_cap_irq target;
        case endpoint_cap of
              NotificationCap x _ _ \<Rightarrow> returnOk ()
              | _                    \<Rightarrow> throw;
        returnOk $ SetIrqHandler irq endpoint_cap endpoint_cap_ref
      odE \<sqinter> throw
  "

definition
  arch_invoke_irq_control :: "arch_cdl_irq_control_invocation \<Rightarrow> unit k_monad"
where
  "arch_invoke_irq_control params \<equiv> case params of
      ARMIssueSGISignal irq target control_slot dest_slot \<Rightarrow>
        insert_cap_child (SGISignalCap irq target) control_slot dest_slot"

definition
  invoke_irq_control :: "cdl_irq_control_invocation \<Rightarrow> unit k_monad"
where
  "invoke_irq_control params \<equiv> case params of
      \<comment> \<open>Create a new IRQ handler cap.\<close>
      IssueIrqHandler irq control_slot dest_slot \<Rightarrow>
        insert_cap_child (IrqHandlerCap irq) control_slot dest_slot
    | ArchIssueIrqHandler arch_inv \<Rightarrow>
        arch_invoke_irq_control arch_inv"

definition
  invoke_irq_handler :: "cdl_irq_handler_invocation \<Rightarrow> unit k_monad"
where
  "invoke_irq_handler params \<equiv> case params of
      \<comment> \<open>Acknowledge and unmask an IRQ.\<close>
      AckIrq irq \<Rightarrow> return ()

      \<comment> \<open>Attach an IRQ handler to write to an endpoint.\<close>
    | SetIrqHandler irq cap slot \<Rightarrow>
        do
          irqslot \<leftarrow> gets (get_irq_slot irq);
          delete_cap_simple irqslot;
          insert_cap_child cap slot irqslot \<sqinter> insert_cap_sibling cap slot irqslot
        od

      \<comment> \<open>Deassociate this handler with all endpoints.\<close>
    | ClearIrqHandler irq \<Rightarrow>
        do
          irqslot \<leftarrow> gets (get_irq_slot irq);
          delete_cap_simple irqslot
        od
  "

(* performs machine op only *)
definition invoke_sgi_signal_generate :: "cdl_sgi_signal_invocation \<Rightarrow> unit k_monad" where
  "invoke_sgi_signal_generate params \<equiv> return ()"

(* Handle an interrupt. *)
definition
  handle_interrupt :: "cdl_irq \<Rightarrow> unit k_monad"
where
  "handle_interrupt irq \<equiv> if irq > maxIRQ then return () else
    do
      irq_slot \<leftarrow> gets $ get_irq_slot irq;
      c \<leftarrow> gets $ opt_cap irq_slot;
      case c of
          None \<Rightarrow> return ()
        | Some cap \<Rightarrow> (
            case cap of
              (NotificationCap obj _ rights) \<Rightarrow>
                  if (Write \<in> rights) then send_signal obj else return ()
              | _ \<Rightarrow> return ()
          )
    od
  "

definition
  handle_pending_interrupts :: "unit k_monad"
where
  "handle_pending_interrupts \<equiv>
    do
      active \<leftarrow> get_active_irq;
      case active of
          Some irq \<Rightarrow> handle_interrupt irq
        | None \<Rightarrow> return ()
    od"

end
