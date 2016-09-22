(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

(*
 * Operations on interrupt objects.
 *)

theory Interrupt_D
imports Endpoint_D "../machine/$L4V_ARCH/Platform"
begin

context begin interpretation Arch .
requalify_types
  irq

requalify_consts
  maxIRQ
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
  decode_irq_control_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
      cdl_irq_control_intent \<Rightarrow> cdl_irq_control_invocation except_monad"
where
  "decode_irq_control_invocation target target_ref caps intent \<equiv> case intent of
      (* Create an IRQ handler cap for the given IRQ, placing it
       * in the specified CNode slot. *)
      IrqControlIssueIrqHandlerIntent irq index depth \<Rightarrow>
        doE
          root \<leftarrow> throw_on_none $ get_index caps 0;
          cnode_cap \<leftarrow> returnOk $ fst root;
          dest_slot_cap_ref \<leftarrow> lookup_slot_for_cnode_op cnode_cap index (unat depth);
          returnOk $ IssueIrqHandler irq target_ref dest_slot_cap_ref
        odE \<sqinter> throw
    | IrqControlArchIrqControlIntent \<Rightarrow> throw
  "

definition
  decode_irq_handler_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
      cdl_irq_handler_intent \<Rightarrow> cdl_irq_handler_invocation except_monad"
where
  "decode_irq_handler_invocation target target_ref caps intent \<equiv> case intent of
    (* Acknowledge an IRQ. *)
    IrqHandlerAckIntent \<Rightarrow>
      doE
        irq \<leftarrow> liftE $ assert_opt $ cdl_cap_irq target;
        returnOk $ AckIrq irq
      odE \<sqinter> throw

    (* Modify the IRQ so that it no longer sends to an endpoint. *)
    | IrqHandlerClearIntent \<Rightarrow>
      doE
        irq \<leftarrow> liftE $ assert_opt $ cdl_cap_irq target;
        returnOk $ ClearIrqHandler irq
      odE \<sqinter> throw

    (* Setup an IRQ to cause an endpoint to be sent to. *)
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
  invoke_irq_control :: "cdl_irq_control_invocation \<Rightarrow> unit k_monad"
where
  "invoke_irq_control params \<equiv> case params of
      (* Create a new IRQ handler cap. *)
      IssueIrqHandler irq control_slot dest_slot \<Rightarrow>
        insert_cap_child (IrqHandlerCap irq) control_slot dest_slot
  "

definition
  invoke_irq_handler :: "cdl_irq_handler_invocation \<Rightarrow> unit k_monad"
where
  "invoke_irq_handler params \<equiv> case params of
      (* Acknowledge and unmask an IRQ. *)
      AckIrq irq \<Rightarrow> return ()

      (* Attach an IRQ handler to write to an endpoint. *)
    | SetIrqHandler irq cap slot \<Rightarrow>
        do
          irqslot \<leftarrow> gets (get_irq_slot irq);
          delete_cap_simple irqslot;
          insert_cap_child cap slot irqslot \<sqinter> insert_cap_sibling cap slot irqslot
        od

      (* Deassociate this handler with all endpoints. *)
    | ClearIrqHandler irq \<Rightarrow>
        do
          irqslot \<leftarrow> gets (get_irq_slot irq);
          delete_cap_simple irqslot
        od
  "

(* Handle an interrupt. *)
definition
  handle_interrupt :: "cdl_irq \<Rightarrow> unit k_monad"
where
  "handle_interrupt irq \<equiv> if (irq > maxIRQ) then return () else 
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
