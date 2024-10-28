(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Formalisation of interrupt handling.
*)

chapter "Interrupts"

theory Interrupt_A
imports ArchInterrupt_A
begin

arch_requalify_consts (A)
  arch_invoke_irq_control
  arch_invoke_irq_handler
  handle_reserved_irq
  arch_mask_irq_signal

text \<open>The IRQControl capability can be used to create a new IRQHandler
capability as well as to perform whatever architecture specific interrupt
actions are available.\<close>
fun
  invoke_irq_control :: "irq_control_invocation \<Rightarrow> (unit,'z::state_ext) p_monad"
where
  "invoke_irq_control (IRQControl irq handler_slot control_slot) =
     liftE (do set_irq_state IRQSignal irq;
               cap_insert (IRQHandlerCap irq) control_slot handler_slot od)"
| "invoke_irq_control (ArchIRQControl invok) =
     arch_invoke_irq_control invok"

text \<open>The IRQHandler capability may be used to configure how interrupts on an
IRQ are delivered and to acknowledge a delivered interrupt. Interrupts are
delivered when Notification capabilities are installed in the relevant per-IRQ
slot. The IRQHandler operations load or clear those capabilities.\<close>

fun
  invoke_irq_handler :: "irq_handler_invocation \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "invoke_irq_handler (ACKIrq irq) = arch_invoke_irq_handler (ACKIrq irq)"
| "invoke_irq_handler (SetIRQHandler irq cap slot) = (do
     irq_slot \<leftarrow> get_irq_slot irq;
     cap_delete_one irq_slot;
     cap_insert cap slot irq_slot
   od)"
| "invoke_irq_handler (ClearIRQHandler irq) = (do
     irq_slot \<leftarrow> get_irq_slot irq;
     cap_delete_one irq_slot
   od)"

text \<open>Handle an interrupt occurence. Timing and scheduling details are not
included in this model, so no scheduling action needs to be taken on timer
ticks. If the IRQ has a valid Notification cap loaded a message is
delivered.\<close>

definition timer_tick :: "(unit, 'z::state_ext) s_monad" where
  "timer_tick \<equiv> do
     cur \<leftarrow> gets cur_thread;
     state \<leftarrow> get_thread_state cur;
     case state of Running \<Rightarrow> do
       ts \<leftarrow> thread_get tcb_time_slice cur;
       let ts' = ts - 1 in
       if (ts' > 0) then thread_set_time_slice cur ts' else do
         thread_set_time_slice cur timeSlice;
         tcb_sched_action tcb_sched_append cur;
         reschedule_required
       od
     od
     | _ \<Rightarrow> return ();
     when (numDomains > 1) (do
       dec_domain_time;
       dom_time \<leftarrow> gets domain_time;
       when (dom_time = 0) reschedule_required
     od)
   od"

definition
  handle_interrupt :: "irq \<Rightarrow> (unit, 'z::state_ext) s_monad" where
 "handle_interrupt irq \<equiv>
   if irq > maxIRQ then do_machine_op $ do
    maskInterrupt True irq;
    ackInterrupt irq
   od
  else do
   st \<leftarrow> get_irq_state irq;
   case st of
     IRQSignal \<Rightarrow> do
       slot \<leftarrow> get_irq_slot irq;
       cap \<leftarrow> get_cap slot;
       when (is_ntfn_cap cap \<and> AllowSend \<in> cap_rights cap)
         $ send_signal (obj_ref_of cap) (cap_ep_badge cap);
       arch_mask_irq_signal irq
     od
   | IRQTimer \<Rightarrow> do
       timer_tick;
       do_machine_op resetTimer
     od
   | IRQInactive \<Rightarrow> fail \<comment> \<open>not meant to be able to get IRQs from inactive lines\<close>
   | IRQReserved \<Rightarrow> handle_reserved_irq irq;
   do_machine_op $ ackInterrupt irq
  od"

end
