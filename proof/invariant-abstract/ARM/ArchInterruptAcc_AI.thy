(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 Arch-specific retype invariants
*)

theory ArchInterruptAcc_AI
imports "../InterruptAcc_AI"
begin

context Arch begin global_naming ARM

named_theorems InterruptAcc_AI_assms

lemma dmo_maskInterrupt_invs [InterruptAcc_AI_assms]:
  "\<lbrace>all_invs_but_valid_irq_states_for irq and (\<lambda>s. state = interrupt_states s irq)\<rbrace>
   do_machine_op (maskInterrupt (state = IRQInactive) irq)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: do_machine_op_def maskInterrupt_def in_monad invs_def valid_state_def
                   all_invs_but_valid_irq_states_for_def valid_irq_states_but_def
                   valid_irq_masks_but_def valid_machine_state_def cur_tcb_def cur_sc_tcb_def
                   valid_irq_states_def valid_irq_masks_def)

end

global_interpretation InterruptAcc_AI?: InterruptAcc_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; fact InterruptAcc_AI_assms)
  qed

end
