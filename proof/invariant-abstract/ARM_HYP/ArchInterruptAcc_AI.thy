(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 Arch-specific retype invariants
*)

theory ArchInterruptAcc_AI
imports InterruptAcc_AI
begin

context Arch begin arch_global_naming

named_theorems InterruptAcc_AI_assms

lemma dmo_maskInterrupt_invs [InterruptAcc_AI_assms]:
  "\<lbrace>all_invs_but_valid_irq_states_for irq and (\<lambda>s. state = interrupt_states s irq)\<rbrace>
   do_machine_op (maskInterrupt (state = IRQInactive) irq)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
   apply (simp add: do_machine_op_def split_def maskInterrupt_def)
   apply wp
   apply (clarsimp simp: in_monad invs_def valid_state_def all_invs_but_valid_irq_states_for_def valid_irq_states_but_def valid_irq_masks_but_def valid_machine_state_def cur_tcb_def valid_irq_states_def valid_irq_masks_def)
  done

lemma handle_spurious_irq_invs:
  "handle_spurious_irq \<lbrace>invs\<rbrace>"
  unfolding handle_spurious_irq_def
  apply (wpsimp wp: dmo_invs machine_op_lift_device_state simp: handleSpuriousIRQ_mop_def)
  apply (clarsimp simp add: machine_op_lift_def machine_rest_lift_def in_monad select_f_def)
  done

end

global_interpretation InterruptAcc_AI?: InterruptAcc_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; fact InterruptAcc_AI_assms)
  qed

end
