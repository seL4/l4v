(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 Arch-specific interrupt invariants
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
  by (wpsimp simp: do_machine_op_def maskInterrupt_def in_monad invs_def valid_state_def
                   all_invs_but_valid_irq_states_for_def valid_irq_states_but_def
                   valid_irq_masks_but_def valid_machine_state_def cur_tcb_def cur_sc_tcb_def
                   valid_irq_states_def valid_irq_masks_def)

lemma getCurrentTime_invs[wp]:
  "do_machine_op getCurrentTime \<lbrace>invs\<rbrace>"
  apply (simp add: getCurrentTime_def modify_def)
  apply (wpsimp wp: dmo_invs simp: modify_def)
  by (simp add: do_machine_op_def modify_def in_get bind_assoc get_def put_def gets_def in_bind
                   split_def select_f_returns in_return)

end

global_interpretation InterruptAcc_AI?: InterruptAcc_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; fact InterruptAcc_AI_assms)
  qed

end
