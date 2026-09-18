(*
 * Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInvariantUpdates_H
imports InvariantUpdates_H
begin

context Arch begin arch_global_naming

clear_named_theorems Arch_assms (* accumulate assumptions for InvariantUpdates_H locale *)

lemma valid_arch_state'_interrupt[simp, Arch_assms]:
  "valid_arch_state' (ksInterruptState_update f s) = valid_arch_state' s"
  by (simp add: valid_arch_state'_def cong: option.case_cong)

(* not generally true for ksInterruptState update *)
lemma global_refs'_intStateIRQTable_update[simp, Arch_assms]:
  "global_refs' (s\<lparr>ksInterruptState := intStateIRQTable_update f (ksInterruptState s)\<rparr>)
   = global_refs' s"
  by (simp add: global_refs'_def)

lemmas InvariantUpdates_H_assms = Arch_assms (* extract accumulated assumptions *)

end (* Arch *)

global_interpretation InvariantUpdates_H?: InvariantUpdates_H
proof goal_cases
  case 1 show ?case by (intro_locales; (unfold_locales; fact ARM_HYP.InvariantUpdates_H_assms)?)
qed

end
