(*
 * Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInvariantUpdates_H
imports InvariantUpdates_H
begin

context Arch begin arch_global_naming

named_theorems InvariantUpdates_H_assms

lemma valid_arch_state'_interrupt[simp, InvariantUpdates_H_assms]:
  "valid_arch_state' (ksInterruptState_update f s) = valid_arch_state' s"
  by (simp add: valid_arch_state'_def cong: option.case_cong)

end

global_interpretation InvariantUpdates_H?: InvariantUpdates_H
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact InvariantUpdates_H_assms)?)
qed

end
