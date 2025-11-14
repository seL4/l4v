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

lemma valid_arch_state'_vmid_next_update[simp]:
  "valid_arch_state' (s\<lparr>ksArchState := armKSNextVMID_update f (ksArchState s)\<rparr>) =
   valid_arch_state' s"
  by (auto simp: valid_arch_state'_def split: option.split)

lemma invs'_armKSNextVMID_update[simp]:
  "invs' (s\<lparr>ksArchState := armKSNextVMID_update f s'\<rparr>) = invs' (s\<lparr>ksArchState := s'\<rparr>)"
  by (simp add: invs'_def valid_state'_def valid_global_refs'_def global_refs'_def table_refs'_def
                valid_machine_state'_def valid_arch_state'_def cong: option.case_cong)

lemma invs_no_cicd'_armKSNextVMID_update[simp]:
  "invs_no_cicd' (s\<lparr>ksArchState := armKSNextVMID_update f s'\<rparr>) = invs_no_cicd' (s\<lparr>ksArchState := s'\<rparr>)"
  by (simp add: invs_no_cicd'_def valid_state'_def valid_global_refs'_def global_refs'_def table_refs'_def
                valid_machine_state'_def valid_arch_state'_def cong: option.case_cong)

lemma invs'_gsTypes_update:
  "ksA' = ksArchState s \<Longrightarrow> invs' (s \<lparr>ksArchState := gsPTTypes_update f ksA'\<rparr>) = invs' s"
  by (simp add: invs'_def valid_state'_def valid_global_refs'_def global_refs'_def
                valid_machine_state'_def valid_arch_state'_def
           cong: option.case_cong)

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
