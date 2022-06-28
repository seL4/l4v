(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchBCorres_AI
imports
  BCorres_AI
begin

context Arch begin global_naming AARCH64

(* FIXME AARCH64: move/generalise; port back to RISC-V before we seed AInvs from there.
   Ideally we want to pick bit0/bit1 automatically based on the value of asid_pool_level. *)
lemmas vm_level_minus_induct = bit1.minus_induct
lemmas vm_level_of_nat_cases = bit1.of_nat_cases
lemmas vm_level_not_less_zero_bit0 = bit1.not_less_zero_bit0
lemmas vm_level_leq_minus1_less = bit1.leq_minus1_less
lemmas vm_level_no_overflow_eq_max_bound = bit1.no_overflow_eq_max_bound
lemmas vm_level_size_inj = bit1.size_inj
lemmas vm_level_plus_one_leq = bit1.plus_one_leq
lemmas vm_level_pred = bit1.pred
lemmas vm_level_zero_least = bit1.zero_least
lemmas vm_level_minus1_leq = bit1.minus1_leq
lemmas vm_level_size_plus = bit1.size_plus
lemmas vm_level_size_less = bit1.size_less
lemmas vm_level_from_top_induct = bit1.from_top_induct
lemmas vm_level_size_less_eq = bit1.size_less_eq


lemma entry_for_asid_truncate[simp]:
  "entry_for_asid asid (truncate_state s) = entry_for_asid asid s"
  by (simp add: entry_for_asid_def pool_for_asid_def obind_def
         split: option.splits)

lemma vspace_for_asid_truncate[simp]:
  "vspace_for_asid asid (truncate_state s) = vspace_for_asid asid s"
  by (simp add: vspace_for_asid_def obind_def oreturn_def)

lemma pool_for_asid_truncate[simp]:
  "pool_for_asid asid (truncate_state s) = pool_for_asid asid s"
  by (simp add: pool_for_asid_def)

lemma vs_lookup_table_truncate[simp]:
  "vs_lookup_table l asid vptr (truncate_state s) = vs_lookup_table l asid vptr s"
  by (simp add: vs_lookup_table_def obind_def oreturn_def split: option.splits)

lemma vs_lookup_slot_truncate[simp]:
  "vs_lookup_slot l asid vptr (truncate_state s) = vs_lookup_slot l asid vptr s"
  by (simp add: vs_lookup_slot_def obind_def oreturn_def split: option.splits)

lemma pt_lookup_from_level_bcorres[wp]:
  "bcorres (pt_lookup_from_level l r b c) (pt_lookup_from_level l r b c)"
  by (induct l arbitrary: r b c rule: vm_level_minus_induct; wpsimp simp: pt_lookup_from_level_simps)

crunch (bcorres) bcorres[wp]: arch_finalise_cap truncate_state
crunch (bcorres) bcorres[wp]: prepare_thread_delete truncate_state

end

requalify_facts AARCH64.arch_finalise_cap_bcorres AARCH64.prepare_thread_delete_bcorres

declare arch_finalise_cap_bcorres[wp] prepare_thread_delete_bcorres[wp]

end
