(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchBCorres_AI
imports
  BCorres_AI
  ArchBitSetup_AI
begin

context Arch begin arch_global_naming

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
  by (induct l arbitrary: r b c rule: vm_level.minus_induct; wpsimp simp: pt_lookup_from_level_simps)

crunch arch_finalise_cap
  for (bcorres) bcorres[wp]: truncate_state
crunch prepare_thread_delete
  for (bcorres) bcorres[wp]: truncate_state

end

end
