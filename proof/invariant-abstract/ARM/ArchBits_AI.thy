(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchBits_AI
imports Invariants_AI
begin

context Arch begin arch_global_naming

lemma invs_unique_table_caps[elim!]:
  "invs s \<Longrightarrow> unique_table_caps (caps_of_state s)"
  by (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)

lemma invs_unique_refs[elim!]:
  "invs s \<Longrightarrow> unique_table_refs (caps_of_state s)"
  by (simp add: invs_def valid_state_def valid_arch_caps_def)


lemma invs_pd_caps:
  "invs s \<Longrightarrow> valid_table_caps s"
  by (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)

lemma invs_valid_vs_lookup[elim!]:
  "invs s \<Longrightarrow> valid_vs_lookup s "
  by (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)

lemma pbfs_atleast_pageBits:
  "pageBits \<le> pageBitsForSize sz"
  by (cases sz) (auto simp: pageBits_def)

lemmas is_cap_simps = is_cap_simps is_ArchObjectCap_def is_arch_cap_simps
lemmas valid_cap_def = valid_cap_def[simplified valid_arch_cap_def]

lemmas valid_cap_simps =
  valid_cap_def[split_simps cap.split arch_cap.split]

lemmas invs_valid_asid_table [elim!] = invs_arch_state[THEN vas_valid_asid_table]
lemmas invs_ran_asid_table = invs_valid_asid_table[THEN valid_asid_table_ran]

end

end
