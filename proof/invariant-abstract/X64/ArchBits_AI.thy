(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchBits_AI
imports Invariants_AI
begin

context Arch begin arch_global_naming

(* arch-specific interpretations of update locales: *)

(* FIXME: do this for other x64 arch_state fields *)
sublocale p_asid_table_current_fpu_update:
  Arch_p_asid_table_update_eq "\<lambda>s. s\<lparr>arch_state := x64_current_fpu_owner_update f (arch_state s)\<rparr>"
  by (unfold_locales) (auto simp: second_level_tables_def)


lemma invs_valid_ioports[elim!]:
  "invs s \<Longrightarrow> valid_ioports s"
  by (simp add: invs_def valid_state_def valid_arch_state_def)

lemma invs_unique_table_caps[elim!]:
  "invs s \<Longrightarrow> unique_table_caps (caps_of_state s)"
  by (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)

lemma invs_unique_refs[elim!]:
  "invs s \<Longrightarrow> unique_table_refs (caps_of_state s)"
  by (simp add: invs_def valid_state_def valid_arch_caps_def)


lemma invs_valid_table_caps[elim!]:
  "invs s \<Longrightarrow> valid_table_caps s"
  by (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)

lemma invs_valid_vs_lookup[elim!]:
  "invs s \<Longrightarrow> valid_vs_lookup s "
  by (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)

lemma pbfs_atleast_pageBits:
  "pageBits \<le> pageBitsForSize sz"
  by (cases sz) (auto simp: pageBits_def)

lemmas is_cap_simps = is_cap_simps is_arch_cap_simps
lemmas valid_cap_def = valid_cap_def[simplified valid_arch_cap_def]

lemmas valid_cap_simps =
  valid_cap_def[split_simps cap.split arch_cap.split, simplified wellformed_mapdata_def]

end

end
