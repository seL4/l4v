(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchBits_AI
imports Invariants_AI
begin

context Arch begin arch_global_naming

lemma invs_unique_table_caps[elim!]:
  "invs s \<Longrightarrow> unique_table_caps s"
  by (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)

lemma invs_unique_refs[elim!]:
  "invs s \<Longrightarrow> unique_table_refs s"
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

lemmas valid_cap_def = valid_cap_def[simplified valid_arch_cap_def]

lemmas valid_cap_simps =
  valid_cap_def[split_simps cap.split arch_cap.split, simplified wellformed_mapdata_def]

definition is_ap_cap :: "cap \<Rightarrow> bool" where
  "is_ap_cap cap \<equiv> arch_cap_fun_lift is_ASIDPoolCap False cap"

lemmas is_ap_cap_simps[simp] =
  is_ap_cap_def[unfolded arch_cap_fun_lift_def, split_simps cap.split arch_cap.split]

lemma is_ap_cap_eq:
  "is_ap_cap cap = (\<exists>p m. cap = ArchObjectCap (ASIDPoolCap p m))"
  by (auto simp: is_ap_cap_def is_ASIDPoolCap_def)

definition is_frame_cap :: "cap \<Rightarrow> bool" where
  "is_frame_cap cap \<equiv> arch_cap_fun_lift is_FrameCap False cap"

lemmas is_frame_cap_simps[simp] =
  is_frame_cap_def[unfolded arch_cap_fun_lift_def, split_simps cap.split arch_cap.split]

lemma is_frame_cap_eq:
  "is_frame_cap cap = (\<exists>p R sz dev m. cap = ArchObjectCap (FrameCap p R sz dev m))"
  by (auto simp: is_frame_cap_def is_FrameCap_def)

lemmas is_arch_cap_simps = is_pt_cap_eq is_ap_cap_eq is_frame_cap_eq

lemmas is_cap_simps = is_cap_simps is_arch_cap_simps

end

end
