(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchBits_AI
imports Invariants_AI
begin

context Arch begin arch_global_naming

(* arch-specific interpretations of update locales: *)

sublocale p_asid_table_kernel_vspace_update:
  Arch_p_asid_table_update_eq "\<lambda>s. s\<lparr>arch_state := arm_kernel_vspace_update f (arch_state s)\<rparr>"
  by (unfold_locales) auto

sublocale p_asid_table_vmid_table_update:
  Arch_p_asid_table_update_eq "\<lambda>s. s\<lparr>arch_state := arm_vmid_table_update f (arch_state s)\<rparr>"
  by (unfold_locales) auto

sublocale p_asid_table_asid_map_update:
  Arch_p_asid_table_update_eq "\<lambda>s. s\<lparr>arch_state := arm_asid_map_update f (arch_state s)\<rparr>"
  by (unfold_locales) auto

sublocale p_asid_table_next_vmid_update:
  Arch_p_asid_table_update_eq "\<lambda>s. s\<lparr>arch_state := arm_next_vmid_update f (arch_state s)\<rparr>"
  by (unfold_locales) auto

sublocale p_asid_table_us_global_vspace_update:
  Arch_p_asid_table_update_eq "\<lambda>s. s\<lparr>arch_state := arm_us_global_vspace_update f (arch_state s)\<rparr>"
  by (unfold_locales) auto

sublocale p_asid_table_current_vcpu_update:
  Arch_p_asid_table_update_eq "\<lambda>s. s\<lparr>arch_state := arm_current_vcpu_update f (arch_state s)\<rparr>"
  by (unfold_locales) auto

sublocale p_asid_table_current_fpu_update:
  Arch_p_asid_table_update_eq "\<lambda>s. s\<lparr>arch_state := arm_current_fpu_owner_update f (arch_state s)\<rparr>"
  by (unfold_locales) auto


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

lemma invs_vmid_inv[elim!]:
  "invs s \<Longrightarrow> vmid_inv s"
  by (auto simp: invs_def valid_state_def valid_arch_state_def)

lemma invs_valid_vmid_table[elim!]:
  "invs s \<Longrightarrow> valid_vmid_table s"
  by (auto simp: invs_def valid_state_def valid_arch_state_def)

lemma invs_valid_global_arch_objs[elim!]:
  "invs s \<Longrightarrow> valid_global_arch_objs s"
  by (clarsimp simp: invs_def valid_state_def valid_arch_state_def)

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

lemmas is_arch_cap_simps = is_pt_cap_eq is_ap_cap_eq is_frame_cap_eq is_SGISignalCap_def

lemmas is_cap_simps = is_cap_simps is_ArchObjectCap_def is_arch_cap_simps

end

end
