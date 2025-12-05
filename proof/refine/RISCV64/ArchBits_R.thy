(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchBits_R
imports Bits_R
begin

context Arch begin arch_global_naming

crunch_ignore (add: lookupPTSlotFromLevel lookupPTFromLevel)

lemma arch_isCap_simps:
  "isFrameCap w = (\<exists>v0 v1 v2 v3 v4. w = FrameCap v0 v1 v2 v3 v4)"
  "isArchFrameCap v = (\<exists>v0 v1 v2 v3 v4. v = ArchObjectCap (FrameCap v0 v1 v2 v3 v4))"
  "isPageTableCap w = (\<exists>v0 v1. w = PageTableCap v0 v1)"
  "isASIDControlCap w = (w = ASIDControlCap)"
  "isASIDPoolCap w = (\<exists>v0 v1. w = ASIDPoolCap v0 v1)"
  by (auto simp: isCap_defs split: capability.splits arch_capability.splits)

lemmas isCap_simps = gen_isCap_simps arch_isCap_simps

lemmas pte_ko_at_valid_objs_valid_pte' =
  ko_at_valid_objs'_pre[where 'a=pte, simplified injectKO_pte valid_obj'_def]

text \<open>Miscellaneous facts about low level constructs\<close>

lemma projectKO_ASID:
  "(projectKO_opt ko = Some t) = (ko = KOArch (KOASIDPool t))"
  by (cases ko)
     (auto simp: projectKO_opts_defs split: arch_kernel_object.splits)

lemma projectKO_PTE:
  "(projectKO_opt ko = Some t) = (ko = KOArch (KOPTE t))"
  by (cases ko)
     (auto simp: projectKO_opts_defs split: arch_kernel_object.splits)

lemma projectKO_user_data:
  "(projectKO_opt ko = Some (t :: user_data)) = (ko = KOUserData)"
  by (cases ko)
     (auto simp: projectKO_opts_defs split: arch_kernel_object.splits)

lemma projectKO_user_data_device:
  "(projectKO_opt ko = Some (t :: user_data_device)) = (ko = KOUserDataDevice)"
  by (cases ko)
     (auto simp: projectKO_opts_defs split: arch_kernel_object.splits)

lemmas arch_projectKOs =
  projectKO_ASID projectKO_PTE projectKO_user_data projectKO_user_data_device

end

(* for projectKO_opt, we want to export the arch-specific instantiation lemmas *)
arch_requalify_facts arch_projectKOs

declare arch_projectKOs[simp]

(* provide combined alias when needed for [simp del] *)
lemmas projectKOs = gen_projectKOs arch_projectKOs

end
