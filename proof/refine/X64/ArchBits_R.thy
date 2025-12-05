(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchBits_R
imports Bits_R
begin

context Arch begin arch_global_naming

named_theorems Bits_R_assms

lemma atcbContext_get_eq[Bits_R_assms, simp]:
  "atcbContextGet (atcbContextSet x atcb) = x"
  by (simp add: atcbContextGet_def atcbContextSet_def)

lemma atcbContext_set_eq[Bits_R_assms, simp]:
  "atcbContextSet (atcbContextGet t) t = t"
  by (cases t, simp add: atcbContextGet_def atcbContextSet_def)

lemma atcbContext_set_set[Bits_R_assms, simp]:
  "atcbContextSet x (atcbContextSet y atcb) = atcbContextSet x atcb"
  by (cases atcb, simp add: atcbContextSet_def)

lemma objBitsKO_less_word_bits[Bits_R_assms]:
  "objBitsKO ko < word_bits"
  unfolding objBits_def
  by (case_tac ko;
      simp add: pageBits_def objBits_simps' word_bits_def
         split: arch_kernel_object.split)

lemma objBitsKO_neq_0[Bits_R_assms]:
  "objBitsKO ko \<noteq> 0"
  unfolding objBits_def
  by (case_tac ko;
      simp add: pageBits_def objBits_simps' word_bits_def
         split: arch_kernel_object.split)

lemma arch_isCap_simps:
  "isPageCap w = (\<exists>d v0 v1 v2 v3 v4. w = PageCap v0 v1 v2 v3 d v4)"
  "isPageTableCap w = (\<exists>v0 v1. w = PageTableCap v0 v1)"
  "isPageDirectoryCap w = (\<exists>v0 v1. w = PageDirectoryCap v0 v1)"
  "isPDPointerTableCap w = (\<exists>v0 v1. w = PDPointerTableCap v0 v1)"
  "isPML4Cap w = (\<exists>v0 v1. w = PML4Cap v0 v1)"
  "isIOPortCap w = (\<exists>v0 v1. w = IOPortCap v0 v1)"
  "isASIDControlCap w = (w = ASIDControlCap)"
  "isASIDPoolCap w = (\<exists>v0 v1. w = ASIDPoolCap v0 v1)"
  "isArchPageCap cap = (\<exists>d ref rghts sz data typ. cap = ArchObjectCap (PageCap ref rghts typ sz d data))"
  "isArchIOPortCap cap = (\<exists>f l. cap = ArchObjectCap (IOPortCap f l))"
  "isIOPortControlCap w = (w = IOPortControlCap)"
  "isIOPortControlCap' cap = (cap = ArchObjectCap IOPortControlCap)"
  by (auto simp: isCap_defs split: capability.splits arch_capability.splits)

lemmas isCap_simps = gen_isCap_simps arch_isCap_simps

lemma pageBits_le_maxUntypedSizeBits[Bits_R_assms, simp]:
  "pageBits \<le> maxUntypedSizeBits"
  by (simp add: pageBits_def maxUntypedSizeBits_def)

text \<open>Miscellaneous facts about low level constructs\<close>

lemma projectKO_ASID:
  "(projectKO_opt ko = Some t) = (ko = KOArch (KOASIDPool t))"
  by (cases ko)
     (auto simp: projectKO_opts_defs split: arch_kernel_object.splits)

lemma projectKO_PTE:
  "(projectKO_opt ko = Some t) = (ko = KOArch (KOPTE t))"
  by (cases ko)
     (auto simp: projectKO_opts_defs split: arch_kernel_object.splits)

lemma projectKO_PDE:
  "(projectKO_opt ko = Some t) = (ko = KOArch (KOPDE t))"
  by (cases ko)
     (auto simp: projectKO_opts_defs split: arch_kernel_object.splits)

lemma projectKO_PDPTE:
  "(projectKO_opt ko = Some t) = (ko = KOArch (KOPDPTE t))"
  by (cases ko)
     (auto simp: projectKO_opts_defs split: arch_kernel_object.splits)

lemma projectKO_PML4E:
  "(projectKO_opt ko = Some t) = (ko = KOArch (KOPML4E t))"
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
  projectKO_ASID projectKO_PTE projectKO_PDE projectKO_PDPTE projectKO_PML4E
  projectKO_user_data projectKO_user_data_device

end

(* for projectKO_opt, we want to export the arch-specific instantiation lemmas *)
arch_requalify_facts arch_projectKOs

declare arch_projectKOs[simp]

(* provide combined alias when needed for [simp del] *)
lemmas projectKOs = gen_projectKOs arch_projectKOs

interpretation Bits_R?: Bits_R
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Bits_R_assms)?)
qed

end
