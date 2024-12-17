(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Preliminary definitions required to define arch-specific invariants and properties.
   These are primarily related to obj_at' and storability.
*)

theory InvariantsPre_H
imports
  LevityCatch
  "AInvs.ArchDetSchedSchedule_AI"
  "Lib.Heap_List"
  Move_R
begin

section \<open>Locale Setup for kernel_state Field Update Identities\<close>

text \<open>
  These locales identify which updates are the identity function on specific field access
  predicates. For instance, when a function doesn't change the @{term ksPSpace} component of the
  state, that function is the identity on all predicates that only depend on @{term ksPSpace}.\<close>

text \<open>
  Since locales can dynamically gain conclusions, we want to avoid situations where someone adds
  a conclusion somewhere in the locale graph and is surprised that it does not appear for
  extensions of that locale. For arch-split there is an extra complication, where the conclusions
  might use arch-specific facts, thus needing to be in Arch.

  This means that for every one of the update locales, we have to add an additional Arch locale.
  In order to not leave gaps in the locale graph, when we combine update locales, the Arch locale
  for their combination must also see the conclusions of \emph{their} Arch locales, leading to a
  pattern of @{text "C = A + B"} followed by @{text "ArchC = C + ArchA + ArchB"}.\<close>

locale pspace_update_eq' =
  fixes f :: "kernel_state \<Rightarrow> kernel_state"
  assumes pspace: "ksPSpace (f s) = ksPSpace s"

locale Arch_pspace_update_eq' = pspace_update_eq' + Arch

locale arch_idle_update_eq' =
  fixes f :: "kernel_state \<Rightarrow> kernel_state"
  assumes arch: "ksArchState (f s) = ksArchState s"
  assumes idle: "ksIdleThread (f s) = ksIdleThread s"
  assumes int_nd:  "intStateIRQNode (ksInterruptState (f s))
                    = intStateIRQNode (ksInterruptState s)"
  assumes maxObj: "gsMaxObjectSize (f s) = gsMaxObjectSize s"

locale Arch_arch_idle_update_eq' = arch_idle_update_eq' + Arch

locale p_arch_idle_update_eq' = pspace_update_eq' + arch_idle_update_eq'
locale Arch_p_arch_idle_update_eq' =
         Arch_pspace_update_eq' + Arch_arch_idle_update_eq' + p_arch_idle_update_eq'

locale int_update_eq' =
  fixes f :: "kernel_state \<Rightarrow> kernel_state"
  assumes int:  "ksInterruptState (f s) = ksInterruptState s"

(* FIXME arch-split: unused, can replace by int_update_eq' to optimise *)
locale Arch_int_update_eq' = int_update_eq' + Arch

locale p_cur_update_eq' = pspace_update_eq' +
  assumes curt: "ksCurThread (f s) = ksCurThread s"
  assumes curd: "ksCurDomain (f s) = ksCurDomain s"

(* FIXME arch-split: unused, can replace by p_cur_update_eq' to optimise *)
locale Arch_p_cur_update_eq' = p_cur_update_eq' + Arch

locale p_int_update_eq' = pspace_update_eq' + int_update_eq'
locale Arch_p_int_update_eq' = Arch_pspace_update_eq' + Arch_int_update_eq' + p_int_update_eq'

locale p_int_cur_update_eq' = p_int_update_eq' + p_cur_update_eq'
locale Arch_p_int_cur_update_eq' = Arch_p_int_update_eq' + Arch_p_cur_update_eq' + p_int_cur_update_eq'

locale p_arch_idle_int_update_eq' = p_arch_idle_update_eq' + p_int_update_eq'
locale Arch_p_arch_idle_int_update_eq' =
         Arch_p_arch_idle_update_eq' + Arch_p_int_update_eq' + p_arch_idle_int_update_eq'

locale p_arch_idle_int_cur_update_eq' = p_arch_idle_int_update_eq' + p_cur_update_eq'
locale Arch_p_arch_idle_int_cur_update_eq' =
         p_arch_idle_int_cur_update_eq' + Arch_p_arch_idle_int_update_eq' + Arch_p_cur_update_eq'


section \<open>Kernel Objects in Memory\<close>

text \<open>
  We do not make use of the VPtr/Ptr/Register abstraction in proofs, only for type safety in Haskell\<close>
(* FIXME arch-split: add to simpset? *)
arch_requalify_facts (H)
  PPtr_def
  fromPPtr_def
  VPtr_def
  fromVPtr_def
  fromVPtr_update_def
  Register_def

definition ps_clear :: "obj_ref \<Rightarrow> nat \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ps_clear p n s \<equiv> (mask_range p n - {p}) \<inter> dom (ksPSpace s) = {}"

definition pspace_no_overlap' :: "obj_ref \<Rightarrow> nat \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "pspace_no_overlap' ptr bits \<equiv>
     \<lambda>s. \<forall>x ko. ksPSpace s x = Some ko \<longrightarrow>
                (mask_range x (objBitsKO ko)) \<inter> {ptr .. (ptr && ~~ mask bits) + mask bits} = {}"

definition ko_wp_at' :: "(kernel_object \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ko_wp_at' P p s \<equiv> \<exists>ko. ksPSpace s p = Some ko \<and> is_aligned p (objBitsKO ko) \<and> P ko \<and>
                          ps_clear p (objBitsKO ko) s"

definition obj_at' :: "('a::pspace_storable \<Rightarrow> bool) \<Rightarrow> machine_word \<Rightarrow> kernel_state \<Rightarrow> bool" where
  obj_at'_real_def:
  "obj_at' P p s \<equiv> ko_wp_at' (\<lambda>ko. \<exists>obj. projectKO_opt ko = Some obj \<and> P obj) p s"

definition typ_at' :: "kernel_object_type \<Rightarrow> machine_word \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "typ_at' T \<equiv> ko_wp_at' (\<lambda>ko. koTypeOf ko = T)"

abbreviation ko_at' :: "'a::pspace_storable \<Rightarrow> obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ko_at' v \<equiv> obj_at' (\<lambda>k. k = v)"

abbreviation irq_node' :: "kernel_state \<Rightarrow> obj_ref" where
  "irq_node' s \<equiv> intStateIRQNode (ksInterruptState s)"

(* FIXME arch-split: consider adding to simpset early in Refine, then changing over definitions *)
(* proof is identical on all arches *)
lemma (in Arch) cteSizeBits_cte_level_bits:
  "cteSizeBits = cte_level_bits"
  unfolding cteSizeBits_def cte_level_bits_def
  by (simp add: wordSizeCase_def wordBits_def word_size)

requalify_facts
  Arch.cteSizeBits_cte_level_bits

end
