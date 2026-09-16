(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchMultikernelDefs_AI
imports MultikernelDefs_AI
begin

context Arch begin arch_global_naming

(* FIXME: model and define kernel_elf_region *)
definition kernel_elf_region :: "'z::state_ext state \<Rightarrow> obj_ref set" where
  "kernel_elf_region s \<equiv> undefined"

(* FIXME: should kernel_device_window be separate and which translation function does it have? *)

(* This is the set of physical addresses that should be distinct between kernels. It includes
   all object and untyped ranges the kernel accesses, all global objects, the kernel stack (in
   ELF region), and the kernel executable (in ELF region) *)
definition kernel_phys_cover :: "'z::state_ext state \<Rightarrow> obj_ref set" where
  "kernel_phys_cover s \<equiv> addrFromPPtr ` kernel_cover s \<union> addrFromKPPtr ` kernel_elf_region s"


(* This is sufficient to prove that the kernel addresses stay separate to an arbitrary set X
   when they were initially separate from X *)

(* prove that kerne elf region is static; trivial in const monad *)
lemma call_kernel_elf_region:
  "call_kernel ev \<lbrace>\<lambda>s. P (kernel_elf_region s)\<rbrace>"
  sorry

lemma inj_inv_subset:
  "\<lbrakk> inj f; f ` A \<subseteq> B \<rbrakk> \<Longrightarrow> A \<subseteq> inv f ` B"
  by (metis image_inv_f_f image_mono)

lemma inj_inv_subset2:
  "\<lbrakk> bij f;  A \<subseteq> inv f ` B \<rbrakk> \<Longrightarrow> f ` A \<subseteq> B"
  by (auto simp: bij_is_surj surj_f_inv_f)

lemma bij_inv_subset_eq:
  "bij f \<Longrightarrow> (f ` A \<subseteq> B) = (A \<subseteq> inv f ` B)"
  by (metis bij_betw_imp_inj_on inj_inv_subset inj_inv_subset2)

lemma bij_addrFromPPtr:
  "bij addrFromPPtr"
  unfolding addrFromPPtr_def
  by (rule bij_diff_right)

lemma call_kernel_addrFromPPtr_cover_bounded:
  "call_kernel ev \<lbrace>\<lambda>s. addrFromPPtr ` kernel_cover s \<subseteq> D\<rbrace>"
  apply (simp add: bij_inv_subset_eq[OF bij_addrFromPPtr])
  apply (rule call_kernel_cover_bounded)
  done

lemma cover_bounded_imp_empty_inter:
  assumes "\<And>C. m \<lbrace>\<lambda>s. A s \<subseteq> C\<rbrace>"
  shows "m \<lbrace>\<lambda>s. A s \<inter> X = {}\<rbrace>"
  unfolding valid_def
  apply clarsimp
  apply (drule use_valid[OF _ assms])
   apply (rule order_refl)
  apply fastforce
  done

lemma call_kernel_phys_inter:
  "call_kernel ev  \<lbrace>\<lambda>s. addrFromPPtr ` kernel_cover s \<inter> X = {}\<rbrace>"
  by (intro cover_bounded_imp_empty_inter call_kernel_addrFromPPtr_cover_bounded)

lemma union_empty_inter_dist:
  "((A \<union> B) \<inter> X = {}) = ((A \<inter> X = {}) \<and> (B \<inter> X = {}))"
  by blast

lemma call_kernel_separation:
  "call_kernel ev \<lbrace>\<lambda>s. kernel_phys_cover s \<inter> X = {}\<rbrace>"
  unfolding kernel_phys_cover_def
  apply (simp add: union_empty_inter_dist)
  apply wp_pre
   apply (wps call_kernel_elf_region)
   apply (wp call_kernel_phys_inter)
  apply simp
  done

end

end
