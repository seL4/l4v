(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory InvariantsPre_AI
imports LevityCatch_AI
begin

context Arch begin

unqualify_types
  aa_type

unqualify_consts
  aa_type :: "arch_kernel_obj \<Rightarrow> aa_type"

end

section "Locale Setup"

locale pspace_update_eq' =
  fixes f :: "'z::state_ext state \<Rightarrow> 'c::state_ext state"
  assumes pspace: "kheap (f s) = kheap s"

locale Arch_pspace_update_eq = pspace_update_eq'
sublocale Arch_pspace_update_eq \<subseteq> Arch .

locale pspace_update_eq = pspace_update_eq'


locale arch_update_eq' =
  fixes f :: "'z::state_ext state \<Rightarrow> 'c::state_ext state"
  assumes arch: "arch_state (f s) = arch_state s"

locale Arch_arch_update_eq = arch_update_eq'
sublocale Arch_arch_update_eq \<subseteq> Arch .

locale arch_update_eq = arch_update_eq'

locale arch_idle_update_eq_more =
  fixes f :: "'z::state_ext state \<Rightarrow> 'c::state_ext state"
  assumes idle: "idle_thread (f s) = idle_thread s"
  assumes irq: "interrupt_irq_node (f s) = interrupt_irq_node s"

locale Arch_arch_idle_update_eq = Arch_arch_update_eq + arch_idle_update_eq_more
sublocale Arch_arch_idle_update_eq \<subseteq> Arch .

locale arch_idle_update_eq = arch_update_eq + arch_idle_update_eq_more


locale Arch_p_arch_update_eq = Arch_pspace_update_eq + Arch_arch_update_eq
sublocale Arch_p_arch_update_eq \<subseteq> Arch .

locale p_arch_update_eq = pspace_update_eq + arch_update_eq

locale Arch_p_arch_idle_update_eq = Arch_p_arch_update_eq + Arch_arch_idle_update_eq
locale p_arch_idle_update_eq = p_arch_update_eq + arch_idle_update_eq

locale Arch_p_arch_idle_update_int_eq = Arch_p_arch_idle_update_eq + Arch_pspace_update_eq

section "Base definitions for Invariants"

definition
  obj_at :: "(Structures_A.kernel_object \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "obj_at P ref s \<equiv> \<exists>ko. kheap s ref = Some ko \<and> P ko"

abbreviation
  "ko_at k \<equiv> obj_at (op = k)"

definition
  aobj_at :: "(arch_kernel_obj \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "aobj_at P ref s \<equiv> \<exists>ako. kheap s ref = Some (ArchObj ako) \<and> P ako"

lemma aobj_at_def2:
  "aobj_at P ref = obj_at (\<lambda>ob. case ob of ArchObj aob \<Rightarrow> P aob | _ \<Rightarrow> False) ref"
  apply (rule ext)
  apply (clarsimp simp add: obj_at_def aobj_at_def)
  apply (rule iffI)
   apply (clarsimp)+
  apply (case_tac ko; clarsimp)
  done

abbreviation
  "ako_at k \<equiv> aobj_at (op = k)"

abbreviation
  "atyp_at T \<equiv> aobj_at (\<lambda>ob. aa_type ob = T)"

lemma obj_atE:
  "\<lbrakk> obj_at P p s; \<And>ko. \<lbrakk> kheap s p = Some ko; P ko \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto simp: obj_at_def)

lemma obj_at_weakenE:
  "\<lbrakk> obj_at P r s; \<And>ko. P ko \<Longrightarrow> P' ko \<rbrakk> \<Longrightarrow> obj_at P' r s"
  by (clarsimp simp: obj_at_def)

lemma ko_at_weakenE:
  "\<lbrakk> ko_at k ptr s; P k \<rbrakk> \<Longrightarrow> obj_at P ptr s"
  by (erule obj_at_weakenE, simp)

lemma aobj_atE:
  "\<lbrakk> aobj_at P p s; \<And>ko. \<lbrakk> kheap s p = Some (ArchObj ko); P ko \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto simp: aobj_at_def)

lemma aobj_at_weakenE:
  "\<lbrakk> aobj_at P r s; \<And>ko. P ko \<Longrightarrow> P' ko \<rbrakk> \<Longrightarrow> aobj_at P' r s"
  by (clarsimp simp: aobj_at_def)

lemma ako_at_weakenE:
  "\<lbrakk> ako_at k ptr s; P k \<rbrakk> \<Longrightarrow> aobj_at P ptr s"
  by (erule aobj_at_weakenE, simp)

definition
  pspace_aligned :: "'z::state_ext state \<Rightarrow> bool"
where
  "pspace_aligned s \<equiv>
     \<forall>x \<in> dom (kheap s). is_aligned x (obj_bits (the (kheap s x)))"

lemma pspace_alignedD [intro?]:
  "\<lbrakk> kheap s p = Some ko; pspace_aligned s \<rbrakk> \<Longrightarrow> is_aligned p (obj_bits ko)"
  unfolding pspace_aligned_def by (drule bspec, blast, simp)

text "objects don't overlap"
definition
  pspace_distinct :: "'z::state_ext state \<Rightarrow> bool"
where
  "pspace_distinct \<equiv>
   \<lambda>s. \<forall>x y ko ko'. kheap s x = Some ko \<and> kheap s y = Some ko' \<and> x \<noteq> y \<longrightarrow>
         {x .. x + (2 ^ obj_bits ko - 1)} \<inter>
         {y .. y + (2 ^ obj_bits ko' - 1)} = {}"


definition
  caps_of_state :: "'z::state_ext state \<Rightarrow> cslot_ptr \<Rightarrow> cap option"
where
 "caps_of_state s \<equiv> (\<lambda>p. if (\<exists>cap. fst (get_cap p s) = {(cap, s)})
                         then Some (THE cap. fst (get_cap p s) = {(cap, s)})
                         else None)"

definition
  arch_caps_of :: "(cslot_ptr \<Rightarrow> cap option) \<Rightarrow> (cslot_ptr \<Rightarrow> arch_cap option)" where
  "arch_caps_of cs \<equiv> (\<lambda>p. case cs p of Some (ArchObjectCap ac) \<Rightarrow> Some ac | _ \<Rightarrow> None)"

lemma
  arch_caps_of_simp[simp]:
  "(arch_caps_of cs p = Some ac) = (cs p = Some (ArchObjectCap ac))"
  by (auto simp: arch_caps_of_def split: option.splits cap.splits)
  


end