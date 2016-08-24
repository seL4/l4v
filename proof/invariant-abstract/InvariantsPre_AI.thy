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

context begin interpretation Arch .

requalify_types
  aa_type

requalify_consts
  aa_type

end

(* FIXME: move *)
declare ranI [intro]

section "Locale Setup"

locale pspace_update_eq =
  fixes f :: "'z::state_ext state \<Rightarrow> 'c::state_ext state"
  assumes pspace: "kheap (f s) = kheap s"

locale Arch_pspace_update_eq = pspace_update_eq + Arch

locale arch_update_eq =
  fixes f :: "'z::state_ext state \<Rightarrow> 'c::state_ext state"
  assumes arch: "arch_state (f s) = arch_state s"

locale Arch_arch_update_eq = arch_update_eq + Arch

locale arch_idle_update_eq_more =
  fixes f :: "'z::state_ext state \<Rightarrow> 'c::state_ext state"
  assumes idle: "idle_thread (f s) = idle_thread s"
  assumes irq: "interrupt_irq_node (f s) = interrupt_irq_node s"

locale arch_idle_update_eq = arch_update_eq + arch_idle_update_eq_more
locale Arch_arch_idle_update_eq = Arch_arch_update_eq + arch_idle_update_eq_more

locale p_arch_update_eq = pspace_update_eq + arch_update_eq
locale Arch_p_arch_update_eq = Arch_pspace_update_eq + Arch_arch_update_eq

locale p_arch_idle_update_eq = p_arch_update_eq + arch_idle_update_eq
locale Arch_p_arch_idle_update_eq = Arch_p_arch_update_eq + Arch_arch_idle_update_eq

locale irq_states_update_eq =
  fixes f :: "'z::state_ext state \<Rightarrow> 'c::state_ext state"
  assumes int: "interrupt_states (f s) = interrupt_states s"

locale pspace_int_update_eq = pspace_update_eq + irq_states_update_eq
locale Arch_pspace_int_update_eq = Arch_pspace_update_eq + irq_states_update_eq

locale p_arch_idle_update_int_eq = p_arch_idle_update_eq + pspace_int_update_eq
locale Arch_p_arch_idle_update_int_eq = Arch_p_arch_idle_update_eq + Arch_pspace_int_update_eq


section "Base definitions for Invariants"

definition
  obj_at :: "(kernel_object \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "obj_at P ref s \<equiv> \<exists>ko. kheap s ref = Some ko \<and> P ko"

lemma obj_at_pspaceI:
  "\<lbrakk> obj_at P ref s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> obj_at P ref s'"
  by (simp add: obj_at_def)

abbreviation
  "ko_at k \<equiv> obj_at (op = k)"

lemma obj_atE:
  "\<lbrakk> obj_at P p s; \<And>ko. \<lbrakk> kheap s p = Some ko; P ko \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto simp: obj_at_def)

lemma obj_at_weakenE:
  "\<lbrakk> obj_at P r s; \<And>ko. P ko \<Longrightarrow> P' ko \<rbrakk> \<Longrightarrow> obj_at P' r s"
  by (clarsimp simp: obj_at_def)

lemma ko_at_weakenE:
  "\<lbrakk> ko_at k ptr s; P k \<rbrakk> \<Longrightarrow> obj_at P ptr s"
  by (erule obj_at_weakenE, simp)


text {* An alternative formulation that allows abstraction over type: *}

datatype a_type =
    ATCB
  | AEndpoint
  | ANTFN
  | ACapTable nat
  | AGarbage nat -- "number of bytes of garbage"
  | AArch aa_type

definition
  a_type :: "kernel_object \<Rightarrow> a_type"
where
 "a_type ob \<equiv> case ob of
           CNode sz cspace           \<Rightarrow> if well_formed_cnode_n sz cspace
                                        then ACapTable sz else AGarbage (cte_level_bits + sz)
         | TCB tcb                   \<Rightarrow> ATCB
         | Endpoint endpoint         \<Rightarrow> AEndpoint
         | Notification notification \<Rightarrow> ANTFN
         | ArchObj ao                \<Rightarrow> AArch (aa_type ao)"

lemmas a_type_simps =
  a_type_def[split_simps kernel_object.split]

lemma a_type_aa_type: "(a_type (ArchObj ako) = AArch T) = (aa_type ako = T)"
  by (simp add: a_type_def)

abbreviation
  "typ_at T \<equiv> obj_at (\<lambda>ob. a_type ob = T)"

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
  "arch_cap_fun_lift P F c \<equiv> case c of ArchObjectCap ac \<Rightarrow> P ac | _ \<Rightarrow> F"

lemmas arch_cap_fun_lift_simps[simp] =
  arch_cap_fun_lift_def[split_simps cap.split]

definition
  "arch_obj_fun_lift P F c \<equiv> case c of ArchObj ac \<Rightarrow> P ac | _ \<Rightarrow> F"

lemmas arch_obj_fun_lift_simps[simp] =
  arch_obj_fun_lift_def[split_simps kernel_object.split]
  
lemma
  arch_obj_fun_lift_in_empty[dest!]:
  "x \<in> arch_obj_fun_lift f {} ko
    \<Longrightarrow> \<exists>ako. ko = ArchObj ako \<and> x \<in> f ako"
    by (cases ko; simp add: arch_obj_fun_lift_def)

lemma
  arch_obj_fun_lift_Some[dest!]:
  "arch_obj_fun_lift f None ko = Some x
    \<Longrightarrow> \<exists>ako. ko = ArchObj ako \<and> f ako = Some x"
    by (cases ko; simp add: arch_obj_fun_lift_def)

lemma
  arch_obj_fun_lift_True[dest!]:
  "arch_obj_fun_lift f False ko
    \<Longrightarrow> \<exists>ako. ko = ArchObj ako \<and> f ako"
    by (cases ko; simp add: arch_obj_fun_lift_def)

lemma
  arch_cap_fun_lift_in_empty[dest!]:
  "x \<in> arch_cap_fun_lift f {} cap
    \<Longrightarrow> \<exists>acap. cap = ArchObjectCap acap \<and> x \<in> f acap"
    by (cases cap; simp add: arch_cap_fun_lift_def)

lemma
  arch_cap_fun_lift_Some[dest!]:
  "arch_cap_fun_lift f None cap = Some x
    \<Longrightarrow> \<exists>acap. cap = ArchObjectCap acap \<and> f acap = Some x"
    by (cases cap; simp add: arch_cap_fun_lift_def)

lemma
  arch_cap_fun_lift_True[dest!]:
  "arch_cap_fun_lift f False cap
    \<Longrightarrow> \<exists>acap. cap = ArchObjectCap acap \<and> f acap"
    by (cases cap; simp add: arch_cap_fun_lift_def)

lemma
  arch_obj_fun_lift_non_arch[simp]:
  "\<forall>ako. ko \<noteq> ArchObj ako \<Longrightarrow> arch_obj_fun_lift f F ko = F"
  by (cases ko; fastforce)

lemma
  arch_cap_fun_lift_non_arch[simp]:
  "\<forall>ako. cap \<noteq> ArchObjectCap ako \<Longrightarrow> arch_cap_fun_lift f F cap = F"
  by (cases cap; fastforce)

(* reftype definitions: moved from Invariants_AI so that arch_refs can be defined *)

datatype reftype
  = TCBBlockedSend | TCBBlockedRecv
     | TCBSignal | TCBBound | EPSend | EPRecv | NTFNSignal | NTFNBound
     | TCBHypRef | HypTCBRef

primrec
 symreftype :: "reftype \<Rightarrow> reftype"
where
  "symreftype TCBBlockedSend = EPSend"
| "symreftype TCBBlockedRecv = EPRecv"
| "symreftype TCBSignal       = NTFNSignal"
| "symreftype TCBBound       = NTFNBound"
| "symreftype EPSend         = TCBBlockedSend"
| "symreftype EPRecv         = TCBBlockedRecv"
| "symreftype NTFNSignal       = TCBSignal"
| "symreftype NTFNBound       = TCBBound"
| "symreftype TCBHypRef = HypTCBRef"
| "symreftype HypTCBRef = TCBHypRef"


definition
  sym_refs :: "(obj_ref \<Rightarrow> (obj_ref \<times> reftype) set) \<Rightarrow> bool"
where
 "sym_refs st \<equiv> \<forall>x. \<forall>(y, tp) \<in> st x. (x, symreftype tp) \<in> st y"


lemma symreftype_inverse[simp]:
  "symreftype (symreftype t) = t"
  by (cases t, simp+)

lemma sym_refsD:
  "\<lbrakk> (y, tp) \<in> st x; sym_refs st \<rbrakk> \<Longrightarrow> (x, symreftype tp) \<in> st y"
  apply (simp add: sym_refs_def)
  apply (drule spec, drule(1) bspec)
  apply simp
  done

lemma sym_refsE:
  "\<lbrakk> sym_refs st; (y, symreftype tp) \<in> st x \<rbrakk> \<Longrightarrow> (x, tp) \<in> st y"
  by (drule(1) sym_refsD, simp)

lemma sym_refs_simp:
  "\<lbrakk> sym_refs S \<rbrakk> \<Longrightarrow> ((y, symreftype tp) \<in> S x) = ((x, tp) \<in> S y)"
  apply safe
   apply (erule(1) sym_refsE)
  apply (erule(1) sym_refsD)
  done

lemma delta_sym_refs:
  assumes x: "sym_refs rfs'"
      and y: "\<And>x y tp. \<lbrakk> (y, tp) \<in> rfs x; (y, tp) \<notin> rfs' x \<rbrakk> \<Longrightarrow> (x, symreftype tp) \<in> rfs y"
      and z: "\<And>x y tp. \<lbrakk> (y, tp) \<in> rfs' x; (y, tp) \<notin> rfs x \<rbrakk> \<Longrightarrow> (x, symreftype tp) \<notin> rfs y"
  shows      "sym_refs rfs"
  unfolding sym_refs_def
  apply clarsimp
  apply (case_tac "(a, b) \<in> rfs' x")
   apply (drule sym_refsD [OF _ x])
   apply (rule ccontr)
   apply (frule(1) z)
   apply simp
  apply (erule(1) y)
  done

end