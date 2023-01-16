(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
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

definition ta_agnostic :: "('s state \<Rightarrow> bool) \<Rightarrow> bool" where
 "ta_agnostic P \<equiv> \<forall>s taf. P (ms_ta_update taf s) = P s"

abbreviation ignore_ta :: "('s state \<Rightarrow> bool) \<Rightarrow> ('s state \<Rightarrow> bool)" where
  "ignore_ta P \<equiv> \<lambda>s. \<forall>taf. P (ms_ta_update taf s)"


lemma ta_agnostic_conj:
  "\<lbrakk>ta_agnostic P1; ta_agnostic P2\<rbrakk> \<Longrightarrow>
  ta_agnostic (\<lambda>s. P1 s \<and> P2 s)"
  by (clarsimp simp:ta_agnostic_def)

lemma ta_agnostic_predconj:
  "\<lbrakk>ta_agnostic P1; ta_agnostic P2\<rbrakk> \<Longrightarrow>
  ta_agnostic (P1 and P2)"
  by (clarsimp simp:ta_agnostic_def)

lemma ta_agnostic_null[simp]:
  "ta_agnostic (\<lambda>s. P)"
  by (clarsimp simp:ta_agnostic_def)

lemma ta_agnostic_irrel_imp:
  "\<lbrakk>ta_agnostic P\<rbrakk> \<Longrightarrow>
  ta_agnostic (\<lambda>s. Q \<longrightarrow> P s)"
  apply (clarsimp simp:ta_agnostic_def)
  done


lemma ta_agnostic_allI:
  "(\<forall>x. ta_agnostic (\<lambda>s. P x s)) \<Longrightarrow>
  ta_agnostic (\<lambda>s. \<forall>x. P x s)"
  apply (clarsimp simp: ta_agnostic_def)
  done

lemma ta_agnostic_imp:
  "\<lbrakk>ta_agnostic Q;
  ta_agnostic P\<rbrakk> \<Longrightarrow>
  ta_agnostic (\<lambda>s. Q s \<longrightarrow> P s)"
  apply (clarsimp simp:ta_agnostic_def)
  done

lemma ignored_agnostic [simp]:
  "ta_agnostic (ignore_ta P)"
  apply (clarsimp simp:ta_agnostic_def)
  apply (rule iffI; clarsimp simp: comp_def)
  apply (drule_tac x="\<lambda>_. tafa (touched_addresses (machine_state s))" in spec)
  apply (metis (mono_tags, lifting) RISCV64.fold_congs(5) abstract_state.fold_congs(6))
  done

lemma agnostic_ignores:
  "ta_agnostic P \<Longrightarrow>
  ignore_ta P = P"
  apply (clarsimp simp: ta_agnostic_def)
  done

lemma ta_agnostic_ex_all:
  "(\<forall>x. ta_agnostic (P x)) \<Longrightarrow>
  ta_agnostic (\<lambda>s. \<exists>x. P x s)"
  apply (clarsimp simp:ta_agnostic_def)
  done

lemmas ta_agnostic_lemmas = ignored_agnostic
                            ta_agnostic_conj
                            ta_agnostic_predconj
                            ta_agnostic_irrel_imp

\<comment> \<open>note that ta is not strictly safe! conj and predconj and irrel_imp aren't safe,
   but we haven't yet come across scenarios where it isn't true, so `ta` intros these without
   backtracking\<close>
method ta uses simp = (
  \<comment> \<open>simplest solve by unwrapping ta_agnostic (plus whatever is given in simp)\<close>
  (solves \<open>clarsimp simp: ta_agnostic_def simp\<close>)
  \<comment> \<open>optionally do some simplification before trying other approaches\<close>
  | (clarsimp simp: simp)?, (
  \<comment> \<open>unwrap conj and predconj\<close>
  \<comment> \<open>fixme: only succeed if we complete generated subgoals?\<close>
  intro allI impI
        ta_agnostic_irrel_imp ta_agnostic_predconj ta_agnostic_conj
        ta_agnostic_ex_all ta_agnostic_allI ta_agnostic_imp; ta?
  ))

method tasafe uses simp =
  (solves \<open>ta\<close>)


\<comment> \<open>A locale for monads m that only change the TA set\<close>
locale touched_addresses_inv =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  fixes m :: "('state_ext::state_ext state, 'r) nondet_monad"
  assumes tainv: "\<And>P. m \<lbrace>ignore_ta P\<rbrace>"
begin

\<comment> \<open>If P doesn't care about the TA set, m preserves P even though it changes the TA set\<close>
lemma agnostic_preserved:
  "ta_agnostic P \<Longrightarrow> m \<lbrace>P\<rbrace>"
  unfolding ta_agnostic_def
  using tainv [of P] by simp

lemma in_inv_by_hoare:
  "\<lbrakk>(x, s') \<in> fst (m s); ignore_ta P s\<rbrakk> \<Longrightarrow>
  ignore_ta P s'"
  using tainv apply -
  unfolding valid_def
  apply (drule_tac x=P in meta_spec)
  apply (drule_tac x=s in spec, clarsimp)
  apply (drule_tac x="(x, s')" in bspec, assumption)
  apply clarsimp
  done

lemma in_inv_by_agnostic:
  "\<lbrakk>(x, s') \<in> fst (m s); ta_agnostic P; P s\<rbrakk> \<Longrightarrow>
  P s'"
  apply (drule in_inv_by_hoare [where P=P])
   apply (clarsimp simp:ta_agnostic_def)+
  done
end

locale touched_addresses_invE = touched_addresses_inv state_ext_t m
  for state_ext_t :: "'state_ext::state_ext itself"
  and m::"('state_ext::state_ext state, 'ra + 'rb) nondet_monad"
begin
lemma validE_tainv[wp]:
  "\<lbrace>ignore_ta P\<rbrace> m \<lbrace>\<lambda>_. ignore_ta P\<rbrace>, \<lbrace>\<lambda>_. ignore_ta P\<rbrace>"
  by (simp add: hoare_valid_validE tainv)

lemma validE2_tainv[wp]:
  "\<lbrace>ignore_ta P and ignore_ta Q\<rbrace> m \<lbrace>\<lambda>_. ignore_ta P\<rbrace>, \<lbrace>\<lambda>_. ignore_ta Q\<rbrace>"
  apply (rule valid_validE2, rule hoare_weaken_pre)
  apply (rule tainv [where P="P and Q"])
    apply simp+
  done

lemma validE_R_tainv[wp]:
  "\<lbrace>ignore_ta P\<rbrace> m \<lbrace>\<lambda>_. ignore_ta P\<rbrace>, -"
  by (simp add: tainv valid_validE_R)

lemma agnostic_preservedE_R:
  "ta_agnostic P \<Longrightarrow> \<lbrace>P\<rbrace> m \<lbrace>\<lambda>_. P\<rbrace>, -"
  unfolding ta_agnostic_def
  by (simp add: agnostic_preserved ta_agnostic_def valid_validE_R)

lemma agnostic_preservedE:
  "ta_agnostic P \<Longrightarrow> \<lbrace>P\<rbrace> m \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding ta_agnostic_def
  by (simp add: agnostic_preserved ta_agnostic_def valid_validE)

lemma agnostic_preservedE2:
  "ta_agnostic P \<Longrightarrow> ta_agnostic Q \<Longrightarrow> \<lbrace>P and Q\<rbrace> m \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (rule valid_validE2 [where Q'="P and Q"])
    apply (rule agnostic_preserved)
    apply (simp add: ta_agnostic_def)
  apply simp+
  done
  
end

(*FIXME: does this actually do anything? *)
sublocale touched_addresses_invE \<subseteq> touched_addresses_inv
  by unfold_locales

(*TODO: how do we get the sublocale-interpretations of touched_addresses_P_inv to map into things
  like agnostic_preservedE_R above?  *)

term "state_ext"
term "state_ext state"

(* these have been removed, as we are trying to avoid certain notations that do not
   simplify nicely.
abbreviation ta_obj_upd :: "machine_word \<Rightarrow> kernel_object \<Rightarrow> machine_state \<Rightarrow> machine_state"
  where
  "ta_obj_upd p ko ms \<equiv> machine_state.touched_addresses_update ((\<union>) (obj_range p ko)) ms"

abbreviation ms_ta_obj_upd :: "machine_word \<Rightarrow> kernel_object \<Rightarrow> 'a state \<Rightarrow> 'a state"
  where
  "ms_ta_obj_upd p ko s \<equiv> s \<lparr> machine_state := ta_obj_upd p ko (machine_state s) \<rparr>"
*)

abbreviation ms_ta_obj_update :: "machine_word \<Rightarrow> kernel_object \<Rightarrow> 'a state \<Rightarrow> 'a state"
  where
  "ms_ta_obj_update p ko s \<equiv> ms_ta_update ((\<union>) (obj_range p ko)) s"


\<comment> \<open>A locale for propositions P that don't care about the TA set (ta_agnostic P),
   relative to a monad m that only changes TA (via locale touched_addresses_inv).
   Instantiate this locale to add a rule to the [wp] set that says m preserves P. \<close>
locale touched_addresses_P_inv = touched_addresses_inv state_ext_t m
  for state_ext_t :: "'state_ext::state_ext itself"
  and m::"('state_ext::state_ext state, 'r) nondet_monad" +
  fixes P :: "'state_ext::state_ext state \<Rightarrow> bool"
  assumes ta_agnostic [simp]: "ta_agnostic P"
begin
lemma m_inv [wp]:
  "m \<lbrace>P\<rbrace>"
  by (rule agnostic_preserved [OF ta_agnostic])

(*FIXME: maybe these should be in a different locale, as this will be duplicated (and
  added to the simp set) for every monad that instantiates touched_addresses_inv -scottb *)
lemma ms_ta_update_simplify [simp]:
  "P (ms_ta_update taf s) = P s"
  by (meson ta_agnostic ta_agnostic_def)

lemma ms_ta_obj_update_simplify [simp]:
  "P (ms_ta_obj_update p obj s) = P s"
  by simp

end

locale pspace_update_eq =
  fixes f :: "'z::state_ext state \<Rightarrow> 'c::state_ext state"
  assumes pspace: "kheap (f s) = kheap s"

locale Arch_pspace_update_eq = pspace_update_eq + Arch

locale pspace_ta_update_eq = pspace_update_eq f
  for f :: "'z::state_ext state \<Rightarrow> 'c::state_ext state" +
  assumes ta: "touched_addresses (machine_state (f s)) = touched_addresses (machine_state s)"

locale Arch_pspace_ta_update_eq = pspace_ta_update_eq + Arch

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

locale p_arch_ta_update_eq = pspace_ta_update_eq + arch_update_eq
locale Arch_p_arch_ta_update_eq = Arch_pspace_ta_update_eq + Arch_p_arch_update_eq

locale p_arch_idle_update_eq = p_arch_update_eq + arch_idle_update_eq
locale Arch_p_arch_idle_update_eq = Arch_p_arch_update_eq + Arch_arch_idle_update_eq

locale irq_states_update_eq =
  fixes f :: "'z::state_ext state \<Rightarrow> 'c::state_ext state"
  assumes int: "interrupt_states (f s) = interrupt_states s"

locale pspace_int_update_eq = pspace_update_eq + irq_states_update_eq
locale Arch_pspace_int_update_eq = Arch_pspace_update_eq + irq_states_update_eq

locale p_arch_idle_update_int_eq = p_arch_idle_update_eq + pspace_int_update_eq
locale Arch_p_arch_idle_update_int_eq = Arch_p_arch_idle_update_eq + Arch_pspace_int_update_eq

locale pspace_ta_int_update_eq = pspace_ta_update_eq + irq_states_update_eq
locale Arch_pspace_ta_int_update_eq = Arch_pspace_ta_update_eq + Arch_pspace_int_update_eq

locale p_arch_idle_update_ta_int_eq = p_arch_idle_update_int_eq + pspace_ta_int_update_eq
locale Arch_p_arch_idle_update_ta_int_eq = Arch_p_arch_idle_update_int_eq + Arch_pspace_ta_int_update_eq

section "Base definitions for Invariants"

definition
  obj_at :: "(kernel_object \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "obj_at P ref s \<equiv> \<exists>ko. kheap s ref = Some ko \<and> P ko"

lemma obj_at_pspaceI:
  "\<lbrakk> obj_at P ref s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> obj_at P ref s'"
  by (simp add: obj_at_def)

abbreviation "ko_at k \<equiv> obj_at ((=) k)"
abbreviation "ako_at ako == ko_at (ArchObj ako)"

lemma obj_atE:
  "\<lbrakk> obj_at P p s; \<And>ko. \<lbrakk> kheap s p = Some ko; P ko \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto simp: obj_at_def)

lemma obj_at_weakenE:
  "\<lbrakk> obj_at P r s; \<And>ko. P ko \<Longrightarrow> P' ko \<rbrakk> \<Longrightarrow> obj_at P' r s"
  by (clarsimp simp: obj_at_def)

lemma ko_at_weakenE:
  "\<lbrakk> ko_at k ptr s; P k \<rbrakk> \<Longrightarrow> obj_at P ptr s"
  by (erule obj_at_weakenE, simp)

lemma ko_atD:
  "ko_at obj pos s \<Longrightarrow> kheap s pos = Some obj"
  by (blast elim: obj_atE)


text \<open>An alternative formulation that allows abstraction over type:\<close>

lemmas a_type_simps =
  a_type_def[split_simps kernel_object.split]

lemma [simp]:
  "a_type (Endpoint x) = AEndpoint"
  "a_type (Notification v) = ANTFN"
  by (simp_all add: a_type_def)

lemma a_type_aa_type: "(a_type (ArchObj ako) = AArch T) = (aa_type ako = T)"
  by (simp add: a_type_def)

abbreviation
  "typ_at T \<equiv> obj_at (\<lambda>ob. a_type ob = T)"

abbreviation
  "typs_of \<equiv> \<lambda>s. kheap s ||> a_type"

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

lemma pspace_distinctD:
  "\<lbrakk> kheap s x = Some ko; kheap s y = Some ko'; x \<noteq> y; pspace_distinct s \<rbrakk>
   \<Longrightarrow> mask_range x (obj_bits ko) \<inter> mask_range y (obj_bits ko') = {}"
  by (simp add: pspace_distinct_def mask_def)

definition
  caps_of_state :: "'z::state_ext state \<Rightarrow> cslot_ptr \<Rightarrow> cap option"
where
 "caps_of_state s \<equiv> (\<lambda>p. if (\<exists>cap. fst (get_cap False p s) = {(cap, s)})
                         then Some (THE cap. fst (get_cap False p s) = {(cap, s)})
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

(* FIXME this is not a destruction rule of sym_refs *)
lemma sym_refsD:
  "\<lbrakk> (y, tp) \<in> st x; sym_refs st \<rbrakk> \<Longrightarrow> (x, symreftype tp) \<in> st y"
  apply (simp add: sym_refs_def)
  apply (drule spec, drule(1) bspec)
  apply simp
  done

(* FIXME this is not a elimination rule of sym_refs *)
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

abbreviation (input)
  "bound a \<equiv> a \<noteq> None"

lemma inj_ObjRef[simp]: "inj ObjRef" by (auto intro!: injI)
lemma inj_IRQRef[simp]: "inj IRQRef" by (auto intro!: injI)
lemma inj_ArchRef[simp]: "inj ArchRef" by (auto intro!: injI)

lemmas arch_cap_set_map_simps[simp] = arch_cap_set_map_def[split_simps cap.split]

lemma a_typeE:
  "\<lbrakk>a_type ko = ACapTable sz; (\<And>cs. \<lbrakk> ko = CNode sz cs; well_formed_cnode_n sz cs \<rbrakk> \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>a_type ko = ATCB; (\<And>tcb. ko = TCB tcb \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>a_type ko = AEndpoint; (\<And>ep. ko = Endpoint ep \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>a_type ko = ANTFN; (\<And>ntfn. ko = Notification ntfn \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>a_type ko = AArch T; (\<And>ao. \<lbrakk> ko = ArchObj ao; aa_type ao = T \<rbrakk> \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>a_type ko = AGarbage sz;
    (\<And>sz' cs. \<lbrakk> ko = CNode (sz - cte_level_bits) cs; \<not>well_formed_cnode_n sz' cs;
                cte_level_bits \<le> sz \<rbrakk> \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R"
  by (cases ko; clarsimp simp add: a_type_def split: if_split_asm)+

lemma typ_at_typs_of:
  "typ_at T p s = (typs_of s p = Some T)"
  by (auto simp: obj_at_def in_opt_map_eq)

(* This generalises pd_shifting' in ARM and ARM_HYP *)
lemma pd_shifting_gen:
  "\<lbrakk>b \<le> a; size pd - c \<le> a - b; is_aligned pd c \<rbrakk> \<Longrightarrow> pd + (vptr >> a << b) && ~~ mask c = pd"
  apply (subgoal_tac "(vptr >> a << b) && ~~ mask c = 0")
   apply (subst word_plus_and_or_coroll)
    apply (erule aligned_mask_disjoint)
    apply (simp add: and_mask_0_iff_le_mask[symmetric])
   apply (simp add: bit.conj_disj_distrib2)
  apply (simp add: shiftr_shiftl1 neg_mask_twice word_bw_assocs)
  apply (rule shiftr_not_mask_0)
  apply (fastforce simp: max_def word_size)
  done

end
