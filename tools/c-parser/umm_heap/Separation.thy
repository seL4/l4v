(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* License: BSD, terms see file ./LICENSE *)

theory Separation
imports TypHeap
begin

(* The store is not captured explicitly, variable values may appear in
   predicates and do not require special treatment *)
type_synonym ('a,'b) map_assert = "('a \<rightharpoonup> 'b) \<Rightarrow> bool"
type_synonym heap_assert = "(addr \<times> s_heap_index,s_heap_value) map_assert"

definition sep_emp :: "('a,'b) map_assert" ("\<box>") where
  "sep_emp \<equiv> (op =) empty"

definition sep_true :: "('a,'b) map_assert" where
  "sep_true \<equiv> \<lambda>s. True"

definition sep_false :: "('a,'b) map_assert" where
  "sep_false \<equiv> \<lambda>s. False"

definition
  sep_conj :: "('a,'b) map_assert \<Rightarrow> ('a,'b) map_assert \<Rightarrow> ('a,'b) map_assert"
  (infixr "\<and>\<^sup>*" 35)
where
  "P \<and>\<^sup>* Q \<equiv> \<lambda>s. \<exists>s\<^sub>0 s\<^sub>1. s\<^sub>0 \<bottom> s\<^sub>1 \<and> s = s\<^sub>1 ++ s\<^sub>0 \<and> P s\<^sub>0 \<and> Q s\<^sub>1"

definition
  sep_impl :: "('a,'b) map_assert \<Rightarrow> ('a,'b) map_assert \<Rightarrow> ('a,'b) map_assert"
  (infixr "\<longrightarrow>\<^sup>*" 25)
where
  "x \<longrightarrow>\<^sup>* y \<equiv> \<lambda>s. \<forall>s'. s \<bottom> s' \<and> x s' \<longrightarrow> y (s ++ s')"


definition
  singleton :: "'a::c_type ptr \<Rightarrow> 'a \<Rightarrow> heap_mem \<Rightarrow> heap_typ_desc \<Rightarrow> heap_state"
where
  "singleton p v h d \<equiv> lift_state (heap_update p v h,d) |` s_footprint p"

text {*
  Like in Separation.thy, these arrows are defined using bsub and esub but
  have an \emph{input} syntax abbreviation with just sub.
  Why? Because if sub is the only way, people write things like
  @{text "p \<mapsto>\<^sup>i\<^sub>(f x y) v"} instead of @{text "p \<mapsto>\<^sup>i\<^bsub>(f x y)\<^esub> v"}. We preserve
  the sub syntax though, because esub and bsub are a pain to type.
*}

definition
  sep_map :: "'a::c_type ptr \<Rightarrow> 'a ptr_guard \<Rightarrow> 'a \<Rightarrow> heap_assert"
  ("_ \<mapsto>\<^bsub>_\<^esub> _" [56,0,51] 56)
where
  "p \<mapsto>\<^bsub>g\<^esub> v \<equiv> \<lambda>s. lift_typ_heap g s p = Some v \<and> dom s = s_footprint p \<and> wf_heap_val s"

notation (input)
  sep_map ("_ \<mapsto>\<^sub>_ _" [56,1000,51] 56)

definition
  sep_map_any :: "'a ::c_type ptr \<Rightarrow> 'a ptr_guard \<Rightarrow> heap_assert" ("_ \<mapsto>\<^bsub>_\<^esub> -" [56,0] 56)
where
  "p \<mapsto>\<^bsub>g\<^esub> - \<equiv> \<lambda>s. \<exists>v. (p \<mapsto>\<^sub>g v) s"

notation (input)
  sep_map_any ("_ \<mapsto>\<^sub>_ -" [56,0] 56)

definition
  sep_map' :: "'a::c_type ptr \<Rightarrow> 'a ptr_guard \<Rightarrow> 'a \<Rightarrow> heap_assert" ("_ \<hookrightarrow>\<^bsub>_\<^esub> _" [56,0,51] 56)
where
  "p \<hookrightarrow>\<^bsub>g\<^esub> v \<equiv> (p \<mapsto>\<^bsub>g\<^esub> v) \<and>\<^sup>* sep_true"

notation (input)
  sep_map' ("_ \<hookrightarrow>\<^sub>_ _" [56,1000,51] 56)

definition
  sep_map'_any :: "'a ::c_type ptr \<Rightarrow> 'a ptr_guard  \<Rightarrow> heap_assert" ("_ \<hookrightarrow>\<^bsub>_\<^esub> -" [56,0] 56)
where
  "p \<hookrightarrow>\<^bsub>g\<^esub> - \<equiv> \<lambda>s. \<exists>x. (p \<hookrightarrow>\<^sub>g x) s"

notation (input)
  sep_map'_any ("_ \<hookrightarrow>\<^sub>_ -" [56,0] 56)

syntax
  "_sep_assert" :: "bool \<Rightarrow> heap_state \<Rightarrow> bool" ("'(_')\<^bsup>sep\<^esup>" [0] 100)


text {* ---- *}

lemma sep_empD:
  "\<box> s \<Longrightarrow> s = empty"
  by (simp add: sep_emp_def)

lemma sep_emp_empty [simp]:
  "\<box> empty"
  by (simp add: sep_emp_def)

lemma sep_true [simp]:
  "sep_true s"
  by (simp add: sep_true_def)

lemma sep_false [simp]:
  "\<not> sep_false s"
  by (simp add: sep_false_def)

declare sep_false_def [symmetric, simp add]

lemma singleton_dom':
  "dom (singleton p (v::'a::mem_type) h d) = dom (lift_state (h,d)) \<inter> s_footprint p"
apply(auto simp: singleton_def lift_state_def
           split: if_split_asm s_heap_index.splits)
done

lemma lift_state_dom:
  "d,g \<Turnstile>\<^sub>t p \<Longrightarrow> s_footprint (p::'a::mem_type ptr) \<subseteq> dom (lift_state (h,d))"
apply(clarsimp simp: h_t_valid_def valid_footprint_def Let_def)
apply(auto simp: lift_state_def split: s_heap_index.splits option.splits)
 apply(drule s_footprintD)
 apply(drule intvlD, clarsimp simp: size_of_def)
 apply(frule s_footprintD2)
apply(rename_tac nat)
apply(drule s_footprintD)
apply(drule intvlD, clarsimp)
apply(drule_tac x=k in spec)
apply(erule impE)
 apply(simp add: size_of_def)
apply(subst (asm) word_unat.eq_norm)
apply(subst (asm) mod_less)
 apply(subst len_of_addr_card)
 apply(erule less_trans)
 apply(rule max_size)
apply(simp add: map_le_def)
apply auto
apply(drule_tac x=nat in bspec)
 apply clarsimp+
done

lemma singleton_dom:
  "d,g \<Turnstile>\<^sub>t p \<Longrightarrow> dom (singleton p (v::'a::mem_type) h d) = s_footprint p"
apply(subst singleton_dom')
apply(drule lift_state_dom)
apply fast
done

lemma wf_heap_val_restrict [simp]:
  "wf_heap_val s \<Longrightarrow> wf_heap_val (s |` X)"
apply(unfold wf_heap_val_def, clarify)
apply(auto simp: restrict_map_def)
done

lemma singleton_wf_heap_val [simp]:
  "wf_heap_val (singleton p v h d)"
apply(unfold singleton_def)
apply simp
done

lemma h_t_valid_restrict_proj_d:
  "\<lbrakk> proj_d s,g \<Turnstile>\<^sub>t p; \<forall>x. x \<in> s_footprint p \<longrightarrow> s x = s' x \<rbrakk> \<Longrightarrow>
      proj_d s',g \<Turnstile>\<^sub>t p"
apply(auto simp: h_t_valid_def valid_footprint_def Let_def)
 apply(drule_tac x=y in spec)
 apply simp
 apply(auto simp: proj_d_def map_le_def split: if_split_asm option.splits)
  apply(drule_tac x="ptr_val p + of_nat y" in spec)
  apply(drule_tac x="SIndexTyp a" in spec)
  apply(erule impE)
   apply(erule  s_footprintI)
   apply(simp add: size_of_def)
  apply simp
 apply(drule_tac x="ptr_val p + of_nat y" in spec)
 apply(drule_tac x="SIndexTyp a" in spec)
 apply(erule impE)
  apply(erule s_footprintI)
  apply(simp add: size_of_def)
 apply simp
apply(drule_tac x=y in spec)
apply clarsimp
apply(drule_tac x="ptr_val p + of_nat y" in spec)
apply(drule_tac x="SIndexVal" in spec)
apply(erule impE)
 apply(rule s_footprintI2)
 apply(simp add: size_of_def)
apply(rule_tac x=ya in exI)
apply simp
done

lemma s_valid_restrict [simp]:
  "s |` s_footprint p,g \<Turnstile>\<^sub>s p = s,g \<Turnstile>\<^sub>s p"
apply(auto simp: s_valid_def )
 apply(erule h_t_valid_restrict_proj_d)
 apply(simp add: s_footprint_restrict)
apply(erule h_t_valid_restrict_proj_d)
apply(simp add: s_footprint_restrict)
done

lemma proj_h_restrict:
  "(x,SIndexVal) \<in> X \<Longrightarrow> proj_h (s |` X) x = proj_h s x"
apply(auto simp: proj_h_def)
done

lemma heap_list_s_restrict [rule_format]:
  "\<forall>p. (\<lambda>x. (x,SIndexVal)) ` {p..+n} \<subseteq> X \<longrightarrow>
      heap_list_s (s |` X) n p = heap_list_s s n p"
apply(induct_tac n)
 apply(simp add: heap_list_s_def)
apply(auto simp: heap_list_s_def)
 apply(rule proj_h_restrict)
 apply(subgoal_tac "p \<in> {p..+Suc n}")
  apply fast
 apply(rule intvl_self, simp)
apply(drule_tac x="p+1" in spec)
apply clarsimp
apply(subgoal_tac "{p+1..+n} \<subseteq> {p..+Suc n}")
 apply fast
apply clarsimp
apply(rule intvl_plus_sub_Suc)
apply simp
done

lemma lift_typ_heap_restrict [simp]:
  "lift_typ_heap g (s |` s_footprint p) p = lift_typ_heap g s p"
apply(auto simp: lift_typ_heap_if)
apply(subst heap_list_s_restrict)
 apply clarsimp
 apply(drule intvlD, clarsimp)
 apply(erule s_footprintI2)
apply simp
done

lemma singleton_s_valid:
  "d,g \<Turnstile>\<^sub>t p \<Longrightarrow> singleton p (v::'a::mem_type) h d,g \<Turnstile>\<^sub>s p"
apply(simp add: singleton_def)
thm h_t_valid_restrict
apply(subst h_t_s_valid)
apply simp
done

lemma singleton_lift_typ_heap_Some:
  "d,g \<Turnstile>\<^sub>t p \<Longrightarrow> lift_typ_heap g (singleton p v h d) p = Some (v::'a::mem_type)"
apply(subst singleton_def)
apply simp
apply(subst lift_t)
apply(subst lift_t_heap_update)
 apply(simp add: h_t_valid_restrict)
apply(simp add: ptr_retyp_h_t_valid)
done

lemma sep_map_g:
  "(p \<mapsto>\<^sub>g v) s \<Longrightarrow> g p"
  by (force simp: sep_map_def dest: lift_typ_heap_g)

lemma sep_map_g_sep_false:
  "\<not> g p \<Longrightarrow> (p \<mapsto>\<^sub>g v) = sep_false"
  by (simp add: sep_map_def lift_typ_heap_if s_valid_def h_t_valid_def)

lemma sep_map_singleton:
  "d,g \<Turnstile>\<^sub>t p \<Longrightarrow> ((p::'a::mem_type ptr) \<mapsto>\<^sub>g v) (singleton p v h d)"
 by (simp add: sep_map_def singleton_lift_typ_heap_Some singleton_dom)

lemma sep_mapD:
  "(p \<mapsto>\<^sub>g v) s \<Longrightarrow> lift_typ_heap g s p = Some v \<and>
      dom s = s_footprint p \<and> wf_heap_val s"
  by (simp add: sep_map_def)

lemma sep_map_lift_typ_heapD:
  "(p \<mapsto>\<^sub>g v) s \<Longrightarrow> lift_typ_heap g s p = Some (v::'a::c_type)"
  by (simp add: sep_map_def)

lemma sep_map_dom_exc:
  "(p \<mapsto>\<^sub>g (v::'a::c_type)) s \<Longrightarrow> dom s = s_footprint p"
  by (simp add: sep_map_def)

lemma sep_map_inj:
  "\<lbrakk> (p \<mapsto>\<^sub>g (v::'a::c_type)) s; (p \<mapsto>\<^sub>h v') s \<rbrakk> \<Longrightarrow> v = v'"
  by (clarsimp simp: sep_map_def lift_typ_heap_if split: if_split_asm)

lemma sep_map_anyI_exc [simp]:
  "(p \<mapsto>\<^sub>g v) s \<Longrightarrow> (p \<mapsto>\<^sub>g -) s"
  by (force simp: sep_map_any_def)

lemma sep_map_anyD_exc:
  "(p \<mapsto>\<^sub>g -) s \<Longrightarrow> \<exists>v. (p \<mapsto>\<^sub>g v) s"
  by (force simp: sep_map_any_def)

lemma sep_map_any_singleton:
  "d,g \<Turnstile>\<^sub>t i \<Longrightarrow> (i \<mapsto>\<^sub>g -) (singleton i (v::'a::mem_type) h d)"
  by (unfold sep_map_any_def, rule_tac x=v in exI, erule sep_map_singleton)

lemma proj_h_heap_merge:
  "proj_h (s ++ t) = (\<lambda>x. if (x,SIndexVal) \<in>  dom t then proj_h t x else proj_h s x)"
  by (force simp: proj_h_def split: option.splits)

lemma s_valid_heap_merge_right:
  "s\<^sub>1,g \<Turnstile>\<^sub>s p \<Longrightarrow> s\<^sub>0 ++ s\<^sub>1,g \<Turnstile>\<^sub>s p"
 apply (simp add: s_valid_def h_t_valid_def valid_footprint_def Let_def
                (*proj_d_heap_merge*))
apply auto
 apply(drule_tac x=y in spec, simp)
 apply clarsimp
 apply(erule map_le_trans)
 apply(clarsimp simp: proj_d_def map_le_def split: option.splits)
apply(drule_tac x=y in spec, simp)
apply(clarsimp simp: proj_d_def map_le_def split: option.splits)
done

lemma proj_d_map_add_fst:
  "fst (proj_d (s ++ t) x) = (if (x,SIndexVal) \<in> dom t then fst (proj_d t x) else
      fst (proj_d s x))"
apply(auto simp: proj_d_def split: option.splits)
done

lemma proj_d_map_add_snd:
  "snd (proj_d (s ++ t) x) n = (if (x,SIndexTyp n) \<in> dom t then snd (proj_d t x) n else
      snd (proj_d s x) n)"
apply(auto simp: proj_d_def split: option.splits)
done

lemma proj_d_restrict_map_fst:
  "(x,SIndexVal) \<in> X \<Longrightarrow> fst (proj_d (s |` X) x) = fst (proj_d s x)"
apply(auto simp: proj_d_def)
done

lemma proj_d_restrict_map_snd:
  "(x,SIndexTyp n) \<in> X \<Longrightarrow> snd (proj_d (s |` X) x) n = snd (proj_d s x) n"
apply(auto simp: proj_d_def)
done

lemma s_valid_heap_merge_right2:
  "\<lbrakk> s\<^sub>0 ++ s\<^sub>1,g \<Turnstile>\<^sub>s p; s_footprint p \<subseteq> dom s\<^sub>1 \<rbrakk> \<Longrightarrow> s\<^sub>1,g \<Turnstile>\<^sub>s p"
apply(auto simp: s_valid_def h_t_valid_def valid_footprint_def Let_def)
 apply(clarsimp simp: map_le_def)
 apply(subst proj_d_map_add_snd)
 apply(clarsimp split: if_split_asm)
 apply(subgoal_tac "(ptr_val p + of_nat y,SIndexTyp a) \<in> s_footprint p")
  apply fast
 apply(erule s_footprintI)
 apply(simp add: size_of_def)
apply(subgoal_tac "(ptr_val p + of_nat y,SIndexVal) \<in> s_footprint p")
 apply(drule (1) subsetD)
 apply clarsimp
 apply(subst (asm) proj_d_map_add_fst)
 apply(drule_tac x=y in spec)
 apply(clarsimp split: if_split_asm)
apply(rule s_footprintI2)
apply(simp add: size_of_def)
done

lemma heap_list_s_heap_merge_right':
  "\<lbrakk> s\<^sub>1,g \<Turnstile>\<^sub>s (p::'a::c_type ptr); (*wf_heap_val s\<^sub>1;*) n \<le> size_of TYPE('a) \<rbrakk> \<Longrightarrow>
      heap_list_s (s\<^sub>0 ++ s\<^sub>1) n (ptr_val p + of_nat (size_of TYPE('a) - n))
          = heap_list_s s\<^sub>1 n (ptr_val p + of_nat (size_of TYPE('a) - n))"
proof (induct n)
  case 0 thus ?case by (simp add: heap_list_s_def)
next
  case (Suc n)
  hence "(ptr_val p + (of_nat (size_of TYPE('a) - Suc n)),SIndexVal) \<in> dom s\<^sub>1"
apply -
apply auto
    by - (drule_tac x="size_of TYPE('a) - Suc n" in s_valid_Some, auto)
  with Suc show ?case
    by (simp add: heap_list_s_def proj_h_heap_merge algebra_simps)
qed

lemma heap_list_s_heap_merge_right:
  "\<lbrakk> s\<^sub>1,g \<Turnstile>\<^sub>s ((Ptr p)::'a::c_type ptr) (*; wf_heap_state s\<^sub>1*) \<rbrakk> \<Longrightarrow>
      heap_list_s (s\<^sub>0 ++ s\<^sub>1) (size_of TYPE('a)) p =
          heap_list_s s\<^sub>1 (size_of TYPE('a)) p"
  by (force dest: heap_list_s_heap_merge_right')

lemma lift_typ_heap_heap_merge_right:
  "\<lbrakk> lift_typ_heap g s\<^sub>1 p = Some v (*; wf_heap_state s\<^sub>1*) \<rbrakk> \<Longrightarrow>
      lift_typ_heap g (s\<^sub>0 ++ s\<^sub>1) (p::'a::c_type ptr) = Some v"
  by (force simp: lift_typ_heap_if s_valid_heap_merge_right
                  heap_list_s_heap_merge_right split: if_split_asm)

lemma lift_typ_heap_heap_merge_sep_map:
  "(p \<mapsto>\<^sub>g v) s\<^sub>1 \<Longrightarrow>
      lift_typ_heap g (s\<^sub>0 ++ s\<^sub>1) p = Some (v::'a::c_type)"
  by - (drule sep_map_lift_typ_heapD,
        erule lift_typ_heap_heap_merge_right)

lemma sep_conjI:
  "\<lbrakk> P s\<^sub>0; Q s\<^sub>1; s\<^sub>0 \<bottom> s\<^sub>1; s = s\<^sub>1 ++ s\<^sub>0 \<rbrakk> \<Longrightarrow> (P \<and>\<^sup>* Q) s"
  by (force simp: sep_conj_def)

lemma sep_conjD:
  "(P \<and>\<^sup>* Q) s \<Longrightarrow> \<exists>s\<^sub>0 s\<^sub>1. s\<^sub>0 \<bottom> s\<^sub>1 \<and> s = s\<^sub>1 ++ s\<^sub>0 \<and> P s\<^sub>0 \<and> Q s\<^sub>1"
  by (force simp: sep_conj_def)

lemma sep_map'I:
  "((p \<mapsto>\<^sub>g v) \<and>\<^sup>* sep_true) s \<Longrightarrow> (p \<hookrightarrow>\<^sub>g v) s"
  by (simp add: sep_map'_def)

lemma sep_map'D:
  "(p \<hookrightarrow>\<^sub>g v) s \<Longrightarrow> ((p \<mapsto>\<^sub>g v) \<and>\<^sup>* sep_true) s"
  by (simp add: sep_map'_def)

lemma sep_map'_g_exc:
  "(p \<hookrightarrow>\<^sub>g v) s \<Longrightarrow> g p"
  by (force simp add: sep_map'_def dest: sep_conjD sep_map_g)

lemma sep_conj_sep_true:
  "P s \<Longrightarrow> (P \<and>\<^sup>* sep_true) s"
  by (erule_tac s\<^sub>1=empty in sep_conjI, simp+)

lemma sep_map_sep_map'_exc [simp]:
  "(p \<mapsto>\<^sub>g v) s \<Longrightarrow> (p \<hookrightarrow>\<^sub>g v) s"
  by (unfold sep_map'_def, erule sep_conj_sep_true)

lemma sep_conj_true [simp]:
  "(sep_true \<and>\<^sup>* sep_true) = sep_true"
  by (rule ext, simp, rule_tac s\<^sub>0=x and s\<^sub>1=empty in sep_conjI, auto)

lemma sep_conj_assocD:
  assumes l: "((P \<and>\<^sup>* Q) \<and>\<^sup>* R) s"
  shows "(P \<and>\<^sup>* (Q \<and>\<^sup>* R)) s"
proof -
  from l obtain s' s\<^sub>2 where disj_o: "s' \<bottom> s\<^sub>2" and merge_o: "s = s\<^sub>2 ++ s'" and
    l_o: "(P \<and>\<^sup>* Q) s'" and r_o: "R s\<^sub>2" by (force dest: sep_conjD)
  then obtain s\<^sub>0 s\<^sub>1 where disj_i: "s\<^sub>0 \<bottom> s\<^sub>1" and merge_i: "s' = s\<^sub>1 ++ s\<^sub>0" and
    l_i: "P s\<^sub>0" and r_i: "Q s\<^sub>1" by (force dest: sep_conjD)
  from disj_o disj_i merge_i have disj_i': "s\<^sub>1 \<bottom> s\<^sub>2"
    by (force simp: map_ac_simps)
  with r_i and r_o have r_o': "(Q \<and>\<^sup>* R) (s\<^sub>2 ++ s\<^sub>1)" by (fast intro: sep_conjI)
  from disj_o merge_i disj_i disj_i' have "s\<^sub>0 \<bottom> s\<^sub>2 ++ s\<^sub>1"
    by (force simp: map_ac_simps)
  with r_o' l_i have "(P \<and>\<^sup>* (Q \<and>\<^sup>* R)) ((s\<^sub>2 ++ s\<^sub>1) ++ s\<^sub>0)"
    by (force intro: sep_conjI)
  moreover from merge_o merge_i disj_i disj_i' have "s = ((s\<^sub>2 ++ s\<^sub>1) ++ s\<^sub>0)"
    by (simp add: map_add_assoc [symmetric])
  ultimately show ?thesis by simp
qed

(* Reynolds' properties from "Separation Logic: A Logic for Shared
   Mutable Data Structures", page 5-6.  *)

lemma sep_conj_com:
  "(P \<and>\<^sup>* Q) = (Q \<and>\<^sup>* P)"
  by (rule ext) (auto simp: map_ac_simps sep_conjI dest!: sep_conjD)

lemma sep_conj_false_right [simp]:
  "(P \<and>\<^sup>* sep_false) = sep_false"
  by (force dest: sep_conjD)

lemma sep_conj_false_left [simp]:
  "(sep_false \<and>\<^sup>* P) = sep_false"
  by (simp add: sep_conj_com)

lemma sep_conj_comD:
  "(P \<and>\<^sup>* Q) s \<Longrightarrow> (Q \<and>\<^sup>* P) s"
  by (simp add: sep_conj_com)

(* FIXME: the need for this kind of special case should disappear with
   generalised separation conjunction *)
lemma exists_left:
  "(Q \<and>\<^sup>* (\<lambda>s. \<exists>x. P x s)) = ((\<lambda>s. \<exists>x. P x s) \<and>\<^sup>* Q)" by (simp add: sep_conj_com)

lemma sep_conj_assoc:
  "((P \<and>\<^sup>* Q) \<and>\<^sup>* R) = (P \<and>\<^sup>* (Q \<and>\<^sup>* R))" (is "?x = ?y")
proof (rule ext, rule)
  fix s
  assume "?x s"
  thus "?y s" by - (erule sep_conj_assocD)
next
  fix s
  assume "?y s"
  hence "((R \<and>\<^sup>* Q) \<and>\<^sup>* P) s" by (simp add: sep_conj_com)
  hence "(R \<and>\<^sup>* (Q \<and>\<^sup>* P)) s" by - (erule sep_conj_assocD)
  thus "?x s" by (simp add: sep_conj_com)
qed

(* For permutative rewriting *)
lemma sep_conj_left_com:
  "(P \<and>\<^sup>* (Q \<and>\<^sup>* R)) = (Q \<and>\<^sup>* (P \<and>\<^sup>* R))" (is "?x = ?y")
proof -
  have "?x = ((Q \<and>\<^sup>* R) \<and>\<^sup>* P)" by (simp add: sep_conj_com)
  also have "\<dots> = (Q \<and>\<^sup>* (R \<and>\<^sup>* P))" by (subst sep_conj_assoc, simp)
  finally show ?thesis by (simp add: sep_conj_com)
qed

lemmas sep_conj_ac = sep_conj_com sep_conj_assoc sep_conj_left_com

lemma sep_conj_empty:
  "(P \<and>\<^sup>* \<box>) = P"
proof (rule ext, rule)
  fix x
  assume "(P \<and>\<^sup>* \<box>) x"
  thus "P x" by (force simp: sep_emp_def dest: sep_conjD)
next
  fix x
  assume "P x"
  moreover have "\<box> empty" by simp
  ultimately show "(P \<and>\<^sup>* \<box>) x" by - (erule (1) sep_conjI, auto)
qed

lemma sep_conj_empty' [simp]:
  "(\<box> \<and>\<^sup>* P) = P"
 by (simp add: sep_conj_empty sep_conj_ac)

lemma sep_conj_true_P [simp]:
  "(sep_true \<and>\<^sup>* (sep_true \<and>\<^sup>* P)) = (sep_true \<and>\<^sup>* P)"
  by (simp add: sep_conj_ac)

lemma sep_map'_unfold_exc:
  "(p \<hookrightarrow>\<^sub>g v) = ((p \<hookrightarrow>\<^sub>g v) \<and>\<^sup>* sep_true)"
  by (simp add: sep_map'_def sep_conj_ac)

lemma sep_conj_disj:
  "((\<lambda>s. P s \<or> Q s) \<and>\<^sup>* R) s = ((P \<and>\<^sup>* R) s \<or> (Q \<and>\<^sup>* R) s)" (is "?x = (?y \<or> ?z)")
proof rule
  assume ?x
  then obtain s\<^sub>0 s\<^sub>1 where "s\<^sub>0 \<bottom> s\<^sub>1" and "s = s\<^sub>1 ++ s\<^sub>0" and "P s\<^sub>0 \<or> Q s\<^sub>0" and
      "R s\<^sub>1"
    by - (drule sep_conjD, auto)
  moreover hence "\<not> ?z \<Longrightarrow> \<not> Q s\<^sub>0"
    by - (clarsimp, erule notE, erule (2) sep_conjI, simp)
  ultimately show "?y \<or> ?z" by (force intro: sep_conjI)
next
  have "?y \<Longrightarrow> ?x"
    by (force simp: map_ac_simps intro: sep_conjI dest: sep_conjD)
  moreover have "?z \<Longrightarrow> ?x"
    by (force simp: map_ac_simps intro: sep_conjI dest: sep_conjD)
  moreover assume "?y \<or> ?z"
  ultimately show ?x by fast
qed

lemma sep_conj_conj:
  "((\<lambda>s. P s \<and> Q s) \<and>\<^sup>* R) s \<Longrightarrow> (P \<and>\<^sup>* R) s \<and> (Q \<and>\<^sup>* R) s"
  by (force intro: sep_conjI dest!: sep_conjD)

lemma sep_conj_exists1:
  "((\<lambda>s. \<exists>x. P x s) \<and>\<^sup>* Q) = (\<lambda>s. (\<exists>x. (P x \<and>\<^sup>* Q) s))"
  by (force intro: sep_conjI dest: sep_conjD)

lemma sep_conj_exists2:
  "(P \<and>\<^sup>* (\<lambda>s. \<exists>x. Q x s)) = (\<lambda>s. (\<exists>x. (P \<and>\<^sup>* Q x) s))"
  by (force intro: sep_conjI dest: sep_conjD)

lemmas sep_conj_exists = sep_conj_exists1 sep_conj_exists2

lemma sep_conj_forall:
  "((\<lambda>s. \<forall>x. P x s) \<and>\<^sup>* Q) s \<Longrightarrow> (P x \<and>\<^sup>* Q) s"
  by (force intro: sep_conjI dest: sep_conjD)

lemma sep_conj_impl:
  "\<lbrakk> (P \<and>\<^sup>* Q) s; \<And>s. P s \<Longrightarrow> P' s; \<And>s. Q s \<Longrightarrow> Q' s \<rbrakk> \<Longrightarrow> (P' \<and>\<^sup>* Q') s"
  by (force intro: sep_conjI dest: sep_conjD)

lemma sep_conj_sep_true_left:
  "(P \<and>\<^sup>* Q) s \<Longrightarrow> (sep_true \<and>\<^sup>* Q) s"
  by (erule sep_conj_impl, simp+)

lemma sep_conj_sep_true_right:
  "(P \<and>\<^sup>* Q) s \<Longrightarrow> (P \<and>\<^sup>* sep_true) s"
  by (subst (asm) sep_conj_com, drule sep_conj_sep_true_left,
      simp add: sep_conj_ac)

lemma sep_globalise:
  "\<lbrakk> (P \<and>\<^sup>* R) s; (\<And>s. P s \<Longrightarrow> Q s) \<rbrakk> \<Longrightarrow> (Q \<and>\<^sup>* R) s"
  by (fast elim: sep_conj_impl)

lemma sep_implI:
  "\<forall>s'. s \<bottom> s' \<and> x s' \<longrightarrow> y (s ++ s') \<Longrightarrow> (x \<longrightarrow>\<^sup>* y) s"
  by (force simp: sep_impl_def)

lemma sep_implI':
  assumes x: "\<And>h'. \<lbrakk> h \<bottom> h'; x h' \<rbrakk> \<Longrightarrow> y (h ++ h')"
  shows "(x \<longrightarrow>\<^sup>* y) h"
  apply (simp add: sep_impl_def)
  apply (intro allI impI)
  apply (erule conjE)
  apply (erule (1) x)
  done

lemma sep_implD:
  "(x \<longrightarrow>\<^sup>* y) s \<Longrightarrow> \<forall>s'. s \<bottom> s' \<and> x s' \<longrightarrow> y (s ++ s')"
  by (force simp: sep_impl_def)

lemma sep_emp_sep_impl [simp]:
  "(\<box> \<longrightarrow>\<^sup>* P) = P"
apply(rule ext)
apply(auto simp: sep_impl_def)
 apply(drule_tac x=empty in spec)
 apply auto
apply(drule sep_empD)
apply simp
done

lemma sep_impl_sep_true [simp]:
  "(P \<longrightarrow>\<^sup>* sep_true) = sep_true"
  by (force intro: sep_implI)

lemma sep_impl_sep_false [simp]:
  "(sep_false \<longrightarrow>\<^sup>* P) = sep_true"
  by (force intro: sep_implI)

lemma sep_impl_sep_true_P:
  "(sep_true \<longrightarrow>\<^sup>* P) s \<Longrightarrow> P s"
  by (auto dest!: sep_implD, drule_tac x=empty in spec, simp)

lemma sep_impl_sep_true_false [simp]:
  "(sep_true \<longrightarrow>\<^sup>* sep_false) = sep_false"
  by (force dest: sep_impl_sep_true_P)

lemma sep_impl_impl:
  "(P \<longrightarrow>\<^sup>* Q \<longrightarrow>\<^sup>* R) = (P \<and>\<^sup>* Q \<longrightarrow>\<^sup>* R)"
apply(rule ext)
apply rule
 apply(rule sep_implI)
 apply clarsimp
 apply(drule sep_conjD, clarsimp)
 apply(drule sep_implD)
 apply(drule_tac x=s\<^sub>0 in spec)
 apply(erule impE)
  apply(clarsimp simp: map_disj_def, fast)
 apply(drule sep_implD)
 apply(drule_tac x=s\<^sub>1 in spec)
 apply(erule impE)
  apply(clarsimp simp: map_disj_def, fast)
 apply(subst map_add_com [where h\<^sub>0=s\<^sub>1])
  apply(clarsimp simp: map_disj_def, fast)
 apply(subst map_add_assoc)
 apply simp
apply(rule sep_implI, clarsimp)
apply(rule sep_implI, clarsimp)
apply(drule sep_implD)
apply(drule_tac x="s' ++ s'a" in spec)
apply(erule impE)
 apply rule
  apply(clarsimp simp: map_disj_def, fast)
 apply(erule (1) sep_conjI)
  apply(clarsimp simp: map_disj_def, fast)
 apply(subst map_add_com)
  apply(clarsimp simp: map_disj_def, fast)
 apply simp
apply(simp add: map_add_assoc)
done

lemma sep_conj_sep_impl:
  "\<lbrakk> P s; \<And>s. (P \<and>\<^sup>* Q) s \<Longrightarrow> R s \<rbrakk> \<Longrightarrow> (Q \<longrightarrow>\<^sup>* R) s"
proof (rule sep_implI, clarsimp)
  fix s'
  assume "P s" and "s \<bottom> s'" and "Q s'"
  hence "(P \<and>\<^sup>* Q) (s ++ s')" by (force simp: map_ac_simps intro: sep_conjI)
  moreover assume "\<And>s. (P \<and>\<^sup>* Q) s \<Longrightarrow> R s"
  ultimately show "R (s ++ s')" by simp
qed

lemma sep_conj_sep_impl2:
  "\<lbrakk> (P \<and>\<^sup>* Q) s; \<And>s. P s \<Longrightarrow> (Q \<longrightarrow>\<^sup>* R) s \<rbrakk> \<Longrightarrow> R s"
  by (force simp: map_ac_simps dest: sep_implD sep_conjD)

lemma sep_map'_anyI_exc [simp]:
  "(p \<hookrightarrow>\<^sub>g v) s \<Longrightarrow> (p \<hookrightarrow>\<^sub>g -) s"
  by (force simp: sep_map'_any_def)

lemma sep_map'_anyD_exc:
  "(p \<hookrightarrow>\<^sub>g -) s \<Longrightarrow> \<exists>v. (p \<hookrightarrow>\<^sub>g v) s"
  by (force simp: sep_map'_any_def)

lemma sep_map'_any_unfold_exc:
  "(i \<hookrightarrow>\<^sub>g -) = ((i \<hookrightarrow>\<^sub>g -) \<and>\<^sup>* sep_true)"
  by (rule ext, simp add: sep_map'_any_def)
     (subst sep_map'_unfold_exc, subst sep_conj_com, subst sep_conj_exists,
      simp add: sep_conj_ac)

lemma sep_map'_inj_exc:
  assumes pv: "(p \<hookrightarrow>\<^sub>g (v::'a::c_type)) s" and pv': "(p \<hookrightarrow>\<^sub>h v') s"
  shows "v = v'"
proof -
  from pv pv' obtain s\<^sub>0 s\<^sub>1 s\<^sub>0' s\<^sub>1' where pv_m: "(p \<mapsto>\<^sub>g v) s\<^sub>1" and
      pv'_m: "(p \<mapsto>\<^sub>h v') s\<^sub>1'" and "s\<^sub>0 ++ s\<^sub>1 = s\<^sub>0' ++ s\<^sub>1'"
    by (force simp: sep_map'_def map_ac_simps dest!: sep_conjD)
  hence "s\<^sub>1 = s\<^sub>1'" by (force dest!: map_add_right_dom_eq sep_map_dom_exc)
  with pv_m pv'_m show ?thesis by (force dest: sep_map_inj)
qed

lemma sep_map'_any_dom_exc:
  "((p::'a::mem_type ptr) \<hookrightarrow>\<^sub>g -) s \<Longrightarrow> (ptr_val p,SIndexVal) \<in> dom s"
  by (clarsimp simp: sep_map'_def sep_map'_any_def sep_conj_ac
               dest!: sep_conjD)
     (subgoal_tac "s\<^sub>1 (ptr_val p,SIndexVal) \<noteq> None", force simp: map_ac_simps,
      force dest: sep_map_dom_exc)

lemma sep_map'_dom_exc:
  "(p \<hookrightarrow>\<^sub>g (v::'a::mem_type)) s \<Longrightarrow> (ptr_val p,SIndexVal) \<in> dom s"
apply(clarsimp simp: sep_map'_def sep_conj_ac dest!: sep_conjD)
apply(subgoal_tac "s\<^sub>1 (ptr_val p, SIndexVal) \<noteq> None")
 apply(force simp: map_ac_simps)
apply(drule sep_map_dom_exc)
apply(subgoal_tac "(ptr_val p, SIndexVal) \<in> s_footprint p")
 apply fast
apply(rule s_footprintI2 [where x=0, simplified])
apply simp
done

lemma sep_map'_lift_typ_heapD:
  "(p \<hookrightarrow>\<^sub>g v) s \<Longrightarrow>
      lift_typ_heap g s p = Some (v::'a::c_type)"
  by (force simp: sep_map'_def map_ac_simps dest: sep_conjD
                  lift_typ_heap_heap_merge_sep_map)

lemma sep_map'_merge:
  assumes map'_v: "(p \<hookrightarrow>\<^sub>g v) s\<^sub>0 \<or> (p \<hookrightarrow>\<^sub>g v) s\<^sub>1" and disj: "s\<^sub>0 \<bottom> s\<^sub>1"
  shows "(p \<hookrightarrow>\<^sub>g v) (s\<^sub>0 ++ s\<^sub>1)" (is "?x")
proof cases
  assume "(p \<hookrightarrow>\<^sub>g v) s\<^sub>0"
  with disj show ?x
    by (clarsimp simp: sep_map'_def sep_conj_ac dest!: sep_conjD)
       (rename_tac s\<^sub>0' s\<^sub>1', rule_tac s\<^sub>1="s\<^sub>1'" and s\<^sub>0="s\<^sub>0' ++ s\<^sub>1" in sep_conjI,
         auto simp: map_ac_simps)
next
  assume "\<not> (p \<hookrightarrow>\<^sub>g v) s\<^sub>0"
  with map'_v have "(p \<hookrightarrow>\<^sub>g v) s\<^sub>1" by simp
  with disj show ?x
    by (clarsimp simp: sep_map'_def sep_conj_ac dest!: sep_conjD)
       (rename_tac s\<^sub>0' s\<^sub>1', rule_tac s\<^sub>1="s\<^sub>1'" and s\<^sub>0="s\<^sub>0 ++ s\<^sub>0'" in sep_conjI,
        auto simp: map_ac_simps)
qed

lemma sep_conj_overlapD:
  "\<lbrakk> (P \<and>\<^sup>* Q) s; \<And>s. P s \<Longrightarrow> ((p::'a::mem_type ptr) \<hookrightarrow>\<^sub>g -) s;
      \<And>s. Q s \<Longrightarrow> (p \<hookrightarrow>\<^sub>h -) s \<rbrakk> \<Longrightarrow> False"
apply(drule sep_conjD, clarsimp simp: map_disj_def)
apply(subgoal_tac "(ptr_val p,SIndexVal) \<in> dom s\<^sub>0 \<and> (ptr_val p,SIndexVal) \<in> dom s\<^sub>1")
 apply fast
apply(fast intro!: sep_map'_any_dom_exc)
done

lemma sep_no_skew:
  "(\<lambda>s. (p \<hookrightarrow>\<^sub>g v) s \<and> (q \<hookrightarrow>\<^sub>h w) s) s \<Longrightarrow>
      p=q \<or> {ptr_val (p::'a::c_type ptr)..+size_of TYPE('a)} \<inter>
          {ptr_val q..+size_of TYPE('a)} = {}"
apply clarsimp
apply(drule sep_map'_lift_typ_heapD)+
apply(clarsimp simp: lift_typ_heap_if s_valid_def split: if_split_asm)
apply(rule ccontr)
apply(drule (1) h_t_valid_neq_disjoint)
  apply simp
 apply(rule peer_typ_not_field_of)
  apply simp+
done

lemma sep_no_skew2:
  "\<lbrakk> (\<lambda>s. (p \<hookrightarrow>\<^sub>g v) s \<and> (q \<hookrightarrow>\<^sub>h w) s) s; typ_uinfo_t TYPE('a) \<bottom>\<^sub>t typ_uinfo_t TYPE('b) \<rbrakk>
      \<Longrightarrow> {ptr_val (p::'a::c_type ptr)..+size_of TYPE('a)} \<inter>
          {ptr_val (q::'b::c_type ptr)..+size_of TYPE('b)} = {}"
apply clarsimp
apply(drule sep_map'_lift_typ_heapD)+
apply(clarsimp simp: lift_typ_heap_if s_valid_def split: if_split_asm)
apply(frule (1) h_t_valid_neq_disjoint[where q=q])
  apply(clarsimp simp: tag_disj_def sub_typ_proper_def)
  apply(simp add: typ_tag_lt_def)
 apply(clarsimp simp: tag_disj_def typ_tag_le_def field_of_t_def field_of_def)
apply assumption
done

lemma sep_conj_impl_same:
  "(P \<and>\<^sup>* (P \<longrightarrow>\<^sup>* Q)) s \<Longrightarrow> Q s"
apply(drule sep_conjD, clarsimp)
apply(drule sep_implD)
apply(drule_tac x="s\<^sub>0" in spec)
apply(clarsimp simp: map_disj_com)
done


(* Pure *)

definition pure :: "('a,'b) map_assert \<Rightarrow> bool" where
  "pure P \<equiv> \<forall>s s'. P s = P s'"

lemma pure_sep_true:
  "pure sep_true"
  by (simp add: pure_def)

lemma pure_sep_fasle:
  "pure sep_true"
  by (simp add: pure_def)

lemma pure_split:
  "pure P = (P = sep_true \<or> P = sep_false)"
  by (force simp: pure_def)

lemma pure_sep_conj:
  "\<lbrakk> pure P; pure Q \<rbrakk> \<Longrightarrow> pure (P \<and>\<^sup>* Q)"
  by (force simp: pure_split)

lemma pure_sep_impl:
  "\<lbrakk> pure P; pure Q \<rbrakk> \<Longrightarrow> pure (P \<longrightarrow>\<^sup>* Q)"
  by (force simp: pure_split)

lemma pure_conj_sep_conj:
  "\<lbrakk> (\<lambda>s. P s \<and> Q s) s; pure P \<or> pure Q \<rbrakk> \<Longrightarrow> (P \<and>\<^sup>* Q) s"
  by (force simp: pure_split sep_conj_ac intro: sep_conj_sep_true)

lemma pure_sep_conj_conj:
  "\<lbrakk> (P \<and>\<^sup>* Q) s; pure P; pure Q \<rbrakk> \<Longrightarrow> (\<lambda>s. P s \<and> Q s) s"
  by (force simp: pure_split)

lemma pure_conj_sep_conj_assoc:
  "pure P \<Longrightarrow> ((\<lambda>s. P s \<and> Q s) \<and>\<^sup>* R) = (\<lambda>s. P s \<and> (Q \<and>\<^sup>* R) s)"
  by (force simp: pure_split)

lemma pure_sep_impl_impl:
  "\<lbrakk> (P \<longrightarrow>\<^sup>* Q) s; pure P \<rbrakk> \<Longrightarrow> P s \<longrightarrow> Q s"
  by (force simp: pure_split dest: sep_impl_sep_true_P)

lemma pure_impl_sep_impl:
  "\<lbrakk> P s \<longrightarrow> Q s; pure P; pure Q \<rbrakk> \<Longrightarrow> (P \<longrightarrow>\<^sup>* Q) s"
  by (force simp: pure_split)

(* Intuitionistic *)

definition
  intuitionistic :: "('a,'b) map_assert \<Rightarrow> bool"
where
  "intuitionistic P \<equiv> \<forall>s s'. P s \<and> s \<subseteq>\<^sub>m s' \<longrightarrow> P s'"

lemma intuitionisticI:
  "(\<And>s s'. \<lbrakk> P s; s \<subseteq>\<^sub>m s' \<rbrakk> \<Longrightarrow> P s') \<Longrightarrow> intuitionistic P"
  by (unfold intuitionistic_def, fast)

lemma intuitionisticD:
  "\<lbrakk> intuitionistic P; P s; s \<subseteq>\<^sub>m s' \<rbrakk> \<Longrightarrow> P s'"
  by (unfold intuitionistic_def, fast)

lemma pure_intuitionistic:
  "pure P \<Longrightarrow> intuitionistic P"
  by (clarsimp simp: intuitionistic_def pure_def, fast)

lemma intuitionistic_sep_map':
  "intuitionistic (p \<hookrightarrow>\<^sub>g v)"
proof (rule intuitionisticI)
  fix s s'
  assume "(p \<hookrightarrow>\<^sub>g v) s"
  then obtain s\<^sub>0 s\<^sub>1 where "(p \<mapsto>\<^sub>g v) s\<^sub>0" and s: "s = s\<^sub>1 ++ s\<^sub>0"
    by (force dest!: sep_conjD sep_map'D)
  moreover assume "s \<subseteq>\<^sub>m s'"
  with s have "s' = s' |` (UNIV - dom s\<^sub>0) ++ s\<^sub>0"
    by - (simp, drule map_add_le_mapE, subst map_le_restrict, fast, force)
  ultimately show "(p \<hookrightarrow>\<^sub>g v) s'" by (force intro: sep_map'I sep_conjI)
qed

lemma intuitionistic_sep_conj_sep_true:
  "intuitionistic (P \<and>\<^sup>* sep_true)"
  by (rule intuitionisticI, drule sep_conjD, clarsimp)
     (erule_tac s\<^sub>1="s'|`(dom s' - dom s\<^sub>0)" in sep_conjI, simp,
      force simp: map_disj_def,
      force intro: map_le_dom_restrict_sub_add map_add_le_mapE  sym)

lemma intuitionistic_sep_impl_sep_true:
  "intuitionistic (sep_true \<longrightarrow>\<^sup>* P)"
proof (rule intuitionisticI, rule sep_implI, clarsimp)
  fix s s' s'a
  assume "(sep_true \<longrightarrow>\<^sup>* P) s" and le: "s \<subseteq>\<^sub>m s'" and "s' \<bottom> s'a"
  moreover hence "P (s ++ (s' |` (dom s' - dom s) ++ s'a))"
    by - (drule sep_implD,
          drule_tac x="s'|`(dom s' - dom s) ++ s'a" in spec,
          force simp: map_disj_def dest: map_disj_map_le)
  moreover have "dom s \<inter> dom (s' |` (dom s' - dom s)) = {}" by force
  ultimately show "P (s' ++ s'a)"
    by (force simp: map_le_dom_restrict_sub_add map_add_assoc dest!: map_add_comm)
qed

lemma intuitionistic_conj:
  "\<lbrakk> intuitionistic P; intuitionistic Q \<rbrakk> \<Longrightarrow> intuitionistic (\<lambda>s. P s \<and> Q s)"
  by (force intro: intuitionisticI dest: intuitionisticD)

lemma intuitionistic_disj:
  "\<lbrakk> intuitionistic P; intuitionistic Q \<rbrakk> \<Longrightarrow> intuitionistic (\<lambda>s. P s \<or> Q s)"
  by (force intro: intuitionisticI dest: intuitionisticD)

lemma intuitionistic_forall:
  "(\<And>x. intuitionistic (P x)) \<Longrightarrow> intuitionistic (\<lambda>s. \<forall>x. P x s)"
  by (force intro: intuitionisticI dest: intuitionisticD)

lemma intuitionistic_exists:
  "(\<And>x. intuitionistic (P x)) \<Longrightarrow> intuitionistic (\<lambda>s. \<exists>x. P x s)"
  by (force intro: intuitionisticI dest: intuitionisticD)

lemma intuitionistic_sep_conj:
  "intuitionistic (P::('a,'b) map_assert) \<Longrightarrow> intuitionistic (P \<and>\<^sup>* Q)"
proof (rule intuitionisticI, drule sep_conjD, clarsimp)
  fix s' s\<^sub>0 s\<^sub>1
  assume le: "s\<^sub>1 ++ s\<^sub>0 \<subseteq>\<^sub>m s'" and disj: "s\<^sub>0 \<bottom> (s\<^sub>1::'a \<rightharpoonup> 'b)"
  hence le_restrict: "s\<^sub>0 \<subseteq>\<^sub>m s' |` (dom s' - dom s\<^sub>1)"
    by - (rule map_le_dom_subset_restrict, erule map_add_le_mapE,
          force simp: map_disj_def  dest: map_le_implies_dom_le
          map_add_le_mapE)
  moreover assume "intuitionistic P" and "P s\<^sub>0"
  ultimately have "P (s' |` (dom s' - dom s\<^sub>1))"
    by - (erule (2) intuitionisticD)
  moreover from le_restrict have "s' |` (dom s' - dom s\<^sub>1) \<bottom> s\<^sub>1"
    by (force simp: map_disj_def dest: map_le_implies_dom_le)
  moreover from le disj have "s\<^sub>1 \<subseteq>\<^sub>m s'"
    by (subst (asm) map_add_comm, force  simp: map_disj_def)
       (erule map_add_le_mapE)
  hence "s' = s\<^sub>1 ++ s' |` (dom s' - dom s\<^sub>1)"
    by (subst map_add_comm, force simp: map_disj_def,
        force simp: map_le_dom_restrict_sub_add map_add_comm map_disj_def)
  moreover assume "Q s\<^sub>1"
  ultimately show "(P \<and>\<^sup>* Q) s'"
    by - (erule (3) sep_conjI)
qed

lemma intuitionistic_sep_impl:
  "intuitionistic (Q::('a,'b) map_assert) \<Longrightarrow> intuitionistic (P \<longrightarrow>\<^sup>* Q)"
proof (rule intuitionisticI, rule sep_implI, clarsimp)
  fix s s' s'a
  assume le: "s \<subseteq>\<^sub>m s'" and disj: "s' \<bottom> (s'a::'a \<rightharpoonup> 'b)"
  moreover hence "s ++ s'a \<subseteq>\<^sub>m s' ++ s'a"
  proof -
    from le disj have "s \<subseteq>\<^sub>m s ++ s'a"
      by (subst map_add_com)
         (force simp: map_disj_def dest: map_le_implies_dom_le, simp)
    with le disj show ?thesis
      by - (rule map_add_le_mapI, subst map_add_com,
            auto elim: map_le_trans)
  qed
  moreover assume "(P \<longrightarrow>\<^sup>* Q) s" and "intuitionistic Q" and "P s'a"
  ultimately show "Q (s' ++ s'a)"
    by (fast elim: map_disj_map_le intuitionisticD dest: sep_implD)
qed

lemma strongest_intuitionistic:
  "\<not> (\<exists>Q. (\<forall>s. (Q s \<longrightarrow> (P \<and>\<^sup>* sep_true) s)) \<and> intuitionistic Q \<and>
      Q \<noteq> (P \<and>\<^sup>* sep_true) \<and> (\<forall>s. P s \<longrightarrow> Q s))"
  by (force intro!: ext dest!: sep_conjD intuitionisticD)

lemma weakest_intuitionistic:
  "\<not> (\<exists>Q. (\<forall>s. ((sep_true \<longrightarrow>\<^sup>* P) s \<longrightarrow> Q s)) \<and> intuitionistic Q \<and>
      Q \<noteq> (sep_true \<longrightarrow>\<^sup>* P) \<and> (\<forall>s. Q s \<longrightarrow> P s))"
  apply (clarsimp intro!: ext)
  apply (rule iffI)
   apply (rule sep_implI')
   apply (drule_tac s=x and s'="x ++ h'" in intuitionisticD)
     apply (clarsimp simp: map_ac_simps)+
  done

lemma intuitionistic_sep_conj_sep_true_P:
  "\<lbrakk> (P \<and>\<^sup>* sep_true) s; intuitionistic P \<rbrakk> \<Longrightarrow> P s"
  by (force dest: intuitionisticD sep_conjD)

lemma intuitionistic_sep_conj_sep_true_simp:
  "intuitionistic P \<Longrightarrow> (P \<and>\<^sup>* sep_true) = P"
  by (fast intro: sep_conj_sep_true elim: intuitionistic_sep_conj_sep_true_P)

lemma intuitionistic_sep_impl_sep_true_P:
  "\<lbrakk> P s; intuitionistic P \<rbrakk> \<Longrightarrow> (sep_true \<longrightarrow>\<^sup>* P) s"
  by (force simp: map_add_com intro: sep_implI dest: intuitionisticD)

lemma intuitionistic_sep_impl_sep_true_simp:
  "intuitionistic P \<Longrightarrow> (sep_true \<longrightarrow>\<^sup>* P) = P"
  by (fast elim: sep_impl_sep_true_P intuitionistic_sep_impl_sep_true_P)

(* Domain exact *)

definition
  dom_exact :: "('a,'b) map_assert \<Rightarrow> bool"
where
  "dom_exact P \<equiv> \<forall>s s'. P s \<and> P s' \<longrightarrow> dom s = dom s'"

lemma dom_exactI:
  "(\<And>s s'. \<lbrakk> P s; P s' \<rbrakk> \<Longrightarrow> dom s = dom s') \<Longrightarrow> dom_exact P"
  by (unfold dom_exact_def, fast)

lemma dom_exactD:
  "\<lbrakk> dom_exact P; P s\<^sub>0; P s\<^sub>1 \<rbrakk> \<Longrightarrow> dom s\<^sub>0 = dom s\<^sub>1"
  by (unfold dom_exact_def, fast)

lemma dom_exact_sep_conj:
  "\<lbrakk> dom_exact P; dom_exact Q \<rbrakk> \<Longrightarrow> dom_exact (P \<and>\<^sup>* Q)"
  by (rule dom_exactI, (drule sep_conjD)+, clarsimp)
     (drule (2) dom_exactD, drule (2) dom_exactD, simp)

lemma dom_exact_sep_conj_conj:
  "\<lbrakk> (P \<and>\<^sup>* R) s; (Q \<and>\<^sup>* R) s; dom_exact R \<rbrakk> \<Longrightarrow> ((\<lambda>s. P s \<and> Q s) \<and>\<^sup>* R) s"
  by ((drule sep_conjD)+, clarsimp simp: sep_conj_ac,
      rule sep_conjI, fast, rule conjI)
     (fast, drule (2) dom_exactD, drule (1) map_disj_add_eq_dom_right_eq,
      auto simp: map_ac_simps)

lemma sep_conj_conj_simp:
  "dom_exact R \<Longrightarrow> ((\<lambda>s. P s \<and> Q s) \<and>\<^sup>* R) = (\<lambda>s. (P \<and>\<^sup>* R) s \<and> (Q \<and>\<^sup>* R) s)"
  by (fast intro!: sep_conj_conj dom_exact_sep_conj_conj)

definition dom_eps :: "('a,'b) map_assert \<Rightarrow> 'a set" where
  "dom_eps P \<equiv> THE x. \<forall>s. P s \<longrightarrow> x = dom s"

lemma dom_epsI:
  "\<lbrakk> dom_exact P; P s; x \<in> dom s \<rbrakk> \<Longrightarrow> x \<in> dom_eps P"
  by (unfold dom_eps_def, rule_tac a="dom s" in theI2)
     (fastforce simp: dom_exact_def, clarsimp+)

lemma dom_epsD [rule_format]:
  "\<lbrakk> dom_exact P; P s \<rbrakk> \<Longrightarrow> x \<in> dom_eps P \<longrightarrow> x \<in> dom s"
  by (unfold dom_eps_def, rule_tac a="dom s" in theI2)
     (fastforce simp: dom_exact_def, clarsimp+)

lemma dom_eps:
  "\<lbrakk> dom_exact P; P s \<rbrakk> \<Longrightarrow> dom s = dom_eps P"
  by (force intro: dom_epsI dest: dom_epsD)

lemma map_restrict_dom_exact:
  "\<lbrakk> dom_exact P; P s \<rbrakk> \<Longrightarrow> s |` dom_eps P = s"
  by (force simp: restrict_map_def None_com intro: dom_epsI)

lemma map_restrict_dom_exact2:
  "\<lbrakk> dom_exact P; P s\<^sub>0; s\<^sub>0 \<bottom> s\<^sub>1 \<rbrakk> \<Longrightarrow> (s\<^sub>1 |` dom_eps P) = empty"
  by (force simp: restrict_map_def map_disj_def dest: dom_epsD)

lemma map_restrict_dom_exact3:
  "\<lbrakk> dom_exact P; P s \<rbrakk> \<Longrightarrow> s |` (UNIV - dom_eps P) = empty"
  by (force simp: restrict_map_def dest: dom_epsI)

lemma map_add_restrict_dom_exact:
  "\<lbrakk> dom_exact P; s\<^sub>0 \<bottom> s\<^sub>1; P s\<^sub>1 \<rbrakk> \<Longrightarrow> (s\<^sub>1 ++ s\<^sub>0) |` (dom_eps P) = s\<^sub>1"
  by (simp add: map_add_restrict map_restrict_dom_exact)
     (subst map_restrict_dom_exact2, auto simp: map_disj_def)

lemma map_add_restrict_dom_exact2:
  "\<lbrakk> dom_exact P; s\<^sub>0 \<bottom> s\<^sub>1; P s\<^sub>0 \<rbrakk> \<Longrightarrow> (s\<^sub>1 ++ s\<^sub>0) |` (UNIV - dom_eps P) = s\<^sub>1"
  by (force simp: map_add_restrict map_disj_def dom_eps
            intro: restrict_map_subdom dest: map_restrict_dom_exact3 )

lemma dom_exact_sep_conj_forall:
  assumes sc: "\<forall>x. (P x \<and>\<^sup>* Q) s" and de: "dom_exact Q"
  shows "((\<lambda>s. \<forall>x. P x s) \<and>\<^sup>* Q) s"
proof (rule_tac s\<^sub>0="s |` (UNIV - dom_eps Q)" and  s\<^sub>1="s |` dom_eps Q" in sep_conjI)
  from sc de show "\<forall>x. P x (s |` (UNIV - dom_eps Q))"
    by (force simp: map_add_restrict_dom_exact2 sep_conj_ac dest: sep_conjD)
next
  from sc de show "Q (s |` dom_eps Q)"
    by (force simp: map_add_restrict_dom_exact dest!: sep_conjD spec)
next
  from sc de show "s |` (UNIV - dom_eps Q) \<bottom> s |` dom_eps Q"
    by (force simp: map_add_restrict_dom_exact2 map_ac_simps
              dest: map_add_restrict_dom_exact dest!: sep_conjD spec)
next
  show "s = s |` dom_eps Q ++ s |` (UNIV - dom_eps Q)" by simp
qed

lemma sep_conj_forall_simp:
  "dom_exact Q \<Longrightarrow> ((\<lambda>s. \<forall>x. P x s) \<and>\<^sup>* Q) = (\<lambda>s. \<forall>x. (P x \<and>\<^sup>* Q) s)"
  by (fast dest: sep_conj_forall dom_exact_sep_conj_forall)

lemma dom_exact_sep_map:
  "dom_exact (i \<mapsto>\<^sub>g x)"
  by (clarsimp simp: dom_exact_def sep_map_def)

lemma dom_exact_P_emp:
  "\<lbrakk> dom_exact P; P empty; P s \<rbrakk> \<Longrightarrow> s = empty"
  by (auto simp: dom_exact_def)


(* Strictly exact *)

definition
  strictly_exact :: "('a,'b) map_assert \<Rightarrow> bool"
where
  "strictly_exact P \<equiv> \<forall>s s'. P s \<and> P s' \<longrightarrow> s = s'"

lemma strictly_exactD:
  "\<lbrakk> strictly_exact P; P s\<^sub>0; P s\<^sub>1 \<rbrakk> \<Longrightarrow> s\<^sub>0 = s\<^sub>1"
  by (unfold strictly_exact_def, fast)

lemma strictly_exactI:
  "(\<And>s s'. \<lbrakk> P s; P s' \<rbrakk> \<Longrightarrow> s = s') \<Longrightarrow> strictly_exact P"
  by (unfold strictly_exact_def, fast)

lemma strictly_exact_dom_exact:
  "strictly_exact P \<Longrightarrow> dom_exact P"
  by (force simp: strictly_exact_def dom_exact_def)

lemma strictly_exact_sep_emp:
  "strictly_exact \<box>"
  by (force simp: strictly_exact_def dest: sep_empD)

lemma strictly_exact_sep_conj:
  "\<lbrakk> strictly_exact P; strictly_exact Q \<rbrakk> \<Longrightarrow> strictly_exact (P \<and>\<^sup>* Q)"
  by (force intro!: strictly_exactI dest: sep_conjD strictly_exactD)

lemma strictly_exact_conj_impl:
  "\<lbrakk> (Q \<and>\<^sup>* sep_true) s; P s; strictly_exact Q \<rbrakk> \<Longrightarrow> (Q \<and>\<^sup>* (Q \<longrightarrow>\<^sup>* P)) s"
  by (force intro: sep_conjI sep_implI dest: strictly_exactD dest!: sep_conjD)

lemma dom_eps_sep_emp [simp]:
  "dom_eps \<box> = {}"
apply(subst dom_eps [symmetric])
  apply(rule strictly_exact_dom_exact)
  apply(rule strictly_exact_sep_emp)
 apply(rule sep_emp_empty)
apply simp
done

lemma dom_eps_sep_map:
  "g p \<Longrightarrow> dom_eps (p \<mapsto>\<^sub>g (v::'a::mem_type)) = s_footprint p"
apply(subst dom_eps [symmetric])
  apply(rule dom_exact_sep_map)
 apply(rule sep_map_singleton)
 apply(erule ptr_retyp_h_t_valid)
apply(subst singleton_dom)
 apply(erule ptr_retyp_h_t_valid)
apply simp
done

(* Non-empty *)

definition non_empty :: "('a,'b) map_assert \<Rightarrow> bool" where
  "non_empty P \<equiv> \<exists>s. P s"

lemma non_emptyI:
  "P s \<Longrightarrow> non_empty P"
  by (force simp: non_empty_def)

lemma non_emptyD:
  "non_empty P \<Longrightarrow> \<exists>s. P s"
  by (force simp: non_empty_def)

lemma non_empty_sep_true:
  "non_empty sep_true"
  by (simp add: non_empty_def)

lemma non_empty_sep_false:
  "\<not> non_empty sep_false"
  by (simp add: non_empty_def)

lemma non_empty_sep_emp:
  "non_empty \<box>"
apply(unfold non_empty_def)
apply(rule exI, rule sep_emp_empty)
done

lemma non_empty_sep_map:
  "g p \<Longrightarrow> non_empty (p \<mapsto>\<^sub>g (v::'a::mem_type))"
apply(unfold non_empty_def)
apply(rule exI, rule sep_map_singleton)
apply(erule ptr_retyp_h_t_valid)
done

lemma non_empty_sep_conj:
  "\<lbrakk> non_empty P; non_empty Q; dom_exact P; dom_exact Q;
      dom_eps P \<inter> dom_eps Q = {} \<rbrakk> \<Longrightarrow> non_empty (P \<and>\<^sup>* Q)"
apply(clarsimp simp: non_empty_def)
apply(rule_tac x="s++sa" in exI)
apply(rule sep_conjI, assumption+)
 apply(clarsimp simp: map_disj_def dom_eps)
apply(subst map_add_com)
 apply(clarsimp simp: map_disj_def dom_eps)
apply simp
done

lemma non_empty_sep_map':
  "g p \<Longrightarrow> non_empty (p \<hookrightarrow>\<^sub>g (v::'a::mem_type))"
apply(unfold sep_map'_def)
apply(clarsimp simp: non_empty_def sep_conj_ac)
apply(rule_tac x="singleton p v h (ptr_retyp p d)" in exI)
apply(rule_tac s\<^sub>0=empty in sep_conjI)
   apply simp
  apply(rule sep_map_singleton)
  apply(erule ptr_retyp_h_t_valid)
 apply(simp add: map_disj_def)
apply simp
done

lemma non_empty_sep_impl:
  "\<not> P empty \<Longrightarrow> non_empty (P \<longrightarrow>\<^sup>* Q)"
apply(clarsimp simp: non_empty_def)
apply(rule_tac x="\<lambda>s. Some undefined" in exI)
apply(rule sep_implI)
apply(clarsimp simp: map_disj_def)
done

(* Some useful lemmas *)

lemma pure_conj_right: "(Q \<and>\<^sup>* (\<lambda>s. P' \<and> Q' s)) = (\<lambda>s. P' \<and> (Q \<and>\<^sup>* Q') s)"
  by (rule ext, rule, rule, clarsimp dest!: sep_conjD)
     (erule sep_conj_impl, auto)

lemma pure_conj_right': "(Q \<and>\<^sup>* (\<lambda>s. P' s \<and> Q')) = (\<lambda>s. Q' \<and> (Q \<and>\<^sup>* P') s)"
  by (simp add: conj_comms pure_conj_right)

lemma pure_conj_left: "((\<lambda>s. P' \<and> Q' s) \<and>\<^sup>* Q) = (\<lambda>s. P' \<and> (Q' \<and>\<^sup>* Q) s)"
  by (simp add: pure_conj_right sep_conj_ac)

lemma pure_conj_left': "((\<lambda>s. P' s \<and> Q') \<and>\<^sup>* Q) = (\<lambda>s. Q' \<and> (P' \<and>\<^sup>* Q) s)"
  by (subst conj_comms, subst pure_conj_left, simp)

lemmas pure_conj = pure_conj_right pure_conj_right' pure_conj_left
    pure_conj_left'

declare pure_conj [simp add]

lemma sep_conj_sep_conj_sep_impl_sep_conj:
  "(P \<and>\<^sup>* R) s \<Longrightarrow> (P \<and>\<^sup>* (Q \<longrightarrow>\<^sup>* (Q \<and>\<^sup>* R))) s"
  by (erule (1) sep_conj_impl, erule sep_conj_sep_impl, simp add: sep_conj_ac)

lemma sep_map'_conjE1_exc:
  "\<lbrakk> (P \<and>\<^sup>* Q) s; \<And>s. P s \<Longrightarrow> (i \<hookrightarrow>\<^sub>g v) s \<rbrakk> \<Longrightarrow> (i \<hookrightarrow>\<^sub>g v) s"
  by (subst sep_map'_unfold_exc, erule sep_conj_impl, simp+)

lemma sep_map'_conjE2_exc:
  "\<lbrakk> (P \<and>\<^sup>* Q) s; \<And>s. Q s \<Longrightarrow> (i \<hookrightarrow>\<^sub>g v) s \<rbrakk> \<Longrightarrow> (i \<hookrightarrow>\<^sub>g v) s"
  by (subst (asm) sep_conj_com, erule sep_map'_conjE1_exc, simp)

lemma sep_map'_any_conjE1_exc:
  "\<lbrakk> (P \<and>\<^sup>* Q) s; \<And>s. P s \<Longrightarrow> (i \<hookrightarrow>\<^sub>g -) s \<rbrakk> \<Longrightarrow> (i \<hookrightarrow>\<^sub>g -) s"
  by (subst sep_map'_any_unfold_exc, erule sep_conj_impl, simp+)

lemma sep_map'_any_conjE2_exc:
  "\<lbrakk> (P \<and>\<^sup>* Q) s; \<And>s. Q s \<Longrightarrow> (i \<hookrightarrow>\<^sub>g -) s \<rbrakk> \<Longrightarrow> (i \<hookrightarrow>\<^sub>g -) s"
  by (subst (asm) sep_conj_com, erule sep_map'_any_conjE1_exc, simp)

lemma sep_conj_mapD_exc:
  "((i \<mapsto>\<^sub>g v) \<and>\<^sup>* P) s \<Longrightarrow> (i \<hookrightarrow>\<^sub>g v) s \<and> ((i \<mapsto>\<^sub>g -) \<and>\<^sup>* P) s"
  by (force simp: sep_conj_ac intro: sep_conj_impl sep_map'_conjE2_exc)

lemma sep_impl_conj_sameD:
  "\<lbrakk> (P \<longrightarrow>\<^sup>* P \<and>\<^sup>* Q) s; dom_exact P; non_empty P; dom s \<subseteq> UNIV - dom_eps P \<rbrakk>
      \<Longrightarrow> Q s"
apply(drule sep_implD)
apply(clarsimp simp: non_empty_def)
apply(drule_tac x=sa in spec)
apply(erule impE)
 apply(clarsimp simp: map_disj_def dom_eps)
 apply fast
apply(drule sep_conjD, clarsimp)
apply(clarsimp simp: map_disj_def)
apply(subst (asm) map_add_comm)
 apply(clarsimp simp: dom_eps)
 apply fast
apply(subst (asm) map_add_comm[of s\<^sub>1])
 apply fast
apply(drule map_disj_add_eq_dom_right_eq)
   apply(simp add: dom_eps)
  apply(clarsimp simp: dom_eps map_disj_def)
  apply fast
 apply(simp add: map_disj_def)
apply clarsimp
done

lemma sep_impl_conj_sameI:
  "Q s \<Longrightarrow>  (P \<longrightarrow>\<^sup>* P \<and>\<^sup>* Q) s "
apply(rule sep_implI, clarsimp)
apply(rule sep_conjI, assumption+)
 apply(simp add: map_disj_com)
apply simp
done

end
