(*
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory ModifiesProofs
imports CLanguage
begin

(* Rules for breaking down modifies goals before feeding them to the VCG.
   Helps avoid some pathological performance issues. *)

definition
  modifies_inv_refl :: "('a \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "modifies_inv_refl P \<equiv> \<forall>x. x \<in> P x"

definition
  modifies_inv_incl :: "('a \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "modifies_inv_incl P \<equiv> \<forall>x y. y \<in> P x \<longrightarrow> P y \<subseteq> P x"

definition
  modifies_inv_prop :: "('a \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "modifies_inv_prop P \<equiv> modifies_inv_refl P \<and> modifies_inv_incl P"

lemma modifies_inv_prop:
  "modifies_inv_refl P \<Longrightarrow> modifies_inv_incl P \<Longrightarrow> modifies_inv_prop P"
  by (simp add: modifies_inv_prop_def)

named_theorems modifies_inv_intros

context
  fixes P :: "'a \<Rightarrow> 'a set"
  assumes p: "modifies_inv_prop P"
begin

private lemmas modifies_inv_prop' =
  p[unfolded modifies_inv_prop_def modifies_inv_refl_def modifies_inv_incl_def]

private lemma modifies_inv_prop_lift:
  assumes c: "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> (P \<sigma>) c (P \<sigma>),(P \<sigma>)"
  using modifies_inv_prop' by (fastforce intro: c hoarep.Conseq)

private lemma modifies_inv_prop_lower:
  assumes c: "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> (P \<sigma>) c (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c (P \<sigma>),(P \<sigma>)"
  using modifies_inv_prop' by (fastforce intro: c hoarep.Conseq)

private lemma modifies_inv_Seq [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c1 (P \<sigma>),(P \<sigma>)" "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c2 (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c1 ;; c2 (P \<sigma>),(P \<sigma>)"
  by (intro modifies_inv_prop_lower HoarePartial.Seq[OF c[THEN modifies_inv_prop_lift]])

private lemma modifies_inv_Cond [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c1 (P \<sigma>),(P \<sigma>)" "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c2 (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Cond b c1 c2 (P \<sigma>),(P \<sigma>)"
  by (auto intro: HoarePartial.Cond c)

private lemma modifies_inv_Guard_strip [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} c (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Guard f b c (P \<sigma>),(P \<sigma>)"
  by (rule HoarePartial.GuardStrip[OF subset_refl c UNIV_I])

private lemma modifies_inv_Skip [modifies_inv_intros]:
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} SKIP (P \<sigma>),(P \<sigma>)"
  using modifies_inv_prop' by (auto intro: modifies_inv_prop_lift HoarePartial.Skip)

private lemma modifies_inv_Skip' [modifies_inv_intros]:
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} SKIP (P \<sigma>)"
  using modifies_inv_prop' by (auto intro: modifies_inv_prop_lift HoarePartial.Skip)

private lemma modifies_inv_whileAnno [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} whileAnno b I V c (P \<sigma>),(P \<sigma>)"
  apply (rule HoarePartial.reannotateWhileNoGuard[where I="P \<sigma>"])
  by (intro HoarePartial.While hoarep.Conseq;
      fastforce simp: modifies_inv_prop' intro: modifies_inv_prop_lift c)

private lemma modifies_inv_While [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} While b c (P \<sigma>),(P \<sigma>)"
  by (intro modifies_inv_whileAnno[unfolded whileAnno_def] c)

private lemma modifies_inv_Throw [modifies_inv_intros]:
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} THROW (P \<sigma>),(P \<sigma>)"
  using modifies_inv_prop' by (auto intro: modifies_inv_prop_lift HoarePartial.Throw)

private lemma modifies_inv_Catch [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c1 (P \<sigma>),(P \<sigma>)"
             "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c2 (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} TRY c1 CATCH c2 END (P \<sigma>),(P \<sigma>)"
  by (intro modifies_inv_prop_lower HoarePartial.Catch[OF c[THEN modifies_inv_prop_lift]])

private lemma modifies_inv_Catch_all [modifies_inv_intros]:
  assumes 1: "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c1 (P \<sigma>),(P \<sigma>)"
  assumes 2: "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c2 (P \<sigma>)"
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} TRY c1 CATCH c2 END (P \<sigma>)"
  apply (intro HoarePartial.Catch[OF 1] hoarep.Conseq, clarsimp)
  apply (metis modifies_inv_prop' 2 singletonI)
  done

private lemma modifies_inv_switch_Nil [modifies_inv_intros]:
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} switch v [] (P \<sigma>),(P \<sigma>)"
  by (auto intro: modifies_inv_Skip)

private lemma modifies_inv_switch_Cons [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c (P \<sigma>),(P \<sigma>)"
             "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} switch p vcs (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} switch p ((v,c) # vcs) (P \<sigma>),(P \<sigma>)"
  by (auto intro: c modifies_inv_Cond)

end

context
  fixes P :: "('c, 'd) state_scheme \<Rightarrow> ('c, 'd) state_scheme set"
  assumes p: "modifies_inv_prop P"
begin

private lemma modifies_inv_creturn [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Basic (\<lambda>s. xfu (\<lambda>_. v s) s) (P \<sigma>),(P \<sigma>)"
             "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Basic (rtu (\<lambda>_. Return)) (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} creturn rtu xfu v (P \<sigma>),(P \<sigma>)"
  unfolding creturn_def by (intro p c modifies_inv_intros)

private lemma modifies_inv_creturn_void [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Basic (rtu (\<lambda>_. Return)) (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} creturn_void rtu (P \<sigma>),(P \<sigma>)"
  unfolding creturn_void_def by (intro p c modifies_inv_intros)

private lemma modifies_inv_cbreak [modifies_inv_intros]:
  assumes c: "\<And>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Basic (rtu (\<lambda>_. Break)) (P \<sigma>),(P \<sigma>)"
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} cbreak rtu (P \<sigma>),(P \<sigma>)"
  unfolding cbreak_def by (intro p c modifies_inv_intros)

private lemma modifies_inv_ccatchbrk [modifies_inv_intros]:
  shows "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} ccatchbrk rt (P \<sigma>),(P \<sigma>)"
  unfolding ccatchbrk_def by (intro p modifies_inv_intros)

end

end
