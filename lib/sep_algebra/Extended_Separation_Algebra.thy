(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
  Adds positivity law to separation algebra, as well as defining
  the septraction and sep-coimplication operators, providing lemmas
  for each.
*)

theory Extended_Separation_Algebra
imports
  Lib.Lib
  "Sep_Tactics"
begin

no_notation pred_and (infixr "and" 35)
no_notation pred_or (infixr "or" 30)
no_notation pred_not ("not _" [40] 40)
no_notation pred_imp (infixr "imp" 25)

lemma sep_conj_exists_left[simp]: "((\<lambda>s. \<exists>x. (P x) s) \<and>* R) \<equiv> (EXS x. (P x \<and>* R)) "
  apply (rule eq_reflection)
  by (clarsimp simp: sep_conj_def, fastforce)

instantiation "bool" :: stronger_sep_algebra
begin
 definition "zero_bool \<equiv> True"
 definition "plus_bool \<equiv> \<lambda>(x :: bool) (y :: bool). x \<and> y"
 definition "sep_disj_bool \<equiv> \<lambda>(x :: bool) (y :: bool). x \<or> y"
instance
  by (intro_classes; fastforce simp: zero_bool_def plus_bool_def sep_disj_bool_def)
end

instantiation "prod" :: (stronger_sep_algebra, stronger_sep_algebra) stronger_sep_algebra
begin
definition "zero_prod \<equiv> (0,0)"
definition "plus_prod p p' \<equiv> (fst p + fst p', snd p + snd p')"
definition "sep_disj_prod p p' \<equiv> fst p ## fst p' \<and> snd p ## snd p'"
instance
  apply (intro_classes; simp add: zero_prod_def plus_prod_def sep_disj_prod_def)
     apply (simp add: sep_add_assoc | fastforce simp: sep_disj_commute sep_add_commute)+
  done
end


instantiation "fun" :: (type, pre_sep_algebra) pre_sep_algebra
begin
definition "zero_fun = (\<lambda>x. 0)"
definition "plus_fun f f'  \<equiv> (\<lambda>x. (f x) + (f' x) )"
definition "sep_disj_fun   \<equiv> (\<lambda>f f'.  \<forall>x. f x ## f' x ) :: ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool "
instance
  apply (intro_classes)
      apply (clarsimp simp:  comp_def sep_disj_fun_def )
      apply (clarsimp simp: zero_fun_def sep_disj_fun_def plus_fun_def )
     apply (clarsimp simp: zero_fun_def comp_def sep_disj_fun_def plus_fun_def )
     apply (simp add: sep_disj_commute)
    apply (clarsimp simp: zero_fun_def sep_disj_commuteI sep_disj_fun_def plus_fun_def)
   apply (clarsimp simp: zero_fun_def sep_disj_commuteI sep_disj_fun_def plus_fun_def sep_add_commute)
  apply (clarsimp simp: zero_fun_def sep_disj_commuteI sep_disj_fun_def plus_fun_def sep_add_commute sep_add_assoc)
  done
end

instantiation "fun" :: (type, sep_algebra) sep_algebra
begin

instance
  apply (intro_classes)
   apply (clarsimp simp: zero_fun_def sep_disj_fun_def plus_fun_def )
  using sep_disj_addD apply blast
  apply (clarsimp simp: zero_fun_def comp_def sep_disj_fun_def plus_fun_def )
  by (simp add: sep_disj_addI1)
end

instantiation option :: (type) sep_algebra begin
definition "sep_disj_option (h :: 'a option) (h' :: 'a option) =
             (case h of (Some x) \<Rightarrow> h' = None | _ \<Rightarrow> h = None)"
definition "plus_option (h :: 'a option) (h' :: 'a option) =
           (case h of (Some x) \<Rightarrow> h | _ \<Rightarrow> h')"
definition "zero_option = None"
instance
  apply (intro_classes)
        by (clarsimp simp: sep_disj_option_def zero_option_def plus_option_def split: option.splits)+
end

instantiation option :: (type) cancellative_sep_algebra begin
instance
  apply (intro_classes)
    apply (simp add: option.case_eq_if plus_option_def sep_disj_option_def)
   apply (clarsimp simp: zero_option_def option.case_eq_if plus_option_def sep_disj_option_def split: if_split_asm  option.splits)
   apply (clarsimp simp: zero_option_def option.case_eq_if plus_option_def sep_disj_option_def split: if_split_asm option.splits)
  done
end


instantiation "fun" :: (type, cancellative_sep_algebra) cancellative_sep_algebra begin
instance
  apply (intro_classes)
    apply (clarsimp simp: plus_fun_def sep_disj_fun_def zero_fun_def)
    apply (safe; fastforce)
   apply (clarsimp simp: plus_fun_def sep_disj_fun_def zero_fun_def)
    apply (rule ext)
    apply (meson sep_disj_positive)
   apply (rule ext)
  apply (clarsimp simp: plus_fun_def sep_disj_fun_def zero_fun_def)
  by (meson sep_add_cancel)
end


lemma sep_substate_antisym:
  "x \<preceq> y \<Longrightarrow> y \<preceq> x \<Longrightarrow> x = (y :: 'a ::cancellative_sep_algebra)"
  apply (clarsimp simp: sep_substate_def)
  apply (rename_tac h' h)
  apply (subgoal_tac "h' = 0")
   apply (clarsimp)
  apply (drule_tac trans[where s=x and t="x+0"])
   apply (clarsimp)
  apply (subgoal_tac "(x + h' + h = x + 0) \<longrightarrow> ((0 + x) = (h' + h) + x)")
   apply (drule mp, clarsimp)
   apply (metis sep_add_cancelD sep_add_disj_eq sep_disj_commuteI sep_disj_positive_zero sep_disj_zero)
  by (metis sep_add_assoc sep_add_commute sep_add_zero sep_add_zero_sym sep_disj_commuteI)

context sep_algebra begin

definition
  septraction :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infix "-*" 25)
where
  "septraction P Q = (not (P \<longrightarrow>* not Q))"


lemma septraction_impl1:
  "(P -* Q) s \<Longrightarrow> (\<And>s. P s \<Longrightarrow> P' s) \<Longrightarrow> (P' -* Q) s "
  apply (clarsimp simp: septraction_def pred_neg_def)
  using sep_impl_def by auto

lemma septraction_impl2:
  "(P -* Q) s \<Longrightarrow> (\<And>s. Q s \<Longrightarrow> Q' s) \<Longrightarrow> (P -* Q') s "
  apply (clarsimp simp: septraction_def pred_neg_def)
  using sep_impl_def by auto

definition
  sep_coimpl :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infix "\<leadsto>*" 24)
where
  "sep_coimpl P Q \<equiv> \<lambda>s. \<not> (P \<and>* not Q) s"

lemma sep_septraction_snake:
  "(P -* Q) s \<Longrightarrow> (\<And>s. Q s \<Longrightarrow> (P \<leadsto>* Q') s) \<Longrightarrow>  Q' s"
  apply (clarsimp simp: sep_coimpl_def septraction_def pred_neg_def sep_conj_def sep_impl_def)
  using sep_add_commute sep_disj_commute by auto

lemma sep_snake_septraction:
  "Q s \<Longrightarrow> (\<And>s. (P -* Q) s \<Longrightarrow> Q' s) \<Longrightarrow> (P \<leadsto>* Q') s  "
  apply (clarsimp simp: sep_coimpl_def septraction_def pred_neg_def sep_conj_def sep_impl_def)
  using sep_add_commute sep_disj_commute by fastforce

lemma septraction_snake_trivial:
  "(P -* (P \<leadsto>* R)) s \<Longrightarrow> R s" by (erule sep_septraction_snake)

end


lemma sep_impl_impl:
  "(P \<longrightarrow>* Q) s\<Longrightarrow> (\<And>s. Q s \<Longrightarrow> Q' s) \<Longrightarrow> (P \<longrightarrow>* Q') s"
  by (metis sep_implD sep_implI)

lemma disjointness_equiv:
  "(\<forall>P (s :: 'a :: sep_algebra). strictly_exact P \<longrightarrow> \<not>P 0 \<longrightarrow> (P \<leadsto>* (P \<leadsto>* sep_false)) s) =
   (\<forall>h :: 'a. h ## h \<longrightarrow> h = 0)"
  apply (rule iffI)
   apply (clarsimp)
   apply (erule_tac x="(=) h" in allE)
   apply (drule mp)
    apply (clarsimp simp: strictly_exact_def)
   apply (rule ccontr)
   apply (drule mp)
    apply (clarsimp)
   apply (erule_tac x="h + h" in allE)
   apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def)
   apply (erule_tac x=h in allE, clarsimp)
   apply (erule_tac x=0 in allE, clarsimp)
  apply (clarsimp)
  apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def strictly_exact_def)
  apply (erule_tac x=x in allE, erule_tac x=xa in allE, clarsimp simp: sep_empty_def)
  apply (erule_tac x=x in allE, clarsimp)
  using sep_disj_addD1 by blast


definition
  sep_min :: "(('a :: sep_algebra) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where
  "sep_min P \<equiv> P and (P \<leadsto>* \<box>)"

definition
  sep_subtract :: "(('a :: sep_algebra) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where
  "sep_subtract P Q \<equiv> P and (Q \<leadsto>* \<box>)"

lemma sep_min_subtract_subtract:
  "sep_min P = sep_subtract P P"
  apply (clarsimp simp: sep_subtract_def sep_min_def)
  done

lemma sep_subtract_distrib_disj:
  "sep_subtract (P or Q) R = ((sep_subtract P R) or (sep_subtract Q R))"
  apply (rule ext, rule iffI)
   apply (clarsimp simp: pred_disj_def pred_conj_def sep_subtract_def)
  apply (clarsimp simp: pred_disj_def pred_conj_def sep_subtract_def)
  apply (safe)
  done

lemma sep_snake_sep_impl:
  "(P \<longrightarrow>* R) s \<Longrightarrow> (\<And> s. R s \<Longrightarrow> (P \<leadsto>* sep_false) s) \<Longrightarrow> (not P \<and>* (not (P -* R))) s"
  apply (drule sep_impl_impl[where Q'="(P \<leadsto>* sep_false)"])
   apply (atomize)
   apply (erule allE, drule mp, assumption)
   apply (assumption)
  apply (erule contrapos_pp)
  apply (clarsimp simp: sep_impl_def sep_coimpl_def sep_conj_def pred_neg_def septraction_def)
  apply (erule_tac x=0 in allE)
  apply (erule_tac x=s in allE)
  apply (clarsimp)
  apply (rule_tac x=0 in exI)
  apply (clarsimp)
  by (metis (full_types) disjoint_zero_sym sep_add_commute sep_add_zero_sym sep_disj_commuteI)

lemma sep_snake_mp:
  "(P \<leadsto>* Q) s \<Longrightarrow> (P \<and>* sep_true) s \<Longrightarrow>  (P \<and>* Q) s  "
  apply (clarsimp simp: sep_coimpl_def)
  apply (clarsimp simp: sep_conj_def sep_coimpl_def pred_neg_def)
  apply (fastforce)
  done

lemma sep_coimpl_contrapos:
  "(P \<leadsto>* Q) = ((not Q) \<leadsto>* (not P))"
  by (rule ext, rule iffI; simp add: sep_coimpl_def pred_neg_def sep_conj_commute)

lemma sep_coimpl_def':
  "(\<not> (P \<and>* Q) s) = ((P \<leadsto>* (not Q)) s)"
  by (simp add: pred_neg_def sep_coimpl_def)

lemma rewrite_sp:
  "(\<forall>R s. (P \<leadsto>* R) s \<longrightarrow> (Q \<and>* R) (f s))  \<longleftrightarrow> (\<forall>R s. R s \<longrightarrow> (Q \<and>* (P -* R)) (f s) )"
  apply (rule iffI)
   apply (clarsimp)
   apply (erule_tac x="P -* R" in allE)
   apply (erule_tac x=s in allE)
   apply (drule mp)
    apply (erule (1) sep_snake_septraction)
   apply (assumption)
  apply (clarsimp)
  apply (erule_tac x="P \<leadsto>* R" in allE)
  apply (erule_tac x=s in allE)
  apply (clarsimp)
  apply (sep_cancel)
  apply (erule (1) sep_septraction_snake)
  done

lemma sep_coimpl_weaken:
  "(P \<leadsto>* Q) s \<Longrightarrow> (\<And>s. P' s \<Longrightarrow> P s) \<Longrightarrow> (P' \<leadsto>* Q) s"
  apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def)
  apply (fastforce)
  done

lemma sep_curry':
  "R s \<Longrightarrow> (P \<longrightarrow>* (P \<and>* R)) s"
  by (simp add: sep_wand_trivial)

lemma sep_coimpl_mp_gen:
  "(P \<and>* Q) s \<Longrightarrow> (P' \<leadsto>* Q') s \<Longrightarrow> (\<And>s. P s \<Longrightarrow> P' s) \<Longrightarrow> ((P and P') \<and>* (Q and Q')) s"
  apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_conj_def pred_neg_def)
  by (fastforce simp: sep_disj_commute sep_add_commute)

lemma ex_pull:
  "\<exists>h s. P h s \<and> Q h \<Longrightarrow> \<exists>h. Q h \<and> (\<exists>s. P h s)"
  apply (fastforce)
  done

lemma sep_mp_snake_mp:
  "(P \<and>* (P \<longrightarrow>* (P \<leadsto>* Q))) s \<Longrightarrow> (P \<and>* Q) s"
  apply (clarsimp simp: sep_conj_def)
  apply (rename_tac x y)
  apply (rule_tac x=x in exI)
  apply (rule_tac x=y in exI)
  apply (clarsimp)
  apply (clarsimp simp: sep_impl_def)
  apply (erule_tac x=x in allE)
  apply (clarsimp simp: sep_disj_commute)
  apply (clarsimp simp: sep_conj_def sep_coimpl_def pred_neg_def)
  by (fastforce simp: sep_disj_commute sep_add_commute)

lemma septract_cancel:
  "(P -* Q) s \<Longrightarrow> (\<And>s. P s \<Longrightarrow> P' s) \<Longrightarrow> (\<And>s. Q s \<Longrightarrow> Q' s) \<Longrightarrow> (P' -* Q') s"
  apply (clarsimp simp: septraction_def sep_impl_def pred_neg_def)
  apply (fastforce)
  done

lemma sep_coimpl_mp_zero:
  "(P \<leadsto>* Q) s \<Longrightarrow> P s   \<Longrightarrow> Q (0)"
  by (clarsimp simp: sep_coimpl_def sep_conj_def)

lemma sep_neg_not:
  "(P \<leadsto>* sep_false) s \<Longrightarrow> \<not>P s"
  apply (cases "P s")
   apply (drule(1) sep_coimpl_mp_zero)
   apply (clarsimp)
  apply (simp)
  done

lemma sep_antimp':
  "P s \<Longrightarrow> (Q \<leadsto>* (Q -* P)) s \<and> P s"
  apply (clarsimp)
  apply (erule sep_snake_septraction, assumption)
  done

definition
  sep_precise_conj :: "(('a :: sep_algebra) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where
  "sep_precise_conj P \<equiv> P and (ALLS R. (sep_true \<longrightarrow>* (P \<leadsto>* R)))"

notation sep_precise_conj (infix "\<and>@" 50)

definition
  coprecise ::  "(('a :: sep_algebra) \<Rightarrow> bool) \<Rightarrow>  bool" where
  "coprecise P = (\<forall>s h h'. P h \<longrightarrow> P h' \<longrightarrow> s \<preceq> h \<longrightarrow> s \<preceq> h' \<longrightarrow> s \<noteq> 0 \<longrightarrow> h = h')"

definition
  cointuitionistic :: "(('a :: sep_algebra) \<Rightarrow> bool) \<Rightarrow> bool" where
  "cointuitionistic P = (\<forall>h h'. P h \<and> h' \<preceq> h \<longrightarrow> P h')"

lemma intuitionistic_def':
  "intuitionistic P = (\<forall>s R. (P \<and>* R) s \<longrightarrow> P s)"
  apply (rule iffI)
   apply (clarsimp simp: intuitionistic_def)
   apply (clarsimp simp: sep_conj_def)
  using sep_substate_disj_add apply blast
  apply (clarsimp simp: intuitionistic_def)
  apply (erule_tac x=h' in allE)
  apply (drule mp)
   apply (rule_tac x=sep_true in exI)
   apply (clarsimp simp:sep_conj_def sep_substate_def, fastforce)
  apply (assumption)
  done

lemma cointuitionistic_def':
  "cointuitionistic P = (\<forall>s R. P s \<longrightarrow> (R \<leadsto>* P) s)"
  apply (rule iffI)
   apply (clarsimp)
   apply (clarsimp simp: sep_coimpl_def)
   apply (clarsimp simp: sep_conj_def pred_neg_def cointuitionistic_def)
   apply (rename_tac R x y)
   apply (erule_tac x="x + y" in allE)
   apply (erule_tac x=y in allE)
   apply (clarsimp)
  using sep_disj_commuteI sep_substate_disj_add' apply blast
  apply (clarsimp simp: cointuitionistic_def)
  apply (erule_tac x=h in allE)
  apply (clarsimp)
  apply (clarsimp simp: sep_substate_def)
  apply (erule_tac x="\<lambda>s. s = z" in allE)
  apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def)
  apply (fastforce simp: sep_disj_commute sep_add_commute)
  done

lemma saturated_split:
  "cointuitionistic P \<Longrightarrow> P s \<Longrightarrow> (Q \<and>* R) s \<Longrightarrow> ((P and Q) \<and>* (P and R)) s"
  apply (clarsimp simp: cointuitionistic_def sep_conj_def pred_conj_def)
  apply (rule_tac x=x in exI)
  apply (rule_tac x=y in exI)
  apply (clarsimp)
  using sep_disj_commuteI sep_substate_disj_add sep_substate_disj_add' by blast

lemma sep_wand_dne:
  "((P \<longrightarrow>* sep_false) \<longrightarrow>* sep_false) s \<Longrightarrow> \<exists>s. P s"
  apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def sep_conj_def sep_coimpl_def)
  apply (erule_tac x=0 in allE)
  apply (clarsimp)
  done

lemma sep_snake_dne:
  "(sep_true \<leadsto>* P) s \<Longrightarrow> ((P \<leadsto>* sep_false) \<leadsto>* sep_false) s"
  apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def sep_conj_def sep_coimpl_def)
  apply (rename_tac x y)
  apply (erule_tac x=y in allE)
  apply (erule_tac x=x in allE)
  apply (rule_tac x=x in exI)
  apply (rule_tac x=0 in exI)
  apply (clarsimp)
  apply (fastforce simp: sep_disj_commute sep_add_commute)
  done

lemma strictly_exactI:
  "(\<And>P s. ((P -* R) -* R) s \<Longrightarrow> P (s :: 'a :: cancellative_sep_algebra)) \<Longrightarrow> strictly_exact R"
  apply (atomize)
  apply (clarsimp simp: strictly_exact_def)
  apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def sep_conj_def sep_coimpl_def strictly_exact_def)
  apply (rename_tac h h')
  apply (erule_tac x="\<lambda>s. s = h" in allE)
  by (metis disjoint_zero_sym sep_add_commute sep_add_zero sep_disj_zero)

lemma strictly_exact_septractD:
  "strictly_exact R \<Longrightarrow> ((P -* R) -* R) s \<Longrightarrow> P (s :: 'a :: cancellative_sep_algebra)"
  apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def sep_conj_def sep_coimpl_def
                        strictly_exact_def)
  by (metis sep_add_cancel sep_add_commute sep_disj_commuteI)

lemma strictly_exact_def':
  "(\<forall>P s. ((P -* R) -* R) s \<longrightarrow> P (s :: 'a :: cancellative_sep_algebra)) = strictly_exact R"
  using strictly_exactI strictly_exact_septractD by auto

lemma copreciseI:
  "(\<forall>(s ) R. (P -* R) s \<longrightarrow> (P \<longrightarrow>* R) s) \<Longrightarrow> coprecise P"
  apply (clarsimp simp: coprecise_def)
  apply (clarsimp simp: sep_substate_def)
  apply (erule_tac x="0" in allE)
  apply (rename_tac s h h')
  apply (erule_tac x="\<lambda>s'. s' = s + h" in allE)
  apply (drule mp)
   apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def)
  apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def)
  done

lemma sep_implI':
  "strictly_exact P \<Longrightarrow> (P -* R) s \<Longrightarrow> (P \<longrightarrow>* R) s"
  apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def coprecise_def strictly_exact_def)
  apply (fastforce)
  done

lemma
  "\<forall>s P. (P -* R) s \<longrightarrow> (P \<longrightarrow>* R) s \<Longrightarrow> \<exists>s. R s \<Longrightarrow> R s"
  apply (clarsimp simp: coprecise_def)
  apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def)
  by (metis disjoint_zero_sym sep_add_zero_sym)

lemma strictly_exactI':
  "\<forall>s R. (P -* R) s \<longrightarrow> (P \<longrightarrow>* R) s \<Longrightarrow> strictly_exact P"
  apply (clarsimp simp: strictly_exact_def)
  apply (erule_tac x="0" in allE)
  apply (rename_tac h h')
  apply (erule_tac x="\<lambda>h. h = h'" in allE)
  apply (drule mp)
   apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def)
  apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def)
  done

lemma strictly_exact_def'':
  "(\<forall>s R. (P -* R) s \<longrightarrow> (P \<longrightarrow>* R) s) = strictly_exact P"
  using sep_implI' strictly_exactI' by blast

lemma conj_coimpl_precise:
  "(\<forall>s R. (P \<and>* R) s \<longrightarrow> (P \<leadsto>* R) s) \<Longrightarrow> precise P"
  apply (clarsimp simp: precise_def)
  apply (clarsimp simp: sep_substate_def)
  apply (rename_tac h h' z z')
  apply (erule_tac x="h + z" in allE)
  apply (erule_tac x="\<lambda>s. s= z" in allE)
  apply (drule mp)
   apply (clarsimp simp: sep_conj_def)
   apply (fastforce)
  apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def)
  using sep_add_cancel by fastforce

lemma precise_conj_coimpl:
  "precise P \<Longrightarrow> (\<forall>s R. (P \<and>* R) s \<longrightarrow> (P \<leadsto>* R) s)"
  apply (clarsimp simp: precise_def)
  apply (clarsimp simp: sep_conj_def sep_coimpl_def pred_neg_def)
  by (metis cancellative_sep_algebra_class.sep_add_cancelD sep_add_commute
             sep_disj_commuteI sep_substate_disj_add)

lemma septract_cancel_eq_precise:
  "(\<forall>s. ((P -* (P \<and>* R)) s \<longrightarrow> R s)) = (\<forall>s. (P \<and>* R) s \<longrightarrow> (P \<leadsto>* R) s)"
  apply (rule iffI)
   apply (clarsimp)
   apply (clarsimp simp: sep_conj_def sep_impl_def septraction_def pred_neg_def sep_coimpl_def)
   apply (rule ccontr)
   apply (rename_tac x y h h')
   apply (erule_tac x=h' in allE)
   apply (clarsimp)
   apply (erule_tac x=h in allE)
   apply (clarsimp simp: sep_disj_commute)
   apply (erule_tac x=x in allE)
   apply (clarsimp)
   apply (erule_tac x=y in allE)
   apply (clarsimp)
   apply (fastforce simp: sep_disj_commute sep_add_commute)
  apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def)
  by (metis pred_neg_def sep_coimpl_def sep_conjI sep_conj_commuteI)

lemma sep_coimpl_cancel:
  "(P \<leadsto>* Q) s \<Longrightarrow> ((P \<and>* Q) s \<Longrightarrow> (P \<leadsto>* Q') s) \<Longrightarrow> (P \<leadsto>* Q') s"
  apply (clarsimp simp: sep_coimpl_def pred_neg_def)
  apply (clarsimp simp: sep_conj_def)
  by blast

lemma sep_cases:
  "R s \<Longrightarrow> (P \<and>* (P -* R)) s \<or> (P \<leadsto>* (sep_false)) s"
  apply (safe)
  apply (clarsimp simp: sep_coimpl_def)
  apply (rule ccontr)
  by (meson sep_antimp' sep_conj_sep_true_right sep_snake_mp)

lemma contra:
  "(\<forall>s. P s \<longrightarrow> Q s) \<Longrightarrow> (\<forall>s. \<not> Q s \<longrightarrow> \<not> P s )"
  apply (safe)
  by (fastforce)

lemma
  "(\<forall>R s. (P \<and>* R) (s) \<longrightarrow> (Q \<and>* R) (f s) ) = (\<forall>R s. (Q \<leadsto>* R) (f s) \<longrightarrow> (P \<leadsto>* R) ( s))"
  apply (clarsimp simp: sep_coimpl_def)
  apply (rule iffI)
   apply (clarsimp)
  apply (clarsimp)
  by (meson sep_coimpl_def sep_coimpl_def')

lemma
  "R s \<Longrightarrow> strictly_exact R \<Longrightarrow> (P \<longrightarrow>* R) s' \<Longrightarrow> (P -* R) s' \<Longrightarrow> s' \<preceq> s \<Longrightarrow> (P \<and>* sep_true) s"
  apply (clarsimp simp: sep_conj_def sep_coimpl_def pred_neg_def septraction_def sep_impl_def)
  by (metis sep_add_commute sep_disj_commuteI strictly_exact_def)

lemma sep_coimpl_comb:
  " (R \<leadsto>* P) s \<Longrightarrow> (R \<leadsto>* Q) s \<Longrightarrow> (R \<leadsto>* (P and Q)) s"
  apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def pred_conj_def)
  done

lemma sep_coimpl_contra:
  "(R \<leadsto>* (not Q)) s \<Longrightarrow> (R \<leadsto>* Q) s \<Longrightarrow> (R \<leadsto>* sep_false) s"
  apply (drule sep_coimpl_comb, assumption)
  apply (clarsimp simp: pred_neg_def pred_conj_def)
  done

lemma sep_comb':
  "((not Q) \<leadsto>* P) s \<Longrightarrow> (Q \<leadsto>* R) s \<Longrightarrow> ((R or P) \<and>* sep_true) s"
  apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def)
  by (metis (full_types) disjoint_zero_sym pred_disj_def sep_add_zero sep_add_zero_sym sep_disj_zero)

lemma sep_coimpl_dne:
  "((R \<leadsto>* sep_false) \<leadsto>* sep_false) s \<Longrightarrow> (R \<and>* sep_true) s"
  by (metis sep_coimpl_def sep_conj_sep_true_right sep_neg_not)

lemma sep_antimp_contrapos:
  " (R) s \<Longrightarrow> ((P \<longrightarrow>* not R) \<leadsto>* (not P)) s "
  by (metis pred_neg_def sep_coimpl_def' sep_mp_gen)

lemma sep_snake_trivial:
  "(sep_true \<leadsto>* Q) s \<Longrightarrow> Q s"
  by (metis pred_neg_def sep_coimpl_def sep_conj_sep_true')

lemma min_predD:
  "(R \<leadsto>* \<box>) s \<Longrightarrow> (R \<and>* sep_true) s  \<Longrightarrow> R s"
  using Sep_Cancel_Set.sep_conj_empty' sep_coimpl_dne sep_snake_mp by blast

lemma septract_sep_wand:
  "(P -* R) s \<Longrightarrow> (P \<longrightarrow>* Q) s \<Longrightarrow> (P -* (Q and R)) s"
  apply (clarsimp simp: sep_impl_def septraction_def pred_neg_def)
  by (fastforce simp: pred_conj_def)

lemma
  "(P -* (P \<and>* R)) s \<Longrightarrow> (P \<longrightarrow>* Q) s \<Longrightarrow> (\<And>s. (Q and (P \<and>* R)) s \<Longrightarrow> (P \<leadsto>* R) s) \<Longrightarrow> R s"
  using sep_septraction_snake septract_sep_wand by blast

lemma sep_elsewhereD:
  "(P -* sep_true) s \<Longrightarrow> (P \<longrightarrow>* (P \<leadsto>* R)) s \<Longrightarrow> R s"
  apply (drule (1) septract_sep_wand, simp add: pred_conj_def)
  using sep_septraction_snake  by blast

lemma sep_conj_coimplI:
  "(Q \<leadsto>* R) s \<Longrightarrow>  ((P \<and>* Q) \<leadsto>* (P -* R)) s  "
  by (metis sep_coimpl_def sep_coimpl_def' sep_conj_commuteI sep_mp_frame septraction_def)

lemma sep_conj_septract_curry:
  "((P \<and>* Q) -* R) s \<Longrightarrow>  (P -* (Q -* R)) s"
  by (smt (verit) sep_antimp' sep_conj_coimplI sep_septraction_snake)

lemma sep_snake_boxI:
  "Q s \<Longrightarrow> (\<box> \<leadsto>* Q) s"
  by (simp add: pred_neg_def sep_coimpl_def)

lemma sep_snake_boxD:
  "(Q \<leadsto>* \<box>) s \<Longrightarrow> ((Q \<leadsto>* sep_false) or Q) s"
  apply (simp only: pred_disj_def)
  apply (safe)
  using Sep_Cancel_Set.sep_conj_empty' sep_coimpl_cancel by blast

lemma septract_wandD:
  "(( R \<longrightarrow>* (not Q)) -* Q) s \<Longrightarrow> (not R) s"
  apply (erule sep_septraction_snake)
  using sep_antimp_contrapos by blast

lemma sep_impl_septractD:
  "(P \<longrightarrow>* Q) s \<Longrightarrow> (R -* (not Q)) s \<Longrightarrow> ((R and not P) -* (not Q)) s"
  apply (clarsimp simp: sep_impl_def pred_neg_def septraction_def)
  apply (erule_tac x=h' in allE)
  apply (clarsimp simp: pred_conj_def)
  apply (fastforce)
  done

lemma sep_neg_impl:
  "(not (R \<longrightarrow>* Q)) = (R -* (not Q)) "
  apply (clarsimp simp: pred_neg_def septraction_def)
  done

lemma
  "P s \<Longrightarrow> (R -* Q) s \<Longrightarrow> ((R and (P -* Q)) -* Q) s"
  apply (clarsimp simp: septraction_def sep_impl_def pred_neg_def pred_conj_def)
  by (fastforce simp: sep_add_commute sep_disj_commute)

lemma sep_coimpl_notempty:
  "(Q \<leadsto>* (not \<box>)) s \<Longrightarrow> (not Q) s"
  apply (clarsimp simp: sep_coimpl_def pred_neg_def)
  done

method sep_subst uses add = (sep_frule (direct) add)

lemma septract_empty_empty:
  "(P -* \<box>) s \<Longrightarrow> \<box> (s :: 'a :: cancellative_sep_algebra)"
  apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def sep_empty_def)
  done

lemma septract_trivial:
  "P s \<Longrightarrow> (sep_true -* P) s"
  apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def sep_empty_def)
  using sep_disj_zero by fastforce

lemma sep_empty_and_conj:
  "\<box> s \<Longrightarrow> (P \<and>* Q) s \<Longrightarrow> P (s :: 'a :: cancellative_sep_algebra)"
  by (metis sep_conj_def sep_disj_positive_zero sep_empty_def)

lemma sep_conj_coimpl_mp:
  "(P \<and>* R) s \<Longrightarrow> (P \<leadsto>* Q) s \<Longrightarrow> (P \<and>* (Q and R)) s"
  apply (drule (2) sep_coimpl_mp_gen, clarsimp simp: pred_conj_def conj_commute)
  done

lemma sep_conj_coimpl_contrapos_mp:
  "(P \<and>* Q) s \<Longrightarrow> (R \<leadsto>* (not Q)) s \<Longrightarrow> (Q \<and>* (P and (not R))) s"
  apply (subst (asm) sep_coimpl_contrapos)
  apply (clarsimp simp: pred_neg_def)
  apply (sep_drule (direct) sep_conj_coimpl_mp[where P=Q], assumption)
  apply (clarsimp simp: pred_conj_def conj_commute)
  done

end