(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Sep_Forward
imports
  Extended_Separation_Algebra
  Sep_Util
begin

lemma sep_conj_sep_impl_spec:
  "\<lbrakk>((Q -* R) \<and>* P) h; \<And>h. (Q -* R) h \<Longrightarrow> (P \<longrightarrow>* R') h\<rbrakk> \<Longrightarrow> R' h"
  by (metis (full_types) sep_conj_sep_impl2)


method sep_invert = ((erule sep_septraction_snake | sep_erule (direct) sep_conj_sep_impl_spec),
                      sep_flatten?; sep_invert?)

lemma sep_conj_coimpl_cancel: "(P \<and>* R) s \<Longrightarrow> (\<And>s. Q s \<Longrightarrow> P s) \<Longrightarrow> precise P \<Longrightarrow>
                               (\<And>s. R s \<Longrightarrow> R' s) \<Longrightarrow> (Q \<leadsto>* R') s"
  apply (clarsimp simp: sep_conj_def sep_coimpl_def pred_neg_def)
  apply (clarsimp simp: precise_def)
  apply (erule_tac x=s in allE)
  apply (erule_tac x=x in allE)
  apply (erule_tac x=xa in allE)
  apply (clarsimp, drule mp)
   apply (intro conjI)
    apply (fastforce simp: sep_substate_def)
   apply (fastforce simp: sep_substate_def)
  apply (clarsimp)
  by (metis sep_add_cancelD sep_add_commute sep_disj_commuteI)

lemma sep_conj_coimpl_cancel': "(P \<and>* R) s \<Longrightarrow> (\<And>s. P s \<Longrightarrow> Q s) \<Longrightarrow> precise Q \<Longrightarrow>
                               (\<And>s. R s \<Longrightarrow> R' s) \<Longrightarrow> (Q \<leadsto>* R') s"
  apply (clarsimp simp: sep_conj_def sep_coimpl_def pred_neg_def)
  apply (clarsimp simp: precise_def)
  apply (erule_tac x=s in allE)
  apply (erule_tac x=x in allE)
  apply (erule_tac x=xa in allE)
  apply (clarsimp, drule mp)
   apply (intro conjI)
    apply (fastforce simp: sep_substate_def)
   apply (fastforce simp: sep_substate_def)
  apply (clarsimp)
  by (metis sep_add_cancelD sep_add_commute sep_disj_commuteI)

lemma sep_conj_coimpl_cancel'':
  "(\<And>s. pred_imp P Q s) \<Longrightarrow> (P \<and>* R) s \<Longrightarrow>  precise Q \<Longrightarrow>
   (\<And>s. R s \<Longrightarrow> R' s) \<Longrightarrow> (Q \<leadsto>* R') s"
  by (simp add: sep_conj_coimpl_cancel')

lemma sep_conj_coimpl_cancel''':
  "(\<And>s. pred_imp Q P s) \<Longrightarrow> (P \<and>* R) s  \<Longrightarrow> precise P \<Longrightarrow>
   (\<And>s. R s \<Longrightarrow> R' s) \<Longrightarrow> (Q \<leadsto>* R') s"
  by (simp add: sep_conj_coimpl_cancel)

lemma sep_coimpl_cancel':
  "(\<And>s. pred_imp Q P s) \<Longrightarrow> (P \<leadsto>* R) s   \<Longrightarrow>
   (\<And>s. R s \<Longrightarrow> R' s) \<Longrightarrow> (Q \<leadsto>* R') s"
  by (metis sep_coimpl_weaken sep_snake_septraction septraction_snake_trivial)


definition "pointer P \<equiv> (\<forall>x y. \<forall>s R. (P x \<and>* R) s \<longrightarrow> (P y \<leadsto>* R and (\<lambda>s. x = y)) s)"

lemma sep_conj_pointer_coimpl_cancel:
  "(P x \<and>* R) s  \<Longrightarrow> pointer P \<Longrightarrow>
   (\<And>s. R s \<Longrightarrow> y = x \<Longrightarrow>  R'  s) \<Longrightarrow> (P y \<leadsto>* R') s"
  apply (clarsimp simp: pointer_def)
  apply (erule_tac x=x in allE)
  apply (erule_tac x=y in allE)
  apply (erule_tac x=s in allE)
  apply (erule_tac x=R in allE)
  apply (clarsimp simp: pred_conj_def)
  apply (erule sep_coimpl_cancel'[rotated]; simp)
  done

named_theorems precise

method septract_cancel declares precise =
   ((sep_erule (direct) sep_cancel[simplified atomize_imp, THEN sep_conj_coimpl_cancel''], rule precise) |
   (sep_erule (direct) sep_cancel[simplified atomize_imp, THEN sep_conj_coimpl_cancel'''], rule precise) |
    erule sep_cancel[simplified atomize_imp, THEN sep_coimpl_cancel'] |
    (sep_erule (direct) sep_conj_pointer_coimpl_cancel , rule precise))

method abs_used for P = (match (P) in "\<lambda>s. ?P" \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow> \<open>-\<close>)

method sep_lift = match conclusion in "(_ \<longrightarrow>* _) s" for s :: "_ :: sep_algebra" \<Rightarrow>
                  \<open>((match premises in I[thin]: "P s" for P \<Rightarrow>
                      \<open>abs_used P,  rule sep_curry[where h=s and P=P, rotated, OF I]\<close>))\<close>

method sep_snake_uncurry = match conclusion in "(_ \<leadsto>* _) s" for s :: "_ :: sep_algebra" \<Rightarrow>
                  \<open>((match premises in I[thin]: "P s" for P \<Rightarrow>
                      \<open>abs_used P, rule sep_snake_septraction[where s=s and Q=P, OF I]\<close>))\<close>

lemma septract_impl_cancel: "(P -* Q) s  \<Longrightarrow> (\<And>s. Q s \<Longrightarrow> Q' s) \<Longrightarrow> strictly_exact P \<Longrightarrow> (P \<longrightarrow>* Q') s"
  apply (clarsimp simp: septraction_def sep_impl_def pred_neg_def strictly_exact_def)
  by (fastforce)

method sep_forward = (sep_cancel | septract_cancel |  sep_lift |
                              sep_snake_uncurry )

method sep_forward_solve = (solves \<open>sep_invert; (sep_forward) +\<close>)

method sep_cancel uses add = (Sep_Cancel.sep_cancel add: add | sep_lift)

lemma septract_mp: "\<lbrakk>(R' \<and>* (R' -* R)) s; \<And>s. R s \<Longrightarrow> (R' \<and>* (R' \<longrightarrow>* R)) s; precise R'\<rbrakk> \<Longrightarrow> R s"
  apply (sep_invert)
  apply (atomize, erule allE, drule (1) mp)
  using precise_conj_coimpl by blast

end