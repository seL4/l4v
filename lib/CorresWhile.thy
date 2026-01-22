(*
 * Copyright 2026, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory CorresWhile
imports ExtraCorres
begin

text \<open>Some @{term corres_underlying} rules for @{term whileLoop}\<close>

lemma in_whileLoop_corres:
  assumes body_corres:
    "\<And>r r'. rrel r r' \<Longrightarrow>
             corres_underlying srel nf nf' rrel (P r and C r) (P' r' and C' r') (B r) (B' r')"
  assumes body_inv:
    "\<And>r. \<lbrace>P r and C r\<rbrace> B r \<lbrace>P\<rbrace>"
    "\<And>r'. \<lbrace>P' r' and C' r'\<rbrace> B' r' \<lbrace>P'\<rbrace>"
  assumes cond: "\<And>r r' s s'. \<lbrakk>rrel r r'; (s, s') \<in> srel; P r s; P' r' s'\<rbrakk> \<Longrightarrow> C r s = C' r' s'"
  assumes result: "(rv', t') \<in> fst (whileLoop C' B' r' s')"
  assumes nf: "\<And>r. nf \<Longrightarrow> no_fail (P r and C r) (B r)"
  shows "\<forall>s r. (s, s') \<in> srel \<and> rrel r r' \<and> P r s \<and> P' r' s'
                \<longrightarrow> (\<exists>rv t. (rv, t) \<in> fst (whileLoop C B r s) \<and> (t, t') \<in> srel \<and> rrel rv rv')"
  apply (rule in_whileLoop_induct[OF result])
   apply (force simp: cond whileLoop_def)
  apply clarsimp
  apply (frule (1) corres_underlyingD2[OF body_corres];
         (fastforce dest: nf simp: cond no_fail_def)?)
  apply clarsimp
  apply (frule use_valid[OF _ body_inv(1)])
   apply (fastforce dest: cond)
  apply (frule use_valid[OF _ body_inv(2)])
   apply fastforce
  apply (fastforce simp: whileLoop_def intro: whileLoop_results.intros(3) dest: cond)
  done

lemma corres_whileLoop_ret:
  assumes cond: "\<And>r r' s s'. \<lbrakk>rrel r r'; (s, s') \<in> srel; P r s; P' r' s'\<rbrakk> \<Longrightarrow> C r s = C' r' s'"
  assumes body_corres:
    "\<And>r r'. rrel r r' \<Longrightarrow>
             corres_underlying srel False nf' rrel (P r and C r) (P' r' and C' r') (B r) (B' r')"
  assumes body_inv:
    "\<And>r. \<lbrace>P r and C r\<rbrace> B r \<lbrace>P\<rbrace>"
    "\<And>r'. \<lbrace>P' r' and C' r'\<rbrace> B' r' \<lbrace>P'\<rbrace>"
  assumes rel: "rrel r r'"
  assumes nf': "\<And>r'. no_fail (P' r' and C' r') (B' r')"
  assumes termin: "\<And>r' s'. \<lbrakk>P' r' s'; C' r' s'\<rbrakk> \<Longrightarrow> whileLoop_terminates C' B' r' s'"
  shows "corres_underlying srel False nf' rrel (P r) (P' r') (whileLoop C B r) (whileLoop C' B' r')"
  apply (rule corres_no_failI)
   apply (fastforce simp: no_fail_whileLoop[OF nf' termin body_inv(2)] no_fail_def)
  apply clarsimp
  apply (frule in_whileLoop_corres[OF body_corres body_inv]; (fastforce dest: cond)?)
  apply (fastforce intro: assms)
  done

lemmas corres_whileLoop =
  corres_whileLoop_ret[where P="\<lambda>_. P" for P, where P'="\<lambda>_. P'" for P', simplified]

lemma whileLoop_terminates_cross:
  assumes body_corres:
    "\<And>r r'. rrel r r' \<Longrightarrow>
             corres_underlying srel nf nf' rrel (P r and C r) (P' r' and C' r') (B r) (B' r')"
  assumes cond: "\<And>r r' s s'. \<lbrakk>rrel r r'; (s, s') \<in> srel; P r s; P' r' s'\<rbrakk> \<Longrightarrow> C r s = C' r' s'"
  assumes body_inv:
    "\<And>r. \<lbrace>P r and C r\<rbrace> B r \<lbrace>P\<rbrace>"
    "\<And>r'. \<lbrace>P' r' and C' r'\<rbrace> B' r' \<lbrace>P'\<rbrace>"
  assumes abs_termination: "\<And>r s. \<lbrakk>P r s; C r s\<rbrakk> \<Longrightarrow> whileLoop_terminates C B r s"
  assumes ex_abs: "ex_abs_underlying srel (P r) s'"
  assumes rrel: "rrel r r'"
  assumes P': "P' r' s'"
  assumes nf: "\<And>r. nf \<Longrightarrow> no_fail (P r and C r) (B r)"
  shows "whileLoop_terminates C' B' r' s'"
proof -
  have helper: "\<And>s. P r s \<and> C r s \<Longrightarrow> \<forall>r' s'. rrel r r' \<and> (s, s') \<in> srel \<and> P r s \<and> P' r' s'
                                               \<longrightarrow> whileLoop_terminates C' B' r' s'"
       (is "\<And>s. _ \<Longrightarrow> ?I r s")
    apply (rule_tac P="?I" in whileLoop_terminates.induct)
      apply (fastforce intro: abs_termination)
     apply (fastforce simp: whileLoop_terminates.intros dest: cond)
    apply (subst whileLoop_terminates.simps)
    apply clarsimp
    apply (frule (1) corres_underlyingD2[OF body_corres], (fastforce dest: nf simp: no_fail_def)+)
    apply (fastforce dest: use_valid intro: body_inv)
    done

  show ?thesis
    apply (insert assms helper)
    apply (cases "C' r' s'")
     apply (fastforce simp: ex_abs_underlying_def)
    apply (simp add: whileLoop_terminates.intros(1))
    done
qed

lemma corres_whileLoop_abs_ret:
  assumes cond: "\<And>r r' s s'. \<lbrakk>rrel r r'; (s, s') \<in> srel; P r s; P' r' s'\<rbrakk> \<Longrightarrow> C r s = C' r' s'"
  assumes body_corres:
    "\<And>r r'. rrel r r' \<Longrightarrow>
             corres_underlying srel nf nf' rrel (P r and C r) (P' r' and C' r') (B r) (B' r')"
  assumes rrel: "rrel r r'"
  assumes body_inv:
    "\<And>r. \<lbrace>P r and C r\<rbrace> B r \<lbrace>P\<rbrace>"
    "\<And>r'. \<lbrace>P' r' and C' r'\<rbrace> B' r' \<lbrace>P'\<rbrace>"
  assumes abs_termination: "\<And>r s. \<lbrakk>P r s; C r s\<rbrakk> \<Longrightarrow> whileLoop_terminates C B r s"
  assumes nf: "\<And>r. nf \<Longrightarrow> no_fail (P r and C r) (B r)"
  shows "corres_underlying srel nf nf' rrel (P r) (P' r') (whileLoop C B r) (whileLoop C' B' r')"
  apply (rule corres_underlyingI)
   apply (frule in_whileLoop_corres[OF body_corres body_inv];
          (fastforce intro: body_corres body_inv rrel dest: nf cond))
  apply (rule_tac I="\<lambda>rv' s'. \<exists>rv s. (s, s') \<in> srel \<and> rrel rv rv' \<and> P rv s \<and> P' rv' s'"
              and R="{((r', s'), r, s). C' r s \<and> (r', s') \<in> fst (B' r s)
                                        \<and> whileLoop_terminates C' B' r s}"
               in not_snd_whileLoop)
    apply (fastforce intro: rrel)
   apply (rename_tac s s' conc_r new_s)
   apply (clarsimp simp: validNF_def)
   apply (rule conjI)
    apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
      apply (rule_tac P'="\<lambda>s'. \<exists>rv s. (s, s') \<in> srel \<and> rrel rv conc_r
                                     \<and> P rv s \<and> (P' conc_r s' \<and> C' conc_r s') \<and> s' = new_s"
                   in hoare_weaken_pre[rotated])
       apply clarsimp
      apply (rule hoare_ex_pre)
      apply (rename_tac abs_r)
      apply (rule hoare_weaken_pre)
       apply (rule_tac P'="rrel abs_r conc_r" in hoare_grab_asm)
       apply (wpsimp wp: wp_from_corres_u[OF body_corres] body_inv)
       apply (fastforce dest: nf)
      apply (fastforce dest: cond)
     apply (fastforce simp: valid_def)
    apply wpsimp
    apply (rule whileLoop_terminates_cross[OF body_corres];
           (fastforce dest: nf cond intro: body_inv abs_termination))
   apply (rule_tac P="\<lambda>s'. \<exists>rv s. (s, s') \<in> srel \<and> rrel rv conc_r
                                  \<and> P rv s \<and> (P' conc_r s' \<and> C' conc_r s') \<and> s' = new_s"
                in no_fail_pre[rotated])
    apply fastforce
   apply (rule no_fail_ex_lift)
   apply (rename_tac abs_r)
   apply (rule no_fail_pre)
    apply (rule_tac G="rrel abs_r conc_r" in no_fail_grab_asm)
    apply (fastforce intro: corres_u_nofail dest: body_corres nf)
   apply (fastforce simp: cond)
  apply (fastforce intro: wf_subset[OF whileLoop_terminates_wf[where C=C']])
  done

lemmas corres_whileLoop_abs =
  corres_whileLoop_abs_ret[where P="\<lambda>_. P" for P, where P'="\<lambda>_. P'" for P', simplified]

end
