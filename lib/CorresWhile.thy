(*
 * Copyright 2026, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory CorresWhile
imports ExtraCorres Heap_List MonadicRewrite
begin

text \<open>Some @{term corres_underlying} rules for @{term whileLoop}\<close>

lemma in_whileLoop_corres':
  assumes body_corres:
    "\<And>r r'. rrel r r' \<Longrightarrow>
             corres_underlying srel nf nf' rrel (P r and C r) (P' r r' and C' r') (B r) (B' r')"
  assumes body_inv:
    "\<And>r. \<lbrace>P r and C r\<rbrace> B r \<lbrace>P\<rbrace>"
    "\<And>r r' new_r s s' t.
      \<lbrakk>rrel r r'; (s, s') \<in> srel; P r s; (new_r, t) \<in> fst (B r s)\<rbrakk>
      \<Longrightarrow> \<lbrace>\<lambda>state. state = s' \<and> P' r r' state \<and> C' r' state\<rbrace> B' r' \<lbrace>\<lambda>r' state. P' new_r r' state\<rbrace>"
  assumes cond: "\<And>r r' s s'. \<lbrakk>rrel r r'; (s, s') \<in> srel; P r s; P' r r' s'\<rbrakk> \<Longrightarrow> C r s = C' r' s'"
  assumes result: "(rv', t') \<in> fst (whileLoop C' B' r' s')"
  assumes nf: "\<And>r. nf \<Longrightarrow> no_fail (P r and C r) (B r)"
  shows "\<forall>s r. (s, s') \<in> srel \<and> rrel r r' \<and> P r s \<and> P' r r' s'
               \<longrightarrow> (\<exists>rv t. (rv, t) \<in> fst (whileLoop C B r s) \<and> (t, t') \<in> srel \<and> rrel rv rv')"
  apply (rule in_whileLoop_induct[OF result])
   apply (force simp: cond whileLoop_def)
  apply clarsimp
  apply (frule (1) corres_underlyingD2[OF body_corres];
         (fastforce dest: nf simp: cond no_fail_def)?)
  apply clarsimp
  apply (frule use_valid[OF _ body_inv(1)])
   apply (fastforce dest: cond)
  apply (frule (4) use_valid[OF _ body_inv(2)])
   apply fastforce
  apply (fastforce simp: whileLoop_def intro: whileLoop_results.intros(3) dest: cond)
  done

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
  by (rule in_whileLoop_corres', (fastforce intro: assms hoare_weaken_pre dest: cond)+)

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

lemma whileLoop_terminates_cross_ret:
  assumes body_corres:
    "\<And>r r'. rrel r r' \<Longrightarrow>
             corres_underlying srel nf nf' rrel (P r and C r) (P' r r' and C' r') (B r) (B' r')"
  assumes cond: "\<And>r r' s s'. \<lbrakk>rrel r r'; (s, s') \<in> srel; P r s; P' r r' s'\<rbrakk> \<Longrightarrow> C r s = C' r' s'"
  assumes body_inv:
    "\<And>r. \<lbrace>P r and C r\<rbrace> B r \<lbrace>P\<rbrace>"
    "\<And>r r' new_r s s' t.
      \<lbrakk>rrel r r'; (s, s') \<in> srel; P r s; (new_r, t) \<in> fst (B r s)\<rbrakk>
      \<Longrightarrow> \<lbrace>\<lambda>state. state = s' \<and> P' r r' state \<and> C' r' state\<rbrace> B' r' \<lbrace>\<lambda>r' state. P' new_r r' state\<rbrace>"
  assumes abs_termination: "\<And>r s. \<lbrakk>P r s; C r s\<rbrakk> \<Longrightarrow> whileLoop_terminates C B r s"
  assumes ex_abs: "ex_abs_underlying srel (P r) s'"
  assumes rrel: "rrel r r'"
  assumes P': "P' r r' s'"
  assumes nf: "\<And>r. nf \<Longrightarrow> no_fail (P r and C r) (B r)"
  shows "whileLoop_terminates C' B' r' s'"
proof -
  have helper:
    "\<And>s. P r s \<and> C r s \<Longrightarrow> \<forall>r' s'. rrel r r' \<and> (s, s') \<in> srel \<and> P r s \<and> P' r r' s'
                                               \<longrightarrow> whileLoop_terminates C' B' r' s'"
     (is "\<And>s. _ \<Longrightarrow> ?I r s")
    apply (rule_tac P="?I" in whileLoop_terminates.induct)
      apply (fastforce intro: abs_termination)
     apply (fastforce simp: whileLoop_terminates.intros dest: cond)
    apply (subst whileLoop_terminates.simps)
    apply clarsimp
    apply (frule (1) corres_underlyingD2[OF body_corres], fastforce+)
     apply (fastforce dest: nf simp: no_fail_def)
    using assms
    by (fastforce dest: use_valid intro: body_inv)

  show ?thesis
    apply (insert assms helper)
    apply (cases "C' r' s'")
     apply (fastforce simp: ex_abs_underlying_def)
    apply (simp add: whileLoop_terminates.intros(1))
    done
qed

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
  apply (insert assms)
  apply (erule whileLoop_terminates_cross_ret[where P'="\<lambda>_ r' s'. P' r' s'"])
         apply force
        apply force
       apply (fastforce intro: hoare_weaken_pre)
      by force+

lemma corres_whileLoop_abs_ret:
  assumes cond: "\<And>r r' s s'. \<lbrakk>rrel r r'; (s, s') \<in> srel; P r s; P' r r' s'\<rbrakk> \<Longrightarrow> C r s = C' r' s'"
  assumes body_corres:
    "\<And>r r'. rrel r r' \<Longrightarrow>
             corres_underlying srel nf nf' rrel (P r and C r) (P' r r' and C' r') (B r) (B' r')"
  assumes rrel: "rrel r r'"
  assumes body_inv:
    "\<And>r. \<lbrace>P r and C r\<rbrace> B r \<lbrace>P\<rbrace>"
    "\<And>r r' new_r s s' t.
      \<lbrakk>rrel r r'; (s, s') \<in> srel; P r s; (new_r, t) \<in> fst (B r s)\<rbrakk>
      \<Longrightarrow> \<lbrace>\<lambda>state. state = s' \<and> P' r r' state \<and> C' r' state\<rbrace> B' r' \<lbrace>\<lambda>r' state. P' new_r r' state\<rbrace>"
  assumes abs_termination: "\<And>r s. \<lbrakk>P r s; C r s\<rbrakk> \<Longrightarrow> whileLoop_terminates C B r s"
  assumes nf: "\<And>r. nf \<Longrightarrow> no_fail (P r and C r) (B r)"
  shows "corres_underlying srel nf nf' rrel (P r) (P' r r') (whileLoop C B r) (whileLoop C' B' r')"
  apply (rule corres_underlyingI)
   apply (frule in_whileLoop_corres'[OF body_corres body_inv];
          (fastforce intro: body_corres body_inv rrel dest: nf cond))
  apply (rule_tac I="\<lambda>rv' s'. \<exists>rv s. (s, s') \<in> srel \<and> rrel rv rv' \<and> P rv s \<and> P' rv rv' s'"
              and R="{((r', s'), r, s). C' r s \<and> (r', s') \<in> fst (B' r s)
                                        \<and> whileLoop_terminates C' B' r s}"
               in not_snd_whileLoop)
    apply (fastforce intro: rrel)
   apply (rename_tac s s' conc_r new_s')
   apply (clarsimp simp: validNF_def)
   apply (rule conjI)
    apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
      apply (rule_tac P'="\<lambda>s'. \<exists>rv s. (s, s') \<in> srel \<and> rrel rv conc_r
                                      \<and> P rv s \<and> (P' rv conc_r s' \<and> C' conc_r s') \<and> s' = new_s'"
                   in hoare_weaken_pre[rotated])
       apply clarsimp
      apply (rule hoare_ex_pre)
      apply (rename_tac abs_r)
      apply (insert body_corres)[1]
      apply (drule_tac x=abs_r in meta_spec)
      apply (drule_tac x=conc_r in meta_spec)
      apply (insert body_inv)[1]
      apply (drule_tac x=abs_r in meta_spec)
      apply (drule_tac x=abs_r in meta_spec)
      apply (drule_tac x=conc_r in meta_spec)
      apply (clarsimp simp: valid_def)
      apply (rename_tac new_s)
      apply (erule_tac s=new_s in corres_underlyingE)
           apply assumption
          apply (fastforce dest: cond)
         apply fastforce
        apply fastforce
       apply (metis case_prodD cond)
      using cond nf
      apply (fastforce simp: no_fail_def)
     apply (fastforce simp: valid_def)
    apply wpsimp
    apply (rule whileLoop_terminates_cross_ret[OF body_corres];
           (fastforce dest: nf cond intro: body_inv abs_termination))
   apply (rule_tac P="\<lambda>s'. \<exists>rv s. (s, s') \<in> srel \<and> rrel rv conc_r
                                  \<and> P rv s \<and> (P' rv conc_r s' \<and> C' conc_r s') \<and> s' = new_s'"
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

text \<open> A weaker version where the guards do not refer to the initial/return values of the loop.\<close>
lemmas corres_whileLoop_abs =
  corres_whileLoop_abs_ret[where P="\<lambda>_. P" for P, where P'="\<lambda>_ _. P'" for P', simplified]

lemma corres_mapM_x_whileLoop_strong:
  assumes body_corres:
    "\<And>ls t.
      \<lbrakk>ls \<noteq> []; hd ls = t\<rbrakk>
      \<Longrightarrow> corres_underlying srel nf nf' dc
            (P ls) (P' ls and (\<lambda>s. heap_ls (nexts_of s) (Some t) ls)) (B t) (B' t)"
  assumes body_inv:
    "\<And>ls t. \<lbrakk>ls \<noteq> []; hd ls = t\<rbrakk> \<Longrightarrow> \<lbrace>P ls\<rbrace> B t \<lbrace>\<lambda>_. P (tl ls)\<rbrace>"
    "\<And>ls t. \<lbrakk>ls \<noteq> []; hd ls = t\<rbrakk>
       \<Longrightarrow> \<lbrace>P' ls and (\<lambda>s. heap_ls (nexts_of s) (Some t) ls) and ex_abs_underlying srel (P ls)\<rbrace>
           B' t
           \<lbrace>\<lambda>_. P' (tl ls)\<rbrace>"
  assumes nf: "\<And>ls t. \<lbrakk>ls \<noteq> []; hd ls = t; nf\<rbrakk> \<Longrightarrow> no_fail (P ls) (B t)"
  assumes rewrite:
    "\<And>ls t. \<lbrakk>ls \<noteq> []; hd ls = t\<rbrakk>
       \<Longrightarrow> monadic_rewrite False True (P' ls and ex_abs_underlying srel (P ls))
             (gets_the (read_next t)) (gets (\<lambda>s. nexts_of s t))"
  assumes no_ofail:
    "\<And>ls t. \<lbrakk>ls \<noteq> []; hd ls = t; nf'\<rbrakk>
       \<Longrightarrow> no_ofail (P' ls and ex_abs_underlying srel (P ls)) (read_next t)"
  assumes heap_ls_valid:
    "\<And>ls t next.
      \<lbrakk>ls \<noteq> []; hd ls = t\<rbrakk>
      \<Longrightarrow> \<lbrace>\<lambda>s. P' ls s \<and> heap_ls (nexts_of s) (Some t) ls \<and> next = nexts_of s t
               \<and> heap_ls (nexts_of s) (Some t) ls \<and> ex_abs_underlying srel (P ls) s\<rbrace>
          B' t
          \<lbrace>\<lambda>_ s. heap_ls (nexts_of s) next (tl ls)\<rbrace>"
  shows
    "corres_underlying srel nf nf' dc
       (P ls) (P' ls and (\<lambda>s. heap_ls (nexts_of s) st ls))
       (mapM_x (\<lambda>t. B t) ls)
       (whileLoop (\<lambda>r _. \<exists>v. r = Some v)
                  (\<lambda>r. do next \<leftarrow> gets_the (read_next (the r));
                          B' (the r);
                          return next
                       od)
                  st)"
  apply (subst mapM_x_whileLoop)
  apply (rule corres_add_noop_rhs_dc)
  apply (rule corres_split_forwards'[rotated, where Q="\<top>\<top>" and Q'="\<top>\<top>" and r'=dc])
     apply wpsimp+
  apply (rule_tac F="(ls = []) = (st = None) \<and> (ls \<noteq> [] \<longrightarrow> hd ls = the st)"
               in corres_req)
   apply (fastforce dest: heap_path_head)
  apply (rule_tac r'="\<lambda>ls q. (ls = [] \<longleftrightarrow> q = None) \<and> (ls \<noteq> [] \<longrightarrow> hd ls = the q)"
               in corres_rel_imp)
   apply (rule stronger_corres_guard_imp)
     apply (rule_tac P="\<lambda>r. P r" and P'="\<lambda>r r'. P' r and (\<lambda>s. heap_ls (nexts_of s) r' r)"
                  in corres_whileLoop_abs_ret)
           apply fastforce
          apply (rule corres_gen_asm)
          apply simp
          apply (rule corres_symb_exec_r_conj_ex_abs_forwards[OF _ gets_the_sp]; (solves wpsimp)?)
           apply (rename_tac "next")
           apply (rule_tac P'="\<lambda>_ s. heap_ls (nexts_of s) next (tl r)"
                       in corres_underlying_split_ex_abs[where r'=dc and P="\<top>\<top>"])
              apply (rule stronger_corres_guard_imp)
                apply (rule body_corres)
                 apply fastforce
                apply (fastforce intro: body_corres)
               apply fastforce
              apply fastforce
             apply (fastforce simp: Some_to_the heap_path_head')
            apply wp
           apply (rule hoare_weaken_pre)
            apply (fastforce intro: heap_ls_valid)
           apply (fastforce dest: rewrite simp: monadic_rewrite_def monad_simps ex_abs_underlying_def)
          apply wpsimp
          apply (fastforce dest!: no_ofail simp: no_ofail_def)
         apply fastforce
        apply (rule_tac S="r \<noteq> []" in hoare_gen_asm_spec)
         apply fastforce
        apply wpsimp
         apply (fastforce intro: body_inv)
        apply fastforce
       apply (rule_tac S="r' \<noteq> None" in hoare_gen_asm_spec)
        apply fastforce
       apply clarsimp
       apply (prop_tac "new_r = tl r")
        apply (clarsimp simp: monad_simps)
       apply (rule hoare_vcg_conj_lift_pre_fix)
        apply wpsimp
          apply (rule body_inv)
           apply (clarsimp simp: monad_simps)
          apply wpsimp
         apply wpsimp
        apply fastforce
       apply (simp flip: conj_assoc)
       apply wpsimp
         apply (fastforce intro: heap_ls_valid)
        apply wpsimp
       apply wpsimp
       apply (fastforce dest: rewrite simp: monadic_rewrite_def monad_simps)
      apply (rule whileLoop_terminates_inv[OF _ _ list_length_wf_helper, where I="\<top>\<top>", simplified])
      apply wpsimp
     apply (rule_tac S="r \<noteq> []" in no_fail_gen_asm_spec)
      apply fastforce
     apply wpsimp
      apply (fastforce intro: nf)+
  done

lemma corres_mapM_x_whileLoop:
  assumes body_corres:
    "\<And>ls t.
      \<lbrakk>ls \<noteq> []; hd ls = t\<rbrakk>
      \<Longrightarrow> corres_underlying srel nf nf' dc
            (P ls) (P' ls and (\<lambda>s. heap_ls (nexts_of s) (Some t) ls)) (B t) (B' t)"
  assumes body_inv:
    "\<And>ls t. \<lbrakk>ls \<noteq> []; hd ls = t\<rbrakk> \<Longrightarrow> \<lbrace>P ls\<rbrace> B t \<lbrace>\<lambda>_. P (tl ls)\<rbrace>"
    "\<And>ls t. \<lbrakk>ls \<noteq> []; hd ls = t\<rbrakk>
       \<Longrightarrow> \<lbrace>P' ls and (\<lambda>s. heap_ls (nexts_of s) (Some t) ls) and ex_abs_underlying srel (P ls)\<rbrace>
           B' t
           \<lbrace>\<lambda>_. P' (tl ls)\<rbrace>"
  assumes nf: "\<And>ls t. \<lbrakk>ls \<noteq> []; hd ls = t; nf\<rbrakk> \<Longrightarrow> no_fail (P ls) (B t)"
  assumes rewrite:
    "\<And>ls t. \<lbrakk>ls \<noteq> []; hd ls = t\<rbrakk>
       \<Longrightarrow> monadic_rewrite False True (P' ls and ex_abs_underlying srel (P ls))
             (gets_the (read_next t)) (gets (\<lambda>s. nexts_of s t))"
  assumes no_ofail:
    "\<And>ls t. \<lbrakk>ls \<noteq> []; hd ls = t; nf'\<rbrakk>
       \<Longrightarrow> no_ofail (P' ls and ex_abs_underlying srel (P ls)) (read_next t)"
  assumes body_heap_upd:
    "\<And>Q ls t t'. \<lbrakk>ls \<noteq> []; hd ls = t\<rbrakk>
       \<Longrightarrow> \<lbrace>\<lambda>s. Q (nexts_of s t') \<and> t' \<noteq> t \<and> t' \<in> set ls \<and> P' ls s
                \<and> heap_ls (nexts_of s) (Some t) ls \<and> ex_abs_underlying srel (P ls) s\<rbrace>
           B' t
           \<lbrace>\<lambda>_ s. Q (nexts_of s t')\<rbrace>"
  shows
    "corres_underlying srel nf nf' dc
       (P ls) (P' ls and (\<lambda>s. heap_ls (nexts_of s) st ls))
       (mapM_x (\<lambda>t. B t) ls)
       (whileLoop (\<lambda>r _. \<exists>v. r = Some v)
                  (\<lambda>r. do next \<leftarrow> gets_the (read_next (the r));
                          B' (the r);
                          return next
                       od)
                  st)"
  apply (rule corres_mapM_x_whileLoop_strong)
      apply (fastforce intro: assms)+
  apply (clarsimp simp: valid_def)
  apply (frule heap_ls_distinct)
  apply (frule distinct_hd_not_in_tl)
  apply (cut_tac hp="nexts_of s" and xs="[hd ls]" and ys="tl ls" and start="Some (hd ls)"
              in heap_path_append)
  apply (rule heap_path_heap_upd_not_in_strong)
   apply fastforce
  apply (rename_tac ls s rv s')
  apply clarsimp
  apply (frule_tac ls1=ls and t1="hd ls" and s=s and t'1=t and Q1="\<lambda>val. val = nexts_of s t"
                in post_by_hoare[OF body_heap_upd])
     apply fastforce
    apply (fastforce dest: list.set_sel(2))
   apply fastforce
  apply fastforce
  done

end
