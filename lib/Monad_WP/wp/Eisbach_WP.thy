(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*  WP-specific Eisbach methods *)

theory Eisbach_WP
imports
  "../../Eisbach_Methods"
  "../NonDetMonadVCG"
  "../../Conjuncts"
  "../../Rule_By_Method"
  "WPI"
begin


text \<open>
  Methods for manipulating the post conditions of hoare triples as if they
  were proper subgoals.

  post_asm can be used with the @ attribute to modify existing proofs. Useful
  for proving large postconditions in one proof and then subsequently decomposing it.

\<close>
context begin

definition "packed_valid P f si r s \<equiv> P si \<and> (r, s) \<in> fst (f si)"

lemma packed_validE:"(\<And>si r s. packed_valid P f si r s \<Longrightarrow> Q r s) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (clarsimp simp: valid_def packed_valid_def)

lemma packed_validI: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<forall>si r s. packed_valid P f si r s \<longrightarrow> Q r s"
  apply (clarsimp simp: valid_def packed_valid_def)
  by auto

definition "packed_validR P f si r s \<equiv> P si \<and> (Inr r, s) \<in> fst (f si)"


lemma packed_validRE:"(\<And>si r s. packed_validR P f si r s \<Longrightarrow> Q r s) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  apply (clarsimp simp: validE_R_def validE_def valid_def packed_validR_def)
  by (metis sum.case sumE)

lemma packed_validRI: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<forall>si r s. packed_validR P f si r s \<longrightarrow> Q r s"
  apply (clarsimp simp: valid_def validE_R_def validE_def packed_validR_def)
  by fastforce

lemma trivial_imp: "\<forall>r s. Q r s \<longrightarrow> Q r s" by simp

lemma uncurry2: "\<forall>r s. Q r s \<and> Q' r s \<longrightarrow> Q'' r s \<Longrightarrow> \<forall>r s. Q r s \<longrightarrow> Q' r s \<longrightarrow> Q'' r s"
  by simp

named_theorems hoare_post_imps

lemmas [hoare_post_imps] = hoare_post_imp_R hoare_post_imp[rotated]

method post_asm_raw methods m =
  (drule hoare_post_imps,
   atomize (full),
   focus_concl
     \<open>intro impI allI,
      m,
      atomize (full),
      ((rule uncurry2)+)?\<close>,
   rule trivial_imp)

method post_asm methods m =
  (post_asm_raw \<open>(simp only: bipred_conj_def pred_conj_def)?,(elim conjE)?,m\<close>)


named_theorems packed_validEs

lemmas [packed_validEs] = packed_validE packed_validRE

named_theorems packed_validIs

lemmas [packed_validIs] = packed_validI packed_validRI

method post_raw methods m =
  (focus_concl
    \<open>rule packed_validEs,
     focus_concl \<open>m,fold_subgoals\<close>,
     atomize (full),
     rule packed_validI\<close>)

method post_strong methods m_distinct m_all =
  (post_raw
     \<open>(simp only: pred_conj_def bipred_conj_def)?,
      (intro impI conjI allI)?,
      distinct_subgoals_strong \<open>m_distinct\<close>,
      all \<open>m_all\<close>,
      fold_subgoals\<close>)

method post methods m = post_strong \<open>(assumption | erule mp)+\<close> \<open>m\<close>

end


text \<open>
  Method (meant to be used with @ as an attribute) used for producing multiple facts out of
  a single hoare triple with a conjunction in its post condition.
\<close>

context begin

private lemma hoare_decompose:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> Q' r s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<and> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>"
  by (fastforce simp add: valid_def pred_conj_def)

private lemma hoare_decomposeE_R:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> Q' r s\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<and> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,-"
  by (fastforce simp add: validE_R_def validE_def valid_def pred_conj_def split: prod.splits sum.splits)

private lemma hoare_decomposeE_E:
  "\<lbrace>P\<rbrace> f -,\<lbrace>\<lambda>r s. Q r s \<and> Q' r s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f -,\<lbrace>Q\<rbrace> \<and> \<lbrace>P\<rbrace> f -,\<lbrace>Q'\<rbrace>"
  by (fastforce simp add: validE_E_def validE_def valid_def pred_conj_def split: prod.splits sum.splits)

private lemma hoare_decomposeE:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. E r s \<and> E' r s\<rbrace>,\<lbrace>\<lambda>r s. R r s \<and> R' r s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>E\<rbrace>,- \<and> \<lbrace>P\<rbrace> f \<lbrace>E'\<rbrace>,- \<and> \<lbrace>P\<rbrace> f -,\<lbrace>R\<rbrace> \<and> \<lbrace>P\<rbrace> f -,\<lbrace>R'\<rbrace>"
  by (fastforce simp add: validE_R_def validE_E_def validE_def valid_def pred_conj_def split: prod.splits sum.splits)

private lemmas hoare_decomposes' = hoare_decompose hoare_decomposeE_R hoare_decomposeE_E hoare_decomposeE

private method add_pred_conj = (subst pred_conj_def[symmetric])
private method add_bipred_conj = (subst bipred_conj_def[symmetric])

private lemmas hoare_decomposes[THEN conjE] =
  hoare_decomposes'
  hoare_decomposes'[# \<open>add_pred_conj\<close>]
  hoare_decomposes'[# \<open>add_bipred_conj\<close>]
  hoare_decomposeE[# \<open>add_pred_conj, add_pred_conj\<close>]
  hoare_decomposeE[# \<open>add_bipred_conj, add_pred_conj\<close>]
  hoare_decomposeE[# \<open>add_pred_conj, add_bipred_conj\<close>]
  hoare_decomposeE[# \<open>add_bipred_conj, add_bipred_conj\<close>]

method hoare_decompose = (elim hoare_decomposes)

end


notepad begin
  fix A :: "'a \<Rightarrow> bool" and B C D f
  assume A: "\<And>s. A s = True" and
         B: "\<And>s :: 'a. B s = True" and
         C: "\<And>s :: 'a. C s = True" and
         D: "\<And>s :: 'a. D s = True" and
         f: "f = (return () :: ('a,unit) nondet_monad)"

  have f_valid[@ \<open>hoare_decompose\<close>,conjuncts]: "\<lbrace>A\<rbrace> f \<lbrace>\<lambda>_. B and C and D\<rbrace>"
  apply (simp add: f)
  apply wp
  by (simp add: B C D)

  note f_valid' = conjuncts

  have f_d: "\<lbrace>A\<rbrace> f \<lbrace>\<lambda>_. D\<rbrace>" by (rule f_valid')

  have f_valid_interm: "\<lbrace>A\<rbrace> f \<lbrace>\<lambda>_. B and C and (\<lambda>s. D s \<longrightarrow> B s)\<rbrace>"
  apply (post_strong \<open>simp\<close> \<open>-\<close>)
  apply (wp f_valid')
  by simp

  (* All rotations are attempted when strengthening *)

  have f_valid_interm: "\<lbrace>A\<rbrace> f \<lbrace>\<lambda>_. (\<lambda>s. D s \<longrightarrow> B s) and B and C \<rbrace>"
  apply (post_strong \<open>simp\<close> \<open>-\<close>, wp f_valid')
  by simp

end




end
