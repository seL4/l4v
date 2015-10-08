(*  Title:      Eisbach_WP.thy
    Author:     Daniel Matichuk, NICTA/UNSW
    
    WP-specific Eisbach methods
*)

theory Eisbach_WP
imports "../Eisbach_Methods" NonDetMonadVCG "../Conjuncts" "../Rule_By_Method"
begin


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

text \<open>Strengthening postconditions automatically\<close>

context begin

private definition "not_triv_implies Q Q' \<equiv> True"

private definition "strong_post P Q \<equiv> P \<longrightarrow> Q"

private lemma not_triv_implies_test:
  "(P \<Longrightarrow> not_triv_implies Q' Q'') \<Longrightarrow> not_triv_implies (strong_post P Q') Q''"
  by (simp add: not_triv_implies_def)

private lemma not_triv_implies_test':
  "(P \<Longrightarrow> Q) \<Longrightarrow> not_triv_implies P Q"
  by (simp add: not_triv_implies_def)

private lemma not_triv_impliesI:
  "not_triv_implies Q Q'"
  by (simp add: not_triv_implies_def)

private lemmas strong_post_cong[cong] = imp_cong[simplified strong_post_def[symmetric]]

private method not_triv_implies =
  (fails 
    \<open>intro not_triv_implies_test not_triv_implies_test' conjI; 
      ((elim conjE)?, assumption)\<close>, 
   rule not_triv_impliesI)

private lemma hoare_find_context:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow>
  (\<And> r s. not_triv_implies (H (Q r s) r s) (Q r s)) \<Longrightarrow>
  \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>r s. strong_post (Q r s) (H (Q r s) r s)\<rbrace> \<Longrightarrow> \<lbrace>P and P'\<rbrace> f \<lbrace>\<lambda>r s. H (Q r s) r s\<rbrace>"
  apply (auto simp add: valid_def strong_post_def)
  by fastforce

private lemma drop_strong_post:
  "\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. strong_post (Q r s) (R r s)\<rbrace>"
  apply (erule hoare_strengthen_post)
  by (simp add: strong_post_def)

private definition "dummy_post r s \<equiv> True"

private lemma hoare_dummy:
  "\<lbrace>P\<rbrace> f \<lbrace>dummy_post\<rbrace>"
  apply (simp add: dummy_post_def[abs_def])
  by wp

private method no_schematic_post = (fails \<open>rule hoare_dummy\<close>)

method post_strengthen methods m =
  ((rule hoare_find_context, no_schematic_post, solves \<open>m\<close>, not_triv_implies)+,
    simp cong: strong_post_cong,
   (rule drop_strong_post)+)

end


notepad begin
  fix P P' P'' and Q Q' Q'' R :: "'b \<Rightarrow> 'a \<Rightarrow> bool" and f :: "('a,'b) nondet_monad"
  assume A[wp]: "\<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>" and B[wp]:"\<lbrace>P''\<rbrace> f \<lbrace>Q'\<rbrace>" and C: "\<And>r s. \<not> R r s \<longrightarrow> Q'' r s"
  have "\<lbrace>P and P' and P''\<rbrace> f \<lbrace>\<lambda>r s. (R r s \<longrightarrow> (Q r s \<and> Q' r s)) \<and> (\<not> R r s \<longrightarrow> (Q r s \<and> Q'' r s))\<rbrace>"
  apply (rule hoare_pre)
  apply (post_strengthen \<open>wp\<close>)
  apply (simp add: C)
  apply wp
  by simp

end

end