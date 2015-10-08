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


definition "strong_post P Q \<equiv> P \<longrightarrow> Q"


lemmas strong_post_cong[cong] = imp_cong[simplified strong_post_def[symmetric]]


lemma hoare_strong_post:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow>
  \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>r s. strong_post (Q r s) (H r s)\<rbrace> \<Longrightarrow> \<lbrace>P and P'\<rbrace> f \<lbrace>\<lambda>r s. H r s\<rbrace>"
  apply (auto simp add: valid_def strong_post_def)
  by fastforce

private lemma drop_strong_post:
  "\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. strong_post (Q r s) (R r s)\<rbrace>"
  apply (erule hoare_strengthen_post)
  by (simp add: strong_post_def)


method find_context for Q :: "'a \<Rightarrow> 'b \<Rightarrow> bool" methods m =
  (match (Q) in 
    "\<lambda>r s. Q' r s \<and> Q'' r s" for Q' Q'' :: "'a \<Rightarrow> 'b \<Rightarrow> bool" \<Rightarrow>
       \<open>(find_context Q' \<open>m\<close>)?, (find_context Q'' \<open>m\<close>)?\<close>
  \<bar> "\<lambda>r s. Q' r s \<longrightarrow> Q'' r s" for Q' Q'' :: "'a \<Rightarrow> 'b \<Rightarrow> bool" \<Rightarrow>
       \<open>(find_context Q' \<open>m\<close>)?, (find_context Q'' \<open>m\<close>)?\<close>
  \<bar> "\<lambda>r s. if (A r s) then Q' r s else Q'' r s" for A Q' Q'' :: "'a \<Rightarrow> 'b \<Rightarrow> bool" \<Rightarrow>
       \<open>(find_context A \<open>m\<close>)?, (find_context Q' \<open>m\<close>)?, (find_context Q'' \<open>m\<close>)?\<close>
  \<bar> "\<lambda>r s. Q' r s \<or> Q'' r s" for Q' Q'' :: "'a \<Rightarrow> 'b \<Rightarrow> bool" \<Rightarrow>
       \<open>(find_context Q' \<open>m\<close>)?, (find_context Q'' \<open>m\<close>)?\<close>
  \<bar> "\<lambda>r. Q' r and Q'' r" for Q' Q'' :: "'a \<Rightarrow> 'b \<Rightarrow> bool" \<Rightarrow>
       \<open>(find_context Q' \<open>m\<close>)?, (find_context Q'' \<open>m\<close>)?\<close>
  \<bar> "\<lambda>r s. \<not> Q' r s" for Q' :: "'a \<Rightarrow> 'b \<Rightarrow> bool" \<Rightarrow>
       \<open>(find_context Q' \<open>m\<close>)?\<close>
  \<bar> "\<lambda>(r :: 'a) (s :: 'b). Q'" for Q' :: "bool" \<Rightarrow> \<open>fail\<close>
  \<bar> _ \<Rightarrow> \<open>rule hoare_strong_post[where Q=Q], solves \<open>m\<close>\<close>     
   )

definition "schematic_equiv P P' \<equiv> (PROP P \<equiv> PROP P')" 

lemma
  hoare_pre_schematic_equiv: 
  "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace> \<Longrightarrow> (\<And>s. PROP schematic_equiv (Trueprop (Q s)) (Trueprop (P s)))\<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>"
  apply (simp add: schematic_equiv_def)
  apply (rule hoare_pre_imp[rotated],assumption)
  apply (drule_tac x=s in meta_spec)
  by (erule equal_elim_rule2)
  

lemma schematic_equivI: "PROP schematic_equiv (PROP P) (PROP P)" 
  by (simp add: schematic_equiv_def)
  

method post_strengthen methods wp' simp' =
  (match conclusion in "\<lbrace>_\<rbrace> _ \<lbrace>Q\<rbrace>" for Q \<Rightarrow>
    \<open>rule hoare_pre_schematic_equiv, find_context Q \<open>wp'\<close>\<close>, 
   find_goal \<open>rule schematic_equivI\<close>,
   simp'; ((rule drop_strong_post)+)?
  )


method wpstr uses add del = 
  (post_strengthen \<open>wp_once add: add del: del\<close> \<open>simp split del: split_if\<close>)

end

notepad begin
  fix P P' P'' and Q Q' Q'' R :: "'b \<Rightarrow> 'a \<Rightarrow> bool" and f :: "('a,'b) nondet_monad"
  assume A: "\<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>" and B[wp]:"\<lbrace>P''\<rbrace> f \<lbrace>Q'\<rbrace>" and C: "\<And>r s. \<not> R r s \<longrightarrow> Q'' r s"
  have "\<lbrace>P and P' and P''\<rbrace> f \<lbrace>\<lambda>r s. (R r s \<longrightarrow> (Q r s \<and> Q' r s)) \<and> (\<not> R r s \<longrightarrow> (Q r s \<and> Q'' r s))\<rbrace>"
  apply (rule hoare_pre)
   apply (wpstr add: A del: B)
   apply wpstr
   apply (simp add: C)
   apply wp
  by simp

end


end