(*  Title:      Subgoal_Focus.thy
    Author:     Daniel Matichuk, NICTA/UNSW
    
    WP-specific Eisbach methods
*)

theory Eisbach_WP
imports Eisbach_Methods "wp/NonDetMonadVCG"
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
   focus (concl) 
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
  (focus 
    \<open>rule packed_validEs,
     focus (concl) \<open>m,fold_subgoals\<close>, 
     atomize (full),
     rule packed_validI\<close>)

method post methods m = 
  (post_raw 
     \<open>intro impI conjI allI,
      distinct_subgoals,
      all \<open>m\<close>,
      fold_subgoals\<close>)

      
end