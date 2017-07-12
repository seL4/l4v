(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory SpecValid_R
imports ExtraCorres
begin

definition
  spec_valid :: "'s \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s, 'r) nondet_monad \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
                 ("_ \<turnstile> /\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>" [60,0,0,0] 100)
where
 "spec_valid st P f Q \<equiv> valid (\<lambda>s. s = st \<and> P s) f Q"

definition
  spec_validE :: "'s \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s, 'e + 'r) nondet_monad \<Rightarrow>
                   ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
                 ("_ \<turnstile> /\<lbrace>_\<rbrace>/ _ /(\<lbrace>_\<rbrace>, /\<lbrace>_\<rbrace>)" [60,0,0,0] 100)
where
 "spec_validE st P f Q E \<equiv> validE (\<lambda>s. s = st \<and> P s) f Q E"

lemma use_spec':
  assumes x: "\<And>s. s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  shows      "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (cut_tac s=s in x)
  apply (clarsimp simp: valid_def spec_valid_def)
  apply (erule(1) my_BallE, simp)
  done

lemma use_specE':
  "\<lbrakk> \<And>s. s \<turnstile> \<lbrace>P'\<rbrace> f' \<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P'\<rbrace> f' \<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace>"
  apply (simp add: validE_def spec_validE_def)
  apply (fold spec_valid_def)
  apply (simp add: use_spec')
  done

lemmas use_spec = use_spec' use_specE'

lemma drop_equalled_validE:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. s = s' \<and> P s\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (erule hoare_pre, clarsimp)

lemma drop_spec_valid[wp_split]:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (simp add: spec_valid_def)
  apply (erule hoare_vcg_precond_imp)
  apply clarsimp
  done

lemma drop_spec_validE[wp_split]:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (simp add: spec_validE_def)
  apply (erule hoare_vcg_precond_impE)
  apply clarsimp
  done

lemma split_spec_bindE[wp_split]:
  assumes x: "\<And>rv s''. (Inr rv, s'') \<in> fst (f s') \<Longrightarrow> s'' \<turnstile> \<lbrace>B rv\<rbrace> g rv \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  shows "s' \<turnstile> \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>,\<lbrace>E\<rbrace>
   \<Longrightarrow> s' \<turnstile> \<lbrace>A\<rbrace> f >>=E g \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  apply (clarsimp simp: spec_validE_def validE_def valid_def bind_def bindE_def lift_def split_def)
  apply (case_tac a)
   apply (clarsimp simp add: throwError_def return_def)
   apply (erule(1) my_BallE, simp)
  apply clarsimp
  apply (erule(1) my_BallE, simp)
  apply (drule x)
  apply (clarsimp simp: spec_validE_def validE_def valid_def split_def)
  apply (erule(1) my_BallE, simp)
  done

lemma split_spec_bind[wp_split]:
  assumes x: "\<And>rv s''. (rv, s'') \<in> fst (f s') \<Longrightarrow> s'' \<turnstile> \<lbrace>B rv\<rbrace> g rv \<lbrace>C\<rbrace>"
  shows "s' \<turnstile> \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>
   \<Longrightarrow> s' \<turnstile> \<lbrace>A\<rbrace> f >>= g \<lbrace>C\<rbrace>"
  apply (clarsimp simp: spec_valid_def valid_def bind_def lift_def split_def)
  apply (erule(1) my_BallE, simp)
  apply (drule x)
  apply (fastforce simp: spec_valid_def valid_def split_def)
  done

lemma split_spec_if[wp_split]:
  "\<lbrakk> G \<Longrightarrow> s' \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>;
     \<not> G \<Longrightarrow> s' \<turnstile> \<lbrace>P'\<rbrace> f' \<lbrace>Q\<rbrace>
   \<rbrakk>  \<Longrightarrow> s' \<turnstile> \<lbrace>\<lambda>s. (G \<longrightarrow> P s) \<and> (\<not> G \<longrightarrow> P' s)\<rbrace> if G then f else f' \<lbrace>Q\<rbrace>"
  by (cases G, simp+)

lemma split_spec_ifE[wp_split]:
  "\<lbrakk> G \<Longrightarrow> s' \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>;
     \<not> G \<Longrightarrow> s' \<turnstile> \<lbrace>P'\<rbrace> f' \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>
   \<rbrakk>  \<Longrightarrow> s' \<turnstile> \<lbrace>\<lambda>s. (G \<longrightarrow> P s) \<and> (\<not> G \<longrightarrow> P' s)\<rbrace> if G then f else f' \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (cases G, simp+)

lemma split_spec_unlessE[wp_split]:
  "\<lbrakk> \<not> G \<Longrightarrow> s' \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk>  \<Longrightarrow>
     s' \<turnstile> \<lbrace>\<lambda>s. (G \<longrightarrow> Q () s) \<and> (\<not> G \<longrightarrow> P s)\<rbrace> unlessE G f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (cases G, simp_all add: unlessE_def)
  apply wp
  done

lemma spec_fun_applyE [wp_split]:
  "s \<turnstile> \<lbrace>P\<rbrace> f x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f $ x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp

lemma split_spec_K_bind[wp_split]:
  "s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> K_bind f x \<lbrace>Q\<rbrace>"
  by simp

lemma split_spec_K_bindE[wp_split]:
  "s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> K_bind f x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp

lemma fudge_hoare:
  "s \<turnstile> \<lbrace>P\<rbrace> \<lambda>s. f s \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  .

lemma split_spec_whenE [wp_split]:
  "\<lbrakk> G \<Longrightarrow> s' \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk>  \<Longrightarrow>
     s' \<turnstile> \<lbrace>\<lambda>s. (G \<longrightarrow> P s) \<and> (\<not> G \<longrightarrow> Q () s)\<rbrace> whenE G f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (cases G, simp_all add: whenE_def)
  apply wp
  done

lemma spec_valid_conj_lift:
  "\<lbrakk> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; s \<turnstile> \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk>
     \<Longrightarrow> s \<turnstile> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>"
  apply (simp add: spec_valid_def)
  apply (drule(1) hoare_vcg_conj_lift)
  apply (simp add: conj_comms)
  done

lemma spec_valid_conj_liftE1:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-; s \<turnstile> \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E'\<rbrace> \<rbrakk>
     \<Longrightarrow> s \<turnstile> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>,\<lbrace>E'\<rbrace>"
  apply (simp add: spec_validE_def)
  apply (drule(1) hoare_vcg_conj_liftE1)
  apply (simp add: conj_comms pred_conj_def)
  done

lemma spec_valid_conj_liftE2:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,-; s \<turnstile> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E'\<rbrace> \<rbrakk>
     \<Longrightarrow> s \<turnstile> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>,\<lbrace>E'\<rbrace>"
  apply (simp add: spec_validE_def)
  apply (drule(1) hoare_vcg_conj_liftE1)
  apply (simp add: conj_comms pred_conj_def)
  done

lemma hoare_pre_spec_valid:
  "\<lbrakk> s \<turnstile> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>; P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (simp add: spec_valid_def)
  apply (erule hoare_pre)
  apply clarsimp
  done

lemma hoare_pre_spec_validE:
  "\<lbrakk> s \<turnstile> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (simp add: spec_validE_def)
  apply (erule hoare_pre)
  apply clarsimp
  done

lemma spec_validE_if:
  "\<lbrakk> G \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<not> G \<Longrightarrow> s \<turnstile> \<lbrace>P'\<rbrace> g \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> s \<turnstile> \<lbrace>P and P'\<rbrace> if G then f else g \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (cases G, simp_all)
   apply (clarsimp elim!: hoare_pre_spec_validE)+
  done

lemma spec_strengthen_post:
  "\<lbrakk> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>; \<And>s r. Q' s r \<Longrightarrow> Q s r \<rbrakk> \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (simp add: spec_valid_def valid_def
                split_def split: sum.splits)

lemma spec_strengthen_postE:
  "\<lbrakk> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>, \<lbrace>E\<rbrace>; \<And>s r. Q' s r \<Longrightarrow> Q s r \<rbrakk> \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  by (simp add: spec_valid_def spec_validE_def validE_def valid_def
                split_def split: sum.splits)

end
