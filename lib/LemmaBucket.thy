(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory LemmaBucket
imports
  HaskellLemmaBucket
  SpecValid_R
  SubMonadLib
begin

lemma corres_underlying_trivial:
  "\<lbrakk> nf \<Longrightarrow> no_fail P' f \<rbrakk> \<Longrightarrow> corres_underlying Id nf op = \<top> P' f f"
  by (auto simp add: corres_underlying_def Id_def no_fail_def)

(* Strengthen *)

lemma strengthen_imp [strg]:
  "A \<longrightarrow> A' \<Longrightarrow> (B \<longrightarrow> A) \<longrightarrow> (B \<longrightarrow> A')" by clarsimp
  
lemma strengthen_hoare [strg]:
  "(\<And>r s. Q r s \<longrightarrow> R r s) \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace> \<longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>"
  apply (rule)
  apply (erule hoare_strengthen_post)
  apply clarsimp
  done

lemma strengthen_validE_R_cong[strg]:
  "\<lbrakk> \<And>rv s. Q rv s \<longrightarrow> R rv s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>,-"
  by (auto intro: hoare_post_imp_R)

lemma strengthen_all[strg]:
  "(\<And>x. P x \<longrightarrow> Q x) \<Longrightarrow> (\<forall>x. P x) \<longrightarrow> (\<forall>x. Q x)"
  by simp

lemma strengthen_ex[strg]:
  "(\<And>x. P x \<longrightarrow> Q x) \<Longrightarrow> (\<exists>x. P x) \<longrightarrow> (\<exists>x. Q x)"
  by fastforce

lemma strengthen_Ball[strg]:
  "(\<And>x. P x \<longrightarrow> Q x) \<Longrightarrow> (\<forall>x \<in> S. P x) \<longrightarrow> (\<forall>x \<in> S. Q x)"
  by simp

lemma hoare_spec_gen_asm:
  "\<lbrakk> F \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> s \<turnstile> \<lbrace>P and K F\<rbrace> f \<lbrace>Q\<rbrace>"
  "\<lbrakk> F \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f' \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> s \<turnstile> \<lbrace>P and K F\<rbrace> f' \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding spec_valid_def spec_validE_def validE_def
  apply (clarsimp simp only: pred_conj_def conj_assoc[symmetric] 
               intro!: hoare_gen_asm[unfolded pred_conj_def])+
  done

lemma spec_validE_fail:
  "s \<turnstile> \<lbrace>P\<rbrace> fail \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by wp

lemma mresults_fail: "mresults fail = {}"
  by (simp add: mresults_def fail_def)

lemma gets_symb_exec_l:
  "corres_underlying sr nf dc P P' (gets f) (return x)"
  by (simp add: corres_underlying_def return_def simpler_gets_def split_def)

lemmas mapM_x_wp_inv = mapM_x_wp[where S=UNIV, simplified]
  
lemma mapM_wp_inv:
  "(\<And>x. \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule  valid_return_unit)
  apply (fold mapM_x_mapM)
  apply (erule mapM_x_wp_inv)
  done

lemmas mapM_x_wp' = mapM_x_wp [OF _ subset_refl]

lemma corres_underlying_similar:
  "\<lbrakk> a = a'; b = b'; nf \<Longrightarrow> no_fail \<top> (f a b) \<rbrakk>
         \<Longrightarrow> corres_underlying Id nf dc \<top> \<top> (f a b) (f a' b')"
  by (simp add: corres_underlying_def no_fail_def, blast)

lemma corres_underlying_gets_pre_lhs:
  "(\<And>x. corres_underlying S nf r (P x) P' (g x) g') \<Longrightarrow>
  corres_underlying S nf r (\<lambda>s. P (f s) s) P' (gets f >>= (\<lambda>x. g x)) g'"
  apply (simp add: simpler_gets_def bind_def split_def corres_underlying_def)
  apply force
  done

lemma mapM_x_inv_wp:
  assumes x: "\<And>s. I s \<Longrightarrow> Q s"
  assumes y: "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> m x \<lbrace>\<lambda>rv. I\<rbrace>"
  assumes z: "\<And>s. I s \<Longrightarrow> P s"
  shows      "\<lbrace>I\<rbrace> mapM_x m xs \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (rule hoare_post_imp)
   apply (erule x)
  apply (rule mapM_x_wp)
   apply (rule hoare_pre_imp [OF _ y])
    apply (erule z)
   apply assumption
  apply simp
  done


lemma mapM_x_accumulate_checks':
  assumes P:  "\<And>x. x \<in> set xs' \<Longrightarrow> \<lbrace>\<top>\<rbrace> f x \<lbrace>\<lambda>rv. P x\<rbrace>"
  assumes P': "\<And>x y. \<lbrakk> x \<in> set xs'; y \<in> set xs' \<rbrakk>
                   \<Longrightarrow> \<lbrace>P y\<rbrace> f x \<lbrace>\<lambda>rv. P y\<rbrace>"
  shows       "set xs \<subseteq> set xs' \<Longrightarrow>
               \<lbrace>\<top>\<rbrace> mapM_x f xs \<lbrace>\<lambda>rv s. \<forall>x \<in> set xs. P x s\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_x_Nil)
  apply (simp add: mapM_x_Cons)
  apply (rule hoare_pre)
   apply (wp mapM_x_wp'[OF P'])
      apply blast
     apply simp
    apply assumption
   apply simp
   apply (rule P)
   apply simp
  apply simp
  done

lemmas mapM_x_accumulate_checks
    = mapM_x_accumulate_checks'[OF _ _ subset_refl]

(* Other *)

lemma isRight_rel_sum_comb2:
  "\<lbrakk> (f \<oplus> r) v v'; isRight v' \<rbrakk>
       \<Longrightarrow> isRight v \<and> r (theRight v) (theRight v')"
  by (clarsimp simp: isRight_def)

lemma enumerate_append:"enumerate i (xs @ ys) = enumerate i xs @ enumerate (i + length xs) ys"
  apply (induct xs arbitrary:ys i)
   apply clarsimp+
  done

lemma enumerate_bound:"(a, b) \<in> set (enumerate n xs) \<Longrightarrow> a < n + length xs"
  by (metis add.commute in_set_enumerate_eq prod.sel(1))

lemma enumerate_exceed:"(n + length xs, b) \<notin> set (enumerate n xs)"
  by (metis enumerate_bound less_not_refl)

lemma all_pair_unwrap:"(\<forall>a. P (fst a) (snd a)) = (\<forall>a b. P a b)"
  by force

lemma if_fold[simp]:"(if P then Q else if P then R else S) = (if P then Q else S)"
  by presburger

end
