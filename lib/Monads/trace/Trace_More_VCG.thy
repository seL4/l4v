(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Partial correctness Hoare logic lemmas over the trace monad. Hoare triples, lifting lemmas, etc.
   If it doesn't contain a Hoare triple it likely doesn't belong in here. *)

theory Trace_More_VCG
  imports
    Trace_VCG
begin

lemma hoare_take_disjunct:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. P' rv s \<and> (False \<or> P'' rv s)\<rbrace>
    \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>P''\<rbrace>"
  by (erule hoare_strengthen_post, simp)

lemma hoare_post_add:
  "\<lbrace>P\<rbrace> S \<lbrace>\<lambda>r s. R r s \<and> Q r s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> S \<lbrace>Q\<rbrace>"
  by (erule hoare_strengthen_post, simp)

lemma hoare_post_addE:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ s. R s \<and> Q s\<rbrace>, \<lbrace>T\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ s. Q s\<rbrace>, \<lbrace>T\<rbrace>"
  by (erule hoare_post_impErr'; simp)

lemma hoare_pre_add:
  "(\<forall>s. P s \<longrightarrow> R s) \<Longrightarrow> (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<longleftrightarrow> \<lbrace>P and R\<rbrace> f \<lbrace>Q\<rbrace>)"
  apply (subst iff_conv_conj_imp)
  by(intro conjI impI; rule hoare_weaken_pre, assumption, clarsimp)

lemma hoare_pre_addE:
  "(\<forall>s. P s \<longrightarrow> R s) \<Longrightarrow> (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>S\<rbrace> \<longleftrightarrow> \<lbrace>P and R\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>S\<rbrace>)"
  apply (subst iff_conv_conj_imp)
  by(intro conjI impI; rule hoare_weaken_preE, assumption, clarsimp)

lemma hoare_name_pre_state:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> \<lbrace>(=) s\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (clarsimp simp: valid_def)

lemma hoare_name_pre_stateE:
  "\<lbrakk>\<And>s. P s \<Longrightarrow> \<lbrace>(=) s\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  by (clarsimp simp: validE_def2)

lemma valid_prove_more: (* FIXME: duplicate *)
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>"
  by (rule hoare_post_add)

lemma hoare_vcg_if_lift:
  "\<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. (P \<longrightarrow> X rv s) \<and> (\<not>P \<longrightarrow> Y rv s)\<rbrace> \<Longrightarrow>
   \<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. if P then X rv s else Y rv s\<rbrace>"

  "\<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. (P \<longrightarrow> X rv s) \<and> (\<not>P \<longrightarrow> Y rv s)\<rbrace> \<Longrightarrow>
   \<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv. if P then X rv else Y rv\<rbrace>"
  by (auto simp: valid_def split_def)

lemma hoare_vcg_if_lift_strong:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>P\<rbrace>; \<lbrace>\<lambda>s. \<not> P' s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>; \<lbrace>Q'\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>R'\<rbrace> f \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. if P' s then Q' s else R' s\<rbrace> f \<lbrace>\<lambda>rv s. if P rv s then Q rv s else R rv s\<rbrace>"

  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>P\<rbrace>; \<lbrace>\<lambda>s. \<not> P' s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>; \<lbrace>Q'\<rbrace> f \<lbrace> Q\<rbrace>; \<lbrace>R'\<rbrace> f \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. if P' s then Q' s else R' s\<rbrace> f \<lbrace>\<lambda>rv s. (if P rv s then Q rv else R rv) s\<rbrace>"
  by (wpsimp wp: hoare_vcg_imp_lift' | assumption | fastforce)+

lemma hoare_vcg_imp_lift_pre_add:
  "\<lbrakk> \<lbrace>P and Q\<rbrace> f \<lbrace>\<lambda>rv s. R rv s\<rbrace>; f \<lbrace>\<lambda>s. \<not> Q s\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q s \<longrightarrow> R rv s\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule hoare_vcg_imp_lift')
    apply fastforce
   apply fastforce
  apply (clarsimp simp: pred_conj_def valid_def)
  done

lemma hoare_pre_tautI:
  "\<lbrakk> \<lbrace>A and P\<rbrace> a \<lbrace>B\<rbrace>; \<lbrace>A and not P\<rbrace> a \<lbrace>B\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> a \<lbrace>B\<rbrace>"
  by (fastforce simp: valid_def split_def pred_conj_def pred_neg_def)

lemma hoare_lift_Pf_pre_conj:
  assumes P: "\<And>x. \<lbrace>\<lambda>s. Q x s\<rbrace> m \<lbrace>P x\<rbrace>"
  assumes f: "\<And>P. \<lbrace>\<lambda>s. P (g s) \<and> R s\<rbrace> m \<lbrace>\<lambda>_ s. P (f s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q (g s) s \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (f s) rv s\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (rule use_valid [OF _ P], simp)
  apply (rule use_valid [OF _ f], simp, simp)
  done

lemmas hoare_lift_Pf4 = hoare_lift_Pf_pre_conj[where R=\<top>, simplified]
lemmas hoare_lift_Pf3 = hoare_lift_Pf4[where f=f and g=f for f]
lemmas hoare_lift_Pf2 = hoare_lift_Pf3[where P="\<lambda>f _. P f" for P]
lemmas hoare_lift_Pf = hoare_lift_Pf2[where Q=P and P=P for P]

lemmas hoare_lift_Pf3_pre_conj = hoare_lift_Pf_pre_conj[where f=f and g=f for f]
lemmas hoare_lift_Pf2_pre_conj = hoare_lift_Pf3_pre_conj[where P="\<lambda>f _. P f" for P]
lemmas hoare_lift_Pf_pre_conj' = hoare_lift_Pf2_pre_conj[where Q=P and P=P for P]

lemma hoare_if_r_and:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. if R r then Q r else Q' r\<rbrace>
  = \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. (R r \<longrightarrow> Q r s) \<and> (\<not>R r \<longrightarrow> Q' r s)\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_convert_imp:
  "\<lbrakk> \<lbrace>\<lambda>s. \<not> P s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> Q s\<rbrace>; \<lbrace>R\<rbrace> f \<lbrace>S\<rbrace> \<rbrakk> \<Longrightarrow>
    \<lbrace>\<lambda>s. P s \<longrightarrow> R s\<rbrace> f \<lbrace>\<lambda>rv s. Q s \<longrightarrow> S rv s\<rbrace>"
  apply (simp only: imp_conv_disj)
  apply (erule(1) hoare_vcg_disj_lift)
  done

lemma hoare_vcg_ex_lift_R:
  "\<lbrakk> \<And>v. \<lbrace>P v\<rbrace> f \<lbrace>Q v\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<exists>v. P v s\<rbrace> f \<lbrace>\<lambda>rv s. \<exists>v. Q v rv s\<rbrace>,-"
  apply (simp add: validE_R_def validE_def)
  apply (rule hoare_strengthen_post, erule hoare_vcg_ex_lift)
  apply (auto split: sum.split)
  done

lemma hoare_case_option_wpR:
  "\<lbrakk>\<lbrace>P\<rbrace> f None \<lbrace>Q\<rbrace>,-; \<And>x. \<lbrace>P' x\<rbrace> f (Some x) \<lbrace>Q' x\<rbrace>,-\<rbrakk> \<Longrightarrow>
  \<lbrace>case_option P P' v\<rbrace> f v \<lbrace>\<lambda>rv. case v of None \<Rightarrow> Q rv | Some x \<Rightarrow> Q' x rv\<rbrace>,-"
  by (cases v) auto

lemma hoare_vcg_conj_liftE_R:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>P'\<rbrace>,-; \<lbrace>Q\<rbrace> f \<lbrace>Q'\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>P and Q\<rbrace> f \<lbrace>\<lambda>rv s. P' rv s \<and> Q' rv s\<rbrace>, -"
  apply (simp add: validE_R_def validE_def valid_def split: sum.splits)
  apply blast
  done

lemma K_valid[wp]:
  "\<lbrace>K P\<rbrace> f \<lbrace>\<lambda>_. K P\<rbrace>"
  by (simp add: valid_def)

lemma hoare_vcg_exI:
  "\<lbrace>P\<rbrace> f \<lbrace>Q x\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<exists>x. Q x rv s\<rbrace>"
  apply (simp add: valid_def split_def)
  apply blast
  done

lemma hoare_exI_tuple:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>(rv,rv') s. Q x rv rv' s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>(rv,rv') s. \<exists>x. Q x rv rv' s\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_ex_all:
  "(\<forall>x. \<lbrace>P x\<rbrace> f \<lbrace>Q\<rbrace>) = \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (rule iffI)
   apply (fastforce simp: valid_def)+
  done

lemma hoare_imp_eq_substR:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. rv = x \<longrightarrow> Q x s\<rbrace>,-"
  by (fastforce simp add: valid_def validE_R_def validE_def split: sum.splits)

lemma hoare_split_bind_case_sum:
  assumes x: "\<And>rv. \<lbrace>R rv\<rbrace> g rv \<lbrace>Q\<rbrace>"
             "\<And>rv. \<lbrace>S rv\<rbrace> h rv \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P\<rbrace> f \<lbrace>S\<rbrace>,\<lbrace>R\<rbrace>"
  shows      "\<lbrace>P\<rbrace> f >>= case_sum g h \<lbrace>Q\<rbrace>"
  apply (rule hoare_seq_ext [OF _ y[unfolded validE_def]])
  apply (case_tac x, simp_all add: x)
  done

lemma hoare_split_bind_case_sumE:
  assumes x: "\<And>rv. \<lbrace>R rv\<rbrace> g rv \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
             "\<And>rv. \<lbrace>S rv\<rbrace> h rv \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes y: "\<lbrace>P\<rbrace> f \<lbrace>S\<rbrace>,\<lbrace>R\<rbrace>"
  shows      "\<lbrace>P\<rbrace> f >>= case_sum g h \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (unfold validE_def)
  apply (rule hoare_seq_ext [OF _ y[unfolded validE_def]])
  apply (case_tac x, simp_all add: x [unfolded validE_def])
  done

lemma assertE_sp:
  "\<lbrace>P\<rbrace> assertE Q \<lbrace>\<lambda>rv s. Q \<and> P s\<rbrace>,\<lbrace>E\<rbrace>"
  by (clarsimp simp: assertE_def) wp

lemma throwErrorE_E [wp]:
  "\<lbrace>Q e\<rbrace> throwError e -, \<lbrace>Q\<rbrace>"
  by (simp add: validE_E_def) wp

lemma gets_inv [simp]:
  "\<lbrace> P \<rbrace> gets f \<lbrace> \<lambda>r. P \<rbrace>"
  by (simp add: gets_def, wp)

lemma select_inv:
  "\<lbrace> P \<rbrace> select S \<lbrace> \<lambda>r. P \<rbrace>"
  by (simp add: select_def valid_def)

lemmas return_inv = hoare_return_drop_var

lemma assert_inv: "\<lbrace>P\<rbrace> assert Q \<lbrace>\<lambda>r. P\<rbrace>"
  unfolding assert_def
  by (cases Q) simp+

lemma assert_opt_inv: "\<lbrace>P\<rbrace> assert_opt Q \<lbrace>\<lambda>r. P\<rbrace>"
  unfolding assert_opt_def
  by (cases Q) simp+

lemma case_options_weak_wp:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<And>x. \<lbrace>P'\<rbrace> g x \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace> case opt of None \<Rightarrow> f | Some x \<Rightarrow> g x \<lbrace>Q\<rbrace>"
  apply (cases opt)
   apply (clarsimp elim!: hoare_weaken_pre)
  apply (rule hoare_weaken_pre [where Q=P'])
   apply simp+
  done

lemma case_option_wp_None_return:
  assumes [wp]: "\<And>x. \<lbrace>P' x\<rbrace> f x \<lbrace>\<lambda>_. Q\<rbrace>"
  shows "\<lbrakk>\<And>x s. (Q and P x) s \<Longrightarrow> P' x s \<rbrakk>
         \<Longrightarrow> \<lbrace>Q and (\<lambda>s. opt \<noteq> None \<longrightarrow> P (the opt) s)\<rbrace>
             (case opt of None \<Rightarrow> return () | Some x \<Rightarrow> f x)
             \<lbrace>\<lambda>_. Q\<rbrace>"
  by (cases opt; wpsimp)

lemma case_option_wp_None_returnOk:
  assumes [wp]: "\<And>x. \<lbrace>P' x\<rbrace> f x \<lbrace>\<lambda>_. Q\<rbrace>,\<lbrace>E\<rbrace>"
  shows "\<lbrakk>\<And>x s. (Q and P x) s \<Longrightarrow> P' x s \<rbrakk>
         \<Longrightarrow> \<lbrace>Q and (\<lambda>s. opt \<noteq> None \<longrightarrow> P (the opt) s)\<rbrace>
             (case opt of None \<Rightarrow> returnOk () | Some x \<Rightarrow> f x)
             \<lbrace>\<lambda>_. Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (cases opt; wpsimp)

lemma list_cases_weak_wp:
  assumes "\<lbrace>P_A\<rbrace> a \<lbrace>Q\<rbrace>"
  assumes "\<And>x xs. \<lbrace>P_B\<rbrace> b x xs \<lbrace>Q\<rbrace>"
  shows
  "\<lbrace>P_A and P_B\<rbrace>
    case ts of
      [] \<Rightarrow> a
    | x#xs \<Rightarrow> b x xs \<lbrace>Q\<rbrace>"
  apply (cases ts)
  apply (simp, rule hoare_weaken_pre, rule assms, simp)+
  done

lemmas hoare_FalseE_R = hoare_FalseE[where E="\<top>\<top>", folded validE_R_def]

lemma hoare_vcg_if_lift2:
  "\<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. (P rv s \<longrightarrow> X rv s) \<and> (\<not> P rv s \<longrightarrow> Y rv s)\<rbrace> \<Longrightarrow>
  \<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. if P rv s then X rv s else Y rv s\<rbrace>"

  "\<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. (P' rv \<longrightarrow> X rv s) \<and> (\<not> P' rv \<longrightarrow> Y rv s)\<rbrace> \<Longrightarrow>
  \<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv. if P' rv then X rv else Y rv\<rbrace>"
  by (auto simp: valid_def split_def)

lemma hoare_vcg_if_lift_ER: (* Required because of lack of rv in lifting rules *)
  "\<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. (P rv s \<longrightarrow> X rv s) \<and> (\<not> P rv s \<longrightarrow> Y rv s)\<rbrace>, - \<Longrightarrow>
  \<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. if P rv s then X rv s else Y rv s\<rbrace>, -"

  "\<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. (P' rv \<longrightarrow> X rv s) \<and> (\<not> P' rv \<longrightarrow> Y rv s)\<rbrace>, - \<Longrightarrow>
  \<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv. if P' rv then X rv else Y rv\<rbrace>, -"
  by (auto simp: valid_def validE_R_def validE_def split_def)

lemma hoare_vcg_imp_liftE:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>, \<lbrace>A\<rbrace>; \<lbrace>Q'\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>A\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s. \<not> P' s \<longrightarrow> Q' s\<rbrace> f \<lbrace>\<lambda>rv s. P rv s \<longrightarrow> Q rv s\<rbrace>, \<lbrace>A\<rbrace>"
  apply (simp only: imp_conv_disj)
  apply (clarsimp simp: validE_def valid_def split_def sum.case_eq_if)
  done

lemma hoare_list_all_lift:
  "(\<And>r. r \<in> set xs \<Longrightarrow> \<lbrace>Q r\<rbrace> f \<lbrace>\<lambda>rv. Q r\<rbrace>)
   \<Longrightarrow> \<lbrace>\<lambda>s. list_all (\<lambda>r. Q r s) xs\<rbrace> f \<lbrace>\<lambda>rv s. list_all (\<lambda>r. Q r s) xs\<rbrace>"
  apply (induct xs; simp)
  apply wpsimp
  apply (rule hoare_vcg_conj_lift; simp)
  done

lemma undefined_valid: "\<lbrace>\<bottom>\<rbrace> undefined \<lbrace>Q\<rbrace>"
  by (rule hoare_pre_cont)

lemma assertE_wp:
  "\<lbrace>\<lambda>s. F \<longrightarrow> Q () s\<rbrace> assertE F \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (rule hoare_pre)
   apply (unfold assertE_def)
   apply wp
  apply simp
  done

lemma doesn't_grow_proof:
  assumes y: "\<And>s. finite (S s)"
  assumes x: "\<And>x. \<lbrace>\<lambda>s. x \<notin> S s \<and> P s\<rbrace> f \<lbrace>\<lambda>rv s. x \<notin> S s\<rbrace>"
  shows      "\<lbrace>\<lambda>s. card (S s) < n \<and> P s\<rbrace> f \<lbrace>\<lambda>rv s. card (S s) < n\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "S b \<subseteq> S s")
   apply (drule card_mono [OF y], simp)
  apply clarsimp
  apply (rule ccontr)
  apply (subgoal_tac "x \<notin> S b", simp)
  apply (erule use_valid [OF _ x])
  apply simp
  done

lemma hoare_vcg_propE_R:
  "\<lbrace>\<lambda>s. P\<rbrace> f \<lbrace>\<lambda>rv s. P\<rbrace>, -"
  by (simp add: validE_R_def validE_def valid_def split_def split: sum.split)

lemma set_preserved_proof:
  assumes y: "\<And>x. \<lbrace>\<lambda>s. Q s \<and> x \<in> S s\<rbrace> f \<lbrace>\<lambda>rv s. x \<in> S s\<rbrace>"
  assumes x: "\<And>x. \<lbrace>\<lambda>s. Q s \<and> x \<notin> S s\<rbrace> f \<lbrace>\<lambda>rv s. x \<notin> S s\<rbrace>"
  shows      "\<lbrace>\<lambda>s. Q s \<and> P (S s)\<rbrace> f \<lbrace>\<lambda>rv s. P (S s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  by (metis (mono_tags, lifting) equalityI post_by_hoare subsetI x y)

lemma set_shrink_proof:
  assumes x: "\<And>x. \<lbrace>\<lambda>s. x \<notin> S s\<rbrace> f \<lbrace>\<lambda>rv s. x \<notin> S s\<rbrace>"
  shows
  "\<lbrace>\<lambda>s. \<forall>S'. S' \<subseteq> S s \<longrightarrow> P S'\<rbrace>
     f
   \<lbrace>\<lambda>rv s. P (S s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (drule spec, erule mp)
  apply (clarsimp simp: subset_iff)
  apply (rule ccontr)
  apply (drule(1) use_valid [OF _ x])
  apply simp
  done

lemma shrinks_proof:
  assumes y: "\<And>s. finite (S s)"
  assumes x: "\<And>x. \<lbrace>\<lambda>s. x \<notin> S s \<and> P s\<rbrace> f \<lbrace>\<lambda>rv s. x \<notin> S s\<rbrace>"
  assumes z: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. x \<notin> S s\<rbrace>"
  assumes w: "\<And>s. P s \<Longrightarrow> x \<in> S s"
  shows      "\<lbrace>\<lambda>s. card (S s) \<le> n \<and> P s\<rbrace> f \<lbrace>\<lambda>rv s. card (S s) < n\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "S b \<subset> S s")
   apply (drule psubset_card_mono [OF y], simp)
  apply (rule psubsetI)
   apply clarsimp
   apply (rule ccontr)
   apply (subgoal_tac "x \<notin> S b", simp)
   apply (erule use_valid [OF _ x])
   apply simp
  by (metis use_valid w z)

lemma use_validE_R:
  "\<lbrakk> (Inr r, s') \<in> fst (f s); \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-; P s \<rbrakk> \<Longrightarrow> Q r s'"
  unfolding validE_R_def validE_def
  by (frule(2) use_valid, simp)

lemma valid_preservation_ex:
  assumes x: "\<And>x P. \<lbrace>\<lambda>s. P (f s x :: 'b)\<rbrace> m \<lbrace>\<lambda>rv s. P (f s x)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (f s :: 'a \<Rightarrow> 'b)\<rbrace> m \<lbrace>\<lambda>rv s. P (f s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (erule subst[rotated, where P=P])
  apply (rule ext)
  apply (erule use_valid [OF _ x])
  apply simp
  done

lemmas valid_prove_more' = valid_prove_more[where Q="\<lambda>rv. Q" for Q]

lemma whenE_inv:
  assumes a: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  shows "\<lbrace>P\<rbrace> whenE Q f \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp wp: a)

lemma whenE_throwError_wp:
  "\<lbrace>\<lambda>s. \<not> P \<longrightarrow> Q s\<rbrace> whenE P (throwError e) \<lbrace>\<lambda>_. Q\<rbrace>, \<lbrace>\<top>\<top>\<rbrace>"
  by wpsimp

lemma ifM_throwError_returnOk:
  "\<lbrace>Q\<rbrace> test \<lbrace>\<lambda>c s. \<not> c \<longrightarrow> P s\<rbrace> \<Longrightarrow> \<lbrace>Q\<rbrace> ifM test (throwError e) (returnOk ()) \<lbrace>\<lambda>_. P\<rbrace>, -"
  by (fastforce simp: ifM_def returnOk_def throwError_def return_def validE_R_def valid_def
                      validE_def bind_def
               split: if_splits)

lemma ifME_liftE:
  "ifME (liftE test) a b = ifM test a b"
  by (simp add: ifME_def ifM_def liftE_bindE)

lemma gets_the_inv: "\<lbrace>P\<rbrace> gets_the V \<lbrace>\<lambda>rv. P\<rbrace>" by wpsimp

lemma select_f_inv:
  "\<lbrace>P\<rbrace> select_f S \<lbrace>\<lambda>_. P\<rbrace>"
  by (simp add: select_f_def valid_def)

lemmas state_unchanged = in_inv_by_hoareD [THEN sym]

lemma validI:
  assumes rl: "\<And>s r s'. \<lbrakk> P s; (r, s') \<in> fst (S s) \<rbrakk> \<Longrightarrow> Q r s'"
  shows "\<lbrace>P\<rbrace> S \<lbrace>Q\<rbrace>"
  unfolding valid_def using rl by safe

lemma opt_return_pres_lift:
  assumes x: "\<And>v. \<lbrace>P\<rbrace> f v \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> case x of None \<Rightarrow> return () | Some v \<Rightarrow> f v \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp wp: x)

lemma valid_return_unit:
  "\<lbrace>P\<rbrace> f >>= (\<lambda>_. return ()) \<lbrace>\<lambda>r. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. Q\<rbrace>"
  apply (rule validI)
  apply (fastforce simp: valid_def return_def bind_def split_def)
  done

lemma static_imp_wp:
  "\<lbrace>Q\<rbrace> m \<lbrace>R\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> Q s\<rbrace> m \<lbrace>\<lambda>rv s. P \<longrightarrow> R rv s\<rbrace>"
  by (cases P, simp_all add: valid_def)

lemma static_imp_wpE :
  "\<lbrace>Q\<rbrace> m \<lbrace>R\<rbrace>,- \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> Q s\<rbrace> m \<lbrace>\<lambda>rv s. P \<longrightarrow> R rv s\<rbrace>,-"
  by (cases P, simp_all)

lemma static_imp_conj_wp:
  "\<lbrakk> \<lbrace>Q\<rbrace> m \<lbrace>Q'\<rbrace>; \<lbrace>R\<rbrace> m \<lbrace>R'\<rbrace> \<rbrakk>
    \<Longrightarrow> \<lbrace>\<lambda>s. (P \<longrightarrow> Q s) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. (P \<longrightarrow> Q' rv s) \<and> R' rv s\<rbrace>"
  apply (rule hoare_vcg_conj_lift)
   apply (rule static_imp_wp)
   apply assumption+
  done

lemma hoare_eq_P:
  assumes "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  shows "\<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>_. (=) s\<rbrace>"
  by (rule assms)

lemma hoare_validE_R_conj:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, -; \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>, -\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q and R\<rbrace>, -"
  by (simp add: valid_def validE_def validE_R_def Let_def split_def split: sum.splits)

lemma hoare_vcg_const_imp_lift_R:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>\<lambda>s. F \<longrightarrow> P s\<rbrace> f \<lbrace>\<lambda>rv s. F \<longrightarrow> Q rv s\<rbrace>,-"
  by (cases F, simp_all)

lemma hoare_vcg_disj_lift_R:
  assumes x: "\<lbrace>P\<rbrace>  f \<lbrace>Q\<rbrace>,-"
  assumes y: "\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,-"
  shows      "\<lbrace>\<lambda>s. P s \<or> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<or> Q' rv s\<rbrace>,-"
  using assms
  by (fastforce simp: validE_R_def validE_def valid_def split: sum.splits)

lemmas throwError_validE_R = throwError_wp [where E="\<top>\<top>", folded validE_R_def]

lemma valid_case_option_post_wp:
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>\<lambda>rv. Q x\<rbrace>) \<Longrightarrow>
    \<lbrace>\<lambda>s. case ep of Some x \<Rightarrow> P x s | _ \<Rightarrow> True\<rbrace>
       f \<lbrace>\<lambda>rv s. case ep of Some x \<Rightarrow> Q x s | _ \<Rightarrow> True\<rbrace>"
  by (cases ep, simp_all add: hoare_vcg_prop)

lemma P_bool_lift:
  assumes t: "\<lbrace>Q\<rbrace> f \<lbrace>\<lambda>r. Q\<rbrace>"
  assumes f: "\<lbrace>\<lambda>s. \<not>Q s\<rbrace> f \<lbrace>\<lambda>r s. \<not>Q s\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (Q s)\<rbrace> f \<lbrace>\<lambda>r s. P (Q s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "Q b = Q s")
   apply simp
  apply (rule iffI)
   apply (rule classical)
   apply (drule (1) use_valid [OF _ f])
   apply simp
  apply (erule (1) use_valid [OF _ t])
  done

lemmas fail_inv = hoare_fail_any[where Q="\<lambda>_. P" and P=P for P]

lemma gets_sp: "\<lbrace>P\<rbrace> gets f \<lbrace>\<lambda>rv. P and (\<lambda>s. f s = rv)\<rbrace>"
  by (wp, simp)

lemma post_by_hoare2:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; (r, s') \<in> fst (f s); P s \<rbrakk> \<Longrightarrow> Q r s'"
  by (rule post_by_hoare, assumption+)

lemma hoare_Ball_helper:
  assumes x: "\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>"
  assumes y: "\<And>P. \<lbrace>\<lambda>s. P (S s)\<rbrace> f \<lbrace>\<lambda>rv s. P (S s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<forall>x \<in> S s. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x \<in> S s. Q x rv s\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "S b = S s")
   apply (erule post_by_hoare2 [OF x])
   apply (clarsimp simp: Ball_def)
  apply (erule_tac P1="\<lambda>x. x = S s" in post_by_hoare2 [OF y])
  apply (rule refl)
  done

lemma handy_prop_divs:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (Q s) \<and> S s\<rbrace> f \<lbrace>\<lambda>rv s. P (Q' rv s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (R s) \<and> S s\<rbrace> f \<lbrace>\<lambda>rv s. P (R' rv s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (Q s \<and> R s) \<and> S s\<rbrace> f \<lbrace>\<lambda>rv s. P (Q' rv s \<and> R' rv s)\<rbrace>"
             "\<lbrace>\<lambda>s. P (Q s \<or> R s) \<and> S s\<rbrace> f \<lbrace>\<lambda>rv s. P (Q' rv s \<or> R' rv s)\<rbrace>"
   apply (clarsimp simp: valid_def
                  elim!: subst[rotated, where P=P])
   apply (rule use_valid [OF _ x(1)], assumption)
   apply (rule use_valid [OF _ x(2)], assumption)
   apply simp
  apply (clarsimp simp: valid_def
                 elim!: subst[rotated, where P=P])
  apply (rule use_valid [OF _ x(1)], assumption)
  apply (rule use_valid [OF _ x(2)], assumption)
  apply simp
  done

lemma hoare_as_subst:
  "\<lbrakk> \<And>P. \<lbrace>\<lambda>s. P (fn s)\<rbrace> f \<lbrace>\<lambda>rv s. P (fn s)\<rbrace>;
     \<And>v :: 'a. \<lbrace>P v\<rbrace> f \<lbrace>Q v\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. P (fn s) s\<rbrace> f \<lbrace>\<lambda>rv s. Q (fn s) rv s\<rbrace>"
  by (rule hoare_lift_Pf3)

lemmas hoare_vcg_ball_lift = hoare_vcg_const_Ball_lift

lemma hoare_set_preserved:
  assumes x: "\<And>x. \<lbrace>fn' x\<rbrace> m \<lbrace>\<lambda>rv. fn x\<rbrace>"
  shows      "\<lbrace>\<lambda>s. set xs \<subseteq> {x. fn' x s}\<rbrace> m \<lbrace>\<lambda>rv s. set xs \<subseteq> {x. fn x s}\<rbrace>"
  apply (induct xs)
   apply simp
   apply wp
  apply simp
  apply (rule hoare_vcg_conj_lift)
   apply (rule x)
  apply assumption
  done

lemma hoare_ex_pre: (* safe, unlike hoare_vcg_ex_lift *)
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_ex_pre_conj:
  "(\<And>x. \<lbrace>\<lambda>s. P x s \<and> P' s\<rbrace> f \<lbrace>Q\<rbrace>)
  \<Longrightarrow> \<lbrace>\<lambda>s. (\<exists>x. P x s) \<and> P' s\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_conj_lift_inv:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>\<lambda>s. P' s \<and> I s\<rbrace> f \<lbrace>\<lambda>rv. I\<rbrace>;
   \<And>s. P s \<Longrightarrow> P' s\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> I s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> I s\<rbrace>"
   by (fastforce simp: valid_def)

lemma hoare_in_monad_post :
  assumes x: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>x. P\<rbrace>"
  shows      "\<lbrace>\<top>\<rbrace> f \<lbrace>\<lambda>rv s. (rv, s) \<in> fst (f s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "s = b", simp)
  apply (simp add: state_unchanged [OF x])
  done

lemma list_case_throw_validE_R:
  "\<lbrakk> \<And>y ys. xs = y # ys \<Longrightarrow> \<lbrace>P\<rbrace> f y ys \<lbrace>Q\<rbrace>,- \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> case xs of [] \<Rightarrow> throwError e | x # xs \<Rightarrow> f x xs \<lbrace>Q\<rbrace>,-"
  apply (case_tac xs, simp_all)
  apply wp
  done

lemma validE_R_sp:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  assumes y: "\<And>x. \<lbrace>Q x\<rbrace> g x \<lbrace>R\<rbrace>,-"
  shows "\<lbrace>P\<rbrace> f >>=E (\<lambda>x. g x) \<lbrace>R\<rbrace>,-"
  by (rule hoare_pre, wp x y, simp)

lemma valid_set_take_helper:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x \<in> set (xs rv s). Q x rv s\<rbrace>
    \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x \<in> set (take (n rv s) (xs rv s)). Q x rv s\<rbrace>"
  apply (erule hoare_strengthen_post)
  apply (clarsimp dest!: in_set_takeD)
  done

lemma whenE_throwError_sp:
  "\<lbrace>P\<rbrace> whenE Q (throwError e) \<lbrace>\<lambda>rv s. \<not> Q \<and> P s\<rbrace>, -"
  apply (simp add: whenE_def validE_R_def)
  apply (intro conjI impI; wp)
  done

lemma weaker_hoare_ifE:
  assumes x: "\<lbrace>P \<rbrace> a \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> b \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  shows      "\<lbrace>P and P'\<rbrace> if test then a else b \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (rule hoare_vcg_precond_impE)
   apply (wp x y)
  apply simp
  done

lemma wp_split_const_if:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>"
  shows "\<lbrace>\<lambda>s. (G \<longrightarrow> P s) \<and> (\<not> G \<longrightarrow> P' s)\<rbrace> f \<lbrace>\<lambda>rv s. (G \<longrightarrow> Q rv s) \<and> (\<not> G \<longrightarrow> Q' rv s)\<rbrace>"
  by (case_tac G, simp_all add: x y)

lemma wp_split_const_if_R:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  assumes y: "\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,-"
  shows "\<lbrace>\<lambda>s. (G \<longrightarrow> P s) \<and> (\<not> G \<longrightarrow> P' s)\<rbrace> f \<lbrace>\<lambda>rv s. (G \<longrightarrow> Q rv s) \<and> (\<not> G \<longrightarrow> Q' rv s)\<rbrace>,-"
  by (case_tac G, simp_all add: x y)

lemma wp_throw_const_imp:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  shows      "\<lbrace>\<lambda>s. G \<longrightarrow> P s\<rbrace> f \<lbrace>\<lambda>rv s. G \<longrightarrow> Q rv s\<rbrace>"
  by (case_tac G, simp_all add: x hoare_vcg_prop)

lemma wp_throw_const_impE:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  shows      "\<lbrace>\<lambda>s. G \<longrightarrow> P s\<rbrace> f \<lbrace>\<lambda>rv s. G \<longrightarrow> Q rv s\<rbrace>,\<lbrace>\<lambda>rv s. G \<longrightarrow> E rv s\<rbrace>"
  apply (case_tac G, simp_all add: x)
  apply wp
  done

lemma hoare_const_imp_R:
  "\<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,- \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> Q s\<rbrace> f \<lbrace>\<lambda>rv s. P \<longrightarrow> R rv s\<rbrace>,-"
  by (cases P, simp_all)

lemma hoare_vcg_imp_lift_R:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>, -; \<lbrace>Q'\<rbrace> f \<lbrace>Q\<rbrace>, - \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P' s \<or> Q' s\<rbrace> f \<lbrace>\<lambda>rv s. P rv s \<longrightarrow> Q rv s\<rbrace>, -"
  by (auto simp add: valid_def validE_R_def validE_def split_def split: sum.splits)

lemma hoare_disj_division:
  "\<lbrakk> P \<or> Q; P \<Longrightarrow> \<lbrace>R\<rbrace> f \<lbrace>S\<rbrace>; Q \<Longrightarrow> \<lbrace>T\<rbrace> f \<lbrace>S\<rbrace> \<rbrakk>
     \<Longrightarrow> \<lbrace>\<lambda>s. (P \<longrightarrow> R s) \<and> (Q \<longrightarrow> T s)\<rbrace> f \<lbrace>S\<rbrace>"
  apply safe
   apply (rule hoare_pre_imp)
    prefer 2
    apply simp
   apply simp
  apply (rule hoare_pre_imp)
   prefer 2
   apply simp
  apply simp
  done

lemma hoare_grab_asm:
  "\<lbrakk> G \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. G \<and> P s\<rbrace> f \<lbrace>Q\<rbrace>"
  by (cases G, simp+)

lemma hoare_grab_asm2:
  "(P' \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> R s\<rbrace> f \<lbrace>Q\<rbrace>)
  \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' \<and> R s\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_grab_exs:
  assumes x: "\<And>x. P x \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>"
  shows      "\<lbrace>\<lambda>s. \<exists>x. P x \<and> P' s\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (erule(2) use_valid [OF _ x])
  done

lemma hoare_prop_E: "\<lbrace>\<lambda>rv. P\<rbrace> f -,\<lbrace>\<lambda>rv s. P\<rbrace>"
  unfolding validE_E_def
  by (rule hoare_pre, wp, simp)

lemma hoare_vcg_conj_lift_R:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-; \<lbrace>R\<rbrace> f \<lbrace>S\<rbrace>,- \<rbrakk> \<Longrightarrow>
     \<lbrace>\<lambda>s. P s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> S rv s\<rbrace>,-"
  apply (simp add: validE_R_def validE_def)
  apply (drule(1) hoare_vcg_conj_lift)
  apply (erule hoare_strengthen_post)
  apply (clarsimp split: sum.splits)
  done

lemma hoare_walk_assmsE:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. P\<rbrace>" and y: "\<And>s. P s \<Longrightarrow> Q s" and z: "\<lbrace>P\<rbrace> g \<lbrace>\<lambda>rv. Q\<rbrace>"
  shows      "\<lbrace>P\<rbrace> doE x \<leftarrow> f; g odE \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (wp z)
   apply (simp add: validE_def)
   apply (rule hoare_strengthen_post [OF x])
   apply (auto simp: y split: sum.splits)
  done

lemma univ_wp:
  "\<lbrace>\<lambda>s. \<forall>(rv, s') \<in> fst (f s). Q rv s'\<rbrace> f \<lbrace>Q\<rbrace>"
  by (simp add: valid_def)

lemma univ_get_wp:
  assumes x: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. P\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<forall>(rv, s') \<in> fst (f s). s = s' \<longrightarrow> Q rv s'\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (rule hoare_pre_imp [OF _ univ_wp])
  apply clarsimp
  apply (drule bspec, assumption, simp)
  apply (subgoal_tac "s = b", simp)
  apply (simp add: state_unchanged [OF x])
  done

lemma result_in_set_wp :
  assumes x: "\<And>P. \<lbrace>P\<rbrace> fn \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "\<lbrace>\<lambda>s. True\<rbrace> fn \<lbrace>\<lambda>v s'. (v, s') \<in> fst (fn s')\<rbrace>"
  by (rule hoare_pre_imp [OF _ univ_get_wp], simp_all add: x split_def) clarsimp

lemma other_result_in_set_wp:
  assumes x: "\<And>P. \<lbrace>P\<rbrace> fn \<lbrace>\<lambda>rv. P\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<forall>(v, s) \<in> fst (fn s). F v = v\<rbrace> fn \<lbrace>\<lambda>v s'. (F v, s') \<in> fst (fn s')\<rbrace>"
  proof -
  have P: "\<And>v s. (F v = v) \<and> (v, s) \<in> fst (fn s) \<Longrightarrow> (F v, s) \<in> fst (fn s)"
    by simp
  show ?thesis
  apply (rule hoare_post_imp [OF P], assumption)
  apply (rule hoare_pre_imp)
  defer
   apply (rule hoare_vcg_conj_lift)
    apply (rule univ_get_wp [OF x])
   apply (rule result_in_set_wp [OF x])
  apply clarsimp
  apply (drule bspec, assumption, simp)
  done
  qed

lemma weak_if_wp:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow>
  \<lbrace>P and P'\<rbrace> f \<lbrace>\<lambda>r. if C r then Q r else Q' r\<rbrace>"
  by (auto simp add: valid_def split_def)

lemma weak_if_wp':
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. Q r and Q' r\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. if C r then Q r else Q' r\<rbrace>"
  by (auto simp add: valid_def split_def)

lemma bindE_split_recursive_asm:
  assumes x: "\<And>x s'. \<lbrakk> (Inr x, s') \<in> fst (f s) \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. B x s \<and> s = s'\<rbrace> g x \<lbrace>C\<rbrace>, \<lbrace>E\<rbrace>"
  shows      "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>, \<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>st. A st \<and> st = s\<rbrace> f >>=E g \<lbrace>C\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: validE_def valid_def bindE_def bind_def lift_def)
  apply (erule allE, erule(1) impE)
  apply (drule(1) bspec, simp)
  apply (case_tac a, simp_all add: throwError_def return_def)
  apply (drule x)
  apply (clarsimp simp: validE_def valid_def)
  apply (drule(1) bspec, simp)
  done

lemma validE_R_abstract_rv:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>rv'. Q rv' s\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  by (erule hoare_post_imp_R, simp)

lemma validE_cases_valid:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q (Inr rv) s\<rbrace>,\<lbrace>\<lambda>rv s. Q (Inl rv) s\<rbrace>
      \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (simp add: validE_def)
  apply (erule hoare_strengthen_post)
  apply (simp split: sum.split_asm)
  done

lemma liftM_pre:
  assumes rl: "\<lbrace>\<lambda>s. \<not> P s \<rbrace> a \<lbrace> \<lambda>_ _. False \<rbrace>"
  shows "\<lbrace>\<lambda>s. \<not> P s \<rbrace> liftM f a \<lbrace> \<lambda>_ _. False \<rbrace>"
  unfolding liftM_def
  apply (rule seq)
  apply (rule rl)
  apply wp
  apply simp
  done

lemma hoare_gen_asm':
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P' and (\<lambda>_. P)\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (auto intro: hoare_assume_pre)
  done

lemma hoare_gen_asm_conj:
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. P' s \<and> P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp: valid_def)


lemma hoare_add_K:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> I\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> I\<rbrace>"
  by (fastforce simp: valid_def)


lemma valid_rv_lift:
  "\<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. rv \<longrightarrow> Q rv s\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. rv \<longrightarrow> P \<and> Q rv s\<rbrace>"
  by (fastforce simp: valid_def)

lemma valid_imp_ex:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<exists>x. rv \<longrightarrow> Q rv s x\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. rv \<longrightarrow> (\<exists>x. Q rv s x)\<rbrace>"
  by (fastforce simp: valid_def)

lemma valid_rv_split:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. rv \<longrightarrow> Q s\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<not>rv \<longrightarrow> Q' s\<rbrace>\<rbrakk>
  \<Longrightarrow>
  \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. if rv then Q s else Q' s\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_rv_split:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. rv \<longrightarrow> (Q rv s)\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. (\<not>rv) \<longrightarrow> (Q rv s)\<rbrace>\<rbrakk>
  \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (case_tac a, fastforce+)
  done

lemma combine_validE: "\<lbrakk> \<lbrace> P \<rbrace> x \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>;
         \<lbrace> P' \<rbrace> x \<lbrace> Q' \<rbrace>,\<lbrace> E' \<rbrace> \<rbrakk> \<Longrightarrow>
         \<lbrace> P and P' \<rbrace> x \<lbrace> \<lambda>r. (Q r) and (Q' r) \<rbrace>,\<lbrace>\<lambda>r. (E r) and (E' r) \<rbrace>"
  apply (clarsimp simp: validE_def valid_def split: sum.splits)
  apply (erule allE, erule (1) impE)+
  apply (drule (1) bspec)+
  apply clarsimp
  done

lemma valid_case_prod:
  "\<lbrakk> \<And>x y. valid (P x y) (f x y) Q \<rbrakk> \<Longrightarrow> valid (case_prod P v) (case_prod (\<lambda>x y. f x y) v) Q"
  by (simp add: split_def)

lemma validE_case_prod:
  "\<lbrakk> \<And>x y. validE (P x y) (f x y) Q E \<rbrakk> \<Longrightarrow> validE (case_prod P v) (case_prod (\<lambda>x y. f x y) v) Q E"
  by (simp add: split_def)

lemma valid_pre_satisfies_post:
  "\<lbrakk> \<And>s r' s'. P s \<Longrightarrow> Q r' s' \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> m \<lbrace> Q \<rbrace>"
  by (clarsimp simp: valid_def)

lemma validE_pre_satisfies_post:
  "\<lbrakk> \<And>s r' s'. P s \<Longrightarrow> Q r' s'; \<And>s r' s'. P s \<Longrightarrow> R r' s' \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> m \<lbrace> Q \<rbrace>,\<lbrace> R \<rbrace>"
  by (clarsimp simp: validE_def2 split: sum.splits)

lemma hoare_validE_R_conjI:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, - ; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>, - \<rbrakk>  \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>, -"
  apply (clarsimp simp: Ball_def validE_R_def validE_def valid_def)
  by (case_tac a; fastforce)

lemma hoare_validE_E_conjI:
  "\<lbrakk> \<lbrace>P\<rbrace> f -, \<lbrace>Q\<rbrace> ; \<lbrace>P\<rbrace> f -, \<lbrace>Q'\<rbrace> \<rbrakk>  \<Longrightarrow> \<lbrace>P\<rbrace> f -, \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>"
  apply (clarsimp simp: Ball_def validE_E_def validE_def valid_def)
  by (case_tac a; fastforce)

lemma validE_R_post_conjD1:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> R r s\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  apply (clarsimp simp: validE_R_def validE_def valid_def)
  by (case_tac a; fastforce)

lemma validE_R_post_conjD2:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> R r s\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>,-"
  apply (clarsimp simp: validE_R_def validE_def valid_def)
  by (case_tac a; fastforce)

lemma throw_opt_wp[wp]:
  "\<lbrace>if v = None then E ex else Q (the v)\<rbrace> throw_opt ex v \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding throw_opt_def by wpsimp auto

lemma hoare_name_pre_state2:
  "(\<And>s. \<lbrace>P and ((=) s)\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (auto simp: valid_def intro: hoare_name_pre_state)

lemma returnOk_E': "\<lbrace>P\<rbrace> returnOk r -,\<lbrace>E\<rbrace>"
  by (clarsimp simp: returnOk_def validE_E_def validE_def valid_def return_def)

lemma throwError_R': "\<lbrace>P\<rbrace> throwError e \<lbrace>Q\<rbrace>,-"
  by (clarsimp simp:throwError_def validE_R_def validE_def valid_def return_def)

end