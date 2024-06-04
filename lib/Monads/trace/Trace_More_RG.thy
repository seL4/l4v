(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Partial correctness RG logic lemmas over the trace monad. RG quintuples, lifting lemmas, etc.
   If it doesn't contain a RG quintuple it likely doesn't belong in here. *)

theory Trace_More_RG
  imports
    Trace_RG
begin

lemma rg_take_disjunct:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P' rv s0 s \<and> (False \<or> P'' rv s0 s)\<rbrace>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>P''\<rbrace>"
  by (erule rg_strengthen_post, simp)

lemma rg_post_add:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>r s0 s. Q' r s0 s \<and> Q r s0 s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (erule rg_strengthen_post, simp)

lemma rg_post_addE:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_ s0 s. R s0 s \<and> Q s0 s\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_ s0 s. Q s0 s\<rbrace>,\<lbrace>E\<rbrace>"
  by (erule rg_strengthen_postE; simp)

lemma rg_pre_add:
  "(\<forall>s0 s. P s0 s \<longrightarrow> P' s0 s) \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<longleftrightarrow> \<lbrace>P and P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (subst iff_conv_conj_imp)
  by(intro conjI impI; rule rg_weaken_pre, assumption, clarsimp)

lemma rg_pre_addE:
  "(\<forall>s0 s. P s0 s \<longrightarrow> R s0 s) \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<longleftrightarrow> \<lbrace>P and R\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (subst iff_conv_conj_imp)
  by(intro conjI impI; rule rg_weaken_preE, assumption, clarsimp)

lemma rg_name_pre_state:
  "\<lbrakk> \<And>s0 s. P s0 s \<Longrightarrow> \<lbrace>\<lambda>_. (=) s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; prefix_closed f \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (clarsimp simp: validI_def)

lemma rg_name_pre_stateE:
  "\<lbrakk>\<And>s0 s. P s0 s \<Longrightarrow> \<lbrace>\<lambda>_. (=) s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; prefix_closed f\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (clarsimp simp: validIE_def2)

lemma rg_vcg_if_lift_strong:
  "\<lbrakk> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>P\<rbrace>; \<lbrace>\<lambda>s0 s. \<not> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<not> P rv s0 s\<rbrace>; \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>S'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s0 s. if P' s0 s then Q' s0 s else S' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. if P rv s0 s then Q rv s0 s else S rv s0 s\<rbrace>"

  "\<lbrakk> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>P\<rbrace>; \<lbrace>\<lambda>s0 s. \<not> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<not> P rv s0 s\<rbrace>; \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace> Q\<rbrace>; \<lbrace>S'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s0 s. if P' s0 s then Q' s0 s else S' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. (if P rv s0 s then Q rv else S rv) s0 s\<rbrace>"
  by (wpsimp wp: rg_vcg_imp_lift' | assumption | fastforce)+

lemma rg_vcg_imp_lift_pre_add:
  "\<lbrakk> \<lbrace>P and Q\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q' rv s0 s\<rbrace>; f \<lbrace>R\<rbrace>,\<lbrace>G\<rbrace>,\<lbrace>\<lambda>s0 s. \<not> Q s0 s\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q s0 s \<longrightarrow> Q' rv s0 s\<rbrace>"
  apply (rule rg_weaken_pre)
   apply (rule rg_vcg_imp_lift')
    apply fastforce
   apply fastforce
  apply clarsimp
  done

lemma rg_pre_tautI:
  "\<lbrakk> \<lbrace>A and P\<rbrace>,\<lbrace>R\<rbrace> a \<lbrace>G\<rbrace>,\<lbrace>B\<rbrace>; \<lbrace>A and not P\<rbrace>,\<lbrace>R\<rbrace> a \<lbrace>G\<rbrace>,\<lbrace>B\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace>,\<lbrace>R\<rbrace> a \<lbrace>G\<rbrace>,\<lbrace>B\<rbrace>"
  by (fastforce simp: validI_def)

lemma rg_lift_Pf_pre_conj:
  assumes P: "\<And>x. \<lbrace>\<lambda>s0 s. Q x s0 s\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>P x\<rbrace>"
  assumes f: "\<And>P. \<lbrace>\<lambda>s0 s. P (g s0 s) \<and> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_ s0 s. P (f s0 s)\<rbrace>"
  shows "\<lbrace>\<lambda>s0 s. Q (g s0 s) s0 s \<and> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P (f s0 s) rv s0 s\<rbrace>"
  apply (clarsimp simp: validI_def validI_prefix_closed[OF f] guar_by_rg[OF f])
  apply (rule use_validI[OF _ P], simp)
  apply (rule use_validI[OF _ f], simp+)
  done

lemmas rg_lift_Pf4 = rg_lift_Pf_pre_conj[where P'="\<top>\<top>", simplified]
lemmas rg_lift_Pf3 = rg_lift_Pf4[where f=f and g=f for f]
lemmas rg_lift_Pf2 = rg_lift_Pf3[where P="\<lambda>f _. P f" for P]
lemmas rg_lift_Pf = rg_lift_Pf2[where Q=P and P=P for P]

lemmas rg_lift_Pf3_pre_conj = rg_lift_Pf_pre_conj[where f=f and g=f for f]
lemmas rg_lift_Pf2_pre_conj = rg_lift_Pf3_pre_conj[where P="\<lambda>f _. P f" for P]
lemmas rg_lift_Pf_pre_conj' = rg_lift_Pf2_pre_conj[where Q=P and P=P for P]

lemma rg_if_r_and:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>r. if P' r then Q r else Q' r\<rbrace>
   = \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>r s0 s. (P' r \<longrightarrow> Q r s0 s) \<and> (\<not>P' r \<longrightarrow> Q' r s0 s)\<rbrace>"
  by (fastforce simp: validI_def)

lemma rg_convert_imp:
  "\<lbrakk> \<lbrace>\<lambda>s0 s. \<not> P s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<not> Q s0 s\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. P s0 s \<longrightarrow> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q s0 s \<longrightarrow> S rv s0 s\<rbrace>"
  apply (simp only: imp_conv_disj)
  apply (erule(1) rg_vcg_disj_lift)
  done

lemma rg_case_option_wpR:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f None \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<And>x. \<lbrace>P' x\<rbrace>,\<lbrace>R\<rbrace> f (Some x) \<lbrace>G\<rbrace>,\<lbrace>Q' x\<rbrace>,\<lbrace>E\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>case_option P P' v\<rbrace>,\<lbrace>R\<rbrace> f v \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. case v of None \<Rightarrow> Q rv | Some x \<Rightarrow> Q' x rv\<rbrace>,\<lbrace>E\<rbrace>"
  by (cases v) auto

lemma rg_exI_tuple:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>(rv,rv') s0 s. Q x rv rv' s0 s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>(rv,rv') s0 s. \<exists>x. Q x rv rv' s0 s\<rbrace>"
  by (fastforce simp: validI_def)

lemma rg_ex_all:
  "(\<forall>x. \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>) = \<lbrace>\<lambda>s0 s. \<exists>x. P x s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (rule iffI)
   apply (fastforce simp: validI_def)+
  done

lemma rg_imp_eq_substR:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. rv = x \<longrightarrow> Q x s0 s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp add: validI_def validIE_def split: sum.splits)

lemma rg_split_bind_case_sum:
  assumes x: "\<And>rv. \<lbrace>E rv\<rbrace>,\<lbrace>R\<rbrace> g rv \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
             "\<And>rv. \<lbrace>Q' rv\<rbrace>,\<lbrace>R\<rbrace> h rv \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace>"
  shows      "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f >>= case_sum g h \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (rule bind_twp[OF _ y[unfolded validIE_def]])
  apply (wpsimp wp: x split: sum.splits)
  done

lemma rg_split_bind_case_sumE:
  assumes x: "\<And>rv. \<lbrace>S' rv\<rbrace>,\<lbrace>R\<rbrace> g rv \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
             "\<And>rv. \<lbrace>S rv\<rbrace>,\<lbrace>R\<rbrace> h rv \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes y: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>,\<lbrace>S'\<rbrace>"
  shows      "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f >>= case_sum g h \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (unfold validIE_def)
  apply (rule bind_twp[OF _ y[unfolded validIE_def]])
  apply (wpsimp wp: x[unfolded validIE_def] split: sum.splits)
  done

lemma assertE_tsp:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> assertE Q \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q \<and> P s0 s\<rbrace>,\<lbrace>E\<rbrace>"
  by (wpsimp wp: assertE_wp)

lemma case_options_weak_twp:
  "\<lbrakk> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<And>x. \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> g x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>P and P'\<rbrace>,\<lbrace>R\<rbrace> case opt of None \<Rightarrow> f | Some x \<Rightarrow> g x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (cases opt)
   apply (clarsimp elim!: rg_weaken_pre)
  apply (rule rg_weaken_pre [where P'=P'])
   apply simp+
  done

lemma case_option_twp_None_return:
  assumes [wp]: "\<And>x. \<lbrace>P' x\<rbrace>,\<lbrace>R\<rbrace> f x \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>"
  shows "\<lbrakk>\<And>x s0 s. (Q and P x) s0 s \<Longrightarrow> P' x s0 s \<rbrakk>
         \<Longrightarrow> \<lbrace>Q and (\<lambda>s0 s. opt \<noteq> None \<longrightarrow> P (the opt) s0 s)\<rbrace>,\<lbrace>R\<rbrace>
             (case opt of None \<Rightarrow> return () | Some x \<Rightarrow> f x)
             \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>"
  by (cases opt; wpsimp)

lemma case_option_twp_None_returnOk:
  assumes [wp]: "\<And>x. \<lbrace>P' x\<rbrace>,\<lbrace>R\<rbrace> f x \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>,\<lbrace>E\<rbrace>"
  shows "\<lbrakk>\<And>x s0 s. (Q and P x) s0 s \<Longrightarrow> P' x s0 s \<rbrakk>
         \<Longrightarrow> \<lbrace>Q and (\<lambda>s0 s. opt \<noteq> None \<longrightarrow> P (the opt) s0 s)\<rbrace>,\<lbrace>R\<rbrace>
             (case opt of None \<Rightarrow> returnOk () | Some x \<Rightarrow> f x)
             \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (cases opt; wpsimp)

lemma list_cases_weak_twp:
  assumes "\<lbrace>P_A\<rbrace>,\<lbrace>R\<rbrace> a \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  assumes "\<And>x xs. \<lbrace>P_B\<rbrace>,\<lbrace>R\<rbrace> b x xs \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  shows
  "\<lbrace>P_A and P_B\<rbrace>,\<lbrace>R\<rbrace>
   case ts of
       [] \<Rightarrow> a
     | x#xs \<Rightarrow> b x xs
   \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (cases ts)
  apply (simp, rule rg_weaken_pre, rule assms, simp)+
  done

lemma rg_vcg_if_lift2:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. (Q rv s0 s \<longrightarrow> X rv s0 s) \<and> (\<not> Q rv s0 s \<longrightarrow> Y rv s0 s)\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. if Q rv s0 s then X rv s0 s else Y rv s0 s\<rbrace>"

  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. (Q' rv \<longrightarrow> X rv s0 s) \<and> (\<not> Q' rv \<longrightarrow> Y rv s0 s)\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. if Q' rv then X rv else Y rv\<rbrace>"
  by (auto simp: validI_def)

lemma rg_vcg_if_lift_ER: (* Required because of lack of rv in lifting rules *)
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. (Q rv s0 s \<longrightarrow> X rv s0 s) \<and> (\<not> Q rv s0 s \<longrightarrow> Y rv s0 s)\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. if Q rv s0 s then X rv s0 s else Y rv s0 s\<rbrace>,\<lbrace>E\<rbrace>"

  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. (Q' rv \<longrightarrow> X rv s0 s) \<and> (\<not> Q' rv \<longrightarrow> Y rv s0 s)\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. if Q' rv then X rv else Y rv\<rbrace>,\<lbrace>E\<rbrace>"
  by (auto simp: validI_def validIE_def)

lemma rg_list_all_lift:
  "\<lbrakk>\<And>r. r \<in> set xs \<Longrightarrow> \<lbrace>Q r\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv. Q r\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<top>\<top>\<top>\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. list_all (\<lambda>r. Q r s0 s) xs \<and> P s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. list_all (\<lambda>r. Q r s0 s) xs\<rbrace>"
  apply (rule validI_split[rotated, simplified pred_conj_def])
   apply assumption
  apply (induct xs; simp)
   apply wpsimp
  apply (rule rg_vcg_conj_lift; simp)
  done

lemma assertE_twp:
  "\<lbrace>\<lambda>s0 s. F \<longrightarrow> Q () s0 s\<rbrace>,\<lbrace>R\<rbrace> assertE F \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (rule rg_pre)
   apply (unfold assertE_def)
   apply wp
  apply simp
  done

(*If there is a use case which requires a specific guarantee then this rule could be extended with
  an extra assumption and precondition.*)
lemma rg_doesn't_grow_proof:
  assumes y: "\<And>s0 s. finite (S s0 s)"
  assumes x: "\<And>x. \<lbrace>\<lambda>s0 s. x \<notin> S s0 s \<and> P s0 s\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv s0 s. x \<notin> S s0 s\<rbrace>"
  shows      "\<lbrace>\<lambda>s0 s. card (S s0 s) < n \<and> P s0 s\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv s0 s. card (S s0 s) < n\<rbrace>"
  apply (clarsimp simp: validI_def validI_prefix_closed[OF x])
  apply (erule le_less_trans[rotated])
  apply (rule card_mono[OF y])
  apply clarsimp
  apply (rule ccontr)
  apply (drule (2) use_validI[OF _ x, OF _ conjI])
  apply simp
  done

lemma rg_vcg_propE_R:
  "prefix_closed f \<Longrightarrow> \<lbrace>\<lambda>s0 s. P\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv s0 s. P\<rbrace>,-"
  by (simp add: validIE_def validI_def split: sum.split)

lemma rg_set_preserved_proof:
  assumes y: "\<And>x. \<lbrace>\<lambda>s0 s. Q s0 s \<and> x \<in> S s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. x \<in> S s0 s\<rbrace>"
  assumes x: "\<And>x. \<lbrace>\<lambda>s0 s. Q s0 s \<and> x \<notin> S s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. x \<notin> S s0 s\<rbrace>"
  shows      "\<lbrace>\<lambda>s0 s. Q s0 s \<and> P (S s0 s)\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P (S s0 s)\<rbrace>"
  apply (clarsimp simp: validI_def)
  by (metis (mono_tags, lifting) equalityI validI_prefix_closed post_by_rg guar_by_rg subsetI x y)

(*If there is a use case which requires a specific guarantee then this rule could be extended with
  an extra assumption and precondition.*)
lemma rg_set_shrink_proof:
  assumes x: "\<And>x. \<lbrace>\<lambda>s0 s. x \<notin> S s0 s\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv s0 s. x \<notin> S s0 s\<rbrace>"
  shows
  "\<lbrace>\<lambda>s0 s. \<forall>S'. S' \<subseteq> S s0 s \<longrightarrow> P S'\<rbrace>,\<lbrace>R\<rbrace>
   f
   -,\<lbrace>\<lambda>rv s0 s. P (S s0 s)\<rbrace>"
  apply (clarsimp simp: validI_def validI_prefix_closed[OF x])
  apply (drule spec, erule mp)
  apply (clarsimp simp: subset_iff)
  apply (rule ccontr)
  apply (drule(1) use_validI [OF _ x])
  apply simp
  done

lemma rg_shrinks_proof:
  assumes y: "\<And>s0 s. finite (S s0 s)"
  assumes x: "\<And>x. \<lbrace>\<lambda>s0 s. x \<notin> S s0 s \<and> P s0 s\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv s0 s. x \<notin> S s0 s\<rbrace>"
  assumes z: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. x \<notin> S s0 s\<rbrace>"
  assumes w: "\<And>s0 s. P s0 s \<Longrightarrow> x \<in> S s0 s"
  shows      "\<lbrace>\<lambda>s0 s. card (S s0 s) \<le> n \<and> P s0 s\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv s0 s. card (S s0 s) < n\<rbrace>"
  apply (clarsimp simp: validI_def validI_prefix_closed[OF x])
  apply (erule less_le_trans[rotated])
  apply (rule psubset_card_mono[OF y])
  apply (rule psubsetI)
   apply clarsimp
   apply (rule ccontr)
   apply (drule (2) use_validI[OF _ x, OF _ conjI])
   apply simp
  by (metis use_validI w z)

lemma use_validIE_R':
  "\<lbrakk>(tr, Result (Inr r, s')) \<in> rely f R s0 s; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; P s0 s; s0' = last_st_tr tr s0\<rbrakk>
   \<Longrightarrow> Q r s0' s'"
  unfolding validIE_def
  by (frule(3) use_validI', simp)

lemmas use_validIE_R = use_validIE_R'[OF _ _ _ refl]

lemma use_validIE_guar:
  "\<lbrakk>(tr, res) \<in> rely f R s0 s; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; P s0 s\<rbrakk>
   \<Longrightarrow> guar_cond G s0 tr"
  unfolding validIE_def
  by (frule(2) use_validI_guar, simp)

lemma validI_preservation_ex:
  assumes x: "\<And>x P. \<lbrace>\<lambda>s0 s. P (f s0 s x :: 'b)\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P (f s0 s x)\<rbrace>"
  shows      "\<lbrace>\<lambda>s0 s. P (f s0 s :: 'a \<Rightarrow> 'b)\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P (f s0 s)\<rbrace>"
  apply (clarsimp simp: validI_def validI_prefix_closed[OF x] guar_by_rg[OF x])
  apply (erule subst[rotated, where P=P])
  apply (rule ext)
  apply (erule use_validI [OF _ x])
  apply simp
  done

lemma whenE_invI:
  assumes a: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>"
  shows "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> whenE Q f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp wp: a)

lemma ifM_throwError_returnOkI:
  "\<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> test \<lbrace>G\<rbrace>,\<lbrace>\<lambda>c s0 s. \<not> c \<longrightarrow> P s0 s\<rbrace>
   \<Longrightarrow> \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> ifM test (throwError e) (returnOk ()) \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>, -"
  unfolding ifM_def
  apply (fold liftE_bindE)
  apply wpsimp
   apply assumption
  apply simp
  done

lemmas state_unchanged_rg = in_inv_by_rgD [THEN sym]
lemmas last_state_unchanged_rg = last_st_in_inv_by_rgD [THEN sym]

(*FIXME MC: name? move (both this one and validI in More_VCG)*)
lemma validI_I:
  assumes px: "prefix_closed S"
  assumes gc: "\<And>s0 s tr res. \<lbrakk> P s0 s; (tr, res) \<in> (rely S R s0 s)\<rbrakk> \<Longrightarrow> guar_cond G s0 tr"
  assumes rl: "\<And>s0 s tr r s'. \<lbrakk> P s0 s; (tr, Result (r, s')) \<in> (rely S R s0 s) \<rbrakk> \<Longrightarrow> Q r (last_st_tr tr s0) s'"
  shows "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> S \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  unfolding validI_def using px gc rl by safe

lemma opt_return_pres_lift_rg:
  assumes x: "\<And>v. \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f v \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> case x of None \<Rightarrow> return () | Some v \<Rightarrow> f v \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp wp: x)

lemma rg_weak_lift_imp_conj:
  "\<lbrakk> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> m -,\<lbrace>Q'\<rbrace>; \<lbrace>P''\<rbrace>,\<lbrace>R\<rbrace> m -,\<lbrace>Q''\<rbrace>; \<lbrace>S\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>\<top>\<top>\<top>\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (P \<longrightarrow> P' s0 s) \<and> P'' s0 s \<and> S s0 s\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. (P \<longrightarrow> Q' rv s0 s) \<and> Q'' rv s0 s\<rbrace>"
  apply wp_pre
  apply (rule rg_vcg_conj_lift)
   apply (rule rg_weak_lift_imp; assumption)
   apply (rule validI_split; assumption)
  apply clarsimp
  done

lemma rg_eq_P:
  assumes "\<And>P. \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>"
  shows "\<lbrace>\<lambda>_. (=) s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_ _. (=) s\<rbrace>"
  by (rule assms)

lemma valid_case_option_post_twp:
  "\<lbrakk>\<And>x. \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv. Q x\<rbrace>\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s0 s. case ep of Some x \<Rightarrow> P x s0 s | _ \<Rightarrow> True\<rbrace>,\<lbrace>R\<rbrace>
   f
   -,\<lbrace>\<lambda>rv s0 s. case ep of Some x \<Rightarrow> Q x s0 s | _ \<Rightarrow> True\<rbrace>"
  by (cases ep; fastforce simp: rg_TrueI)

lemma P_bool_lift:
  assumes t: "\<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>r. Q\<rbrace>"
  assumes f: "\<lbrace>\<lambda>s0 s. \<not>Q s0 s\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>r s0 s. \<not>Q s0 s\<rbrace>"
  shows "\<lbrace>\<lambda>s0 s. P (Q s0 s)\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>r s0 s. P (Q s0 s)\<rbrace>"
  apply (clarsimp simp: validI_def validI_prefix_closed[OF f])
  apply (rule back_subst[where P=P], assumption)
  apply (rule iffI)
   apply (erule (1) use_validI [OF _ t])
  apply (rule classical)
  apply (drule (1) use_validI [OF _ f])
  apply simp
  done

lemma gets_sp: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> gets f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. P and (\<lambda>s0 s. f s = rv)\<rbrace>"
  by (wp, simp)

lemma post_by_rg2:
  "\<lbrakk>\<lbrace>P\<rbrace>, \<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>, \<lbrace>Q\<rbrace>; (tr, Result (rv, s')) \<in> rely f R s0 s; P s0 s\<rbrakk>
  \<Longrightarrow> Q rv (last_st_tr tr s0) s'"
  by (rule post_by_rg, assumption+)

lemma rg_Ball_helper:
  assumes x: "\<And>x. \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>Q x\<rbrace>"
  assumes y: "\<And>P. \<lbrace>\<lambda>s0 s. P (S s0 s)\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv s0 s. P (S s0 s)\<rbrace>"
  shows "\<lbrace>\<lambda>s0 s. \<forall>x \<in> S s0 s. P x s0 s\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv s0 s. \<forall>x \<in> S s0 s. Q x rv s0 s\<rbrace>"
  apply (clarsimp simp: validI_def validI_prefix_closed[OF x])
  apply (drule bspec, erule back_subst[where P="\<lambda>A. x\<in>A" for x])
   apply (erule post_by_rg[OF y, rotated])
   apply (rule refl)
  apply (erule (1) post_by_rg[OF x])
  done

lemma handy_prop_divs_rg:
  assumes x: "\<And>P. \<lbrace>\<lambda>s0 s. P (Q s0 s) \<and> S s0 s\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv s0 s. P (Q' rv s0 s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s0 s. P (T s0 s) \<and> S s0 s\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv s0 s. P (T' rv s0 s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s0 s. P (Q s0 s \<and> T s0 s) \<and> S s0 s\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv s0 s. P (Q' rv s0 s \<and> T' rv s0 s)\<rbrace>"
             "\<lbrace>\<lambda>s0 s. P (Q s0 s \<or> T s0 s) \<and> S s0 s\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv s0 s. P (Q' rv s0 s \<or> T' rv s0 s)\<rbrace>"
   apply (clarsimp simp: validI_def validI_prefix_closed[OF x(1)]
                  elim!: subst[rotated, where P=P])
   apply (rule use_validI [OF _ x(1)], assumption)
   apply (rule use_validI [OF _ x(2)], assumption)
   apply simp
  apply (clarsimp simp: validI_def validI_prefix_closed[OF x(1)]
                 elim!: subst[rotated, where P=P])
  apply (rule use_validI [OF _ x(1)], assumption)
  apply (rule use_validI [OF _ x(2)], assumption)
  apply simp
  done

lemma rg_as_subst:
  "\<lbrakk> \<And>P. \<lbrace>\<lambda>s0 s. P (fn s0 s)\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P (fn s0 s)\<rbrace>;
     \<And>v :: 'a. \<lbrace>P v\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q v\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s0 s. P (fn s0 s) s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q (fn s0 s) rv s0 s\<rbrace>"
  by (rule rg_lift_Pf3)

lemmas rg_vcg_ball_lift = rg_vcg_const_Ball_lift

lemma rg_set_preserved:
  assumes x: "\<And>x. \<lbrace>fn' x\<rbrace>,\<lbrace>R\<rbrace> m -,\<lbrace>\<lambda>rv. fn x\<rbrace>"
  shows      "\<lbrace>\<lambda>s0 s. set xs \<subseteq> {x. fn' x s0 s}\<rbrace>,\<lbrace>R\<rbrace> m -,\<lbrace>\<lambda>rv s0 s. set xs \<subseteq> {x. fn x s0 s}\<rbrace>"
  apply (induct xs)
   apply (simp add: rg_TrueI validI_prefix_closed[OF x])
  apply simp
  apply (rule rg_vcg_conj_lift)
   apply (rule x)
  apply assumption
  done

lemma rg_ex_pre: (* safe, unlike rg_vcg_ex_lift *)
  "(\<And>x. \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s0 s. \<exists>x. P x s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (fastforce simp: validI_def)

lemma rg_ex_pre_conj:
  "\<lbrakk>\<And>x. \<lbrace>\<lambda>s0 s. P x s0 s \<and> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (\<exists>x. P x s0 s) \<and> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (fastforce simp: validI_def)

lemma rg_conj_lift_inv:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>\<lambda>s0 s. P' s0 s \<and> I s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. I\<rbrace>;
    \<And>s0 s. P s0 s \<Longrightarrow> P' s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. P s0 s \<and> I s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<and> I s0 s\<rbrace>"
   by (fastforce simp: validI_def)

lemma rg_in_rely_post:
  assumes x: "\<And>P. \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>x. P\<rbrace>"
  shows      "\<lbrace>\<top>\<top>\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv s0 s. (rv, s) \<in> mres (rely f R s0 s)\<rbrace>"
  apply (clarsimp simp: validI_def validI_prefix_closed[OF x])
  apply (rule back_subst[where P="\<lambda>s0. x\<in>mres (rely f R s0 s)" for x s])
   apply (rule back_subst[where P="\<lambda>s. x\<in>mres (rely f R s0 s)" for x s0])
   apply (drule in_mres, assumption)
   apply (simp add: state_unchanged_rg[OF x])
  apply (simp add: last_state_unchanged_rg[OF x])
  done

lemma list_case_throw_validIE_R:
  "\<lbrakk> \<And>y ys. xs = y # ys \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f y ys \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,- \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> case xs of [] \<Rightarrow> throwError e | x # xs \<Rightarrow> f x xs \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,-"
  apply (cases xs, simp_all)
  apply wp
  done

lemma validI_set_take_helper:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<forall>x \<in> set (xs rv s0 s). Q x rv s0 s\<rbrace>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<forall>x \<in> set (take (n rv s0 s) (xs rv s0 s)). Q x rv s0 s\<rbrace>"
  apply (erule rg_strengthen_post)
  apply (clarsimp dest!: in_set_takeD)
  done

lemma whenE_throwError_tsp:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> whenE Q (throwError e) \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<not> Q \<and> P s0 s\<rbrace>, -"
  apply (simp add: whenE_def)
  apply (intro conjI impI; wp)
  done

lemma weaker_rg_ifE:
  assumes x: "\<lbrace>P \<rbrace>,\<lbrace>R\<rbrace> a \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> b \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  shows      "\<lbrace>P and P'\<rbrace>,\<lbrace>R\<rbrace> if test then a else b \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (rule rg_weaken_preE)
   apply (wp x y)
  apply simp
  done

lemma twp_split_const_if:
  assumes x: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>"
  shows "\<lbrace>\<lambda>s0 s. (S \<longrightarrow> P s0 s) \<and> (\<not> S \<longrightarrow> P' s0 s)\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. (S \<longrightarrow> Q rv s0 s) \<and> (\<not> S \<longrightarrow> Q' rv s0 s)\<rbrace>"
  by (cases S, simp_all add: x y)

lemma twp_split_const_ifE_R:
  assumes x: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace>"
  shows "\<lbrace>\<lambda>s0 s. (S \<longrightarrow> P s0 s) \<and> (\<not> S \<longrightarrow> P' s0 s)\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. (S \<longrightarrow> Q rv s0 s) \<and> (\<not> S \<longrightarrow> Q' rv s0 s)\<rbrace>,\<lbrace>E\<rbrace>"
  by (cases S, simp_all add: x y)

lemma rg_disj_division:
  "\<lbrakk> P \<or> P'; P \<Longrightarrow> \<lbrace>S\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; P' \<Longrightarrow> \<lbrace>T\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (P \<longrightarrow> S s0 s) \<and> (P' \<longrightarrow> T s0 s)\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (fastforce intro: rg_weaken_pre)

lemma rg_grab_asm:
  "\<lbrakk> P' \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<not> P' \<Longrightarrow> prefix_closed f \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s0 s. P' \<and> P s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (cases P'; simp)

lemma rg_grab_asm2:
  "\<lbrakk>P' \<Longrightarrow> \<lbrace>\<lambda>s0 s. P s0 s \<and> P'' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<not> P' \<Longrightarrow> prefix_closed f\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. P s0 s \<and> P' \<and> P'' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (fastforce simp: validI_def)

lemma rg_grab_exs:
  assumes x: "\<And>x. P x \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  assumes y: "prefix_closed f"
  shows      "\<lbrace>\<lambda>s0 s. \<exists>x. P x \<and> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (clarsimp simp: validI_def y use_validI_guar[OF _ x])
  apply (erule(2) use_validI [OF _ x])
  done

lemma rg_prop_E:
  "prefix_closed f \<Longrightarrow> \<lbrace>\<lambda>s0 s. P\<rbrace>,\<lbrace>R\<rbrace> f -,-,\<lbrace>\<lambda>rv s0 s. P\<rbrace>"
  by wpsimp

lemma rg_walk_assmsE:
  assumes x: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. P\<rbrace>" and y: "\<And>s0 s. P s0 s \<Longrightarrow> Q s0 s" and z: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. Q\<rbrace>"
  shows      "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> doE x \<leftarrow> f; g odE \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (wp z)
   apply (simp add: validIE_def)
   apply (rule rg_strengthen_post [OF x])
   apply (auto simp: y split: sum.splits)
  done

(*FIXME MC: it is not immediately obvious what the validI equivalent of these rules should be, so I
          think it is best to leave them until we have a specific use case.
lemma univ_twp:
  "prefix_closed f \<Longrightarrow> \<lbrace>\<lambda>s0 s. \<forall>(rv, s') \<in> mres (rely f R s0 s). Q rv s0 s'\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>Q\<rbrace>"
  by (simp add: validI_def)

lemma univ_get_twp:
  assumes x: "\<And>P. \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. P\<rbrace>"
  shows "\<lbrace>\<lambda>s0 s. \<forall>(rv, s0 s') \<in> mres (f s0 s). s0 s = s0 s' \<longrightarrow> Q rv s0 s'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (rule rg_pre_imp[OF _ univ_wp])
  apply clarsimp
  apply (drule bspec, assumption, simp)
  apply (drule mp)
   apply (simp add: state_unchanged[OF x])
  apply simp
  done

lemma other_rg_in_monad_post:
  assumes x: "\<And>P. \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> fn \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. P\<rbrace>"
  shows "\<lbrace>\<lambda>s0 s. \<forall>(v, s0 s) \<in> mres (fn s0 s). F v = v\<rbrace>,\<lbrace>R\<rbrace> fn \<lbrace>G\<rbrace>,\<lbrace>\<lambda>v s0 s'. (F v, s0 s') \<in> mres (fn s0 s')\<rbrace>"
  proof -
  have P: "\<And>v s0 s. (F v = v) \<and> (v, s0 s) \<in> mres (fn s0 s) \<Longrightarrow> (F v, s0 s) \<in> mres (fn s0 s)"
    by simp
  show ?thesis
  apply (rule rg_post_imp [OF P], assumption)
  apply (rule rg_pre_imp)
  defer
   apply (rule rg_vcg_conj_lift)
    apply (rule univ_get_wp [OF x])
   apply (rule rg_in_monad_post [OF x])
  apply clarsimp
  apply (drule bspec, assumption, simp)
  done
  qed*)

lemma weak_if_twp:
  "\<lbrakk> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>P and P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>r. if C r then Q r else Q' r\<rbrace>"
  by (auto simp: validI_def)

lemma weak_if_twp':
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>r. Q r and Q' r\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>r. if C r then Q r else Q' r\<rbrace>"
  by (auto simp: validI_def)

lemma validE_R_abstract_rv:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<forall>rv'. Q rv' s0 s\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (erule rg_strengthen_postE; simp)

lemma validIE_cases_validI:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q (Inr rv) s0 s\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q (Inl rv) s0 s\<rbrace>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (simp add: validIE_def)
  apply (erule rg_strengthen_post)
  apply (simp split: sum.split_asm)
  done

lemma liftM_pre_rg:
  assumes rl: "\<lbrace>\<lambda>s0 s. \<not> P s0 s \<rbrace>,\<lbrace>R\<rbrace> a \<lbrace>G\<rbrace>,\<lbrace> \<lambda>_ _ _. False \<rbrace>"
  shows "\<lbrace>\<lambda>s0 s. \<not> P s0 s \<rbrace>,\<lbrace>R\<rbrace> liftM f a \<lbrace>G\<rbrace>,\<lbrace> \<lambda>_ _ _. False \<rbrace>"
  unfolding liftM_def
  apply (rule bind_twp_fwd)
   apply (rule rl)
  apply wp
  done

lemma rg_gen_asm_conj:
  "\<lbrakk>P \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<not> P \<Longrightarrow> prefix_closed f\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s0 s. P' s0 s \<and> P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (fastforce simp: validI_def)

lemma rg_add_K:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s0 s. P s0 s \<and> I\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<and> I\<rbrace>"
  by (fastforce simp: validI_def)

lemma valid_rv_lift:
  "\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. rv \<longrightarrow> Q rv s0 s\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s0 s. P \<and> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. rv \<longrightarrow> P \<and> Q rv s0 s\<rbrace>"
  by (fastforce simp: validI_def)

lemma valid_rv_split:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. rv \<longrightarrow> Q s0 s\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<not>rv \<longrightarrow> Q' s0 s\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. if rv then Q s0 s else Q' s0 s\<rbrace>"
  by (fastforce simp: validI_def)

lemma rg_rv_split:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. rv \<longrightarrow> (Q rv s0 s)\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. (\<not>rv) \<longrightarrow> (Q rv s0 s)\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (clarsimp simp: validI_def)
  by (metis (full_types))

lemma combine_validE:
  "\<lbrakk> \<lbrace> P \<rbrace>,\<lbrace>R\<rbrace> x \<lbrace>G\<rbrace>,\<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>; \<lbrace> P' \<rbrace>,\<lbrace>R\<rbrace> x \<lbrace>G\<rbrace>,\<lbrace> Q' \<rbrace>,\<lbrace> E' \<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace> P and P' \<rbrace>,\<lbrace>R\<rbrace> x \<lbrace>G\<rbrace>,\<lbrace> \<lambda>r. Q r and Q' r \<rbrace>,\<lbrace>\<lambda>r. E r and E' r \<rbrace>"
  apply (clarsimp simp: validIE_def validI_def split: sum.splits)
  done

lemma validI_case_prod:
  "\<lbrakk> \<And>x y. validI (P x y) R (f x y) G Q \<rbrakk> \<Longrightarrow> validI (case_prod P v) R (case_prod (\<lambda>x y. f x y) v) G Q"
  by (simp add: split_def)

lemma validIE_case_prod:
  "\<lbrakk> \<And>x y. validIE (P x y) R (f x y) G Q E \<rbrakk> \<Longrightarrow> validIE (case_prod P v) R (case_prod (\<lambda>x y. f x y) v) G Q E"
  by (simp add: split_def)

lemma rg_validIE_E_conjI:
  "\<lbrakk> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E'\<rbrace> \<rbrakk>  \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv s0 s. E rv s0 s \<and> E' rv s0 s\<rbrace>"
  by (fastforce simp: validIE_def validI_def split: sum.splits)

lemma validIE_R_post_conjD1:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>r s0 s. Q r s0 s \<and> Q' r s0 s\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validIE_def validI_def split: sum.splits)

lemma validIE_R_post_conjD2:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>r s0 s. Q r s0 s \<and> Q' r s0 s\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validIE_def validI_def split: sum.splits)

lemma rg_name_pre_state2:
  "(\<And>s. \<lbrace>\<lambda>s0' s'. P s0' s' \<and> (s' = s)\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (auto simp: validI_def)

end