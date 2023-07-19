(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Total correctness Hoare logic for the Trace_Monad (= valid + no_fail) *)

theory Trace_Total
  imports Trace_No_Fail
begin

section \<open>Total correctness for Trace_Monad and Trace_Monad with exceptions\<close>

subsection Definitions

text \<open>
  It is often desired to prove non-failure and a Hoare triple simultaneously, as the reasoning
  is often similar. The following definitions allow such reasoning to take place.\<close>

definition validNF ::
  "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) tmonad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>!") where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>! \<equiv> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<and> no_fail P f"

lemma validNF_alt_def:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>! = (\<forall>s. P s \<longrightarrow> ((\<forall>(r', s') \<in> mres (f s). Q r' s') \<and> Failed \<notin> snd ` (f s)))"
  by (auto simp: validNF_def valid_def no_fail_def)

definition validE_NF ::
  "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'a + 'b) tmonad \<Rightarrow> ('b \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace>/ _ /(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>!)") where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>! \<equiv> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace> \<and> no_fail P f"

lemma validE_NF_alt_def:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>! = \<lbrace>P\<rbrace> f \<lbrace>\<lambda>v s. case v of Inl e \<Rightarrow> E e s | Inr r \<Rightarrow> Q r s\<rbrace>!"
  by (clarsimp simp: validE_NF_def validE_def validNF_def)


subsection \<open>@{method wpc} setup\<close>

lemma wpc_helper_validNF:
  "\<lbrace>Q\<rbrace> g \<lbrace>S\<rbrace>! \<Longrightarrow> wpc_helper (P, P', P'') (Q, Q', Q'') \<lbrace>P\<rbrace> g \<lbrace>S\<rbrace>!"
  unfolding wpc_helper_def
  by clarsimp (metis hoare_vcg_precond_imp no_fail_pre validNF_def)

wpc_setup "\<lambda>m. \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>!" wpc_helper_validNF


subsection \<open>Basic @{const validNF} theorems\<close>

lemma validNF[intro?]: (* FIXME lib: should be validNFI *)
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>; no_fail P f \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>!"
  by (clarsimp simp: validNF_def)

lemma validNF_valid:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>"
  by (clarsimp simp: validNF_def)

lemma validNF_no_fail:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>! \<rbrakk> \<Longrightarrow> no_fail P f"
  by (clarsimp simp: validNF_def)

lemma snd_validNF:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>!; P s \<rbrakk> \<Longrightarrow> Failed \<notin> snd ` (f s)"
  by (clarsimp simp: validNF_def no_fail_def)

lemma use_validNF:
  "\<lbrakk> (r', s') \<in> mres (f s); \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>!; P s \<rbrakk> \<Longrightarrow> Q r' s'"
  by (fastforce simp: validNF_def valid_def)


subsection \<open>@{const validNF} weakest precondition rules\<close>

lemma validNF_return[wp]:
  "\<lbrace> P x \<rbrace> return x \<lbrace> P \<rbrace>!"
  by (wp validNF)+

lemma validNF_get[wp]:
  "\<lbrace> \<lambda>s. P s s  \<rbrace> get \<lbrace> P \<rbrace>!"
  by (wp validNF)+

lemma validNF_put[wp]:
  "\<lbrace> \<lambda>s. P () x  \<rbrace> put x \<lbrace> P \<rbrace>!"
  by (wp validNF)+

lemma validNF_K_bind[wp]:
  "\<lbrace> P \<rbrace> x \<lbrace> Q \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> K_bind x f \<lbrace> Q \<rbrace>!"
  by simp

lemma validNF_fail[wp]:
  "\<lbrace> \<lambda>s. False \<rbrace> fail \<lbrace> Q \<rbrace>!"
  by (clarsimp simp: validNF_def fail_def no_fail_def)

lemma validNF_prop[wp_unsafe]:
  "\<lbrakk> no_fail (\<lambda>s. P) f \<rbrakk> \<Longrightarrow> \<lbrace> \<lambda>s. P \<rbrace> f \<lbrace> \<lambda>rv s. P \<rbrace>!"
  by (wp validNF)+

lemma validNF_post_conj[intro!]:
  "\<lbrakk> \<lbrace> P \<rbrace> a \<lbrace> Q \<rbrace>!; \<lbrace> P \<rbrace> a \<lbrace> R \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> a \<lbrace> Q and R \<rbrace>!"
  by (auto simp: validNF_def)

lemma validNF_pre_disj[intro!]:
  "\<lbrakk> \<lbrace> P \<rbrace> a \<lbrace> R \<rbrace>!; \<lbrace> Q \<rbrace> a \<lbrace> R \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace> P or Q \<rbrace> a \<lbrace> R \<rbrace>!"
  by (rule validNF) (auto dest: validNF_valid validNF_no_fail intro: no_fail_or)

text \<open>
  Set up combination rules for @{method wp}, which also requires a @{text wp_trip} rule for
  @{const validNF}.\<close>
definition validNF_property :: "('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> ('s,'a) tmonad \<Rightarrow> bool" where
  "validNF_property Q s b \<equiv> Failed \<notin> snd ` (b s) \<and> (\<forall>(r', s') \<in> mres (b s). Q r' s')"

lemma validNF_is_triple[wp_trip]:
  "validNF P f Q = triple_judgement P f (validNF_property Q)"
  by (auto simp: validNF_def triple_judgement_def validNF_property_def no_fail_def valid_def)

lemma validNF_weaken_pre[wp_pre]:
  "\<lbrakk>\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>!; \<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>!"
  by (metis hoare_pre_imp no_fail_pre validNF_def)

lemma validNF_post_comb_imp_conj:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>!; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>!"
  by (fastforce simp: validNF_def valid_def)

lemma validNF_post_comb_conj_L:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>!"
  by (fastforce simp: validNF_def valid_def no_fail_def)

lemma validNF_post_comb_conj_R:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>!"
  by (fastforce simp: validNF_def valid_def no_fail_def)

lemma validNF_post_comb_conj:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>!"
  by (fastforce simp: validNF_def valid_def no_fail_def)

lemma validNF_if_split[wp_split]:
  "\<lbrakk>P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>S\<rbrace>!; \<not> P \<Longrightarrow> \<lbrace>R\<rbrace> g \<lbrace>S\<rbrace>!\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not> P \<longrightarrow> R s)\<rbrace> if P then f else g \<lbrace>S\<rbrace>!"
  by simp

lemma validNF_vcg_conj_lift:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>!"
  by (fastforce intro!: validNF_post_conj[unfolded pred_conj_def] intro: validNF_weaken_pre)

lemma validNF_vcg_disj_lift:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<or> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<or> Q' rv s\<rbrace>!"
  by (auto  simp: validNF_def no_fail_def intro!: hoare_vcg_disj_lift)

lemma validNF_vcg_all_lift[wp]:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>!"
  by (auto simp: validNF_def no_fail_def intro!: hoare_vcg_all_lift)

lemma validNF_bind[wp_split]:
  "\<lbrakk> \<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>!; \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>C\<rbrace>!"
  unfolding validNF_def
  by (auto intro: hoare_seq_ext no_fail_bind[where P=Q and Q=Q for Q, simplified])

lemmas validNF_seq_ext = validNF_bind


subsection "validNF compound rules"

lemma validNF_state_assert[wp]:
  "\<lbrace> \<lambda>s. P () s \<and> G s  \<rbrace> state_assert G \<lbrace> P \<rbrace>!"
  apply (rule validNF)
  apply wpsimp
  apply (clarsimp simp: no_fail_def state_assert_def
              bind_def2 assert_def return_def get_def)
  done

lemma validNF_modify[wp]:
  "\<lbrace> \<lambda>s. P () (f s) \<rbrace> modify f \<lbrace> P \<rbrace>!"
  apply (clarsimp simp: modify_def)
  apply wp
  done

lemma validNF_gets[wp]:
  "\<lbrace>\<lambda>s. P (f s) s\<rbrace> gets f \<lbrace>P\<rbrace>!"
  apply (clarsimp simp: gets_def)
  apply wp
  done

lemma validNF_condition[wp]:
  "\<lbrakk> \<lbrace> Q \<rbrace> A \<lbrace>P\<rbrace>!; \<lbrace> R \<rbrace> B \<lbrace>P\<rbrace>!\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. if C s then Q s else R s\<rbrace> condition C A B \<lbrace>P\<rbrace>!"
  apply rule
   apply (drule validNF_valid)+
   apply (erule (1) condition_wp)
  apply (drule validNF_no_fail)+
  apply (clarsimp simp: no_fail_def condition_def)
  done

lemma validNF_assert[wp]:
    "\<lbrace> (\<lambda>s. P) and (R ()) \<rbrace> assert P \<lbrace> R \<rbrace>!"
  apply (rule validNF)
   apply (clarsimp simp: valid_def in_return)
  apply (clarsimp simp: no_fail_def return_def)
  done

lemma validNF_false_pre:
  "\<lbrace> \<lambda>_. False \<rbrace> P \<lbrace> Q \<rbrace>!"
  by (clarsimp simp: validNF_def no_fail_def)

lemma validNF_chain:
   "\<lbrakk>\<lbrace>P'\<rbrace> a \<lbrace>R'\<rbrace>!; \<And>s. P s \<Longrightarrow> P' s; \<And>r s. R' r s \<Longrightarrow> R r s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>!"
  by (fastforce simp: validNF_def valid_def no_fail_def Ball_def)

lemma validNF_case_prod[wp]:
  "\<lbrakk> \<And>x y. validNF (P x y) (B x y) Q \<rbrakk> \<Longrightarrow> validNF (case_prod P v) (case_prod (\<lambda>x y. B x y) v) Q"
  by (metis prod.exhaust split_conv)

lemma validE_NF_case_prod[wp]:
    "\<lbrakk> \<And>a b. \<lbrace>P a b\<rbrace> f a b \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>! \<rbrakk> \<Longrightarrow>
          \<lbrace>case x of (a, b) \<Rightarrow> P a b\<rbrace> case x of (a, b) \<Rightarrow> f a b \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>!"
  apply (clarsimp simp: validE_NF_alt_def)
  apply (erule validNF_case_prod)
  done

lemma no_fail_is_validNF_True: "no_fail P s = (\<lbrace> P \<rbrace> s \<lbrace> \<lambda>_ _. True \<rbrace>!)"
  by (clarsimp simp: no_fail_def validNF_def valid_def)


subsection \<open>@{const validNF} reasoning in the exception monad\<close>

lemma validE_NF[intro?]:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>; no_fail P f \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>!"
  by (clarsimp simp: validE_NF_def)

lemma validE_NF_valid:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>"
  by (clarsimp simp: validE_NF_def)

lemma validE_NF_no_fail:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>! \<rbrakk> \<Longrightarrow> no_fail P f"
  by (clarsimp simp: validE_NF_def)

lemma validE_NF_weaken_pre[wp_pre]:
  "\<lbrakk>\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace>!; \<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace>!"
  by (simp add: validE_NF_alt_def validNF_weaken_pre)

lemma validE_NF_post_comb_conj_L:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>!; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>, \<lbrace>\<lambda>_ _. True\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>, \<lbrace>E\<rbrace>!"
  unfolding validE_NF_alt_def
  by (fastforce simp: validE_def validNF_def valid_def no_fail_def split: sum.splits)

lemma validE_NF_post_comb_conj_R:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>\<lambda>_ _. True\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>, \<lbrace>E\<rbrace>! \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>, \<lbrace>E\<rbrace>!"
  unfolding validE_NF_alt_def validE_def validNF_def valid_def no_fail_def
  by (force split: sum.splits)

lemma validE_NF_post_comb_conj:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>!; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>, \<lbrace>E\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>, \<lbrace>E\<rbrace>!"
  unfolding validE_NF_alt_def validE_def validNF_def valid_def no_fail_def
  by (force split: sum.splits)

lemma validE_NF_chain:
  "\<lbrakk> \<lbrace>P'\<rbrace> a \<lbrace>R'\<rbrace>,\<lbrace>E'\<rbrace>!; \<And>s. P s \<Longrightarrow> P' s; \<And>r' s'. R' r' s' \<Longrightarrow> R r' s';
     \<And>r'' s''. E' r'' s'' \<Longrightarrow> E r'' s''\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. P s \<rbrace> a \<lbrace>\<lambda>r' s'. R r' s'\<rbrace>,\<lbrace>\<lambda>r'' s''. E r'' s''\<rbrace>!"
  by (fastforce simp: validE_NF_def validE_def2 no_fail_def Ball_def split: sum.splits)

lemma validE_NF_bind_wp[wp]:
  "\<lbrakk>\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>, \<lbrace>E\<rbrace>!; \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>, \<lbrace>E\<rbrace>!\<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> f >>=E (\<lambda>x. g x) \<lbrace>C\<rbrace>, \<lbrace>E\<rbrace>!"
  apply (unfold validE_NF_alt_def bindE_def)
  apply (rule validNF_bind [rotated])
   apply assumption
  apply (clarsimp simp: lift_def throwError_def split: sum.splits)
    apply wpsimp
  done

lemma validNF_catch[wp]:
  "\<lbrakk>\<And>x. \<lbrace>E x\<rbrace> handler x \<lbrace>Q\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>!\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f <catch> (\<lambda>x. handler x) \<lbrace>Q\<rbrace>!"
  apply (unfold validE_NF_alt_def catch_def)
  apply (rule validNF_bind [rotated])
   apply assumption
  apply (clarsimp simp: lift_def throwError_def split: sum.splits)
  apply wp
  done

lemma validNF_throwError[wp]:
  "\<lbrace>E e\<rbrace> throwError e \<lbrace>P\<rbrace>, \<lbrace>E\<rbrace>!"
  by (unfold validE_NF_alt_def throwError_def o_def) wpsimp

lemma validNF_returnOk[wp]:
  "\<lbrace>P e\<rbrace> returnOk e \<lbrace>P\<rbrace>, \<lbrace>E\<rbrace>!"
 by (clarsimp simp: validE_NF_alt_def returnOk_def) wpsimp

lemma validNF_whenE[wp]:
  "(P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>!) \<Longrightarrow> \<lbrace>if P then Q else R ()\<rbrace> whenE P f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>!"
  unfolding whenE_def by clarsimp wp

lemma validNF_nobindE[wp]:
  "\<lbrakk> \<lbrace>B\<rbrace> g \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>!; \<lbrace>A\<rbrace> f \<lbrace>\<lambda>r s. B s\<rbrace>,\<lbrace>E\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> doE f; g odE \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>!"
  by clarsimp wp

text \<open>
  Set up triple rules for @{term validE_NF} so that we can use @{method wp} combinator rules.\<close>
definition validE_NF_property ::
  "('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> ('s, 'c+'a) tmonad \<Rightarrow> bool" where
  "validE_NF_property Q E s b \<equiv>
   Failed \<notin> snd ` (b s) \<and> (\<forall>(r', s') \<in> mres (b s). case r' of Inl x \<Rightarrow> E x s' | Inr x \<Rightarrow> Q x s')"

lemma validE_NF_is_triple[wp_trip]:
  "validE_NF P f Q E = triple_judgement P f (validE_NF_property Q E)"
  by (fastforce simp: validE_NF_def validE_def2 no_fail_def triple_judgement_def
                      validE_NF_property_def
                split: sum.splits)

lemma validNF_cong:
  "\<lbrakk> \<And>s. P s = P' s; \<And>s. P s \<Longrightarrow> m s = m' s;
     \<And>r' s' s. \<lbrakk> P s; (r', s') \<in> mres (m s) \<rbrakk> \<Longrightarrow> Q r' s' = Q' r' s' \<rbrakk> \<Longrightarrow>
   (\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>!) = (\<lbrace>P'\<rbrace> m' \<lbrace>Q'\<rbrace>!)"
  by (fastforce simp: validNF_alt_def)

lemma validE_NF_liftE[wp]:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>! \<Longrightarrow> \<lbrace>P\<rbrace> liftE f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!"
  by (wpsimp simp: validE_NF_alt_def liftE_def)

lemma validE_NF_handleE'[wp]:
  "\<lbrakk> \<And>x. \<lbrace>F x\<rbrace> handler x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>F\<rbrace>! \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> f <handle2> (\<lambda>x. handler x) \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!"
  unfolding validE_NF_alt_def handleE'_def
  apply (erule validNF_bind[rotated])
  apply (clarsimp split: sum.splits)
  apply wpsimp
  done

lemma validE_NF_handleE[wp]:
  "\<lbrakk> \<And>x. \<lbrace>F x\<rbrace> handler x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>F\<rbrace>! \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> f <handle> handler \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!"
  unfolding handleE_def
  by (metis validE_NF_handleE')

lemma validE_NF_condition[wp]:
  "\<lbrakk> \<lbrace> Q \<rbrace> A \<lbrace>P\<rbrace>,\<lbrace> E \<rbrace>!; \<lbrace> R \<rbrace> B \<lbrace>P\<rbrace>,\<lbrace> E \<rbrace>!\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. if C s then Q s else R s\<rbrace> condition C A B \<lbrace>P\<rbrace>,\<lbrace> E \<rbrace>!"
  apply rule
   apply (drule validE_NF_valid)+
   apply wp
  apply (drule validE_NF_no_fail)+
  apply (clarsimp simp: no_fail_def condition_def)
  done

end