(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Lemmas about the no_fail predicate. *)

theory No_Fail
  imports
    In_Monad
    NonDetMonadVCG
    WPSimp
begin

subsection "Non-Failure"

text \<open>
  With the failure flag, we can formulate non-failure separately
  from validity. A monad @{text m} does not fail under precondition
  @{text P}, if for no start state in that precondition it sets
  the failure flag.
\<close>
definition
  no_fail :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) nondet_monad \<Rightarrow> bool"
where
  "no_fail P m \<equiv> \<forall>s. P s \<longrightarrow> \<not> (snd (m s))"


text \<open>
  It is often desired to prove non-failure and a Hoare triple
  simultaneously, as the reasoning is often similar. The following
  definitions allow such reasoning to take place.
\<close>

definition
  validNF ::"('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) nondet_monad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
      ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>!")
where
  "validNF P f Q \<equiv> valid P f Q \<and> no_fail P f"

definition
  validE_NF :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'a + 'b) nondet_monad \<Rightarrow>
             ('b \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
             ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace>/ _ /(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>!)")
where
  "validE_NF P f Q E \<equiv> validE P f Q E \<and> no_fail P f"

lemma validE_NF_alt_def:
  "\<lbrace> P \<rbrace> B \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>! = \<lbrace> P \<rbrace> B \<lbrace> \<lambda>v s. case v of Inl e \<Rightarrow> E e s | Inr r \<Rightarrow> Q r s \<rbrace>!"
  by (clarsimp simp: validE_NF_def validE_def validNF_def)

lemma validNF_make_schematic_post:
  "(\<forall>s0. \<lbrace> \<lambda>s. P s0 s \<rbrace> f \<lbrace> \<lambda>rv s. Q s0 rv s \<rbrace>!) \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>s0. P s0 s \<and> (\<forall>rv s'. Q s0 rv s' \<longrightarrow> Q' rv s') \<rbrace> f \<lbrace> Q' \<rbrace>!"
  by (auto simp add: valid_def validNF_def no_fail_def split: prod.splits)

lemma validE_NF_make_schematic_post:
  "(\<forall>s0. \<lbrace> \<lambda>s. P s0 s \<rbrace> f \<lbrace> \<lambda>rv s. Q s0 rv s \<rbrace>, \<lbrace> \<lambda>rv s. E s0 rv s \<rbrace>!) \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>s0. P s0 s \<and> (\<forall>rv s'. Q s0 rv s' \<longrightarrow> Q' rv s')
        \<and> (\<forall>rv s'. E s0 rv s' \<longrightarrow> E' rv s') \<rbrace> f \<lbrace> Q' \<rbrace>, \<lbrace> E' \<rbrace>!"
  by (auto simp add: validE_NF_def validE_def valid_def no_fail_def split: prod.splits sum.splits)

lemma validNF_conjD1: "\<lbrace> P \<rbrace> f \<lbrace> \<lambda>rv s. Q rv s \<and> Q' rv s \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>!"
  by (fastforce simp: validNF_def valid_def no_fail_def)

lemma validNF_conjD2: "\<lbrace> P \<rbrace> f \<lbrace> \<lambda>rv s. Q rv s \<and> Q' rv s \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q' \<rbrace>!"
  by (fastforce simp: validNF_def valid_def no_fail_def)


lemma no_fail_pre[wp_pre]:
  "\<lbrakk> no_fail P f; \<And>s. Q s \<Longrightarrow> P s\<rbrakk> \<Longrightarrow> no_fail Q f"
  by (simp add: no_fail_def)

lemma wpc_helper_no_fail_final:
  "no_fail Q f \<Longrightarrow> wpc_helper (P, P') (Q, Q') (no_fail P f)"
  by (clarsimp simp: wpc_helper_def elim!: no_fail_pre)

lemma wpc_helper_validNF:
  "\<lbrace>Q\<rbrace> g \<lbrace>S\<rbrace>! \<Longrightarrow> wpc_helper (P, P') (Q, Q') \<lbrace>P\<rbrace> g \<lbrace>S\<rbrace>!"
  apply (clarsimp simp: wpc_helper_def)
  by (metis hoare_vcg_precond_imp no_fail_pre validNF_def)

wpc_setup "\<lambda>m. no_fail P m" wpc_helper_no_fail_final
wpc_setup "\<lambda>m. \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>!" wpc_helper_validNF


bundle no_pre = hoare_pre [wp_pre del] no_fail_pre [wp_pre del]

bundle classic_wp_pre = hoare_pre [wp_pre del]
    all_classic_wp_combs[wp_comb del] all_classic_wp_combs[wp_comb]



subsection "Non-Failure"

lemma no_failD:
  "\<lbrakk> no_fail P m; P s \<rbrakk> \<Longrightarrow> \<not>(snd (m s))"
  by (simp add: no_fail_def)

lemma no_fail_modify [wp,simp]:
  "no_fail \<top> (modify f)"
  by (simp add: no_fail_def modify_def get_def put_def bind_def)

lemma no_fail_gets_simp[simp]:
  "no_fail P (gets f)"
  unfolding no_fail_def gets_def get_def return_def bind_def
  by simp

lemma no_fail_gets:
  "no_fail \<top> (gets f)"
  by simp

lemma no_fail_select [simp]:
  "no_fail \<top> (select S)"
  by (simp add: no_fail_def select_def)

lemma no_fail_alt [wp]:
  "\<lbrakk> no_fail P f; no_fail Q g \<rbrakk> \<Longrightarrow> no_fail (P and Q) (f \<sqinter> g)"
  by (simp add: no_fail_def alternative_def)

lemma no_fail_return [simp, wp]:
  "no_fail \<top> (return x)"
  by (simp add: return_def no_fail_def)

lemma no_fail_get [simp, wp]:
  "no_fail \<top> get"
  by (simp add: get_def no_fail_def)

lemma no_fail_put [simp, wp]:
  "no_fail \<top> (put s)"
  by (simp add: put_def no_fail_def)

lemma no_fail_when [wp]:
  "(P \<Longrightarrow> no_fail Q f) \<Longrightarrow> no_fail (if P then Q else \<top>) (when P f)"
  by (simp add: when_def)

lemma no_fail_unless [wp]:
  "(\<not>P \<Longrightarrow> no_fail Q f) \<Longrightarrow> no_fail (if P then \<top> else Q) (unless P f)"
  by (simp add: unless_def when_def)

lemma no_fail_fail [simp, wp]:
  "no_fail \<bottom> fail"
  by (simp add: fail_def no_fail_def)

lemmas [wp] = no_fail_gets

lemma no_fail_assert [simp, wp]:
  "no_fail (\<lambda>_. P) (assert P)"
  by (simp add: assert_def)

lemma no_fail_assert_opt [simp, wp]:
  "no_fail (\<lambda>_. P \<noteq> None) (assert_opt P)"
  by (simp add: assert_opt_def split: option.splits)

lemma no_fail_case_option [wp]:
  assumes f: "no_fail P f"
  assumes g: "\<And>x. no_fail (Q x) (g x)"
  shows "no_fail (if x = None then P else Q (the x)) (case_option f g x)"
  by (clarsimp simp add: f g)

lemma no_fail_if [wp]:
  "\<lbrakk> P \<Longrightarrow> no_fail Q f; \<not>P \<Longrightarrow> no_fail R g \<rbrakk> \<Longrightarrow>
  no_fail (if P then Q else R) (if P then f else g)"
  by simp

lemma no_fail_apply [wp]:
  "no_fail P (f (g x)) \<Longrightarrow> no_fail P (f $ g x)"
  by simp

lemma no_fail_undefined [simp, wp]:
  "no_fail \<bottom> undefined"
  by (simp add: no_fail_def)

lemma no_fail_returnOK [simp, wp]:
  "no_fail \<top> (returnOk x)"
  by (simp add: returnOk_def)

lemma no_fail_bind [wp]:
  assumes f: "no_fail P f"
  assumes g: "\<And>rv. no_fail (R rv) (g rv)"
  assumes v: "\<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>"
  shows "no_fail (P and Q) (f >>= (\<lambda>rv. g rv))"
  apply (clarsimp simp: no_fail_def bind_def)
  apply (rule conjI)
   prefer 2
   apply (erule no_failD [OF f])
  apply clarsimp
  apply (drule (1) use_valid [OF _ v])
  apply (drule no_failD [OF g])
  apply simp
  done


lemma no_fail_assume_pre:
  "(\<And>s. P s \<Longrightarrow> no_fail P f) \<Longrightarrow> no_fail P f"
  by (simp add: no_fail_def)

lemma no_fail_liftM_eq [simp]:
  "no_fail P (liftM f m) = no_fail P m"
  by (auto simp: liftM_def no_fail_def bind_def return_def)

lemma no_fail_select_f [wp]:
  "no_fail (\<lambda>s. \<not>snd S) (select_f S)"
  by (simp add: select_f_def no_fail_def)

lemma no_fail_liftM [wp]:
  "no_fail P m \<Longrightarrow> no_fail P (liftM f m)"
  by (simp)

lemma no_fail_pre_and:
  "no_fail P f \<Longrightarrow> no_fail (P and Q) f"
  by (erule no_fail_pre) simp

lemma no_fail_spec:
  "\<lbrakk> \<And>s. no_fail (((=) s) and P) f \<rbrakk> \<Longrightarrow> no_fail P f"
  by (simp add: no_fail_def)

lemma no_fail_assertE [wp]:
  "no_fail (\<lambda>_. P) (assertE P)"
  by (simp add: assertE_def split: if_split)

lemma no_fail_spec_pre:
  "\<lbrakk> no_fail (((=) s) and P') f; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> no_fail (((=) s) and P) f"
  by (erule no_fail_pre, simp)

lemma no_fail_whenE [wp]:
  "\<lbrakk> G \<Longrightarrow> no_fail P f \<rbrakk> \<Longrightarrow> no_fail (\<lambda>s. G \<longrightarrow> P s) (whenE G f)"
  by (simp add: whenE_def split: if_split)

lemma no_fail_unlessE [wp]:
  "\<lbrakk> \<not> G \<Longrightarrow> no_fail P f \<rbrakk> \<Longrightarrow> no_fail (\<lambda>s. \<not> G \<longrightarrow> P s) (unlessE G f)"
  by (simp add: unlessE_def split: if_split)

lemma no_fail_throwError [wp]:
  "no_fail \<top> (throwError e)"
  by (simp add: throwError_def)

lemma no_fail_liftE [wp]:
  "no_fail P f \<Longrightarrow> no_fail P (liftE f)"
  unfolding liftE_def by wpsimp

lemma no_fail_gets_the [wp]:
  "no_fail (\<lambda>s. f s \<noteq> None) (gets_the f)"
  apply (simp add: gets_the_def)
  apply (rule no_fail_pre, wp)
  apply simp
  done

lemma assert_opt_If:
  "assert_opt v = If (v = None) fail (return (the v))"
  by (simp_all add: assert_opt_def split: option.split)

lemma if_to_top_of_bind:
  "(bind (If P x y) z) = If P (bind x z) (bind y z)"
  by (simp split: if_split)

lemma if_to_top_of_bindE:
  "(bindE (If P x y) z) = If P (bindE x z) (bindE y z)"
  by (simp split: if_split)

lemma alternative_bind:
  "((a \<sqinter> b) >>= c) = ((a >>= c) \<sqinter> (b >>= c))"
  apply (rule ext, simp add: alternative_def bind_def split_def)
  apply blast
  done

lemma alternative_refl:
  "(a \<sqinter> a) = a"
  by (rule ext, simp add: alternative_def)

lemma alternative_com:
  "(f \<sqinter> g) = (g \<sqinter> f)"
  apply (rule ext)
  apply (auto simp: alternative_def)
  done

lemma liftE_alternative:
  "liftE (a \<sqinter> b) = (liftE a \<sqinter> liftE b)"
  by (simp add: liftE_def alternative_bind)

lemma no_fail_bindE [wp]:
  "\<lbrakk> no_fail P f; \<And>rv. no_fail (R rv) (g rv); \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,- \<rbrakk>
     \<Longrightarrow> no_fail (P and Q) (f >>=E g)"
  apply (simp add: bindE_def)
  apply (erule no_fail_bind)
   apply (simp add: lift_def)
   apply wpc
    apply (simp add: throwError_def)
    apply wp
   apply assumption
  apply (simp add: validE_R_def validE_def)
  apply (erule hoare_strengthen_post)
  apply clarsimp
  done

lemma no_fail_False [simp]:
  "no_fail (\<lambda>_. False) X"
  by (clarsimp simp: no_fail_def)

lemma no_fail_gets_map[wp]:
  "no_fail (\<lambda>s. f s p \<noteq> None) (gets_map f p)"
  unfolding gets_map_def by wpsimp

lemma no_fail_or:
  "\<lbrakk>no_fail P a; no_fail Q a\<rbrakk> \<Longrightarrow> no_fail (P or Q) a"
  by (clarsimp simp: no_fail_def)

lemma no_fail_state_assert[wp]:
  "no_fail P (state_assert P)"
  unfolding state_assert_def
  by wpsimp

section "validNF Rules"

subsection "Basic validNF theorems"

lemma validNF [intro?]:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>; no_fail P f \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>!"
  by (clarsimp simp: validNF_def)

lemma validNF_valid: "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>"
  by (clarsimp simp: validNF_def)

lemma validNF_no_fail: "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>! \<rbrakk> \<Longrightarrow> no_fail P f"
  by (clarsimp simp: validNF_def)

lemma snd_validNF:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>!; P s \<rbrakk> \<Longrightarrow> \<not> snd (f s)"
  by (clarsimp simp: validNF_def no_fail_def)

lemma use_validNF:
  "\<lbrakk> (r', s') \<in> fst (f s); \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>!; P s \<rbrakk> \<Longrightarrow> Q r' s'"
  by (fastforce simp: validNF_def valid_def)

subsection "validNF weakest pre-condition rules"

lemma validNF_return [wp]:
  "\<lbrace> P x \<rbrace> return x \<lbrace> P \<rbrace>!"
  by (wp validNF)+

lemma validNF_get [wp]:
  "\<lbrace> \<lambda>s. P s s  \<rbrace> get \<lbrace> P \<rbrace>!"
  by (wp validNF)+

lemma validNF_put [wp]:
  "\<lbrace> \<lambda>s. P () x  \<rbrace> put x \<lbrace> P \<rbrace>!"
  by (wp validNF)+

lemma validNF_K_bind [wp]:
  "\<lbrace> P \<rbrace> x \<lbrace> Q \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> K_bind x f \<lbrace> Q \<rbrace>!"
  by simp

lemma validNF_fail [wp]:
  "\<lbrace> \<lambda>s. False \<rbrace> fail \<lbrace> Q \<rbrace>!"
  by (clarsimp simp: validNF_def fail_def no_fail_def)

lemma validNF_prop [wp_unsafe]:
  "\<lbrakk> no_fail (\<lambda>s. P) f \<rbrakk> \<Longrightarrow> \<lbrace> \<lambda>s. P \<rbrace> f \<lbrace> \<lambda>rv s. P \<rbrace>!"
  by (wp validNF)+

lemma validNF_post_conj [intro!]:
  "\<lbrakk> \<lbrace> P \<rbrace> a \<lbrace> Q \<rbrace>!; \<lbrace> P \<rbrace> a \<lbrace> R \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> a \<lbrace> Q and R \<rbrace>!"
  by (auto simp: validNF_def)

lemma validNF_pre_disj [intro!]:
  "\<lbrakk> \<lbrace> P \<rbrace> a \<lbrace> R \<rbrace>!; \<lbrace> Q \<rbrace> a \<lbrace> R \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace> P or Q \<rbrace> a \<lbrace> R \<rbrace>!"
  by (rule validNF) (auto dest: validNF_valid validNF_no_fail intro: no_fail_or)

(*
 * Set up combination rules for WP, which also requires
 * a "wp_trip" rule for validNF.
 *)

definition "validNF_property Q s b \<equiv> \<not> snd (b s) \<and> (\<forall>(r', s') \<in> fst (b s). Q r' s')"

lemma validNF_is_triple [wp_trip]:
  "validNF P f Q = triple_judgement P f (validNF_property Q)"
  apply (clarsimp simp: validNF_def triple_judgement_def validNF_property_def)
  apply (auto simp: no_fail_def valid_def)
  done

lemma validNF_weaken_pre[wp_pre]:
  "\<lbrakk>\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>!; \<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>!"
  by (metis hoare_pre_imp no_fail_pre validNF_def)

lemma validNF_post_comb_imp_conj:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>!; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>!"
  by (fastforce simp: validNF_def valid_def)

lemma validNF_post_comb_conj_L:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>!"
  apply (clarsimp simp: validNF_def valid_def no_fail_def)
  apply force
  done

lemma validNF_post_comb_conj_R:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>!"
  apply (clarsimp simp: validNF_def valid_def no_fail_def)
  apply force
  done

lemma validNF_post_comb_conj:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>!"
  apply (clarsimp simp: validNF_def valid_def no_fail_def)
  apply force
  done

lemma validNF_if_split [wp_split]:
  "\<lbrakk>P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>S\<rbrace>!; \<not> P \<Longrightarrow> \<lbrace>R\<rbrace> g \<lbrace>S\<rbrace>!\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not> P \<longrightarrow> R s)\<rbrace> if P then f else g \<lbrace>S\<rbrace>!"
  by simp

lemma validNF_vcg_conj_lift:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>! \<rbrakk> \<Longrightarrow>
      \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>!"
  apply (subst pred_conj_def[symmetric], subst pred_conj_def[symmetric], rule validNF_post_conj)
   apply (erule validNF_weaken_pre, fastforce)
  apply (erule validNF_weaken_pre, fastforce)
  done

lemma validNF_vcg_disj_lift:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>! \<rbrakk> \<Longrightarrow>
       \<lbrace>\<lambda>s. P s \<or> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<or> Q' rv s\<rbrace>!"
  apply (clarsimp simp: validNF_def)
  apply safe
   apply (auto intro!: hoare_vcg_disj_lift)[1]
  apply (clarsimp simp: no_fail_def)
  done

lemma validNF_vcg_all_lift [wp]:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>!"
  apply atomize
  apply (rule validNF)
   apply (clarsimp simp: validNF_def)
   apply (rule hoare_vcg_all_lift)
   apply force
  apply (clarsimp simp: no_fail_def validNF_def)
  done

lemma validNF_bind [wp_split]:
  "\<lbrakk> \<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>!; \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>! \<rbrakk> \<Longrightarrow>
       \<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>C\<rbrace>!"
  apply (rule validNF)
   apply (metis validNF_valid hoare_seq_ext)
  apply (clarsimp simp: no_fail_def validNF_def bind_def' valid_def)
  apply blast
  done

lemmas validNF_seq_ext = validNF_bind

subsection "validNF compound rules"

lemma validNF_state_assert [wp]:
  "\<lbrace> \<lambda>s. P () s \<and> G s  \<rbrace> state_assert G \<lbrace> P \<rbrace>!"
  apply (rule validNF)
   apply wpsimp
  apply (clarsimp simp: no_fail_def state_assert_def
              bind_def' assert_def return_def get_def)
  done

lemma validNF_modify [wp]:
  "\<lbrace> \<lambda>s. P () (f s) \<rbrace> modify f \<lbrace> P \<rbrace>!"
  apply (clarsimp simp: modify_def)
  apply wp
  done

lemma validNF_gets [wp]:
  "\<lbrace>\<lambda>s. P (f s) s\<rbrace> gets f \<lbrace>P\<rbrace>!"
  apply (clarsimp simp: gets_def)
  apply wp
  done

lemma validNF_condition [wp]:
  "\<lbrakk> \<lbrace> Q \<rbrace> A \<lbrace>P\<rbrace>!; \<lbrace> R \<rbrace> B \<lbrace>P\<rbrace>!\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. if C s then Q s else R s\<rbrace> condition C A B \<lbrace>P\<rbrace>!"
  apply rule
   apply (drule validNF_valid)+
   apply (erule (1) condition_wp)
  apply (drule validNF_no_fail)+
  apply (clarsimp simp: no_fail_def condition_def)
  done

lemma validNF_alt_def:
  "validNF P m Q = (\<forall>s. P s \<longrightarrow> ((\<forall>(r', s') \<in> fst (m s). Q r' s') \<and> \<not> snd (m s)))"
  by (fastforce simp: validNF_def valid_def no_fail_def)

lemma validNF_assert [wp]:
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

lemma validNF_case_prod [wp]:
  "\<lbrakk> \<And>x y. validNF (P x y) (B x y) Q \<rbrakk> \<Longrightarrow> validNF (case_prod P v) (case_prod (\<lambda>x y. B x y) v) Q"
  by (metis prod.exhaust split_conv)

lemma validE_NF_case_prod [wp]:
    "\<lbrakk> \<And>a b. \<lbrace>P a b\<rbrace> f a b \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>! \<rbrakk> \<Longrightarrow>
          \<lbrace>case x of (a, b) \<Rightarrow> P a b\<rbrace> case x of (a, b) \<Rightarrow> f a b \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>!"
  apply (clarsimp simp: validE_NF_alt_def)
  apply (erule validNF_case_prod)
  done

lemma no_fail_is_validNF_True: "no_fail P s = (\<lbrace> P \<rbrace> s \<lbrace> \<lambda>_ _. True \<rbrace>!)"
  by (clarsimp simp: no_fail_def validNF_def valid_def)

subsection "validNF reasoning in the exception monad"

lemma validE_NF [intro?]:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>; no_fail P f \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>!"
  apply (clarsimp simp: validE_NF_def)
  done

lemma validE_NF_valid:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>"
  apply (clarsimp simp: validE_NF_def)
  done

lemma validE_NF_no_fail:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>! \<rbrakk> \<Longrightarrow> no_fail P f"
  apply (clarsimp simp: validE_NF_def)
  done

lemma validE_NF_weaken_pre[wp_pre]:
   "\<lbrakk>\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace>!; \<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace>!"
  apply (clarsimp simp: validE_NF_alt_def)
  apply (erule validNF_weaken_pre)
  apply simp
  done

lemma validE_NF_post_comb_conj_L:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace> E \<rbrace>!; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>, \<lbrace> \<lambda>_ _. True \<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>, \<lbrace> E \<rbrace>!"
  apply (clarsimp simp: validE_NF_alt_def validE_def validNF_def
          valid_def no_fail_def split: sum.splits)
  apply force
  done

lemma validE_NF_post_comb_conj_R:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace> \<lambda>_ _. True \<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>, \<lbrace> E \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>, \<lbrace> E \<rbrace>!"
  apply (clarsimp simp: validE_NF_alt_def validE_def validNF_def
          valid_def no_fail_def split: sum.splits)
  apply force
  done

lemma validE_NF_post_comb_conj:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace> E \<rbrace>!; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>, \<lbrace> E \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>, \<lbrace> E \<rbrace>!"
  apply (clarsimp simp: validE_NF_alt_def validE_def validNF_def
          valid_def no_fail_def split: sum.splits)
  apply force
  done

lemma validE_NF_chain:
   "\<lbrakk>\<lbrace>P'\<rbrace> a \<lbrace>R'\<rbrace>,\<lbrace>E'\<rbrace>!;
    \<And>s. P s \<Longrightarrow> P' s;
    \<And>r' s'. R' r' s' \<Longrightarrow> R r' s';
    \<And>r'' s''. E' r'' s'' \<Longrightarrow> E r'' s''\<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. P s \<rbrace> a \<lbrace>\<lambda>r' s'. R r' s'\<rbrace>,\<lbrace>\<lambda>r'' s''. E r'' s''\<rbrace>!"
  by (fastforce simp: validE_NF_def validE_def2 no_fail_def Ball_def split: sum.splits)

lemma validE_NF_bind_wp [wp]:
  "\<lbrakk>\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>, \<lbrace>E\<rbrace>!; \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>, \<lbrace>E\<rbrace>!\<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> f >>=E (\<lambda>x. g x) \<lbrace>C\<rbrace>, \<lbrace>E\<rbrace>!"
  apply (unfold validE_NF_alt_def bindE_def)
  apply (rule validNF_bind [rotated])
   apply assumption
  apply (clarsimp simp: lift_def throwError_def split: sum.splits)
  apply wpsimp
  done

lemma validNF_catch [wp]:
  "\<lbrakk>\<And>x. \<lbrace>E x\<rbrace> handler x \<lbrace>Q\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>!\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f <catch> (\<lambda>x. handler x) \<lbrace>Q\<rbrace>!"
  apply (unfold validE_NF_alt_def catch_def)
  apply (rule validNF_bind [rotated])
   apply assumption
  apply (clarsimp simp: lift_def throwError_def split: sum.splits)
  apply wp
  done

lemma validNF_throwError [wp]:
  "\<lbrace>E e\<rbrace> throwError e \<lbrace>P\<rbrace>, \<lbrace>E\<rbrace>!"
  by (unfold validE_NF_alt_def throwError_def o_def) wpsimp

lemma validNF_returnOk [wp]:
  "\<lbrace>P e\<rbrace> returnOk e \<lbrace>P\<rbrace>, \<lbrace>E\<rbrace>!"
  by (clarsimp simp: validE_NF_alt_def returnOk_def) wpsimp

lemma validNF_whenE [wp]:
  "(P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>!) \<Longrightarrow> \<lbrace>if P then Q else R ()\<rbrace> whenE P f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>!"
  unfolding whenE_def by clarsimp wp

lemma validNF_nobindE [wp]:
  "\<lbrakk> \<lbrace>B\<rbrace> g \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>!;
     \<lbrace>A\<rbrace> f \<lbrace>\<lambda>r s. B s\<rbrace>,\<lbrace>E\<rbrace>! \<rbrakk> \<Longrightarrow>
   \<lbrace>A\<rbrace> doE f; g odE \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>!"
  by clarsimp wp

text \<open>
Setup triple rules for @{term validE_NF} so that we can use
wp combinator rules.
\<close>

definition "validE_NF_property Q E s b \<equiv> \<not> snd (b s)
       \<and> (\<forall>(r', s') \<in> fst (b s). case r' of Inl x \<Rightarrow> E x s' | Inr x \<Rightarrow> Q x s')"

lemma validE_NF_is_triple [wp_trip]:
  "validE_NF P f Q E = triple_judgement P f (validE_NF_property Q E)"
  apply (clarsimp simp: validE_NF_def validE_def2 no_fail_def triple_judgement_def
           validE_NF_property_def split: sum.splits)
  apply blast
  done

lemma validNF_cong:
   "\<lbrakk> \<And>s. P s = P' s; \<And>s. P s \<Longrightarrow> m s = m' s;
           \<And>r' s' s. \<lbrakk> P s; (r', s') \<in> fst (m s) \<rbrakk> \<Longrightarrow> Q r' s' = Q' r' s' \<rbrakk> \<Longrightarrow>
     (\<lbrace> P \<rbrace> m \<lbrace> Q \<rbrace>!) = (\<lbrace> P' \<rbrace> m' \<lbrace> Q' \<rbrace>!)"
  by (fastforce simp: validNF_alt_def)

lemma validE_NF_liftE [wp]:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>! \<Longrightarrow> \<lbrace>P\<rbrace> liftE f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!"
  by (wpsimp simp: validE_NF_alt_def liftE_def)

lemma validE_NF_handleE' [wp]:
  "\<lbrakk> \<And>x. \<lbrace>F x\<rbrace> handler x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>F\<rbrace>! \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> f <handle2> (\<lambda>x. handler x) \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!"
  apply (unfold validE_NF_alt_def handleE'_def)
  apply (rule validNF_bind [rotated])
   apply assumption
  apply (clarsimp split: sum.splits)
  apply wpsimp
  done

lemma validE_NF_handleE [wp]:
  "\<lbrakk> \<And>x. \<lbrace>F x\<rbrace> handler x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>F\<rbrace>! \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> f <handle> handler \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!"
  apply (unfold handleE_def)
  apply (metis validE_NF_handleE')
  done

lemma validE_NF_condition [wp]:
  "\<lbrakk> \<lbrace> Q \<rbrace> A \<lbrace>P\<rbrace>,\<lbrace> E \<rbrace>!; \<lbrace> R \<rbrace> B \<lbrace>P\<rbrace>,\<lbrace> E \<rbrace>!\<rbrakk>
      \<Longrightarrow> \<lbrace>\<lambda>s. if C s then Q s else R s\<rbrace> condition C A B \<lbrace>P\<rbrace>,\<lbrace> E \<rbrace>!"
  apply rule
   apply (drule validE_NF_valid)+
   apply wp
  apply (drule validE_NF_no_fail)+
  apply (clarsimp simp: no_fail_def condition_def)
  done

lemma hoare_assume_preNF:
  "(\<And>s. P s \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!"
  by (metis validNF_alt_def)

end
