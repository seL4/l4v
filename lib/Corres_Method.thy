(*
 *
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Corres_Method
imports Corres_UL SpecValid_R
begin

chapter \<open>Corres Methods\<close>

section \<open>Boilerplate\<close>

context begin

lemma stronger_corres_guard_imp_str:
  assumes x: "corres_underlying sr nf nf' r Q Q' f g"
  assumes y: "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> sr \<rbrakk> \<Longrightarrow> Q s \<and> Q' s'"
  shows      "corres_underlying sr nf nf' r P P' f g"
  using x by (auto simp: y corres_underlying_def)

private lemma corres_trivial:
  "corres_underlying sr nf nf' r P P' f f' \<Longrightarrow> corres_underlying sr nf nf' r P P' f f'"
  by simp

method check_corres = (succeeds \<open>rule corres_trivial\<close>, fails \<open>rule TrueI\<close>)

private definition "my_false s \<equiv> False"

private
  lemma corres_my_false: "corres_underlying sr nf nf' r my_false P f f'"
                         "corres_underlying sr nf nf' r P' my_false f f'"
  by (auto simp add: my_false_def[abs_def] corres_underlying_def)


method corres_pre =
  (check_corres, (fails \<open>rule corres_my_false\<close>, rule stronger_corres_guard_imp_str)?)


named_theorems corres_concrete_r

private lemma corres_r_False:
  "False \<Longrightarrow> corres_underlying sr nf nf' (\<lambda>_. my_false) P P' f f'"
  by simp

method corres_concrete_r declares corres_concrete_r =
  (fails \<open>rule corres_r_False\<close>, determ \<open>rule corres_concrete_r\<close>)

named_theorems corres_concrete_P

private lemma corres_both_False:
  "corres_underlying sr nf nf' r my_false my_false f f'"
  by (auto simp add: my_false_def[abs_def] corres_underlying_def)

method corres_concrete_P declares corres_concrete_P =
  (fails \<open>rule corres_both_False\<close>, determ \<open>rule corres_concrete_P\<close>)

end

section \<open>Corresc - Corres over case statements\<close>

definition
  "corres_underlyingL \<equiv> corres_underlying"

lemma wpc_helper_corres1:
  "corres_underlyingL sr nf nf' r Q A f f' \<Longrightarrow> wpc_helper (P, P') (Q, Q') (corres_underlying sr nf nf' r P A f f')"
  by (clarsimp simp: wpc_helper_def corres_underlyingL_def elim!: corres_guard_imp)

lemma wpc_helper_corres2:
  "corres_underlying sr nf nf' r A Q f f' \<Longrightarrow> wpc_helper (P, P') (Q, Q') (corres_underlyingL sr nf nf' r A P f f')"
  by (clarsimp simp: wpc_helper_def corres_underlyingL_def elim!: corres_guard_imp)

wpc_setup "\<lambda>f. corres_underlying sr nf nf' r P P' f f'" wpc_helper_corres1
wpc_setup "\<lambda>f'. corres_underlyingL sr nf nf' r P P' f f'" wpc_helper_corres2

lemma
  wpc_contr_helper:
  "A = B \<Longrightarrow> A = C \<Longrightarrow> B \<noteq> C \<Longrightarrow> P"
  by blast

text \<open>
 Generate quadratic blowup of the case statements on either side of refinement.
 Attempt to discharge resulting contradictions.
\<close>

method corresc uses simp =
  (check_corres, wpc; wpc;
    (solves \<open>rule FalseE,
      (simp add: simp)?, (erule (1) wpc_contr_helper, simp add: simp)?\<close>)?)[1]

section \<open>Alternative split rules\<close>

text \<open>
 These split rules provide much greater information about what is happening on each side
 of the refinement.
 \<close>

lemma corres_split_strongest:
  assumes x: "corres_underlying sr nf nf' r' P P' a c"
  assumes y: "\<And>rv rv'. r' rv rv' \<Longrightarrow> corres_underlying sr nf nf' r (R rv' rv) (R' rv rv') (b rv) (d rv')"
  assumes    "\<lbrace>\<lambda>s. (\<exists>s'. (s,s') \<in> sr \<and> Q' s') \<and> Q s\<rbrace> a \<lbrace>\<lambda>r s. \<forall>x. r' r x \<longrightarrow> (\<exists>s'. (s, s') \<in> sr) \<longrightarrow> R x r s\<rbrace>"
              "\<lbrace>\<lambda>s'. (\<exists>s. (s, s') \<in> sr \<and> Q s) \<and> Q' s'\<rbrace> c \<lbrace>\<lambda>r s'. \<forall>x. r' x r \<longrightarrow> (\<exists>s. (s, s') \<in> sr) \<longrightarrow> R' x r s'\<rbrace>"
  shows      "corres_underlying sr nf nf' r (P and Q) (P' and Q') (a >>= (\<lambda>rv. b rv)) (c >>= (\<lambda>rv'. d rv'))"
  using assms
  apply -
  apply (clarsimp simp: corres_underlying_def bind_def)
  apply (clarsimp simp: Bex_def Ball_def valid_def)
  by (safe, metis, meson+)

lemma corres_split_str:
  assumes x: "corres_underlying sr nf nf' r' P P' a c"
  assumes y: "\<And>rv rv'. r' rv rv' \<Longrightarrow> corres_underlying sr nf nf' r (R rv' rv) (R' rv rv') (b rv) (d rv')"
  assumes z: "\<lbrace>Q\<rbrace> a \<lbrace>\<lambda>r s. \<forall>x. r' r x \<longrightarrow> R x r s\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>\<lambda>r s. \<forall>x. r' x r \<longrightarrow> R' x r s\<rbrace>"
  shows      "corres_underlying sr nf nf' r (P and Q) (P' and Q') (a >>= (\<lambda>rv. b rv)) (c >>= (\<lambda>rv'. d rv'))"
  apply (rule corres_split_strongest[OF x y])
  using z
  by (auto simp add: valid_def split: prod.splits)



section \<open>Corres Method\<close>

text \<open>Handles structured decomposition of corres goals\<close>

named_theorems
  corres_splits and
  corres_simp and (* conservative simplification rules applied when no progress can be made *)
  corres_simp_del and (* bad simp rules that break everything *)
  corres (* solving terminal corres subgoals *)

context begin

text \<open>Testing for schematic goal state\<close>

lemma corres_fold_dc:
  "corres_underlying sr nf nf' dc P P' f f' \<Longrightarrow> corres_underlying sr nf nf' (\<lambda>_ _. True) P P' f f'"
  by (simp add: dc_def[abs_def])

private method corres_fold_dc =
  (match conclusion in
    "corres_underlying _ _ _ (\<lambda>_ _. True) _ _ _ _" \<Rightarrow> \<open>rule corres_fold_dc\<close>)


method corres_once declares corres_splits corres corres_simp =
   (corres_fold_dc?,
   (corres_concrete_P | (corres_pre,
    #break "corres",
    ( determ \<open>rule corres\<close>
    | corres_concrete_r
    | corresc
    | (rule corres_splits, corres_once)
    | (simp only: corres_simp, corres_once)
    ))))


method corres declares corres_splits corres corres_simp =
  (corres_once+)[1]

end

lemma corres_when_str:
  "\<lbrakk>G \<Longrightarrow> G' \<Longrightarrow> corres_underlying sr nf nf' dc P P' a c\<rbrakk>
\<Longrightarrow> corres_underlying sr nf nf' dc (K(G = G') and (\<lambda>x. G \<longrightarrow> P x)) (\<lambda>x. G' \<longrightarrow> P' x) (when G a) (when G' c)"
  apply (simp add: corres_underlying_def)
  apply (cases "G = G'"; cases G; simp)
  by (clarsimp simp: return_def)

lemma corres_return_trivial:
  "corres_underlying sr nf nf' dc (\<lambda>_. True) (\<lambda>_. True) (return ()) (return ())"
  by simp

lemma corres_return_eq:
  "corres_underlying sr nf nf' (op =) (\<lambda>_. True) (\<lambda>_. True) (return x) (return x)"
  by simp


lemmas [corres_splits] =
  corres_split_str

lemmas [corres] =
  corres_when_str
  corres_liftM2_simp[THEN iffD2]
  corres_return_trivial
  corres_return_eq

lemmas [corres_simp] =
  fun_app_def comp_apply option.inject K_bind_def return_bind
  Let_def liftE_bindE



section \<open>Corres Search - find symbolic execution path that allows a given rule to be applied\<close>

lemma corres_if_str:
  "\<lbrakk>(G \<Longrightarrow> G' \<Longrightarrow> corres_underlying sr nf nf' r P P' a c); (\<not>G \<Longrightarrow> \<not>G' \<Longrightarrow> corres_underlying sr nf nf' r Q Q' b d)\<rbrakk>
\<Longrightarrow> corres_underlying sr nf nf' r (K(G = G') and (if G then P else Q)) (if G' then P' else Q') (if G then a else b)
      (if G' then c else d)"
    by (simp add: corres_underlying_def)

lemma corres_if_str_rev:
  "\<lbrakk>(\<not> G \<Longrightarrow> G' \<Longrightarrow> corres_underlying sr nf nf' r P P' a c); (G \<Longrightarrow> \<not>G' \<Longrightarrow> corres_underlying sr nf nf' r Q Q' b d)\<rbrakk>
\<Longrightarrow> corres_underlying sr nf nf' r (K((\<not> G) = G') and (if G then Q else P)) (if G' then P' else Q') (if G then b else a)
      (if G' then c else d)"
    by (simp add: corres_underlying_def)

lemma corres_symb_exec_l_str:
  assumes z: "\<And>rv. corres_underlying sr nf True r (Q rv) (P' rv) (x rv) y"
  shows
  "\<lbrakk>\<And>s. \<lbrace>PP s\<rbrace> m \<lbrace>\<lambda>_. op = s\<rbrace>; empty_fail m; no_fail P m; \<lbrace>R\<rbrace> m \<lbrace>Q\<rbrace>\<rbrakk>
\<Longrightarrow> corres_underlying sr nf True r (P and R and (\<lambda>s. \<forall>s'. s = s' \<longrightarrow> PP s s'))
  (\<lambda>s'. (\<forall>s. (s, s') \<in> sr \<longrightarrow> (\<forall>rv. Q rv s \<longrightarrow> P' rv s'))) (m >>= x) y"
  apply (insert z)
  apply (clarsimp simp: corres_underlying_def bind_def valid_def empty_fail_def no_fail_def)
  apply (drule_tac x=a in meta_spec)+
  apply (drule_tac x=a in spec)+
  by (auto split: prod.splits; fastforce)

lemma corres_symb_exec_r_str:
  "\<lbrakk>\<And>rv. corres_underlying sr nf nf' r (P rv) (Q' rv) x (y rv);
 \<And>s. \<lbrace>PP' s\<rbrace> m \<lbrace>\<lambda>r. op = s\<rbrace>; \<lbrace>P'\<rbrace> m \<lbrace>Q'\<rbrace>; nf' \<Longrightarrow> no_fail R m\<rbrakk>
\<Longrightarrow> corres_underlying sr nf nf' r (\<lambda>s'. (\<forall>s. (s', s) \<in> sr \<longrightarrow> (\<forall>rv. Q' rv s \<longrightarrow> P rv s'))) (P' and R and (\<lambda>s. \<forall>s'. s = s' \<longrightarrow> PP' s s')) x (m >>= y)"
  apply (clarsimp simp: corres_underlying_def bind_def valid_def empty_fail_def no_fail_def)
  by (auto split: prod.splits; fastforce)

lemma corres_symb_exec_r_str':
  "\<lbrakk>\<And>rv. corres_underlying sr nf nf' r (P rv) (Q' rv) x (y rv);
 \<And>s. \<lbrace>PP' s\<rbrace> m \<lbrace>\<lambda>r. op = s\<rbrace>; \<lbrace>P'\<rbrace> m \<lbrace>Q'\<rbrace>; nf' \<Longrightarrow> no_fail R m\<rbrakk>
\<Longrightarrow> corres_underlying sr nf nf' r (\<lambda>s'. (\<forall>s. (s', s) \<in> sr \<longrightarrow> (\<forall>rv. Q' rv s \<longrightarrow> P rv s'))) (P' and R and (\<lambda>s. \<forall>s'. s = s' \<longrightarrow> PP' s s')) x (m >>= y)"
  apply (clarsimp simp: corres_underlying_def bind_def valid_def empty_fail_def no_fail_def)
  by (auto split: prod.splits; fastforce)

named_theorems corres_symb_exec_ls and corres_symb_exec_rs

lemma corres_symb_exec_l_search[corres_symb_exec_ls]:
  fixes x :: "'b \<Rightarrow> 'a \<Rightarrow> ('d \<times> 'a) set \<times> bool"
  shows
  "\<lbrakk>\<And>s. \<lbrace>PP s\<rbrace> m \<lbrace>\<lambda>_. op = s\<rbrace>; \<And>rv. corres_underlying sr nf True r (Q rv) P' (x rv) y;
   empty_fail m; no_fail P m; \<lbrace>R\<rbrace> m \<lbrace>Q\<rbrace>\<rbrakk>
\<Longrightarrow> corres_underlying sr nf True r (P and R and (\<lambda>s. \<forall>s'. s = s' \<longrightarrow> PP s' s)) P' (m >>= x) y"
  apply (rule corres_guard_imp)
  apply (rule corres_symb_exec_l_str; assumption)
  by auto

lemmas corres_symb_exec_liftME_l_search[corres_symb_exec_ls] =
  corres_symb_exec_l_search[where 'd="'x + 'y", folded liftE_bindE]


lemma corres_symb_exec_r_search[corres_symb_exec_rs]:
  fixes y :: "'b \<Rightarrow> 'a \<Rightarrow> ('e \<times> 'a) set \<times> bool"
  shows
  "\<lbrakk>\<And>s. \<lbrace>PP' s\<rbrace> m \<lbrace>\<lambda>r. op = s\<rbrace>; \<And>rv. corres_underlying sr nf nf' r P (Q' rv) x (y rv);
   nf' \<Longrightarrow> no_fail P' m; \<lbrace>R\<rbrace> m \<lbrace>Q'\<rbrace>\<rbrakk>
\<Longrightarrow> corres_underlying sr nf nf' r P (P' and R and (\<lambda>s. \<forall>s'. s = s' \<longrightarrow> PP' s' s)) x (m >>= y)"
  apply (rule corres_guard_imp)
  apply (rule corres_symb_exec_r_str; assumption)
  by auto

lemmas corres_symb_exec_liftME_r_search[corres_symb_exec_rs] =
  corres_symb_exec_r_search[where 'e="'x + 'y", folded liftE_bindE]

context begin

private method corres_search_wp = solves \<open>((wp | wpc | simp)+)[1]\<close>

text \<open>
  Depth-first search via symbolic execution of both left and right hand
  sides, handling case statements and
  potentially mismatched if statements. The find_goal
  method handles searching each branch of case or if statements, while
  we rely on backtracking to guess the order of left/right executions.

  According to the above rules, a symbolic execution step can be taken
  when the function can be shown to not modify the state. Questions
  of wellformedness (i.e. empty_fail or no_fail) are deferred to the user
  after the search concludes.
\<close>


private method corres_search_frame methods m uses search =
   (#break "corres_search",
    ((corres?, corres_once corres: search)
    | (corresc, find_goal \<open>m\<close>)[1]
    | (rule corres_if_str, find_goal \<open>m\<close>)[1]
    | (rule corres_if_str_rev, find_goal \<open>m\<close>)[1]
    | (rule corres_symb_exec_ls, corres_search_wp, m)
    | (rule corres_symb_exec_rs, corres_search_wp, m)))

text \<open>
   Set up local context where we make sure we don't know how to
   corres our given rule. The search is finished when we can only
   make corres progress once we add our rule back in
\<close>

method corres_search uses search
  declares corres corres_simp corres_symb_exec_ls corres_symb_exec_rs =
  (corres_pre,
   use search[corres del] in
     \<open>use in \<open>corres_search_frame \<open>corres_search search: search\<close> search: search\<close>\<close>)[1]

end

chapter \<open>Misc Helper Lemmas\<close>

lemma corres_assert_assume_str:
  "\<lbrakk> P' \<Longrightarrow> corres_underlying sr nf nf' r P Q f (g ()); \<And>s. Q s \<Longrightarrow> P' \<rbrakk> \<Longrightarrow>
  corres_underlying sr nf nf' r P Q f (assert P' >>= g)"
  by (auto simp: bind_def assert_def fail_def return_def
                 corres_underlying_def)

lemma corres_assert_str[corres]:
  "corres_underlying sr nf nf' dc (%_. Q \<longrightarrow> P) (%_. Q) (assert P) (assert Q)"
  by (auto simp add: corres_underlying_def return_def assert_def fail_def)

lemma corres_stateAssert_implied_frame:
  "\<lbrakk>\<forall>s s'. (s, s') \<in> sr \<longrightarrow> P' s \<longrightarrow> Q' s' \<longrightarrow> A s';
    corres_underlying sr nf nf' r P Q f (g ())\<rbrakk>
\<Longrightarrow> corres_underlying sr nf nf' r (P and P') (Q and Q') f (stateAssert A [] >>= g)"
  apply (clarsimp simp: bind_assoc stateAssert_def)
  apply (rule corres_symb_exec_r [OF _ get_sp])
    apply (rule corres_assume_pre)
    apply (rule corres_assert_assume)
     apply (erule corres_guard_imp, clarsimp+)
   apply (wp | rule no_fail_pre)+
  done

lemma corres_return_str [corres_concrete_r]:
  "corres_underlying sr nf nf' r (\<lambda>_. r a b) \<top> (return a) (return b)"
  by simp

lemma corres_return_str':
  "corres_underlying sr nf nf' r \<top> (\<lambda>_. r a b)  (return a) (return b)"
  by simp

lemma corres_K_bind [corres]:
  "corres_underlying sr nf nf' r P P' f f' \<Longrightarrow>
   corres_underlying sr nf nf' r P P' f (K_bind f' a)"
  by simp

lemma corres_name_pre:
  "\<lbrakk> \<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> sr \<rbrakk>
                 \<Longrightarrow> corres_underlying sr nf nf' r (op = s) (op = s') f g \<rbrakk>
        \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  apply (simp add: corres_underlying_def split_def
                   Ball_def)
  apply blast
  done

chapter \<open>Extra Stuff\<close>

section \<open>Named state rules\<close>

text \<open>This forms the bases of the a similar framework for spec_valid (i.e. induction proofs)\<close>

definition
  "with_state P s \<equiv> \<lambda>s'. s = s' \<and> P s"


lemma corres_name_state:
  assumes "\<And>s s'. (s,s') \<in> sr \<Longrightarrow> corres_underlying sr nf nf' r (with_state P s) (with_state P' s') f f'"
  shows
  "corres_underlying sr nf nf' r P P' f f'"
  apply (insert assms)
  apply (simp add: corres_underlying_def with_state_def)
  by (fastforce split: prod.splits prod.split_asm)

lemma corres_name_state_pre:
  assumes "corres_underlying sr nf nf' r (with_state Q s) (with_state Q' s') f f'"
          "\<And>s. P s \<Longrightarrow> Q s" "\<And>s'. P' s' \<Longrightarrow> Q' s'"
  shows
  "corres_underlying sr nf nf' r (with_state P s) (with_state P' s') f f'"
  apply (insert assms)
  apply (simp add: corres_underlying_def with_state_def)
  by (fastforce split: prod.splits prod.split_asm)

lemma corres_drop_state:
  assumes "corres_underlying sr nf nf' r P P' f f'"
  shows "corres_underlying sr nf nf' r (with_state P s) (with_state P' s') f f'"
  apply (rule corres_guard_imp)
  apply (rule assms)
  by (auto simp add: with_state_def)


lemma corres_split_named:
  assumes x: "(s, s') \<in> sr \<Longrightarrow> corres_underlying sr nf nf' r' (with_state P s) (with_state P' s') a c"
  assumes y: "\<And>ss ss' rv rv'. r' rv rv' \<Longrightarrow> (rv,ss) \<in> fst (a s) \<Longrightarrow> (rv',ss') \<in> fst (c s') \<Longrightarrow>
  (ss,ss') \<in> sr \<Longrightarrow>
  corres_underlying sr nf nf' r (with_state (R rv' rv) ss) (with_state (R' rv rv') ss') (b rv) (d rv')"
  assumes    "(s,s') \<in> sr \<Longrightarrow> Q' s' \<Longrightarrow> s \<turnstile> \<lbrace>Q\<rbrace> a \<lbrace>\<lambda>r s. (\<exists>s'' r''. r' r r'' \<and> (s,s'') \<in> sr \<and> (r'',s'') \<in> fst (c s')) \<longrightarrow> (\<forall>r''. r' r r'' \<longrightarrow>  R r'' r s)\<rbrace>"
             "(s,s') \<in> sr \<Longrightarrow> Q s \<Longrightarrow> s' \<turnstile> \<lbrace>Q'\<rbrace> c \<lbrace>\<lambda>r s'. \<forall>x. r' x r \<longrightarrow> (\<exists>s. (s,s') \<in> sr) \<longrightarrow> R' x r s'\<rbrace>"
  shows      "corres_underlying sr nf nf' r (with_state (P and Q) s) (with_state (P' and Q') s') (a >>= (\<lambda>rv. b rv)) (c >>= (\<lambda>rv'. d rv'))"
  using assms
  apply -
  apply (clarsimp simp: corres_underlying_def bind_def with_state_def)
  apply (clarsimp simp: Bex_def Ball_def valid_def spec_valid_def)
  by meson

lemma normal_corres:
  "A \<longrightarrow> corres_underlying sr nf nf' r P Q f f' \<Longrightarrow>
   corres_underlying sr nf nf' r (K A and P) Q f f'"
  by (auto simp add: corres_underlying_def)

lemma normal_corres':
  "A \<longrightarrow> corres_underlying sr nf nf' r P Q f f' \<Longrightarrow>
   corres_underlying sr nf nf' r P (K A and Q) f f'"
  by (auto simp add: corres_underlying_def)

(* assumes atomized *)

method normal_corres = (((drule uncurry)+)?, drule normal_corres)
method normal_corres' = (((drule uncurry)+)?, drule normal_corres')

experiment
  fixes A B C :: bool
  assumes P: "\<And>P. P"
begin

lemma f: "A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> corres_underlying sr nf nf' r P Q f f'"
  by (rule P)

lemma "corres_underlying sr nf nf' r (K ((A \<and> B) \<and> C) and P) Q f f'"
  by (rule f[atomized, @ \<open>normal_corres\<close>])

end

lemmas [THEN iffD2, corres] =
  corres_liftE_rel_sum
  corres_liftM2_simp
  corres_liftM_simp

(* Error monad *)

lemma corres_splitEE_str [corres_splits]:
  assumes x: "corres_underlying sr nf nf' (f \<oplus> r') P P' a c"
  assumes y: "\<And>rv rv'. r' rv rv' \<Longrightarrow> corres_underlying sr nf nf' (f \<oplus> r) (R rv' rv) (R' rv rv') (b rv) (d rv')"
  assumes z: "\<lbrace>Q\<rbrace> a \<lbrace>\<lambda>r s. \<forall>x. r' r x \<longrightarrow> R x r s\<rbrace>, \<lbrace>\<lambda>_ _. True\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>\<lambda>r s. \<forall>x. r' x r \<longrightarrow> R' x r s\<rbrace>, \<lbrace>\<lambda>_ _. True\<rbrace>"
  shows      "corres_underlying sr nf nf' (f \<oplus> r) (P and Q) (P' and Q') (a >>=E (\<lambda>rv. b rv)) (c >>=E (\<lambda>rv'. d rv'))"
  apply (simp add: bindE_def)
  apply (rule corres_split_str[OF x])
   apply (case_tac rv; case_tac rv'; simp)
   apply (rule corres_guard_imp)
   apply (rule y)
   apply simp
   apply (subgoal_tac "(case (Inr ba, Inr b) of (Inr ba, Inr b) \<Rightarrow> R ba b s
                        | _ \<Rightarrow> True)",
      find_goal \<open>assumption\<close>)
   apply (subgoal_tac "(case (Inr b, Inr ba) of (Inr b, Inr ba) \<Rightarrow> R' b ba s
                        | _ \<Rightarrow> True)",
      find_goal \<open>assumption\<close>)
    apply clarsimp+
   apply (insert z)
   by (fastforce simp: valid_def validE_def split: sum.splits)+

lemma corres_returnOk_str [corres_concrete_r]:
  "corres_underlying sr nf nf' r (\<lambda>_. r (Inr a) (Inr b)) \<top> (returnOk a) (returnOk b)"
  by (simp add: returnOk_def)

lemma corres_assertE_str[corres]:
  "corres_underlying sr nf nf' (f \<oplus> dc) (\<lambda>_. Q \<longrightarrow> P) (\<lambda>_. Q) (assertE P) (assertE Q)"
  by (auto simp add: corres_underlying_def returnOk_def return_def assertE_def fail_def)

lemmas corres_symb_exec_whenE_l_search[corres_symb_exec_ls] =
  corres_symb_exec_l_search[where 'd="'x + 'y", folded liftE_bindE]

(* Failure *)

lemma corres_fail_str[corres_concrete_P]:
  "(\<And>s s'. \<lbrakk>(s, s') \<in> sr; P s; P' s'\<rbrakk> \<Longrightarrow> False) \<Longrightarrow> corres_underlying sr nf True R P P' f fail"
  by (fastforce intro!: corres_fail)

lemma corres_fail_str'[corres]:
  "corres_underlying sr nf False (\<lambda>_ _. False) (\<lambda>_. True) (\<lambda>_. True) f fail"
  by (fastforce intro!: corres_fail)

(* Wrap it up in a big hammer. Small optimization to avoid searching when no fact is given. *)


method corressimp uses simp search wp
  declares corres corres_splits corres_simp =
  ((corres
    | use hoare_vcg_precond_imp[wp_comb del] hoare_vcg_precond_imp[wp_pre del] in
      \<open>use in \<open>wp add: wp\<close>\<close>
    | wpc | clarsimp simp: simp simp del: corres_simp_del |
      (match search in _ \<Rightarrow> \<open>corres_search search: search\<close>))+)[1]

declare corres_return[corres_simp_del]

end
