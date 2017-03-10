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

lemma stronger_corres_guard_imp_str:
  assumes x: "corres_underlying sr nf nf' r Q Q' f g"
  assumes y: "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> sr \<rbrakk> \<Longrightarrow> Q s \<and> Q' s'"
  shows      "corres_underlying sr nf nf' r P P' f g"
  using x by (auto simp: y corres_underlying_def)

section \<open>Corres Method\<close>

text \<open>Handles structured decomposition of corres goals\<close>

named_theorems
  corres_splits and
  corres_simp and (* conservative simplification rules applied when no progress can be made *)
  corres (* solving terminal corres subgoals *)

context begin

text \<open>Testing for schematic goal state\<close>

private definition "my_false s \<equiv> False"
private definition "my_false' s \<equiv> False"

private lemma corres_my_false: "corres_underlying sr nf nf' r my_false my_false' f f'"
  by (simp add: my_false_def[abs_def] my_false'_def[abs_def])

private lemma corres_trivial:
  "corres_underlying sr nf nf' r P P' f f' \<Longrightarrow> corres_underlying sr nf nf' r P P' f f'"
  by simp

method check_corres = succeeds \<open>rule corres_trivial\<close>

private method corres_pre =
  (check_corres, (fails \<open>rule corres_my_false\<close>, rule stronger_corres_guard_imp_str)?)


lemma corres_fold_dc:
  "corres_underlying sr nf nf' dc P P' f f' \<Longrightarrow> corres_underlying sr nf nf' (\<lambda>_ _. True) P P' f f'"
  by (simp add: dc_def[abs_def])

private method corres_fold_dc =
  (match conclusion in
    "corres_underlying _ _ _ (\<lambda>_ _. True) _ _ _ _" \<Rightarrow> \<open>rule corres_fold_dc\<close>)

method corres_once declares corres_splits corres corres_simp =
   ((check_corres,corres_fold_dc?,
    #break "corres",
    ( determ \<open>rule corres\<close>
    | (rule corres_splits, corres_once)
    | (simp only: corres_simp, corres_once)
    )))


method corres declares corres_splits corres corres_simp =
  (corres_pre, (corres_once)+)[1]

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
  Let_def

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

method corresc =
  (check_corres, wpc; wpc; (solves \<open>rule FalseE, simp?, (erule (1) wpc_contr_helper, simp)?\<close>)?)[1]

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

context begin

private lemma corres_symb_exec_l_search:
  "\<lbrakk>\<And>s. \<lbrace>PP s\<rbrace> m \<lbrace>\<lambda>_. op = s\<rbrace>; \<And>rv. corres_underlying sr nf True r (Q rv) P' (x rv) y;
   empty_fail m; no_fail P m; \<lbrace>R\<rbrace> m \<lbrace>Q\<rbrace>\<rbrakk>
\<Longrightarrow> corres_underlying sr nf True r (P and R and (\<lambda>s. \<forall>s'. s = s' \<longrightarrow> PP s' s)) P' (m >>= x) y"
  apply (rule corres_guard_imp)
  apply (rule corres_symb_exec_l_str; assumption)
  by auto

private lemma corres_symb_exec_r_search:
  "\<lbrakk>\<And>s. \<lbrace>PP' s\<rbrace> m \<lbrace>\<lambda>r. op = s\<rbrace>; \<And>rv. corres_underlying sr nf nf' r P (Q' rv) x (y rv);
  \<lbrace>P'\<rbrace> m \<lbrace>Q'\<rbrace>; nf' \<Longrightarrow> no_fail P' m\<rbrakk>
\<Longrightarrow> corres_underlying sr nf nf' r P (P' and (\<lambda>s. \<forall>s'. s = s' \<longrightarrow> PP' s' s)) x (m >>= y)"
  apply (rule corres_guard_imp)
  apply (rule corres_symb_exec_r_str; assumption)
  by auto

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
    | (rule corres_symb_exec_l_search, corres_search_wp, m)
    | (rule corres_symb_exec_r_search, corres_search_wp, m)))

text \<open>
   Set up local context where we make sure we don't know how to
   corres our given rule. The search is finished when we can only
   make corres progress once we add our rule back in
\<close>

method corres_search uses search =
  (use search[corres del] in
   \<open>use in \<open>corres_search_frame \<open>corres_search search: search\<close> search: search\<close>\<close>)

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

end
