(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory RCorres
imports
  Corres_UL DetWPLib SubMonadLib
begin

chapter \<open>An approach to correspondence with general relations\<close>

text \<open>
  When wanting to show correspondence between an abstract monadic function @{term f} and a concrete
  monadic function @{term f'}, it is occasionally useful for us to be able to state a relation
  between all four values from the pair @{term "(rv', t')"} in the set of results of @{term f'}
  and the pair @{term "(rv, t)"} in the set of results of @{term f}. This is a partial
  generalisation of our usual @{const corres_underlying} framework, which allows for us to state a
  relation between the return values, and a relation between the states, but does not allow more
  general "mixing" of these four values. We envisage that this greater generality may be of use when
  these functions return especially complicated return values, and which we would also like to
  relate to the returned states. An example that is used within the proofs is list_queue_relation.

  This shares many similarities with Hoare triples, as seen by the split rule for
  @{const Nondet_Monad.bind}, as well as the lifting rules, though there are some important
  differences involving determinacy that are explained below.

  Note that rcorres is not a full generalisation of @{const corres_underlying}, in that it does not
  address failure. While it may be tempting to strengthen rcorres to include this, it does not seem
  to pair well with our general approach to showing rcorres goals. More explicitly, lifting rules
  play a prominent role in the proofs we wish to perform for rcorres goals. We have lifting rules
  for the usual Boolean connectives, but will also wish to lift an rcorres goal to a @{const valid}
  goal when the postcondition of the rcorres goal mentions only the return value and state from
  one of the two monads. These lifting rules often require @{const no_fail} assumptions, and so when
  lifting an rcorres goal with a concrete function that is a @{const Nondet_Monad.bind} of other
  functions, we will immediately be required to show @{const no_fail} for the composite function
  anyway. Therefore, we have chosen to keep failure separate. The section below regarding
  interactions with @{const no_fail} includes a rule that allows us to show @{const no_fail} for
  composite functions by transforming complex predicates with rcorres. The section below regarding
  @{const corres_underlying} shows the relation between rcorres and @{const corres_underlying}.\<close>

definition rcorres ::
  "('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('s, 'a) nondet_monad \<Rightarrow> ('t, 'b) nondet_monad
   \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 's \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "rcorres R f f' R'\<equiv>
     \<forall>s s'. R s s' \<longrightarrow> (\<forall>(rv', t') \<in> fst (f' s'). \<exists>(rv, t) \<in> fst (f s). R' rv rv' t t')"


section \<open>Interactions with @{const valid}\<close>

lemma rcorres_as_valid:
  "rcorres R f f' R' \<longleftrightarrow> (\<forall>s. \<lbrace>\<lambda>s'. R s s'\<rbrace> f' \<lbrace>\<lambda>rv' t'. \<exists>(rv, t) \<in> fst (f s). R' rv rv' t t'\<rbrace>)"
  by (clarsimp simp: rcorres_def valid_def)

lemmas valid_from_rcorres = rcorres_as_valid[THEN iffD1]

lemmas rcorres_from_valid = rcorres_as_valid[THEN iffD2]

lemma valid_from_rcorres_det:
  "\<lbrakk>fst (f s) = {(rv, t)}; rcorres R f f' R'\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s'. R s s'\<rbrace> f' \<lbrace>\<lambda>rv' t'. R' rv rv' t t'\<rbrace>"
  by (fastforce simp: rcorres_def valid_def)

lemma valid_from_rcorres_det_return:
  "rcorres R (return v) f' R' \<Longrightarrow> \<lbrace>\<lambda>s'. R s s'\<rbrace> f' \<lbrace>\<lambda>rv' t'. R' v rv' s t'\<rbrace>"
  by (clarsimp simp: rcorres_def valid_def return_def)

lemma rcorres_from_valid_det:
  assumes "\<And>s'. det_wp (\<lambda>s. R s s') f"
  assumes "\<And>rv s t. (rv, t) \<in> fst (f s) \<Longrightarrow> \<lbrace>\<lambda>s'. R s s'\<rbrace> f' \<lbrace>\<lambda>rv' t'. R' rv rv' t t'\<rbrace>"
  shows "rcorres R f f' R'"
  using assms
  by (force simp: rcorres_def det_wp_def valid_def)


section \<open>Manipulating the precondition and the postcondition\<close>

lemma rcorres_weaken_pre:
  "\<lbrakk>rcorres Q' f f' R; \<And>s s'. Q s s' \<Longrightarrow> Q' s s'\<rbrakk> \<Longrightarrow> rcorres Q f f' R"
  by (fastforce simp: rcorres_def)

lemma rcorres_strengthen_post:
  "\<lbrakk>rcorres R f f' Q'; \<And>rv rv' s s'. Q' rv rv' s s' \<Longrightarrow> R' rv rv' s s'\<rbrakk>
   \<Longrightarrow> rcorres R f f' R'"
  apply (clarsimp simp: rcorres_def)
  apply force
  done

lemmas rcorres_post_imp = rcorres_strengthen_post[rotated]

lemma rcorres_add_to_pre:
  "\<lbrakk>\<And>s s'. R s s' \<Longrightarrow> Q s s'; rcorres (\<lambda>s s'. R s s' \<and> Q s s') f f' R'\<rbrakk>
   \<Longrightarrow> rcorres R f f' R'"
  by (fastforce simp: rcorres_def)

lemma rcorres_req:
  "\<lbrakk>\<And>s s'. R s s' \<Longrightarrow> F; F \<Longrightarrow> rcorres R f f' R'\<rbrakk> \<Longrightarrow> rcorres R f f' R'"
  by (clarsimp simp: rcorres_def)

lemma rcorres_gen_asm:
  "\<lbrakk>P \<Longrightarrow> rcorres R f f' R'; \<And>s s'. R s s' \<Longrightarrow> P\<rbrakk> \<Longrightarrow> rcorres (R and (\<lambda>_ _. P)) f f' R'"
  by (fastforce simp: rcorres_def)

lemma rcorres_assume_pre:
  "\<lbrakk>\<And>s s'. R s s' \<Longrightarrow> rcorres R f f' R'\<rbrakk> \<Longrightarrow> rcorres R f f' R'"
  by (rule rcorres_req)

lemma rcorres_assume_name_pre:
  "\<lbrakk>\<And>s s'. R s s' \<Longrightarrow> rcorres (\<lambda>t t'. t = s \<and> t' = s')  f f' R'\<rbrakk> \<Longrightarrow> rcorres R f f' R'"
  by (fastforce simp: rcorres_def)


section \<open>Interactions with @{const Nondet_Monad.bind}\<close>

lemma rcorres_split:
  "\<lbrakk>\<And>rv rv'. rcorres (Q rv rv') (b rv) (d rv') R; rcorres P a c Q\<rbrakk>
   \<Longrightarrow> rcorres P (a >>= b) (c >>= d) R"
  apply (clarsimp simp: rcorres_def bind_def)
  apply (rename_tac s s' rv' t' rv'' t'')
  apply (drule_tac x=s in spec)
  apply (drule_tac x=s' in spec)
  apply clarsimp
  apply (drule_tac x="(rv', t')" in bspec, fastforce)
  by force

lemma rcorres_return:
  "(\<And>s s'. R s s' \<Longrightarrow> R' v v' s s') \<Longrightarrow> rcorres R (return v) (return v') R'"
  by (clarsimp simp: rcorres_def return_def)

lemma rcorres_add_return_l:
 "rcorres R (f >>= return) g R' \<Longrightarrow> rcorres R f g R'"
  by (simp add: rcorres_def)

lemma rcorres_add_return_r:
 "rcorres R f (g >>= return) R' \<Longrightarrow> rcorres R f g R'"
  by (simp add: rcorres_def)


section \<open>Symbolic execution and assertions\<close>

lemma rcorres_symb_exec_l:
  "\<lbrakk>\<And>s'. \<lbrace>\<lambda>s. R s s'\<rbrace> a \<lbrace>\<lambda>rv s. Q rv s s'\<rbrace>; \<And>s s'. R s s' \<Longrightarrow> \<lbrace>(=) s\<rbrace> a \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>;
    \<And>rv. rcorres (\<lambda>s s'. R s s' \<and> Q rv s s') (b rv) c R'\<rbrakk>
   \<Longrightarrow> rcorres R (a >>= b) c R'"
  apply (clarsimp simp: rcorres_def bind_def exs_valid_def)
  apply (rename_tac s s' rv' t')
  apply (drule_tac x=s in meta_spec)
  apply (drule_tac x=s' in meta_spec)+
  apply clarsimp
  apply (rename_tac rv t)
  apply (rule_tac x="(rv, t)" in bexI[rotated], fastforce)
  apply (fastforce simp: valid_def)
  done

lemma rcorres_symb_exec_r:
  "\<lbrakk>\<And>s. \<lbrace>\<lambda>s'. R s s'\<rbrace> c \<lbrace>\<lambda>rv s'. Q rv s s'\<rbrace>;
    \<And>rv'. rcorres (\<lambda>s s'. Q rv' s s') a (d rv') R'\<rbrakk>
   \<Longrightarrow> rcorres R a (c >>= d) R'"
  by (force simp: rcorres_def bind_def valid_def)

lemma rcorres_assert_l:
  "\<lbrakk>P \<Longrightarrow> rcorres R (b ()) c R'\<rbrakk> \<Longrightarrow> rcorres (\<lambda>s s'. R s s' \<and> P) (assert P >>= b) c R'"
  by (fastforce intro: rcorres_assume_pre)

lemma rcorres_assert_l_fwd:
  "\<lbrakk>\<And>s s'. R s s' \<Longrightarrow> P; rcorres (\<lambda>s s'. R s s' \<and> P) (b ()) c R'\<rbrakk>
   \<Longrightarrow> rcorres R (assert P >>= b) c R'"
  by (fastforce intro: rcorres_assume_pre)

lemma rcorres_assert_r:
  "\<lbrakk>P \<Longrightarrow> rcorres R a (c ()) R'\<rbrakk> \<Longrightarrow> rcorres (\<lambda>s s'. R s s' \<and> P) a (assert P >>= c) R'"
  by (fastforce intro: rcorres_assume_pre)

lemma rcorres_assert_r_fwd:
  "\<lbrakk>\<And>s s'. R s s' \<Longrightarrow> P; rcorres (\<lambda>s s'. R s s' \<and> P) a (c ()) R'\<rbrakk>
   \<Longrightarrow> rcorres R a (assert P >>= c) R'"
  by (fastforce intro: rcorres_assume_pre)

lemma rcorres_stateAssert_l:
  "rcorres R (b ()) c R' \<Longrightarrow> rcorres (\<lambda>s s'. R s s' \<and> P s) (stateAssert P xs >>= b) c R'"
  apply (rule rcorres_symb_exec_l[OF stateAssert_sp])
   apply (wpsimp simp: stateAssert_def)
  apply (fastforce intro: rcorres_weaken_pre)
  done

lemma rcorres_stateAssert_l_fwd:
  "\<lbrakk>\<And>s s'. R s s' \<Longrightarrow> Q s; rcorres (\<lambda>s s'. R s s' \<and> Q s) (f ()) f' R'\<rbrakk>
   \<Longrightarrow> rcorres R (stateAssert Q xs >>= f) f' R'"
  apply (rule rcorres_symb_exec_l)
    apply (rule stateAssert_sp)
   apply (wpsimp simp: stateAssert_def)
  apply fastforce
  done

lemma rcorres_stateAssert_r:
  "rcorres R a (c ()) R' \<Longrightarrow> rcorres (\<lambda>s s'. R s s' \<and> P s) a (stateAssert P xs >>= c) R'"
  apply (rule rcorres_symb_exec_r[OF stateAssert_sp])
   apply (wpsimp simp: stateAssert_def)
  apply (fastforce intro: rcorres_weaken_pre)
  done

lemma rcorres_stateAssert_r_fwd:
  "rcorres (\<lambda>s s'. R s s' \<and> Q s') f (f' ()) R' \<Longrightarrow> rcorres R f (stateAssert Q xs >>= f') R'"
  apply (rule rcorres_weaken_pre)
   apply (rule rcorres_symb_exec_r)
     apply (rule stateAssert_sp)
   apply (fastforce intro: rcorres_weaken_pre)
  apply fastforce
  done

lemma rcorres_return_stateAssert:
  "rcorres (\<lambda>s s'. R' s s' \<and> P s') (return ()) (stateAssert P []) (\<lambda>_ _. R')"
  apply (rule rcorres_add_return_r)
  apply (rule rcorres_stateAssert_r_fwd)
  apply (fastforce intro: rcorres_return)
  done

lemma rcorres_gets_the:
  "no_ofail P f
   \<Longrightarrow> rcorres
         (\<lambda>s s'. (\<forall>rv rv'. f s = Some rv \<longrightarrow> f' s' = Some rv' \<longrightarrow> Q rv rv' s s') \<and> P s)
         (gets_the f) (gets_the f') Q"
  by (force simp: rcorres_def no_ofail_def gets_the_def gets_def Nondet_Monad.bind_def get_def
                  return_def assert_opt_def fail_def
           split: option.splits)

lemma rcorres_gets_the_fwd:
  "\<lbrakk>\<And>rv rv' s s'. \<lbrakk>P s s'; f s = Some rv; f' s' = Some rv'\<rbrakk> \<Longrightarrow> rrel rv rv';
    \<And>s'. no_ofail (\<lambda>s. P s s') f \<rbrakk>
   \<Longrightarrow> rcorres P (gets_the f) (gets_the f') (\<lambda>rv rv' _ _. rrel rv rv')"
  apply (rule rcorres_assume_name_pre)
  apply (fastforce intro!: rcorres_weaken_pre[OF rcorres_gets_the])
  done

lemma rcorres_rrel:
  "\<lbrakk>rcorres P (gets_the f) (gets_the g) (\<lambda>rv rv' _ _. rrel rv rv'); P s s';
    f s = Some rv; g s' = Some rv'\<rbrakk>
   \<Longrightarrow> rrel rv rv'"
  by (force simp: rcorres_def get_def monad_simps)

lemma rcorres_rrel_eq:
  "\<lbrakk>rcorres P (gets_the f) (gets_the g) (\<lambda>rv rv' _ _. rv = rv'); P s s';
    \<exists>rv. f s = Some rv; \<exists>rv'. g s' = Some rv'\<rbrakk>
   \<Longrightarrow> f s = g s'"
  by (clarsimp, frule rcorres_rrel, fastforce+)

lemma rcorres_rrel':
  "\<lbrakk>rcorres P (gets_the f) (gets_the g) (\<lambda>rv rv' _ _. rrel rv rv'); no_ofail (\<lambda>s'. Q s s') g;
    P s s'; Q s s'\<rbrakk>
   \<Longrightarrow> \<exists>rv rv'. f s = Some rv \<and> g s' = Some rv' \<and> rrel rv rv'"
  apply (clarsimp simp: rcorres_def)
  apply (drule_tac x=s in spec)
  apply (force simp: no_ofail_def get_def monad_simps split: option.splits)
  done

lemma rcorres_split_gets_the:
  "\<lbrakk>rcorres P (gets_the f) (gets_the g) (\<lambda>rv rv' _ _. rrel rv rv'); no_ofail Q f;
    \<And>rv rv'. rrel rv rv' \<Longrightarrow> rcorres (R rv rv') (b rv) (d rv') R'\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. P s s' \<and> Q s
                 \<and> (\<forall>rv rv'. f s = Some rv \<longrightarrow> g s' = Some rv' \<longrightarrow> rrel rv rv' \<longrightarrow> R rv rv' s s'))
         (gets_the f >>= b) (gets_the g >>= d) R'"
  (is "\<lbrakk>_; _; \<And>_ _. _ \<Longrightarrow> _\<rbrakk> \<Longrightarrow> rcorres ?pre _ _ _")
  apply (rule_tac Q="\<lambda>rv rv' s s'. ?pre s s' \<and> f s = Some rv \<and> g s' = Some rv' \<and> rrel rv rv'"
               in rcorres_split[rotated])
   apply (rule rcorres_from_valid_det)
    apply wpsimp
    apply (fastforce dest: no_ofailD[where m=f])
   apply wpsimp
   apply (fastforce dest: rcorres_rrel simp: in_monad)
  apply (rule_tac F="rrel rv rv'" in rcorres_req)
   apply fastforce
  apply (fastforce intro: rcorres_weaken_pre)
  done

lemma rcorres_split_gets_the_fwd:
  "\<lbrakk>rcorres R (gets_the f) (gets_the g) (\<lambda>rv rv' _ _. rrel rv rv'); \<And>s'. no_ofail (\<lambda>s. R s s') f;
    \<And>rv rv'.
      rcorres
        (\<lambda>s s'. R s s' \<and> f s = Some rv \<and> g s' = Some rv' \<and> rrel rv rv' )
        (b rv) (d rv') R'\<rbrakk>
   \<Longrightarrow> rcorres R (gets_the f >>= b) (gets_the g >>= d) R'"
  apply (rule rcorres_assume_name_pre)
  apply (fastforce intro: rcorres_weaken_pre[OF rcorres_split_gets_the])
  done


section \<open>if\<close>

lemma rcorres_if_l:
  "\<lbrakk>b \<Longrightarrow> rcorres T f f' R'; \<not> b \<Longrightarrow> rcorres F g f' R'\<rbrakk>
  \<Longrightarrow> rcorres (T and F) (if b then f else g) f' R'"
  by (fastforce simp: rcorres_def)

lemmas rcorres_if_l_fwd = rcorres_if_l[where T=R and F=R for R, simplified]

lemma rcorres_if_r:
  "\<lbrakk>b \<Longrightarrow> rcorres T f f' R'; \<not> b \<Longrightarrow> rcorres F f g' R'\<rbrakk>
  \<Longrightarrow> rcorres (T and F) f (if b then f' else g') R'"
  by (fastforce simp: rcorres_def)

lemmas rcorres_if_r_fwd = rcorres_if_r[where T=R and F=R for R, simplified]


section \<open>Lifting rules\<close>

text \<open>
  We would like a lifting rule for conjunctions, and so a rule with assumptions including
  @{const rcorres} statements for the postconditions @{term R'} and @{term Q'} separately, with
  conclusion an @{term rcorres} statement for the conjunction @{term "R' \<and> Q'"}, roughly speaking.
  The inclusion of the @{term det_wp} assumption in the following rule warrants some explanation.

  Noting the definition of @{const rcorres}, suppose that we have two states @{term s} and @{term s'}
  which satisfy the precondition of the conclusion, as well as a pair @{term "(rv', t')"} in the
  result of @{term f'}. We must show that there is a pair @{term "(rv, t)"} in the result of
  @{term f} such that @{term "R' rv rv' t t' \<and> Q' rv rv' t t'"} holds.

  From our assumptions, we know that there is there is some pair @{term "(rv1, t1)"} in the result
  of @{term f} such that @{term "R' rv1 rv' t1 t'"} holds, and that there is some pair
  @{term "(rv2, t2)"} in the result of @{term f} such that @{term "Q' rv2 rv' t2 t' holds"}.
  However, without any further assumptions on @{term f}, we cannot infer that
  @{term "(rv1, t1) = (rv2, t2)"} and therefore that there is a pair @{term "(rv, t)"} in the
  result of @{term f} such that the desired conjunction holds. The @{const det_wp}
  assumption does allow us to make this inference, and so we include this assumption in our rule.

  It does not seem possible for us to state an adequate lifting rule for conjunction for
  @{const rcorres} with a nondeterministic abstract monadic function, and so in such a situation,
  it may be necessary to unfold the definition of @{const rcorres}.\<close>
lemma rcorres_conj_lift:
  "\<lbrakk>det_wp P f; rcorres Q f f' R'; rcorres R f f' Q'\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. P s \<and> Q s s' \<and> R s s')
         f f' (\<lambda>rv rv' s s'. R' rv rv' s s' \<and> Q' rv rv' s s')"
  by (fastforce simp: rcorres_def det_wp_def)

lemma rcorres_conj_lift_fwd:
  "\<lbrakk>\<And>s'. det_wp (\<lambda>s. R s s') f; rcorres R f f' R'; rcorres R f f' Q'\<rbrakk>
   \<Longrightarrow> rcorres R f f' (\<lambda>rv rv' s s'. R' rv rv' s s' \<and> Q' rv rv' s s')"
  apply (rule rcorres_assume_name_pre)
  apply (fastforce intro!: rcorres_weaken_pre[OF rcorres_conj_lift])
  done

lemma rcorres_imp_lift:
  "\<lbrakk>rcorres P' f f' (\<lambda>rv rv' s s'. \<not> P rv rv' s s'); rcorres Q' f f' Q\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. (\<not> P' s s' \<longrightarrow> Q' s s') \<and> R s s')
         f f' (\<lambda>rv rv' s s'. P rv rv' s s' \<longrightarrow> Q rv rv' s s')"
  by (fastforce simp: rcorres_def det_wp_def)

lemma rcorres_imp_lift_fwd:
  "\<lbrakk>rcorres (\<lambda>s s'. R s s' \<and> \<not> A s s') f f' (\<lambda>_ _ s s'. \<not> A s s');
    rcorres (\<lambda>s s'. R s s' \<and> A s s') f f' (\<lambda>rv rv' s s'. R' rv rv' s s')\<rbrakk>
   \<Longrightarrow> rcorres R f f' (\<lambda>rv rv' s s'. A s s' \<longrightarrow> R' rv rv' s s')"
  by (rule rcorres_weaken_pre, rule rcorres_imp_lift, fastforce+)

text
  \<open>As with @{thm rcorres_conj_lift}, the @{const det_wp} assumption seems necessary in order
   to state an adequate lifting rule for @{const All}.\<close>
lemma rcorres_allI:
  "\<lbrakk>det_wp P f; \<And>x. rcorres (\<lambda>s s'. R x s s') f f' (\<lambda>rv rv' s s'. R' x rv rv' s s')\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. P s \<and> (\<forall>x. R x s s')) f f' (\<lambda>rv rv' s s'. \<forall>x. R' x rv rv' s s')"
  by (fastforce simp: rcorres_def det_wp_def singleton_iff)

lemma rcorres_allI_fwd:
  "\<lbrakk>\<And>s'. det_wp (\<lambda>s. R s s') f; \<And>x. rcorres R f f' (\<lambda>rv rv' s s'. R' x rv rv' s s')\<rbrakk>
   \<Longrightarrow> rcorres R f f' (\<lambda>rv rv' s s'. \<forall>x. R' x rv rv' s s')"
  apply (rule rcorres_assume_name_pre)
  apply (fastforce intro!: rcorres_weaken_pre[OF rcorres_allI])
  done

lemma rcorres_prop:
  "\<lbrakk>no_fail (\<lambda>s. Q s) f; empty_fail f\<rbrakk> \<Longrightarrow> rcorres (\<lambda>s s'. Q s \<and> R')  f f' (\<lambda>_ _ _ _. R')"
  by (fastforce simp: rcorres_def no_fail_def empty_fail_def)

lemma rcorres_prop_fwd:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f; \<And>s s'. Q s s' \<Longrightarrow> R'\<rbrakk>
   \<Longrightarrow> rcorres Q f f' (\<lambda>_ _ _ _. R')"
  by (fastforce simp: rcorres_def no_fail_def empty_fail_def)

lemma rcorres_lift_abs:
  "\<lbrakk>\<And>x. rcorres (\<lambda>s s'. p s = x \<and> R x s s' \<and> Q s s') f f' (\<lambda>rv rv' s s'. R' rv rv' x s s');
    \<And>P s'. \<lbrace>\<lambda>s. P (p s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (p s)\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. R (p s) s s' \<and> Q s s') f f' (\<lambda>rv rv' s s'. R' rv rv' (p s) s s')"
  apply (clarsimp simp: rcorres_def valid_def)
  apply (rename_tac s s' rv' t')
  apply (drule_tac x="p s" in meta_spec)
  apply (drule_tac x=s in spec)
  apply (drule_tac x=s' in spec)
  apply fast
  done

lemma rcorres_lift_conc:
  "\<lbrakk>\<And>x. rcorres (\<lambda>s s'. p s' = x \<and> R s x s' \<and> Q s s') f f' (\<lambda>rv rv' s s'. R' rv rv' s x s');
    \<And>P s. \<lbrace>\<lambda>s'. P (p s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (p s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. R s (p s') s' \<and> Q s s') f f' (\<lambda>rv rv' s s'. R' rv rv' s (p s') s')"
  apply (clarsimp simp: rcorres_def valid_def)
  apply (rename_tac s s' rv' t')
  apply (drule_tac x="p s'" in meta_spec)
  apply (drule_tac x=s in spec)
  apply (drule_tac x=s' in spec)
  apply fast
  done

lemma rcorres_lift_abs_only:
  "\<lbrakk>no_fail P f; empty_fail f; \<And>s'. \<lbrace>\<lambda>s. R s s'\<rbrace> f \<lbrace>\<lambda>rv s. R' rv s\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. P s \<and> R s s') f f' (\<lambda>rv _ s _. R' rv s)"
  by (fastforce simp: rcorres_def valid_def no_fail_def empty_fail_def)

lemma rcorres_lift_abs_only_fwd:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. R s s') f; empty_fail f; \<And>s'. \<lbrace>\<lambda>s. R s s'\<rbrace> f \<lbrace>\<lambda>rv s. R' rv s\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres R f f' (\<lambda>rv _ s _. R' rv s)"
  apply (rule rcorres_assume_name_pre)
  apply (fastforce intro!: rcorres_weaken_pre[OF rcorres_lift_abs_only])
  done

lemma rcorres_lift_conc_only:
  "\<lbrakk>no_fail P f; empty_fail f; \<And>s. \<lbrace>\<lambda>s'. R s s'\<rbrace> f' \<lbrace>\<lambda>rv' s'. R' rv' s'\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. P s \<and> R s s') f f' (\<lambda>_ rv' _ s'. R' rv' s')"
  by (fastforce simp: rcorres_def valid_def no_fail_def empty_fail_def)

lemma rcorres_lift_conc_only_fwd:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. R s s') f; empty_fail f; \<And>s. \<lbrace>\<lambda>s'. R s s'\<rbrace> f' \<lbrace>\<lambda>rv' s'. R' rv' s'\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres R f f' (\<lambda>_ rv' _ s'. R' rv' s')"
  apply (rule rcorres_assume_name_pre)
  apply (fastforce intro!: rcorres_weaken_pre[OF rcorres_lift_conc_only])
  done


section \<open>Interactions with @{const corres_underlying}\<close>

lemma corres_underlying_from_rcorres:
  "\<lbrakk>nf' \<Longrightarrow> no_fail (\<lambda>s'. \<exists>s. (s, s') \<in> srel \<and> P s \<and> P' s') f';
    rcorres (\<lambda>s s'. P s \<and> P' s' \<and> (s, s') \<in> srel) f f' (\<lambda>rv rv' s s'. (s, s') \<in> srel \<and> r rv rv')\<rbrakk>
   \<Longrightarrow> corres_underlying srel nf nf' r P P' f f'"
  by (fastforce simp: corres_underlying_def rcorres_def no_fail_def)

lemma rcorres_from_corres_underlying:
  "\<lbrakk>corres_underlying srel nf nf' r P P' f f'; nf \<Longrightarrow> no_fail P f\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. P s \<and> P' s' \<and> (s, s') \<in> srel) f f' (\<lambda>rv rv' s s'. (s, s') \<in> srel \<and> r rv rv')"
  by (fastforce simp: corres_underlying_def rcorres_def no_fail_def)


section \<open>Interactions with @{const no_fail}\<close>

lemma no_fail_rcorres_bind:
  "\<lbrakk>\<And>rv rv'. no_fail (\<lambda>s'. \<exists>s. R rv rv' s s') (g' rv'); rcorres Q f f' R;
    no_fail (\<lambda>s'. \<exists>s. P s s') f'\<rbrakk>
   \<Longrightarrow> no_fail (\<lambda>s'. \<exists>s. P s s' \<and> Q s s') (f' >>= g')"
  apply (clarsimp simp: no_fail_def rcorres_def bind_def)
  apply (rename_tac s' s)
  apply (drule_tac x=s' in spec)
  apply fast
  done


section \<open>Automation\<close>

named_theorems rcorres
named_theorems rcorres_lift

method rcorres_step uses rcorres_del rcorres_lift_del wp simp declares rcorres rcorres_lift =
  declaring rcorres_del[rcorres del] rcorres_lift_del[rcorres_lift del] in
  \<open>rule rcorres
   | rule rcorres_split rcorres_conj_lift
   | rule rcorres_lift rcorres_lift_abs_only rcorres_lift_conc_only
   | wpsimp wp: wp simp: simp\<close>

declare rcorres_weaken_pre[wp_pre]

method rcorres uses rcorres_del rcorres_lift_del wp simp declares rcorres rcorres_lift =
  wp_pre,
  ((rcorres_step rcorres: rcorres rcorres_del: rcorres_del
                 rcorres_lift: rcorres_lift rcorres_lift_del: rcorres_lift_del
                 wp: wp simp: simp)+)[1]

text \<open>
  This method is intended to be used to solve or make progress with @{const rcorres} goals via
  lifting, when the precondition is not schematic.\<close>
method rcorres_conj_lift methods solve uses rule simp wp =
  (rule rcorres_conj_lift_fwd,
   (solves \<open>rule det_wp_pre, rule rule, clarsimp\<close> | solves \<open>wpsimp wp: wp simp: simp\<close>))?,
  rule rcorres_weaken_pre,
  (rule rcorres_lift, (solves \<open>rule rule\<close> | solves \<open>wpsimp wp: wp simp: simp\<close>)+)[1],
  solves solve

experiment
  fixes f f' :: "('s, 'r) nondet_monad"
  fixes g g' h :: "'r \<Rightarrow> ('s, 'r) nondet_monad"

  fixes P Q :: "'s \<Rightarrow> bool"
  fixes R V :: "'s \<Rightarrow> 's \<Rightarrow> bool"
  fixes S T U :: "'r \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"

  assumes [wp]: "f \<lbrace>P\<rbrace>" "\<And>rv. g rv \<lbrace>P\<rbrace>" "f \<lbrace>Q\<rbrace>" "\<And>rv. g rv \<lbrace>Q\<rbrace>"
  assumes [wp]: "no_fail P f" "\<And>rv. no_fail P (g rv)"
  assumes [wp]: "det_wp P f"
  assumes [wp]: "empty_fail f" "\<And>rv. empty_fail (g rv)"

  assumes [rcorres]: "rcorres R f f' S"
  assumes [rcorres]: "\<And>rv rv'. rcorres (S rv rv') (g rv) (g' rv') T"
  assumes [rcorres]: "\<And>rv rv'. rcorres (T rv rv') (h rv) (return rv') U"

  assumes
    lift[rcorres_lift]:
      "\<And>(f :: ('s, 'r) nondet_monad) (f' :: ('s, 'r) nondet_monad).
         \<lbrakk>no_fail P f; empty_fail f; f \<lbrace>Q\<rbrace>\<rbrakk> \<Longrightarrow> rcorres V f f' (\<lambda>_ _. V)"
begin

text \<open>The rcorres method works very similarly to wpsimp in straightforward cases.\<close>
lemma "rcorres R (do rv \<leftarrow> f; g rv od) (do rv \<leftarrow> f'; g' rv od) T"
  apply rcorres
  apply simp
  done

text \<open>
  It may help to add a @{const return} on one side in order to balance the abstract and concrete
  functions, so that splitting occurs in the desired way.\<close>
lemma "rcorres R (do x \<leftarrow> f; y \<leftarrow> g x; h y od) (do x \<leftarrow> f'; g' x od) U"
  apply (rule rcorres_add_return_r)
  apply (simp only: bind_assoc) \<comment> \<open>now @{term h} will be lined up with @{const return}\<close>
  apply rcorres
  apply simp
  done

text \<open>
  Although the rule @{thm lift} is in the set rcorres_lift, in this instance, we can give the rule
  directly to the rcorres argument for it to be applied before the method attempts to split the
  functions.\<close>
lemma "rcorres V (do rv \<leftarrow> f; g rv od) (do rv \<leftarrow> f'; g' rv od) (\<lambda>_ _. V)"
  apply (rcorres rcorres: lift)
  apply simp
  done

text
  \<open>When the postcondition refers to the return value and state from only one of the monads, then
   the rules @{thm rcorres_lift_abs_only} or @{thm rcorres_lift_conc_only} will be applied.\<close>
lemma "rcorres (\<lambda>s _. P s) f f' (\<lambda>_ _ s _. P s)"
  apply rcorres
  apply simp
  done

text \<open>A typical example of the rcorres_conj_lift method.\<close>
lemma "rcorres (\<lambda>s s'. V s s' \<and> P s) f f' (\<lambda>_ _ s s'. V s s' \<and> W s s')"
  apply (rcorres_conj_lift \<open>clarsimp\<close>) \<comment> \<open>breaks off the first conjunct and solves it with @{thm lift}\<close>
  oops \<comment> \<open>leaves the goal with the same precondition, and the second conjunct as the postcondition\<close>

end

end
