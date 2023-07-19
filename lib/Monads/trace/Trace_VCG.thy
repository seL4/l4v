(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Trace_VCG
  imports
    Trace_Lemmas
    WPSimp
begin

section \<open>Hoare Logic\<close>

subsection \<open>Validity\<close>

text \<open>
  This section defines a Hoare logic for partial correctness for
  the interference trace monad as well as the exception monad.
  The logic talks only about the behaviour part of the monad and ignores
  the failure flag.

  The logic is defined semantically. Rules work directly on the
  validity predicate.

  In the interference trace monad, validity is a triple of precondition,
  monad, and postcondition. The precondition is a function from state to
  bool (a state predicate), the postcondition is a function from return value
  to state to bool. A triple is valid if for all states that satisfy the
  precondition, all result values and result states that are returned by
  the monad satisfy the postcondition. Note that if the computation returns
  the empty set, the triple is trivially valid. This means @{term "assert P"}
  does not require us to prove that @{term P} holds, but rather allows us
  to assume @{term P}! Proving non-failure is done via separate predicate and
  calculus (see below).\<close>

definition valid :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) tmonad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>") where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<equiv> \<forall>s. P s \<longrightarrow> (\<forall>(r,s') \<in> mres (f s). Q r s')"

text \<open>
  We often reason about invariant predicates. The following provides shorthand syntax
  that avoids repeating potentially long predicates.\<close>
abbreviation (input) invariant ::
  "('s,'a) tmonad \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" ("_ \<lbrace>_\<rbrace>" [59,0] 60) where
  "invariant f P \<equiv> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"

text \<open>
  Validity for the exception monad is similar and build on the standard
  validity above. Instead of one postcondition, we have two: one for
  normal and one for exceptional results.\<close>
definition validE ::
  "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'a + 'b) tmonad \<Rightarrow> ('b \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace>/ _ /(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)" ) where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<equiv> \<lbrace>P\<rbrace> f \<lbrace> \<lambda>v s. case v of Inr r \<Rightarrow> Q r s | Inl e \<Rightarrow> E e s \<rbrace>"

lemma validE_def2:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<equiv> \<forall>s. P s \<longrightarrow> (\<forall>(r,s') \<in> mres (f s). case r of Inr b \<Rightarrow> Q b s' | Inl a \<Rightarrow> E a s')"
  by (unfold valid_def validE_def)
(*
text \<open>Validity for exception monad with interferences. Not as easy to phrase
 as we need to \<close>
definition validIE :: "('s, 'a + 'b) tmonad \<Rightarrow>
             's rg_pred \<Rightarrow>
             's rg_pred \<Rightarrow> 's rg_pred \<Rightarrow>
             ('b \<Rightarrow> 's rg_pred) \<Rightarrow>
             ('a \<Rightarrow> 's rg_pred) \<Rightarrow> bool"
 ("_ //PRE _//RELY _//GUAR _//POST _//EXC _" [59,0,0,0,0,0] 60) where
  "validIE f P R G Q E \<equiv> f SAT [P,R,G,\<lambda>v. case v of Inr r \<Rightarrow> Q r | Inl e \<Rightarrow> E e]"

abbreviation (input)
  validIEsat :: "('s, 'a + 'b) tmonad \<Rightarrow>
             's rg_pred \<Rightarrow>
             's rg_pred \<Rightarrow> 's rg_pred \<Rightarrow>
             ('b \<Rightarrow> 's rg_pred) \<Rightarrow>
             ('a \<Rightarrow> 's rg_pred) \<Rightarrow> bool"
  ("_ //SAT [_, _, _, _, _]" [59,0,0,0,0,0] 60)
  where
  "validIEsat f P R G Q E \<equiv> validIE f P R G Q E"
 *)
text \<open>
  The following two instantiations are convenient to separate reasoning for exceptional and
  normal case.\<close>
(* Narrator: they are in fact not convenient, and are now considered a mistake that should have
             been an abbreviation instead. *)
definition validE_R :: (* FIXME lib: this should be an abbreviation *)
  "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'e + 'a) tmonad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>, -") where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<equiv> validE P f Q (\<lambda>x y. True)"

definition validE_E :: (* FIXME lib: this should be an abbreviation *)
  "('s \<Rightarrow> bool) \<Rightarrow>  ('s, 'e + 'a) tmonad \<Rightarrow> ('e \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" ("\<lbrace>_\<rbrace>/ _ /-, \<lbrace>_\<rbrace>") where
  "\<lbrace>P\<rbrace> f -,\<lbrace>Q\<rbrace> \<equiv> validE P f (\<lambda>x y. True) Q"


section \<open>Lemmas\<close>

lemma hoare_pre_imp:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> Q s; \<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>"
  by (fastforce simp: valid_def)

lemmas hoare_weaken_pre = hoare_pre_imp[rotated]

lemma hoare_vcg_precond_impE: (* FIXME lib: eliminate in favour of hoare_weaken_preE *)
  "\<lbrakk> \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace>; \<And>s. P s \<Longrightarrow> Q s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp add:validE_def2)

lemmas hoare_weaken_preE = hoare_vcg_precond_impE

lemma hoare_vcg_precond_impE_R: (* FIXME lib: rename to hoare_weaken_preE_R *)
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,-; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  unfolding validE_R_def
  by (rule hoare_vcg_precond_impE)

lemma hoare_weaken_preE_E:
  "\<lbrakk> \<lbrace>P'\<rbrace> f -,\<lbrace>Q\<rbrace>; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f -,\<lbrace>Q\<rbrace>"
  by (fastforce simp add: validE_E_def validE_def valid_def)

lemmas hoare_pre [wp_pre] =
  hoare_weaken_pre
  hoare_weaken_preE
  hoare_vcg_precond_impE_R
  hoare_weaken_preE_E


subsection \<open>Setting up the precondition case splitter.\<close>

lemma wpc_helper_valid:
  "\<lbrace>Q\<rbrace> g \<lbrace>S\<rbrace> \<Longrightarrow> wpc_helper (P, P', P'') (Q, Q', Q'') \<lbrace>P\<rbrace> g \<lbrace>S\<rbrace>"
  by (clarsimp simp: wpc_helper_def elim!: hoare_pre)

lemma wpc_helper_validE:
  "\<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> wpc_helper (P, P', P'') (Q, Q', Q'') \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace>"
  by (clarsimp simp: wpc_helper_def elim!: hoare_pre)

lemma wpc_helper_validE_R:
  "\<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,- \<Longrightarrow> wpc_helper (P, P', P'') (Q, Q', Q'') \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>,-"
  by (clarsimp simp: wpc_helper_def elim!: hoare_pre)

lemma wpc_helper_validR_R:
  "\<lbrace>Q\<rbrace> f -,\<lbrace>E\<rbrace> \<Longrightarrow> wpc_helper (P, P', P'') (Q, Q', Q'') \<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace>"
  by (clarsimp simp: wpc_helper_def elim!: hoare_pre)


wpc_setup "\<lambda>m. \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>" wpc_helper_valid
wpc_setup "\<lambda>m. \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>" wpc_helper_validE
wpc_setup "\<lambda>m. \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>,-" wpc_helper_validE_R
wpc_setup "\<lambda>m. \<lbrace>P\<rbrace> m -,\<lbrace>E\<rbrace>" wpc_helper_validR_R


subsection "Simplification Rules for Lifted And/Or"

lemma bipred_disj_op_eq[simp]:
  "reflp R \<Longrightarrow> ((=) or R) = R"
  apply (rule ext, rule ext)
  apply (auto simp: reflp_def)
  done

lemma bipred_le_true[simp]: "R \<le> \<top>\<top>"
  by clarsimp

subsection "Hoare Logic Rules"

lemma bind_wp[wp_split]:
  "\<lbrakk> \<And>r. \<lbrace>Q' r\<rbrace> g r \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace>f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f >>= (\<lambda>rv. g rv) \<lbrace>Q\<rbrace>"
  by (fastforce simp: valid_def bind_def2 mres_def intro: image_eqI[rotated])

lemma seq':
  "\<lbrakk> \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>; \<forall>x. P x \<longrightarrow> \<lbrace>C\<rbrace> g x \<lbrace>D\<rbrace>; \<forall>x s. B x s \<longrightarrow> P x \<and> C s \<rbrakk> \<Longrightarrow>
   \<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>D\<rbrace>"
  apply (erule bind_wp[rotated])
  apply (clarsimp simp: valid_def)
  apply (fastforce elim: rev_bexI image_eqI[rotated])
  done

lemma seq:
  assumes f_valid: "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>"
  assumes g_valid: "\<And>x. P x \<Longrightarrow> \<lbrace>C\<rbrace> g x \<lbrace>D\<rbrace>"
  assumes bind:  "\<And>x s. B x s \<Longrightarrow> P x \<and> C s"
  shows "\<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>D\<rbrace>"
  apply (insert f_valid g_valid bind)
  apply (blast intro: seq')
  done

lemma seq_ext':
  "\<lbrakk> \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>; \<forall>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>C\<rbrace>"
  by (metis bind_wp)

lemmas seq_ext = bind_wp[rotated]

lemma seqE':
  "\<lbrakk> \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>,\<lbrace>E\<rbrace>; \<forall>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>A\<rbrace> doE x \<leftarrow> f; g x odE \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  apply (simp add: bindE_def validE_def)
  apply (erule seq_ext')
  apply (auto simp: lift_def valid_def throwError_def return_def mres_def
             split: sum.splits)
  done

lemma seqE:
  assumes f_valid: "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>,\<lbrace>E\<rbrace>"
  assumes g_valid: "\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  shows "\<lbrace>A\<rbrace> doE x \<leftarrow> f; g x odE \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  apply (insert f_valid g_valid)
  apply (blast intro: seqE')
  done

lemma hoare_TrueI:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. \<top>\<rbrace>"
  by (simp add: valid_def)

lemma hoareE_TrueI:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. \<top>\<rbrace>, \<lbrace>\<lambda>r. \<top>\<rbrace>"
  by (simp add: validE_def valid_def)

lemma hoare_True_E_R[simp]:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ s. True\<rbrace>, -"
  by (auto simp: validE_R_def validE_def valid_def split: sum.splits)

lemma hoare_post_conj[intro]:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q and R\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_pre_disj[intro]:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>; \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P or Q\<rbrace> f \<lbrace>R\<rbrace>"
  by (simp add:valid_def pred_disj_def)

lemma hoare_conj:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace> f \<lbrace>Q and Q'\<rbrace>"
  unfolding valid_def by auto

lemmas hoare_post_taut = hoare_TrueI (* FIXME lib: eliminate *)

lemmas wp_post_taut = hoare_TrueI[where P=\<top>]
lemmas wp_post_tautE = hoareE_TrueI[where P=\<top>]

lemma hoare_pre_cont[simp]:
  "\<lbrace>\<bottom>\<rbrace> f \<lbrace>P\<rbrace>"
  by (simp add:valid_def)

lemma hoare_return_drop_var[iff]:
  "\<lbrace>Q\<rbrace> return x \<lbrace>\<lambda>r. Q\<rbrace>"
  by (simp add: valid_def return_def mres_def)

lemma hoare_gets[intro]:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> Q (f s) s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> gets f \<lbrace>Q\<rbrace>"
  by (simp add:valid_def gets_def get_def bind_def return_def mres_def)

lemma hoare_modifyE_var:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> Q (f s) \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> modify f \<lbrace>\<lambda>_ s. Q s\<rbrace>"
  by(simp add: valid_def modify_def put_def get_def bind_def mres_def)

lemma hoare_if:
  "\<lbrakk> P \<Longrightarrow> \<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>; \<not> P \<Longrightarrow> \<lbrace>Q\<rbrace> b \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>Q\<rbrace> if P then a else b \<lbrace>R\<rbrace>"
  by (simp add: valid_def)

lemma hoare_pre_subst:
  "\<lbrakk> A = B; \<lbrace>A\<rbrace> a \<lbrace>C\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>B\<rbrace> a \<lbrace>C\<rbrace>"
  by (erule subst)

lemma hoare_post_subst:
  "\<lbrakk> B = C; \<lbrace>A\<rbrace> a \<lbrace>B\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> a \<lbrace>C\<rbrace>"
  by (erule subst)

lemma hoare_post_imp:
  "\<lbrakk> \<And>rv s. Q rv s \<Longrightarrow> R rv s; \<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>"
  by(fastforce simp:valid_def split_def)

lemma hoare_post_impErr': (* FIXME lib: eliminate *)
  "\<lbrakk> \<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<forall>rv s. Q rv s \<longrightarrow> R rv s; \<forall>e s. E e s \<longrightarrow> F e s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>F\<rbrace>"
  unfolding validE_def valid_def
  by (fastforce split: sum.splits)

lemma hoare_post_impErr:
  "\<lbrakk> \<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<And>rv s. Q rv s \<Longrightarrow> R rv s; \<And>e s. E e s \<Longrightarrow> F e s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>F\<rbrace>"
  by (blast intro: hoare_post_impErr')

lemma hoare_validE_cases:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>\<lambda>_ _. True\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>R\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_post_imp_dc:
  "\<lbrakk>\<lbrace>P\<rbrace> a \<lbrace>\<lambda>_. Q\<rbrace>; \<And>s. Q s \<Longrightarrow> R s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>\<lambda>_. R\<rbrace>, \<lbrace>\<lambda>_. R\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_post_imp_dc2:
  "\<lbrakk>\<lbrace>P\<rbrace> a \<lbrace>\<lambda>_. Q\<rbrace>; \<And>s. Q s \<Longrightarrow> R s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>\<lambda>_. R\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_post_imp_dc2E:
  "\<lbrakk>\<lbrace>P\<rbrace> a \<lbrace>\<lambda>_. Q\<rbrace>; \<And>s. Q s \<Longrightarrow> R s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>\<lambda>_. \<top>\<rbrace>, \<lbrace>\<lambda>_. R\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_post_imp_dc2_actual:
  "\<lbrace>P\<rbrace> a \<lbrace>\<lambda>_. R\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>\<lambda>_. R\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>"
  by (rule hoare_post_imp_dc2)

lemma hoare_post_imp_dc2E_actual:
  "\<lbrace>P\<rbrace> a \<lbrace>\<lambda>_. R\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>\<lambda>_. \<top>\<rbrace>, \<lbrace>\<lambda>_. R\<rbrace>"
  by (rule hoare_post_imp_dc2E)

lemmas hoare_post_impE = hoare_post_imp (* FIXME lib: eliminate; probably should be on validE *)

lemma hoare_conjD1:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv and R rv\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv\<rbrace>"
  unfolding valid_def by auto

lemma hoare_conjD2:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv and R rv\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. R rv\<rbrace>"
  unfolding valid_def by auto

lemma hoare_post_disjI1:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv or R rv\<rbrace>"
  unfolding valid_def by auto

lemma hoare_post_disjI2:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. R rv\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv or R rv\<rbrace>"
  unfolding valid_def by auto

lemmas hoare_strengthen_post = hoare_post_imp[rotated]

lemma use_valid:
  "\<lbrakk>(r, s') \<in> mres (f s); \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; P s \<rbrakk> \<Longrightarrow> Q r s'"
  unfolding valid_def by blast

lemmas post_by_hoare = use_valid[rotated]

lemma use_validE_norm:
  "\<lbrakk> (Inr r', s') \<in> mres (B s); \<lbrace>P\<rbrace> B \<lbrace>Q\<rbrace>,\<lbrace> E \<rbrace>; P s \<rbrakk> \<Longrightarrow> Q r' s'"
  unfolding validE_def valid_def by force

lemma use_validE_except:
  "\<lbrakk> (Inl r', s') \<in> mres (B s); \<lbrace>P\<rbrace> B \<lbrace>Q\<rbrace>,\<lbrace> E \<rbrace>; P s \<rbrakk> \<Longrightarrow> E r' s'"
  unfolding validE_def valid_def by force

lemma in_inv_by_hoareD:
  "\<lbrakk> \<And>P. f \<lbrace>P\<rbrace>; (x,s') \<in> mres (f s) \<rbrakk> \<Longrightarrow> s' = s"
  by (auto simp add: valid_def) blast


subsection \<open>Misc\<close>

lemma hoare_return_simp:
  "\<lbrace>P\<rbrace> return x \<lbrace>Q\<rbrace> = (\<forall>s. P s \<longrightarrow> Q x s)"
  by (simp add: valid_def return_def mres_def)

lemma hoare_gen_asm:
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P' and K P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp add: valid_def)

lemma hoare_conjI:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> R r s\<rbrace>"
  unfolding valid_def by blast

lemma hoare_disjI1:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<or>  R rv s \<rbrace>"
  unfolding valid_def by blast

lemma hoare_disjI2:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<or>  R rv s \<rbrace>"
  unfolding valid_def by blast

lemma hoare_assume_pre:
  "(\<And>s. P s \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (auto simp: valid_def)

lemma hoare_assume_preE:
  "(\<And>s. P s \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace>"
  by (auto simp: valid_def validE_def)

lemma hoare_allI:
  "(\<And>x. \<lbrace>P\<rbrace>f\<lbrace>Q x\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace>f\<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>"
  by (simp add: valid_def) blast

lemma validE_allI:
  "(\<And>x. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q x r s\<rbrace>,\<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: valid_def validE_def split: sum.splits)

lemma hoare_exI:
  "\<lbrace>P\<rbrace> f \<lbrace>Q x\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<exists>x. Q x rv s\<rbrace>"
  by (simp add: valid_def) blast

lemma hoare_impI:
  "(R \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. R \<longrightarrow> Q rv s\<rbrace>"
  by (simp add: valid_def) blast

lemma validE_impI:
  "\<lbrakk>\<And>E. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>E\<rbrace>; (P' \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>)\<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. P' \<longrightarrow> Q rv s\<rbrace>, \<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_case_option_wp:
  "\<lbrakk> \<lbrace>P\<rbrace> f None \<lbrace>Q\<rbrace>; \<And>x.  \<lbrace>P' x\<rbrace> f (Some x) \<lbrace>Q' x\<rbrace> \<rbrakk>
  \<Longrightarrow> \<lbrace>case_option P P' v\<rbrace> f v \<lbrace>\<lambda>rv. case v of None \<Rightarrow> Q rv | Some x \<Rightarrow> Q' x rv\<rbrace>"
  by (cases v) auto

lemma hoare_vcg_prop:
  "\<lbrace>\<lambda>s. P\<rbrace> f \<lbrace>\<lambda>rv s. P\<rbrace>"
  by (simp add: valid_def)


subsection \<open>@{const valid} and @{const validE}, @{const validE_R}, @{const validE_E}\<close>

lemma valid_validE:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>, \<lbrace>\<lambda>_. Q\<rbrace>"
  by (rule hoare_post_imp_dc)

lemma valid_validE2:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q'\<rbrace>; \<And>s. Q' s \<Longrightarrow> Q s; \<And>s. Q' s \<Longrightarrow> E s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>, \<lbrace>\<lambda>_. E\<rbrace>"
  unfolding valid_def validE_def
  by (clarsimp split: sum.splits) blast

lemma validE_valid:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>, \<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>"
  unfolding validE_def valid_def
  by fastforce

lemma valid_validE_R:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>,-"
  by (simp add: validE_R_def hoare_post_impErr [OF valid_validE])

lemma valid_validE_E:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f -,\<lbrace>\<lambda>_. Q\<rbrace>"
  by (simp add: validE_E_def hoare_post_impErr [OF valid_validE])

lemma validE_validE_R:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>\<top>\<top>\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  by (simp add: validE_R_def)

lemma validE_R_validE:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
  by (simp add: validE_R_def)

lemma validE_validE_E:
  "\<lbrace>P\<rbrace> f \<lbrace>\<top>\<top>\<rbrace>, \<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f -, \<lbrace>E\<rbrace>"
  by (simp add: validE_E_def)

lemma validE_E_validE:
  "\<lbrace>P\<rbrace> f -, \<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<top>\<top>\<rbrace>, \<lbrace>E\<rbrace>"
  by (simp add: validE_E_def)


subsection \<open>@{const liftM}\<close>

lemma in_image_constant:
  "(x \<in> (\<lambda>_. v) ` S) = (x = v \<and> S \<noteq> {})"
  by (simp add: image_constant_conv)

lemma hoare_liftM_subst:
  "\<lbrace>P\<rbrace> liftM f m \<lbrace>Q\<rbrace> = \<lbrace>P\<rbrace> m \<lbrace>Q \<circ> f\<rbrace>"
  apply (simp add: liftM_def bind_def2 return_def split_def)
  apply (simp add: valid_def Ball_def mres_def image_Un)
  apply (simp add: image_image in_image_constant)
  apply force
  done

lemma hoare_liftME_subst:
  "\<lbrace>P\<rbrace> liftME f m \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace> = \<lbrace>P\<rbrace> m \<lbrace>Q \<circ> f\<rbrace>, \<lbrace>E\<rbrace>"
  unfolding validE_def liftME_liftM hoare_liftM_subst o_def
  by (fastforce intro!: arg_cong[where f="valid P m"] split: sum.splits)

lemma liftE_validE[simp]:
  "\<lbrace>P\<rbrace> liftE f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace> = \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (simp add: liftE_liftM validE_def hoare_liftM_subst o_def)


subsection \<open>Operator lifting/splitting\<close>

lemma hoare_vcg_if_split:
  "\<lbrakk> P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>S\<rbrace>; \<not>P \<Longrightarrow> \<lbrace>R\<rbrace> g \<lbrace>S\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not>P \<longrightarrow> R s)\<rbrace> if P then f else g \<lbrace>S\<rbrace>"
  by simp

lemma hoare_vcg_if_splitE:
  "\<lbrakk> P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>S\<rbrace>,\<lbrace>E\<rbrace>; \<not>P \<Longrightarrow> \<lbrace>R\<rbrace> g \<lbrace>S\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not>P \<longrightarrow> R s)\<rbrace> if P then f else g \<lbrace>S\<rbrace>,\<lbrace>E\<rbrace>"
  by simp

lemma hoare_vcg_split_case_option:
 "\<lbrakk> \<And>x. x = None \<Longrightarrow> \<lbrace>P x\<rbrace> f x \<lbrace>R x\<rbrace>; \<And>x y. x = Some y \<Longrightarrow> \<lbrace>Q x y\<rbrace> g x y \<lbrace>R x\<rbrace> \<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. (x = None \<longrightarrow> P x s) \<and> (\<forall>y. x = Some y \<longrightarrow> Q x y s)\<rbrace>
  case x of None \<Rightarrow> f x | Some y \<Rightarrow> g x y
  \<lbrace>R x\<rbrace>"
  by (cases x; simp)

lemma hoare_vcg_split_case_optionE:
  "\<lbrakk> \<And>x. x = None \<Longrightarrow> \<lbrace>P x\<rbrace> f x \<lbrace>R x\<rbrace>,\<lbrace>E x\<rbrace>; \<And>x y. x = Some y \<Longrightarrow> \<lbrace>Q x y\<rbrace> g x y \<lbrace>R x\<rbrace>,\<lbrace>E x\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. (x = None \<longrightarrow> P x s) \<and> (\<forall>y. x = Some y \<longrightarrow> Q x y s)\<rbrace>
   case x of None \<Rightarrow> f x | Some y \<Rightarrow> g x y
   \<lbrace>R x\<rbrace>, \<lbrace>E x\<rbrace>"
  by (cases x; simp)

lemma hoare_vcg_split_case_sum:
 "\<lbrakk> \<And>x a. x = Inl a \<Longrightarrow> \<lbrace>P x a\<rbrace> f x a \<lbrace>R x\<rbrace>; \<And>x b. x = Inr b \<Longrightarrow> \<lbrace>Q x b\<rbrace> g x b \<lbrace>R x\<rbrace> \<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. (\<forall>a. x = Inl a \<longrightarrow> P x a s) \<and> (\<forall>b. x = Inr b \<longrightarrow> Q x b s) \<rbrace>
  case x of Inl a \<Rightarrow> f x a | Inr b \<Rightarrow> g x b
  \<lbrace>R x\<rbrace>"
  by (cases x; simp)

lemmas hoare_vcg_precond_imp = hoare_weaken_pre (* FIXME lib: eliminate *)

lemmas hoare_seq_ext = seq_ext[rotated]
lemmas hoare_vcg_seqE = seqE[rotated]

lemma hoare_seq_ext_nobind:
  "\<lbrakk> \<lbrace>B\<rbrace> g \<lbrace>C\<rbrace>; \<lbrace>A\<rbrace> f \<lbrace>\<lambda>_. B\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> do f; g od \<lbrace>C\<rbrace>"
  by (erule seq_ext) (clarsimp simp: valid_def)

lemma hoare_seq_ext_nobindE:
  "\<lbrakk> \<lbrace>B\<rbrace> g \<lbrace>C\<rbrace>, \<lbrace>E\<rbrace>; \<lbrace>A\<rbrace> f \<lbrace>\<lambda>_. B\<rbrace>, \<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> doE f; g odE \<lbrace>C\<rbrace>, \<lbrace>E\<rbrace>"
  by (erule seqE) (clarsimp simp: validE_def)

lemmas hoare_seq_ext_skip' = hoare_seq_ext[where Q'=Q and Q=Q for Q]

lemma hoare_chain:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<And>s. R s \<Longrightarrow> P s; \<And>rv s. Q rv s \<Longrightarrow> S rv s \<rbrakk> \<Longrightarrow> \<lbrace>R\<rbrace> f \<lbrace>S\<rbrace>"
  by (wp_pre, rule hoare_post_imp)

lemma validE_weaken: (* FIXME lib: eliminate in favour of hoare_chainE *)
  "\<lbrakk> \<lbrace>P'\<rbrace> A \<lbrace>Q'\<rbrace>,\<lbrace>E'\<rbrace>; \<And>s. P s \<Longrightarrow> P' s; \<And>rv s. Q' rv s \<Longrightarrow> Q rv s; \<And>rv s. E' rv s \<Longrightarrow> E rv s \<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace> A \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by wp_pre (rule hoare_post_impErr)

lemmas hoare_chainE = validE_weaken

lemma hoare_vcg_conj_lift:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>"
  unfolding valid_def
  by fastforce

lemma hoare_vcg_conj_liftE1:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding valid_def validE_R_def validE_def
  by (fastforce simp: split_def split: sum.splits)

lemma hoare_vcg_disj_lift:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<or> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<or> Q' rv s\<rbrace>"
  unfolding valid_def
  by fastforce

lemma hoare_vcg_const_Ball_lift:
  "\<lbrakk> \<And>x. x \<in> S \<Longrightarrow> \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x\<in>S. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x\<in>S. Q x rv s\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_vcg_const_Ball_lift_R:
 "\<lbrakk> \<And>x. x \<in> S \<Longrightarrow> \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x \<in> S. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x \<in> S. Q x rv s\<rbrace>,-"
  unfolding validE_R_def validE_def
  by (rule hoare_strengthen_post)
     (fastforce intro!: hoare_vcg_const_Ball_lift split: sum.splits)+

lemma hoare_vcg_all_lift:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_vcg_all_lift_R:
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>, -) \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>, -"
  by (rule hoare_vcg_const_Ball_lift_R[where S=UNIV, simplified])

lemma hoare_vcg_const_imp_lift:
  "\<lbrakk> P \<Longrightarrow> \<lbrace>Q\<rbrace> m \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> Q s\<rbrace> m \<lbrace>\<lambda>rv s. P \<longrightarrow> R rv s\<rbrace>"
  by (cases P, simp_all add: hoare_vcg_prop)

lemma hoare_vcg_const_imp_lift_R:
  "(P \<Longrightarrow> \<lbrace>Q\<rbrace> m \<lbrace>R\<rbrace>,-) \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> Q s\<rbrace> m \<lbrace>\<lambda>rv s. P \<longrightarrow> R rv s\<rbrace>,-"
  by (fastforce simp: validE_R_def validE_def valid_def split_def split: sum.splits)

lemma hoare_weak_lift_imp:
  "\<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> P' s\<rbrace> f \<lbrace>\<lambda>rv s. P \<longrightarrow> Q rv s\<rbrace>"
  by (auto simp add: valid_def split_def)

lemma hoare_vcg_ex_lift:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<exists>x. Q x rv s\<rbrace>"
  by (clarsimp simp: valid_def, blast)

lemma hoare_vcg_ex_lift_R1:
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q\<rbrace>, -) \<Longrightarrow> \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>Q\<rbrace>, -"
  by (fastforce simp: valid_def validE_R_def validE_def split: sum.splits)

(* for instantiations *)
lemma hoare_triv:    "\<lbrace>P\<rbrace>f\<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>f\<lbrace>Q\<rbrace>" .
lemma hoare_trivE:   "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>" .
lemma hoare_trivE_R: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-" .
lemma hoare_trivR_R: "\<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace>" .

lemma hoare_vcg_E_conj:
  "\<lbrakk> \<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>Q'\<rbrace>, \<lbrace>\<lambda>rv s. E rv s \<and> E' rv s\<rbrace>"
  unfolding validE_def validE_E_def
  by (rule hoare_post_imp[OF _ hoare_vcg_conj_lift]; simp split: sum.splits)

lemma hoare_vcg_E_elim:
  "\<lbrakk> \<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (rule hoare_post_impErr[OF hoare_vcg_E_conj]) (simp add: validE_R_def)+

lemma hoare_vcg_R_conj:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>,-"
  unfolding validE_R_def validE_def
  by (rule hoare_post_imp[OF _ hoare_vcg_conj_lift]; simp split: sum.splits)

lemma hoare_post_imp_R:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,-; \<And>rv s. Q' rv s \<Longrightarrow> Q rv s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  unfolding validE_R_def
  by (erule hoare_post_impErr)

lemma hoare_post_comb_imp_conj:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>"
  by (wpsimp wp: hoare_vcg_conj_lift)


subsection \<open>Weakest Precondition Rules\<close>

lemma fail_wp:
  "\<lbrace>\<top>\<rbrace> fail \<lbrace>Q\<rbrace>"
  by (simp add: valid_def fail_def mres_def vimage_def)

lemma return_wp:
  "\<lbrace>P x\<rbrace> return x \<lbrace>P\<rbrace>"
  by(simp add: valid_def return_def mres_def)

lemma get_wp:
  "\<lbrace>\<lambda>s. Q s s\<rbrace> get \<lbrace>Q\<rbrace>"
  by (simp add: get_def valid_def mres_def)

lemma gets_wp:
  "\<lbrace>\<lambda>s. P (f s) s\<rbrace> gets f \<lbrace>P\<rbrace>"
  by(simp add: valid_def split_def gets_def return_def get_def bind_def mres_def)

lemma put_wp:
  "\<lbrace>\<lambda>_. Q () s\<rbrace> put s \<lbrace>Q\<rbrace>"
  by (simp add: put_def valid_def mres_def)

lemma modify_wp:
  "\<lbrace>\<lambda>s. Q () (f s)\<rbrace> modify f \<lbrace>Q\<rbrace>"
  unfolding modify_def
  by (wp put_wp get_wp)

lemma failE_wp:
  "\<lbrace>\<top>\<rbrace> fail \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  by (simp add: validE_def fail_wp)

lemma returnOk_wp:
  "\<lbrace>P x\<rbrace> returnOk x \<lbrace>P\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: validE_def2 returnOk_def return_def mres_def)

lemma throwError_wp:
  "\<lbrace>E e\<rbrace> throwError e \<lbrace>P\<rbrace>,\<lbrace>E\<rbrace>"
  by(simp add: validE_def2 throwError_def return_def mres_def)

lemma returnOKE_R_wp:
  "\<lbrace>P x\<rbrace> returnOk x \<lbrace>P\<rbrace>, -"
  by (simp add: validE_R_def validE_def valid_def returnOk_def return_def mres_def)

lemma liftE_wp:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> liftE f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp

lemma catch_wp:
  "\<lbrakk> \<And>x. \<lbrace>E x\<rbrace> handler x \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> catch f handler \<lbrace>Q\<rbrace>"
  apply (unfold catch_def validE_def)
  apply (erule seq_ext)
  apply (simp add: return_wp split: sum.splits)
  done

lemma handleE'_wp:
  "\<lbrakk> \<And>x. \<lbrace>F x\<rbrace> handler x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>F\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f <handle2> handler \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (unfold handleE'_def validE_def)
  apply (erule seq_ext)
  apply (clarsimp split: sum.splits)
  apply (simp add: valid_def return_def mres_def)
  done

lemma handleE_wp:
  assumes x: "\<And>x. \<lbrace>F x\<rbrace> handler x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes y: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>F\<rbrace>"
  shows      "\<lbrace>P\<rbrace> f <handle> handler \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: handleE_def handleE'_wp [OF x y])

lemma liftM_wp:
  "\<lbrace>P\<rbrace> m \<lbrace>Q \<circ> f\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> liftM f m \<lbrace>Q\<rbrace>"
  by (simp add: hoare_liftM_subst)

lemma liftME_wp:
  "\<lbrace>P\<rbrace> m \<lbrace>Q \<circ> f\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> liftME f m \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: hoare_liftME_subst)

lemma assert_wp:
  "\<lbrace>\<lambda>s. P \<longrightarrow> Q () s\<rbrace> assert P \<lbrace>Q\<rbrace>"
  unfolding assert_def
  by (wpsimp wp: return_wp fail_wp | rule conjI)+

lemma list_cases_wp:
  assumes a: "\<lbrace>P_A\<rbrace> a \<lbrace>Q\<rbrace>"
  assumes b: "\<And>x xs. ts = x#xs \<Longrightarrow> \<lbrace>P_B x xs\<rbrace> b x xs \<lbrace>Q\<rbrace>"
  shows "\<lbrace>case_list P_A P_B ts\<rbrace> case ts of [] \<Rightarrow> a | x # xs \<Rightarrow> b x xs \<lbrace>Q\<rbrace>"
  by (cases ts, auto simp: a b)

lemma hoare_vcg_handle_elseE:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<And>e. \<lbrace>E e\<rbrace> g e \<lbrace>R\<rbrace>,\<lbrace>F\<rbrace>; \<And>x. \<lbrace>Q x\<rbrace> h x \<lbrace>R\<rbrace>,\<lbrace>F\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> f <handle> g <else> h \<lbrace>R\<rbrace>,\<lbrace>F\<rbrace>"
  unfolding handle_elseE_def validE_def
  by (wpsimp wp: seq_ext | assumption | rule conjI)+

lemma alternative_wp:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> f' \<lbrace>Q\<rbrace>"
  shows      "\<lbrace>P and P'\<rbrace> f \<sqinter> f' \<lbrace>Q\<rbrace>"
  unfolding valid_def alternative_def mres_def
  using post_by_hoare[OF x _ in_mres] post_by_hoare[OF y _ in_mres]
  by fastforce

lemma alternativeE_wp:
  assumes "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes "\<lbrace>P'\<rbrace> f' \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  shows   "\<lbrace>P and P'\<rbrace> f \<sqinter> f' \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding validE_def
  by (wpsimp wp: assms alternative_wp | fold validE_def)+

lemma alternativeE_R_wp:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-; \<lbrace>P'\<rbrace> f' \<lbrace>Q\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace> f \<sqinter> f' \<lbrace>Q\<rbrace>,-"
  unfolding validE_R_def
  by (rule alternativeE_wp)

lemma alternativeE_E_wp:
  "\<lbrakk> \<lbrace>P\<rbrace> f -,\<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> g -,\<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace> f \<sqinter> g -, \<lbrace>Q\<rbrace>"
  unfolding validE_E_def
  by (rule alternativeE_wp)

lemma select_wp:
  "\<lbrace>\<lambda>s. \<forall>x \<in> S. Q x s\<rbrace> select S \<lbrace>Q\<rbrace>"
  by (simp add: select_def valid_def mres_def image_def)

lemma state_select_wp:
  "\<lbrace> \<lambda>s. \<forall>t. (s, t) \<in> f \<longrightarrow> P () t \<rbrace> state_select f \<lbrace>P\<rbrace>"
  apply (clarsimp simp: state_select_def assert_def)
  apply (rule hoare_weaken_pre)
   apply (wp put_wp select_wp hoare_vcg_if_split return_wp fail_wp get_wp)
  apply simp
  done

lemma condition_wp:
  "\<lbrakk> \<lbrace>Q\<rbrace> A \<lbrace>P\<rbrace>;  \<lbrace>R\<rbrace> B \<lbrace>P\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. if C s then Q s else R s\<rbrace> condition C A B \<lbrace>P\<rbrace>"
  by (clarsimp simp: condition_def valid_def)

lemma conditionE_wp:
  "\<lbrakk> \<lbrace>P\<rbrace> A \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace>; \<lbrace>P'\<rbrace> B \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. if C s then P s else P' s\<rbrace> condition C A B \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace>"
  by (clarsimp simp: condition_def validE_def valid_def)

lemma state_assert_wp:
  "\<lbrace>\<lambda>s. f s \<longrightarrow> P () s\<rbrace> state_assert f \<lbrace>P\<rbrace>"
  unfolding state_assert_def
  by (wp seq_ext get_wp assert_wp)

lemma when_wp[wp_split]:
  "\<lbrakk> P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>if P then Q else R ()\<rbrace> when P f \<lbrace>R\<rbrace>"
  by (clarsimp simp: when_def valid_def return_def mres_def)

lemma unless_wp[wp_split]:
  "(\<not>P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>) \<Longrightarrow> \<lbrace>if P then R () else Q\<rbrace> unless P f \<lbrace>R\<rbrace>"
  unfolding unless_def by wp auto

lemma whenE_wp:
  "(P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>if P then Q else R ()\<rbrace> whenE P f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>"
  unfolding whenE_def by clarsimp (wp returnOk_wp)

lemma hoare_K_bind[wp_split]:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> K_bind f x \<lbrace>Q\<rbrace>"
  by simp

lemma hoare_fun_app_wp:
  "\<lbrace>P\<rbrace> f' x \<lbrace>Q'\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f' $ x \<lbrace>Q'\<rbrace>"
  "\<lbrace>P\<rbrace> f x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f $ x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  "\<lbrace>P\<rbrace> f x \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f $ x \<lbrace>Q\<rbrace>,-"
  "\<lbrace>P\<rbrace> f x -,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f $ x -,\<lbrace>E\<rbrace>"
  by simp+

lemma liftE_validE_E:
  "\<lbrace>\<top>\<rbrace> liftE f -, \<lbrace>Q\<rbrace>"
  by (clarsimp simp: validE_E_def valid_def)

lemma returnOk_E:
  "\<lbrace>\<top>\<rbrace> returnOk r -, \<lbrace>Q\<rbrace>"
  by (simp add: validE_E_def) (wp returnOk_wp)

lemma case_option_wp:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> m x \<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> m' \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. (x = None \<longrightarrow> P' s) \<and> (x \<noteq> None \<longrightarrow> P (the x) s)\<rbrace> case_option m' m x \<lbrace>Q\<rbrace>"
  by (cases x; simp)

lemma case_option_wpE:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> m x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P'\<rbrace> m' \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. (x = None \<longrightarrow> P' s) \<and> (x \<noteq> None \<longrightarrow> P (the x) s)\<rbrace> case_option m' m x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (cases x; simp)

lemmas liftME_E_E_wp[wp_split] = validE_validE_E [OF liftME_wp, simplified, OF validE_E_validE]

(* FIXME: make wp *)
lemma whenE_throwError_wp:
  "\<lbrace>\<lambda>s. \<not>Q \<longrightarrow> P s\<rbrace> whenE Q (throwError e) \<lbrace>\<lambda>rv. P\<rbrace>, -"
  by (simp add: whenE_def returnOk_def throwError_def return_def validE_R_def validE_def valid_def
                mres_def)

lemma select_throwError_wp:
  "\<lbrace>\<lambda>s. \<forall>x\<in>S. Q x s\<rbrace> select S >>= throwError -, \<lbrace>Q\<rbrace>"
  by (clarsimp simp: bind_def throwError_def return_def select_def validE_E_def
                     validE_def valid_def mres_def)


subsection \<open>Setting up the @{method wp} method\<close>

lemma valid_is_triple:
  "valid P f Q = triple_judgement P f (postcondition Q (\<lambda>s f. mres (f s)))"
  by (simp add: triple_judgement_def valid_def postcondition_def)

lemma validE_is_triple:
  "validE P f Q E =
   triple_judgement P f
     (postconditions (postcondition Q (\<lambda>s f. {(rv, s'). (Inr rv, s') \<in> mres (f s)}))
                     (postcondition E (\<lambda>s f. {(rv, s'). (Inl rv, s') \<in> mres (f s)})))"
  by (fastforce simp: validE_def triple_judgement_def valid_def postcondition_def postconditions_def
                split: sum.split)

lemma validE_R_is_triple:
  "validE_R P f Q =
   triple_judgement P f (postcondition Q (\<lambda>s f. {(rv, s'). (Inr rv, s') \<in> mres (f s)}))"
  by (simp add: validE_R_def validE_is_triple postconditions_def postcondition_def)

lemma validE_E_is_triple:
  "validE_E P f E =
   triple_judgement P f (postcondition E (\<lambda>s f. {(rv, s'). (Inl rv, s') \<in> mres (f s)}))"
  by (simp add: validE_E_def validE_is_triple postconditions_def postcondition_def)

lemmas hoare_wp_combs = hoare_vcg_conj_lift

lemmas hoare_wp_combsE =
  validE_validE_R
  hoare_vcg_R_conj
  hoare_vcg_E_elim
  hoare_vcg_E_conj

lemmas hoare_wp_state_combsE =
  valid_validE_R
  hoare_vcg_R_conj[OF valid_validE_R]
  hoare_vcg_E_elim[OF valid_validE_E]
  hoare_vcg_E_conj[OF valid_validE_E]

lemmas hoare_classic_wp_combs = hoare_post_comb_imp_conj hoare_vcg_precond_imp hoare_wp_combs
lemmas hoare_classic_wp_combsE = hoare_vcg_precond_impE hoare_vcg_precond_impE_R hoare_wp_combsE

lemmas hoare_classic_wp_state_combsE =
  hoare_vcg_precond_impE[OF valid_validE]
  hoare_vcg_precond_impE_R[OF valid_validE_R]
  hoare_wp_state_combsE

lemmas all_classic_wp_combs =
  hoare_classic_wp_state_combsE
  hoare_classic_wp_combsE
  hoare_classic_wp_combs

lemmas hoare_wp_splits[wp_split] =
  hoare_seq_ext hoare_vcg_seqE handleE'_wp handleE_wp
  validE_validE_R [OF hoare_vcg_seqE [OF validE_R_validE]]
  validE_validE_R [OF handleE'_wp [OF validE_R_validE]]
  validE_validE_R [OF handleE_wp [OF validE_R_validE]]
  catch_wp hoare_vcg_if_split hoare_vcg_if_splitE
  validE_validE_R [OF hoare_vcg_if_splitE [OF validE_R_validE validE_R_validE]]
  liftM_wp liftME_wp
  validE_validE_R [OF liftME_wp [OF validE_R_validE]]
  validE_valid

lemmas [wp_comb] = hoare_wp_state_combsE hoare_wp_combsE  hoare_wp_combs

(* rules towards the bottom will be matched first *)
lemmas [wp] = hoare_vcg_prop
              wp_post_taut
              hoare_fun_app_wp
              returnOk_E
              liftE_validE_E
              put_wp
              get_wp
              gets_wp
              modify_wp
              return_wp
              returnOk_wp
              throwError_wp
              fail_wp
              failE_wp
              assert_wp
              state_assert_wp
              liftE_wp
              alternative_wp
              alternativeE_R_wp
              alternativeE_E_wp
              alternativeE_wp
              select_wp
              state_select_wp
              condition_wp
              conditionE_wp

lemmas [wp_trip] = valid_is_triple validE_is_triple validE_E_is_triple validE_R_is_triple

lemmas validE_E_combs[wp_comb] =
    hoare_vcg_E_conj[where Q'="\<top>\<top>", folded validE_E_def]
    valid_validE_E
    hoare_vcg_E_conj[where Q'="\<top>\<top>", folded validE_E_def, OF valid_validE_E]


text \<open>Simplifications on conjunction\<close>

lemma hoare_post_eq:
  "\<lbrakk> Q = Q'; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by simp

lemma hoare_post_eqE1:
  "\<lbrakk> Q = Q'; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp

lemma hoare_post_eqE2:
  "\<lbrakk> E = E'; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp

lemma hoare_post_eqE_R:
  "\<lbrakk> Q = Q'; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  by simp

lemma pred_conj_apply_elim:
  "(\<lambda>rv. Q rv and Q' rv) = (\<lambda>rv s. Q rv s \<and> Q' rv s)"
  by (simp add: pred_conj_def)

lemma pred_conj_conj_elim:
  "(\<lambda>rv s. (Q rv and Q' rv) s \<and> Q'' rv s) = (\<lambda>rv s. Q rv s \<and> Q' rv s \<and> Q'' rv s)"
  by simp

lemma conj_assoc_apply:
  "(\<lambda>rv s. (Q rv s \<and> Q' rv s) \<and> Q'' rv s) = (\<lambda>rv s. Q rv s \<and> Q' rv s \<and> Q'' rv s)"
  by simp

lemma all_elim:
  "(\<lambda>rv s. \<forall>x. P rv s) = P"
  by simp

lemma all_conj_elim:
  "(\<lambda>rv s. (\<forall>x. P rv s) \<and> Q rv s) = (\<lambda>rv s. P rv s \<and> Q rv s)"
  by simp

lemmas vcg_rhs_simps =
  pred_conj_apply_elim pred_conj_conj_elim conj_assoc_apply all_elim all_conj_elim

lemma if_apply_reduct:
  "\<lbrace>P\<rbrace> If P' (f x) (g x) \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> If P' f g x \<lbrace>Q\<rbrace>"
  by (cases P'; simp)

lemma if_apply_reductE:
  "\<lbrace>P\<rbrace> If P' (f x) (g x) \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> If P' f g x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (cases P'; simp)

lemma if_apply_reductE_R:
  "\<lbrace>P\<rbrace> If P' (f x) (g x) \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> If P' f g x \<lbrace>Q\<rbrace>,-"
  by (cases P'; simp)

lemmas hoare_wp_simps [wp_split] =
  vcg_rhs_simps [THEN hoare_post_eq] vcg_rhs_simps [THEN hoare_post_eqE1]
  vcg_rhs_simps [THEN hoare_post_eqE2] vcg_rhs_simps [THEN hoare_post_eqE_R]
  if_apply_reduct if_apply_reductE if_apply_reductE_R TrueI

schematic_goal if_apply_test:
  "\<lbrace>?Q\<rbrace> (if A then returnOk else K fail) x \<lbrace>P\<rbrace>,\<lbrace>E\<rbrace>"
  by wpsimp

lemma hoare_elim_pred_conj:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv and Q' rv\<rbrace>"
  by (unfold pred_conj_def)

lemma hoare_elim_pred_conjE1:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv and Q' rv\<rbrace>,\<lbrace>E\<rbrace>"
  by (unfold pred_conj_def)

lemma hoare_elim_pred_conjE2:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>\<lambda>rv s. E rv s \<and> E' rv s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv. E rv and E' rv\<rbrace>"
  by (unfold pred_conj_def)

lemma hoare_elim_pred_conjE_R:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv and Q' rv\<rbrace>,-"
  by (unfold pred_conj_def)

lemmas hoare_wp_pred_conj_elims =
  hoare_elim_pred_conj hoare_elim_pred_conjE1
  hoare_elim_pred_conjE2 hoare_elim_pred_conjE_R


text \<open>Miscellaneous lemmas on hoare triples\<close>

lemma hoare_vcg_mp:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<longrightarrow> Q' r s\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>"
  by (auto simp: valid_def split_def)

(* note about this precond stuff: rules get a chance to bind directly
   before any of their combined forms. As a result, these precondition
   implication rules are only used when needed. *)
lemma hoare_add_post:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>; \<And>s. P s \<Longrightarrow> P' s; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q' rv s \<longrightarrow> Q rv s\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  unfolding valid_def
  by fastforce

lemma hoare_gen_asmE:
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,-) \<Longrightarrow> \<lbrace>P' and K P\<rbrace> f \<lbrace>Q\<rbrace>, -"
  by (simp add: validE_R_def validE_def valid_def) blast

lemma hoare_list_case:
  "\<lbrakk> \<lbrace>P1\<rbrace> f f1 \<lbrace>Q\<rbrace>; \<And>y ys. xs = y#ys \<Longrightarrow> \<lbrace>P2 y ys\<rbrace> f (f2 y ys) \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>case xs of [] \<Rightarrow> P1 | y#ys \<Rightarrow> P2 y ys\<rbrace> f (case xs of [] \<Rightarrow> f1 | y#ys \<Rightarrow> f2 y ys) \<lbrace>Q\<rbrace>"
  by (cases xs; simp)

lemma hoare_use_eq:
  assumes "\<And>P. \<lbrace>\<lambda>s. P (f s)\<rbrace> m \<lbrace>\<lambda>_ s. P (f s)\<rbrace>"
  assumes "\<And>f. \<lbrace>\<lambda>s. P f s\<rbrace> m \<lbrace>\<lambda>_ s. Q f s\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (f s) s\<rbrace> m \<lbrace>\<lambda>_ s. Q (f s) s \<rbrace>"
  apply (rule hoare_post_imp[where Q="\<lambda>_ s. \<exists>y. y = f s \<and> Q y s"], simp)
  apply (wpsimp wp: hoare_vcg_ex_lift assms)
  done

lemma hoare_fail_any[simp]:
  "\<lbrace>P\<rbrace> fail \<lbrace>Q\<rbrace>"
  by wp

lemma hoare_failE[simp]:
  "\<lbrace>P\<rbrace> fail \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  by wp

lemma hoare_FalseE[simp]:
  "\<lbrace>\<bottom>\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  by (simp add: valid_def validE_def)

lemma hoare_validE_pred_conj:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q and R\<rbrace>, \<lbrace>E\<rbrace>"
  unfolding valid_def validE_def
  by (simp add: split_def split: sum.splits)

lemma hoare_validE_conj:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> R rv s\<rbrace>, \<lbrace>E\<rbrace>"
  unfolding valid_def validE_def
  by (simp add: split_def split: sum.splits)

lemmas hoare_valid_validE = valid_validE (* FIXME lib: eliminate one *)

declare validE_validE_E[wp_comb]

lemmas if_validE_E[wp_split] =
  validE_validE_E[OF hoare_vcg_if_splitE[OF validE_E_validE validE_E_validE]]

lemma hoare_drop_imp:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. R rv s \<longrightarrow> Q rv s\<rbrace>"
  by (auto simp: valid_def)

lemma hoare_drop_impE:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. Q\<rbrace>, \<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. R rv s \<longrightarrow> Q s\<rbrace>, \<lbrace>E\<rbrace>"
  by (simp add: validE_weaken)

lemma hoare_drop_impE_R:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. R rv s \<longrightarrow> Q rv s\<rbrace>, -"
  by (auto simp: validE_R_def validE_def valid_def split_def split: sum.splits)

lemma hoare_drop_impE_E:
  "\<lbrace>P\<rbrace> f -,\<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f -, \<lbrace>\<lambda>rv s. R rv s \<longrightarrow> Q rv s\<rbrace>"
  by (auto simp: validE_E_def validE_def valid_def split_def split: sum.splits)

lemmas hoare_drop_imps = hoare_drop_imp hoare_drop_impE_R hoare_drop_impE_E

lemmas bindE_E_wp[wp_split] = validE_validE_E[OF hoare_vcg_seqE [OF validE_E_validE]]

lemma True_E_E[wp]:
  "\<lbrace>\<top>\<rbrace> f -,\<lbrace>\<top>\<top>\<rbrace>"
  by (auto simp: validE_E_def validE_def valid_def split: sum.splits)


subsection \<open>Strongest postcondition rules\<close>

lemma get_sp:
  "\<lbrace>P\<rbrace> get \<lbrace>\<lambda>rv s. s = rv \<and> P s\<rbrace>"
  by(simp add:get_def valid_def mres_def)

lemma put_sp:
  "\<lbrace>\<top>\<rbrace> put a \<lbrace>\<lambda>_ s. s = a\<rbrace>"
  by(simp add:put_def valid_def mres_def)

lemma return_sp:
  "\<lbrace>P\<rbrace> return a \<lbrace>\<lambda>rv s. rv = a \<and> P s\<rbrace>"
  by(simp add:return_def valid_def mres_def)

lemma hoare_return_sp: (* FIXME lib: eliminate *)
  "\<lbrace>P\<rbrace> return x \<lbrace>\<lambda>rv. P and K (rv = x)\<rbrace>"
  by (simp add: valid_def return_def mres_def)

lemma assert_sp:
  "\<lbrace>P\<rbrace> assert Q \<lbrace>\<lambda>_ s. P s \<and> Q \<rbrace>"
  by (simp add: assert_def fail_def return_def valid_def mres_def)

lemma hoare_gets_sp:
  "\<lbrace>P\<rbrace> gets f \<lbrace>\<lambda>rv s. rv = f s \<and> P s\<rbrace>"
  by (simp add: valid_def simpler_gets_def mres_def)

lemma hoare_returnOk_sp:
  "\<lbrace>P\<rbrace> returnOk x \<lbrace>\<lambda>rv s. rv = x \<and> P s\<rbrace>, \<lbrace>Q\<rbrace>"
  by (simp add: valid_def validE_def returnOk_def return_def mres_def)




lemma trace_steps_append:
  "trace_steps (xs @ ys) s
    = trace_steps xs s \<union> trace_steps ys (last_st_tr (rev xs) s)"
  by (induct xs arbitrary: s, simp_all add: last_st_tr_def hd_append)

lemma rely_cond_append:
  "rely_cond R s (xs @ ys) = (rely_cond R s ys \<and> rely_cond R (last_st_tr ys s) xs)"
  by (simp add: rely_cond_def trace_steps_append ball_Un conj_comms)

lemma guar_cond_append:
  "guar_cond G s (xs @ ys) = (guar_cond G s ys \<and> guar_cond G (last_st_tr ys s) xs)"
  by (simp add: guar_cond_def trace_steps_append ball_Un conj_comms)

lemma prefix_closed_bind:
  "prefix_closed f \<Longrightarrow> (\<forall>x. prefix_closed (g x)) \<Longrightarrow> prefix_closed (f >>= g)"
  apply (subst prefix_closed_def, clarsimp simp: bind_def)
  apply (auto simp: Cons_eq_append_conv split: tmres.split_asm
             dest!: prefix_closedD[rotated];
    fastforce elim: rev_bexI)
  done

lemmas prefix_closed_bind[rule_format, wp_split]

lemma last_st_tr_append[simp]:
  "last_st_tr (tr @ tr') s = last_st_tr tr (last_st_tr tr' s)"
  by (simp add: last_st_tr_def hd_append)

lemma last_st_tr_Nil[simp]:
  "last_st_tr [] s = s"
  by (simp add: last_st_tr_def)

lemma last_st_tr_Cons[simp]:
  "last_st_tr (x # xs) s = snd x"
  by (simp add: last_st_tr_def)

lemma bind_twp[wp_split]:
  "\<lbrakk>  \<And>r. \<lbrace>Q' r\<rbrace>,\<lbrace>R\<rbrace> g r \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace> \<rbrakk>
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f >>= (\<lambda>r. g r) \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (subst validI_def, rule conjI)
   apply (blast intro: prefix_closed_bind validI_prefix_closed)
  apply (clarsimp simp: bind_def rely_def)
  apply (drule(2) validI_D)
   apply (clarsimp simp: rely_cond_append split: tmres.split_asm)
  apply (clarsimp split: tmres.split_asm)
  apply (drule meta_spec, frule(2) validI_D)
   apply (clarsimp simp: rely_cond_append split: if_split_asm)
  apply (clarsimp simp: guar_cond_append)
  done

lemma trace_steps_rev_drop_nth:
  "trace_steps (rev (drop n tr)) s
        = (\<lambda>i. (fst (rev tr ! i), (if i = 0 then s else snd (rev tr ! (i - 1))),
            snd (rev tr ! i))) ` {..< length tr - n}"
  apply (simp add: trace_steps_nth)
  apply (intro image_cong refl)
  apply (simp add: rev_nth)
  done

lemma prefix_closed_drop:
  "(tr, res) \<in> f s \<Longrightarrow> prefix_closed f \<Longrightarrow> \<exists>res'. (drop n tr, res') \<in> f s"
proof (induct n arbitrary: res)
  case 0 then show ?case by auto
next
  case (Suc n)
  have drop_1: "\<And>tr res. (tr, res) \<in> f s \<Longrightarrow> \<exists>res'. (drop 1 tr, res') \<in> f s"
    by (case_tac tr; fastforce dest: prefix_closedD[rotated] intro: Suc)
  show ?case
    using Suc.hyps[OF Suc.prems]
    by (metis drop_1[simplified] drop_drop add_0 add_Suc)
qed

lemma validI_GD_drop:
  "\<lbrakk> \<lbrace>P\<rbrace>, \<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>, \<lbrace>Q\<rbrace>; P s0 s; (tr, res) \<in> f s;
        rely_cond R s0 (drop n tr) \<rbrakk>
    \<Longrightarrow> guar_cond G s0 (drop n tr)"
  apply (drule prefix_closed_drop[where n=n], erule validI_prefix_closed)
  apply (auto dest: validI_GD)
  done

lemma parallel_prefix_closed[wp_split]:
  "prefix_closed f \<Longrightarrow> prefix_closed g
    \<Longrightarrow> prefix_closed (parallel f g)"
  apply (subst prefix_closed_def, clarsimp simp: parallel_def)
  apply (case_tac f_steps; clarsimp)
  apply (drule(1) prefix_closedD)+
  apply fastforce
  done

lemma rely_cond_drop:
  "rely_cond R s0 xs \<Longrightarrow> rely_cond R s0 (drop n xs)"
  using rely_cond_append[where xs="take n xs" and ys="drop n xs"]
  by simp

lemma rely_cond_is_drop:
  "rely_cond R s0 xs
    \<Longrightarrow> (ys = drop (length xs - length ys) xs)
    \<Longrightarrow> rely_cond R s0 ys"
  by (metis rely_cond_drop)

lemma bounded_rev_nat_induct:
  "(\<And>n. N \<le> n \<Longrightarrow> P n) \<Longrightarrow> (\<And>n. n < N \<Longrightarrow> P (Suc n) \<Longrightarrow> P n)
    \<Longrightarrow> P n"
  by (induct diff\<equiv>"N - n" arbitrary: n; simp)

lemma drop_n_induct:
  "P [] \<Longrightarrow> (\<And>n. n < length xs \<Longrightarrow> P (drop (Suc n) xs) \<Longrightarrow> P (drop n xs))
    \<Longrightarrow> P (drop n xs)"
  by (induct len\<equiv>"length (drop n xs)" arbitrary: n xs; simp)

lemma guar_cond_Cons_eq:
  "guar_cond R s0 (x # xs)
        = (guar_cond R s0 xs \<and> (fst x \<noteq> Env \<longrightarrow> R (last_st_tr xs s0) (snd x)))"
  by (cases "fst x"; simp add: guar_cond_def trace_steps_append conj_comms)

lemma guar_cond_Cons:
  "guar_cond R s0 xs
    \<Longrightarrow> fst x \<noteq> Env \<longrightarrow> R (last_st_tr xs s0) (snd x)
    \<Longrightarrow> guar_cond R s0 (x # xs)"
  by (simp add: guar_cond_Cons_eq)

lemma guar_cond_drop_Suc_eq:
  "n < length xs
    \<Longrightarrow> guar_cond R s0 (drop n xs) = (guar_cond R s0 (drop (Suc n) xs)
        \<and> (fst (xs ! n) \<noteq> Env \<longrightarrow> R (last_st_tr (drop (Suc n) xs) s0) (snd (xs ! n))))"
  apply (rule trans[OF _ guar_cond_Cons_eq])
  apply (simp add: Cons_nth_drop_Suc)
  done

lemma guar_cond_drop_Suc:
  "guar_cond R s0 (drop (Suc n) xs)
    \<Longrightarrow> fst (xs ! n) \<noteq> Env \<longrightarrow> R (last_st_tr (drop (Suc n) xs) s0) (snd (xs ! n))
    \<Longrightarrow> guar_cond R s0 (drop n xs)"
  by (case_tac "n < length xs"; simp add: guar_cond_drop_Suc_eq)

lemma rely_cond_Cons_eq:
  "rely_cond R s0 (x # xs)
        = (rely_cond R s0 xs \<and> (fst x = Env \<longrightarrow> R (last_st_tr xs s0) (snd x)))"
  by (simp add: rely_cond_def trace_steps_append conj_comms)

lemma rely_cond_Cons:
  "rely_cond R s0 xs
    \<Longrightarrow> fst x = Env \<longrightarrow> R (last_st_tr xs s0) (snd x)
    \<Longrightarrow> rely_cond R s0 (x # xs)"
  by (simp add: rely_cond_Cons_eq)

lemma rely_cond_drop_Suc_eq:
  "n < length xs
    \<Longrightarrow> rely_cond R s0 (drop n xs) = (rely_cond R s0 (drop (Suc n) xs)
        \<and> (fst (xs ! n) = Env \<longrightarrow> R (last_st_tr (drop (Suc n) xs) s0) (snd (xs ! n))))"
  apply (rule trans[OF _ rely_cond_Cons_eq])
  apply (simp add: Cons_nth_drop_Suc)
  done

lemma rely_cond_drop_Suc:
  "rely_cond R s0 (drop (Suc n) xs)
    \<Longrightarrow> fst (xs ! n) = Env \<longrightarrow> R (last_st_tr (drop (Suc n) xs) s0) (snd (xs ! n))
    \<Longrightarrow> rely_cond R s0 (drop n xs)"
  by (cases "n < length xs"; simp add: rely_cond_drop_Suc_eq)

lemma last_st_tr_map_zip_hd:
  "length flags = length tr
    \<Longrightarrow> tr \<noteq> [] \<longrightarrow> snd (f (hd flags, hd tr)) = snd (hd tr)
    \<Longrightarrow> last_st_tr (map f (zip flags tr)) = last_st_tr tr"
  apply (cases tr; simp)
  apply (cases flags; simp)
  apply (simp add: fun_eq_iff)
  done

lemma last_st_tr_drop_map_zip_hd:
  "length flags = length tr
    \<Longrightarrow> n < length tr \<longrightarrow> snd (f (flags ! n, tr ! n)) = snd (tr ! n)
    \<Longrightarrow> last_st_tr (drop n (map f (zip flags tr))) = last_st_tr (drop n tr)"
  apply (simp add: drop_map drop_zip)
  apply (rule last_st_tr_map_zip_hd; clarsimp)
  apply (simp add: hd_drop_conv_nth)
  done

lemma last_st_tr_map_zip:
  "length flags = length tr
    \<Longrightarrow> \<forall>fl tmid s. snd (f (fl, (tmid, s))) = s
    \<Longrightarrow> last_st_tr (map f (zip flags tr)) = last_st_tr tr"
  apply (erule last_st_tr_map_zip_hd)
  apply (clarsimp simp: neq_Nil_conv)
  done

lemma parallel_rely_induct:
  assumes preds: "(tr, v) \<in> parallel f g s" "Pf s0 s" "Pg s0 s"
  assumes validI: "\<lbrace>Pf\<rbrace>,\<lbrace>Rf\<rbrace> f' \<lbrace>Gf\<rbrace>,\<lbrace>Qf\<rbrace>"
     "\<lbrace>Pg\<rbrace>,\<lbrace>Rg\<rbrace> g' \<lbrace>Gg\<rbrace>,\<lbrace>Qg\<rbrace>"
     "f s \<subseteq> f' s" "g s \<subseteq> g' s"
  and compat: "R \<le> Rf" "R \<le> Rg" "Gf \<le> G" "Gg \<le> G"
     "Gf \<le> Rg" "Gg \<le> Rf"
  and rely: "rely_cond R s0 (drop n tr)"
  shows "\<exists>tr_f tr_g. (tr_f, v) \<in> f s \<and> (tr_g, v) \<in> g s
      \<and> rely_cond Rf s0 (drop n tr_f) \<and> rely_cond Rg s0 (drop n tr_g)
      \<and> map snd tr_f = map snd tr \<and> map snd tr_g = map snd tr
      \<and> (\<forall>i \<le> length tr. last_st_tr (drop i tr_g) s0 = last_st_tr (drop i tr_f) s0)
      \<and> guar_cond G s0 (drop n tr)"
  (is "\<exists>ys zs. _ \<and> _ \<and> ?concl ys zs")
proof -
  obtain ys zs where tr: "tr = map parallel_mrg (zip ys zs)"
      and all2: "list_all2 (\<lambda>y z. (fst y = Env \<or> fst z = Env) \<and> snd y = snd z) ys zs"
      and ys: "(ys, v) \<in> f s" and zs: "(zs, v) \<in> g s"
    using preds
    by (clarsimp simp: parallel_def2)
  note len[simp] = list_all2_lengthD[OF all2]

  have ys': "(ys, v) \<in> f' s" and zs': "(zs, v) \<in> g' s"
    using ys zs validI by auto

  note rely_f_step = validI_GD_drop[OF validI(1) preds(2) ys' rely_cond_drop_Suc]
  note rely_g_step = validI_GD_drop[OF validI(2) preds(3) zs' rely_cond_drop_Suc]

  note snd[simp] = list_all2_nthD[OF all2, THEN conjunct2]

  have "?concl ys zs"
    using rely tr all2 rely_f_step rely_g_step
    apply (induct n rule: bounded_rev_nat_induct)
     apply (subst drop_all, assumption)
     apply clarsimp
     apply (simp add: list_all2_conv_all_nth last_st_tr_def drop_map[symmetric]
                      hd_drop_conv_nth hd_append)
     apply (fastforce simp: split_def intro!: nth_equalityI)
     apply clarsimp
    apply (erule_tac x=n in meta_allE)+
    apply (drule meta_mp, erule rely_cond_is_drop, simp)
    apply (subst(asm) rely_cond_drop_Suc_eq[where xs="map f xs" for f xs], simp)
    apply (clarsimp simp: last_st_tr_drop_map_zip_hd if_split[where P="\<lambda>x. x = Env"]
                          split_def)
    apply (intro conjI; (rule guar_cond_drop_Suc rely_cond_drop_Suc, assumption))
      apply (auto simp: guar_cond_drop_Suc_eq last_st_tr_drop_map_zip_hd
                 intro: compat[THEN predicate2D])
    done

  thus ?thesis
    using ys zs
    by auto
qed

lemmas parallel_rely_induct0 = parallel_rely_induct[where n=0, simplified]

lemma rg_validI:
  assumes validI: "\<lbrace>Pf\<rbrace>,\<lbrace>Rf\<rbrace> f \<lbrace>Gf\<rbrace>,\<lbrace>Qf\<rbrace>"
     "\<lbrace>Pg\<rbrace>,\<lbrace>Rg\<rbrace> g \<lbrace>Gg\<rbrace>,\<lbrace>Qg\<rbrace>"
  and compat: "R \<le> Rf" "R \<le> Rg" "Gf \<le> G" "Gg \<le> G"
     "Gf \<le> Rg" "Gg \<le> Rf"
  shows "\<lbrace>Pf and Pg\<rbrace>,\<lbrace>R\<rbrace> parallel f g \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. Qf rv and Qg rv\<rbrace>"
  apply (clarsimp simp: validI_def rely_def pred_conj_def
                        parallel_prefix_closed validI[THEN validI_prefix_closed])
  apply (drule(3) parallel_rely_induct0[OF _ _ _ validI order_refl order_refl compat])
  apply clarsimp
  apply (drule(2) validI[THEN validI_rvD])+
  apply (simp add: last_st_tr_def)
  done

lemma validI_weaken_pre[wp_pre]:
  "\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>
    \<Longrightarrow> (\<And>s0 s. P s0 s \<Longrightarrow> P' s0 s)
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (simp add: validI_def, blast)

lemma rely_weaken:
  "(\<forall>s0 s. R s0 s \<longrightarrow> R' s0 s)
    \<Longrightarrow> (tr, res) \<in> rely f R s s0 \<Longrightarrow> (tr, res) \<in> rely f R' s s0"
  by (simp add: rely_def rely_cond_def, blast)

lemma validI_weaken_rely[wp_pre]:
  "\<lbrace>P\<rbrace>,\<lbrace>R'\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>
    \<Longrightarrow> (\<forall>s0 s. R s0 s \<longrightarrow> R' s0 s)
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (simp add: validI_def)
  by (metis rely_weaken)

lemma validI_strengthen_post:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>
    \<Longrightarrow> (\<forall>v s0 s. Q' v s0 s \<longrightarrow> Q v s0 s)
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (simp add: validI_def)

lemma validI_strengthen_guar:
  "\<lbrace>P\<rbrace>, \<lbrace>R\<rbrace> f \<lbrace>G'\<rbrace>, \<lbrace>Q\<rbrace>
    \<Longrightarrow> (\<forall>s0 s. G' s0 s \<longrightarrow> G s0 s)
    \<Longrightarrow> \<lbrace>P\<rbrace>, \<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>, \<lbrace>Q\<rbrace>"
  by (force simp: validI_def guar_cond_def)

lemma rely_prim[simp]:
  "rely (\<lambda>s. insert (v s) (f s)) R s0 = (\<lambda>s. {x. x = v s \<and> rely_cond R s0 (fst x)} \<union> (rely f R s0 s))"
  "rely (\<lambda>s. {}) R s0 = (\<lambda>_. {})"
  by (auto simp: rely_def prod_eq_iff)

lemma prefix_closed_put_trace_elem[iff]:
  "prefix_closed (put_trace_elem x)"
  by (clarsimp simp: prefix_closed_def put_trace_elem_def)

lemma prefix_closed_return[iff]:
  "prefix_closed (return x)"
  by (simp add: prefix_closed_def return_def)

lemma prefix_closed_put_trace[iff]:
  "prefix_closed (put_trace tr)"
  by (induct tr; clarsimp simp: prefix_closed_bind)

lemma put_trace_eq_drop:
  "put_trace xs s
    = ((\<lambda>n. (drop n xs, if n = 0 then Result ((), s) else Incomplete)) ` {.. length xs})"
  apply (induct xs)
   apply (clarsimp simp: return_def)
  apply (clarsimp simp: put_trace_elem_def bind_def)
  apply (simp add: atMost_Suc_eq_insert_0 image_image)
  apply (rule equalityI; clarsimp)
   apply (split if_split_asm; clarsimp)
   apply (auto intro: image_eqI[where x=0])[1]
  apply (rule rev_bexI, simp)
  apply clarsimp
  done

lemma put_trace_res:
  "(tr, res) \<in> put_trace xs s
    \<Longrightarrow> \<exists>n. tr = drop n xs \<and> n \<le> length xs
        \<and> res = (case n of 0 \<Rightarrow> Result ((), s) | _ \<Rightarrow> Incomplete)"
  apply (clarsimp simp: put_trace_eq_drop)
  apply (case_tac n; auto intro: exI[where x=0])
  done

lemma put_trace_twp[wp]:
  "\<lbrace>\<lambda>s0 s. (\<forall>n. rely_cond R s0 (drop n xs) \<longrightarrow> guar_cond G s0 (drop n xs))
    \<and> (rely_cond R s0 xs \<longrightarrow> Q () (last_st_tr xs s0) s)\<rbrace>,\<lbrace>R\<rbrace> put_trace xs \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (clarsimp simp: validI_def rely_def)
  apply (drule put_trace_res)
  apply (clarsimp; clarsimp split: nat.split_asm)
  done

lemmas put_trace_elem_twp = put_trace_twp[where xs="[x]" for x, simplified]

lemma prefix_closed_select[iff]:
  "prefix_closed (select S)"
  by (simp add: prefix_closed_def select_def image_def)

lemma rely_cond_rtranclp:
  "rely_cond R s (map (Pair Env) xs) \<Longrightarrow> rtranclp R s (last_st_tr (map (Pair Env) xs) s)"
  apply (induct xs arbitrary: s rule: rev_induct)
   apply simp
  apply (clarsimp simp add: rely_cond_def)
  apply (erule converse_rtranclp_into_rtranclp)
  apply simp
  done

definition
  no_trace :: "('s,'a) tmonad  \<Rightarrow> bool"
where
  "no_trace f = (\<forall>tr res s. (tr, res) \<in> f s \<longrightarrow> tr = [] \<and> res \<noteq> Incomplete)"

lemmas no_traceD = no_trace_def[THEN iffD1, rule_format]

lemma no_trace_emp:
  "no_trace f \<Longrightarrow> (tr, r) \<in> f s \<Longrightarrow> tr = []"
  by (simp add: no_traceD)

lemma no_trace_Incomplete_mem:
  "no_trace f \<Longrightarrow> (tr, Incomplete) \<notin> f s"
  by (auto dest: no_traceD)

lemma no_trace_Incomplete_eq:
  "no_trace f \<Longrightarrow> (tr, res) \<in> f s \<Longrightarrow> res \<noteq> Incomplete"
  by (auto dest: no_traceD)

lemma no_trace_prefix_closed:
  "no_trace f \<Longrightarrow> prefix_closed f"
  by (auto simp add: prefix_closed_def dest: no_trace_emp)

(* Attempt to define triple_judgement to use valid_validI_wp as wp_comb rule.
   It doesn't work. It seems that wp_comb rules cannot take more than 1 assumption *)
lemma validI_is_triple:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> =
     triple_judgement (\<lambda>(s0, s). prefix_closed f \<longrightarrow> P s0 s) f
                      (\<lambda>(s0,s) f. prefix_closed f \<and> (\<forall>tr res. (tr, res) \<in> rely f R s0 s
                          \<longrightarrow> guar_cond G s0 tr
                              \<and> (\<forall>rv s'. res = Result (rv, s') \<longrightarrow> Q rv (last_st_tr tr s0) s')))"
  apply (simp add: triple_judgement_def validI_def )
  apply (cases "prefix_closed f"; simp)
  done

lemma no_trace_is_triple:
  "no_trace f = triple_judgement \<top> f (\<lambda>() f. id no_trace f)"
  by (simp add: triple_judgement_def split: unit.split)

lemmas [wp_trip] = validI_is_triple no_trace_is_triple

lemma valid_validI_wp[wp_comb]:
  "no_trace f \<Longrightarrow> (\<And>s0. \<lbrace>P s0\<rbrace> f \<lbrace>\<lambda>v. Q v s0 \<rbrace>)
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (fastforce simp: rely_def validI_def valid_def mres_def no_trace_prefix_closed dest: no_trace_emp
    elim: image_eqI[rotated])

(* Since valid_validI_wp in wp_comb doesn't work, we add the rules directly in the wp set *)
lemma no_trace_prim:
  "no_trace get"
  "no_trace (put s)"
  "no_trace (modify f)"
  "no_trace (return v)"
  "no_trace fail"
  by (simp_all add: no_trace_def get_def put_def modify_def bind_def
                    return_def select_def fail_def)

lemma no_trace_select:
  "no_trace (select S)"
  by (clarsimp simp add: no_trace_def select_def)

lemma no_trace_bind:
  "no_trace f \<Longrightarrow> \<forall>rv. no_trace (g rv)
    \<Longrightarrow> no_trace (do rv \<leftarrow> f; g rv od)"
  apply (subst no_trace_def)
  apply (clarsimp simp add: bind_def split: tmres.split_asm;
    auto dest: no_traceD[rotated])
  done

lemma no_trace_extra:
  "no_trace (gets f)"
  "no_trace (assert P)"
  "no_trace (assert_opt Q)"
  by (simp_all add: gets_def assert_def assert_opt_def no_trace_bind no_trace_prim
             split: option.split)

lemmas no_trace_all[wp, iff] = no_trace_prim no_trace_select no_trace_extra

lemma env_steps_twp[wp]:
  "\<lbrace>\<lambda>s0 s. (\<forall>s'. R\<^sup>*\<^sup>* s0 s' \<longrightarrow> Q () s' s') \<and> Q () s0 s\<rbrace>,\<lbrace>R\<rbrace> env_steps \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (simp add: interference_def env_steps_def)
  apply wp
  apply (clarsimp simp: guar_cond_def trace_steps_rev_drop_nth rev_nth)
  apply (drule rely_cond_rtranclp)
  apply (clarsimp simp add: last_st_tr_def hd_append)
  done

lemma interference_twp[wp]:
  "\<lbrace>\<lambda>s0 s. (\<forall>s'. R\<^sup>*\<^sup>* s s' \<longrightarrow> Q () s' s') \<and> G s0 s\<rbrace>,\<lbrace>R\<rbrace>  interference \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (simp add: interference_def commit_step_def del: put_trace.simps)
  apply wp
  apply clarsimp
  apply (simp add: drop_Cons nat.split rely_cond_def guar_cond_def)
  done

(* what Await does if we haven't committed our step is a little
   strange. this assumes we have, which means s0 = s. we should
   revisit this if we find a use for Await when this isn't the
   case *)
lemma Await_sync_twp:
  "\<lbrace>\<lambda>s0 s. s = s0 \<and> (\<forall>x. R\<^sup>*\<^sup>* s0 x \<and> c x \<longrightarrow> Q () x x)\<rbrace>,\<lbrace>R\<rbrace> Await c \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (simp add: Await_def split_def)
  apply wp
  apply clarsimp
  apply (clarsimp simp: guar_cond_def trace_steps_rev_drop_nth rev_nth)
  apply (drule rely_cond_rtranclp)
  apply (simp add: o_def)
  done

(* FIXME: this needs adjustment, case_prod Q is unlikely to unify *)
lemma wpc_helper_validI:
  "(\<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>) \<Longrightarrow> wpc_helper (P, P', P'') (case_prod Q, Q', Q'') (\<lbrace>curry P\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>)"
  by (clarsimp simp: wpc_helper_def elim!: validI_weaken_pre)

wpc_setup "\<lambda>m. \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>" wpc_helper_validI

lemma mres_union:
 "mres (a \<union> b) = mres a \<union> mres b"
  by (simp add: mres_def image_Un)

lemma mres_Failed_empty:
  "mres ((\<lambda>xs. (xs, Failed)) ` X ) = {}"
  "mres ((\<lambda>xs. (xs, Incomplete)) ` X ) = {}"
  by (auto simp add: mres_def image_def)

lemma det_set_option_eq:
  "(\<Union>a\<in>m. set_option (snd a)) = {(r, s')} \<Longrightarrow>
       (ts, Some (rr, ss)) \<in> m \<Longrightarrow> rr = r \<and> ss = s'"
  by (metis UN_I option.set_intros prod.inject singleton_iff snd_conv)

lemma det_set_option_eq':
  "(\<Union>a\<in>m. set_option (snd a)) = {(r, s')} \<Longrightarrow>
       Some (r, s') \<in> snd ` m"
  using image_iff by fastforce

lemma validI_name_pre:
  "prefix_closed f \<Longrightarrow>
  (\<And>s0 s. P s0 s \<Longrightarrow> \<lbrace>\<lambda>s0' s'. s0' = s0 \<and> s' = s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>)
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  unfolding validI_def
  by metis

lemma validI_well_behaved':
  "prefix_closed f
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R'\<rbrace> f \<lbrace>G'\<rbrace>,\<lbrace>Q\<rbrace>
    \<Longrightarrow> R \<le> R'
    \<Longrightarrow> G' \<le> G
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (subst validI_def, clarsimp)
  apply (clarsimp simp add: rely_def)
  apply (drule (2)  validI_D)
  apply (fastforce simp: rely_cond_def guar_cond_def)+
  done

lemmas validI_well_behaved = validI_well_behaved'[unfolded le_fun_def, simplified]

end
