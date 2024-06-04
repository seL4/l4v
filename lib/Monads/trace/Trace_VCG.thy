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
  failures and the trace.

  The logic is defined semantically. Rules work directly on the
  validity predicate.

  In the interference trace monad, validity is a triple of precondition,
  monad, and postcondition. The precondition is a function from state to
  bool (a state predicate), the postcondition is a function from return value
  to state to bool. A triple is valid if for all states that satisfy the
  precondition, all result values and result states that are returned by
  the monad satisfy the postcondition. Note that if the result of the
  computation is the empty set then the triple is trivially valid. This means
  @{term "assert P"} does not require us to prove that @{term P} holds, but
  rather allows us to assume @{term P}! Proving non-failure is done via a
  separate predicate and calculus (see @{text Trace_No_Fail}).\<close>
definition valid ::
  "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) tmonad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>") where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<equiv> \<forall>s. P s \<longrightarrow> (\<forall>(r,s') \<in> mres (f s). Q r s')"

text \<open>
  We often reason about invariant predicates. The following provides shorthand syntax
  that avoids repeating potentially long predicates.\<close>
abbreviation (input) invariant :: "('s,'a) tmonad \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" ("_ \<lbrace>_\<rbrace>" [59,0] 60) where
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

(* These lemmas are useful to apply to rules to convert valid rules into a format suitable for wp. *)
lemma valid_make_schematic_post:
  "(\<forall>s0. \<lbrace> \<lambda>s. P s0 s \<rbrace> f \<lbrace> \<lambda>rv s. Q s0 rv s \<rbrace>) \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>s0. P s0 s \<and> (\<forall>rv s'. Q s0 rv s' \<longrightarrow> Q' rv s') \<rbrace> f \<lbrace> Q' \<rbrace>"
  by (auto simp add: valid_def split: prod.splits)

lemma validE_make_schematic_post:
  "(\<forall>s0. \<lbrace> \<lambda>s. P s0 s \<rbrace> f \<lbrace> \<lambda>rv s. Q s0 rv s \<rbrace>, \<lbrace> \<lambda>rv s. E s0 rv s \<rbrace>) \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>s0. P s0 s \<and> (\<forall>rv s'. Q s0 rv s' \<longrightarrow> Q' rv s')
        \<and> (\<forall>rv s'. E s0 rv s' \<longrightarrow> E' rv s') \<rbrace> f \<lbrace> Q' \<rbrace>, \<lbrace> E' \<rbrace>"
  by (auto simp add: validE_def valid_def split: prod.splits sum.splits)


section \<open>Pre Lemmas\<close>

lemma hoare_pre_imp:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> P' s; \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp: valid_def)

lemmas hoare_weaken_pre = hoare_pre_imp[rotated]

lemma hoare_weaken_preE:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def2)

lemma hoare_weaken_preE_R:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,-; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  unfolding validE_R_def
  by (rule hoare_weaken_preE)

lemma hoare_weaken_preE_E:
  "\<lbrakk> \<lbrace>P'\<rbrace> f -,\<lbrace>Q\<rbrace>; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f -,\<lbrace>Q\<rbrace>"
  by (fastforce simp: validE_E_def validE_def valid_def)

lemmas hoare_pre [wp_pre] =
  hoare_weaken_pre
  hoare_weaken_preE
  hoare_weaken_preE_R
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


subsection "Hoare Logic Rules"

lemma bind_wp[wp_split]:
  "\<lbrakk>\<And>rv. \<lbrace>Q' rv\<rbrace> g rv \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f >>= (\<lambda>rv. g rv) \<lbrace>Q\<rbrace>"
  by (fastforce simp: valid_def bind_def' mres_def intro: image_eqI[rotated])

lemma bindE_wp[wp_split]:
  "\<lbrakk>\<And>rv. \<lbrace>Q' rv\<rbrace> g rv \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f >>=E (\<lambda>rv. g rv) \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def2 bindE_def bind_def throwError_def return_def lift_def mres_def image_def
               split: sum.splits tmres.splits)

lemma bindE_R_wp:
  "\<lbrakk>\<And>rv. \<lbrace>Q' rv\<rbrace> g rv \<lbrace>Q\<rbrace>,-; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,-\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f >>=E (\<lambda>rv. g rv) \<lbrace>Q\<rbrace>,-"
  apply (clarsimp simp: validE_R_def)
  by (wp | assumption)+

lemma bindE_E_wp:
  "\<lbrakk>\<And>rv. \<lbrace>Q' rv\<rbrace> g rv -,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f >>=E (\<lambda>rv. g rv) -,\<lbrace>E\<rbrace>"
  apply (clarsimp simp: validE_E_def)
  by (wp | assumption)+

lemmas bind_wp_fwd = bind_wp[rotated]
lemmas bindE_wp_fwd = bindE_wp[rotated]

lemma bind_wpE_R:
  "\<lbrakk>\<And>rv. \<lbrace>Q' rv\<rbrace> g rv \<lbrace>Q\<rbrace>,-; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f >>= (\<lambda>rv. g rv) \<lbrace>Q\<rbrace>,-"
  apply (clarsimp simp: validE_R_def validE_def)
  by (wp | assumption)+

lemma bind_wpE_E:
  "\<lbrakk>\<And>rv. \<lbrace>Q' rv\<rbrace> g rv -,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f >>= (\<lambda>rv. g rv) -,\<lbrace>E\<rbrace>"
  apply (clarsimp simp: validE_E_def validE_def)
  by (wp | assumption)+

lemma bind_wpE:
  "\<lbrakk>\<And>rv. \<lbrace>Q' rv\<rbrace> g rv \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f >>= (\<lambda>rv. g rv) \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (clarsimp simp: validE_def)
  by (wp | assumption)+

lemma hoare_TrueI:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. \<top>\<rbrace>"
  by (simp add: valid_def)

lemma hoareE_TrueI:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. \<top>\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>"
  by (simp add: validE_def valid_def)

lemma hoareE_R_TrueI:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. \<top>\<rbrace>, -"
  by (auto simp: validE_R_def validE_def valid_def split: sum.splits)

lemma hoareE_E_TrueI:
  "\<lbrace>P\<rbrace> f -,\<lbrace>\<lambda>_. \<top>\<rbrace>"
  by (auto simp: validE_E_def validE_def valid_def split: sum.splits)

lemmas wp_post_taut = hoare_TrueI[where P=\<top>]
lemmas wp_post_tautE = hoareE_TrueI[where P=\<top>]
lemmas wp_post_tautE_R = hoareE_R_TrueI[where P=\<top>]
lemmas wp_post_tautE_E = hoareE_E_TrueI[where P=\<top>]
lemmas wp_post_tauts[intro] = wp_post_taut wp_post_tautE wp_post_tautE_R wp_post_tautE_E

lemma hoare_post_conj[intro]:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q and Q'\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_pre_disj[intro]:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P or P'\<rbrace> f \<lbrace>Q\<rbrace>"
  by (simp add:valid_def pred_disj_def)

lemma hoare_conj:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace> f \<lbrace>Q and Q'\<rbrace>"
  unfolding valid_def by auto

lemma hoare_pre_cont[simp]:
  "\<lbrace>\<bottom>\<rbrace> f \<lbrace>P\<rbrace>"
  by (simp add:valid_def)

lemma hoare_FalseE[simp]:
  "\<lbrace>\<bottom>\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: valid_def validE_def)

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
  "\<lbrakk> P' \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<not> P' \<Longrightarrow> \<lbrace>P\<rbrace> g \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> if P' then f else g \<lbrace>Q\<rbrace>"
  by (simp add: valid_def)

lemma hoare_pre_subst:
  "\<lbrakk> P = P'; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>"
  by (erule subst)

lemma hoare_post_subst:
  "\<lbrakk> Q = Q'; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>"
  by (erule subst)

lemma hoare_post_imp:
  "\<lbrakk> \<And>rv s. Q' rv s \<Longrightarrow> Q rv s; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by(fastforce simp:valid_def split_def)

lemma hoare_post_impE:
  "\<lbrakk> \<And>rv s. Q' rv s \<Longrightarrow> Q rv s; \<And>e s. E' e s \<Longrightarrow> E e s; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by(fastforce simp: validE_def2 split: sum.splits)

lemmas hoare_strengthen_post = hoare_post_imp[rotated]
lemmas hoare_strengthen_postE = hoare_post_impE[rotated 2]

lemma hoare_strengthen_postE_R:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,-; \<And>rv s. Q' rv s \<Longrightarrow> Q rv s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  unfolding validE_R_def
  by (erule hoare_post_impE)

lemma hoare_strengthen_postE_E:
  "\<lbrakk> \<lbrace>P\<rbrace> f -,\<lbrace>E'\<rbrace>; \<And>rv s. E' rv s \<Longrightarrow> E rv s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace>"
  unfolding validE_E_def
  by (rule hoare_post_impE)

lemma hoare_validE_cases:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>_ _. True\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_post_impE_dc:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q'\<rbrace>; \<And>s. Q' s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>, \<lbrace>\<lambda>_. Q\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_post_impE_R_dc:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q'\<rbrace>; \<And>s. Q' s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_post_impE_E_dc:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q'\<rbrace>; \<And>s. Q' s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. \<top>\<rbrace>, \<lbrace>\<lambda>_. Q\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_post_impE_R_dc_actual:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>"
  by (rule hoare_post_impE_R_dc)

lemma hoare_post_impE_E_dc_actual:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. \<top>\<rbrace>, \<lbrace>\<lambda>_. Q\<rbrace>"
  by (rule hoare_post_impE_E_dc)

lemma hoare_conjD1:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv and Q' rv\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv\<rbrace>"
  unfolding valid_def by auto

lemma hoare_conjD2:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv and Q' rv\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q' rv\<rbrace>"
  unfolding valid_def by auto

lemma hoare_post_disjI1:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv or Q' rv\<rbrace>"
  unfolding valid_def by auto

lemma hoare_post_disjI2:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q' rv\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv or Q' rv\<rbrace>"
  unfolding valid_def by auto

lemma use_valid:
  "\<lbrakk>(r, s') \<in> mres (f s); \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; P s \<rbrakk> \<Longrightarrow> Q r s'"
  unfolding valid_def by blast

lemmas post_by_hoare = use_valid[rotated]

lemma use_valid_inv:
  assumes step: "(r, s') \<in> mres (f s)"
  assumes pres: "\<And>N. \<lbrace>\<lambda>s. N (P s) \<and> E s\<rbrace> f \<lbrace>\<lambda>rv s. N (P s)\<rbrace>"
  shows "E s \<Longrightarrow> P s = P s'"
  using use_valid[where f=f, OF step pres[where N="\<lambda>p. p = P s"]] by simp

lemma use_validE_norm:
  "\<lbrakk> (Inr r', s') \<in> mres (f s); \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; P s \<rbrakk> \<Longrightarrow> Q r' s'"
  unfolding validE_def valid_def by force

lemma use_validE_except:
  "\<lbrakk> (Inl r', s') \<in> mres (f s); \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; P s \<rbrakk> \<Longrightarrow> E r' s'"
  unfolding validE_def valid_def by force

lemma in_inv_by_hoareD:
  "\<lbrakk> \<And>P. f \<lbrace>P\<rbrace>; (x,s') \<in> mres (f s) \<rbrakk> \<Longrightarrow> s' = s"
  by (auto simp add: valid_def) blast


subsection \<open>Misc\<close>

lemma hoare_gen_asm:
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P' and K P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp add: valid_def)

lemmas hoare_gen_asm_single = hoare_gen_asm[where P'="\<top>", simplified pred_conj_def simp_thms]

lemma hoare_gen_asm_lk:
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>K P and P'\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp add: valid_def)

\<comment> \<open>Useful for forward reasoning, when P is known.
    The first version allows weakening the precondition.\<close>
lemma hoare_gen_asm_spec':
  "\<lbrakk> \<And>s. P s \<Longrightarrow> S \<and> P' s; S \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_gen_asm_spec:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> S; S \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (rule hoare_gen_asm_spec'[where S=S and P'=P]) simp

lemma hoare_conjI:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> Q' r s\<rbrace>"
  unfolding valid_def by blast

lemma hoare_disjI1:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<or> Q' rv s \<rbrace>"
  unfolding valid_def by blast

lemma hoare_disjI2:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<or> Q' rv s \<rbrace>"
  unfolding valid_def by blast

lemma hoare_assume_pre:
  "(\<And>s. P s \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (auto simp: valid_def)

lemma hoare_assume_preE:
  "(\<And>s. P s \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
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
  "(P' \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. P' \<longrightarrow> Q rv s\<rbrace>"
  by (simp add: valid_def) blast

lemma validE_impI:
  "\<lbrakk>\<And>E. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>E\<rbrace>; (P' \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>)\<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. P' \<longrightarrow> Q rv s\<rbrace>, \<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_case_option_wp:
  "\<lbrakk> \<lbrace>P\<rbrace> f None \<lbrace>Q\<rbrace>; \<And>x.  \<lbrace>P' x\<rbrace> f (Some x) \<lbrace>Q' x\<rbrace> \<rbrakk>
  \<Longrightarrow> \<lbrace>case_option P P' v\<rbrace> f v \<lbrace>\<lambda>rv. case v of None \<Rightarrow> Q rv | Some x \<Rightarrow> Q' x rv\<rbrace>"
  by (cases v) auto

lemma hoare_case_option_wp2:
  "\<lbrakk> \<lbrace>P\<rbrace> f None \<lbrace>Q\<rbrace>; \<And>x.  \<lbrace>P' x\<rbrace> f (Some x) \<lbrace>Q' x\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>case_option P P' v\<rbrace> f v \<lbrace>\<lambda>rv s. case v of None \<Rightarrow> Q rv s | Some x \<Rightarrow> Q' x rv s\<rbrace>"
  by (cases v) auto

(* Might be useful for forward reasoning, when P is known. *)
lemma hoare_when_cases:
  "\<lbrakk>\<And>s. \<lbrakk>\<not>B; P s\<rbrakk> \<Longrightarrow> Q s; B \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> when B f \<lbrace>\<lambda>_. Q\<rbrace>"
  by (cases B; simp add: valid_def return_def mres_def)

lemma hoare_vcg_prop:
  "\<lbrace>\<lambda>s. P\<rbrace> f \<lbrace>\<lambda>rv s. P\<rbrace>"
  by (simp add: valid_def)


subsection \<open>@{const valid} and @{const validE}, @{const validE_R}, @{const validE_E}\<close>

lemma valid_validE:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>, \<lbrace>\<lambda>_. Q\<rbrace>"
  by (rule hoare_post_impE_dc)

lemma valid_validE2:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q'\<rbrace>; \<And>s. Q' s \<Longrightarrow> Q s; \<And>s. Q' s \<Longrightarrow> E s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>, \<lbrace>\<lambda>_. E\<rbrace>"
  unfolding valid_def validE_def
  by (clarsimp split: sum.splits) blast

lemma validE_valid:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>, \<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>"
  unfolding validE_def
  by fastforce

lemma valid_validE_R:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>,-"
  by (simp add: validE_R_def hoare_strengthen_postE[OF valid_validE])

lemma valid_validE_E:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f -,\<lbrace>\<lambda>_. Q\<rbrace>"
  by (simp add: validE_E_def hoare_strengthen_postE[OF valid_validE])

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

lemma validE_eq_valid:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q\<rbrace>,\<lbrace>\<lambda>rv. Q\<rbrace> = \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q\<rbrace>"
  by (simp add: validE_def)


subsection \<open>@{const liftM}\<close>

lemma in_image_constant:
  "(x \<in> (\<lambda>_. v) ` S) = (x = v \<and> S \<noteq> {})"
  by (simp add: image_constant_conv)

lemma hoare_liftM_subst:
  "\<lbrace>P\<rbrace> liftM f m \<lbrace>Q\<rbrace> = \<lbrace>P\<rbrace> m \<lbrace>Q \<circ> f\<rbrace>"
  apply (simp add: liftM_def bind_def' return_def split_def)
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
  "\<lbrakk> P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>; \<not>P \<Longrightarrow> \<lbrace>P''\<rbrace> g \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. (P \<longrightarrow> P' s) \<and> (\<not>P \<longrightarrow> P'' s)\<rbrace> if P then f else g \<lbrace>Q\<rbrace>"
  by simp

lemma hoare_vcg_if_splitE:
  "\<lbrakk> P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<not>P \<Longrightarrow> \<lbrace>P''\<rbrace> g \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. (P \<longrightarrow> P' s) \<and> (\<not>P \<longrightarrow> P'' s)\<rbrace> if P then f else g \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp

lemma hoare_vcg_split_case_option:
  "\<lbrakk> \<And>x. x = None \<Longrightarrow> \<lbrace>P x\<rbrace> f x \<lbrace>Q x\<rbrace>; \<And>x y. x = Some y \<Longrightarrow> \<lbrace>P' x y\<rbrace> g x y \<lbrace>Q x\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s. (x = None \<longrightarrow> P x s) \<and> (\<forall>y. x = Some y \<longrightarrow> P' x y s)\<rbrace>
       case x of None \<Rightarrow> f x | Some y \<Rightarrow> g x y
       \<lbrace>Q x\<rbrace>"
  by (cases x; simp)

lemma hoare_vcg_split_case_optionE:
  "\<lbrakk> \<And>x. x = None \<Longrightarrow> \<lbrace>P x\<rbrace> f x \<lbrace>Q x\<rbrace>,\<lbrace>E x\<rbrace>; \<And>x y. x = Some y \<Longrightarrow> \<lbrace>P' x y\<rbrace> g x y \<lbrace>Q x\<rbrace>,\<lbrace>E x\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s. (x = None \<longrightarrow> P x s) \<and> (\<forall>y. x = Some y \<longrightarrow> P' x y s)\<rbrace>
       case x of None \<Rightarrow> f x | Some y \<Rightarrow> g x y
       \<lbrace>Q x\<rbrace>, \<lbrace>E x\<rbrace>"
  by (cases x; simp)

lemma hoare_vcg_split_case_sum:
  "\<lbrakk> \<And>x a. x = Inl a \<Longrightarrow> \<lbrace>P x a\<rbrace> f x a \<lbrace>Q x\<rbrace>; \<And>x b. x = Inr b \<Longrightarrow> \<lbrace>P' x b\<rbrace> g x b \<lbrace>Q x\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s. (\<forall>a. x = Inl a \<longrightarrow> P x a s) \<and> (\<forall>b. x = Inr b \<longrightarrow> P' x b s)\<rbrace>
       case x of Inl a \<Rightarrow> f x a | Inr b \<Rightarrow> g x b
       \<lbrace>Q x\<rbrace>"
  by (cases x; simp)

lemma bind_wp_nobind:
  "\<lbrakk> \<lbrace>Q'\<rbrace> g \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> do f; g od \<lbrace>Q\<rbrace>"
  by (erule bind_wp_fwd) (clarsimp simp: valid_def)

lemma bindE_wp_nobind:
  "\<lbrakk> \<lbrace>Q'\<rbrace> g \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q'\<rbrace>, \<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> doE f; g odE \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  by (erule bindE_wp_fwd) (clarsimp simp: validE_def)

lemmas bind_wp_skip = bind_wp[where Q=Q and Q'=Q for Q]

lemma hoare_chain:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>; \<And>s. P s \<Longrightarrow> P' s; \<And>rv s. Q' rv s \<Longrightarrow> Q rv s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (wp_pre, rule hoare_post_imp)

lemma hoare_chainE:
  "\<lbrakk> \<lbrace>P'\<rbrace> A \<lbrace>Q'\<rbrace>,\<lbrace>E'\<rbrace>; \<And>s. P s \<Longrightarrow> P' s; \<And>rv s. Q' rv s \<Longrightarrow> Q rv s; \<And>rv s. E' rv s \<Longrightarrow> E rv s \<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace> A \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by wp_pre (rule hoare_post_impE)

lemma hoare_vcg_conj_lift:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>"
  unfolding valid_def
  by fastforce

\<comment> \<open>A variant which works nicely with subgoals that do not contain schematics\<close>
lemmas hoare_vcg_conj_lift_pre_fix = hoare_vcg_conj_lift[where P=P and P'=P for P, simplified]

lemma hoare_vcg_conj_liftE1:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding valid_def validE_R_def validE_def
  by (fastforce simp: split_def split: sum.splits)

lemma hoare_vcg_conj_liftE2:
  "\<lbrakk> \<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv s. E rv s \<and> E' rv s\<rbrace>"
  unfolding valid_def validE_E_def validE_def
  by (fastforce simp: split_def split: sum.splits)

lemma hoare_vcg_conj_liftE_weaker:
  assumes "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  assumes "\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>, \<lbrace>E\<rbrace>"
  shows "\<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>, \<lbrace>E\<rbrace>"
  apply (rule hoare_pre)
   apply (fastforce intro: assms hoare_vcg_conj_liftE1 validE_validE_R hoare_post_impE)
  apply simp
  done

lemma hoare_vcg_disj_lift:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<or> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<or> Q' rv s\<rbrace>"
  unfolding valid_def
  by fastforce

lemma hoare_vcg_disj_lift_R:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  assumes y: "\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,-"
  shows      "\<lbrace>\<lambda>s. P s \<or> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<or> Q' rv s\<rbrace>,-"
  using assms
  by (fastforce simp: validE_R_def validE_def valid_def split: sum.splits)

lemma hoare_vcg_const_Ball_lift:
  "\<lbrakk> \<And>x. x \<in> S \<Longrightarrow> \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x\<in>S. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x\<in>S. Q x rv s\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_vcg_const_Ball_liftE:
  "\<lbrakk> \<And>x. x \<in> S \<Longrightarrow> \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>\<lambda>s. True\<rbrace> f \<lbrace>\<lambda>r s. True\<rbrace>, \<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x\<in>S. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x\<in>S. Q x rv s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_vcg_const_Ball_liftE_R:
 "\<lbrakk> \<And>x. x \<in> S \<Longrightarrow> \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x \<in> S. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x \<in> S. Q x rv s\<rbrace>,-"
  unfolding validE_R_def validE_def
  by (rule hoare_strengthen_post)
     (fastforce intro!: hoare_vcg_const_Ball_lift split: sum.splits)+

lemma hoare_vcg_const_Ball_liftE_E:
 "(\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P x\<rbrace> f -,\<lbrace>Q x\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x \<in> S. P x s\<rbrace> f -,\<lbrace>\<lambda>rv s. \<forall>x \<in> S. Q x rv s\<rbrace>"
  unfolding validE_E_def validE_def valid_def
  by (fastforce split: sum.splits)

lemma hoare_vcg_all_lift:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_vcg_all_liftE:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_vcg_all_liftE_R:
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>, -) \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>, -"
  by (rule hoare_vcg_const_Ball_liftE_R[where S=UNIV, simplified])

lemma hoare_vcg_all_liftE_E:
  "(\<And>x. \<lbrace>P x\<rbrace> f -, \<lbrace>Q x\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> f -,\<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>"
  by (rule hoare_vcg_const_Ball_liftE_E[where S=UNIV, simplified])

lemma hoare_vcg_imp_lift:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>; \<lbrace>Q'\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P' s \<or> Q' s\<rbrace> f \<lbrace>\<lambda>rv s. P rv s \<longrightarrow> Q rv s\<rbrace>"
  by (simp only: imp_conv_disj) (rule hoare_vcg_disj_lift)

lemma hoare_vcg_imp_lift':
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>; \<lbrace>Q'\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<not> P' s \<longrightarrow> Q' s\<rbrace> f \<lbrace>\<lambda>rv s. P rv s \<longrightarrow> Q rv s\<rbrace>"
  by (wpsimp wp: hoare_vcg_imp_lift)

lemma hoare_vcg_imp_liftE:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>, \<lbrace>E\<rbrace>; \<lbrace>Q'\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s. P' s \<or> Q' s\<rbrace> f \<lbrace>\<lambda>rv s. P rv s \<longrightarrow> Q rv s\<rbrace>, \<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_vcg_imp_liftE':
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>, \<lbrace>E\<rbrace>; \<lbrace>Q'\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s. \<not> P' s \<longrightarrow> Q' s\<rbrace> f \<lbrace>\<lambda>rv s. P rv s \<longrightarrow> Q rv s\<rbrace>, \<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_vcg_imp_liftE_R:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>, -; \<lbrace>Q'\<rbrace> f \<lbrace>Q\<rbrace>, - \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P' s \<or> Q' s\<rbrace> f \<lbrace>\<lambda>rv s. P rv s \<longrightarrow> Q rv s\<rbrace>, -"
  by (auto simp add: valid_def validE_R_def validE_def split_def split: sum.splits)

lemma hoare_vcg_imp_liftE_R':
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>, -; \<lbrace>Q'\<rbrace> f \<lbrace>Q\<rbrace>, - \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<not>P' s \<longrightarrow> Q' s\<rbrace> f \<lbrace>\<lambda>rv s. P rv s \<longrightarrow> Q rv s\<rbrace>, -"
  by (auto simp add: valid_def validE_R_def validE_def split_def split: sum.splits)

lemma hoare_vcg_imp_liftE_E:
  "\<lbrakk>\<lbrace>P'\<rbrace> f -, \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>; \<lbrace>Q'\<rbrace> f -, \<lbrace>Q\<rbrace>\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. P' s \<or> Q' s\<rbrace> f -, \<lbrace>\<lambda>rv s. P rv s \<longrightarrow> Q rv s\<rbrace>"
  by (auto simp add: valid_def validE_E_def validE_def split_def split: sum.splits)

lemma hoare_vcg_imp_liftE_E':
  "\<lbrakk>\<lbrace>P'\<rbrace> f -, \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>; \<lbrace>Q'\<rbrace> f -, \<lbrace>Q\<rbrace>\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. \<not> P' s \<longrightarrow> Q' s\<rbrace> f -, \<lbrace>\<lambda>rv s. P rv s \<longrightarrow> Q rv s\<rbrace>"
  by (auto simp add: valid_def validE_E_def validE_def split_def split: sum.splits)

lemma hoare_vcg_imp_conj_lift[wp_comb]:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> Q' rv s\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. (Q rv s \<longrightarrow> Q'' rv s) \<and> Q''' rv s\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>P and P'\<rbrace> f \<lbrace>\<lambda>rv s. (Q rv s \<longrightarrow> Q' rv s \<and> Q'' rv s) \<and> Q''' rv s\<rbrace>"
  by (auto simp: valid_def)

lemmas hoare_vcg_imp_conj_lift'[wp_unsafe] = hoare_vcg_imp_conj_lift[where Q'''="\<top>\<top>", simplified]

lemma hoare_absorb_imp:
  "\<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> Q' rv s\<rbrace>"
  by (erule hoare_post_imp[rotated], blast)

lemma hoare_weaken_imp:
  "\<lbrakk> \<And>rv s. Q rv s \<Longrightarrow> Q' rv s ; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q' rv s \<longrightarrow> S rv s\<rbrace> \<rbrakk>
    \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> S rv s\<rbrace>"
  by (clarsimp simp: valid_def split_def)

lemma hoare_vcg_const_imp_lift:
  "\<lbrakk> P \<Longrightarrow> \<lbrace>P'\<rbrace> m \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> P' s\<rbrace> m \<lbrace>\<lambda>rv s. P \<longrightarrow> Q rv s\<rbrace>"
  by (cases P, simp_all add: hoare_vcg_prop)

lemma hoare_vcg_const_imp_liftE_E:
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f -, \<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> P' s\<rbrace> f -, \<lbrace>\<lambda>rv s. P \<longrightarrow> E rv s\<rbrace>"
  by (fastforce simp: validE_E_def validE_def valid_def split_def split: sum.splits)

lemma hoare_vcg_const_imp_liftE_R:
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> m \<lbrace>Q\<rbrace>,-) \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> P' s\<rbrace> m \<lbrace>\<lambda>rv s. P \<longrightarrow> Q rv s\<rbrace>,-"
  by (fastforce simp: validE_R_def validE_def valid_def split_def split: sum.splits)

lemma hoare_weak_lift_imp:
  "\<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> P' s\<rbrace> f \<lbrace>\<lambda>rv s. P \<longrightarrow> Q rv s\<rbrace>"
  by (auto simp add: valid_def split_def)

lemma hoare_weak_lift_impE:
  "\<lbrace>P'\<rbrace> m \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> P' s\<rbrace> m \<lbrace>\<lambda>rv s. P \<longrightarrow> Q rv s\<rbrace>,\<lbrace>\<lambda>rv s. P \<longrightarrow> E rv s\<rbrace>"
  by (cases P; simp add: validE_def hoare_vcg_prop)

lemma hoare_weak_lift_impE_R:
  "\<lbrace>P'\<rbrace> m \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> P' s\<rbrace> m \<lbrace>\<lambda>rv s. P \<longrightarrow> Q rv s\<rbrace>,-"
  by (cases P; wpsimp wp: wp_post_tautE_R)

lemma hoare_vcg_ex_lift:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<exists>x. Q x rv s\<rbrace>"
  by (clarsimp simp: valid_def, blast)

lemma hoare_vcg_ex_liftE:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<exists>x. Q x rv s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_vcg_ex_liftE_E:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> f -,\<lbrace>E x\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f -,\<lbrace>\<lambda>rv s. \<exists>x. E x rv s\<rbrace>"
  by (fastforce simp: validE_E_def validE_def valid_def split: sum.splits)

lemma hoare_vcg_ex_lift_R1:
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q\<rbrace>, -) \<Longrightarrow> \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>Q\<rbrace>, -"
  by (fastforce simp: valid_def validE_R_def validE_def split: sum.splits)

lemma hoare_liftP_ext:
  assumes "\<And>P x. m \<lbrace>\<lambda>s. P (f s x)\<rbrace>"
  shows "m \<lbrace>\<lambda>s. P (f s)\<rbrace>"
  unfolding valid_def
  apply clarsimp
  apply (erule subst[rotated, where P=P])
  apply (rule ext)
  apply (drule use_valid, rule assms, rule refl)
  apply simp
  done

(* for instantiations *)
lemma hoare_triv:    "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" .
lemma hoare_trivE:   "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>" .
lemma hoare_trivE_R: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-" .
lemma hoare_trivR_R: "\<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace>" .

lemma hoare_vcg_conj_liftE_E:
  "\<lbrakk> \<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>Q'\<rbrace>, \<lbrace>\<lambda>rv s. E rv s \<and> E' rv s\<rbrace>"
  unfolding validE_def validE_E_def
  by (rule hoare_post_imp[OF _ hoare_vcg_conj_lift]; simp split: sum.splits)

lemma hoare_vcg_conj_elimE:
  "\<lbrakk> \<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (rule hoare_strengthen_postE[OF hoare_vcg_conj_liftE_E]) (simp add: validE_R_def)+

lemma hoare_vcg_conj_liftE_R:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>,-"
  unfolding validE_R_def validE_def
  by (rule hoare_post_imp[OF _ hoare_vcg_conj_lift]; simp split: sum.splits)

lemma hoare_vcg_conj_liftE_R':
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>, -"
  apply (simp add: validE_R_def validE_def valid_def split: sum.splits)
  apply blast
  done

lemma hoare_lift_Pf_E_R:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> m \<lbrace>\<lambda>_. P x\<rbrace>, -; \<And>P. \<lbrace>\<lambda>s. P (f s)\<rbrace> m \<lbrace>\<lambda>_ s. P (f s)\<rbrace>, - \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. P (f s) s\<rbrace> m \<lbrace>\<lambda>_ s. P (f s) s\<rbrace>, -"
  by (fastforce simp: validE_R_def validE_def valid_def split: sum.splits)

lemma hoare_lift_Pf_E_E:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> m -, \<lbrace>\<lambda>_. P x\<rbrace>; \<And>P. \<lbrace>\<lambda>s. P (f s)\<rbrace> m -, \<lbrace>\<lambda>_ s. P (f s)\<rbrace> \<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. P (f s) s\<rbrace> m -, \<lbrace>\<lambda>_ s. P (f s) s\<rbrace>"
  by (fastforce simp: validE_E_def validE_def valid_def split: sum.splits)

lemma hoare_post_comb_imp_conj:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>"
  by (wpsimp wp: hoare_vcg_conj_lift)

lemma hoare_vcg_if_lift:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. (P' \<longrightarrow> X rv s) \<and> (\<not>P' \<longrightarrow> Y rv s)\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. if P' then X rv s else Y rv s\<rbrace>"

  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. (P' \<longrightarrow> X rv s) \<and> (\<not>P' \<longrightarrow> Y rv s)\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. if P' then X rv else Y rv\<rbrace>"
  by (auto simp: valid_def split_def)

lemma hoare_vcg_split_lift[wp]:
  "\<lbrace>P\<rbrace> f x y \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> case (x, y) of (a, b) \<Rightarrow> f a b \<lbrace>Q\<rbrace>"
  by simp

named_theorems hoare_vcg_op_lift
lemmas [hoare_vcg_op_lift] =
  hoare_vcg_const_imp_lift
  hoare_vcg_const_imp_liftE_E
  hoare_vcg_const_imp_liftE_R
  (* leaving out hoare_vcg_conj_lift*, because that is built into wp *)
  hoare_vcg_disj_lift
  hoare_vcg_disj_lift_R
  hoare_vcg_ex_lift
  hoare_vcg_ex_liftE
  hoare_vcg_ex_liftE_E
  hoare_vcg_all_lift
  hoare_vcg_all_liftE
  hoare_vcg_all_liftE_E
  hoare_vcg_all_liftE_R
  hoare_vcg_const_Ball_lift
  hoare_vcg_const_Ball_liftE
  hoare_vcg_const_Ball_liftE_R
  hoare_vcg_const_Ball_liftE_E
  hoare_vcg_split_lift
  hoare_vcg_if_lift
  hoare_vcg_imp_lift'
  hoare_vcg_imp_liftE'
  hoare_vcg_imp_liftE_R'
  hoare_vcg_imp_liftE_E'


subsection \<open>Weakest Precondition Rules\<close>

lemma fail_wp:
  "\<lbrace>\<top>\<rbrace> fail \<lbrace>Q\<rbrace>"
  by (simp add: valid_def fail_def mres_def vimage_def)

lemma return_wp:
  "\<lbrace>P x\<rbrace> return x \<lbrace>P\<rbrace>"
  by(simp add: valid_def return_def mres_def)

lemma get_wp:
  "\<lbrace>\<lambda>s. P s s\<rbrace> get \<lbrace>P\<rbrace>"
  by (simp add: valid_def get_def mres_def)

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
  unfolding catch_def valid_def validE_def return_def mres_def image_def
  by (fastforce simp: bind_def split: sum.splits tmres.splits)

lemma handleE'_wp:
  "\<lbrakk> \<And>x. \<lbrace>F x\<rbrace> handler x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>F\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f <handle2> handler \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding handleE'_def valid_def validE_def return_def mres_def image_def
  by (fastforce simp: bind_def split: sum.splits tmres.splits)

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
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E'\<rbrace>; \<And>e. \<lbrace>E' e\<rbrace> g e \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<And>x. \<lbrace>Q' x\<rbrace> h x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> f <handle> g <else> h \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding handle_elseE_def validE_def
  by (wpsimp wp: bind_wp_fwd | assumption | rule conjI)+

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
  "\<lbrace>\<lambda>s. \<forall>t. (s, t) \<in> f \<longrightarrow> P () t\<rbrace> state_select f \<lbrace>P\<rbrace>"
  unfolding state_select_def2
  by (wpsimp wp: put_wp select_wp return_wp get_wp assert_wp)

lemma condition_wp:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> g \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. if C s then P s else P' s\<rbrace> condition C f g \<lbrace>Q\<rbrace>"
  by (clarsimp simp: condition_def valid_def)

lemma conditionE_wp:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P'\<rbrace> g \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. if C s then P s else P' s\<rbrace> condition C f g \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (clarsimp simp: condition_def validE_def valid_def)

lemma state_assert_wp:
  "\<lbrace>\<lambda>s. f s \<longrightarrow> P () s\<rbrace> state_assert f \<lbrace>P\<rbrace>"
  unfolding state_assert_def
  by (wp bind_wp_fwd get_wp assert_wp)

lemma when_wp[wp_split]:
  "\<lbrakk> P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>if P then P' else Q ()\<rbrace> when P f \<lbrace>Q\<rbrace>"
  by (clarsimp simp: when_def valid_def return_def mres_def)

lemma unless_wp[wp_split]:
  "(\<not>P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>if P then Q () else P'\<rbrace> unless P f \<lbrace>Q\<rbrace>"
  unfolding unless_def by wp auto

lemma whenE_wp:
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>if P then P' else Q ()\<rbrace> whenE P f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding whenE_def by clarsimp (wp returnOk_wp)

lemma unlessE_wp:
  "(\<not> P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>if P then Q () else P'\<rbrace> unlessE P f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding unlessE_def
  by (wpsimp wp: returnOk_wp)

lemma maybeM_wp:
  "(\<And>x. y = Some x \<Longrightarrow> \<lbrace>P x\<rbrace> m x \<lbrace>Q\<rbrace>) \<Longrightarrow>
   \<lbrace>\<lambda>s. (\<forall>x. y = Some x \<longrightarrow> P x s) \<and> (y = None \<longrightarrow> Q () s)\<rbrace> maybeM m y \<lbrace>Q\<rbrace>"
  unfolding maybeM_def by (wpsimp wp: return_wp) auto

lemma notM_wp:
  "\<lbrace>P\<rbrace> m \<lbrace>\<lambda>c. Q (\<not> c)\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> notM m \<lbrace>Q\<rbrace>"
  unfolding notM_def by (wpsimp wp: return_wp)

lemma ifM_wp:
  assumes [wp]: "\<lbrace>Q\<rbrace> f \<lbrace>S\<rbrace>" "\<lbrace>Q'\<rbrace> g \<lbrace>S\<rbrace>"
  assumes [wp]: "\<lbrace>A\<rbrace> P \<lbrace>\<lambda>c s. c \<longrightarrow> Q s\<rbrace>" "\<lbrace>B\<rbrace> P \<lbrace>\<lambda>c s. \<not>c \<longrightarrow> Q' s\<rbrace>"
  shows "\<lbrace>A and B\<rbrace> ifM P f g \<lbrace>S\<rbrace>"
  unfolding ifM_def
  by (wpsimp wp: hoare_vcg_if_split hoare_vcg_conj_lift)

lemma andM_wp:
  assumes [wp]: "\<lbrace>Q'\<rbrace> B \<lbrace>Q\<rbrace>"
  assumes [wp]: "\<lbrace>P\<rbrace> A \<lbrace>\<lambda>c s. c \<longrightarrow> Q' s\<rbrace>" "\<lbrace>P'\<rbrace> A \<lbrace>\<lambda>c s. \<not> c \<longrightarrow> Q False s\<rbrace>"
  shows "\<lbrace>P and P'\<rbrace> andM A B \<lbrace>Q\<rbrace>"
  unfolding andM_def by (wp ifM_wp return_wp)

lemma orM_wp:
  assumes [wp]: "\<lbrace>Q'\<rbrace> B \<lbrace>Q\<rbrace>"
  assumes [wp]: "\<lbrace>P\<rbrace> A \<lbrace>\<lambda>c s. c \<longrightarrow> Q True s\<rbrace>" "\<lbrace>P'\<rbrace> A \<lbrace>\<lambda>c s. \<not> c \<longrightarrow> Q' s\<rbrace>"
  shows "\<lbrace>P and P'\<rbrace> orM A B \<lbrace>Q\<rbrace>"
  unfolding orM_def by (wp ifM_wp return_wp)

lemma whenM_wp:
  assumes [wp]: "\<lbrace>Q\<rbrace> f \<lbrace>S\<rbrace>"
  assumes [wp]: "\<lbrace>A\<rbrace> P \<lbrace>\<lambda>c s. c \<longrightarrow> Q s\<rbrace>" "\<lbrace>B\<rbrace> P \<lbrace>\<lambda>c s. \<not>c \<longrightarrow> S () s\<rbrace>"
  shows "\<lbrace>A and B\<rbrace> whenM P f \<lbrace>S\<rbrace>"
  unfolding whenM_def by (wp ifM_wp return_wp)

lemma hoare_K_bind[wp_split]:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> K_bind f x \<lbrace>Q\<rbrace>"
  by simp

lemma validE_K_bind[wp_split]:
  "\<lbrace> P \<rbrace> x \<lbrace> Q \<rbrace>, \<lbrace> E \<rbrace> \<Longrightarrow> \<lbrace> P \<rbrace> K_bind x f \<lbrace> Q \<rbrace>, \<lbrace> E \<rbrace>"
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

lemma assert_opt_wp:
  "\<lbrace>\<lambda>s. x \<noteq> None \<longrightarrow> Q (the x) s\<rbrace> assert_opt x \<lbrace>Q\<rbrace>"
  unfolding assert_opt_def
  by (cases x; wpsimp wp: fail_wp return_wp)

lemma gets_the_wp:
  "\<lbrace>\<lambda>s. (f s \<noteq> None) \<longrightarrow> Q (the (f s)) s\<rbrace> gets_the f \<lbrace>Q\<rbrace>"
  unfolding gets_the_def
  by (wp bind_wp_fwd gets_wp assert_opt_wp)

lemma gets_the_wp': (* FIXME: should prefer this one in [wp] *)
  "\<lbrace>\<lambda>s. \<forall>rv. f s = Some rv \<longrightarrow> Q rv s\<rbrace> gets_the f \<lbrace>Q\<rbrace>"
  unfolding gets_the_def
  by (wpsimp wp: bind_wp_fwd gets_wp assert_opt_wp)

lemma gets_map_wp:
  "\<lbrace>\<lambda>s. f s p \<noteq> None \<longrightarrow> Q (the (f s p)) s\<rbrace> gets_map f p \<lbrace>Q\<rbrace>"
  unfolding gets_map_def
  by (wpsimp wp: bind_wp_fwd gets_wp assert_opt_wp)

lemma gets_map_wp':
  "\<lbrace>\<lambda>s. \<forall>rv. f s p = Some rv \<longrightarrow> Q rv s\<rbrace> gets_map f p \<lbrace>Q\<rbrace>"
  unfolding gets_map_def
  by (wpsimp wp: bind_wp_fwd gets_wp assert_opt_wp)

(* FIXME: make wp *)
lemma whenE_throwError_wp:
  "\<lbrace>\<lambda>s. \<not>Q \<longrightarrow> P s\<rbrace> whenE Q (throwError e) \<lbrace>\<lambda>_. P\<rbrace>, -"
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
  validE_validE_E
  hoare_vcg_conj_liftE_R
  hoare_vcg_conj_elimE
  hoare_vcg_conj_liftE_E

lemmas hoare_wp_state_combsE =
  valid_validE_R
  hoare_vcg_conj_liftE_R[OF valid_validE_R]
  hoare_vcg_conj_elimE[OF valid_validE_E]
  hoare_vcg_conj_liftE_E[OF valid_validE_E]

lemmas hoare_classic_wp_combs = hoare_post_comb_imp_conj hoare_weaken_pre hoare_wp_combs
lemmas hoare_classic_wp_combsE = hoare_weaken_preE hoare_weaken_preE_R hoare_wp_combsE

lemmas hoare_classic_wp_state_combsE =
  hoare_weaken_preE[OF valid_validE]
  hoare_weaken_preE_R[OF valid_validE_R]
  hoare_wp_state_combsE

lemmas all_classic_wp_combs =
  hoare_classic_wp_state_combsE
  hoare_classic_wp_combsE
  hoare_classic_wp_combs

lemmas hoare_wp_splits[wp_split] =
  handleE'_wp handleE_wp
  validE_validE_R [OF handleE'_wp [OF validE_R_validE]]
  validE_validE_R [OF handleE_wp [OF validE_R_validE]]
  catch_wp hoare_vcg_if_split hoare_vcg_if_splitE
  validE_validE_R [OF hoare_vcg_if_splitE [OF validE_R_validE validE_R_validE]]
  liftM_wp liftME_wp
  validE_validE_R [OF liftME_wp [OF validE_R_validE]]
  validE_valid

lemmas [wp_comb] = hoare_wp_state_combsE hoare_wp_combsE hoare_wp_combs

(* Add these rules to wp first to control when they are applied. We want them used last, only when
   no other more specific wp rules apply.
   bind_wp, bindE_wp and their variants are wp rules instead of wp_split rules because
   they should be used before other wp_split rules, and in combination with wp_comb rules when
   necessary.
   hoare_vcg_prop is unsafe in certain circumstances but still useful to have applied automatically,
   so we make it the very last rule to be tried. *)
lemmas [wp] =
  hoare_vcg_prop bind_wp
  bindE_R_wp bindE_E_wp bindE_wp
  bind_wpE_R bind_wpE_E bind_wpE

(* rules towards the bottom will be matched first *)
lemmas [wp] = wp_post_tauts
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
              assert_opt_wp
              gets_the_wp
              gets_map_wp'
              liftE_wp
              alternative_wp
              alternativeE_R_wp
              alternativeE_E_wp
              alternativeE_wp
              select_wp
              state_select_wp
              condition_wp
              conditionE_wp
              maybeM_wp notM_wp ifM_wp andM_wp orM_wp whenM_wp

lemmas [wp_trip] = valid_is_triple validE_is_triple validE_E_is_triple validE_R_is_triple

lemmas validE_E_combs[wp_comb] =
    hoare_vcg_conj_liftE_E[where Q'="\<top>\<top>", folded validE_E_def]
    valid_validE_E
    hoare_vcg_conj_liftE_E[where Q'="\<top>\<top>", folded validE_E_def, OF valid_validE_E]


subsection \<open>Simplifications on conjunction\<close>

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

lemmas hoare_wp_simps[wp_split] =
  vcg_rhs_simps[THEN hoare_post_eq] vcg_rhs_simps[THEN hoare_post_eqE1]
  vcg_rhs_simps[THEN hoare_post_eqE2] vcg_rhs_simps[THEN hoare_post_eqE_R]
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


subsection \<open>Bundles\<close>

bundle no_pre = hoare_pre [wp_pre del]

bundle classic_wp_pre = hoare_pre [wp_pre del]
    all_classic_wp_combs[wp_comb del] all_classic_wp_combs[wp_comb]


text \<open>Miscellaneous lemmas on hoare triples\<close>

lemma hoare_pre_cases:
  "\<lbrakk> \<lbrace>\<lambda>s. C s \<and> P s\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>\<lambda>s. \<not>C s \<and> P' s\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace> f \<lbrace>Q\<rbrace>"
  unfolding valid_def by fastforce

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

lemmas whenE_wps[wp_split] =
  whenE_wp whenE_wp[THEN validE_validE_R] whenE_wp[THEN validE_validE_E]

lemmas unlessE_wps[wp_split] =
  unlessE_wp unlessE_wp[THEN validE_validE_R] unlessE_wp[THEN validE_validE_E]

lemma hoare_use_eq:
  assumes "\<And>P. \<lbrace>\<lambda>s. P (f s)\<rbrace> m \<lbrace>\<lambda>_ s. P (f s)\<rbrace>"
  assumes "\<And>f. \<lbrace>\<lambda>s. P f s\<rbrace> m \<lbrace>\<lambda>_ s. Q f s\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (f s) s\<rbrace> m \<lbrace>\<lambda>_ s. Q (f s) s \<rbrace>"
  apply (rule hoare_post_imp[where Q'="\<lambda>_ s. \<exists>y. y = f s \<and> Q y s"], simp)
  apply (wpsimp wp: hoare_vcg_ex_lift assms)
  done

lemma hoare_fail_any[simp]:
  "\<lbrace>P\<rbrace> fail \<lbrace>Q\<rbrace>"
  by wp

lemma hoare_failE[simp]:
  "\<lbrace>P\<rbrace> fail \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  by wp

lemma hoare_validE_pred_conj:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q and Q'\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding valid_def validE_def
  by (simp add: split_def split: sum.splits)

lemma hoare_validE_conj:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding valid_def validE_def
  by (simp add: split_def split: sum.splits)

lemmas if_validE_E[wp_split] =
  validE_validE_E[OF hoare_vcg_if_splitE[OF validE_E_validE validE_E_validE]]

lemma hoare_drop_imp:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q' rv s \<longrightarrow> Q rv s\<rbrace>"
  by (auto simp: valid_def)

lemma hoare_drop_impE:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q' rv s \<longrightarrow> Q rv s\<rbrace>, \<lbrace>E\<rbrace>"
  by (simp add: hoare_chainE)

lemma hoare_drop_impE_R:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q' rv s \<longrightarrow> Q rv s\<rbrace>, -"
  by (auto simp: validE_R_def validE_def valid_def split_def split: sum.splits)

(*Q is used instead of E so that hoare_drop_imps can be instantiated, which requires that all of its
  thms have the same variables.*)
lemma hoare_drop_impE_E:
  "\<lbrace>P\<rbrace> f -,\<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f -, \<lbrace>\<lambda>rv s. Q' rv s \<longrightarrow> Q rv s\<rbrace>"
  by (auto simp: validE_E_def validE_def valid_def split_def split: sum.splits)

lemmas hoare_drop_imps = hoare_drop_imp hoare_drop_impE hoare_drop_impE_R hoare_drop_impE_E

(*This is unsafe, but can be very useful when supplied as a comb rule.*)
lemma hoare_drop_imp_conj[wp_unsafe]:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. (Q rv s \<longrightarrow> Q'' rv s) \<and> Q''' rv s\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>P and P'\<rbrace> f \<lbrace>\<lambda>rv s. (Q rv s \<longrightarrow> Q' rv s \<and> Q'' rv s) \<and> Q''' rv s\<rbrace>"
  by (auto simp: valid_def)

lemmas hoare_drop_imp_conj'[wp_unsafe] = hoare_drop_imp_conj[where Q'''="\<top>\<top>", simplified]

lemma hoare_vcg_set_pred_lift:
  assumes "\<And>P x. m \<lbrace> \<lambda>s. P (f x s) \<rbrace>"
  shows "m \<lbrace> \<lambda>s. P {x. f x s} \<rbrace>"
  using assms[where P="\<lambda>x . x"] assms[where P=Not] use_valid
  by (fastforce simp: valid_def elim!: subst[rotated, where P=P])

lemma hoare_vcg_set_pred_lift_mono:
  assumes f: "\<And>x. m \<lbrace> f x \<rbrace>"
  assumes mono: "\<And>A B. A \<subseteq> B \<Longrightarrow> P A \<Longrightarrow> P B"
  shows "m \<lbrace> \<lambda>s. P {x. f x s} \<rbrace>"
  by (fastforce simp: valid_def elim!: mono[rotated] dest: use_valid[OF _ f])

text \<open>If a function contains an @{term assert}, or equivalent, then it might be
      possible to strengthen the precondition of an already-proven hoare triple
      @{text pos}, by additionally proving a side condition @{text neg}, that
      violating some condition causes failure. The stronger hoare triple produced
      by this theorem allows the precondition to assume that the condition is
      satisfied.\<close>
lemma hoare_strengthen_pre_via_assert_forward:
  assumes pos: "\<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>"
  assumes rel: "\<And>s. S s \<longrightarrow> P s \<or> N s"
  assumes neg: "\<lbrace> N \<rbrace> f \<lbrace> \<bottom>\<bottom> \<rbrace>"
  shows "\<lbrace> S \<rbrace> f \<lbrace> Q \<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule hoare_strengthen_post)
    apply (rule hoare_vcg_disj_lift[OF pos neg])
   by (auto simp: rel)

text \<open>Like @{thm hoare_strengthen_pre_via_assert_forward}, strengthen a precondition
      by proving a side condition that the negation of that condition would cause
      failure. This version is intended for backward reasoning. Apply it to a goal to
      obtain a stronger precondition after proving the side condition.\<close>
lemma hoare_strengthen_pre_via_assert_backward:
  assumes neg: "\<lbrace> Not \<circ> E \<rbrace> f \<lbrace> \<bottom>\<bottom> \<rbrace>"
  assumes pos: "\<lbrace> P and E \<rbrace> f \<lbrace> Q \<rbrace>"
  shows "\<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>"
  by (rule hoare_strengthen_pre_via_assert_forward[OF pos _ neg], simp)


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
  "\<lbrace>P\<rbrace> assert Q \<lbrace>\<lambda>_ s. P s \<and> Q\<rbrace>"
  by (simp add: assert_def fail_def return_def valid_def mres_def)

lemma hoare_gets_sp:
  "\<lbrace>P\<rbrace> gets f \<lbrace>\<lambda>rv s. rv = f s \<and> P s\<rbrace>"
  by (simp add: valid_def simpler_gets_def mres_def)

lemma hoare_returnOk_sp:
  "\<lbrace>P\<rbrace> returnOk x \<lbrace>\<lambda>rv s. rv = x \<and> P s\<rbrace>, \<lbrace>Q\<rbrace>"
  by (simp add: valid_def validE_def returnOk_def return_def mres_def)

\<comment> \<open>For forward reasoning in Hoare proofs, these lemmas allow us to step over the
    left-hand-side of monadic bind, while keeping the same precondition.\<close>

named_theorems forward_inv_step_rules

lemmas hoare_forward_inv_step_nobind[forward_inv_step_rules] =
  bind_wp_nobind[where Q'=P and P=P for P, rotated]

lemmas bind_wp_fwd_skip[forward_inv_step_rules] =
  bind_wp_fwd[where Q'="\<lambda>_. P" and P=P for P]

lemmas hoare_forward_inv_step_nobindE_valid[forward_inv_step_rules] =
  bindE_wp_nobind[where Q'=P and P=P and E="\<lambda>_. Q" and Q="\<lambda>_. Q" for P Q,
                        simplified validE_eq_valid, rotated]

lemmas hoare_forward_inv_step_valid[forward_inv_step_rules] =
  bindE_wp_fwd[where Q'="\<lambda>_. P" and P=P and E="\<lambda>_. Q" and Q="\<lambda>_. Q" for P Q,
                 simplified validE_eq_valid]

lemmas hoare_forward_inv_step_nobindE[forward_inv_step_rules] =
  bindE_wp_nobind[where Q'=P and P=P for P, rotated]

lemmas bindE_wp_fwd_skip[forward_inv_step_rules] =
  bindE_wp_fwd[where Q'="\<lambda>_. P" and P=P for P]

lemmas hoare_forward_inv_step_nobindE_validE_E[forward_inv_step_rules] =
  hoare_forward_inv_step_nobindE[where Q="\<top>\<top>", simplified validE_E_def[symmetric]]

lemmas hoare_forward_inv_step_validE_E[forward_inv_step_rules] =
  bindE_wp_fwd_skip[where Q="\<top>\<top>", simplified validE_E_def[symmetric]]

lemmas hoare_forward_inv_step_nobindE_validE_R[forward_inv_step_rules] =
  hoare_forward_inv_step_nobindE[where E="\<top>\<top>", simplified validE_R_def[symmetric]]

lemmas hoare_forward_inv_step_validE_R[forward_inv_step_rules] =
  bindE_wp_fwd_skip[where E="\<top>\<top>", simplified validE_R_def[symmetric]]

method forward_inv_step uses wp simp =
  rule forward_inv_step_rules, solves \<open>wpsimp wp: wp simp: simp\<close>

end
