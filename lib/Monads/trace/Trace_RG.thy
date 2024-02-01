(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Trace_RG
  imports
    Trace_More_VCG
    Trace_Monad_Equations
    Trace_Prefix_Closed
begin

section \<open>Rely-Guarantee Logic\<close>

subsection \<open>Validity\<close>

text \<open>
  This section defines a Rely-Guarantee logic for partial correctness for
  the interference trace monad.

  The logic is defined semantically. Rules work directly on the
  validity predicate.

  In the interference trace monad, RG validity is a quintuple of precondition,
  rely, monad, guarantee, and postcondition. The precondition is a function
  from initial state to current state to bool (a state predicate), the rely and
  guarantee are functions from state before to state after to bool, and the
  postcondition is a function from return value to last state in the trace to
  final state to bool. A quintuple is valid if for all initial and current
  states that satisfy the precondition and all traces that satisfy the rely,
  all of the pssible self steps performed by the monad satisfy the guarantee
  and all of the result values and result states that are returned by the monad
  satisfy the postcondition. Note that if the computation returns an empty
  trace and no successful results then the quintuple is trivially valid. This
  means @{term "assert P"} does not require us to prove that @{term P} holds,
  but rather allows us to assume @{term P}! Proving non-failure is done via a
  separate predicate and calculus (see @{text Trace_No_Fail}).\<close>

primrec trace_steps :: "(tmid \<times> 's) list \<Rightarrow> 's \<Rightarrow> (tmid \<times> 's \<times> 's) set" where
    "trace_steps (elem # trace) s0 = {(fst elem, s0, snd elem)} \<union> trace_steps trace (snd elem)"
  | "trace_steps [] s0 = {}"

lemma trace_steps_nth:
  "trace_steps xs s0 = (\<lambda>i. (fst (xs ! i), (if i = 0 then s0 else snd (xs ! (i - 1))), snd (xs ! i))) ` {..< length xs}"
proof (induct xs arbitrary: s0)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  show ?case
    apply (simp add: lessThan_Suc_eq_insert_0 Cons image_image nth_Cons')
    apply (intro arg_cong2[where f=insert] refl image_cong)
    apply simp
    done
qed

text \<open>@{text rg_pred} type: Rely-Guaranty predicates (@{text "state before => state after => bool"})\<close>
type_synonym 's rg_pred = "'s \<Rightarrow> 's \<Rightarrow> bool"

text \<open>Abbreviations for trivial postconditions (taking three arguments):\<close>
abbreviation(input)
  toptoptop :: "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" ("\<top>\<top>\<top>") where
  "\<top>\<top>\<top> \<equiv> \<lambda>_ _ _. True"

abbreviation(input)
  botbotbot :: "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" ("\<bottom>\<bottom>\<bottom>") where
  "\<bottom>\<bottom>\<bottom> \<equiv> \<lambda>_ _ _. False"

text \<open>
  Test whether the environment steps in @{text tr} satisfy the rely condition @{text R},
  assuming that @{text s0s} was the initial state before the first step in the trace.\<close>
definition rely_cond :: "'s rg_pred \<Rightarrow> 's \<Rightarrow> (tmid \<times> 's) list \<Rightarrow> bool" where
  "rely_cond R s0s tr = (\<forall>(ident, s0, s) \<in> trace_steps (rev tr) s0s. ident = Env \<longrightarrow> R s0 s)"

text \<open>
  Test whether the self steps in @{text tr} satisfy the guarantee condition @{text G},
  assuming that @{text s0s} was the initial state before the first step in the trace.\<close>
definition guar_cond :: "'s rg_pred \<Rightarrow> 's \<Rightarrow> (tmid \<times> 's) list \<Rightarrow> bool" where
  "guar_cond G s0s tr = (\<forall>(ident, s0, s) \<in> trace_steps (rev tr) s0s. ident = Me \<longrightarrow> G s0 s)"

lemma rg_empty_conds[simp]:
  "rely_cond R s0s []"
  "guar_cond G s0s []"
  by (simp_all add: rely_cond_def guar_cond_def)

lemma rg_conds_True[simp]:
  "rely_cond \<top>\<top> = \<top>\<top>"
  "guar_cond \<top>\<top> = \<top>\<top>"
  by (clarsimp simp: rely_cond_def guar_cond_def fun_eq_iff)+

text \<open>
  @{text "rely f R s0s"} constructs a new function from @{text f}, where the environment
  steps are constrained by @{text R} and @{text s0s} was the initial state before the first
  step in the trace.\<close>
definition rely :: "('s, 'a) tmonad \<Rightarrow> 's rg_pred \<Rightarrow> 's \<Rightarrow> ('s, 'a) tmonad" where
  "rely f R s0s \<equiv> (\<lambda>s. f s \<inter> ({tr. rely_cond R s0s tr} \<times> UNIV))"

definition validI ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's rg_pred \<Rightarrow> ('s,'a) tmonad \<Rightarrow> 's rg_pred \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)/ _ /(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)") where
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<equiv>
     prefix_closed f
     \<and> (\<forall>s0 s tr res. P s0 s \<and> (tr, res) \<in> (rely f R s0 s)
         \<longrightarrow> guar_cond G s0 tr
           \<and> (\<forall>rv s'. res = Result (rv, s') \<longrightarrow> Q rv (last_st_tr tr s0) s'))"

text \<open>
  We often reason about invariant predicates. The following provides shorthand syntax
  that avoids repeating potentially long predicates.\<close>
abbreviation (input) invariantI ::
  "('s,'a) tmonad \<Rightarrow> 's rg_pred \<Rightarrow> 's rg_pred \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("_/ \<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>" [59,0] 60) where
  "invariantI f R G P \<equiv> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>"

text \<open> Validity for exception monad with interferences, built on @{term validI}. \<close>
definition validIE ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's rg_pred \<Rightarrow> ('s, 'a + 'b) tmonad \<Rightarrow> 's rg_pred \<Rightarrow> ('b \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)/ _ /(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)") where
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<equiv> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace> \<lambda>v s0 s. case v of Inr r \<Rightarrow> Q r s0 s | Inl e \<Rightarrow> E e s0 s \<rbrace>"

lemma validIE_def2:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<equiv>
     prefix_closed f
     \<and> (\<forall>s0 s tr res. P s0 s \<and> (tr, res) \<in> (rely f R s0 s)
         \<longrightarrow> guar_cond G s0 tr
           \<and> (\<forall>rv s'. res = Result (rv, s')
                \<longrightarrow> (case rv of Inr b \<Rightarrow> Q b (last_st_tr tr s0) s' | Inl a \<Rightarrow> E a (last_st_tr tr s0) s')))"
  by (unfold validI_def validIE_def)

text \<open>
  The following two abbreviations are convenient to separate reasoning for exceptional and
  normal case.\<close>
abbreviation validIE_R ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's rg_pred \<Rightarrow> ('s, 'a + 'b) tmonad \<Rightarrow> 's rg_pred \<Rightarrow> ('b \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
   bool"
  ("(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)/ _ /(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>,/ -)") where
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,- \<equiv> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>"

abbreviation validIE_E ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's rg_pred \<Rightarrow> ('s, 'a + 'b) tmonad \<Rightarrow> 's rg_pred \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    bool"
  ("(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)/ _ /(\<lbrace>_\<rbrace>,/ -,/ \<lbrace>_\<rbrace>)") where
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,-,\<lbrace>E\<rbrace> \<equiv> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>,\<lbrace>E\<rbrace>"

text \<open>
  The following abbreviations are convenient to separate reasoning about postconditions and the
  guarantee condition.\<close>
abbreviation validI_no_guarantee ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's rg_pred \<Rightarrow> ('s,'a) tmonad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)/ _ /(-,/ \<lbrace>_\<rbrace>)") where
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>Q\<rbrace> \<equiv> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>Q\<rbrace>"

abbreviation (input) invariantI_no_guarantee ::
  "('s,'a) tmonad \<Rightarrow> 's rg_pred \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("_/ \<lbrace>_\<rbrace>,/ -,/ \<lbrace>_\<rbrace>" [59,0] 60) where
  "f \<lbrace>R\<rbrace>, -, \<lbrace>P\<rbrace> \<equiv> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>"

abbreviation validIE_no_guarantee ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's rg_pred \<Rightarrow> ('s, 'a + 'b) tmonad \<Rightarrow> ('b \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)/ _ /(-,/ \<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)") where
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<equiv> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"

abbreviation validIE_R_no_guarantee ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's rg_pred \<Rightarrow> ('s, 'a + 'b) tmonad \<Rightarrow> ('b \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)/ _ /(-,/ \<lbrace>_\<rbrace>,/ -)") where
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>Q\<rbrace>,- \<equiv> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>"

abbreviation validIE_E_no_guarantee ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's rg_pred \<Rightarrow> ('s, 'a + 'b) tmonad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)/ _ /(-,/ -,/ \<lbrace>_\<rbrace>)") where
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f -,-,\<lbrace>E\<rbrace> \<equiv> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>,\<lbrace>E\<rbrace>"

lemma in_rely:
  "\<lbrakk>(tr, res) \<in> f s; rely_cond R s0s tr\<rbrakk> \<Longrightarrow> (tr, res) \<in> rely f R s0s s"
  by (simp add: rely_def)

lemmas validI_D =
  validI_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, rule_format,
             OF _ conjI, OF _ _ in_rely]
lemmas validI_GD = validI_D[THEN conjunct1]
lemmas validI_rvD = validI_D[THEN conjunct2, rule_format, rotated -1, OF refl]
lemmas validI_prefix_closed = validI_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct1]
lemmas validI_prefix_closed_T =
  validI_prefix_closed[where P="\<lambda>_ _. False" and R="\<lambda>_ _. False" and G="\<lambda>_ _. True"
                         and Q="\<lambda>_ _ _. True"]

declare validI_prefix_closed[elim!]


section \<open>Pre Lemmas\<close>

lemma rg_weaken_pre:
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<And>s0 s. P s0 s \<Longrightarrow> P' s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (simp add: validI_def, blast)

lemmas rg_pre_imp = rg_weaken_pre[rotated]

lemma rg_weaken_preE:
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<And>s0 s. P s0 s \<Longrightarrow> P' s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: validIE_def rg_weaken_pre)

lemma rely_weaken:
  "\<lbrakk>\<forall>s0 s. R s0 s \<longrightarrow> R' s0 s; (tr, res) \<in> rely f R s s0\<rbrakk>
   \<Longrightarrow> (tr, res) \<in> rely f R' s s0"
  by (simp add: rely_def rely_cond_def, blast)

lemma rg_weaken_rely:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R'\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<And>s0 s. R s0 s \<Longrightarrow> R' s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (simp add: validI_def)
  by (metis rely_weaken)

lemma rg_weaken_relyE:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R'\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<And>s0 s. R s0 s \<Longrightarrow> R' s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: validIE_def rg_weaken_rely)

lemma rg_weaken_pre_rely:
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R'\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<And>s0 s. R s0 s \<Longrightarrow> R' s0 s; \<And>s0 s. P s0 s \<Longrightarrow> P' s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (rule rg_weaken_pre, rule rg_weaken_rely; assumption)

lemma rg_weaken_pre_relyE:
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R'\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<And>s0 s. R s0 s \<Longrightarrow> R' s0 s; \<And>s0 s. P s0 s \<Longrightarrow> P' s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: validIE_def rg_weaken_pre_rely)

lemmas rg_pre[wp_pre] =
  rg_weaken_pre
  rg_weaken_preE


subsection \<open>Setting up the precondition case splitter.\<close>

(* FIXME: this needs adjustment, case_prod Q is unlikely to unify *)
lemma wpc_helper_validI:
  "\<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace> \<Longrightarrow> wpc_helper (P, P', P'') (case_prod Q, Q', Q'') (\<lbrace>curry P\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>)"
  by (clarsimp simp: wpc_helper_def elim!: rg_pre)

lemma wpc_helper_validIE:
  "\<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> wpc_helper (P, P', P'') (case_prod Q, Q', Q'') (\<lbrace>curry P\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>,\<lbrace>E\<rbrace>)"
  by (clarsimp simp: wpc_helper_def elim!: rg_pre)

wpc_setup "\<lambda>m. \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>" wpc_helper_validI
wpc_setup "\<lambda>m. \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>,\<lbrace>E\<rbrace>" wpc_helper_validIE


subsection \<open>RG Logic Rules\<close>

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

lemma no_trace_last_st_tr:
  "\<lbrakk>no_trace f; (tr, res) \<in> f s\<rbrakk> \<Longrightarrow> last_st_tr tr s0 = s0"
  by (fastforce simp: no_trace_def)

lemma no_trace_rely_cond:
  "\<lbrakk>no_trace f; (tr, res) \<in> f s\<rbrakk> \<Longrightarrow> rely_cond R s0 tr"
  by (fastforce simp: no_trace_def rely_cond_def)

lemma validI_valid_no_trace_eq:
  "no_trace f \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> = (\<forall>s0. \<lbrace>P s0\<rbrace> f \<lbrace>\<lambda>v. Q v s0\<rbrace>)"
  apply (rule iffI)
   apply (fastforce simp: rely_def validI_def valid_def mres_def
                    dest: no_trace_emp)
  apply (clarsimp simp: rely_def validI_def valid_def mres_def no_trace_prefix_closed)
  apply (fastforce simp: eq_snd_iff dest: no_trace_emp)
  done

lemma validIE_validE_no_trace_eq:
  "no_trace f \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> = (\<forall>s0. \<lbrace>P s0\<rbrace> f \<lbrace>\<lambda>v. Q v s0\<rbrace>,\<lbrace>\<lambda>v. E v s0\<rbrace>)"
  unfolding validIE_def validE_def
  apply (clarsimp simp: validI_valid_no_trace_eq)
  done

(*FIXME MC: name*)
lemma validI_split:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<top>\<top>\<top>\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (auto simp: validI_def)

lemma validIE_split:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<top>\<top>\<top>\<rbrace>,\<lbrace>\<top>\<top>\<top>\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (auto simp: validIE_def validI_split)

lemma bind_twp[wp_split]:
  "\<lbrakk>\<And>r. \<lbrace>Q' r\<rbrace>,\<lbrace>R\<rbrace> g r \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f >>= (\<lambda>rv. g rv) \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
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

lemma bindE_twp[wp_split]:
  "\<lbrakk>\<And>r. \<lbrace>Q' r\<rbrace>,\<lbrace>R\<rbrace> g r \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f >>=E (\<lambda>r. g r) \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (simp add: bindE_def validIE_def)
  apply (erule bind_twp[rotated])
  apply (clarsimp simp: lift_def throwError_def split: sum.splits)
  apply (subst validI_valid_no_trace_eq)
   apply wpsimp+
  done

lemmas bind_twp_fwd = bind_twp[rotated]
lemmas bindE_twp_fwd = bindE_twp[rotated]

lemma rg_TrueI:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>_ _. \<top>\<rbrace> = prefix_closed f"
  by (simp add: validI_def)

lemma rgE_TrueI:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>_ _. \<top>\<rbrace>,\<lbrace>\<lambda>_ _. \<top>\<rbrace> = prefix_closed f"
  by (simp add: validIE_def rg_TrueI)

lemmas twp_post_taut = rg_TrueI[where P="\<top>\<top>", THEN iffD2]
lemmas twp_post_tautE = rgE_TrueI[where P="\<top>\<top>", THEN iffD2]
lemmas [elim!] = twp_post_taut twp_post_tautE

lemma rg_post_conj[intro]:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q and Q'\<rbrace>"
  by (fastforce simp: validI_def)

lemma rg_pre_disj[intro]:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P or P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (fastforce simp: validI_def pred_disj_def)

lemma rg_conj:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q and Q'\<rbrace>"
  unfolding validI_def by auto

lemma rg_pre_cont[simp]:
  "\<lbrace>\<bottom>\<bottom>\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> = prefix_closed f"
  by (simp add: validI_def)

lemma rg_FalseE[simp]:
  "\<lbrace>\<bottom>\<bottom>\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> = prefix_closed f"
  by (simp add: validI_def validIE_def)

lemma rg_post_imp:
  "\<lbrakk>\<And>v s0 s. Q' v s0 s \<Longrightarrow> Q v s0 s; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (simp add: validI_def)

lemma rg_post_impE:
  "\<lbrakk>\<And>v s0 s. Q' v s0 s \<Longrightarrow> Q v s0 s; \<And>v s0 s. E' v s0 s \<Longrightarrow> E v s0 s; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,\<lbrace>E'\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (clarsimp simp: validIE_def2 split: sum.splits)

lemma rg_post_imp_dc:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> a \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q'\<rbrace>; \<And>s0 s. Q' s0 s \<Longrightarrow> Q s0 s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> a \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>"
  by (fastforce simp: validIE_def validI_def split: sum.splits)

lemma rg_post_imp_dc2:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> a \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q'\<rbrace>; \<And>s0 s. Q' s0 s \<Longrightarrow> Q s0 s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> a \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>,-"
  by (fastforce simp: validIE_def validI_def split: sum.splits)

lemma rg_post_imp_dc2E:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> a \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q'\<rbrace>; \<And>s0 s. Q' s0 s \<Longrightarrow> Q s0 s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> a \<lbrace>G\<rbrace>,-,\<lbrace>\<lambda>_. Q\<rbrace>"
  by (fastforce simp: validIE_def validI_def split: sum.splits)

lemma rg_guar_imp:
  "\<lbrakk>\<And>s0 s. G' s0 s \<Longrightarrow> G s0 s; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G'\<rbrace>,\<lbrace>Q\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (force simp: validI_def guar_cond_def)

lemma rg_guar_impE:
  "\<lbrakk>\<And>s0 s. G' s0 s \<Longrightarrow> G s0 s; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G'\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (clarsimp simp: validIE_def elim!: rg_guar_imp)

lemmas rg_strengthen_post = rg_post_imp[rotated]
lemmas rg_strengthen_postE = rg_post_impE[rotated 2]
lemmas rg_strengthen_guar = rg_guar_imp[rotated]
lemmas rg_strengthen_guarE = rg_guar_impE[rotated]

lemma rg_conjD1:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0. Q rv s0 and Q' rv s0\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. Q rv\<rbrace>"
  unfolding validI_def by auto

lemma rg_conjD2:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0. Q rv s0 and Q' rv s0\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. Q' rv\<rbrace>"
  unfolding validI_def by auto

lemma rg_post_disjI1:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. Q rv\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0. Q rv s0 or Q' rv s0\<rbrace>"
  unfolding validI_def by auto

lemma rg_post_disjI2:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. Q' rv\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0. Q rv s0 or Q' rv s0\<rbrace>"
  unfolding validI_def by auto

lemma use_validI':
  "\<lbrakk>(tr, Result (rv, s')) \<in> rely f R s0 s; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; P s0 s; s0' = last_st_tr tr s0\<rbrakk>
   \<Longrightarrow> Q rv s0' s'"
  unfolding validI_def by auto

lemmas use_validI = use_validI'[OF _ _ _ refl]

lemmas post_by_rg = use_validI[rotated]

lemma use_validI_guar:
  "\<lbrakk>(tr, res) \<in> rely f R s0 s; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; P s0 s\<rbrakk>
   \<Longrightarrow> guar_cond G s0 tr"
  unfolding validI_def by auto

lemmas guar_by_rg = use_validI_guar[rotated]

lemma in_inv_by_rgD:
  "\<lbrakk>\<And>P. f \<lbrace>R\<rbrace>,-,\<lbrace>P\<rbrace>; (tr, Result (rv, s')) \<in> rely f R s0 s\<rbrakk> \<Longrightarrow> s' = s"
  unfolding validI_def
  apply (drule meta_spec[where x="\<lambda>_. (=) s"])
  apply blast
  done

lemma last_st_in_inv_by_rgD:
  "\<lbrakk>\<And>P. f \<lbrace>R\<rbrace>,-,\<lbrace>P\<rbrace>; (tr, Result (rv, s')) \<in> rely f R s0 s\<rbrakk> \<Longrightarrow> last_st_tr tr s0 = s0"
  unfolding validI_def
  apply (drule meta_spec[where x="\<lambda>s0' _. s0' = s0"])
  apply blast
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
  "\<lbrakk>(tr, res) \<in> f s; prefix_closed f\<rbrakk> \<Longrightarrow> \<exists>res'. (drop n tr, res') \<in> f s"
proof (induct n arbitrary: res)
  case 0 then show ?case by auto
next
  case (Suc n)
  have drop_1: "(tr, res) \<in> f s \<Longrightarrow> \<exists>res'. (drop 1 tr, res') \<in> f s" for tr res
    by (cases tr; fastforce dest: prefix_closedD[rotated] intro: Suc)
  show ?case
    using Suc.hyps[OF Suc.prems]
    by (metis drop_1[simplified] drop_drop add_0 add_Suc)
qed

lemma validI_GD_drop:
  "\<lbrakk>\<lbrace>P\<rbrace>, \<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>, \<lbrace>Q\<rbrace>; P s0 s; (tr, res) \<in> f s;
     rely_cond R s0 (drop n tr)\<rbrakk>
   \<Longrightarrow> guar_cond G s0 (drop n tr)"
  apply (drule prefix_closed_drop[where n=n], erule validI_prefix_closed)
  apply (auto dest: validI_GD)
  done

lemma rely_cond_drop:
  "rely_cond R s0 xs \<Longrightarrow> rely_cond R s0 (drop n xs)"
  using rely_cond_append[where xs="take n xs" and ys="drop n xs"]
  by simp

lemma rely_cond_is_drop:
  "\<lbrakk>rely_cond R s0 xs; (ys = drop (length xs - length ys) xs)\<rbrakk>
   \<Longrightarrow> rely_cond R s0 ys"
  by (metis rely_cond_drop)

lemma bounded_rev_nat_induct:
  "\<lbrakk>(\<And>n. N \<le> n \<Longrightarrow> P n); \<And>n. \<lbrakk>n < N; P (Suc n)\<rbrakk> \<Longrightarrow> P n\<rbrakk>
   \<Longrightarrow> P n"
  by (induct diff\<equiv>"N - n" arbitrary: n; simp)

lemma drop_n_induct:
  "\<lbrakk>P []; \<And>n. \<lbrakk>n < length xs; P (drop (Suc n) xs)\<rbrakk> \<Longrightarrow> P (drop n xs)\<rbrakk>
   \<Longrightarrow> P (drop n xs)"
  by (induct len\<equiv>"length (drop n xs)" arbitrary: n xs; simp)

lemma guar_cond_Cons_eq:
  "guar_cond R s0 (x # xs)
   = (guar_cond R s0 xs \<and> (fst x \<noteq> Env \<longrightarrow> R (last_st_tr xs s0) (snd x)))"
  by (cases "fst x"; simp add: guar_cond_def trace_steps_append conj_comms)

lemma guar_cond_Cons:
  "\<lbrakk>guar_cond R s0 xs; fst x \<noteq> Env \<longrightarrow> R (last_st_tr xs s0) (snd x)\<rbrakk>
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
  "\<lbrakk>guar_cond R s0 (drop (Suc n) xs);
    fst (xs ! n) \<noteq> Env \<longrightarrow> R (last_st_tr (drop (Suc n) xs) s0) (snd (xs ! n))\<rbrakk>
   \<Longrightarrow> guar_cond R s0 (drop n xs)"
  by (cases "n < length xs"; simp add: guar_cond_drop_Suc_eq)

lemma rely_cond_Cons_eq:
  "rely_cond R s0 (x # xs)
   = (rely_cond R s0 xs \<and> (fst x = Env \<longrightarrow> R (last_st_tr xs s0) (snd x)))"
  by (simp add: rely_cond_def trace_steps_append conj_comms)

lemma rely_cond_Cons:
  "\<lbrakk>rely_cond R s0 xs; fst x = Env \<longrightarrow> R (last_st_tr xs s0) (snd x)\<rbrakk>
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
  "\<lbrakk>rely_cond R s0 (drop (Suc n) xs);
    fst (xs ! n) = Env \<longrightarrow> R (last_st_tr (drop (Suc n) xs) s0) (snd (xs ! n))\<rbrakk>
   \<Longrightarrow> rely_cond R s0 (drop n xs)"
  by (cases "n < length xs"; simp add: rely_cond_drop_Suc_eq)

lemma last_st_tr_map_zip_hd:
  "\<lbrakk>length flags = length tr; tr \<noteq> [] \<longrightarrow> snd (f (hd flags, hd tr)) = snd (hd tr)\<rbrakk>
   \<Longrightarrow> last_st_tr (map f (zip flags tr)) = last_st_tr tr"
  apply (cases tr; simp)
  apply (cases flags; simp)
  apply (simp add: fun_eq_iff)
  done

lemma last_st_tr_drop_map_zip_hd:
  "\<lbrakk>length flags = length tr;
    n < length tr \<longrightarrow> snd (f (flags ! n, tr ! n)) = snd (tr ! n)\<rbrakk>
   \<Longrightarrow> last_st_tr (drop n (map f (zip flags tr))) = last_st_tr (drop n tr)"
  apply (simp add: drop_map drop_zip)
  apply (rule last_st_tr_map_zip_hd; clarsimp)
  apply (simp add: hd_drop_conv_nth)
  done

lemma last_st_tr_map_zip:
  "\<lbrakk>length flags = length tr; \<forall>fl tmid s. snd (f (fl, (tmid, s))) = s\<rbrakk>
   \<Longrightarrow> last_st_tr (map f (zip flags tr)) = last_st_tr tr"
  apply (erule last_st_tr_map_zip_hd)
  apply (clarsimp simp: neq_Nil_conv)
  done

lemma parallel_rely_induct:
  assumes preds: "(tr, v) \<in> parallel f g s" "Pf s0 s" "Pg s0 s"
  and validI: "\<lbrace>Pf\<rbrace>,\<lbrace>Rf\<rbrace> f' \<lbrace>Gf\<rbrace>,\<lbrace>Qf\<rbrace>"
     "\<lbrace>Pg\<rbrace>,\<lbrace>Rg\<rbrace> g' \<lbrace>Gg\<rbrace>,\<lbrace>Qg\<rbrace>"
     "f s \<subseteq> f' s" "g s \<subseteq> g' s"
  and compat: "R \<le> Rf" "R \<le> Rg" "Gf \<le> G" "Gg \<le> G" "Gf \<le> Rg" "Gg \<le> Rf"
  and rely: "rely_cond R s0 (drop n tr)"
  shows
    "\<exists>tr_f tr_g. (tr_f, v) \<in> f s \<and> (tr_g, v) \<in> g s
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
    apply (drule meta_mp, erule rely_cond_is_drop, simp)
    apply clarsimp
    apply (erule meta_allE, drule meta_mp, assumption)+
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
  and compat: "R \<le> Rf" "R \<le> Rg" "Gf \<le> G" "Gg \<le> G" "Gf \<le> Rg" "Gg \<le> Rf"
  shows "\<lbrace>Pf and Pg\<rbrace>,\<lbrace>R\<rbrace> parallel f g \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. Qf rv and Qg rv\<rbrace>"
  apply (clarsimp simp: validI_def rely_def pred_conj_def
                        prefix_closed_parallel validI[THEN validI_prefix_closed])
  apply (drule(3) parallel_rely_induct0[OF _ _ _ validI order_refl order_refl compat])
  apply clarsimp
  apply (drule(2) validI[THEN validI_rvD])+
  apply (simp add: last_st_tr_def)
  done

lemma rely_prim[simp]:
  "rely (\<lambda>s. insert (v s) (f s)) R s0 = (\<lambda>s. {x. x = v s \<and> rely_cond R s0 (fst x)} \<union> (rely f R s0 s))"
  "rely (\<lambda>s. {}) R s0 = (\<lambda>_. {})"
  "rely (\<lambda>s. (f s) \<union> (g s)) R s0 = (\<lambda>s. (rely f R s0 s) \<union> (rely g R s0 s))"
  "rely (\<lambda>s. if C s then f s else g s) R s0 = (\<lambda>s. if C s then rely f R s0 s else rely g R s0 s)"
  by (auto simp: rely_def prod_eq_iff split: if_splits)

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
  apply (auto simp: gr0_conv_Suc intro: exI[where x=0])
  done

lemma put_trace_twp[wp]:
  "\<lbrace>\<lambda>s0 s. (\<forall>n. rely_cond R s0 (drop n xs) \<longrightarrow> guar_cond G s0 (drop n xs))
     \<and> (rely_cond R s0 xs \<longrightarrow> Q () (last_st_tr xs s0) s)\<rbrace>,\<lbrace>R\<rbrace>
   put_trace xs
   \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (clarsimp simp: validI_def rely_def)
  apply (drule put_trace_res)
  apply (clarsimp; clarsimp split: nat.split_asm)
  done

lemmas put_trace_elem_twp = put_trace_twp[where xs="[x]" for x, simplified]

lemma rely_cond_rtranclp:
  "rely_cond R s (map (Pair Env) xs) \<Longrightarrow> rtranclp R s (last_st_tr (map (Pair Env) xs) s)"
  apply (induct xs arbitrary: s rule: rev_induct)
   apply simp
  apply (clarsimp simp add: rely_cond_def)
  apply (erule converse_rtranclp_into_rtranclp)
  apply simp
  done


subsection \<open>Misc\<close>

lemma rg_gen_asm:
  "\<lbrakk>P \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<not> P \<Longrightarrow> prefix_closed f\<rbrakk> \<Longrightarrow> \<lbrace>P' and (\<lambda>_ _. P)\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (auto simp: validI_def)

lemmas rg_gen_asm_single = rg_gen_asm[where P'="\<top>\<top>", simplified pred_conj_def simp_thms]

lemma rg_gen_asm_lk:
  "\<lbrakk>P \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<not> P \<Longrightarrow> prefix_closed f\<rbrakk> \<Longrightarrow> \<lbrace>(\<lambda>_ _. P) and P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (auto simp: validI_def)

\<comment> \<open>Useful for forward reasoning, when P is known.
    The first version allows weakening the precondition.\<close>
lemma rg_gen_asm_spec':
  "\<lbrakk>\<And>s0 s. P s0 s \<Longrightarrow> S \<and> P' s0 s; S \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<not> S \<Longrightarrow> prefix_closed f\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (auto 6 2 simp: validI_def)

lemma rg_gen_asm_spec:
  "\<lbrakk>\<And>s0 s. P s0 s \<Longrightarrow> S; S \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<not> S \<Longrightarrow> prefix_closed f\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (rule rg_gen_asm_spec'[where S=S and P'=P]) simp

lemma rg_conjI:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<and> Q' rv s0 s\<rbrace>"
  unfolding validI_def by auto

lemma rg_disjI1:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<or> Q' rv s0 s\<rbrace>"
  unfolding validI_def by blast

lemma rg_disjI2:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<or> Q' rv s0 s\<rbrace>"
  unfolding validI_def by blast

lemma rg_assume_pre:
  "\<lbrakk>\<And>s0 s. P s0 s \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; prefix_closed f\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (auto simp: validI_def)

lemma rg_assume_preE:
  "\<lbrakk>\<And>s0 s. P s0 s \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; prefix_closed f\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (auto simp: validI_def validIE_def)

lemma rg_allI:
  "(\<And>x. \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q x\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<forall>x. Q x rv s0 s\<rbrace>"
  by (simp add: validI_def)

lemma validE_allI:
  "(\<And>x. \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>r s. Q x r s\<rbrace>,\<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<forall>x. Q x rv s0 s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validI_def validIE_def split: sum.splits)

lemma rg_exI:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q x\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<exists>x. Q x rv s0 s\<rbrace>"
  by (simp add: validI_def) blast

lemma rg_impI:
  "P' \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv s0 s. P' \<longrightarrow> Q rv s0 s\<rbrace>"
  by (simp add: validI_def)

lemma validIE_impI:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>,\<lbrace>E\<rbrace>; P' \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P' \<longrightarrow> Q rv s0 s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validIE_def validI_def split: sum.splits)

lemma rg_case_option_wp:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f None \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<And>x. \<lbrace>P' x\<rbrace>,\<lbrace>R\<rbrace> f (Some x) \<lbrace>G\<rbrace>,\<lbrace>Q' x\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>case_option P P' v\<rbrace>,\<lbrace>R\<rbrace> f v \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. case v of None \<Rightarrow> Q rv | Some x \<Rightarrow> Q' x rv\<rbrace>"
  by (cases v) auto

lemma rg_case_option_wp2:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f None \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<And>x. \<lbrace>P' x\<rbrace>,\<lbrace>R\<rbrace> f (Some x) \<lbrace>G\<rbrace>,\<lbrace>Q' x\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>case_option P P' v\<rbrace>,\<lbrace>R\<rbrace> f v \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. case v of None \<Rightarrow> Q rv s0 s | Some x \<Rightarrow> Q' x rv s0 s\<rbrace>"
  by (cases v) auto

(* Might be useful for forward reasoning, when P is known. *)
lemma rg_when_cases:
  "\<lbrakk>\<And>s0 s. \<lbrakk>\<not>B; P s0 s\<rbrakk> \<Longrightarrow> Q s0 s; B \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> when B f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>"
  by (cases B; simp add: validI_def prefix_closed_def return_def)

lemma rg_vcg_prop:
  "prefix_closed f \<Longrightarrow> \<lbrace>\<lambda>s0 s. P\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>\<lambda>rv s0 s. P\<rbrace>"
  by (simp add: validI_def)


subsection \<open>@{const validI} and @{const validIE}, @{const validIE_R}, @{const validIE_E}\<close>

lemma validI_validIE:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>"
  by (rule rg_post_imp_dc)

lemma validI_validIE2:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q'\<rbrace>; \<And>s0 s. Q' s0 s \<Longrightarrow> Q s0 s; \<And>s0 s. Q' s0 s \<Longrightarrow> E s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>, \<lbrace>\<lambda>_. E\<rbrace>"
  unfolding validI_def validIE_def
  by (clarsimp split: sum.splits)

lemma validIE_validI:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>"
  unfolding validIE_def
  by fastforce

lemma validI_validIE_R:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>,-"
  by (rule rg_post_imp_dc2)

lemma validI_validIE_E:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,-,\<lbrace>\<lambda>_. Q\<rbrace>"
  by (rule rg_post_imp_dc2E)

lemma validIE_eq_validI:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. Q\<rbrace>,\<lbrace>\<lambda>rv. Q\<rbrace> = \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. Q\<rbrace>"
  by (simp add: validIE_def)


subsection \<open>@{const liftM}\<close>

(*FIXME: make proof nicer*)
lemma rg_liftM_subst:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> liftM f m \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> = \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>Q \<circ> f\<rbrace>"
  apply (clarsimp simp: validI_def)
  apply (rule conj_cong, clarsimp)
  apply (rule iff_allI)+
  apply (clarsimp simp: liftM_def bind_def' return_def image_def)
  apply safe
     apply (drule_tac x="map_tmres id f res" in spec)
     apply (case_tac res; clarsimp)
       apply (auto simp: rely_def split: tmres.splits)[3]
   apply (drule_tac x="map_tmres id f (Result (rv, s'))" in spec)
  apply (auto simp: rely_def split: tmres.splits)
  done

lemma rg_liftME_subst:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> liftME f m \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace> = \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>Q \<circ> f\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding validIE_def liftME_liftM rg_liftM_subst o_def
  by (fastforce intro!: arg_cong[where f="validI P R m G"] split: sum.splits)

lemma liftE_validIE[simp]:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> liftE f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> = \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (simp add: liftE_liftM validIE_def rg_liftM_subst o_def)


subsection \<open>Operator lifting/splitting\<close>

lemma rg_vcg_if_split:
  "\<lbrakk>P \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<not>P \<Longrightarrow> \<lbrace>P''\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (P \<longrightarrow> P' s0 s) \<and> (\<not>P \<longrightarrow> P'' s0 s)\<rbrace>,\<lbrace>R\<rbrace> if P then f else g \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by simp

lemma rg_vcg_if_splitE:
  "\<lbrakk>P \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<not>P \<Longrightarrow> \<lbrace>P''\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (P \<longrightarrow> P' s0 s) \<and> (\<not>P \<longrightarrow> P'' s0 s)\<rbrace>,\<lbrace>R\<rbrace> if P then f else g \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp

lemma rg_vcg_split_case_option:
  "\<lbrakk>\<And>x. x = None \<Longrightarrow> \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f x \<lbrace>G\<rbrace>,\<lbrace>Q x\<rbrace>; \<And>x y. x = Some y \<Longrightarrow> \<lbrace>P' x y\<rbrace>,\<lbrace>R\<rbrace> g x y \<lbrace>G\<rbrace>,\<lbrace>Q x\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (x = None \<longrightarrow> P x s0 s) \<and> (\<forall>y. x = Some y \<longrightarrow> P' x y s0 s)\<rbrace>,\<lbrace>R\<rbrace>
       case x of None \<Rightarrow> f x | Some y \<Rightarrow> g x y
       \<lbrace>G\<rbrace>,\<lbrace>Q x\<rbrace>"
  by (cases x; simp)

lemma rg_vcg_split_case_optionE:
  "\<lbrakk>\<And>x. x = None \<Longrightarrow> \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f x \<lbrace>G\<rbrace>,\<lbrace>Q x\<rbrace>,\<lbrace>E x\<rbrace>; \<And>x y. x = Some y \<Longrightarrow> \<lbrace>P' x y\<rbrace>,\<lbrace>R\<rbrace> g x y \<lbrace>G\<rbrace>,\<lbrace>Q x\<rbrace>,\<lbrace>E x\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (x = None \<longrightarrow> P x s0 s) \<and> (\<forall>y. x = Some y \<longrightarrow> P' x y s0 s)\<rbrace>,\<lbrace>R\<rbrace>
       case x of None \<Rightarrow> f x | Some y \<Rightarrow> g x y
       \<lbrace>G\<rbrace>,\<lbrace>Q x\<rbrace>,\<lbrace>E x\<rbrace>"
  by (cases x; simp)

lemma rg_vcg_split_case_sum:
  "\<lbrakk>\<And>x a. x = Inl a \<Longrightarrow> \<lbrace>P x a\<rbrace>,\<lbrace>R\<rbrace> f x a \<lbrace>G\<rbrace>,\<lbrace>Q x\<rbrace>; \<And>x b. x = Inr b \<Longrightarrow> \<lbrace>P' x b\<rbrace>,\<lbrace>R\<rbrace> g x b \<lbrace>G\<rbrace>,\<lbrace>Q x\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (\<forall>a. x = Inl a \<longrightarrow> P x a s0 s) \<and> (\<forall>b. x = Inr b \<longrightarrow> P' x b s0 s)\<rbrace>,\<lbrace>R\<rbrace>
       case x of Inl a \<Rightarrow> f x a | Inr b \<Rightarrow> g x b
       \<lbrace>G\<rbrace>, \<lbrace>Q x\<rbrace>"
  by (cases x; simp)

lemma bind_twp_nobind:
  "\<lbrakk>\<lbrace>B\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>C\<rbrace>; \<lbrace>A\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. B\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace>,\<lbrace>R\<rbrace> do f; g od \<lbrace>G\<rbrace>,\<lbrace>C\<rbrace>"
  by (erule bind_twp_fwd) clarsimp

lemma bindE_twp_nobind:
  "\<lbrakk>\<lbrace>B\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>C\<rbrace>, \<lbrace>E\<rbrace>; \<lbrace>A\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. B\<rbrace>, \<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace>,\<lbrace>R\<rbrace> doE f; g odE \<lbrace>G\<rbrace>,\<lbrace>C\<rbrace>, \<lbrace>E\<rbrace>"
  by (erule bindE_twp_fwd) clarsimp

lemmas bind_twp_skip = bind_twp[where Q=Q and Q'=Q for Q]

lemma rg_chain:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<And>s0 s. P' s0 s \<Longrightarrow> P s0 s; \<And>rv s0 s. Q rv s0 s \<Longrightarrow> S rv s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>"
  by (wp_pre, rule rg_post_imp)

lemma validIE_weaken: (* FIXME lib: eliminate in favour of rg_chainE *)
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> A \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,\<lbrace>E'\<rbrace>; \<And>s0 s. P s0 s \<Longrightarrow> P' s0 s; \<And>rv s0 s. Q' rv s0 s \<Longrightarrow> Q rv s0 s;
    \<And>rv s0 s. E' rv s0 s \<Longrightarrow> E rv s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> A \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by wp_pre (rule rg_post_impE)

lemmas rg_chainE = validIE_weaken

lemma rg_vcg_conj_lift:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. P s0 s \<and> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<and> Q' rv s0 s\<rbrace>"
  unfolding validI_def
  by fastforce

\<comment> \<open>A variant which works nicely with subgoals that do not contain schematics\<close>
lemmas rg_vcg_conj_lift_pre_fix = rg_vcg_conj_lift[where P=P and P'=P for P, simplified]

lemma rg_vcg_conj_liftE1:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,-; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P and P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<and> Q' rv s0 s\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding validI_def validIE_def
  by (fastforce simp: split_def split: sum.splits)

lemma rg_vcg_conj_liftE2:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,-,\<lbrace>E\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,\<lbrace>E'\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. P s0 s \<and> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,\<lbrace>\<lambda>rv s0 s. E rv s0 s \<and> E' rv s0 s\<rbrace>"
  unfolding validIE_def
  by (rule rg_post_imp[OF _ rg_vcg_conj_lift]; simp split: sum.splits)

lemma rg_vcg_conj_liftE_weaker:
  assumes "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes "\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace>"
  shows "\<lbrace>\<lambda>s0 s. P s0 s \<and> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<and> Q' rv s0 s\<rbrace>,\<lbrace>E\<rbrace>"
  apply (rule rg_pre)
    apply (fastforce intro: assms rg_vcg_conj_liftE1 validE_validE_R rg_post_impE)
   apply simp+
  done

lemma rg_vcg_disj_lift:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. P s0 s \<or> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<or> Q' rv s0 s\<rbrace>"
  unfolding validI_def
  by fastforce

lemma rg_vcg_disj_lift_R:
  assumes x: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,-"
  assumes y: "\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,-"
  shows      "\<lbrace>\<lambda>s0 s. P s0 s \<or> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<or> Q' rv s0 s\<rbrace>,-"
  using assms
  by (fastforce simp: validIE_def validI_def split: sum.splits)

lemma rg_vcg_const_Ball_lift:
  "\<lbrakk>\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>Q x\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<top>\<top>\<top>\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (\<forall>x\<in>S. P x s0 s) \<and> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<forall>x\<in>S. Q x rv s0 s\<rbrace>"
  by (fastforce simp: validI_def)

lemma rg_vcg_const_Ball_liftE:
  "\<lbrakk>\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>Q x\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,-, \<lbrace>E\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (\<forall>x\<in>S. P x s0 s) \<and> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<forall>x\<in>S. Q x rv s0 s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validIE_def validI_def split: sum.splits)

lemmas rg_vcg_const_Ball_liftE_R = rg_vcg_const_Ball_liftE[where E="\<top>\<top>\<top>", simplified validIE_eq_validI]

lemma rg_vcg_const_Ball_liftE_E:
 "\<lbrakk>\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f -,-,\<lbrace>E x\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<top>\<top>\<top>\<rbrace>\<rbrakk>
  \<Longrightarrow> \<lbrace>\<lambda>s0 s.(\<forall>x\<in>S. P x s0 s) \<and> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,-,\<lbrace>\<lambda>rv s0 s. \<forall>x \<in> S. E x rv s0 s\<rbrace>"
  unfolding validIE_def
  by (rule rg_strengthen_post)
     (fastforce intro!: rg_vcg_const_Ball_lift split: sum.splits)+

lemmas rg_vcg_const_Ball_lift_T = rg_vcg_const_Ball_lift[where G="\<top>\<top>" and P'="\<top>\<top>", simplified]
lemmas rg_vcg_const_Ball_liftE_R_T = rg_vcg_const_Ball_liftE_R[where G="\<top>\<top>" and P'="\<top>\<top>", simplified]
lemmas rg_vcg_const_Ball_liftE_E_T = rg_vcg_const_Ball_liftE_E[where G="\<top>\<top>" and P'="\<top>\<top>", simplified]

lemma rg_vcg_all_lift:
  "\<lbrakk>\<And>x. \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q x\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s0 s. \<forall>x. P x s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<forall>x. Q x rv s0 s\<rbrace>"
  by (fastforce simp: validI_def)

lemma rg_vcg_all_liftE_R:
  "\<lbrakk>\<And>x. \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q x\<rbrace>,\<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s0 s. \<forall>x. P x s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<forall>x. Q x rv s0 s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validIE_def validI_def split: sum.splits)

lemma rg_vcg_all_liftE_E:
  "\<lbrakk>\<And>x. \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E x\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s0 s. \<forall>x. P x s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<forall>x. E x rv s0 s\<rbrace>"
  by (fastforce simp: validIE_def validI_def split: sum.splits)

lemma rg_vcg_imp_lift:
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<not> P rv s0 s\<rbrace>; \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. P' s0 s \<or> Q' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P rv s0 s \<longrightarrow> Q rv s0 s\<rbrace>"
  by (simp only: imp_conv_disj) (rule rg_vcg_disj_lift)

lemma rg_vcg_imp_lift':
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<not> P rv s0 s\<rbrace>; \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. \<not> P' s0 s \<longrightarrow> Q' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P rv s0 s \<longrightarrow> Q rv s0 s\<rbrace>"
  by (wpsimp wp: rg_vcg_imp_lift)

lemma rg_vcg_imp_liftE:
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<not> P rv s0 s\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. P' s0 s \<or> Q' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P rv s0 s \<longrightarrow> Q rv s0 s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validIE_def validI_def split: sum.splits)

lemma rg_vcg_imp_liftE':
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<not> P rv s0 s\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. \<not> P' s0 s \<longrightarrow> Q' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P rv s0 s \<longrightarrow> Q rv s0 s\<rbrace>,\<lbrace>E\<rbrace>"
  by (wpsimp wp: rg_vcg_imp_liftE)

lemma rg_vcg_imp_liftE_E:
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<not> P rv s0 s\<rbrace>; \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. P' s0 s \<or> Q' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv s0 s. P rv s0 s \<longrightarrow> E rv s0 s\<rbrace>"
  by (auto simp add: validI_def validIE_def split: sum.splits)

lemma rg_vcg_imp_liftE_E':
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<not> P rv s0 s\<rbrace>; \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. \<not> P' s0 s \<longrightarrow> Q' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv s0 s. P rv s0 s \<longrightarrow> E rv s0 s\<rbrace>"
  by (wpsimp wp: rg_vcg_imp_liftE_E)

lemma rg_vcg_imp_conj_lift[wp_comb]:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<longrightarrow> Q' rv s0 s\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. (Q rv s0 s \<longrightarrow> Q'' rv s0 s) \<and> Q''' rv s0 s\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P and P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. (Q rv s0 s \<longrightarrow> Q' rv s0 s \<and> Q'' rv s0 s) \<and> Q''' rv s0 s\<rbrace>"
  by (auto simp: validI_def)

lemmas rg_vcg_imp_conj_lift'[wp_unsafe] = rg_vcg_imp_conj_lift[where Q'''="\<top>\<top>\<top>", simplified]

lemma rg_absorb_imp:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<and> Q' rv s0 s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<longrightarrow> Q' rv s0 s\<rbrace>"
  by (erule rg_post_imp[rotated], blast)

lemma rg_weaken_imp:
  "\<lbrakk>\<And>rv s0 s. Q rv s0 s \<Longrightarrow> Q' rv s0 s ;  \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q' rv s0 s \<longrightarrow> S rv s0 s\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<longrightarrow> S rv s0 s\<rbrace>"
  by (clarsimp simp: validI_def split_def)

lemma rg_vcg_const_imp_lift:
  "\<lbrakk>P \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>Q\<rbrace>; \<lbrace>P''\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<top>\<top>\<top>\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (P \<longrightarrow> P' s0 s) \<and> P'' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P \<longrightarrow> Q rv s0 s\<rbrace>"
  apply (cases P; simp)
  apply wp_pre
    apply (rule validI_split; assumption)
   apply clarsimp+
  done

lemma rg_vcg_const_imp_liftE_E:
  "\<lbrakk>P \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f -,-,\<lbrace>E\<rbrace>; \<lbrace>P''\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<top>\<top>\<top>\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (P \<longrightarrow> P' s0 s) \<and> P'' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,-,\<lbrace>\<lambda>rv s0 s. P \<longrightarrow> E rv s0 s\<rbrace>"
  unfolding validIE_def
  by (rule rg_strengthen_post)
     (fastforce intro!: rg_vcg_const_imp_lift split: sum.splits)+

lemma rg_vcg_const_imp_liftE_R:
  "\<lbrakk>P \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>Q\<rbrace>,-; \<lbrace>P''\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<top>\<top>\<top>\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (P \<longrightarrow> P' s0 s) \<and> P'' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P \<longrightarrow> Q rv s0 s\<rbrace>,-"
  unfolding validIE_def
  by (rule rg_strengthen_post)
     (fastforce intro!: rg_vcg_const_imp_lift split: sum.splits)+

(*FIXME MC: not clear whether we want these _T variants, and if we do whether they should be in the
          wp set along with the above rules*)
lemmas rg_vcg_const_imp_lift_T = rg_vcg_const_imp_lift[where G="\<top>\<top>" and P''="\<top>\<top>", simplified]
lemmas rg_vcg_const_imp_liftE_E_T = rg_vcg_const_imp_liftE_E[where G="\<top>\<top>" and P''="\<top>\<top>", simplified]
lemmas rg_vcg_const_imp_liftE_R_T = rg_vcg_const_imp_liftE_R[where G="\<top>\<top>" and P''="\<top>\<top>", simplified]

lemma rg_weak_lift_imp:
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>Q\<rbrace>; \<lbrace>P''\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<top>\<top>\<top>\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (P \<longrightarrow> P' s0 s) \<and> P'' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P \<longrightarrow> Q rv s0 s\<rbrace>"
  by (auto simp: validI_def split_def)

lemma rg_weak_lift_impE:
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P''\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<top>\<top>\<top>\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (P \<longrightarrow> P' s0 s) \<and> P'' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P \<longrightarrow> Q rv s0 s\<rbrace>,\<lbrace>\<lambda>rv s0 s. P \<longrightarrow> E rv s0 s\<rbrace>"
  unfolding validIE_def
  by (rule rg_strengthen_post)
     (fastforce intro!: rg_weak_lift_imp split: sum.splits)+

lemma rg_weak_lift_impE_R:
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f -,\<lbrace>Q\<rbrace>,-; \<lbrace>P''\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<top>\<top>\<top>\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. (P \<longrightarrow> P' s0 s) \<and> P'' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. P \<longrightarrow> Q rv s0 s\<rbrace>,-"
  unfolding validIE_def
  by (rule rg_strengthen_post)
     (fastforce intro!: rg_weak_lift_imp split: sum.splits)+

lemmas rg_weak_lift_imp_T = rg_weak_lift_imp[where G="\<top>\<top>" and P''="\<top>\<top>", simplified]
lemmas rg_weak_lift_impE_T = rg_weak_lift_impE[where G="\<top>\<top>" and P''="\<top>\<top>", simplified]
lemmas rg_weak_lift_impE_R_T = rg_weak_lift_impE_R[where G="\<top>\<top>" and P''="\<top>\<top>", simplified]

lemma rg_vcg_ex_lift:
  "\<lbrakk>\<And>x. \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q x\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s0 s. \<exists>x. P x s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<exists>x. Q x rv s0 s\<rbrace>"
  by (clarsimp simp: validI_def, blast)

lemma rg_vcg_ex_liftE:
  "\<lbrakk>\<And>x. \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q x\<rbrace>,\<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s0 s. \<exists>x. P x s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. \<exists>x. Q x rv s0 s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validIE_def validI_def split: sum.splits)

lemma rg_vcg_ex_liftE_E:
  "\<lbrakk>\<And>x. \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,-,\<lbrace>E x\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s0 s. \<exists>x. P x s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,-,\<lbrace>\<lambda>rv s0 s. \<exists>x. E x rv s0 s\<rbrace>"
  by (fastforce simp: validIE_def validI_def split: sum.splits)

lemma rg_vcg_ex_lift_R1:
  "\<lbrakk>\<And>x. \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,-\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s0 s. \<exists>x. P x s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,-"
  by (fastforce simp: validI_def validIE_def split: sum.splits)

lemma rg_liftP_ext:
  assumes "\<And>P x. m \<lbrace>R\<rbrace>,\<lbrace>G\<rbrace>,\<lbrace>\<lambda>s0 s. P s0 (f s x)\<rbrace>"
  shows "m \<lbrace>R\<rbrace>,\<lbrace>G\<rbrace>,\<lbrace>\<lambda>s0 s. P s0 (f s)\<rbrace>"
  unfolding validI_def
  apply (rule conjI, rule validI_prefix_closed[OF assms])
  apply clarsimp
  apply (rule conjI, clarsimp simp: rely_def, erule (2) validI_GD[OF assms])
  apply clarsimp
  apply (erule subst2[rotated 2, where P=P])
   apply (drule use_validI, rule assms, rule refl)
   apply simp
  apply (rule ext)
  apply (drule use_validI, rule assms, rule refl)
  apply simp
  done

(* for instantiations *)
lemma rg_triv:    "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace>f\<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace>f\<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>" .
lemma rg_trivE:   "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>" .
lemma rg_trivE_R: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,-" .
lemma rg_trivR_R: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,-,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,-,\<lbrace>E\<rbrace>" .

lemma rg_vcg_E_elim:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,-,\<lbrace>E\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,-\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s0 s. P s0 s \<and> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (rule rg_strengthen_postE[OF rg_vcg_conj_liftE2]) simp+

lemma rg_strengthen_post_R:
  "\<lbrakk> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,-; \<And>rv s0 s. Q' rv s0 s \<Longrightarrow> Q rv s0 s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,-"
  by (erule rg_post_impE)

lemma rg_strengthen_post_E:
  "\<lbrakk> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,-,\<lbrace>Q'\<rbrace>; \<And>rv s0 s. Q' rv s0 s \<Longrightarrow> Q rv s0 s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,-,\<lbrace>Q\<rbrace>"
  by (rule rg_post_impE)

lemma rg_post_comb_imp_conj:
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>; \<And>s0 s. P s0 s \<Longrightarrow> P' s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<and> Q' rv s0 s\<rbrace>"
  by (wpsimp wp: rg_vcg_conj_lift)

lemma rg_vcg_if_lift:
  "\<lbrace>R\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. (P \<longrightarrow> X rv s0 s) \<and> (\<not>P \<longrightarrow> Y rv s0 s)\<rbrace> \<Longrightarrow>
   \<lbrace>R\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. if P then X rv s0 s else Y rv s0 s\<rbrace>"

  "\<lbrace>R\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. (P \<longrightarrow> X rv s0 s) \<and> (\<not>P \<longrightarrow> Y rv s0 s)\<rbrace> \<Longrightarrow>
   \<lbrace>R\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. if P then X rv else Y rv\<rbrace>"
  by (auto simp: validI_def split_def)

lemma rg_vcg_split_lift[wp]:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f x y \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> case (x, y) of (a, b) \<Rightarrow> f a b \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by simp

named_theorems rg_vcg_op_lift
lemmas [rg_vcg_op_lift] =
  rg_vcg_const_imp_lift
  rg_vcg_const_imp_liftE_E
  rg_vcg_const_imp_liftE_R
  (* leaving out rg_vcg_conj_lift*, because that is built into wp *)
  rg_vcg_disj_lift
  rg_vcg_disj_lift_R
  rg_vcg_ex_lift
  rg_vcg_ex_liftE
  rg_vcg_ex_liftE_E
  rg_vcg_all_lift
  rg_vcg_all_liftE_R
  rg_vcg_all_liftE_E
  rg_vcg_const_Ball_lift
  rg_vcg_const_Ball_liftE
  rg_vcg_const_Ball_liftE_R
  rg_vcg_const_Ball_liftE_E
  rg_vcg_split_lift
  rg_vcg_if_lift
  rg_vcg_imp_lift'
  rg_vcg_imp_liftE'
  rg_vcg_imp_liftE_E'


subsection \<open>Weakest Precondition Rules\<close>

lemma valid_validI_wp:
  "\<lbrakk>no_trace f; \<And>s0. \<lbrace>P s0\<rbrace> f \<lbrace>\<lambda>v. Q v s0 \<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (clarsimp simp: validI_valid_no_trace_eq)

lemma validE_validIE_wp:
  "\<lbrakk>no_trace f; \<And>s0. \<lbrace>P s0\<rbrace> f \<lbrace>\<lambda>v. Q v s0 \<rbrace>,\<lbrace>\<lambda>v. E v s0\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (clarsimp simp: validIE_validE_no_trace_eq)

lemmas valid_validI_lifts[wp] = no_trace_terminal[THEN valid_validI_wp]

lemmas validE_validIE_lifts[wp] =
  no_trace_fail[THEN validE_validIE_wp] no_trace_returnOk[THEN validE_validIE_wp]
  no_trace_assertE[THEN validE_validIE_wp] no_trace_throwError[THEN validE_validIE_wp]
  no_trace_throw_opt[THEN validE_validIE_wp]

lemma liftE_twp:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> liftE f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp

lemma catch_twp:
  "\<lbrakk> \<And>x. \<lbrace>E x\<rbrace>,\<lbrace>R\<rbrace> handler x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> catch f handler \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  unfolding validI_def validIE_def
  apply (rule conjI, clarsimp)
  unfolding catch_def return_def rely_def bind_def
  apply (fastforce simp: rely_cond_append guar_cond_append
                 split: sum.splits tmres.splits)
  done

lemma handleE'_twp:
  "\<lbrakk> \<And>x. \<lbrace>F x\<rbrace>,\<lbrace>R\<rbrace> handler x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>F\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f <handle2> handler \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding validI_def validIE_def
  apply (rule conjI, clarsimp)
  unfolding handleE'_def return_def rely_def bind_def
  apply (fastforce simp: rely_cond_append guar_cond_append
                 split: sum.splits tmres.splits)
  done

lemma handleE_twp:
  assumes x: "\<And>x. \<lbrace>F x\<rbrace>,\<lbrace>R\<rbrace> handler x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes y: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>F\<rbrace>"
  shows      "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f <handle> handler \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: handleE_def handleE'_twp[OF x y])

lemma liftM_twp:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>Q \<circ> f\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> liftM f m \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (simp add: rg_liftM_subst)

lemma liftME_twp:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>Q \<circ> f\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> liftME f m \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: rg_liftME_subst)

lemma list_cases_twp:
  assumes a: "\<lbrace>P_A\<rbrace>,\<lbrace>R\<rbrace> a \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  assumes b: "\<And>x xs. ts = x#xs \<Longrightarrow> \<lbrace>P_B x xs\<rbrace>,\<lbrace>R\<rbrace> b x xs \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  shows "\<lbrace>case_list P_A P_B ts\<rbrace>,\<lbrace>R\<rbrace> case ts of [] \<Rightarrow> a | x # xs \<Rightarrow> b x xs \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (cases ts, auto simp: a b)

lemma rg_vcg_handle_elseE:
  "\<lbrakk> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,\<lbrace>E'\<rbrace>; \<And>e. \<lbrace>E' e\<rbrace>,\<lbrace>R\<rbrace> g e \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<And>x. \<lbrace>Q' x\<rbrace>,\<lbrace>R\<rbrace> h x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f <handle> g <else> h \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding handle_elseE_def validIE_def
  by (wpsimp wp: bind_twp_fwd | assumption | rule conjI)+

lemma alternative_twp:
  assumes x: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f' \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  shows      "\<lbrace>P and P'\<rbrace>,\<lbrace>R\<rbrace> f \<sqinter> f' \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  unfolding validI_def
  apply (rule conjI, fastforce simp: validI_prefix_closed[OF x] validI_prefix_closed[OF y])
  by (fastforce simp: alternative_def post_by_rg[OF x] post_by_rg[OF y] guar_by_rg[OF x] guar_by_rg[OF y])

lemma alternativeE_twp:
  assumes "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes "\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f' \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  shows   "\<lbrace>P and P'\<rbrace>,\<lbrace>R\<rbrace> f \<sqinter> f' \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding validIE_def
  by (wpsimp wp: assms alternative_twp | fold validIE_def)+

lemma condition_twp:
  "\<lbrakk> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> A \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> B \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. if C s then P s0 s else P' s0 s\<rbrace>,\<lbrace>R\<rbrace> condition C A B \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (auto simp: condition_def validI_def prefix_closed_def)

lemma conditionE_twp:
  "\<lbrakk> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> A \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> B \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s0 s. if C s then P s0 s else P' s0 s\<rbrace>,\<lbrace>R\<rbrace> condition C A B \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (clarsimp simp: validIE_def condition_twp)

lemma when_twp[wp_split]:
  "\<lbrakk> P \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>if P then P' else Q ()\<rbrace>,\<lbrace>R\<rbrace> when P f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  unfolding when_def by wpsimp

lemma unless_twp[wp_split]:
  "(\<not>P \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>if P then Q () else P'\<rbrace>,\<lbrace>R\<rbrace> unless P f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  unfolding unless_def by wpsimp (simp split: if_splits)+

lemma whenE_twp:
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>if P then P' else Q ()\<rbrace>,\<lbrace>R\<rbrace> whenE P f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding whenE_def by wpsimp

lemma unlessE_twp:
  "(\<not> P \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>if P then Q () else P'\<rbrace>,\<lbrace>R\<rbrace> unlessE P f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding unlessE_def by wpsimp

lemma maybeM_twp:
  "(\<And>x. y = Some x \<Longrightarrow> \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> m x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>) \<Longrightarrow>
   \<lbrace>\<lambda>s0 s. (\<forall>x. y = Some x \<longrightarrow> P x s0 s) \<and> (y = None \<longrightarrow> Q () s0 s)\<rbrace>,\<lbrace>R\<rbrace> maybeM m y \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  unfolding maybeM_def by wpsimp (simp split: if_splits)+

lemma notM_twp:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>\<lambda>c. Q (\<not> c)\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> notM m \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  unfolding notM_def by wpsimp

lemma ifM_twp:
  assumes [wp]: "\<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>" "\<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>"
  assumes [wp]: "\<lbrace>A\<rbrace>,\<lbrace>R\<rbrace> P \<lbrace>G\<rbrace>,\<lbrace>\<lambda>c s0 s. c \<longrightarrow> Q s0 s\<rbrace>" "\<lbrace>B\<rbrace>,\<lbrace>R\<rbrace> P \<lbrace>G\<rbrace>,\<lbrace>\<lambda>c s0 s. \<not>c \<longrightarrow> Q' s0 s\<rbrace>"
  shows "\<lbrace>A and B\<rbrace>,\<lbrace>R\<rbrace> ifM P f g \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>"
  unfolding ifM_def
  by (wpsimp wp: rg_vcg_if_split rg_vcg_conj_lift)

lemma andM_twp:
  assumes [wp]: "\<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> B \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  assumes [wp]: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> A \<lbrace>G\<rbrace>,\<lbrace>\<lambda>c s0 s. c \<longrightarrow> Q' s0 s\<rbrace>" "\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> A \<lbrace>G\<rbrace>,\<lbrace>\<lambda>c s0 s. \<not> c \<longrightarrow> Q False s0 s\<rbrace>"
  shows "\<lbrace>P and P'\<rbrace>,\<lbrace>R\<rbrace> andM A B \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  unfolding andM_def by (wpsimp wp: ifM_twp)

lemma orM_twp:
  assumes [wp]: "\<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> B \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  assumes [wp]: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> A \<lbrace>G\<rbrace>,\<lbrace>\<lambda>c s0 s. c \<longrightarrow> Q True s0 s\<rbrace>" "\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> A \<lbrace>G\<rbrace>,\<lbrace>\<lambda>c s0 s. \<not> c \<longrightarrow> Q' s0 s\<rbrace>"
  shows "\<lbrace>P and P'\<rbrace>,\<lbrace>R\<rbrace> orM A B \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  unfolding orM_def by (wp ifM_twp)

lemma whenM_twp:
  assumes [wp]: "\<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>"
  assumes [wp]: "\<lbrace>A\<rbrace>,\<lbrace>R\<rbrace> P \<lbrace>G\<rbrace>,\<lbrace>\<lambda>c s0 s. c \<longrightarrow> Q s0 s\<rbrace>" "\<lbrace>B\<rbrace>,\<lbrace>R\<rbrace> P \<lbrace>G\<rbrace>,\<lbrace>\<lambda>c s0 s. \<not>c \<longrightarrow> S () s0 s\<rbrace>"
  shows "\<lbrace>A and B\<rbrace>,\<lbrace>R\<rbrace> whenM P f \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>"
  unfolding whenM_def by (wp ifM_twp)

lemma rg_K_bind[wp_split]:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> K_bind f x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by simp

lemma validE_K_bind[wp_split]:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> K_bind x f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp

lemma rg_fun_app_twp:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f' x \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f' $ x \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>"
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f $ x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp+

lemma case_option_twp:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> m x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> m' \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<rbrakk>\<Longrightarrow>
   \<lbrace>\<lambda>s0 s. (x = None \<longrightarrow> P' s0 s) \<and> (x \<noteq> None \<longrightarrow> P (the x) s0 s)\<rbrace>,\<lbrace>R\<rbrace> case_option m' m x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (cases x; simp)

lemma case_option_twpE:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace>,\<lbrace>R\<rbrace> m x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> m' \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s0 s. (x = None \<longrightarrow> P' s0 s) \<and> (x \<noteq> None \<longrightarrow> P (the x) s0 s)\<rbrace>,\<lbrace>R\<rbrace> case_option m' m x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (cases x; simp)

(* FIXME: make wp *)
lemma whenE_throwError_twp:
  "\<lbrace>\<lambda>s0 s. \<not>P \<longrightarrow> Q s0 s\<rbrace>,\<lbrace>R\<rbrace> whenE P (throwError e) \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>,-"
  by (simp add: whenE_def returnOk_def throwError_def return_def validIE_def validI_def prefix_closed_def)

(*FIXME MC: not used, worth updating for validI or just delete?
lemma select_throwError_twp:
  "\<lbrace>\<lambda>s0 s. \<forall>x\<in>S. Q x s0 s\<rbrace>,\<lbrace>R\<rbrace> select S >>= throwError \<lbrace>G\<rbrace>,-,\<lbrace>Q\<rbrace>"
  by (simp add: bind_def throwError_def return_def select_def validIE_def validI_def prefix_closed_def)*)

(*FIXME MC: explore adding a rely_preserves definition for the first part of this precondition*)
lemma env_steps_twp[wp]:
  "\<lbrace>\<lambda>s0 s. (\<forall>s'. R\<^sup>*\<^sup>* s0 s' \<longrightarrow> Q () s' s') \<and> Q () s0 s\<rbrace>,\<lbrace>R\<rbrace> env_steps \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (simp add: env_steps_def)
  apply wp
  apply (clarsimp simp: guar_cond_def trace_steps_rev_drop_nth rev_nth)
  apply (drule rely_cond_rtranclp)
  apply (clarsimp simp add: last_st_tr_def hd_append)
  done

lemma interference_twp[wp]:
  "\<lbrace>\<lambda>s0 s. (\<forall>s'. R\<^sup>*\<^sup>* s s' \<longrightarrow> Q () s' s') \<and> G s0 s\<rbrace>,\<lbrace>R\<rbrace> interference \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
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


subsection \<open>Setting up the @{method wp} method\<close>

(* Attempt to define triple_judgement to use valid_validI_wp as wp_comb rule.
   It doesn't work. It seems that wp_comb rules cannot take more than 1 assumption *)
lemma validI_is_triple:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>
   = triple_judgement (\<lambda>(s0,s). prefix_closed f \<longrightarrow> P s0 s) f
                      (\<lambda>(s0,s) f. prefix_closed f \<and> (\<forall>tr res. (tr, res) \<in> rely f R s0 s
                          \<longrightarrow> guar_cond G s0 tr
                              \<and> (\<forall>rv s'. res = Result (rv, s') \<longrightarrow> Q rv (last_st_tr tr s0) s')))"
  apply (simp add: triple_judgement_def validI_def )
  apply (cases "prefix_closed f"; fastforce)
  done

lemma validIE_is_triple:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>
   = triple_judgement (\<lambda>(s0,s). prefix_closed f \<longrightarrow> P s0 s) f
                      (\<lambda>(s0,s) f. prefix_closed f \<and> (\<forall>tr res. (tr, res) \<in> rely f R s0 s
                          \<longrightarrow> guar_cond G s0 tr
                              \<and> (\<forall>rv s'. res = Result (rv, s')
                                   \<longrightarrow> (case rv of Inr b \<Rightarrow> Q b (last_st_tr tr s0) s'
                                                 | Inl a \<Rightarrow> E a (last_st_tr tr s0) s'))))"
  by (fastforce simp: validIE_def2 triple_judgement_def)

lemmas rg_wp_combs = rg_vcg_conj_lift

lemmas rg_wp_combsE =
  rg_vcg_conj_liftE1
  rg_vcg_conj_liftE2
  rg_vcg_E_elim

lemmas rg_wp_state_combsE =
  validI_validIE_R
  rg_vcg_conj_liftE1[OF validI_validIE_R]
  rg_vcg_E_elim[OF validI_validIE_E]
  rg_vcg_conj_liftE2[OF validI_validIE_E]

lemmas rg_classic_wp_combs = rg_post_comb_imp_conj rg_weaken_pre rg_wp_combs
lemmas rg_classic_wp_combsE = rg_weaken_preE rg_wp_combsE

lemmas rg_classic_wp_state_combsE =
  rg_weaken_preE[OF validI_validIE]
  rg_wp_state_combsE

lemmas all_rg_classic_wp_combs =
  rg_classic_wp_state_combsE
  rg_classic_wp_combsE
  rg_classic_wp_combs

lemmas rg_wp_splits[wp_split] =
  bind_twp bindE_twp handleE'_twp handleE_twp
  catch_twp rg_vcg_if_split rg_vcg_if_splitE
  liftM_twp liftME_twp whenE_twp unlessE_twp
  validIE_validI

lemmas [wp_comb] = rg_wp_state_combsE rg_wp_combsE rg_wp_combs

(* rules towards the bottom will be matched first *)
lemmas [wp] = rg_vcg_prop
              twp_post_taut
              twp_post_tautE
              rg_fun_app_twp
              liftE_twp
              alternative_twp
              alternativeE_twp
              condition_twp
              conditionE_twp
              maybeM_twp notM_twp ifM_twp andM_twp orM_twp whenM_twp

lemmas [wp_trip] = validI_is_triple validIE_is_triple


subsection \<open>Simplifications on conjunction\<close>

lemma rg_post_eq:
  "\<lbrakk> Q = Q'; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by simp

lemma rg_post_eqE1:
  "\<lbrakk> Q = Q'; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp

lemma rg_post_eqE2:
  "\<lbrakk> E = E'; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp

lemma pred_conj_apply_elim':
  "(\<lambda>rv. Q rv and Q' rv) = (\<lambda>rv s0 s. Q rv s0 s \<and> Q' rv s0 s)"
  by (simp add: pred_conj_def)

lemma pred_conj_conj_elim':
  "(\<lambda>rv s0 s. (Q rv and Q' rv) s0 s \<and> Q'' rv s0 s) = (\<lambda>rv s0 s. Q rv s0 s \<and> Q' rv s0 s \<and> Q'' rv s0 s)"
  by simp

lemma conj_assoc_apply':
  "(\<lambda>rv s0 s. (Q rv s0 s \<and> Q' rv s0 s) \<and> Q'' rv s0 s) = (\<lambda>rv s0 s. Q rv s0 s \<and> Q' rv s0 s \<and> Q'' rv s0 s)"
  by simp

lemma all_elim':
  "(\<lambda>rv s0 s. \<forall>x. P rv s0 s) = P"
  by simp

lemma all_conj_elim':
  "(\<lambda>rv s0 s. (\<forall>x. P rv s0 s) \<and> Q rv s0 s) = (\<lambda>rv s0 s. P rv s0 s \<and> Q rv s0 s)"
  by simp

lemmas rg_vcg_rhs_simps =
  pred_conj_apply_elim' pred_conj_conj_elim' conj_assoc_apply' all_elim' all_conj_elim'

lemma if_apply_reductI:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> If P' (f x) (g x) \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> If P' f g x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (cases P'; simp)

lemma if_apply_reductIE:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> If P' (f x) (g x) \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> If P' f g x \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (cases P'; simp)

lemmas rg_wp_simps[wp_split] =
  rg_vcg_rhs_simps[THEN rg_post_eq] rg_vcg_rhs_simps[THEN rg_post_eqE1]
  rg_vcg_rhs_simps[THEN rg_post_eqE2]
  if_apply_reductI if_apply_reductIE TrueI

schematic_goal rg_if_apply_test:
  "\<lbrace>?Q\<rbrace>,\<lbrace>R\<rbrace> (if A then returnOk else K fail) x \<lbrace>G\<rbrace>,\<lbrace>P\<rbrace>,\<lbrace>E\<rbrace>"
  by wpsimp

lemma rg_elim_pred_conj:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<and> Q' rv s0 s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. Q rv and Q' rv\<rbrace>"
  by (unfold pred_conj_def)

lemma rg_elim_pred_conjE1:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<and> Q' rv s0 s\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. Q rv and Q' rv\<rbrace>,\<lbrace>E\<rbrace>"
  by (unfold pred_conj_def)

lemma rg_elim_pred_conjE2:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv s0 s. E rv s0 s \<and> E' rv s0 s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv. E rv and E' rv\<rbrace>"
  by (unfold pred_conj_def)

lemmas rg_wp_pred_conj_elims =
  rg_elim_pred_conj rg_elim_pred_conjE1 rg_elim_pred_conjE2


subsection \<open>Bundles\<close>

bundle no_rg_pre = rg_pre [wp_pre del]

bundle classic_twp_pre = rg_pre [wp_pre del]
    all_rg_classic_wp_combs[wp_comb del] all_rg_classic_wp_combs[wp_comb]


text \<open>Miscellaneous lemmas on rg quintuples\<close>

lemma rg_pre_cases:
  "\<lbrakk> \<lbrace>\<lambda>s0 s. C s0 s \<and> P s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>\<lambda>s0 s. \<not>C s0 s \<and> P' s0 s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>P and P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  unfolding validI_def by fastforce

lemma rg_vcg_mp:
  "\<lbrakk> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>r s0 s. Q r s0 s \<longrightarrow> Q' r s0 s\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>"
  by (auto simp: validI_def)

(* note about this precond stuff: rules get a chance to bind directly
   before any of their combined forms. As a result, these precondition
   implication rules are only used when needed. *)
lemma rg_add_post:
  "\<lbrakk> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>; \<And>s0 s. P s0 s \<Longrightarrow> P' s0 s; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q' rv s0 s \<longrightarrow> Q rv s0 s\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  unfolding validI_def by fastforce

lemma rg_gen_asmE:
  "\<lbrakk>P \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<not> P \<Longrightarrow> prefix_closed f\<rbrakk>
   \<Longrightarrow> \<lbrace>P' and (\<lambda>_ _. P)\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: validIE_def validI_def) blast

lemma rg_list_case:
  "\<lbrakk> \<lbrace>P1\<rbrace>,\<lbrace>R\<rbrace> f f1 \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<And>y ys. xs = y#ys \<Longrightarrow> \<lbrace>P2 y ys\<rbrace>,\<lbrace>R\<rbrace> f (f2 y ys) \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>case xs of [] \<Rightarrow> P1 | y#ys \<Rightarrow> P2 y ys\<rbrace>,\<lbrace>R\<rbrace> f (case xs of [] \<Rightarrow> f1 | y#ys \<Rightarrow> f2 y ys) \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (cases xs; simp)

lemma rg_use_eq:
  assumes "\<And>P. \<lbrace>\<lambda>s0 s. P (f s)\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_ s0 s. P (f s)\<rbrace>"
  assumes "\<And>f. \<lbrace>\<lambda>s0 s. P f s0 s\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_ s0 s. Q f s0 s\<rbrace>"
  shows "\<lbrace>\<lambda>s0 s. P (f s) s0 s\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_ s0 s. Q (f s) s0 s \<rbrace>"
  apply (rule rg_post_imp[where Q'="\<lambda>_ s0 s. \<exists>y. y = f s \<and> Q y s0 s"], simp)
  apply (wpsimp wp: rg_vcg_ex_lift assms)
  done

lemma rg_validE_pred_conj:
  "\<lbrakk> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q and Q'\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding validI_def validIE_def
  by (simp split: sum.splits)

lemma rg_validE_conj:
  "\<lbrakk> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q rv s0 s \<and> Q' rv s0 s\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding validI_def validIE_def
  by (simp split: sum.splits)

lemma rg_drop_imp:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q' rv s0 s \<longrightarrow> Q rv s0 s\<rbrace>"
  by (auto simp: validI_def)

lemma rg_drop_impE:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>r. Q\<rbrace>, \<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q' rv s0 s \<longrightarrow> Q s0 s\<rbrace>, \<lbrace>E\<rbrace>"
  by (simp add: validIE_weaken)

lemma rg_drop_impE_E:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>, \<lbrace>\<lambda>rv s0 s. E' rv s0 s \<longrightarrow> E rv s0 s\<rbrace>"
  by (auto simp: validIE_def validI_def split: sum.splits)

lemmas rg_drop_imps = rg_drop_imp rg_drop_impE rg_drop_impE_E

(*This is unsafe, but can be very useful when supplied as a comb rule.*)
lemma rg_drop_imp_conj[wp_unsafe]:
  "\<lbrakk> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>; \<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. (Q rv s0 s \<longrightarrow> Q'' rv s0 s) \<and> Q''' rv s0 s\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>P and P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. (Q rv s0 s \<longrightarrow> Q' rv s0 s \<and> Q'' rv s0 s) \<and> Q''' rv s0 s\<rbrace>"
  by (auto simp: validI_def)

lemmas rg_drop_imp_conj'[wp_unsafe] = rg_drop_imp_conj[where Q'''="\<top>\<top>\<top>", simplified]

lemma rg_vcg_set_pred_lift:
  assumes "\<And>P x. m \<lbrace>R\<rbrace>,\<lbrace>G\<rbrace>,\<lbrace> \<lambda>s0 s. P (f x s0 s) \<rbrace>"
  shows "m \<lbrace>R\<rbrace>,\<lbrace>G\<rbrace>,\<lbrace> \<lambda>s0 s. P {x. f x s0 s} \<rbrace>"
  using assms[where P="\<lambda>x . x"] assms[where P=Not]
  by (fastforce simp: validI_def elim!: subst[rotated, where P=P])

(*If there is a use case which requires a specific guarantee then this rule could be extended with
  an extra assumption and precondition.*)
lemma rg_vcg_set_pred_lift_mono:
  assumes f: "\<And>x. m \<lbrace>R\<rbrace>,-,\<lbrace> f x \<rbrace>"
  assumes mono: "\<And>A B. A \<subseteq> B \<Longrightarrow> P A \<Longrightarrow> P B"
  shows "m \<lbrace>R\<rbrace>,-,\<lbrace> \<lambda>s0 s. P {x. f x s0 s} \<rbrace>"
  by (fastforce simp: validI_def validI_prefix_closed[OF f] elim!: mono[rotated]
                dest: use_validI[OF _ f])

text \<open>If a function contains an @{term assert}, or equivalent, then it might be
      possible to strengthen the precondition of an already-proven rg quintuple
      @{text pos}, by additionally proving a side condition @{text neg}, that
      violating some condition causes failure. The stronger rg quintuple produced
      by this theorem allows the precondition to assume that the condition is
      satisfied.\<close>
lemma rg_strengthen_pre_via_assert_forward:
  assumes pos: "\<lbrace> P \<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace> Q \<rbrace>"
  assumes rel: "\<And>s0 s. S s0 s \<longrightarrow> P s0 s \<or> N s0 s"
  assumes neg: "\<lbrace> N \<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace> \<bottom>\<bottom>\<bottom> \<rbrace>"
  shows "\<lbrace> S \<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace> Q \<rbrace>"
  apply (rule rg_weaken_pre)
   apply (rule rg_strengthen_post)
    apply (rule rg_vcg_disj_lift[OF pos neg])
   by (auto simp: rel)

text \<open>Like @{thm rg_strengthen_pre_via_assert_forward}, strengthen a precondition
      by proving a side condition that the negation of that condition would cause
      failure. This version is intended for backward reasoning. Apply it to a goal to
      obtain a stronger precondition after proving the side condition.\<close>
lemma rg_strengthen_pre_via_assert_backward:
  assumes neg: "\<lbrace> \<lambda>s0 s. \<not> E s0 s \<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace> \<bottom>\<bottom>\<bottom> \<rbrace>"
  assumes pos: "\<lbrace> P and E \<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace> Q \<rbrace>"
  shows "\<lbrace> P \<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace> Q \<rbrace>"
  by (rule rg_strengthen_pre_via_assert_forward[OF pos _ neg], simp)


subsection \<open>Strongest postcondition rules\<close>

lemma get_tsp:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> get \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. s = rv \<and> P s0 s\<rbrace>"
  by (simp add: get_def validI_def prefix_closed_def)

lemma put_tsp:
  "\<lbrace>\<top>\<top>\<rbrace>,\<lbrace>R\<rbrace> put a \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_ s0 s. s = a\<rbrace>"
  by (simp add: put_def validI_def prefix_closed_def)

lemma return_tsp:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> return a \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. rv = a \<and> P s0 s\<rbrace>"
  by (simp add:return_def validI_def prefix_closed_def)

lemma rg_return_tsp: (* FIXME lib: eliminate *)
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> return x \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. P and (\<lambda>_ _. rv = x)\<rbrace>"
  by (simp add: validI_def return_def prefix_closed_def)

lemma assert_tsp:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> assert Q \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_ s0 s. P s0 s \<and> Q\<rbrace>"
  by (simp add: assert_def fail_def return_def validI_def prefix_closed_def)

lemma rg_gets_tsp:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> gets f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. rv = f s \<and> P s0 s\<rbrace>"
  by (simp add: validI_def simpler_gets_def prefix_closed_def)

lemma rg_returnOk_tsp:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> returnOk x \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv s0 s. rv = x \<and> P s0 s\<rbrace>, \<lbrace>Q\<rbrace>"
  by (simp add: validI_def validIE_def returnOk_def return_def prefix_closed_def)

\<comment> \<open>For forward reasoning in RG proofs, these lemmas allow us to step over the
    left-hand-side of monadic bind, while keeping the same precondition.\<close>

named_theorems forward_inv_step_rules

lemmas rg_forward_inv_step_nobind[forward_inv_step_rules] =
  bind_twp_nobind[where B=A and A=A for A, rotated]

lemmas bind_twp_fwd_skip[forward_inv_step_rules] =
  bind_twp_fwd[where Q'="\<lambda>_. P" and P=P for P]

lemmas rg_forward_inv_step_nobindE_valid[forward_inv_step_rules] =
  bindE_twp_nobind[where B=A and A=A and E="\<lambda>_. C" and C="\<lambda>_. C" for A C,
                        simplified validIE_eq_validI, rotated]

lemmas rg_forward_inv_step_valid[forward_inv_step_rules] =
  bindE_twp_fwd[where Q'="\<lambda>_. P" and P=P and E="\<lambda>_. Q" and Q="\<lambda>_. Q" for P Q,
                 simplified validIE_eq_validI]

lemmas rg_forward_inv_step_nobindE[forward_inv_step_rules] =
  bindE_twp_nobind[where B=A and A=A for A, rotated]

lemmas bindE_twp_fwd_skip[forward_inv_step_rules] =
  bindE_twp_fwd[where Q'="\<lambda>_. P" and P=P for P]

method forward_inv_step uses wp simp =
  rule forward_inv_step_rules, solves \<open>wpsimp wp: wp simp: simp\<close>


subsection \<open>FIXME MC: look at these lemmas and work out where they should go / what this section should be called\<close>

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
  "\<lbrakk>prefix_closed f; \<lbrace>P\<rbrace>,\<lbrace>R'\<rbrace> f \<lbrace>G'\<rbrace>,\<lbrace>Q\<rbrace>; R \<le> R'; G' \<le> G\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (subst validI_def, clarsimp)
  apply (clarsimp simp add: rely_def)
  apply (drule (2)  validI_D)
   apply (fastforce simp: rely_cond_def guar_cond_def)+
  done

lemmas validI_well_behaved = validI_well_behaved'[unfolded le_fun_def, simplified]

lemmas bind_promote_If =
  if_distrib[where f="\<lambda>f. bind f g" for g]
  if_distrib[where f="\<lambda>g. bind f g" for f]

lemma bind_promote_If2:
  "do x \<leftarrow> f; if P then g x else h x od
   = (if P then bind f g else bind f h)"
  by simp

lemma exec_put_trace[unfolded K_bind_def]:
  "(do put_trace xs; f od) s
   = (\<Union>n \<in> {n. 0 < n \<and> n \<le> length xs}. {(drop n xs, Incomplete)})
     \<union> ((\<lambda>(a, b). (a @ xs, b)) ` f s)"
  apply (simp add: put_trace_eq_drop bind_def)
  apply (safe; (clarsimp split: if_split_asm)?;
         fastforce intro: bexI[where x=0] rev_bexI)
  done

lemma UN_If_distrib:
  "(\<Union>x \<in> S. if P x then A x else B x)
   = ((\<Union>x \<in> S \<inter> {x. P x}. A x) \<union> (\<Union>x \<in> S \<inter> {x. \<not> P x}. B x))"
  by (fastforce split: if_split_asm)

lemma Await_redef:
  "Await P = do
     s1 \<leftarrow> select {s. P s};
     env_steps;
     s \<leftarrow> get;
     select (if P s then {()} else {})
   od"
  apply (simp add: Await_def env_steps_def bind_assoc)
  apply (cases "{s. P s} = {}")
   apply (simp add: select_def bind_def get_def)
  apply (rule ext)
  apply (simp add: exec_get select_bind_UN put_then_get_then)
  apply (simp add: bind_promote_If2 if_distribR if_distrib[where f=select])
  apply (simp add: exec_put_trace cong: if_cong)
  apply (simp add: put_def bind_def select_def cong: if_cong)
  apply (strengthen equalityI)
  apply clarsimp
  apply (strengthen exI[where x="s # xs" for s xs])
  apply (strengthen exI[where x="Suc n" for n])
  apply simp
  apply blast
  done

lemma eq_Me_neq_Env:
  "(x = Me) = (x \<noteq> Env)"
  by (cases x; simp)

lemma validI_invariant_imp:
  assumes v: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
    and P: "\<forall>s0 s. P s0 s \<longrightarrow> I s0"
    and R: "\<forall>s0 s. I s0 \<longrightarrow> R s0 s \<longrightarrow> I s"
    and G: "\<forall>s0 s. I s0 \<longrightarrow> G s0 s \<longrightarrow> I s"
  shows "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>\<lambda>s0 s. I s0 \<and> I s \<and> G s0 s\<rbrace>,\<lbrace>\<lambda>rv s0 s. I s0 \<and> Q rv s0 s\<rbrace>"
proof -
  { fix tr s0 i
    assume r: "rely_cond R s0 tr" and g: "guar_cond G s0 tr"
      and I: "I s0"
    hence imp: "\<forall>(_, s, s') \<in> trace_steps (rev tr) s0. I s \<longrightarrow> I s'"
      apply (clarsimp simp: guar_cond_def rely_cond_def)
      apply (drule(1) bspec)+
      apply (clarsimp simp: eq_Me_neq_Env)
      apply (metis R G)
      done
    hence "i < length tr \<longrightarrow> I (snd (rev tr ! i))"
      using I
      apply (induct i)
       apply (clarsimp simp: neq_Nil_conv[where xs="rev tr" for tr, simplified])
      apply clarsimp
      apply (drule bspec, fastforce simp add: trace_steps_nth)
      apply simp
      done
  }
  note I = this
  show ?thesis
    using v
    apply (clarsimp simp: validI_def rely_def imp_conjL)
    apply (drule spec2, drule(1) mp)+
    apply clarsimp
    apply (frule P[rule_format])
    apply (clarsimp simp: guar_cond_def trace_steps_nth I last_st_tr_def
                          hd_append last_rev[symmetric]
                          last_conv_nth rev_map)
    done
qed

lemma validI_guar_post_conj_lift:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G1\<rbrace>,\<lbrace>Q1\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G2\<rbrace>,\<lbrace>Q2\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>\<lambda>s0 s. G1 s0 s \<and> G2 s0 s\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q1 rv s0 s \<and> Q2 rv s0 s\<rbrace>"
  apply (frule validI_prefix_closed)
  apply (subst validI_def, clarsimp simp: rely_def)
  apply (drule(3) validI_D)+
  apply (auto simp: guar_cond_def)
  done

lemma validI_valid_wp:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>\<top>\<top>\<rbrace> f -,\<lbrace>\<lambda>rv _ s. Q rv s\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P s0\<rbrace> f \<lbrace>Q\<rbrace>"
  by (auto simp: rely_def validI_def valid_def mres_def)

lemma validI_triv_valid_eq:
  "prefix_closed f \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>\<top>\<top>\<rbrace> f -,\<lbrace>\<lambda>rv _ s. Q rv s\<rbrace> = (\<forall>s0. \<lbrace>\<lambda>s. P s0 s\<rbrace> f \<lbrace>Q\<rbrace>)"
  by (fastforce simp: rely_def validI_def valid_def mres_def image_def)

end