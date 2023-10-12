(*
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Syntax for using multi-argument functions as predicates, e.g "P and Q" where P and Q are
   functions to bool, taking one or more parameters. *)

chapter \<open>Function Predicate Syntax\<close>

theory Fun_Pred_Syntax
imports Main
begin

section \<open>Definitions\<close>

text \<open>
  Functions are already instances of Boolean algebras and provide all the standard laws one
  would like to have. Default simplifications are automatic. Search for @{const inf}/
  @{const sup}/@{const uminus} to find further laws and/or unfold via the definitions below.

  The abbreviations here provide special syntax for the function instance of Boolean
  algebras only, leaving other instances (such as @{typ bool}) untouched.\<close>

abbreviation pred_conj :: "('a \<Rightarrow> 'b::boolean_algebra) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "pred_conj \<equiv> inf"

abbreviation pred_disj :: "('a \<Rightarrow> 'b::boolean_algebra) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "pred_disj \<equiv> sup"

abbreviation pred_neg :: "('a \<Rightarrow> 'b::boolean_algebra) \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "pred_neg \<equiv> uminus"


text \<open>
  Lifted True/False: ideally, we'd map these to top/bot, but top/bot are constants and there are
  currently too many rules and tools that expect these conditions to beta-reduce and match against
  True/False directly.\<close>

abbreviation (input) pred_top :: "'a \<Rightarrow> bool" where
  "pred_top \<equiv> \<lambda>_. True"

abbreviation (input) pred_bot :: "'a \<Rightarrow> bool" where
  "pred_bot \<equiv> \<lambda>_. False"


text \<open>Version with two arguments for compatibility. Can hopefully be eliminated at some point.\<close>

abbreviation (input) pred_top2 :: "'a \<Rightarrow> 'b \<Rightarrow> bool" where
  "pred_top2 \<equiv> \<lambda>_ _. True"

abbreviation (input) pred_bot2 :: "'a \<Rightarrow> 'b \<Rightarrow> bool" where
  "pred_bot2 \<equiv> \<lambda>_ _. False"


section \<open>Syntax bundles\<close>

bundle fun_pred_syntax
begin
  (* infixl instead of infixr, because we want to split off conjuncts from the left *)
  notation pred_conj (infixl "and" 35)
  notation pred_disj (infixl "or" 30)
  notation pred_neg ("not _" [40] 40)
  notation pred_top ("\<top>")
  notation pred_bot ("\<bottom>")
  notation pred_top2 ("\<top>\<top>")
  notation pred_bot2 ("\<bottom>\<bottom>")
end

bundle no_fun_pred_syntax
begin
  no_notation pred_conj (infixl "and" 35)
  no_notation pred_disj (infixl "or" 30)
  no_notation pred_neg ("not _" [40] 40)
  no_notation pred_top ("\<top>")
  no_notation pred_bot ("\<bottom>")
  no_notation pred_top2 ("\<top>\<top>")
  no_notation pred_bot2 ("\<bottom>\<bottom>")
end

unbundle fun_pred_syntax


section \<open>Definitions specialised to @{typ bool} and @{text fun} instance of @{class boolean_algebra}\<close>

lemmas pred_conj_def =
  inf_fun_def[where 'b=bool, simplified]
  inf_fun_def[where f="f::'a \<Rightarrow> 'b::boolean_algebra" for f]

lemmas pred_disj_def =
  sup_fun_def[where 'b=bool, simplified]
  sup_fun_def[where f="f::'a \<Rightarrow> 'b::boolean_algebra" for f]

lemmas pred_neg_def =
  fun_Compl_def[where 'b=bool, simplified]
  fun_Compl_def[where A="A::'a \<Rightarrow> 'b::boolean_algebra" for A]

lemmas pred_top_def[simp] =
  top_fun_def[where 'b=bool, simplified] top_fun_def[where 'b="'b::boolean_algebra"]

lemmas pred_bot_def[simp] =
  bot_fun_def[where 'b=bool, simplified] bot_fun_def[where 'b="'b::boolean_algebra"]


section \<open>Other lemmas\<close>

text \<open>AC rewriting renamed and specialised, so we don't have to remember inf/sup\<close>

lemmas pred_conj_aci = inf_aci[where 'a="'a \<Rightarrow> 'b::boolean_algebra"]
lemmas pred_disj_aci = sup_aci[where 'a="'a \<Rightarrow> 'b::boolean_algebra"]


text \<open>Useful legacy names\<close>

lemmas pred_conjI = inf1I inf2I

lemmas pred_disjI1 = sup1I1[where 'a="'a \<Rightarrow> 'b::boolean_algebra"]
lemmas pred_disjI2 = sup1I2[where 'a="'a \<Rightarrow> 'b::boolean_algebra"]

lemmas pred_disj1CI[intro!] = sup1CI[where 'a="'a \<Rightarrow> 'b::boolean_algebra"]
lemmas pred_disj2CI = sup2CI[where 'a="'a \<Rightarrow> 'b::boolean_algebra"]

lemmas pred_conj_assoc = inf.assoc[where 'a="'a \<Rightarrow> 'b::boolean_algebra", symmetric]
lemmas pred_conj_comm = inf.commute[where 'a="'a \<Rightarrow> 'b::boolean_algebra"]

lemmas pred_disj_assoc = sup.assoc[where 'a="'a \<Rightarrow> 'b::boolean_algebra", symmetric]
lemmas pred_disj_comm = sup.commute[where 'a="'a \<Rightarrow> 'b::boolean_algebra"]


text \<open>Top/bot and function composition\<close>

lemma pred_top_comp[simp]:
  "\<top> \<circ> f = \<top>"
  by (simp add: comp_def)

lemma pred_bot_comp[simp]:
  "\<bottom> \<circ> f = \<bottom>"
  by (simp add: comp_def)


text \<open>
  We would get these for free if we could instantiate @{const pred_top}/@{const pred_bot} to
  @{const top}/@{const bot} directly:\<close>

lemmas pred_top_left_neutral[simp] =
  inf_top.left_neutral[where 'a="'a \<Rightarrow> bool", unfolded pred_top_def]

lemmas pred_top_right_neutral[simp] =
  inf_top.right_neutral[where 'a="'a \<Rightarrow> bool", unfolded pred_top_def]

lemmas pred_bot_left_neutral[simp] =
  sup_bot.left_neutral[where 'a="'a \<Rightarrow> bool", unfolded pred_bot_def]

lemmas pred_bot_right_neutral[simp] =
  sup_bot.right_neutral[where 'a="'a \<Rightarrow> bool", unfolded pred_bot_def]

lemmas pred_top_left[simp] =
  sup_top_left[where 'a="'a \<Rightarrow> bool", unfolded pred_top_def]

lemmas pred_top_right[simp] =
  sup_top_right[where 'a="'a \<Rightarrow> bool", unfolded pred_top_def]

lemmas pred_bot_left[simp] =
  inf_bot_left[where 'a="'a \<Rightarrow> bool", unfolded pred_bot_def]

lemmas pred_bot_right[simp] =
  inf_bot_right[where 'a="'a \<Rightarrow> bool", unfolded pred_bot_def]

lemmas pred_neg_top_eq[simp] =
  compl_top_eq[where 'a="'a \<Rightarrow> bool", unfolded pred_bot_def pred_top_def]

lemmas pred_neg_bot_eq[simp] =
  compl_bot_eq[where 'a="'a \<Rightarrow> bool", unfolded pred_bot_def pred_top_def]

(* no special setup for pred_top2/pred_bot2 at the moment, since we hope to eliminate these
   entirely in the future *)


subsection "Simplification Rules for Lifted And/Or"

lemma bipred_disj_op_eq[simp]:
  "reflp R \<Longrightarrow> ((=) or R) = R"
  "reflp R \<Longrightarrow> (R or (=)) = R"
  by (auto simp: reflp_def)

lemma bipred_le_true[simp]: "R \<le> \<top>\<top>"
  by clarsimp


section \<open>Examples\<close>

experiment
begin

(* Standard laws are available by default: *)
lemma "(P and P) = P" for P :: "'a \<Rightarrow> bool"
  by simp

(* Works for functions with multiple arguments: *)
lemma "(P and Q) = (Q and P)" for P :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  by (simp add: pred_conj_aci)

(* Unfolds automatically when applied: *)
lemma "(P and Q) s t = (P s t \<and> Q s t)"
  by simp

(* pred_top and pred_bot work for only one argument currently: *)
lemma "(P and not P) = \<bottom>" for P :: "'a \<Rightarrow> bool"
  by simp

(* You can still use them with more arguments and sometimes get simplification: *)
lemma "(P and not P) = (\<lambda>_ _. \<bottom>)" for P :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
  by simp

(* But sometimes you need to fold pred_top_def/pred_bot_def for rules on top/bot to fire: *)
lemma "(P and (\<lambda>_ _. \<bottom>)) = (\<lambda>_ _. \<bottom>)"
  by (simp flip: pred_bot_def)

lemma "(P and \<bottom>\<bottom>) = \<bottom>\<bottom>"
  by (simp flip: pred_bot_def)

end

end
