(*
 * Copyright 2024, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Predicates on option that map None to True/False, or more generally to top/bot.
   E.g. "none_top ((\<noteq>) 0) opt_ptr" or "none_top tcb_at p s".

   They are definitions, not abbreviations so that they don't participate in general
   option case splits (separate split rules are provided), and so that we can control
   simp/intro/elim setup a bit better. It should usually be unnecessary to unfold the
   definitions (e.g. see the all/ex rules + intro/dest/elim rules), but it is not
   harmful to do so.

   The main setup is for the general lattice case, followed by a section that spells
   out properties for the more common bool and function cases together with additional
   automation setup for these.
*)

theory None_Top_Bot
  imports Monads.Fun_Pred_Syntax
begin

definition none_top :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b::top" where
  "none_top \<equiv> case_option top"

definition none_bot :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b::bot" where
  "none_bot \<equiv> case_option bot"


section \<open>General lattice properties for @{const none_top}\<close>

lemma none_top_simps[simp]:
  "none_top f None = top"
  "none_top f (Some x) = f x"
  by (auto simp: none_top_def)

(* Mirrors option.splits *)
lemma none_top_split:
  "P (none_top f opt) = ((opt = None \<longrightarrow> P top) \<and> (\<forall>x. opt = Some x \<longrightarrow> P (f x)))"
  by (cases opt) auto

lemma none_top_split_asm:
  "P (none_top f opt) = (\<not> (opt = None \<and> \<not> P top \<or> (\<exists>x. opt = Some x \<and> \<not> P (f x))))"
  by (cases opt) auto

lemmas none_top_splits = none_top_split none_top_split_asm

lemma none_top_if:
  "none_top f opt = (if opt = None then top else f (the opt))"
  by (cases opt) auto

(* General version of none_top_bool_all below *)
lemma none_top_Inf:
  "none_top f opt = (Inf {f x |x. opt = Some x} :: 'a :: complete_lattice)"
  by (cases opt) auto

lemma none_top_top[simp]:
  "none_top top = top"
  by (rule ext) (simp split: none_top_splits)


section \<open>Bool/fun lemmas for @{const none_top}\<close>

lemma none_top_bool_all:
  "none_top f opt = (\<forall>x. opt = Some x \<longrightarrow> f x)"
  by (auto simp: none_top_Inf)

lemma none_top_bool_cases:
  "none_top f opt = (opt = None \<or> (\<exists>x. opt = Some x \<and> f x))"
  by (cases opt) auto

lemma none_top_boolI:
  "(\<And>x. opt = Some x \<Longrightarrow> f x) \<Longrightarrow> none_top f opt"
  by (simp add: none_top_bool_all)

lemma none_top_boolD:
  "none_top f opt \<Longrightarrow> opt = None \<or> (\<exists>x. opt = Some x \<and> f x)"
  by (cases opt) auto

lemma none_top_boolE:
  "\<lbrakk> none_top f opt; opt = None \<Longrightarrow> P; \<And>x. \<lbrakk> opt = Some x; f x \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (cases opt) auto

lemma none_top_False_bool_None[simp]:
  "none_top \<bottom> opt = (opt = None)"
  by (cases opt) auto

(* We don't usually use "bot" on bool -- only putting this here for completeness. *)
lemma none_top_bot_bool_None[intro!, simp]:
  "none_top bot opt = (opt = None)"
  by (cases opt) auto

lemma none_top_True[simp]:
  "none_top \<top> = \<top>"
  by (rule ext) (simp split: none_top_split)

lemma none_top_True_bool[intro!]:
  "none_top \<top> opt"
  by simp

lemma none_top_fun_all:
  "none_top f opt s = (\<forall>x. opt = Some x \<longrightarrow> f x s)"
  by (cases opt) auto

lemma none_top_fun_cases:
  "none_top f opt s = (opt = None \<or> (\<exists>x. opt = Some x \<and> f x s))"
  by (cases opt) auto

lemma none_top_funI:
  "(\<And>x. opt = Some x \<Longrightarrow> f x s) \<Longrightarrow> none_top f opt s"
  by (simp add: none_top_fun_all)

lemma none_top_funD:
  "none_top f opt s \<Longrightarrow> opt = None \<or> (\<exists>x. opt = Some x \<and> f x s)"
  by (cases opt) auto

lemma none_top_funE:
  "\<lbrakk> none_top f opt s; opt = None \<Longrightarrow> P; \<And>x. \<lbrakk> opt = Some x; f x s \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (cases opt) auto

lemma none_top_False_fun_None[simp]:
  "none_top \<bottom>\<bottom> opt s = (opt = None)"
  by (cases opt) auto

lemma none_top_True_True[simp]:
  "none_top \<top>\<top> = \<top>\<top>"
  by (rule ext) (simp split: none_top_split)

lemma none_top_True_fun[intro!]:
  "none_top \<top>\<top> opt s"
  by simp

section \<open>General lattice properties for @{const none_bot}\<close>

lemma none_bot_simps[simp]:
  "none_bot f None = bot"
  "none_bot f (Some x) = f x"
  by (auto simp: none_bot_def)

(* Mirrors option.splits *)
lemma none_bot_split:
  "P (none_bot f opt) = ((opt = None \<longrightarrow> P bot) \<and> (\<forall>x. opt = Some x \<longrightarrow> P (f x)))"
  by (cases opt) auto

lemma none_bot_split_asm:
  "P (none_bot f opt) = (\<not> (opt = None \<and> \<not> P bot \<or> (\<exists>x. opt = Some x \<and> \<not> P (f x))))"
  by (cases opt) auto

lemmas none_bot_splits = none_bot_split none_bot_split_asm

(* General version of none_bot_bool_ex below *)
lemma none_bot_Sup:
  "none_bot f opt = (Sup {f x |x. opt = Some x} :: 'a :: complete_lattice)"
  by (cases opt) auto

lemma none_bot_if:
  "none_bot f opt = (if opt = None then bot else f (the opt))"
  by (cases opt) auto

lemma none_bot_bot[simp]:
  "none_bot bot = bot"
  by (rule ext) (simp split: none_bot_splits)


section \<open>Bool/fun lemmas for @{const none_bot}\<close>

lemma none_bot_bool_ex:
  "none_bot f opt = (\<exists>x. opt = Some x \<and> f x)"
  by (auto simp: none_bot_Sup)

lemma none_bot_boolI:
  "\<exists>x. opt = Some x \<and> f x \<Longrightarrow> none_bot f opt"
  by (auto simp: none_bot_bool_ex)

lemma none_bot_boolD:
  "none_bot f opt \<Longrightarrow> \<exists>x. opt = Some x \<and> f x"
  by (cases opt) auto

lemma none_bot_boolE:
  "\<lbrakk> none_bot f opt; \<And>x. \<lbrakk> opt = Some x; f x \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (cases opt) auto

(* As for none_top_bot, it would be unusual to see "top" for bool. Only adding the lemma here for
   completeness *)
lemma none_bot_top_neq_None[simp]:
  "none_bot top opt = (opt \<noteq> None)"
  by (cases opt) auto

lemma none_bot_True_bool_neq_None[simp]:
  "none_bot \<top> opt = (opt \<noteq> None)"
  by (cases opt) auto

lemma none_bot_False_bool[simp]:
  "none_bot \<bottom> = \<bottom>"
  by (rule ext) (simp split: none_bot_split)

lemma none_bot_False_boolE[dest!]:
  "none_bot \<bottom> opt \<Longrightarrow> False"
  by simp

lemma none_bot_fun_ex:
  "none_bot f opt s = (\<exists>x. opt = Some x \<and> f x s)"
  by (cases opt) auto

lemma none_bot_funI:
  "\<exists>x. opt = Some x \<and> f x s \<Longrightarrow> none_bot f opt s"
  by (simp add: none_bot_fun_ex)

lemma none_bot_funD:
  "none_bot f opt s \<Longrightarrow> \<exists>x. opt = Some x \<and> f x s"
  by (cases opt) auto

lemma none_bot_funE:
  "\<lbrakk> none_bot f opt s; \<And>x. \<lbrakk> opt = Some x; f x s \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (cases opt) auto

lemma none_bot_True_fun_neq_None[simp]:
  "none_bot \<top>\<top> opt s = (opt \<noteq> None)"
  by (cases opt) auto

lemma none_bot_False_fun[simp]:
  "none_bot \<bottom>\<bottom> = \<bottom>\<bottom>"
  by (rule ext) (simp split: none_bot_split)

lemma none_bot_False_funE[dest!]:
  "none_bot \<bottom>\<bottom> opt s \<Longrightarrow> False"
  by simp

section \<open>Automation setup and short-hand names\<close>

lemmas none_topI[intro!] = none_top_boolI none_top_funI
lemmas none_topD = none_top_boolD none_top_funD
lemmas none_topE = none_top_boolE none_top_funE
lemmas none_top_all = none_top_bool_all none_top_fun_all
lemmas none_top_case = none_top_bool_cases none_top_fun_cases

lemmas none_botI = none_bot_boolI none_bot_funI
lemmas none_botD = none_bot_boolD none_bot_funD
lemmas none_botE[elim!] = none_bot_boolE none_bot_funE
lemmas none_bot_ex = none_bot_bool_ex none_bot_fun_ex

end