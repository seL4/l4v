(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Weakest Preconditions\<close>

theory WP
imports
  WP_Pre
  WPFix
  Eisbach_Tools.Apply_Debug
  ML_Utils.ML_Utils
begin

definition
  triple_judgement :: "('a \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
where
 "triple_judgement pre body property = (\<forall>s. pre s \<longrightarrow> property s body)"

definition
  postcondition :: "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> ('r \<times> 's) set)
            \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
where
 "postcondition P f = (\<lambda>a b. \<forall>(rv, s) \<in> f a b. P rv s)"

definition
  postconditions :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
where
 "postconditions P Q = (\<lambda>a b. P a b \<and> Q a b)"

lemma conj_TrueI: "P \<Longrightarrow> True \<and> P" by simp
lemma conj_TrueI2: "P \<Longrightarrow> P \<and> True" by simp

ML_file "WP-method.ML"

declare [[wp_trace = false, wp_trace_instantiation = false]]

setup WeakestPre.setup

method_setup wp = \<open>WeakestPre.apply_wp_args\<close>
  "applies weakest precondition rules"

end
