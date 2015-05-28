(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory WP
imports "~~/src/HOL/Main"
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

ML_file "WP-method.ML"

declare [[wp_warn_unused = false]]

setup WeakestPre.setup

method_setup wp = {* WeakestPre.apply_rules_args false *}
  "applies weakest precondition rules"

method_setup wp_once = {* WeakestPre.apply_once_args false *}
  "applies one weakest precondition rule"

method_setup wp_trace = {* WeakestPre.apply_rules_args true *}
  "applies weakest precondition rules with tracing"

method_setup wp_once_trace = {* WeakestPre.apply_once_args true *}
  "applies one weakest precondition rule with tracing"

end
