(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory SP
  imports
    Nondet_More_VCG
    Eisbach_Tools.Eisbach_Methods
begin

chapter \<open>Methods for strongest postcondition reasoning.\<close>

named_theorems sp

text \<open>
  This method uses the reverse ordering of the @{thm sp} set, so that if more than one rule in the
  set matches, the more recently added rule will be used.\<close>
method_setup sp_once =
  \<open>Scan.optional (Scan.lift (Args.$$$ "rules" -- Args.colon) |-- Attrib.thms) [] >>
     (fn rules => fn ctxt =>
       SIMPLE_METHOD' (resolve_tac ctxt (rules @ rev (Named_Theorems.get ctxt @{named_theorems sp}))))\<close>

text \<open>
  In strongest postcondition reasoning, care must be taken to ensure that a schematic postcondition
  is always created as late as possible: a schematic postcondition that is created too early in the
  chain of strongest postcondition steps may not be able to unify with bound variables that arise
  along this chain, leading to unprovable goals. The following is used to check whether a goal
  is a Hoare triple with schematic postcondition.\<close>
lemma post_test_True: "False \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ _. True\<rbrace>" by simp
lemma post_test_False: "False \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ _. False\<rbrace>" by simp

method sp_post_schematic = succeeds \<open>rule post_test_True\<close>, succeeds \<open>rule post_test_False\<close>

method sp_fwd uses rules = fwd_all_new \<open>sp_once rules: rules\<close> \<open>sp_fwd | fails sp_post_schematic\<close>

method sp_finish uses rules = rule hoare_strengthen_post, sp_fwd rules: rules

text \<open>
  Perform strongest postcondition reasoning, ensuring that unsolved subgoals with schematic
  postconditions are not created.

  In addition to the rules in the set @{thm sp}, the user may specify additional rules to the rules:
  argument, which will be used in preference to those in the @{thm sp} set.\<close>
method sp uses rules \<open>apply strongest postcondition rules\<close> =
  (sp_fwd rules: rules; (sp_finish rules: rules)?) | (sp_finish rules: rules)

method sp_step uses rules \<open>do one step of strongest postcondition reasoning\<close> =
  (sp_once rules: rules, (sp_once rules: rules)?), fails sp_post_schematic

lemmas [sp] =
  bind_wp_fwd return_sp get_sp put_sp gets_sp modify_sp assert_sp assert_opt_sp
  select_sp select_f_sp state_select_sp fail_sp chaos_sp hoare_returnOk_sp hoare_K_bind

end
