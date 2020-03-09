(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Sep_Provers
imports Sep_Rotate
begin

(* Constrained lens for sep_erule tactic *)
lemma sep_asm_eq_erule:
  "(P \<and>* R) s \<Longrightarrow> (\<And>s. T s = (P \<and>* R) s) \<Longrightarrow> (T s \<Longrightarrow> (P' \<and>* R') s) \<Longrightarrow> (P' \<and>* R') s"
  by (clarsimp)

lemma sep_rule:
  "(\<And>s. T s \<Longrightarrow> P s) \<Longrightarrow> (T \<and>* R) s \<Longrightarrow> (P \<and>* R) s"
  by (rule sep_conj_impl1)

lemma sep_erule:
  "(T \<and>* R') s  \<Longrightarrow> (\<And>s. T s \<Longrightarrow> P s) \<Longrightarrow> (\<And>s. R' s \<Longrightarrow> R s) \<Longrightarrow>  (P \<and>* R) s"
  by (rule sep_conj_impl)

(* Construct analogues to rule/drule etc,  for separation logic *)

ML \<open>
fun sep_select ctxt = resolve_tac ctxt [@{thm sep_eq}]
fun sep_asm_select ctxt = dresolve_tac ctxt [@{thm sep_asm_eq}]
fun sep_asm_erule_select ctxt = eresolve_tac ctxt [@{thm sep_asm_eq_erule}]

fun sep_rule_tactic ctxt thms =
  let val sep_rule = resolve_tac ctxt [@{thm sep_rule}]
  in sep_apply_tactic ctxt sep_rule thms end

fun sep_drule_tactic ctxt thms =
  let val sep_drule = dresolve_tac ctxt [rotate_prems ~1 @{thm sep_rule}]
  in sep_apply_tactic ctxt sep_drule thms end

fun sep_frule_tactic ctxt thms  =
  let val sep_frule = forward_tac ctxt [rotate_prems ~1 @{thm sep_rule}]
  in sep_apply_tactic ctxt sep_frule thms end

fun sep_erule_tactic ctxt thms =
  let val sep_erule = (eresolve_tac ctxt [@{thm sep_erule}])
  in sep_apply_tactic ctxt sep_erule thms end

fun sep_rule_tac tac ctxt = rotator (sep_select ctxt) tac ctxt
fun sep_drule_tac tac ctxt = rotator (sep_asm_select ctxt) tac ctxt
fun sep_erule_tac tac ctxt =  rotator (sep_asm_select ctxt) tac ctxt
fun sep_erule_concl_tac tac ctxt = rotator (sep_select ctxt) tac ctxt

fun sep_erule_full_tac tac ctxt =
  let val r = rotator' ctxt
  in
    tac |> r (sep_asm_erule_select ctxt) |> r (sep_select ctxt)
  end

fun sep_erule_full_tac' tac ctxt =
  let val r = rotator' ctxt
  in
    tac |> r (sep_select ctxt) |> r (sep_asm_erule_select ctxt)
  end

fun sep_rule_comb_tac true  thms ctxt  = sep_rule_tac (resolve_tac ctxt thms) ctxt
  | sep_rule_comb_tac false thms ctxt  = sep_rule_tac (sep_rule_tactic ctxt thms) ctxt

fun sep_rule_method bool thms ctxt = SIMPLE_METHOD' (sep_rule_comb_tac bool thms ctxt)

fun sep_drule_comb_tac true  thms ctxt = sep_drule_tac (dresolve_tac ctxt thms) ctxt
  | sep_drule_comb_tac false thms ctxt = sep_drule_tac (sep_drule_tactic ctxt thms) ctxt

fun sep_drule_method bool thms ctxt = SIMPLE_METHOD' (sep_drule_comb_tac bool thms ctxt)

fun sep_frule_method true  thms ctxt = SIMPLE_METHOD' (sep_drule_tac (forward_tac ctxt thms) ctxt)
  | sep_frule_method false thms ctxt = SIMPLE_METHOD' (sep_drule_tac (sep_frule_tactic ctxt thms) ctxt)

fun sep_erule_method true  thms ctxt = SIMPLE_METHOD' (sep_erule_tac (eresolve_tac ctxt thms) ctxt)
  | sep_erule_method false thms ctxt = SIMPLE_METHOD' (sep_erule_tac (sep_erule_tactic ctxt thms) ctxt)

fun sep_erule_concl_method true  thms ctxt =
      SIMPLE_METHOD' (sep_erule_concl_tac (eresolve_tac ctxt thms) ctxt)
  | sep_erule_concl_method false thms ctxt =
      SIMPLE_METHOD' (sep_erule_concl_tac (sep_erule_tactic ctxt thms) ctxt)

fun sep_erule_full_method true thms ctxt =
      SIMPLE_METHOD' (sep_erule_full_tac (eresolve_tac ctxt thms) ctxt)
  | sep_erule_full_method false thms ctxt =
      SIMPLE_METHOD' (sep_erule_full_tac (sep_erule_tactic ctxt thms) ctxt)
\<close>

method_setup sep_rule = \<open>
  Scan.lift (Args.mode "direct") -- Attrib.thms  >> uncurry sep_rule_method
\<close>

method_setup sep_drule = \<open>
  Scan.lift (Args.mode "direct") -- Attrib.thms >> uncurry sep_drule_method
\<close>

method_setup sep_frule = \<open>
  Scan.lift (Args.mode "direct") -- Attrib.thms >> uncurry sep_frule_method
\<close>

method_setup sep_erule = \<open>
  Scan.lift (Args.mode "direct") -- Attrib.thms >> uncurry sep_erule_method
\<close>

method_setup sep_erule_concl = \<open>
  Scan.lift (Args.mode "direct") -- Attrib.thms >> uncurry sep_erule_concl_method
\<close>

method_setup sep_erule_full = \<open>
  Scan.lift (Args.mode "direct") -- Attrib.thms>> uncurry sep_erule_full_method
\<close>

end
