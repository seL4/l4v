(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Trace_No_Trace
  imports
    Trace_Monad
    WPSimp
begin

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

lemma no_trace_is_triple:
  "no_trace f = triple_judgement \<top> f (\<lambda>() f. id no_trace f)"
  by (simp add: triple_judgement_def split: unit.split)

lemmas [wp_trip] = no_trace_is_triple

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

end