(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*Alternate apply command which displays "used" theorems in refinement step*)

theory Apply_Trace_Cmd
imports Apply_Trace
keywords "apply_trace" :: prf_script
begin

ML{*

val _ =
  Outer_Syntax.command @{command_keyword "apply_trace"} "initial refinement step (unstructured)"

  (Args.mode "only_names" -- (Scan.option (Parse.position Parse.cartouche)) --  Method.parse >>
    (fn ((on,query),text) => Toplevel.proofs (Apply_Trace.apply_results {silent_fail = false}
     (Pretty.writeln ooo (Apply_Trace.pretty_deps on query)) text)));

*}

lemmas [no_trace] = protectI protectD TrueI Eq_TrueI eq_reflection

(* Test. *)
lemma "(a \<and> b) = (b \<and> a)"
  apply_trace auto
  oops

(* Test. *)
lemma "(a \<and> b) = (b \<and> a)"
  apply_trace \<open>intro\<close> auto
  oops

(* Local assumptions might mask real facts (or each other). Probably not an issue in practice.*)
lemma
  assumes X: "b = a"
  assumes Y: "b = a"
  shows
  "b = a"
  apply_trace (rule Y)
  oops

(* If any locale facts are accessible their local variant is assumed to the one that is used. *)

locale Apply_Trace_foo = fixes b a
  assumes X: "b = a"
begin

  lemma shows "b = a" "b = a"
   apply -
   apply_trace (rule Apply_Trace_foo.X)
   prefer 2
   apply_trace (rule X)
   oops
end

experiment begin

text \<open>Example of trace for grouped lemmas\<close>
definition ex :: "nat set"  where
 "ex = {1,2,3,4}"

lemma v1:  "1 \<in> ex"  by (simp add: ex_def)
lemma v2:  "2 \<in> ex"  by (simp add: ex_def)
lemma v3:  "3 \<in> ex"  by (simp add: ex_def)

text \<open>Group several lemmas in a single one\<close>
lemmas vs = v1 v2 v3

lemma "2 \<in> ex"
  apply_trace (simp add: vs)
  oops

end
end
