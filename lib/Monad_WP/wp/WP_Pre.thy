(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory WP_Pre
imports
  "~~/src/HOL/Main"
  "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

(* Succeed if a predicate P holds on the head goal *)
ML \<open>
  fun cond_method P =
    Scan.succeed (fn _ => SIMPLE_METHOD
      (SUBGOAL (fn (t,_) => COND (fn _ => P t) all_tac no_tac) 1))
\<close>

(* Succeed if the conclusion of the head goal has schematic variables *)
method_setup concl_has_vars =
  \<open>cond_method (fn t => Term.exists_subterm Term.is_Var (Logic.strip_imp_concl t))\<close>

named_theorems wp_pre

(* Use safe thm to make sure wp_pre is not empty *)
declare TrueI [wp_pre]

(* Apply wp_pre if conclusion of head goal has no schematic variables *)
method wp_pre = (concl_has_vars | (rule wp_pre)?)

end
