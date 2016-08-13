(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Solves_Tac
imports
  "Main"
begin

ML \<open>

val ETAC_LIMIT = 5;

(* Solve the tactic by applying the given rule, then unifying assumptions. *)
fun solve_tac ctxt thm i goal =
let
  (* Use "etac", but give up if there are countless unifications that
   * don't end up working. *)
  fun limited_etac thm i =
    Seq.take ETAC_LIMIT o eresolve_tac ctxt [thm] i
in
  if Thm.no_prems thm then
    SOLVED' (resolve_tac ctxt [thm]) i goal
  else
    SOLVED' (
      limited_etac thm
      THEN_ALL_NEW (
        Goal.norm_hhf_tac ctxt THEN' Method.assm_tac ctxt))  i goal
end

(*
 * Return all thms available in the context.
 *
 * Clagged from "find_theorems"
 *)
fun all_facts_of ctxt =
let
  val local_facts = Proof_Context.facts_of ctxt;
  val global_facts = Global_Theory.facts_of (Proof_Context.theory_of ctxt);
in
  maps Facts.selections
   (Facts.dest_static false [global_facts] local_facts @
    Facts.dest_static false [] global_facts)
  |> map snd
end

(* Try blindly applying every previously proven rule. *)
fun solves_tac ctxt =
let
  val assms =
    Proof_Context.get_fact ctxt (Facts.named "local.assms")
      handle ERROR _ => [];
  fun add_prems i = TRY (Method.insert_tac ctxt assms i);
  val all_facts = all_facts_of ctxt
  val solve_tacs = map (fn thm => solve_tac ctxt thm 1) all_facts
in
  (add_prems THEN' assume_tac ctxt)
  ORELSE'
  SOLVED' (Subgoal.FOCUS_PARAMS (K (add_prems 1 THEN FIRST solve_tacs)) ctxt)
end

\<close>

method_setup solves = "
  Scan.succeed (SIMPLE_METHOD' o solves_tac)
" "find a previously proven fact that solves the goal"


lemma "(A = B) = (B = A)"
  apply solves
  oops

lemma "\<lbrakk> A \<Longrightarrow> B ; B \<Longrightarrow> A \<rbrakk> \<Longrightarrow> A = B"
  apply solves
  oops

end
