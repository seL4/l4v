(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * This file introduces an experimental "distinct" command that takes
 * a list of 'n' terms, and generates O(n^2) lemmas for you to prove
 * that the 'n' terms are all distinct. These proofs can typically be
 * carried out by an "apply auto" command, giving you O(n^2)
 * distinctness theorems relatively easily. These new theorems can then
 * be thrown into a simpset to avoid having to constantly unfold
 * definitions merely to prove distinctness.
 *
 * This may significantly simplify certain proofs where inequality of
 * defined terms is frequently relied upon.
 *
 * The "distinct" command is not really scalable, due to its O(n^2)
 * proof terms generated. If we wanted to use this in a larger example,
 * we would probably want a "ordered" command, which forces you to show
 * that 'n' terms have some ordering, and then automatically derive the
 * O(n^2) possible proof terms on-the-fly in a simproc (possibly using
 * Isabelle's existing "order_tac").
 *)
theory Distinct_Cmd
imports Main
  keywords "distinct" :: thy_goal
begin

ML \<open>
local

(*
 * Process a parsed binding, converting it from raw tokens (which
 * can't be passed into Local_Theory.note) into its semantic meaning
 * (which can).
 *)
fun process_binding lthy binding =
  apsnd (map (Attrib.check_src lthy)) binding

(* Parse the parameters to "distinct". *)
val distinct_parser =
  (Scan.optional (Parse_Spec.opt_thm_name ":") Binding.empty_atts
         -- Scan.repeat1 Parse.term)

(* Generate a prop of the form "a ~= b". *)
fun mk_inequality_pair a b =
  HOLogic.mk_eq (a, b)
  |> HOLogic.mk_not
  |> HOLogic.mk_Trueprop

(* Generate O(n^2) distinctness goals. *)
fun gen_distinct_goals terms =
  map_product
    (fn a => fn b =>
        if a = b then NONE
        else SOME (mk_inequality_pair a b))
    terms terms
  |> map_filter I
  |> map (fn t => (t, []))

(* Given a list of terms, coerce them all into the same type. *)
fun coerce_terms_to_same_type lthy terms =
  HOLogic.mk_list dummyT terms
  |> Syntax.check_term lthy
  |> HOLogic.dest_list

(* We save the theorems to the context afterwards. *)
fun after_qed thm_name thms lthy =
  Local_Theory.note (thm_name, (flat thms)) lthy |> snd

in

val _ =
   Outer_Syntax.local_theory_to_proof @{command_keyword "distinct"}
      "prove distinctness of a list of terms"
      (distinct_parser
        >> (fn (thm_name, terms) => fn lthy =>
              Proof.theorem NONE (after_qed (process_binding lthy thm_name)) [
                  map (Syntax.parse_term lthy) terms
                  |> coerce_terms_to_same_type lthy
                  |> gen_distinct_goals
              ] lthy
            ))

end
\<close>

(* Test. *)
context
  fixes A :: nat
  fixes B :: nat
  fixes C :: nat
  assumes x: "A = 1 \<and> B = 2 \<and> C = 3"
begin

distinct A B C "5" "6" "2 + 11"
  by (auto simp: x)

end

end
