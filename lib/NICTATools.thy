(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Miscellaneous Isabelle tools. *)
theory NICTATools
imports
  Apply_Trace_Cmd
  Apply_Debug
  Find_Names
  (* Solves_Tac *)
  Rule_By_Method
  Eisbach_Methods
  TSubst
  Time_Methods_Cmd
  Try_Attribute
  Trace_Schematic_Insts
  Insulin
  ShowTypes
  AutoLevity_Hooks
  Locale_Abbrev
begin

section "Detect unused meta-forall"

(*
 * Detect meta-foralls that are unused in "lemma" statements,
 * and warn the user about them.
 *
 * They can sometimes create weird issues, usually due to the
 * fact that they have the empty sort "'a::{}", which confuses
 * certain tools, such as "atomize".
 *)
ML \<open>

(* Return a list of meta-forall variable names that appear
 * to be unused in the input term. *)
fun find_unused_metaall (Const (@{const_name "Pure.all"}, _) $ Abs (n, _, t)) =
      (if not (Term.is_dependent t) then [n] else []) @ find_unused_metaall t
  | find_unused_metaall (Abs (_, _, t)) =
      find_unused_metaall t
  | find_unused_metaall (a $ b) =
      find_unused_metaall a @ find_unused_metaall b
  | find_unused_metaall _ = []

(* Given a proof state, analyse its assumptions for unused
 * meta-foralls. *)
fun detect_unused_meta_forall _ (state : Proof.state) =
let
  (* Fetch all assumptions and the main goal, and analyse them. *)
  val {context = lthy, goal = goal, ...} = Proof.goal state
  val checked_terms =
      [Thm.concl_of goal] @ map Thm.term_of (Assumption.all_assms_of lthy)
  val results = List.concat (map find_unused_metaall checked_terms)

  (* Produce a message. *)
  fun message results =
    Pretty.paragraph [
      Pretty.str "Unused meta-forall(s): ",
      Pretty.commas
        (map (fn b => Pretty.mark_str (Markup.bound, b)) results)
      |> Pretty.paragraph,
      Pretty.str "."
    ]

  (* We use a warning instead of the standard mechanisms so that
   * we can produce a "warning" icon in Isabelle/jEdit. *)
  val _ =
    if length results > 0 then
      warning (message results |> Pretty.string_of)
    else ()
in
  (false, ("", []))
end

(* Setup the tool, stealing the "auto_solve_direct" option. *)
val _ = Try.tool_setup ("unused_meta_forall",
    (1, @{system_option auto_solve_direct}, detect_unused_meta_forall))
\<close>

lemma test_unused_meta_forall: "\<And>x. y \<or> \<not> y"
  oops

end
