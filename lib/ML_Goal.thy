(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ML_Goal
imports Main
keywords "ML_goal" :: thy_goal_stmt
begin

\<comment>\<open>
  Defines a new command `ML_goal`. `ML_goal` is similar to @{command lemma}
  and @{command theorem} in that it specifies a goal and enters a proof state
  for you prove that goal.

  However, instead of parsing goal terms from user input, `ML_goal` uses
  an ML block to produce a list of ML terms, and then sets up the proof state
  to prove those terms as goals.

  Each goal term must be an instance of either @{typ bool} or @{typ prop}.

  There are some concrete examples in @{file ML_Goal_Test.thy}.
\<close>

ML \<open>

structure ML_goal_data = Proof_Data(
  type T = term list
  val init = K []
);

local

\<comment>\<open>
  Why are we stashing something into a `Proof_Data` and then immediately
  taking it out again?

  In @{ML "fn (pos, source, ctxt: Context.generic) =>
      ML_Context.expression pos source ctxt"},
  `source` is a fragment of ML code which gets evaluated in the ML context
  associated with `ctxt`, which in this case should be the proof context
  associated with the call to `ML_goal`. The result is a new generic context
  with a new ML context, updated with the effects of evaluating `source`.

  This means the only way to extract information out of `source` is via
  its side-effects on the ML context. We have two main options:

  - Declare an @{ML "Unsynchronized.ref"} in this file (ML_Goal), and stash
    the value described by `source` into that.
    - This is unlikely to play well with deferred or concurrent proofs.

  - Use an instance of `Proof_Data` to declare some new state that's
    associated with all proof contexts (in this case "the result of
    the ML block passed to `ML_goal`"), and evaluate `source` in such a way
    as to store the result there.
    - This has more overhead compared to the `ref` solution, but it's
      still negligible.
    - This is the 'preferred' way to store 'local state' in contexts.
    - This is safe for deferred or concurrent proofs.
\<close>
fun evaluate_goals source =
    ML_Context.expression
      (Input.pos_of source)
      (ML_Lex.read "Theory.local_setup (ML_goal_data.put (("
        @ ML_Lex.read_source source
        @ ML_Lex.read "): term list))")
    |> Context.proof_map
    #> ML_goal_data.get;

fun err_msg_bad_type goal (typ: typ) ctxt =
    "The goal " ^ (@{make_string} (Syntax.pretty_term ctxt goal)) ^ " " ^
    "has unsupported type " ^ (@{make_string} typ) ^ ". " ^
    "The ML_goal command expects either a " ^ (@{make_string} @{typ bool}) ^ " " ^
    "or a " ^ (@{make_string} @{typ prop}) ^ ".";

fun begin_proof ((name, attrs): Attrib.binding, ml_block: Input.source) ctxt =
    let
      \<comment>\<open>
        In the very common case that a goal is a @{typ bool}, we wrap
        it in @{term Trueprop} to keep the Proof.theorem command happy.
      \<close>
      fun prop_wrap goal =
          case Term.type_of goal of
            @{typ bool} => goal |> HOLogic.mk_Trueprop
          | @{typ prop} => goal
          | other => error (err_msg_bad_type goal other ctxt);

      val goals =
          evaluate_goals ml_block ctxt
          |> List.map prop_wrap

          \<comment>\<open> Ensures free variables are type-consistent. \<close>
          |> Syntax.check_props ctxt
          |> List.map (rpair []);

      \<comment>\<open>
        Figures out that the `folded` in `[folded foo]` means
        @{attribute folded}. Required for attributes to work.
      \<close>
      val parsed_attrs = map (Attrib.check_src ctxt) attrs;
      val binding = (name, parsed_attrs);

      val start_pos = Position.thread_data ();

      fun after_qed (results: thm list list) ctxt =
          let
            val thms = results |> hd;
            val ((res_name, res), ctxt') =
                Local_Theory.note (binding, thms) ctxt;
            val _ =
                Proof_Display.print_results { interactive = true, pos = start_pos } ctxt'
                  (("theorem", res_name), [("", res)])
          in ctxt' end
    in
      Proof.theorem NONE
        after_qed
        [goals] ctxt
    end;

val ML_goal_cmd =
    Scan.optional (Parse_Spec.opt_thm_name ":") Binding.empty_atts
    -- Parse.ML_source
    >> begin_proof

val _  =
    Outer_Syntax.local_theory_to_proof
      \<^command_keyword>\<open>ML_goal\<close>
      "ML-provided goal"
      ML_goal_cmd;

in end
\<close>

end