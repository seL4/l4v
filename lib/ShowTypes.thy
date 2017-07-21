(*
 * @TAG(NICTA_BSD)
 *
 * ShowTypes: show "hidden" type constraints in terms.
 * This is a simple utility around Sledgehammer's type annotation code.
 *
 * Based on Sledgehammer_Isar_Annotate and related modules
 * (by Blanchette and Smolka).
 *
 *
 * Usage
 * ----
 * This theory provides the improper commands
 *   term_show_types <term>
 *   thm_show_types <thm> [<thm> ...]
 *   goal_show_types [N]
 * as well as the ML function Show_Types.term_show_types.
 *
 * term_show_types and thm_show_types can be used as replacements
 * for the term and thm commands.
 *
 *
 * Known issues
 * ----
 * \<bullet> Type constraints for variables, etc. are not always printed.
 *   In that case, set show_types/show_sorts to get extra annotations.
 *
 * \<bullet> Doesn't print sort constraints. show_sorts will print them but
 *   the output may not be formatted properly.
 *
 * \<bullet> Doesn't compose with other term-display utils like Insulin.
 *)

theory ShowTypes imports
  Main
keywords "term_show_types" "thm_show_types" "goal_show_types" :: diag
begin

ML {*
structure Show_Types = struct

fun pretty_markup_to_string no_markup =
  Pretty.string_of
  #> YXML.parse_body
  #> (if no_markup then XML.content_of else YXML.string_of_body)

fun term_show_types no_markup ctxt term =
  let val keywords = Thy_Header.get_keywords' ctxt
      val ctxt' = ctxt
      |> Config.put show_markup false
      |> Config.put Printer.show_type_emphasis false

      (* FIXME: the sledgehammer code also sets these,
       *        but do we always want to force them on the user? *)
      (*
      |> Config.put show_types false
      |> Config.put show_sorts false
      |> Config.put show_consts false
      *)
      |> Variable.auto_fixes term
  in
    singleton (Syntax.uncheck_terms ctxt') term
    |> Sledgehammer_Isar_Annotate.annotate_types_in_term ctxt'
    |> Syntax.unparse_term ctxt'
    |> pretty_markup_to_string no_markup
  end

fun goal_show_types no_markup ctxt goal n = let
  val subgoals = goal |> Thm.prems_of
  val subgoals = if n = 0 then subgoals else
                 if n < 1 orelse n > length subgoals then
                      (* trigger error *) [Logic.get_goal (Thm.term_of (Thm.cprop_of goal)) n]
                 else [nth subgoals (n - 1)]
  val results = map (fn t => (NONE, term_show_types no_markup ctxt t)
                             handle ex as TERM _ => (SOME ex, term_show_types no_markup ctxt t))
                    subgoals
  in if null results
        then error "No subgoals to show"
     else if forall (Option.isSome o fst) results
        then raise the (fst (hd results))
     else map snd results
  end

end;

Outer_Syntax.command @{command_keyword term_show_types}
  "term_show_types TERM -> show TERM with type annotations"
  (Parse.term >> (fn t =>
    Toplevel.keep (fn state =>
      let val ctxt = Toplevel.context_of state in
        Show_Types.term_show_types false ctxt (Syntax.read_term ctxt t)
        |> writeln end)));

Outer_Syntax.command @{command_keyword thm_show_types}
  "thm_show_types THM1 THM2 ... -> show theorems with type annotations"
  (Parse.thms1 >> (fn ts =>
    Toplevel.keep (fn state =>
      let val ctxt = Toplevel.context_of state in
        Attrib.eval_thms ctxt ts
        |> app (Thm.prop_of #> Show_Types.term_show_types false ctxt #> writeln) end)));

let
  fun print_subgoals (x::xs) n = (writeln (Int.toString n ^ ". " ^ x); print_subgoals xs (n+1))
    | print_subgoals [] _ = ();
in
Outer_Syntax.command @{command_keyword goal_show_types}
  "goal_show_types [N] -> show subgoals (or Nth goal) with type annotations"
  (Scan.option Parse.int >> (fn n =>
    Toplevel.keep (fn state =>
      let val ctxt = Toplevel.context_of state
          val goal = Toplevel.proof_of state |> Proof.raw_goal |> #goal
      in Show_Types.goal_show_types false ctxt goal (Option.getOpt (n, 0))
         |> (fn xs => case xs of
                         [x] => writeln x
                       | _ => print_subgoals xs 1) end)))
end;
*}


text \<open>
  Simple demo. The main HOL theories don't have that much
  hidden polymorphism, so we use l4.verified.
\<close>

(*
experiment begin
  lemma c_guard_cast_byte: "c_guard (x :: ('a :: {mem_type}) ptr) \<Longrightarrow> c_guard (ptr_coerce x :: 8 word ptr)"
    goal_show_types 0
    using [[show_sorts]]
    goal_show_types 0
    apply (case_tac x)
    apply (fastforce intro!: byte_ptr_guarded simp: c_guard_def dest: c_null_guard)
    done

  thm c_guard_cast_byte[where x = "Ptr (ucast (0 :: 8 word))"]
  thm_show_types c_guard_cast_byte[where x = "Ptr (ucast (0 :: 8 word))"]

  (* Round-trip test *)
  ML {*
  let val ctxt = Config.put show_sorts true @{context}
      (* NB: this test fails if we leave some polymorphism in the term *)
      val term = @{thm c_guard_cast_byte[where x = "Ptr (ucast (0 :: 8 word)) :: unit ptr"]} |> Thm.prop_of
      val string_no_types = Syntax.pretty_term ctxt term
                            |> Pretty.string_of |> YXML.content_of
      val string_show_types = Show_Types.term_show_types true ctxt term

      val _ = assert (Syntax.read_term ctxt string_no_types <> term) "Show_Types test (baseline)"
      val _ = assert (Syntax.read_term ctxt string_show_types = term) "Show_Types test"
  in () end
  *}
end
*)

end