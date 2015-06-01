(*  Title:      Subgoal_Focus.thy
    Author:     Daniel Matichuk, NICTA/UNSW
    Author:     Makarius

Support for structured proof "scripts", via subgoal focus command.

TODO:
  - discontinue 'premises' binding, use general 'noting' instead (?);
*)

theory Subgoal_Focus
imports Main
keywords
  "subgoal" :: prf_goal and
  "premises"
begin

ML \<open>
signature SUBGOAL_FOCUS =
sig
  val subgoal_focus: Attrib.binding -> Attrib.binding ->
    (binding * typ option * mixfix) list -> Proof.state -> Proof.state
  val subgoal_focus_cmd: Attrib.binding -> Attrib.binding ->
    (binding * string option * mixfix) list -> Proof.state -> Proof.state
end;

structure Subgoal_Focus: SUBGOAL_FOCUS =
struct

local

fun find_matching pred (fix :: fs) (goal_param :: gps) =
      if pred (fix, goal_param)
      then fst fix :: find_matching pred fs gps
      else goal_param :: find_matching pred (fix :: fs) gps
  | find_matching _ [] _ = []
  | find_matching _ ((_, b) :: _) [] =
      error ("Couldn't find parameter in subgoal" ^ Position.here (Binding.pos_of b));

fun check_unique_fixes' checked (((x, _), b) :: fs) =
      if member (op =) checked x
      then error ("Duplicate for-fixed subgoal parameter" ^ Position.here (Binding.pos_of b))
      else check_unique_fixes' (x :: checked) fs
  | check_unique_fixes' _ [] = ();

fun check_unique_fixes fs = check_unique_fixes' [] fs;

fun gen_focus prep_vars prep_atts
    raw_binding raw_prems_binding raw_fixes state =
  let
    val _ = Proof.assert_backward state;
    val ctxt = Proof.context_of state;
    val goal = #goal (Proof.simple_goal state);

    val binding = apsnd (map (prep_atts ctxt)) raw_binding;
    val prems_binding = apsnd (map (prep_atts ctxt)) raw_prems_binding;

    val (fixes, ctxt') = prep_vars raw_fixes ctxt;

    val fixes' =
      fixes
      |> map (fn (b, optT, _) =>
          (Free (Binding.name_of b, the_default (Type_Infer.anyT []) optT), b))
      |> burrow_fst (Type_Infer_Context.infer_types ctxt')
      |> map (apfst Term.dest_Free);

    val () = check_unique_fixes fixes';

    val (_, goal_params) = Logic.goal_params (Thm.prop_of goal) 1;
    val goal_params' = map (apfst Name.internal o Term.dest_Free) goal_params;

    val typ_matches = Sign.typ_instance (Proof_Context.theory_of ctxt);

    val renames =
      find_matching (fn (((_, T1), _), (_, T2)) => typ_matches (T2, T1)) fixes' goal_params'
      |> rev |> map fst;

    val goal' =
        (* FIXME proper check in/for rename_tac *)
        (case SINGLE (rename_tac renames 1) goal of
          SOME goal' => goal'
        | NONE => raise Fail "Failed to rename subgoal");

    val subgoal = Goal.init (Thm.cprem_of goal' 1);
    val (focus as {context = focus_ctxt, ...}, _) = Subgoal.focus ctxt' 1 subgoal;

    fun after_qed [[res]] state' =  (* FIXME continue with state' *)
      let
        val retrofit =
          Subgoal.retrofit focus_ctxt ctxt' (#params focus) (#asms focus) 1
            (Goal.protect 0 res) subgoal
          |> Seq.hd
          |> Goal.conclude;
        val result = Raw_Simplifier.norm_hhf ctxt retrofit;
      in
        state
        |> Proof.refine (Method.primitive_text (fn _ =>
            Thm.bicompose NONE {flatten = false, match = false, incremented = false}
              (false, retrofit, 0) 1 #> Seq.hd))
        |> Seq.hd
        |> Proof.map_context (snd o Proof_Context.note_thmss "" [(binding, [([result], [])])])
      end;

    val thesis = Object_Logic.drop_judgment focus_ctxt (Thm.term_of (#concl focus));
  in
    (* FIXME more conventional block structure, like Proof.begin_block *)
    Proof.begin_notepad focus_ctxt
    |> Proof.local_goal (K (K ())) (K I) (pair o rpair I) "subgoal" NONE after_qed
      [(Thm.empty_binding, [Thm.term_of (#concl focus)])]
    |> Proof.map_context (snd o
        Proof_Context.note_thmss ""
          [((Binding.name "prems", []), [(#prems focus, [])]),
           (prems_binding, [(#prems focus, [])])])
    |> Proof.bind_terms [((Auto_Bind.thesisN, 0), SOME thesis)]
  end;

in

val subgoal_focus = gen_focus Proof_Context.cert_vars Attrib.attribute;
val subgoal_focus_cmd = gen_focus Proof_Context.read_vars Attrib.attribute_cmd;

end;

val fact_binding = (Parse.binding -- Parse.opt_attribs || Parse.attribs >> pair Binding.empty);
val opt_fact_binding = Scan.optional fact_binding Attrib.empty_binding;

val _ =
  Outer_Syntax.command @{command_keyword subgoal} "focus subgoal"
    (opt_fact_binding --
      (Scan.optional (@{keyword "premises"} |-- Parse.!!! fact_binding) Attrib.empty_binding) --
      Parse.for_fixes >>
      (fn ((a, b), c) => Toplevel.proofs (Seq.make_results o Seq.single o subgoal_focus_cmd a b c)));

end;
\<close>

end