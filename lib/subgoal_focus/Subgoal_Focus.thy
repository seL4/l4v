(*  Title:      Subgoal_Focus.thy
    Author:     Daniel Matichuk, NICTA/UNSW
    Author:     Makarius

Support for structured proof "scripts", via subgoal focus command.

TODO:
  - discontinue 'premises' binding, use general 'noting' instead (?);
    - speculatively: 'premises' avoids inserting prems into focused goal
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
  val subgoal_focus: Attrib.binding -> Attrib.binding option ->
    (binding * typ option * mixfix) list -> Proof.state -> Proof.state
  val subgoal_focus_cmd: Attrib.binding -> Attrib.binding option ->
    (binding * string option * mixfix) list -> Proof.state -> Proof.state
end;

structure Subgoal_Focus: SUBGOAL_FOCUS =
struct

local

fun find_matching ctxt ((fix as ((x,T),_)) :: fs) (ct :: gps) =
      let
        val T' = Thm.typ_of (Thm.ctyp_of_cterm ct);
      in
        if Sign.typ_instance (Proof_Context.theory_of ctxt) (T',T)
        then Thm.cterm_of ctxt (Free (x, T')) :: find_matching ctxt fs gps
        else ct :: find_matching ctxt (fix :: fs) gps
      end
  | find_matching _ [] gps = gps
  | find_matching _ ((_, b) :: _) [] =
      error ("Couldn't find parameter in subgoal: " ^ quote (Binding.name_of b) ^
        Position.here (Binding.pos_of b));

fun subst_cterm (in_ct,in_ct') ct =
  let
    val abs = Thm.dest_arg (Thm.cprop_of (Thm.abstract_rule "_dummy_" in_ct (Thm.reflexive ct)));
    val ct' = Drule.beta_conv abs in_ct';
  in ct' end;

fun focus_named_params ctxt params subgoal =
  let
    val goal_params = Logic.strip_params (Thm.term_of subgoal);
    val internal_params = map (Name.internal o fst) goal_params;
    
    val ((_, [st]), ctxt1) = Variable.importT [Thm.reflexive subgoal] ctxt;
    val subgoal1 = Thm.dest_arg (Thm.cprop_of st);

    val renamed =
      subgoal1
      |> Thm.renamed_term (Logic.list_rename_params internal_params (Thm.term_of subgoal1));

    val ((goal_params',subgoal2),ctxt2) =
      Variable.focus_cterm renamed ctxt1
      |> apfst (apfst (map snd));

    val goal_params'' = rev (find_matching ctxt2 params (rev goal_params'));

    val subgoal3 = fold subst_cterm (ListPair.zip (goal_params',goal_params'')) subgoal2;

    val (focus,_) = Subgoal.focus ctxt2 1 (Goal.init subgoal3);

    val params_out = map (fn ct => (fst (Term.dest_Free (Thm.term_of ct)),ct)) goal_params'';

  in
    {asms = #asms focus, prems = #prems focus, concl = #concl focus, params = params_out,
     context = #context focus}
  end;


fun gen_focus prep_vars prep_atts
    raw_binding raw_prems_binding raw_fixes state =
  let
    val _ = Proof.assert_backward state;
    val ctxt = Proof.context_of state;
    val goal = #goal (Proof.simple_goal state);

    val binding = apsnd (map (prep_atts ctxt)) raw_binding;
    val opt_prems_binding = Option.map (apsnd (map (prep_atts ctxt))) raw_prems_binding;
    val prems_binding = the_default (Binding.empty,[]) opt_prems_binding;

    val (fixes, ctxt') = prep_vars raw_fixes ctxt;
    val (xs,ctxt'') = Proof_Context.add_fixes fixes ctxt';

    val fixes' =
      xs
      |> map (fn x => Free (x,the (Variable.default_type ctxt'' x)))
      |> Type_Infer_Context.infer_types ctxt''
      |> map Term.dest_Free
      |> map2 (fn (b,_,_) => rpair b) fixes;

    val subgoal = Thm.cprem_of goal 1;

    val focus = focus_named_params ctxt'' fixes' subgoal;
    val focus_ctxt = #context focus;

    fun after_qed [[res]] state' =  (* FIXME continue with state' *)
      let
        val retrofit =
          Subgoal.retrofit focus_ctxt ctxt'' (#params focus) (#asms focus) 1
            (Goal.protect 0 res) (Goal.init subgoal)
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

    val insert_prems = not (Option.isSome opt_prems_binding);
  in
    (* FIXME more conventional block structure, like Proof.begin_block *)
    Proof.begin_notepad focus_ctxt
    |> Proof.map_context (snd o
        Proof_Context.note_thmss ""
          [((Binding.name "prems", []), [(#prems focus, [])]),
           (prems_binding, [(#prems focus, [])])])
    |> Proof.bind_terms [((Auto_Bind.thesisN, 0), SOME thesis)]
    |> Proof.local_goal (K (K ())) (K I) (pair o rpair I) "subgoal" NONE after_qed
      [(Thm.empty_binding, [Thm.term_of (#concl focus)])]
    |> insert_prems ? Proof.refine_insert (#prems focus)
    |> (Seq.hd o Proof.refine Method.succeed_text)
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
      (Scan.option (@{keyword "premises"} |-- Parse.!!! opt_fact_binding)) --
      Parse.for_fixes >>
      (fn ((a, b), c) =>
         Toplevel.proofs (Seq.make_results o Seq.single o subgoal_focus_cmd a b c)));

end;
\<close>

end
