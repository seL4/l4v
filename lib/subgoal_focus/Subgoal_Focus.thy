(*  Title:      Subgoal_Focus.thy
    Author:     Daniel Matichuk, NICTA/UNSW
    Author:     Makarius

Support for structured proof "scripts", via subgoal focus command.

TODO:
  - discontinue 'premises' binding: use general 'supply';
  - prefer explicit "using prems" over implicit "apply (insert prems)" (!?);
  - speculatively: 'premises' avoids inserting prems into focused goal (???);
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
    bool * (bstring option * Position.T) list -> Proof.state -> Proof.state
  val subgoal_focus_cmd: Attrib.binding -> Attrib.binding option ->
    bool * (bstring option * Position.T) list -> Proof.state -> Proof.state
end;

structure Subgoal_Focus: SUBGOAL_FOCUS =
struct

local

fun cert_var v ctxt = apfst hd (Proof_Context.cert_vars [v] ctxt);

fun subst_cterm (in_ct, in_ct') ct =
  let
    val abs = Thm.dest_arg (Thm.cprop_of (Thm.abstract_rule "_dummy_" in_ct (Thm.reflexive ct)));
    val ct' = Drule.beta_conv abs in_ct';
  in ct' end;

fun unprotect_cterm ct = Thm.cprop_of (Goal.conclude (Thm.assume ct));

fun focus_named_params ctxt do_prems (param_suffix, raw_param_specs) subgoal =
  let
    val goal_params = Logic.strip_params (Thm.term_of subgoal);

    val internal_params =
      goal_params
      |> Variable.variant_frees ctxt [Thm.term_of subgoal]
      |> map (Name.internal o fst);

    val n = length goal_params;
    val m = length raw_param_specs;

    val _ =
      m <= n orelse
        error ("Excessive subgoal parameter specification" ^
          Position.here_list (map snd (drop n raw_param_specs)));

    val param_specs =
      raw_param_specs |> map
        (fn (NONE, _) => NONE
          | (SOME x, pos) =>
              let val b = #1 (#1 (cert_var (Binding.make (x, pos), NONE, NoSyn) ctxt))
              in SOME (Variable.check_name b) end)
      |> param_suffix ? append (replicate (n - m) NONE);

    val (param_specs',ctxt1) = fold_burrow Variable.variant_fixes (map the_list param_specs) ctxt
      |>> map (find_first (K true))

    val ((_, [st]), ctxt2) = Variable.importT [Thm.reflexive subgoal] ctxt1;

    val subgoal1 = Thm.dest_arg (Thm.cprop_of st);

    val renamed =
      subgoal1
      |> Thm.renamed_term (Logic.list_rename_params internal_params (Thm.term_of subgoal1));

    val ((goal_params', subgoal2), ctxt3) =
      Variable.focus_cterm renamed ctxt2
      |> apfst (apfst (map snd));

    fun rename_free ct opt_n = case opt_n of SOME n => 
    let
      val (_,T) = Term.dest_Free (Thm.term_of ct);
    in Thm.cterm_of ctxt2 (Free (n,T)) end
    | NONE => ct
    
    fun rename_list (opt_x :: xs) (y :: ys) = (rename_free y opt_x :: rename_list xs ys)
      | rename_list _ ys = ys;
    
    val goal_params'' = rename_list param_specs' goal_params';

    val ctxt4 = fold (Variable.declare_constraints o Thm.term_of) goal_params'' ctxt3;
    val subgoal3 = fold subst_cterm (ListPair.zip (goal_params', goal_params'')) subgoal2;
    val subgoal4 =
      if do_prems then subgoal3 else Thm.apply (Thm.cterm_of ctxt3 Logic.protectC) subgoal3;
    val (focus, _) = Subgoal.focus ctxt4 1 (Goal.init subgoal4);

    val params_out = map (fn ct => (fst (Term.dest_Free (Thm.term_of ct)), ct)) goal_params'';
    val concl = if do_prems then #concl focus else unprotect_cterm (#concl focus);
  in
    {asms = #asms focus, prems = #prems focus, concl = concl, params = params_out,
     context = #context focus}
  end;

fun primitive_raw_text r = Method.Basic (fn ctxt => fn _ => EMPTY_CASES (PRIMITIVE (r ctxt)));

fun gen_focus prep_atts
    raw_binding raw_prems_binding param_specs state =
  let
    val _ = Proof.assert_backward state;
    val ctxt = Proof.context_of state;
    val goal = #goal (Proof.raw_goal state);

    val binding = apsnd (map (prep_atts ctxt)) raw_binding;
    val opt_prems_binding = Option.map (apsnd (map (prep_atts ctxt))) raw_prems_binding;
    val prems_binding = the_default (Binding.empty, []) opt_prems_binding;

    val do_prems = is_some opt_prems_binding;

    val subgoal = Thm.cprem_of goal 1;

    val focus = focus_named_params ctxt do_prems param_specs subgoal;
    val focus_ctxt = #context focus;

    fun after_qed [[res]] state' =  (* FIXME continue with state' *)
      let
        val retrofit =
          Subgoal.retrofit focus_ctxt ctxt (#params focus) (#asms focus) 1
            (Goal.protect 0 res) (Goal.init subgoal)
          |> Seq.hd
          |> Goal.conclude;
        val result = Raw_Simplifier.norm_hhf ctxt retrofit;
      in
        state
        |> Proof.refine (primitive_raw_text (fn _ =>
            Thm.bicompose NONE {flatten = false, match = false, incremented = false}
              (false, retrofit, 0) 1 #> Seq.hd))
        |> Seq.hd
        |> Proof.map_context (snd o Proof_Context.note_thmss "" [(binding, [([result], [])])])
      end;

  in
    (* FIXME more conventional block structure, like Proof.begin_block *)
    Proof.begin_notepad focus_ctxt
    |> Proof.map_context (snd o
        Proof_Context.note_thmss ""
          [(prems_binding, [(#prems focus, [])])])
    |> Proof.local_goal (K (K ())) (K I) (pair o rpair I) "subgoal" NONE after_qed
      [(Thm.empty_binding, [Thm.term_of (#concl focus)])]
  end;

in

val subgoal_focus = gen_focus Attrib.attribute;
val subgoal_focus_cmd = gen_focus Attrib.attribute_cmd;

end;

val fact_binding = (Parse.binding -- Parse.opt_attribs || Parse.attribs >> pair Binding.empty);
val opt_fact_binding = Scan.optional fact_binding Attrib.empty_binding;

val dots = Parse.sym_ident :-- (fn "\<dots>" => Scan.succeed () | _ => Scan.fail) >> #1;

val for_params =
  Scan.optional
    (@{keyword "for"} |--
      Parse.!!! ((Scan.option dots >> is_some) --
        (Scan.repeat1 (Parse.position (Parse.maybe Parse.name)))))
    (false, []);

val _ =
  Outer_Syntax.command @{command_keyword subgoal} "focus subgoal"
    (opt_fact_binding --
      (Scan.option (@{keyword "premises"} |-- Parse.!!! opt_fact_binding)) --
      for_params >>
      (fn ((a, b), c) =>
         Toplevel.proofs (Seq.make_results o Seq.single o subgoal_focus_cmd a b c)));

end;
\<close>

end
