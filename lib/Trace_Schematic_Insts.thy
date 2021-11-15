(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Trace_Schematic_Insts
imports
  Main
  MLUtils
  TermPatternAntiquote
begin

text \<open>
  See Trace_Schematic_Insts_Test for tests and examples.
\<close>

locale data_stash
begin

text \<open>
  We use this to stash a list of the schematics in the conclusion of the proof
  state. After running a method, we can read off the schematic instantiations
  (if any) from this list, then restore the original conclusion. Schematic
  types are added as "undefined :: ?'a" (for now, we don't worry about types
  that don't have sort "type").

  TODO: there ought to be some standard way of stashing things into the proof
  state. Find out what that is and refactor
\<close>
definition container :: "'a \<Rightarrow> bool \<Rightarrow> bool"
  where
  "container a b \<equiv> True"

lemma proof_state_add:
  "Pure.prop PROP P \<equiv> PROP Pure.prop (container True xs \<Longrightarrow> PROP P)"
  by (simp add: container_def)

lemma proof_state_remove:
  "PROP Pure.prop (container True xs \<Longrightarrow> PROP P) \<equiv> Pure.prop (PROP P)"
  by (simp add: container_def)

lemma rule_add:
  "PROP P \<equiv> (container True xs \<Longrightarrow> PROP P)"
  by (simp add: container_def)

lemma rule_remove:
  "(container True xs \<Longrightarrow> PROP P) \<equiv> PROP P"
  by (simp add: container_def)

lemma elim:
  "container a b"
  by (simp add: container_def)

ML \<open>
signature TRACE_SCHEMATIC_INSTS = sig
  type instantiations = {
    bounds: (string * typ) list,
    terms: (term * term) list,
    typs: (typ * typ) list
  }
  val empty_instantiations: instantiations

  val trace_schematic_insts:
        Method.method -> (instantiations -> unit) -> Method.method
  val default_report:
        Proof.context -> string -> instantiations -> unit

  val trace_schematic_insts_tac:
        Proof.context ->
        (instantiations -> instantiations -> unit) ->
        (thm -> int -> tactic) ->
        thm -> int -> tactic
  val default_rule_report:
        Proof.context -> string -> instantiations -> instantiations -> unit

  val skip_dummy_state: Method.method -> Method.method
  val make_term_container: term list -> term
  val dest_term_container: term -> term list

  val attach_proof_annotations: Proof.context -> term list -> thm -> thm
  val detach_proof_annotations: thm -> term list * thm

  val attach_rule_annotations: Proof.context -> term list -> thm -> thm
  val detach_rule_result_annotations:
        Proof.context -> thm -> ((string * typ) list * term list) * thm

  val instantiate_thm: Proof.context -> thm -> instantiations -> term
end

structure Trace_Schematic_Insts: TRACE_SCHEMATIC_INSTS = struct

\<comment>\<open>
  Each pair in the terms and typs fields are a (schematic, instantiation) pair.

  The bounds field records the binders which are due to subgoal bounds.

  An explanation: if we instantiate some schematic `?P` within a subgoal like
  @{term "\<And>x y. Q"}, it might be instantiated to @{term "\<lambda>a. R a
  x"}.  We need to capture `x` when reporting the instantiation, so we report
  that `?P` has been instantiated to @{term "\<lambda>x y a. R a x"}. In order
  to distinguish between the bound `x`, `y`, and `a`, we record the bound
  variables from the subgoal so that we can handle them as necessary.

  As an example, let us consider the case where the subgoal is
  @{term "\<And>x::int. foo (\<lambda>a. a::'e) (\<lambda>a. a + x) (0::nat)"}
  and the rule being applied is
  @{term "foo ((f::'d \<Rightarrow> 'a \<Rightarrow> 'a) y) (g::'b \<Rightarrow> 'b) (0::'c::zero)"}.
  This results in the instantiations
  {bounds: [("x", int)],
   terms: [(?f, \<lambda>x a b. b), (?g, \<lambda>x a. x + a), (?y, \<lambda>x. ?y x)],
   typs: [(?'a, 'e), (?'b, int), (?'c, nat)]}.
\<close>
type instantiations = {
  bounds: (string * typ) list,
  terms: (term * term) list,
  typs: (typ * typ) list
}

val empty_instantiations = {bounds = [], terms = [], typs = []}

\<comment>\<open>
  Work around Isabelle running every apply method on a dummy proof state
\<close>
fun skip_dummy_state method =
  fn facts => fn (ctxt, st) =>
    case Thm.prop_of st of
        Const (@{const_name Pure.prop}, _) $
          (Const (@{const_name Pure.term}, _) $ Const (@{const_name Pure.dummy_pattern}, _)) =>
          Seq.succeed (Seq.Result (ctxt, st))
      | _ => method facts (ctxt, st);

\<comment>\<open>
  Utils
\<close>
fun rewrite_state_concl eqn st =
  Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of st) (K eqn)) st

\<comment>\<open>
  Strip the @{term Pure.prop} that wraps proof state conclusions
\<close>
fun strip_prop ct =
      case Thm.term_of ct of
        Const (@{const_name "Pure.prop"}, @{typ "prop \<Rightarrow> prop"}) $ _ => Thm.dest_arg ct
      | _ => raise CTERM ("strip_prop: head is not Pure.prop", [ct])

fun cconcl_of st =
  funpow (Thm.nprems_of st) Thm.dest_arg (Thm.cprop_of st)
  |> strip_prop

fun vars_of_term t =
  Term.add_vars t []
  |> sort_distinct Term_Ord.var_ord

fun type_vars_of_term t =
  Term.add_tvars t []
  |> sort_distinct Term_Ord.tvar_ord

\<comment>\<open>
  Create annotation list
\<close>
fun make_term_container ts =
      fold (fn t => fn container =>
              Const (@{const_name container},
                    fastype_of t --> @{typ "bool \<Rightarrow> bool"}) $
                t $ container)
        (rev ts) @{term "True"}

\<comment>\<open>
  Retrieve annotation list
\<close>
fun dest_term_container
      (Const (@{const_name container}, _) $ x $ list) =
          x :: dest_term_container list
  | dest_term_container _ = []

\<comment>\<open>
  Attach some terms to a proof state, by "hiding" them in the protected goal.
\<close>
fun attach_proof_annotations ctxt terms st =
  let
    val container = make_term_container terms
    (* FIXME: this might affect st's maxidx *)
    val add_eqn =
          Thm.instantiate
            (TVars.empty,
             Vars.make [((("P", 0), @{typ prop}), cconcl_of st),
                        ((("xs", 0), @{typ bool}), Thm.cterm_of ctxt container)])
            @{thm proof_state_add}
  in
    rewrite_state_concl add_eqn st
  end

\<comment>\<open>
  Retrieve attached terms from a proof state
\<close>
fun detach_proof_annotations st =
  let
    val st_concl = cconcl_of st
    val (ccontainer', real_concl) = Thm.dest_implies st_concl
    val ccontainer =
          ccontainer'
          |> Thm.dest_arg (* strip Trueprop *)
          |> Thm.dest_arg \<comment>\<open>strip outer @{term "container True"}\<close>
    val terms =
          ccontainer
          |> Thm.term_of
          |> dest_term_container
    val remove_eqn =
          Thm.instantiate
            (TVars.empty,
             Vars.make [((("P", 0), @{typ prop}), real_concl),
                        ((("xs", 0), @{typ bool}), ccontainer)])
            @{thm proof_state_remove}
  in
    (terms, rewrite_state_concl remove_eqn st)
  end

\<comment> \<open>
  Attaches the given terms to the given thm by stashing them as a new @{term
  "container"} premise, *after* all the existing premises (this minimises
  disruption when the rule is used with things like `erule`).
\<close>
fun attach_rule_annotations ctxt terms thm =
  let
    val container = make_term_container terms
    (* FIXME: this might affect thm's maxidx *)
    val add_eqn =
          Thm.instantiate
            (TVars.empty,
             Vars.make [((("P", 0), @{typ prop}), Thm.cconcl_of thm),
                        ((("xs", 0), @{typ bool}), Thm.cterm_of ctxt container)])
            @{thm rule_add}
  in
    rewrite_state_concl add_eqn thm
  end

\<comment> \<open>
  Finds all the variables and type variables in the given thm,
  then uses `attach` to stash them in a @{const "container"} within
  the thm.

  Returns a tuple containing the variables and type variables which were attached this way.
\<close>
fun annotate_with_vars_using (attach: Proof.context -> term list -> thm -> thm) ctxt thm =
  let
    val tvars = type_vars_of_term (Thm.prop_of thm) |> map TVar
    val tvar_carriers = map (fn tvar => Const (@{const_name undefined}, tvar)) tvars
    val vars = vars_of_term (Thm.prop_of thm) |> map Var
    val annotated_rule = attach ctxt (vars @ tvar_carriers) thm
  in ((vars, tvars), annotated_rule) end

val annotate_rule = annotate_with_vars_using attach_rule_annotations
val annotate_proof_state = annotate_with_vars_using attach_proof_annotations

fun split_and_zip_instantiations (vars, tvars) (bounds, insts): instantiations =
  let
    val (var_insts, tvar_insts) = chop (length vars) insts
    val tvar_insts' = map (TermExtras.drop_binders (length bounds) o fastype_of) tvar_insts
  in {
    bounds = bounds,
    terms = vars ~~ var_insts,
    typs = tvars ~~ tvar_insts'
  } end

\<comment>\<open>
  Matches subgoals of the form:

  @{term "\<And>A B C. X \<Longrightarrow> Y \<Longrightarrow> Z \<Longrightarrow> container True data"}

  Extracts the instantiation variables from `?data`, and re-applies the surrounding
  meta abstractions (in this case `\<And>A B C`).
\<close>
fun dest_instantiation_container_subgoal t =
    let
      val (vars, goal) = t |> TermExtras.strip_all
      val goal = goal |> Logic.strip_imp_concl
    in
      case goal of
        @{term_pat "Trueprop (container True ?data)"} =>
            dest_term_container data
            |> map (fn t => Logic.rlist_abs (rev vars, t)) (* reapply variables *)
            |> pair vars
            |> SOME
      | _ => NONE
    end

\<comment>\<open>
  Finds the first subgoal with a @{term container} conclusion. Extracts the data from
  the container and removes the subgoal.
\<close>
fun detach_rule_result_annotations ctxt st =
  let
    val (idx, data) =
        st
        |> Thm.prems_of
        |> Library.get_index dest_instantiation_container_subgoal
        |> OptionExtras.get_or_else (fn () => error "No container subgoal!")
    val st' =
        st
        |> resolve_tac ctxt @{thms elim} (idx + 1)
        |> Seq.hd
  in
    (data, st')
  end

\<comment> \<open>
  Instantiate subterms of a given term, using the supplied var_insts. A
  complication is that to deal with bound variables, lambda terms might have
  been inserted to the instantiations. To handle this, we first generate some
  fresh free variables, apply them to the lambdas, do the substitution,
  re-abstract the frees, and then clean up any inner applications.

  subgoal: @{term "\<And>x::int. foo (\<lambda>a. a::'e) (\<lambda>a. a + x) (0::nat)"},
  rule: @{term "foo ((f::'d \<Rightarrow> 'a \<Rightarrow> 'a) y) (g::'b \<Rightarrow> 'b) (0::'c::zero)"}, and
  instantiations: {bounds: [("x", int)],
                   terms: [(?f, \<lambda>x a b. b), (?g, \<lambda>x a. x + a), (?y, \<lambda>x. ?y x)],
                   typs: [(?'a, 'e), (?'b, int), (?'c, nat)]},
  this leads to
  vars: [("x", int)],
  var_insts: [(?f, \<lambda>a b. b), (?g, \<lambda>a. x + a), (?y, ?y x)]
  subst_free: "foo ((\<lambda>a b. b) (?y x)) (\<lambda>a. a + x) 0"
  absfree: "\<lambda>x. foo ((\<lambda>a b. b) (?y x)) (\<lambda>a. a + x) 0"
  beta_norm: @{term "\<lambda>x. foo (\<lambda>a. a) (\<lambda>a. a + x) 0"}
  abs_all: @{term "\<And>x. foo (\<lambda>a. a) (\<lambda>a. a + x) 0"}
\<close>
fun instantiate_terms ctxt bounds var_insts term =
  let
    val vars = Variable.variant_frees ctxt (term :: map #2 var_insts) bounds
    fun var_inst_beta term term' =
      (term, Term.betapplys (term', map Free vars))
    val var_insts' = map (uncurry var_inst_beta) var_insts
  in term
    |> Term.subst_free var_insts'
    |> fold Term.absfree vars
    |> Envir.beta_norm
    |> TermExtras.abs_all (length bounds)
  end

\<comment> \<open>
  Instantiate subtypes of a given term, using the supplied tvar_insts. Similarly
  to above, to deal with bound variables we first need to drop any binders
  that had been added to the instantiations.
\<close>
fun instantiate_types ctxt _ tvar_insts term =
  let
    fun instantiateT tvar_inst typ =
      let
        val tyenv = Sign.typ_match (Proof_Context.theory_of ctxt) tvar_inst Vartab.empty
        val S = Vartab.dest tyenv
        val S' = map (fn (s,(t,u)) => ((s,t),u)) S
      in Term_Subst.instantiateT (TVars.make S') typ
      end
  in fold (fn typs => Term.map_types (instantiateT typs)) tvar_insts term
  end

\<comment> \<open>
  Instantiate a given thm with the supplied instantiations, returning a term.
\<close>
fun instantiate_thm ctxt thm {bounds, terms, typs} =
  Thm.prop_of thm
  |> instantiate_terms ctxt bounds terms
  |> instantiate_types ctxt (length bounds) typs

fun filtered_instantiation_lines ctxt {bounds, terms, typs} =
  let
    val vars_lines =
        map (fn (var, inst) =>
          if var = inst then "" (* don't show unchanged *) else
              "  " ^ Syntax.string_of_term ctxt var ^ "  =>  " ^
              Syntax.string_of_term ctxt (TermExtras.abs_all (length bounds) inst) ^ "\n")
        terms
    val tvars_lines =
        map (fn (tvar, inst) =>
          if tvar = inst then "" (* don't show unchanged *) else
              "  " ^ Syntax.string_of_typ ctxt tvar ^ "  =>  " ^
              Syntax.string_of_typ ctxt inst ^ "\n")
        typs
  in
    vars_lines @ tvars_lines
  end

\<comment>\<open>
  Default callback for black-box method tracing. Prints nontrivial instantiations to tracing output
  with the given title line.
\<close>
fun default_report ctxt title insts =
  let
    val all_insts = String.concat (filtered_instantiation_lines ctxt insts)
  (* TODO: add a quiet flag, to suppress output when nothing was instantiated *)
  in title ^ "\n" ^ (if all_insts = "" then "  (no instantiations)\n" else all_insts)
     |> tracing
  end

\<comment> \<open>
  Default callback for tracing rule applications. Prints nontrivial
  instantiations to tracing output with the given title line. Separates
  instantiations of rule variables and goal variables.
\<close>
fun default_rule_report ctxt title rule_insts proof_insts =
  let
    val rule_lines = String.concat (filtered_instantiation_lines ctxt rule_insts)
    val rule_lines =
        if rule_lines = ""
        then "(no rule instantiations)\n"
        else "rule instantiations:\n" ^ rule_lines;
    val proof_lines = String.concat (filtered_instantiation_lines ctxt proof_insts)
    val proof_lines =
        if proof_lines = ""
        then "(no goal instantiations)\n"
        else "goal instantiations:\n" ^ proof_lines;
  in title ^ "\n" ^ rule_lines ^ "\n" ^ proof_lines |> tracing  end

\<comment> \<open>
  `trace_schematic_insts_tac ctxt callback tactic thm idx` does the following:

  - Produce a @{term container}-annotated version of `thm`.
  - Runs `tactic` on subgoal `idx`, using the annotated version of `thm`.
  - If the tactic succeeds, call `callback` with the rule instantiations and the goal
    instantiations, in that order.
\<close>
fun trace_schematic_insts_tac
    ctxt
    (callback: instantiations -> instantiations -> unit)
    (tactic: thm -> int -> tactic)
    thm idx st =
  let
    val (rule_vars, annotated_rule) = annotate_rule ctxt thm
    val (proof_vars, annotated_proof_state) = annotate_proof_state ctxt st
    val st = tactic annotated_rule idx annotated_proof_state
  in
    st |> Seq.map (fn st =>
      let
        val (rule_terms, st) = detach_rule_result_annotations ctxt st
        val (proof_terms, st) = detach_proof_annotations st
        val rule_insts = split_and_zip_instantiations rule_vars rule_terms
        val proof_insts = split_and_zip_instantiations proof_vars ([], proof_terms)
        val () = callback rule_insts proof_insts
      in
        st
      end
    )
  end

\<comment>\<open>
  ML interface, calls the supplied function with schematic unifications
  (will be given all variables, including those that haven't been instantiated).
\<close>
fun trace_schematic_insts (method: Method.method) callback
  = fn facts => fn (ctxt, st) =>
    let
      val (vars, annotated_st) = annotate_proof_state ctxt st
    in (* Run the method *)
      method facts (ctxt, annotated_st)
      |> Seq.map_result (fn (ctxt', annotated_st') => let
            (* Retrieve the stashed list, now with unifications *)
            val (annotations, st') = detach_proof_annotations annotated_st'
            val insts = split_and_zip_instantiations vars ([], annotations)
            (* Report the list *)
            val _ = callback insts
         in (ctxt', st') end)
    end

end
\<close>
end

method_setup trace_schematic_insts = \<open>
  let
    open Trace_Schematic_Insts
  in
    (Scan.option (Scan.lift Parse.liberal_name) -- Method.text_closure) >>
    (fn (maybe_title, method_text) => fn ctxt =>
      trace_schematic_insts
          (Method.evaluate method_text ctxt)
          (default_report ctxt
              (Option.getOpt (maybe_title, "trace_schematic_insts:")))
      |> skip_dummy_state
    )
  end
\<close> "Method combinator to trace schematic variable and type instantiations"

end
