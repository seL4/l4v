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
 * Rewrite L2 specifications to use "nat" and "int" data-types instead of
 * "word" data types. The former tend to be easier to reason about.
 *
 * The main interface to this module is translate (and inner functions
 * convert and define). See AutoCorresUtil for a conceptual overview.
 *)

structure WordAbstract =
struct

(* Maximum depth that we will go before assuming that we are diverging. *)
val WORD_ABS_MAX_DEPTH = 200

(* Convenience shortcuts. *)
val warning = Utils.ac_warning
val apply_tac = Utils.apply_tac
val the' = Utils.the'

type WARules = {
     ctype : typ, atype : typ,
     abs_fn : term, inv_fn : term,
     rules : thm list
}

fun mk_word_abs_rule T =
{
  ctype = fastype_of (@{mk_term "x :: (?'W::len) word" ('W)} T),
  atype = @{typ nat},
  abs_fn = @{mk_term "unat :: (?'W::len) word => nat" ('W)} T,
  inv_fn = @{mk_term "of_nat :: nat => (?'W::len) word" ('W)} T,
  rules = @{thms word_abs_word}
}

val word_abs : WARules list =
    map mk_word_abs_rule [@{typ 32}, @{typ 16}, @{typ 8}]

fun mk_sword_abs_rule T =
{
  ctype = fastype_of (@{mk_term "x :: (?'W::len) signed word" ('W)} T),
  atype = @{typ int},
  abs_fn = @{mk_term "sint :: (?'W::len) signed word => int" ('W)} T,
  inv_fn = @{mk_term "of_int :: int => (?'W::len) signed word" ('W)} T,
  rules = @{thms word_abs_sword}
}

val sword_abs : WARules list =
    map mk_sword_abs_rule [@{typ 32}, @{typ 16}, @{typ 8}]

(* Get abstract version of a HOL type. *)
fun get_abs_type (rules : WARules list) T =
    Option.getOpt
        (List.find (fn r => #ctype r = T) rules
         |> Option.map (fn r => #atype r),
         T)

(* Get abstraction function for a HOL type. *)
fun get_abs_fn (rules : WARules list) T =
    Option.getOpt
        (List.find (fn r => #ctype r = T) rules
         |> Option.map (fn r => #abs_fn r),
         @{mk_term "id :: ?'a => ?'a" ('a)} T)

fun get_abs_inv_fn (rules : WARules list) t =
    Option.getOpt
        (List.find (fn r => #ctype r = fastype_of t) rules
         |> Option.map (fn r => #inv_fn r $ t),
         t)

(*
 * From a list of abstract arguments to a function, derive a list of
 * concrete arguments and types and a precondition that links the two.
 *)
fun get_wa_conc_args rules l2_infos fn_name fn_args lthy =
let
  (* Construct arguments for the concrete body. We use the abstract names
   * with a prime ('), but with the concrete types. *)
  val args0 = the (Symtab.lookup l2_infos fn_name) |> #args;
  val conc_types = map snd args0;
  val (conc_names, lthy) = Variable.variant_fixes (map (fn Free (n, T) => n ^ "'") fn_args) lthy;
  val conc_args = map Free (conc_names ~~ conc_types)
  val arg_pairs = (conc_args ~~ fn_args)

  (* Create preconditions that link the new types to the old types. *)
  val precond =
      map (fn (old, new) => @{mk_term "abs_var ?n ?f ?o" (o, f, n)}
          (old, get_abs_fn rules (fastype_of old), new))
          arg_pairs
      |> Utils.mk_conj_list
in
  (conc_types, conc_args, precond, arg_pairs, lthy)
end

(* Get the expected type of a function from its name. *)
fun get_expected_fn_type rules l2_infos fn_name =
let
  val fn_info = the (Symtab.lookup l2_infos fn_name)
  val fn_params_typ = map ((get_abs_type rules) o snd) (#args fn_info)
  val fn_ret_typ = get_abs_type rules (#return_type fn_info)
  val globals_typ = LocalVarExtract.dest_l2monad_T (fastype_of (#const fn_info)) |> snd |> #1
  val measure_typ = @{typ "nat"}
in
  (measure_typ :: fn_params_typ)
      ---> LocalVarExtract.mk_l2monadT globals_typ fn_ret_typ @{typ unit}
end

(* Get the expected theorem that will be generated about a function. *)
fun get_expected_fn_thm rules l2_infos ctxt fn_name
                        function_free fn_args _ measure_var =
let
  val old_def = the (Symtab.lookup l2_infos fn_name)
  val (old_arg_types, old_args, precond, arg_pairs, ctxt)
      = get_wa_conc_args rules l2_infos fn_name fn_args ctxt

  val old_term = betapplys (#const old_def, measure_var :: old_args)
  val new_term = betapplys (function_free, measure_var :: fn_args)
in
  @{mk_term "Trueprop (corresTA (%x. ?P) ?rt id ?A ?C)" (rt, A, C, P)}
      (get_abs_fn rules (#return_type old_def), new_term, old_term, precond)
  |> fold (fn t => fn v => Logic.all t v) (rev (map fst arg_pairs))
end

(* Get arguments passed into the function. *)
fun get_expected_fn_args rules l2_infos fn_name =
  map (apsnd (get_abs_type rules)) (#args (the (Symtab.lookup l2_infos fn_name)))

(*
 * Convert a theorem of the form:
 *
 *    corresTA (%_. abs_var True a f a' \<and> abs_var True b f b' \<and> ...) ...
 *
 * into
 *
 *   [| abstract_val A a f a'; abstract_val B b (f b') |] ==> corresTA (%_. A \<and> B \<and> ...) ...
 *
 * the latter of which better suits our resolution approach of proof
 * construction.
 *)
fun extract_preconds_of_call thm =
let
  fun r thm =
    r (thm RS @{thm corresTA_extract_preconds_of_call_step})
    handle THM _ => (thm RS @{thm corresTA_extract_preconds_of_call_final}
    handle THM _ => thm RS @{thm corresTA_extract_preconds_of_call_final'});
in
  r (thm RS @{thm corresTA_extract_preconds_of_call_init})
end


(* Convert a program by abstracting words. *)
fun translate
      (filename: string)
      (prog_info: ProgramInfo.prog_info)
      (* Note that we refer to the previous phase as "l2"; it may be
       * from the L2 or HL phase. *)
      (l2_results: FunctionInfo.phase_results)
      (existing_l2_infos: FunctionInfo.function_info Symtab.table)
      (existing_wa_infos: FunctionInfo.function_info Symtab.table)
      (unsigned_abs: Symset.key Symset.set)
      (no_signed_abs: Symset.key Symset.set)
      (trace_funcs: string list)
      (do_opt: bool)
      (trace_opt: bool)
      (add_trace: string -> string -> AutoCorresData.Trace -> unit)
      (wa_function_name: string -> string)
      : FunctionInfo.phase_results =
if FSeq.null l2_results then FSeq.empty () else
let
  (*
   * Select the rules to translate each function.
   *)
  fun rules_for fn_name =
      (if Symset.contains unsigned_abs fn_name then word_abs else []) @
      (if Symset.contains no_signed_abs fn_name then [] else sword_abs)

  (* Convert each function. *)
  fun convert lthy l2_infos f: AutoCorresUtil.convert_result =
  let
    val old_fn_info = the (Symtab.lookup l2_infos f);
    val wa_rules = rules_for f;

    (* Fix measure variable. *)
    val ([measure_var_name], lthy) = Variable.variant_fixes ["rec_measure'"] lthy;
    val measure_var = Free (measure_var_name, AutoCorresUtil.measureT);

    (* Add callee assumptions. *)
    val (lthy, export_thm, callee_terms) =
      AutoCorresUtil.assume_called_functions_corres lthy
        (#callees old_fn_info) (#rec_callees old_fn_info)
        (fn f => get_expected_fn_type (rules_for f) l2_infos f)
        (fn lthy => fn f => get_expected_fn_thm (rules_for f) l2_infos lthy f)
        (fn f => get_expected_fn_args (rules_for f) l2_infos f)
        wa_function_name
        measure_var;

    (* Fix argument variables. *)
    val new_fn_args = get_expected_fn_args wa_rules l2_infos f;
    val (arg_names, lthy) = Variable.variant_fixes (map fst new_fn_args) lthy;
    val arg_frees = map Free (arg_names ~~ map snd new_fn_args);

    (* Construct free variables to represent our concrete arguments. *)
    val (conc_types, conc_args, precond, arg_pairs, lthy)
        = get_wa_conc_args wa_rules l2_infos f arg_frees lthy

    (* Fetch the function definition, and instantiate its arguments. *)
    val old_body_def =
        #definition old_fn_info
        (* Instantiate the arguments. *)
        |> Utils.inst_args lthy (map (Thm.cterm_of lthy) (measure_var :: conc_args))

    (* Get old body definition with function arguments. *)
    val old_term = betapplys (#const old_fn_info, measure_var :: conc_args)

    (* Get a schematic variable accepting new arguments. *)
    val new_var = betapplys (
        Var (("A", 0), get_expected_fn_type wa_rules l2_infos f), measure_var :: arg_frees)

    (* Fetch monotonicity theorems of callees. *)
    val callee_mono_thms =
        Symset.dest (FunctionInfo.all_callees old_fn_info)
        |> List.mapPartial (fn callee =>
               if FunctionInfo.is_function_recursive (the (Symtab.lookup l2_infos callee))
               then the (Symtab.lookup l2_infos callee) |> #mono_thm
               else NONE)

    (*
     * Generate a schematic goal.
     *
     * We only want ?A to depend on abstracted variables and ?C to depend on
     * concrete variables. We force this by applying bound variables to each
     * of the schematics, giving us something like:
     *
     *     !!a a' b b'. corresTA ... (?A a b) (?C a' b')
     *
     * The abstract side will hence be prevented from capturing (i.e., using)
     * concrete variables, and vice-versa.
     *)
    val goal = @{mk_term "Trueprop (corresTA (%x. ?precond) ?ra id ?A ?C)" (ra, A, C, precond)}
            (get_abs_fn wa_rules (#return_type old_fn_info), new_var, old_term, precond)
        |> fold (fn t => fn v => Logic.all t v) (rev (arg_frees @ map fst arg_pairs))
        |> Thm.cterm_of lthy
        |> Goal.init
        |> Utils.apply_tac "move precond to assumption" (resolve_tac lthy @{thms corresTA_precond_to_asm} 1)
        |> Utils.apply_tac "split precond" (REPEAT (CHANGED (eresolve_tac lthy @{thms conjE} 1)))
        |> Utils.apply_tac "create schematic precond" (resolve_tac lthy @{thms corresTA_precond_to_guard} 1)
        |> Utils.apply_tac "unfold RHS" (CHANGED (Utils.unfold_once_tac lthy (Utils.abs_def lthy old_body_def) 1))

    (*
     * Fetch rules from the theory.
     * FIXME: move this out of convert?
     *)
    val rules = Utils.get_rules lthy @{named_theorems word_abs}
                @ List.concat (map #rules wa_rules)
                @ @{thms word_abs_default}
    val fo_rules = [@{thm abstract_val_fun_app}]

    val rules = rules @ (map (snd #> #3 #> extract_preconds_of_call) callee_terms)
                      @ callee_mono_thms

    (* Standard tactics. *)
    fun my_rtac ctxt thm n =
        Utils.trace_if_success ctxt thm (
          DETERM (EVERY' (resolve_tac ctxt [thm] :: replicate (Rule_Cases.get_consumes thm) (assume_tac ctxt)) n))

    (* Apply a conversion to the abstract/concrete side of the given "abstract_val" term. *)
    fun wa_conc_body_conv conv =
      Conv.params_conv (~1) (K (Conv.concl_conv (~1) ((Conv.arg_conv (Utils.nth_arg_conv 4 conv)))))

    (* Tactics and conversions for converting goals into first-order format. *)
    fun to_fo_tac ctxt =
        CONVERSION (Drule.beta_eta_conversion then_conv wa_conc_body_conv (HeapLift.mk_first_order ctxt) ctxt)
    fun from_fo_tac ctxt =
        CONVERSION (wa_conc_body_conv (HeapLift.dest_first_order ctxt then_conv Drule.beta_eta_conversion) ctxt)
    fun make_fo_tac tac ctxt = ((to_fo_tac ctxt THEN' tac) THEN_ALL_NEW from_fo_tac ctxt)


    (*
     * Recursively solve subgoals.
     *
     * We allow backtracking in order to solve a particular subgoal, but once a
     * subgoal is completed we don't ever try to solve it in a different way.
     *
     * This allows us to try different approaches to solving subgoals,
     * hopefully reducing exponential explosion (of many different combinations
     * of "good solutions") once we hit an unsolvable subgoal.
     *)

    (*
     * Eliminate a lambda term in the concrete state, but only if the
     * lambda is "real".
     *
     * That is, we don't attempt to eta-expand in order to apply the theorem
     * "abstract_val_lambda", because that may lead to an infinite loop with
     * "abstract_val_fun_app".
     *)
    fun lambda_tac n thm =
      case Logic.concl_of_goal (Thm.prop_of thm) n of
        (Const (@{const_name "Trueprop"}, _) $
            (Const (@{const_name "abstract_val"}, _) $ _ $ _ $ _ $ (
                Abs (_, _, _)))) =>
                    resolve_tac lthy @{thms abstract_val_lambda} n thm
      | _ => no_tac thm

    (* All tactics we try, in the order we should try them. *)
    val step_tacs =
        [(@{thm imp_refl}, assume_tac lthy 1)]
        @ (map (fn thm => (thm, my_rtac lthy thm 1)) rules)
        @ (map (fn thm => (thm, make_fo_tac (my_rtac lthy thm) lthy 1)) fo_rules)
        @ [(@{thm abstract_val_lambda}, lambda_tac 1)]
        @ [(@{thm reflexive},
            fn thm =>
            (if Config.get lthy ML_Options.exception_trace then
              warning ("Could not solve subgoal: " ^
                (Goal_Display.string_of_goal lthy thm))
            else (); no_tac thm))]

    (* Solve the goal. *)
    val replay_failure_start = 1
    val replay_failures = Unsynchronized.ref replay_failure_start
    val (thm, trace) =
        case AutoCorresTrace.maybe_trace_solve_tac lthy (member (op =) trace_funcs f) true false
                 (K step_tacs) goal (SOME WORD_ABS_MAX_DEPTH) replay_failures of
           NONE => (* intentionally generate a TRACE_SOLVE_TAC_FAIL *)
                   (AutoCorresTrace.trace_solve_tac lthy false false (K step_tacs) goal NONE (Unsynchronized.ref 0);
                    (* never reached *) error "word_abstract fail tac: impossible")
         | SOME (thm, [trace]) => (Goal.finish lthy thm, trace)
    val _ = if !replay_failures < replay_failure_start then
              @{trace} (f ^ " WA: reverted to slow replay " ^
                        Int.toString(replay_failure_start - !replay_failures) ^ " time(s)") else ()

    (* Clean out any final function application ($) constants or "id" constants
     * generated by some rules. *)
    fun corresTA_abs_conv conv =
      Utils.remove_meta_conv (fn ctxt => Utils.nth_arg_conv 4 (conv ctxt)) lthy

    val thm =
      Conv.fconv_rule (
        corresTA_abs_conv (fn ctxt =>
          (HeapLift.dest_first_order ctxt)
          then_conv (Simplifier.rewrite (
                put_simpset HOL_basic_ss ctxt addsimps [@{thm id_def}]))
          then_conv Drule.beta_eta_conversion
        )
      ) thm

    (* Ensure no schematics remain in the goal. *)
    val _ = Sign.no_vars lthy (Thm.prop_of thm)

    (*
     * Instantiate abstract function's meta-forall variables with their actual values.
     *
     * That is, we go from:
     *
     *    !!a b c a' b' c'. corresTA (P a b c) ...
     *
     * to
     *
     *    !!a' b' c'. corresTA (P a b c) ...
     *)
    val thm = Drule.forall_elim_list (map (Thm.cterm_of lthy) arg_frees) thm

    (* Apply peephole optimisations to the theorem. *)
    val _ = writeln ("Simpifying (WA) " ^ f)
    val (thm, opt_traces) = L2Opt.cleanup_thm_tagged lthy thm (if do_opt then 0 else 2) 4 trace_opt "WA"

    (* We end up with an unwanted L2_guard outside the L2_recguard.
     * L2Opt should simplify the condition to (%_. True) even if (not do_opt),
     * so we match the guard and get rid of it here. *)
    val thm = Simplifier.rewrite_rule lthy @{thms corresTA_simp_trivial_guard} thm

    (* Convert all-quantified vars in the concrete body to schematics. *)
    val thm = Variable.gen_all lthy thm

    (* Extract the abstract term out of a corresTA thm. *)
    fun dest_corresTA_term_abs @{term_pat "corresTA _ _ _ ?t _"} = t
    val f_body =
        Thm.concl_of thm
        |> HOLogic.dest_Trueprop
        |> dest_corresTA_term_abs;

    (* Get actual recursive callees *)
    val rec_callees = AutoCorresUtil.get_rec_callees callee_terms f_body;

    (* Return the constants that we fixed. This will be used to process the returned body. *)
    val callee_consts =
          callee_terms |> map (fn (callee, (_, const, _)) => (callee, const)) |> Symtab.make;
  in
    { body = f_body,
      proof = Morphism.thm export_thm thm,
      rec_callees = rec_callees,
      callee_consts = callee_consts,
      arg_frees = map dest_Free (measure_var :: arg_frees),
      traces = (if member (op =) trace_funcs f
                then [("WA", AutoCorresData.RuleTrace trace)] else []) @ opt_traces
    }
  end

  (* Define a previously-converted function (or recursive function group).
   * lthy must include all definitions from wa_callees. *)
  fun define
        (lthy: local_theory)
        (l2_infos: FunctionInfo.function_info Symtab.table)
        (wa_callees: FunctionInfo.function_info Symtab.table)
        (funcs: AutoCorresUtil.convert_result Symtab.table)
        : FunctionInfo.function_info Symtab.table * local_theory = let
    val funcs' = Symtab.dest funcs |>
          map (fn result as (name, {proof, arg_frees, ...}) =>
                     (name, (AutoCorresUtil.abstract_fn_body l2_infos result,
                             proof, arg_frees)));
    val (new_thms, lthy') =
          AutoCorresUtil.define_funcs
              FunctionInfo.WA filename l2_infos wa_function_name
              (fn f => get_expected_fn_type (rules_for f) l2_infos f)
              (fn lthy => fn f => get_expected_fn_thm (rules_for f) l2_infos lthy f)
              (fn f => get_expected_fn_args (rules_for f) l2_infos f)
              @{thm corresTA_recguard_0}
              lthy (Symtab.map (K #corres_thm) wa_callees)
              funcs';
    val new_infos = Symtab.map (fn f_name => fn (const, def, corres_thm) => let
          val old_info = the (Symtab.lookup l2_infos f_name);
          in old_info
             |> FunctionInfo.function_info_upd_phase FunctionInfo.WA
             |> FunctionInfo.function_info_upd_const const
             |> FunctionInfo.function_info_upd_definition def
             |> FunctionInfo.function_info_upd_corres_thm corres_thm
             |> FunctionInfo.function_info_upd_return_type
                    (get_abs_type (rules_for f_name) (#return_type old_info))
             |> FunctionInfo.function_info_upd_args
                    (map (apsnd (get_abs_type (rules_for f_name))) (#args old_info))
             |> FunctionInfo.function_info_upd_mono_thm NONE (* added later *)
          end) new_thms;
    in (new_infos, lthy') end;

  (* Do conversions in parallel. *)
  val converted_groups = AutoCorresUtil.par_convert convert existing_l2_infos l2_results add_trace;

  (* Sequence of intermediate states: (lthy, new_defs) *)
  val def_results = FSeq.mk (fn _ =>
        (* If there's nothing to translate, we won't have a lthy to use *)
        if FSeq.null l2_results then NONE else
          let (* Get initial lthy from end of L2 defs *)
              val (l2_lthy, _) = FSeq.list_of l2_results |> List.last;
              val results = AutoCorresUtil.define_funcs_sequence
                              l2_lthy define existing_l2_infos existing_wa_infos converted_groups;
          in FSeq.uncons results end);

  (* Produce a mapping from each function group to its L1 phase_infos and the
   * earliest intermediate lthy where it is defined. *)
  val results =
        def_results
        |> FSeq.map (fn (lthy, f_defs) => let
              (* Add monad_mono proofs. These are done in parallel as well
               * (though in practice, they already run pretty quickly). *)
              val mono_thms = if FunctionInfo.is_function_recursive (snd (hd (Symtab.dest f_defs)))
                              then LocalVarExtract.l2_monad_mono lthy f_defs
                              else Symtab.empty;
              val f_defs' = f_defs |> Symtab.map (fn f =>
                    FunctionInfo.function_info_upd_mono_thm (Symtab.lookup mono_thms f));
              in (lthy, f_defs') end);
in results end;

end
