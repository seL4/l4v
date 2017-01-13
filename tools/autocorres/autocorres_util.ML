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
 * Common code for all translation phases: defining funcs, calculating dependencies,
 * variable fixes, etc.
 *)

(*
 * Here is a brief explanation of how most AutoCorres phases work
 * with each other.
 *
 * AutoCorres's phases are L1, L2, HL, WA and TS. (TS doesn't share these
 * utils for historical reasons; fixing that is another story.)
 * Basically, each of L1, L2, HL and WA:
 *   1. takes a list of input function specs;
 *   2. converts each function individually;
 *   3. defines each new function (or recursive function group).
 *      This updates the local theory sequentially;
 *   4. proves monad_mono theorems and places them into the
 *      output list of functions;
 *   5. outputs a list of new function specs in the original format.
 *
 * === Concurrency ===
 * To support concurrent processing better, we do not use lists.
 * Instead, we use a future-chained sequence (FSeq, below) so that
 * define and convert steps can be done in parallel (up to the
 * dependencies between them, of course).
 *
 * (We do not use a plain list of futures because a define
 * step may produce one or more function groups, so we can't
 * know how many groups there will be in advance. See the
 * recursive group splitting comment for define_funcs_sequence.)
 *
 * Additionally, AutoCorres is structured so that conversions
 * do not require the most up-to-date local theory, so we also
 * output a stream of intermediate local theories. This allows
 * conversions of phase N+1 to be pipelined with define steps of
 * phase N.
 *
 * FunctionInfo.phase_results is the uniform sequence type that
 * most AutoCorres translation phases adhere to.
 *
 * === (2) Conversion ===
 * Converting a function starts by assuming correspondence theorems
 * for all the functions that it calls (including itself, if
 * recursive). We invent free variables to stand for those functions;
 * see assume_called_functions_corres.
 *
 * Because it's fiddly to have these assumptions everywhere,
 * we use Assumption to hide them in the thm hyps during conversion.
 * When done, we export the assumptions using Morphism.thm.
 *
 * After performing these conversions, we get a corres theorem
 * with corres assumptions for called functions (along with other
 * auxillary info). These are generally packaged into a
 * convert_result record.
 *
 * The conversions are all independent, so we launch them in
 * topological order; see par_convert. This is the most convenient
 * because each conversion takes place between the previous and next
 * define step, which already require topological order.
 *
 * === (3) Definition ===
 * We take the sequence of conversion results and define each
 * function (or recursive group) in the theory.
 *
 * Each function group and its convert_results are processed by
 * define_funcs. Conventionally, AutoCorres phases provide a
 * "define" wrapper that sets up the required inputs to define_funcs
 * and constructs function_infos for the newly defined functions.
 *
 * There is also a high-level wrapper, define_funcs_sequence, that
 * calls these "define" wrappers in the correct order.
 * It also splits recursive groups after defining them; see its
 * documentation for details.
 *
 * === (4) Corollaries ===
 * Currently, each phase only proves one type of corollary,
 * monad_mono theorems. These proofs are duplicated in the source
 * of the individual phases (this should be fixed) and do not make
 * use of the utils here.
 *
 * === Incremental mode support ===
 * AutoCorres supports incremental translation, which means that
 * we need to insert previously-translated function data at the
 * appropriate places. The par_convert and define_funcs_sequence
 * wrappers take "existing_foo" arguments and ensure that these
 * are available to the per-phase convert and define steps.
 *)

structure AutoCorresUtil =
struct

(*
 * Maximum time to let an individual function translation phase to run for.
 *
 * Note that this is wall time, and not CPU time, so it is a very rough
 * tool.
 * FIXME: convert to proper option
 *)
val max_run_time = Unsynchronized.ref NONE
(*
val max_run_time = Unsynchronized.ref (SOME (seconds 900.0))
*)

exception AutocorresTimeout of string list

fun time_limit f v =
  case !max_run_time of
    SOME t =>
      (Timeout.apply t f ()
      handle Timeout.TIMEOUT _ =>
        raise AutocorresTimeout v)
  | NONE =>
      f ()

(* Should we use concurrency? *)
val concurrent = Unsynchronized.ref true;

(*
 * Conditionally fork a group of tasks, depending on the value
 * of "concurrent".
 *)
fun maybe_fork f = if !concurrent then Future.fork f else Future.value (f ());

(*
 * Get functions called by a particular function.
 *
 * We split the result into standard calls and recursive calls (i.e., calls
 * which may recursively call back into us).
 *)
fun get_callees fn_infos fn_name =
let
  val fn_info = the (Symtab.lookup fn_infos fn_name)
in
  (Symset.dest (#callees fn_info), Symset.dest (#rec_callees fn_info))
end

(* Measure variables are currently hardcoded as nats. *)
val measureT = @{typ nat};

(*
 * Assume theorems for called functions.
 *
 * A new context is returned with the assumptions in it, along with a morphism
 * used for exporting the theorems out, and a list of the functions assumed:
 *
 *   (<function name>, (<is_mutually_recursive>, <function free>, <arg frees>, <function thm>))
 *
 * In this context, the theorems refer to functions by fixed free variables.
 *
 * get_fn_args may return user-friendly argument names that clash with other names.
 * We will process these names to avoid conflicts.
 *
 * get_fn_assumption should produce the desired theorems to assume. Its arguments:
 *   context (with fixed vars), callee name, callee term, arg terms, is recursive, measure term
 * (all terms are fixed free vars).
 *
 * get_const_name generates names for the free function placeholders.
 * FIXME: probably unnecessary and/or broken.
 *
 * We return a morphism that exposes the assumptions and generalises over the
 * assumed constants.
 * FIXME: automatically generalising over the assumed free variables is
 * probably broken. Instead, the caller should manually generalise and
 * instantiate the frees to avoid clashes.
 *)
fun assume_called_functions_corres ctxt callees rec_callees
    get_fn_type get_fn_assumption get_fn_args get_const_name callers_measure_var =
let
  (* Assume the existence of a function, along with a theorem about its
   * behaviour. *)
  fun assume_func ctxt fn_name is_recursive_call =
  let
    val fn_args = get_fn_args fn_name

    (* Fix a variable for the function. *)
    val ([fixed_fn_name], ctxt') = Variable.variant_fixes [get_const_name fn_name] ctxt
    val fn_free = Free (fixed_fn_name, get_fn_type fn_name)

    (* Fix a variable for the measure and function arguments. *)
    val (measure_var_name :: arg_names, ctxt'')
        = Variable.variant_fixes ("rec_measure'" :: (map fst fn_args)) ctxt'
    val fn_arg_terms = map (fn (n, T) => Free (n, T)) (arg_names ~~ (map snd fn_args))
    val my_measure_var = Free (measure_var_name, @{typ nat})

    (*
     * A measure variable is needed to handle recursion: for recursive calls,
     * we need to decrement the caller's input measure value (and our
     * assumption will need to assume this to). This is so we can later prove
     * termination of our function definition: the measure always reaches zero.
     *
     * Non-recursive calls can have a fresh value.
     *)
    val measure_var =
      if is_recursive_call then
        @{const "recguard_dec"} $ callers_measure_var
      else
        my_measure_var

    (* Create our assumption. *)
    val assumption =
        get_fn_assumption ctxt'' fn_name fn_free fn_arg_terms
            is_recursive_call measure_var
        |> fold Logic.all (rev ((if is_recursive_call then [] else [my_measure_var]) @ fn_arg_terms))
        |> Sign.no_vars ctxt'
        |> Thm.cterm_of ctxt'
    val ([thm], ctxt''') = Assumption.add_assumes [assumption] ctxt'

    (* Generate a morphism for escaping this context. *)
    val m = (Assumption.export_morphism ctxt''' ctxt')
        $> (Variable.export_morphism ctxt' ctxt)
  in
    (fn_free, thm, ctxt''', m)
  end

  (* Add assumptions: recursive calls first, matching the order in define_functions *)
  val (res, (ctxt', m)) = fold_map (
    fn (fn_name, is_recursive_call) =>
      fn (ctxt, m) =>
        let
          val (free, thm, ctxt', m') =
              assume_func ctxt fn_name is_recursive_call
        in
          ((fn_name, (is_recursive_call, free, thm)), (ctxt', m' $> m))
        end)
    (map (fn f => (f, false)) (Symset.dest callees) @
     map (fn f => (f, true)) (Symset.dest rec_callees))
    (ctxt, Morphism.identity)
in
  (ctxt', m, res)
end

(* Determine which functions are called by a code fragment.
 * Only function terms in callee_consts are used. *)
fun get_body_callees
      (callee_consts: string Termtab.table)
      (body: term)
      : symset =
  Term.fold_aterms (fn t => fn a =>
      (Termtab.lookup callee_consts t
          |> Option.map single
          |> the_default []) @ a)
      body []
  |> Symset.make;

(* Determine which recursive calls are actually used by a code fragment.
 * This is used to make adjustments to recursive function groups
 * between conversion and definition steps.
 *
 * callee_terms is a list of (is_recursive, func const, thm)
 * as provided by assume_called_functions_corres *)
fun get_rec_callees
      (callee_terms: (string * (bool * term * thm)) list)
      (body: term)
      : symset = let
    val callee_lookup =
          callee_terms |> List.mapPartial (fn (callee, (is_rec, const, _)) =>
              if is_rec then SOME (const, callee) else NONE)
          |> Termtab.make;
    in get_body_callees callee_lookup body end;

(*
 * Given one or more function specs, define them and instantiate corres proofs.
 *
 *   "callee_thms" contains corres theorems for already-defined functions.
 *
 *   "fn_infos" is used to look up function callees. It is expected
 *   to consist of the previous translation output for the functions
 *   being defined, but may of course contain other entries.
 *
 *   "functions" contains a list of (fn_name, (body, corres proof, arg_frees)).
 *   The body should be of the form generated by abstract_fn_body,
 *   with lambda abstractions for all callees and arguments.
 *
 *   The given corres proof is expected to use the free variables in
 *   arg_frees for the function's arguments (including the measure variable,
 *   if there if there is one). It is also expected to use schematic
 *   variables for assumed callees.
 *   (FIXME: this interface should be simplified a bit.)
 *
 *   We assume that all functions in this list are mutually recursive.
 *   (If not, you should call "define_funcs" multiple times, each
 *   time with a single function.)
 *
 * Returns the new function constants, definitions, final corres proofs,
 * and local theory.
 *)
fun define_funcs
    (phase : FunctionInfo.phase)
    (filename : string)
    (fn_infos : FunctionInfo.function_info Symtab.table)
    (get_const_name : string -> string)
    (get_fn_type : string -> typ)
    (get_fn_assumption : Proof.context -> string -> term -> term list -> bool -> term -> term)
    (get_fn_args : string -> (string * typ) list)
    (rec_base_case : thm)
    (ctxt : Proof.context)
    (callee_thms : thm Symtab.table)
    (functions : (string * (term * thm * (string * typ) list)) list)
  : (term * thm * thm) Symtab.table * Proof.context =
  let
    val fn_names = map fst functions
    val fn_bodies = map (snd #> #1) functions
    (* Generalise over the function arguments *)
    val fn_thms = map (snd #> (fn (_, thm, frees) =>
                        (Thm.generalize ([], map fst frees) (Thm.maxidx_of thm + 1) thm)))
                      functions

    val _ = writeln ("Defining (" ^ FunctionInfo.string_of_phase phase ^ ") " ^
                     (Utils.commas (map get_const_name fn_names)))

    (*
     * Determine if we are in a recursive case by checking to see if the
     * first function in our list makes recursive calls to any other
     * function. (This "other function" will be itself if it is simple
     * recursion, but may be a different function if we are mutually
     * recursive.)
     *)
    val is_recursive = FunctionInfo.is_function_recursive (the (Symtab.lookup fn_infos (hd fn_names)))
    val _ = assert (length fn_names = 1 orelse is_recursive)
            "define_funcs passed multiple functions, but they don't appear to be recursive."

    (*
     * Patch in functions into our function body in the following order:
     *
     *    * Non-recursive calls;
     *    * Recursive calls
     *)
    fun fill_body fn_name body =
    let
      val fn_info = the (Symtab.lookup fn_infos fn_name)
      val non_rec_calls = map (fn x => Utils.get_term ctxt (get_const_name x)) (Symset.dest (#callees fn_info))
      val rec_calls = map (fn x => Free (get_const_name x, get_fn_type x)) (Symset.dest (#rec_callees fn_info))
    in
      body
      |> (fn t => betapplys (t, non_rec_calls))
      |> (fn t => betapplys (t, rec_calls))
    end

    (*
     * Define our functions.
     *
     * Definitions should be of the form:
     *
     *    %arg1 arg2 arg3. (arg1 + arg2 + arg3)
     *
     * Mutually recursive calls should be of the form "Free (fn_name, fn_type)".
     *)
    val defs = map (
        fn (fn_name, fn_body) => let
            val fn_args = get_fn_args fn_name
            (* FIXME: this retraces assume_called_functions_corres *)
            val (fn_free :: measure_free :: arg_frees, _) = Variable.variant_fixes
                    (get_const_name fn_name :: "rec_measure'" :: map fst fn_args) ctxt
            in (get_const_name fn_name, (* be inflexible when it comes to fn_name *)
                (measure_free, @{typ nat}) :: (arg_frees ~~ map snd fn_args), (* changing arg names is ok *)
                fill_body fn_name fn_body) end)
        (fn_names ~~ fn_bodies)
    val (fn_def_thms, ctxt) = Utils.define_functions defs true is_recursive ctxt

    (*
     * Instantiate schematic function calls in our theorems with their
     * concrete definitions.
     *)
    val combined_callees = map (get_callees fn_infos) (map fst functions)
    val combined_normal_calls =
        map fst combined_callees |> flat |> sort_distinct fast_string_ord
    val combined_recursive_calls =
        map snd combined_callees |> flat |> sort_distinct fast_string_ord
    val callee_terms =
        (combined_recursive_calls @ combined_normal_calls)
        |> map (fn x => (get_const_name x, Utils.get_term ctxt (get_const_name x)))
        |> Symtab.make
    fun fill_proofs thm =
      Utils.instantiate_thm_vars ctxt
        (fn ((name, _), _) =>
          Symtab.lookup callee_terms name
          |> Option.map (Thm.cterm_of ctxt)) thm
    val fn_thms = map fill_proofs fn_thms

    (* Fix free variable for the measure. *)
    val ([measure_var_name], ctxt') = Variable.variant_fixes ["m"] ctxt
    val measure_var = Free (measure_var_name, @{typ nat})

    (* Generate corres predicates for each function. *)
    val preds = map (
      fn fn_name =>
      let
        fun mk_forall v t = HOLogic.all_const (Term.fastype_of v) $ lambda v t
        val fn_const = Utils.get_term ctxt' (get_const_name fn_name)

        (* Fetch parameters to this function. *)
        val free_params =
            get_fn_args fn_name
            |> Variable.variant_frees ctxt' [measure_var]
            |> map Free
      in
        (* Generate the prop. *)
          get_fn_assumption ctxt' fn_name fn_const
              free_params is_recursive measure_var
          |> fold Logic.all (rev free_params)
      end) fn_names

    (* We generate a goal which solves all the mutually recursive calls simultaneously. *)
    val goal = map (Object_Logic.atomize_term ctxt') preds
        |> Utils.mk_conj_list
        |> HOLogic.mk_Trueprop
        |> Thm.cterm_of ctxt'

    (* Prove each of the predicates above, leaving any assumptions about called
     * functions unsolved. *)
    val pred_thms = map (
        fn (pred, thm, body_def) =>
          Thm.trivial (Thm.cterm_of ctxt' pred)
          |> Utils.apply_tac "unfold body" (Hypsubst.stac ctxt' body_def 1)
          |> Utils.apply_tac "apply rule" (resolve_tac ctxt' [thm] 1)
          |> Goal.norm_result ctxt
          |> singleton (Variable.export ctxt' ctxt)
        )
        (Utils.zip3 preds fn_thms fn_def_thms)

    (* Create a set of "helper theorems", which should be sufficient to discharge
     * all assumptions that our callees refine. *)
    val helper_thms =
        (map (Symtab.lookup callee_thms #> the) combined_normal_calls) @ pred_thms
        |> map (Drule.forall_intr_vars)
        |> map (Conv.fconv_rule (Object_Logic.atomize ctxt))

    (* Generate a proof term of equivalence using the folded definitions. *)
    val new_thm =
      Goal.init goal
      |> (fn thm =>
        if is_recursive then (
          Utils.apply_tac "start induction"
                (resolve_tac ctxt'
                    [Utils.named_cterm_instantiate ctxt'
                        [("n", Thm.cterm_of ctxt' measure_var)] @{thm recguard_induct}]
                    1) thm
          |> Utils.apply_tac "unfold bodies"
              (EVERY (map (fn x => (EqSubst.eqsubst_tac ctxt' [1] [x] 1)) (rev fn_def_thms)))
          |> Utils.apply_tac "solve induction base cases"
              (SOLVES ((simp_tac (put_simpset HOL_ss ctxt' addsimps [rec_base_case]) 1)))
          |> Utils.apply_tac "solve remaining goals"
              (Utils.metis_insert_tac ctxt helper_thms 1)
        ) else (
          Utils.apply_tac "solve remaining goals"
                    (Utils.metis_insert_tac ctxt helper_thms 1) thm
        ))
      |> Goal.finish ctxt'

    (*
     * The proof above is of the form (L1corres a & L1corres b & ...).
     * Split it up into several proofs.
     *)
    fun prove_partial_corres thm pred =
      Thm.cterm_of ctxt' pred
      |> Goal.init
      |> Utils.apply_tac "solving using metis" (Utils.metis_tac ctxt [thm] 1)
      |> Goal.finish ctxt'

    (* Generate the final theorems. *)
    val new_thms =
        map (prove_partial_corres new_thm) preds
        |> (Variable.export ctxt' ctxt)
        |> map (Goal.norm_result ctxt)

    val results =
          fn_names ~~ (new_thms ~~ fn_def_thms)
          |> map (fn (fn_name, (corres_thm, def_thm)) =>
                    (* FIXME: ugly way to get the function constant *)
                    (fn_name, (Utils.get_term ctxt (get_const_name fn_name), def_thm, corres_thm)))
          |> Symtab.make;
  in
    (results, ctxt)
  end

(* Support function for incremental translation.
 * This updates #callees of the functions we are translating, to include
 * background functions that have already been translated.
 * (We don't need to handle #rec_callees because recursive groups
 * cannot be translated piecemeal.) *)
fun add_background_callees
      (background: FunctionInfo.function_info Symtab.table)
      : FunctionInfo.function_info Symtab.table ->
        FunctionInfo.function_info Symtab.table = let
  val bg_consts =
        Symtab.dest background
        |> map (fn (f, bg_info) => (#raw_const bg_info, f))
        |> Termtab.make;
  in Symtab.map (K (fn fn_info => let
       val bg_callees = get_body_callees bg_consts (Thm.prop_of (#definition fn_info));
       in FunctionInfo.function_info_upd_callees (Symset.union (#callees fn_info) bg_callees) fn_info end))
  end;

(* Utility for doing conversions in parallel.
 * The conversion of each function f should depend only on the previous
 * define phase for f (which necessarily also includes f's callees). *)
type convert_result = {
       body: term, (* new body *)
       proof: thm, (* corres thm *)
       rec_callees: symset, (* minimal rec_callees after translation *)
       callee_consts: term Symtab.table, (* assumed frees for other callees *)
       arg_frees: (string * typ) list, (* fixed argument frees, including measure *)
       traces: (string * AutoCorresData.Trace) list (* traces *)
     }
fun par_convert
      (* Worker: lthy -> function_infos for func and callees -> func name -> results *)
      (convert: local_theory -> FunctionInfo.function_info Symtab.table ->
                string -> convert_result)
      (* Functions from prior incremental translation *)
      (existing_infos: FunctionInfo.function_info Symtab.table)
      (* Functions from previous phase *)
      (prev_results: FunctionInfo.phase_results)
      (* Add traces from the conversion result. *)
      (add_trace: string -> string -> AutoCorresData.Trace -> unit)
      (* Return converted functions in recursive groups.
       * The groups are tagged with fn_infos from prev_results to identify them. *)
      : (FunctionInfo.function_info Symtab.table * convert_result Symtab.table) FSeq.fseq =
    (* Knowing that prev_results is in topological order,
     * we accumulate its function_infos, which will be a superset
     * of the callee infos that each conversion requires. *)
    FSeq.fold_map (fn fn_infos_accum => fn (lthy, fn_infos) => let
           val fn_infos = add_background_callees existing_infos fn_infos;
           val fn_infos_accum = Symtab.merge (K false) (fn_infos_accum, fn_infos);
           (* Convert fn_infos in parallel, but join the results right away.
            * This is fine because we will define them together. *)
           val conv_results =
                 Symtab.dest fn_infos
                 |> Par_List.map (fn (f, _) =>
                      (f, convert lthy fn_infos_accum f))
                 |> Symtab.make;
           val _ = app (fn (f, result) => app (fn (typ, trace) =>
                                add_trace f typ trace) (#traces result))
                       (Symtab.dest conv_results);
           in ((fn_infos, conv_results), fn_infos_accum) end)
        existing_infos prev_results;

(* Given a function body containing arguments and assumed function calls,
 * abstract the code over those parameters.
 *
 * The returned body will have free variables as placeholders for the function's
 * measure parameter and other arguments, as well as for the functions it calls.
 *
 * We modify the body to be of the form:
 *
 *     %fun1 fun2 rec1 rec2 measure arg1 arg2. f <...>
 *
 * That is, all non-recursive calls are abstracted out the front, followed by
 * recursive calls, followed by the measure variable, followed by function
 * arguments. This is the format expected by define_funcs.
 *)
fun abstract_fn_body
      (prev_fn_infos: FunctionInfo.function_info Symtab.table)
      (fn_name, {body, callee_consts, arg_frees, ...} : convert_result) = let
  val (callees, rec_callees) = get_callees prev_fn_infos fn_name;
  val calls = map (the o Symtab.lookup callee_consts) callees;
  val rec_calls = map (the o Symtab.lookup callee_consts) rec_callees;

  val abs_body = body
        |> fold lambda (rev (map Free arg_frees))
        |> fold lambda (rev rec_calls)
        |> fold lambda (rev calls);
  in abs_body end;

(* Utility for defining functions.
 *
 * Definitions update the theory sequentially.
 * Each definition step produces a lthy that contains the current function
 * group, and can immediately be used in the next conversion phase for
 * those functions. Hence we return the intermediate lthys as futures.
 *
 * The actual recursive function groups may be finer-grained than in
 * converted_groups, as function calls can be removed by dead code
 * elimination and other transformations. Hence we detect the actual
 * function groups after defining them. *)
fun define_funcs_sequence
      (lthy: local_theory)
      (define_worker: local_theory ->
                      (* previous infos for functions *)
                      FunctionInfo.function_info Symtab.table ->
                      (* new infos for callees *)
                      FunctionInfo.function_info Symtab.table ->
                      (* data for functions *)
                      convert_result Symtab.table ->
                      (* new infos for functions *)
                      FunctionInfo.function_info Symtab.table * local_theory)
      (* previous infos from prior translation (in incremental mode) *)
      (existing_infos: FunctionInfo.function_info Symtab.table)
      (* functions defined so far, initially populated from prior translation *)
      (defined_so_far: FunctionInfo.function_info Symtab.table)
      (converted_groups: (FunctionInfo.function_info Symtab.table *
                          convert_result Symtab.table) FSeq.fseq)
      : FunctionInfo.phase_results = FSeq.mk (fn () =>
    case FSeq.uncons converted_groups of
        NONE => NONE
      | SOME ((prev_infos, conv_group), remaining_groups) => SOME let
        (* NB: we don't need to add_background_callees to prev_infos because
         *     par_convert already does that *)
        (* Define the function group, then split into minimal recursive groups. *)
        val (new_infos, lthy') =
               define_worker lthy (Symtab.merge (K false) (prev_infos, existing_infos))
                             defined_so_far conv_group;
        (* Minimise callees and split recursive group if needed. *)
        val new_infoss = FunctionInfo.recalc_callees defined_so_far new_infos;
        val defined_so_far = Symtab.merge (K false) (defined_so_far, new_infos);
        (* We can't wrap the first result because we're already in FSeq.mk.
         * Fortunately, one is guaranteed to exist *)
        val new_infos1 :: new_infoss = new_infoss;
       (* Output new group(s) in the result sequence. *)
        val remaining_results =
              define_funcs_sequence lthy' define_worker
                                    existing_infos defined_so_far remaining_groups;
        in
           ((lthy', new_infos1),
            FSeq.append
              (FSeq.of_list (map (fn defs => (lthy', defs)) new_infoss))
              remaining_results)
        end);

end
