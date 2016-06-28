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
 * Common code for all translation phases: defining funcs, calculating dependencies, variable fixes, etc.
 *)

structure AutoCorresUtil2 =
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
      (TimeLimit.timeLimit t f ()
      handle TimeLimit.TimeOut =>
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
 *   "callee_thms" contains a table mapping function names to complete
 *   corres proofs for those functions. At this point, the functions are
 *   still free variables.
 *
 *   "fn_infos" is used to look up function callees. It is expected
 *   to consist of the previous translation output for the functions
 *   being defined, but may of course contain other entries.
 *
 *   "functions" contains a list of (fn_name, (proof, body)).
 *   The body should be of the form generated by gen_corres_for_function,
 *   with lambda abstractions for all callees and arguments.
 *
 *   We assume that all functions in this list are mutually recursive.
 *   (If not, you should call "define_funcs" multiple times, each
 *   time with a single function.)
 *
 * Returns the new function constants, definitions, corres proofs,
 * and local theory.
 *)
fun define_funcs
    (phase : FunctionInfo2.phase)
    (filename : string)
    (fn_infos : FunctionInfo2.function_info Symtab.table)
    (get_const_name : string -> string)
    (get_fn_type : string -> typ)
    (get_fn_assumption : Proof.context -> string -> term -> term list -> bool -> term -> term)
    (get_fn_args : string -> (string * typ) list)
    (rec_base_case : thm)
    (ctxt : Proof.context)
    (callee_thms : thm Symtab.table)
    (accum : 'a) (* translate allows an accumulator, but we don't use it here *)
    (functions : (string * (thm * term)) list)
  : (term * thm * thm) Symtab.table * 'a * Proof.context =
  let
    val fn_names = map fst functions
    val fn_thms = map (snd #> #1) functions
    val fn_bodies = map (snd #> #2) functions

    val _ = writeln ("Defining (" ^ FunctionInfo2.string_of_phase phase ^ ") " ^
                     (Utils.commas (map get_const_name fn_names)))

    (*
     * Determine if we are in a recursive case by checking to see if the
     * first function in our list makes recursive calls to any other
     * function. (This "other function" will be itself if it is simple
     * recursion, but may be a different function if we are mutually
     * recursive.)
     *)
    val is_recursive = FunctionInfo2.is_function_recursive (the (Symtab.lookup fn_infos (hd fn_names)))
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
          |> Utils.apply_tac "solve remaing goals"
              (Utils.metis_insert_tac ctxt helper_thms 1)
        ) else (
          Utils.apply_tac "solve remaing goals"
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
    (results, accum, ctxt)
  end

end
