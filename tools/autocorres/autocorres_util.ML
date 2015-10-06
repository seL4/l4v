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
 * High-level use of AutoCorres
 *)
signature AUTOCORRES_UTIL =
sig
  val translate :
        local_theory
        -> FunctionInfo.fn_info
        -> (local_theory -> string -> 'a)
        -> (local_theory -> 'b Symtab.table -> 'c -> (string * 'a) list -> ('b list * 'c * local_theory))
        -> ((term * thm) list -> local_theory -> thm list)
        -> (local_theory -> 'c -> FunctionInfo.function_def -> FunctionInfo.function_def)
        -> 'c -> (local_theory * FunctionInfo.fn_info * 'c)

  val do_translation_phase :
        string -> string (* phase name, source file name *)
        -> ProgramInfo.prog_info -> FunctionInfo.fn_info
        (* generate fn type *)
        -> (string -> typ)
        (* generate fn assumption : ctxt -> fn_name -> free -> args -> recursive ->
                                    measure -> assm *)
        -> (Proof.context -> string -> term -> term list -> bool -> term -> term)
        (* generate fn args *)
        -> (string -> (string * typ) list)
        (* generate fn name *)
        -> (string -> string)
        (* convert : ctxt -> fn_name -> callee_terms -> measure -> args -> (fn, corres_thm, trace option)
           [ callee_terms : (recursive, callee, corres_thm) table ] *)
        -> (Proof.context -> string -> ((bool * term * thm) Symtab.table)
            -> term -> term list -> (term * thm * (string * AutoCorresData.Trace) list))
        (* prove_mono : (fn_term, fn_def) list -> ctxt -> mono_thms *)
        -> ((term * thm) list -> Proof.context -> thm list)
        (* update function info *)
        -> (local_theory -> FunctionInfo.function_def -> FunctionInfo.function_def)
        (* recursion basecase *)
        -> thm
        -> Proof.context
        (* result *)
        -> (Proof.context * FunctionInfo.fn_info)

  val map_all : Proof.context -> FunctionInfo.fn_info -> (string -> 'a) -> 'a list
  val concurrent : bool Unsynchronized.ref
  val has_simpl_body_def : local_theory -> string -> bool
  val max_run_time : Time.time option Unsynchronized.ref
end;

structure AutoCorresUtil : AUTOCORRES_UTIL =
struct

(*
 * Maximum time to let an individual function translation phase to run for.
 *
 * Note that this is wall time, and not CPU time, so it is a very rough
 * tool.
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
datatype 'a maybe_fork = Future of 'a future | Boring of 'a

(* Fork a group of tasks. *)
fun maybe_fork ctxt vals =
  if ((!concurrent) andalso not (Config.get ctxt ML_Options.exception_trace)) then
    map Future (Future.forks {
        name = "", group = NONE, deps = [], pri = ~1, interrupts = true}
      vals)
  else
    map (fn x => Boring (x ())) vals

(* Ensure a forked task has completed. *)
fun maybe_join v =
  case v of
    Boring x => x
  | Future x => Future.join x

(* Functional map. *)
fun par_map ctxt f a =
  if ((!concurrent) andalso not (Config.get ctxt ML_Options.exception_trace)) then
    Par_List.map f a
  else
    map f a

(* Does a SIMPL body exist for the given function name? *)
fun has_simpl_body_def lthy name =
  try (fn name => Proof_Context.get_thm lthy (name ^ "_body_def")) name
  |> is_some


(*
 * A translation step transforms the program from one form to another;
 * such as from SIMPL to a monadic type, or from one type of monad to
 * another.
 *
 * "filename" is the name of the file we are translating: this is required as a
 * key to fetch data stashed away by the C parser.
 *
 * "lthy" is the local theory.
 *
 * "convert" performs any proof work required for this translation step. All
 * conversions are performed in parallel, so must be able to be completed
 * without results from previous steps.
 *
 * "define" actually sets up any definitions required by the translation;
 * definition steps occur serially, but may be in parallel with conversion
 * steps whose results are not yet required.
 *
 * "prove_mono" should prove the monad_mono property for recursive functions.
 * (* It is run in parallel over all recursive groups. *)
 *
 * Because functions handed to us by the C parser may be mutually recursive and
 * such mutually recursive functions must typically be defined simultaneously,
 * "define" is handed a list of functions which must all be defined in one
 * step.
 *)
fun translate lthy fn_info convert define prove_mono fn_def_translate v =
  let
    (* Get list of functions we need to translate. *)
    val function_groups = FunctionInfo.get_topo_sorted_functions fn_info
    val all_functions = List.concat function_groups

    (*
     * Convert every function.
     *
     * We perform the conversions using futures, which are run in parallel.
     * This allows us to perform conversions while we start defining functions,
     * hopefully speeding everything up on multicore systems.
     *)
    val converted_body_thms =
        map (fn name => fn _ =>
                time_limit (fn _ => convert lthy name) [name]) all_functions
        |> maybe_fork lthy
    val converted_bodies = Symtab.make (all_functions ~~ converted_body_thms)

    (* In sorted order, define constants and proofs for the functions. *)
    fun translate fn_names (callee_thms, new_fn_defs, v, lthy) =
      let
        val defs = map (fn fn_name =>
            Symtab.lookup converted_bodies fn_name |> the |> maybe_join) fn_names
        val (proofs, v, lthy)
            = time_limit (fn _ =>
                define lthy callee_thms v (fn_names ~~ defs)) fn_names
        val new_callee_thms = fold Symtab.update_new
            (fn_names ~~ proofs) callee_thms
        val new_fn_defs = fold (fn n =>
            Symtab.update_new (n, fn_def_translate lthy v (FunctionInfo.get_function_def fn_info n)))
            fn_names new_fn_defs
      in
        (new_callee_thms, new_fn_defs, v, lthy)
      end

    val (proof_table, new_fn_defs, v, lthy)
        = fold translate function_groups (Symtab.empty, Symtab.empty, v, lthy)

    val mono_thms =
        function_groups
        |> map (fn funcs => if not (FunctionInfo.is_function_recursive fn_info (hd funcs))
                  then K [] else (fn _ => time_limit (fn _ =>
                      List.mapPartial (Symtab.lookup new_fn_defs) funcs
                      |> (fn fn_defs => prove_mono (map #const fn_defs ~~
                                                    map #definition fn_defs) lthy)
                      |> (fn thms => funcs ~~ thms)) funcs))
        |> maybe_fork lthy |> map maybe_join
        |> List.concat |> Symtab.make

    val new_fn_defs =
        Symtab.map (fn func => fn fn_def =>
            case Symtab.lookup mono_thms func of
                NONE => fn_def
              | SOME thm => FunctionInfo.fn_def_update_mono_thm thm fn_def) new_fn_defs
  in
    (lthy, FunctionInfo.map_fn_info (fn x => Symtab.lookup new_fn_defs (#name x)) fn_info, v)
  end

(*
 * A translation step that maps over every function in the program.
 *
 * "convert" performs any proof work required for this translation step. All
 * conversions are performed in parallel, so must be able to be completed
 * without results from previous steps.
 *
 * We return a list of all results.
 *)
fun map_all ctxt fn_info convert =
  par_map ctxt convert (FunctionInfo.get_functions fn_info |> Symtab.keys)

(*
 * Get functions called by a particular function.
 *
 * We split the result into standard calls and recursive calls (i.e., calls
 * which may recursively call back into us).
 *)
fun get_callees fn_info fn_name =
let
  (* Get a list of functions we call. *)
  val all_callees = FunctionInfo.get_function_callees fn_info fn_name

  (* Fetch calls that may recursively call back to us. *)
  val recursive_calls = FunctionInfo.get_recursive_group fn_info fn_name

  (* Remove "recursive_calls" from the standard callee set. *)
  val callees =
      Symset.make all_callees
      |> Symset.subtract (Symset.make recursive_calls)
      |> Symset.dest
in
  (callees, recursive_calls)
end

(* Is the given term a Trueprop? *)
fun is_Trueprop (Const (@{const_name "Trueprop"}, _) $ _) = true
  | is_Trueprop _ = false

(*
 * Assume the existence of the given list of functions.
 *
 * A new context is returned with the assumptions in it, along with a morphism
 * used for exporting the theorems out, and a list of the functions assumed:
 *
 *   (<function name>, (<is_mutually_recursive>, <function free>, <function thm>))
 *)
fun assume_called_functions_corres ctxt fn_info callees
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

  (* Apply each assumption. *)
  val (res, (ctxt', m)) = fold_map (
    fn (fn_name, is_recursive_call) =>
      fn (ctxt, m) =>
        let
          val (free, thm, ctxt', m') =
              assume_func ctxt fn_name is_recursive_call
        in
          ((fn_name, (is_recursive_call, free, thm)), (ctxt', m' $> m))
        end)
    callees (ctxt, Morphism.identity)
in
  (ctxt', m, res)
end

(*
 * Convert a single function.
 *
 * Given a single concrete function, abstract that function and
 * return a theorem that shows the correspondence.
 *
 * A theorem is returned which has assumptions that called functions
 * correspond, giving a goal that this given function corresponds.
 *)
fun gen_corres_for_function
    (phase : string)
    (fn_info : FunctionInfo.fn_info)
    (get_fn_type : string -> typ)
    (get_fn_assumption : Proof.context -> string -> term -> term list -> bool -> term -> term)
    (get_fn_args : string -> (string * typ) list)
    (get_const_name : string -> string)
    (convert : Proof.context -> string -> ((bool * term * thm) Symtab.table) ->
               term -> term list -> (term * thm * (string * AutoCorresData.Trace) list))
    (ctxt : Proof.context)
    (fn_name : string) =
let
  val _ = writeln ("Converting (" ^ phase ^") " ^ fn_name)
  val start_time = Timer.startRealTimer ()

  (* Get a list of functions we call. *)
  val (normal_calls, recursive_calls)
      = get_callees fn_info fn_name
  val callees =
      (map (fn x => (x, false)) normal_calls)
      @ (map (fn x => (x, true)) recursive_calls)

  (* Fix a measure variable that will be used to track recursion progress. *)
  val ([measure_var_name], ctxt') = Variable.variant_fixes ["rec_measure'"] ctxt
  val measure_var = Free (measure_var_name, @{typ nat})
  val measure_var_morph = Variable.export_morphism ctxt' ctxt

  (* Fix variables for function arguments. *)
  val fn_args = get_fn_args fn_name
  val (arg_names, ctxt'')
      = Variable.variant_fixes (map (fn (a, _) => a ^ "'arg") fn_args) ctxt'
  val fn_arg_terms = map (fn (n, T) => Free (n, T)) (arg_names ~~ (map snd fn_args))
  val fn_args_morph = Variable.export_morphism ctxt'' ctxt'

  (* Enter a context where we assume our callees exist. *)
  val (ctxt''', m, callee_info_and_proofs)
      = assume_called_functions_corres ctxt'' fn_info callees
            get_fn_type get_fn_assumption get_fn_args get_const_name
            measure_var

  (*
   * Do the conversion.  We receive a new monadic version of the SIMPL
   * term and a tactic for proving correspondence.
   *)
  val callee_tab = Symtab.make callee_info_and_proofs
  val (body, thm, trace) = convert ctxt''' fn_name callee_tab measure_var fn_arg_terms

  (*
   * The returned body will have free variables as placeholders for the function's
   * input parameters, for the functions it calls, and for its measure variable.
   *
   * We modify the body to be of the form:
   *
   *     %fun1 fun2 rec1 rec2 measure arg1 arg2. f <...>
   *
   * That is, all non-recursive calls are abstracted out the front, followed by
   * recursive calls, followed by the measure variable, followed by function
   * arguments.
   *)
  val body =
    fold lambda (rev fn_arg_terms) body
    |> lambda measure_var
    |> fold lambda (rev (map (fn x => Symtab.lookup callee_tab x |> the |> #2) recursive_calls))
    |> fold lambda (rev (map (fn x => Symtab.lookup callee_tab x |> the |> #2) normal_calls))
 
  (* Export the theorem out of our context. *)
  val exported_thm = Morphism.thm (m $> fn_args_morph $> measure_var_morph) thm

  (* TODO: allow this message to be configured *)
  val _ = @{trace} ("Converted (" ^ phase ^ ") " ^ fn_name ^ " in " ^
                    Time.toString (Timer.checkRealTimer start_time) ^ " s")
in
  (exported_thm, body, trace)
end

(*
 * Given a SIMPL function, define a constant and a proof for it.
 *
 *   "callee_thms" contains a table mapping function names to complete
 *   corres proofs for those functions.
 *
 *   "functions" contains a list of (fn_name, (proof, callees)). We
 *   assume that all functions in this list are mutually recursive. (If
 *   not, you should call "define_funcs" multiple times, each
 *   time with a single function.)
 *
 * This code is quite complex in order to support mutual recursion,
 * where function definitions and proofs must simultaneously take place
 * for several functions: if we were only supporting non-recursive
 * functions, life would be easier.
 *)
fun define_funcs
    (phase : string)
    (filename : string)
    (fn_info : FunctionInfo.fn_info)
    (get_const_name : string -> string)
    (get_fn_type : string -> typ)
    (get_fn_assumption : Proof.context -> string -> term -> term list -> bool -> term -> term)
    (get_fn_args : string -> (string * typ) list)
    (rec_base_case : thm)
    (ctxt : Proof.context)
    (callee_thms : thm Symtab.table)
    _
    (functions : (string * (thm * term * (string * AutoCorresData.Trace) list)) list)
    =
  let
    val fn_names = map fst functions
    val fn_thms = map (snd #> #1) functions
    val fn_bodies = map (snd #> #2) functions
    val fn_traces = map (fn (fn_name, (_, _, traces)) => map (fn (module, trace) => (module, fn_name, trace)) traces) functions |> List.concat

    val _ = writeln ("Defining (" ^ phase ^ ") " ^ (Utils.commas (map get_const_name fn_names)))

    (*
     * Determine if we are in a recursive case by checking to see if the
     * first function in our list makes recursive calls to any other
     * function. (This "other function" will be itself if it is simple
     * recursion, but may be a different function if we are mutually
     * recursive.)
     *)
    val is_recursive = FunctionInfo.is_function_recursive fn_info (hd fn_names)
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
      val (normal_calls, recursive_calls)
          = get_callees fn_info fn_name
      val non_rec_calls = map (fn x => Utils.get_term ctxt (get_const_name x)) normal_calls
      val rec_calls = map (fn x => Free (get_const_name x, get_fn_type x)) recursive_calls
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
        fn (fn_name, fn_body) =>
            (get_const_name fn_name,
              ("rec_measure'", @{typ nat}) :: get_fn_args fn_name,
              fill_body fn_name fn_body))
        (fn_names ~~ fn_bodies)
    val (fn_def_thms, ctxt) = Utils.define_functions defs true is_recursive ctxt

    (* Record the constant in our theory data. *)
    val ctxt = fold (fn (fn_name, def) =>
        Local_Theory.background_theory (
            AutoCorresData.add_def filename (phase ^ "def") fn_name def))
        (Utils.zip fn_names fn_def_thms) ctxt

    (*
     * Instantiate schematic function calls in our theorems with their
     * concrete definitions.
     *)
    val combined_callees = map (get_callees fn_info) (map fst functions)
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
          |> Utils.apply_tac "apply rule" (rtac thm 1)
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
                (rtac (@{thm recguard_induct} WHERE [
                    ("n", Thm.cterm_of ctxt' measure_var)]) 1) thm
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
    fun prove_partial_l1_corres thm pred =
      Thm.cterm_of ctxt' pred
      |> Goal.init
      |> Utils.apply_tac "solving using metis" (Utils.metis_tac ctxt [thm] 1)
      |> Goal.finish ctxt'

    (* Generate the final theorems. *)
    val new_thms =
        map (prove_partial_l1_corres new_thm) preds
        |> (Variable.export ctxt' ctxt)
        |> map (Goal.norm_result ctxt)

    (* Record the theorems in our theory data. *)
    val ctxt = fold (fn (fn_name, thm) =>
        Local_Theory.background_theory
          (AutoCorresData.add_thm filename (phase ^ "corres") fn_name thm))
        (fn_names ~~ new_thms) ctxt

    (* Add the theorems to the context. *)
    val ctxt = fold (fn (fn_name, thm) =>
        Utils.define_lemma (fn_name ^ "_" ^ phase ^ "corres") thm #> snd)
        (fn_names ~~ new_thms) ctxt

    (* Add the traces to the context. *)
    val ctxt = Local_Theory.background_theory
                 (fold (fn (phase, fn_name, trace) =>
                          AutoCorresData.add_trace filename phase fn_name trace) fn_traces) ctxt
  in
    (new_thms, (), ctxt)
  end

(*
 * Do a translation phase, converting every function from one form to another.
 *)
fun do_translation_phase
    (phase : string)
    (filename : string)
    (prog_info : ProgramInfo.prog_info)
    (fn_info : FunctionInfo.fn_info)
    (get_fn_type : string -> typ)
    (get_fn_assumption : Proof.context -> string -> term -> term list -> bool -> term -> term)
    (get_fn_args : string -> (string * typ) list)
    (get_const_name : string -> string)
    (convert : Proof.context -> string -> ((bool * term * thm) Symtab.table) ->
               term -> term list -> (term * thm * (string * AutoCorresData.Trace) list))
    (prove_mono : (term * thm) list -> Proof.context -> thm list)
    (update_fn_info : Proof.context -> FunctionInfo.function_def -> FunctionInfo.function_def)
    (rec_base_case : thm)
    (ctxt : Proof.context) =
let
  val do_gen_corres =
    gen_corres_for_function phase fn_info get_fn_type get_fn_assumption
        get_fn_args get_const_name convert;
  val do_define_funcs =
    define_funcs phase filename fn_info get_const_name get_fn_type
        get_fn_assumption get_fn_args rec_base_case

  (* Do the translation. *)
  val (ctxt', new_fn_info, _) = translate ctxt fn_info do_gen_corres do_define_funcs prove_mono
      (fn lthy => K (update_fn_info lthy)) ()

  (* Map function information. *)
in
  (ctxt', new_fn_info)
end

end
