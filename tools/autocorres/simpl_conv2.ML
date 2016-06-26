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
 * Automatically convert SIMPL code fragments into a monadic form, with proofs
 * of correspondence between the two.
 *)
structure SimplConv2 =
struct

(* Convenience shortcuts. *)
val warning = Utils.ac_warning
val apply_tac = Utils.apply_tac
val the' = Utils.the'

exception FunctionNotFound of string

val simpl_conv_ss = AUTOCORRES_SIMPSET

(*
 * Given a function constant name such as "Blah.foo_'proc", guess the underlying
 * function name "foo".
 *)
fun guess_function_name const_name =
  const_name |> unsuffix "_'proc" |> Long_Name.base_name

(* Generate a L1 monad type. *)
fun mk_l1monadT stateT =
  Utils.gen_typ @{typ "'a L1_monad"} [stateT]

(*
 * Extract the L1 monadic term out of a L1corres constant.
 *)
fun get_L1corres_monad @{term_pat "L1corres _ _ ?l1_monad _"} = l1_monad
  | get_L1corres_monad t = raise TERM ("get_L1corres_monad", [t])

(*
 * Generate a SIMPL term that calls the given function.
 *
 * For instance, we might return:
 *
 *   "Call foo_'proc"
 *)
fun mk_SIMPL_call_term ctxt prog_info target_fn =
  @{mk_term "Call ?proc :: (?'s, int, strictc_errortype) com" (proc, 's)}
      (#const target_fn, #state_type prog_info)

(*
 * Construct a correspondence lemma between a given monadic term and a SIMPL fragment.
 *
 * The term is of the form:
 *
 *    L1corres check_termination \<Gamma> monad simpl
 *)
fun mk_L1corres_prop prog_info check_termination monad_term simpl_term =
  @{mk_term "L1corres ?ct ?gamma ?monad ?simpl" (ct, gamma, monad, simpl)}
      (Utils.mk_bool check_termination, #gamma prog_info, monad_term, simpl_term)

(*
 * Construct a prop claiming that the given term is equivalent to
 * a call to the given SIMPL function:
 *
 *    L1corres ct \<Gamma> <term> (Call foo_'proc)
 *
 *)
fun mk_L1corres_call_prop ctxt prog_info check_termination target_fn term =
    mk_L1corres_prop prog_info check_termination term
      (mk_SIMPL_call_term ctxt prog_info target_fn)
    |> HOLogic.mk_Trueprop

(*
 * Convert a SIMPL fragment into a monadic term.
 *
 * We return the monadic version of the input fragment and a tactic
 * to prove correspondence.
 *)
fun simpl_conv'
    (prog_info : ProgramInfo.prog_info)
    (simpl_defs : FunctionInfo2.function_info Symtab.table)
    (simpl_calls : FunctionInfo2.call_graph_info)
    (ctxt : Proof.context)
    (callee_terms : (bool * term * thm) Symtab.table)
    (measure_var : term)
    (simpl_term : term) =
  let
    fun prove_term subterms base_thm result_term =
      let
        val subterms' = map (simpl_conv' prog_info simpl_defs simpl_calls ctxt
                               callee_terms measure_var) subterms;
        val converted_terms = map fst subterms';
        val subproofs = map snd subterms';
        val new_term = (result_term converted_terms);
      in
        (new_term, (resolve_tac ctxt [base_thm] 1) THEN (EVERY subproofs))
      end

    (* Construct a "L1 monad" term with the given arguments applied to it. *)
    fun mk_l1 (Const (a, _)) args =
      Term.betapplys (Const (a, map fastype_of args
          ---> mk_l1monadT (#state_type prog_info)), args)

    (* Convert a set construct into a predicate construct. *)
    fun set_to_pred t =
      (Const (@{const_name L1_set_to_pred},
          fastype_of t --> (HOLogic.dest_setT (fastype_of t) --> @{typ bool})) $ t)
  in
    (case simpl_term of
        (*
         * Various easy cases of SIMPL to monadic conversion.
         *)

        (Const (@{const_name Skip}, _)) =>
          prove_term [] @{thm L1corres_skip}
            (fn _ => mk_l1 @{term "L1_skip"} [])

      | (Const (@{const_name Seq}, _) $ left $ right) =>
          prove_term [left, right] @{thm L1corres_seq}
            (fn [l, r] => mk_l1 @{term "L1_seq"} [l, r])

      | (Const (@{const_name Basic}, _) $ m) =>
          prove_term [] @{thm L1corres_modify}
            (fn _ => mk_l1 @{term "L1_modify"} [m])

      | (Const (@{const_name Cond}, _) $ c $ left $ right) =>
          prove_term [left, right] @{thm L1corres_condition}
            (fn [l, r] => mk_l1 @{term "L1_condition"} [set_to_pred c, l, r])

      | (Const (@{const_name Catch}, _) $ left $ right) =>
          prove_term [left, right] @{thm L1corres_catch}
            (fn [l, r] => mk_l1 @{term "L1_catch"} [l, r])

      | (Const (@{const_name While}, _) $ c $ body) =>
          prove_term [body] @{thm L1corres_while}
            (fn [body] => mk_l1 @{term "L1_while"} [set_to_pred c, body])

      | (Const (@{const_name Throw}, _)) =>
          prove_term [] @{thm L1corres_throw}
            (fn _ => mk_l1 @{term "L1_throw"} [])

      | (Const (@{const_name Guard}, _) $ _ $ c $ body) =>
          prove_term [body] @{thm L1corres_guard}
            (fn [body] => mk_l1 @{term "L1_seq"} [mk_l1 @{term "L1_guard"} [set_to_pred c], body])

      | @{term_pat "lvar_nondet_init _ ?upd"} =>
          prove_term [] @{thm L1corres_init}
            (fn _ => mk_l1 @{term "L1_init"} [upd])

      | (Const (@{const_name Spec}, _) $ s) =>
          prove_term [] @{thm L1corres_spec}
            (fn _ => mk_l1 @{term "L1_spec"} [s])

      | (Const (@{const_name guarded_spec_body}, _) $ _ $ s) =>
          prove_term [] @{thm L1corres_guarded_spec}
            (fn _ => mk_l1 @{term "L1_spec"} [s])

      (*
       * "call": This is primarily what is output by the C parser. We
       * accept input terms of the form:
       *
       *     "call <argument_setup> <proc_to_call> <locals_reset> (%_ s. Basic (<store return value> s))".
       *
       * In particular, the last argument needs to be of precisely the
       * form above. SIMPL, in theory, supports complex expressions in
       * the last argument.  In practice, the C parser only outputs
       * the form above, and supporting more would be a pain.
       *)
      | (Const (@{const_name call}, _) $ a $ (fn_const as Const (b, _)) $ c $ (Abs (_, _, Abs (_, _, (Const (@{const_name Basic}, _) $ d))))) =>
          let
            val state_type = #state_type prog_info
            val target_fn_name = Termtab.lookup (#const_to_function simpl_calls) fn_const
          in
            case Option.mapPartial (Symtab.lookup callee_terms) target_fn_name of
                NONE =>
                (* If no proof of our callee could be found, we emit a call to
                 * "fail". This may happen for functions without bodies. *)
                let
                  val _ = warning ("Function '" ^ guess_function_name b ^ "' contains no body. "
                      ^ "Replacing the function call with a \"fail\" command.")
                in
                  prove_term [] @{thm L1corres_fail} (fn _ => mk_l1 @{term "L1_fail"} [])
                end
              | SOME (is_rec, term, thm) =>
                let
                  (*
                   * If this is an internal recursive call, decrement the measure.
                   * Or if this is calling a recursive function, use measure_call.
                   * If the callee isn't recursive, it doesn't use the measure var
                   * and we can just give an arbitrary value.
                   *)
                  val target_fn_name = (the target_fn_name)
                  val target_fn = Utils.the' ("missing SIMPL def for " ^ target_fn_name)
                                    (Symtab.lookup simpl_defs target_fn_name)
                  val target_rec = FunctionInfo2.is_function_recursive target_fn
                  val term' =
                    if is_rec then
                      term $ (@{term "recguard_dec"} $ measure_var)
                    else if target_rec then
                      @{mk_term "measure_call ?f" f} term
                    else
                      term $ @{term "undefined :: nat"}
                in
                  (* Generate the term. *)
                  (mk_l1 @{term "L1_call"}
                      [a, term', c, absdummy state_type d],
                   resolve_tac ctxt [if is_rec orelse not target_rec then
                                     @{thm L1corres_reccall} else @{thm L1corres_call}] 1
                   THEN resolve_tac ctxt [thm] 1)
                end
          end

      (* TODO : Don't currently support DynCom *)
      | other => Utils.invalid_term "a SIMPL term" other)
  end

(* Perform post-processing on a theorem. *)
fun cleanup_thm ctxt do_opt trace_opt prog_info fn_name thm =
let
  (* Measure the term. *)
  fun gather_stats phase thm =
    Statistics.gather ctxt phase fn_name
        (Thm.concl_of thm |> HOLogic.dest_Trueprop |> get_L1corres_monad)
  val _ = gather_stats "L1" thm

  (* For each function, we want to prepend a statement that sets its return
   * value undefined. It is actually always defined, but our analysis isn't
   * sophisticated enough to realise. *)
  fun prepend_undef thm fn_name =
  let
    val ret_var_name =
        Symtab.lookup (ProgramAnalysis.get_fninfo (#csenv prog_info)) fn_name
        |> the
        |> (fn (ctype, _, _) => NameGeneration.return_var_name ctype |> MString.dest)
    val ret_var_setter = Symtab.lookup (#var_setters prog_info) ret_var_name
    val ret_var_getter = Symtab.lookup (#var_getters prog_info) ret_var_name
    fun try_unify (x::xs) =
      ((x ()) handle THM _ => try_unify xs)
  in
    case ret_var_setter of
        SOME _ =>
          (* Prepend the L1_init code. *)
          Utils.named_cterm_instantiate ctxt
            [("X", Thm.cterm_of ctxt (the ret_var_setter)),
             ("X'", Thm.cterm_of ctxt (the ret_var_getter))]
            (try_unify [
                (fn _ => @{thm L1corres_prepend_unknown_var_recguard} OF [thm]),
                (fn _ => @{thm L1corres_prepend_unknown_var} OF [thm]),
                (fn _ => @{thm L1corres_prepend_unknown_var'} OF [thm])])

          (* Discharge the given proof obligation. *)
          |> simp_tac (put_simpset simpl_conv_ss ctxt) 1 |> Seq.hd
      | NONE => thm
  end
  val thm = prepend_undef thm fn_name

  (* Conversion combinator to apply a conversion only to the L1 subterm of a
   * L1corres term. *)
  fun l1conv conv = (Conv.arg_conv (Utils.nth_arg_conv 3 conv))

  (* Conversion to simplify guards. *)
  fun guard_conv' c =
    case (Thm.term_of c) of
      (Const (@{const_name "L1_guard"}, _) $ _) =>
        Simplifier.asm_full_rewrite (put_simpset simpl_conv_ss ctxt) c
    | _ =>
        Conv.all_conv c
  val guard_conv = Conv.top_conv (K guard_conv') ctxt

  (* Apply all the conversions on the generated term. *)
  val (thm, guard_opt_trace) = AutoCorresTrace.fconv_rule_maybe_traced ctxt (l1conv guard_conv) thm trace_opt
  val (thm, peephole_opt_trace) =
      AutoCorresTrace.fconv_rule_maybe_traced ctxt
          (l1conv (Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps
                     (if do_opt then Utils.get_rules ctxt @{named_theorems L1opt} else []))))
          thm trace_opt
  val _ = gather_stats "L1peep" thm

  (* Rewrite exceptions. *)
  val (thm, exn_opt_trace) = AutoCorresTrace.fconv_rule_maybe_traced ctxt
                                 (l1conv (ExceptionRewrite.except_rewrite_conv ctxt do_opt)) thm trace_opt
  val _ = gather_stats "L1except" thm
in
  (thm,
   [("L1 guard opt", guard_opt_trace), ("L1 peephole opt", peephole_opt_trace), ("L1 exception opt", exn_opt_trace)]
   |> List.mapPartial (fn (n, tr) => case tr of NONE => NONE | SOME x => SOME (n, AutoCorresData.SimpTrace x))
  )
end

(*
 * Get theorems about a SIMPL body in a format convenient to reason about.
 *
 * In particular, we unfold parts of SIMPL where we would prefer to reason
 * about raw definitions instead of more abstract constructs generated
 * by the C parser.
 *)
fun get_simpl_body ctxt simpl_defs fn_name =
let
  (* Find the definition of the given function. *)
  val simpl_thm = #definition (the (Symtab.lookup simpl_defs fn_name))
      handle ERROR _ => raise FunctionNotFound fn_name;

  (* Unfold terms in the body which we don't want to deal with. *)
  val unfolded_simpl_thm =
      Conv.fconv_rule (Utils.rhs_conv
          (Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps
             (Utils.get_rules ctxt @{named_theorems L1unfold}))))
          simpl_thm
  val unfolded_simpl_term = Thm.concl_of unfolded_simpl_thm |> Utils.rhs_of;

  (*
   * Get the implementation definition for this function. These rules are of
   * the form "Gamma foo_'proc = Some foo_body".
   *)
  val impl_thm =
    Proof_Context.get_thm ctxt (fn_name ^ "_impl")
    |> Local_Defs.unfold ctxt [unfolded_simpl_thm]
    |> SOME
    handle (ERROR _) => NONE
in
  (unfolded_simpl_term, unfolded_simpl_thm, impl_thm)
end

fun get_l1corres_thm prog_info simpl_defs simpl_calls check_termination ctxt do_opt trace_opt
                     fn_name callee_terms measure_var = let
  val fn_def = the (Symtab.lookup simpl_defs fn_name);
  val thy = Proof_Context.theory_of ctxt
  val (simpl_term, simpl_thm, impl_thm) = get_simpl_body ctxt simpl_defs fn_name

  (* Fetch stats on pre-converted term. *)
  val _ = Statistics.gather ctxt "CParser" fn_name simpl_term

  (*
   * Do the conversion.  We receive a new monadic version of the SIMPL
   * term and a tactic for proving correspondence.
   *)
  val (monad, tactic) = simpl_conv' prog_info simpl_defs simpl_calls ctxt
                                    callee_terms measure_var simpl_term

  (*
   * Wrap the monad in a "L1_recguard" statement, which triggers
   * failure when the measure reaches zero. This lets us automatically
   * prove termination of the recursive function.
   *)
  val is_recursive = FunctionInfo2.is_function_recursive fn_def
  val (monad, tactic) =
    if is_recursive then
      (Utils.mk_term thy @{term "L1_recguard"} [measure_var, monad],
        (resolve_tac ctxt @{thms L1corres_recguard} 1 THEN tactic))
    else
      (monad, tactic)

  (*
   * Return a new theorem of correspondence between the original
   * SIMPL body (with folded constants) and the output monad term.
   *)
in
  mk_L1corres_call_prop ctxt prog_info check_termination (the (Symtab.lookup simpl_defs fn_name)) monad
  |> Thm.cterm_of ctxt
  |> Goal.init
  |> (case impl_thm of
          NONE     => apply_tac "unfold SIMPL body" (resolve_tac ctxt @{thms L1corres_undefined_call} 1)
        | SOME def => apply_tac "unfold SIMPL body" (resolve_tac ctxt @{thms L1corres_Call} 1 THEN
                                                     resolve_tac ctxt [def] 1)
                      #> apply_tac "solve L1corres" tactic)
  |> Goal.finish ctxt
  (* Apply simplifications to the L1 term. *)
  |> cleanup_thm ctxt do_opt trace_opt prog_info fn_name
end

fun get_body_of_l1corres_thm thm =
   (* Extract the monad from the thm. *)
   Thm.concl_of thm
   |> HOLogic.dest_Trueprop
   |> get_L1corres_monad

fun split_conj thm =
  (thm RS @{thm conjunct1}) :: split_conj (thm RS @{thm conjunct2})
  handle THM _ => [thm]

(* Prove monad_mono for recursive functions. *)
fun l1_monad_mono lthy (l1_defs : FunctionInfo2.function_info Symtab.table) =
let
    val l1_defs' = Symtab.dest l1_defs;
    fun mk_stmt [func] = @{mk_term "monad_mono ?f" f} func
      | mk_stmt (func :: funcs) = @{mk_term "monad_mono ?f \<and> ?g" (f, g)} (func, mk_stmt funcs);
    val mono_thm = @{term "Trueprop"} $ mk_stmt (map (#const o snd) l1_defs');
    val func_expand = map (fn (_, l1_def) =>
          EqSubst.eqsubst_tac lthy [0] [Utils.abs_def lthy (#definition l1_def)]) l1_defs';
    val tac =
        REPEAT (EqSubst.eqsubst_tac lthy [0]
                [@{thm monad_mono_alt_def}, @{thm all_conj_distrib} RS @{thm sym}] 1)
        THEN resolve_tac lthy @{thms allI} 1 THEN resolve_tac lthy @{thms nat.induct} 1
          THEN EVERY (map (fn expand =>
                              TRY (resolve_tac lthy @{thms conjI} 1)
                              THEN expand 1
                              THEN resolve_tac lthy @{thms monad_mono_step_L1_recguard_0} 1) func_expand)
        THEN REPEAT (eresolve_tac lthy @{thms conjE} 1)
        THEN EVERY (map (fn expand =>
                            TRY (resolve_tac lthy @{thms conjI} 1)
                            THEN expand 1
                            THEN REPEAT (FIRST [assume_tac lthy 1,
                                                resolve_tac lthy @{thms L1_monad_mono_step_rules} 1]))
                        func_expand);
in
  Goal.prove lthy [] [] mono_thm (K tac)
  |> split_conj
  |> (fn thms => map fst l1_defs' ~~ thms)
  |> Symtab.make
end


(* For functions that are not translated, just generate a trivial wrapper. *)
fun mk_l1corres_call_simpl_thm check_termination ctxt simpl_def = let
    val const = #const simpl_def
    val impl_thm = Proof_Context.get_thm ctxt (#name simpl_def ^ "_impl")
    val gamma = safe_mk_meta_eq impl_thm |> Thm.concl_of |> Logic.dest_equals
        |> fst |> (fn (f $ _) => f | t => raise TERM ("gamma", [t]))
    val thm = Utils.named_cterm_instantiate ctxt
        [("ct", Thm.cterm_of ctxt (Utils.mk_bool check_termination)),
         ("proc", Thm.cterm_of ctxt const),
         ("Gamma", Thm.cterm_of ctxt gamma)]
        @{thm L1corres_call_simpl}
  in thm end


(*
 * Convert a single function. Returns a thm that looks like
 *   \<lbrakk> L1corres ?callee1 (Call callee1_'proc); ... \<rbrakk> \<Longrightarrow>
 *   L1corres (conversion result...) (Call f_'proc)
 * i.e. with assumptions for called functions, which are parameterised as Vars.
 *)
fun convert
      (lthy: local_theory)
      (prog_info: ProgramInfo.prog_info)
      (simpl_defs: FunctionInfo2.function_info Symtab.table)
      (check_termination: bool)
      (do_opt: bool)
      (trace_opt: bool)
      (l1_function_name: string -> string)
      (f_name: string)
      : thm * symset * (string * typ) list = let
  (* FIXME: refactor? *)
  val (simpl_calls, simpl_defs) = FunctionInfo2.calc_call_graph simpl_defs;

  val f_info = Utils.the' ("SimplConv: missing SIMPL def for " ^ f_name) (Symtab.lookup simpl_defs f_name);
  val callee_names = FunctionInfo2.all_callees f_info;
  (* TODO sanity check:
     - all SIMPL defs exist *)

  val measureT = @{typ nat};

  (* All L1 functions have the same signature: measure \<Rightarrow> L1_monad *)
  val l1_fn_type = measureT --> mk_l1monadT (#state_type prog_info);

  (* L1corres for f's callees. *)
  fun get_l1_fn_assumption ctxt fn_name free _ _ measure_var =
      mk_L1corres_call_prop ctxt prog_info check_termination
          (Utils.the' ("SimplConv: missing callee def for " ^ fn_name)
                      (Symtab.lookup simpl_defs fn_name)) (betapply (free, measure_var));

  (* Fix measure variable. *)
  val ([measure_var_name], lthy') = Variable.variant_fixes ["rec_measure'"] lthy;
  val measure_var = Free (measure_var_name, measureT);

  (* Add callee assumptions. Note that our define code has to use the same assumption order. *)
  val (lthy'', export_thm, callee_terms) =
    AutoCorresUtil2.assume_called_functions_corres lthy'
      (#callees f_info) (#rec_callees f_info)
      (K l1_fn_type)
      get_l1_fn_assumption
      (K [])
      l1_function_name
      measure_var;

  val (thm, opt_traces) =
      if #is_simpl_wrapper f_info
      then (mk_l1corres_call_simpl_thm check_termination lthy'' f_info, [])
      else get_l1corres_thm prog_info simpl_defs simpl_calls check_termination lthy'' do_opt trace_opt f_name
                            (Symtab.make callee_terms) measure_var;

  (* Get actual recursive callees *)
  val callee_consts =
        callee_terms |> List.mapPartial (fn (callee, (is_rec, const, _)) =>
            if is_rec then SOME (const, callee) else NONE)
        |> Termtab.make;
  val rec_callees =
        Term.fold_aterms (fn t => fn a =>
            (Termtab.lookup callee_consts t
                |> Option.map single
                |> the_default []) @ a)
            (get_L1corres_monad (HOLogic.dest_Trueprop (Thm.concl_of thm))) []
          |> Symset.make;

  (* FIXME: return traces *)
  in (Morphism.thm export_thm thm,
      (* Used for recalculating the recursive call graph *)
      rec_callees,
      (* Provide the fixed vars so the user can generalize/instantiate them *)
      [dest_Free measure_var])
  end


(* Define a previously-converted function (or recursive function group).
 * lthy must include all definitions from l1_callees.
 * simpl_defs must include current function set and its immediate callees.  *)
fun define
      (lthy: local_theory)
      (filename: string)
      (prog_info: ProgramInfo.prog_info)
      (simpl_defs: FunctionInfo2.function_info Symtab.table)
      (check_termination: bool)
      (l1_callees: FunctionInfo2.function_info Symtab.table)
      (l1_function_name: string -> string)
      (funcs: (string * thm * (string * typ) list) list) (* name, corres, arg frees *)
      : FunctionInfo2.function_info Symtab.table * local_theory = let
  (* FIXME: dedup with convert *)

  (* All L1 functions have the same signature: measure \<Rightarrow> L1_monad *)
  val measureT = @{typ nat};
  val l1_fn_type = measureT --> mk_l1monadT (#state_type prog_info);

  (* L1corres for f's callees. *)
  fun get_l1_fn_assumption ctxt fn_name free _ _ measure_var =
      mk_L1corres_call_prop ctxt prog_info check_termination
          (the (Symtab.lookup simpl_defs fn_name)) (betapply (free, measure_var));

  (* FIXME: pass this from assume_called_functions_corres, etc. *)
  fun guess_callee_var thm callee = let
    val base_name = l1_function_name callee;
    val mentioned_vars = Term.add_vars (Thm.prop_of thm) [];
    in hd (filter (fn ((v, _), _) => v = base_name) mentioned_vars) end;

  fun prepare_fn_body (fn_name, corres_thm, measure_free) = let
    val @{term_pat "Trueprop (L1corres _ _ ?body _)"} = Thm.concl_of corres_thm;
    val fn_info = the (Symtab.lookup simpl_defs fn_name);
    val calls = map (fn c => Var (guess_callee_var corres_thm c))
                  (Symset.dest (#callees fn_info));
    val recursive_calls = map (fn c => Var (guess_callee_var corres_thm c))
                            (Symset.dest (#rec_callees fn_info));
    (*
     * The returned body will have free variables as placeholders for the function's
     * measure parameter and other arguments, and schematic variables for the functions it calls.
     *
     * We modify the body to be of the form:
     *
     *     %fun1 fun2 rec1 rec2 measure arg1 arg2. f <...>
     *
     * That is, all non-recursive calls are abstracted out the front, followed by
     * recursive calls, followed by the measure variable, followed by function
     * arguments (none for L1). This is the format expected by define_funcs.
     *)
    val abs_body = body
      |> fold lambda (rev (map Free measure_free))
      |> fold lambda (rev recursive_calls)
      |> fold lambda (rev calls);
    in abs_body end;

  val funcs' = funcs |>
        map (fn (name, thm, frees) =>
                   (name, (* FIXME: define_funcs needs this currently *)
                          (Thm.generalize ([], map fst frees) (Thm.maxidx_of thm + 1) thm,
                          prepare_fn_body (name, thm, frees))));
  val _ = @{trace} ("L1.define", map (fn (name, (thm, body)) => (name, thm, Thm.cterm_of lthy body)) funcs');
  val (new_thms, (), lthy') =
        AutoCorresUtil2.define_funcs FunctionInfo2.L1 filename simpl_defs
            l1_function_name (K l1_fn_type) get_l1_fn_assumption (K []) @{thm L1corres_recguard_0}
            lthy (Symtab.map (K #corres_thm) l1_callees) ()
            funcs';
  val new_defs = Symtab.map (fn f_name => fn (const, def, corres_thm) => let
        val f_info = the (Symtab.lookup simpl_defs f_name);
        in f_info
           |> FunctionInfo2.function_info_upd_phase FunctionInfo2.L1
           |> FunctionInfo2.function_info_upd_definition def
           |> FunctionInfo2.function_info_upd_corres_thm corres_thm
           |> FunctionInfo2.function_info_upd_const const
           |> FunctionInfo2.function_info_upd_mono_thm NONE (* done in translate *)
        end) new_thms;
  in (new_defs, lthy') end;


(*
 * Top level translation from SIMPL to a monadic spec.
 *
 * We accept a filename (the same filename passed to the C parser; the
 * parser stashes away important information using this filename as the
 * key) and a local theory.
 *
 * We define a number of new functions (the converted monadic
 * specifications of the SIMPL functions) and theorems (proving
 * correspondence between our generated specs and the original SIMPL
 * code).
 *)
(* FIXME: use AutoCorresUtil.Future instead of default *)
fun translate
      (filename: string)
      (prog_info: ProgramInfo.prog_info)
      (simpl_infos: FunctionInfo2.function_info Symtab.table)
      (check_termination: bool)
      (do_opt: bool)
      (trace_opt: bool)
      (l1_function_name: string -> string)
      (lthy: local_theory)
      : (local_theory * FunctionInfo2.function_info Symtab.table) FSeq.fseq =
let
  val funcs_to_translate = Symtab.keys simpl_infos;

  (* All conversions can run in parallel. *)
  val converted_funcs =
        funcs_to_translate |> map (fn f =>
          (f, Future.fork (fn _ =>
                convert lthy prog_info simpl_infos check_termination do_opt trace_opt l1_function_name f)))
        |> Symtab.make;

  (* Definitions update lthy sequentially.
   * We use the arbitrary (but deterministic) ordering defined by get_topo_sorted_functions.
   * Each definition step produces a lthy that has a prefix of the update sequence,
   * and can be used in an L2 translation that depends only on that prefix.
   * Hence we return the intermediate lthys as futures. *)
  fun add_defs _ _ [] = FSeq.empty ()
    | add_defs lthy defined_so_far (f_names :: next_names) =
        FSeq.fcons (fn () => let
          (* Wait for conversions to finish *)
          val (call_graph, f_convs) =
                map (fn f => let
                      val conv = the' ("didn't convert function: " ^ quote f ^ "??")
                                      (Symtab.lookup converted_funcs f);
                      val (corres_thm, rec_callees, arg_frees) = Future.join conv;
                      in ((f, rec_callees), (f, (corres_thm, arg_frees))) end)
                    f_names
                |> split_list;
          val f_convs = Symtab.make f_convs;

          (* Split this recursive group prior to defining the functions.
           * Function calls can be removed by dead code elimination and other
           * transformations, which could cause the group to split. *)
          val f_callees = Symtab.make (map (apsnd Symset.dest) call_graph);
          (* Add each function to its own callees to get a complete inverse *)
          val f_callers = flip_symtab (Symtab.map cons f_callees);

          val topo_sorted_functions =
                Topo_Sort.topo_sort {
                  cmp = String.compare,
                  graph = Symtab.lookup f_callees #> the,
                  converse = Symtab.lookup f_callers #> the
                } (Symtab.keys f_callees |> sort String.compare)
                |> map Symset.make;

          val f_convss =
                topo_sorted_functions |> map (fn group =>
                    map (fn f => (f, the (Symtab.lookup f_convs f)))
                        (Symset.dest group)
                    |> Symtab.make);

          (* Define each function group and append it to the result sequence. *)
          fun add_subgroup_defs lthy defined_so_far [] =
                add_defs lthy defined_so_far next_names
            | add_subgroup_defs lthy defined_so_far (f_convs :: f_convss) =
                FSeq.fcons (fn () => let
                  val f_convs_list =
                        Symtab.dest f_convs
                        |> map (fn (f, (corres_thm, arg_frees)) => (f, corres_thm, arg_frees));
                  val (new_defs, lthy') =
                      define lthy filename prog_info simpl_infos check_termination
                             defined_so_far l1_function_name f_convs_list;
                  (* Update (non-recursive) callees *)
                  val new_defs = FunctionInfo2.recalc_base_callees defined_so_far new_defs;
                  val defined_so_far' = Symtab.merge (K false) (defined_so_far, new_defs);
                  in ((lthy', new_defs),
                      add_subgroup_defs lthy' defined_so_far' f_convss)
                  end);
          in (* a bit ugly -- may need to tweak the FSeq interface *)
             the (FSeq.uncons (add_subgroup_defs lthy defined_so_far f_convss)) end);

  val (simpl_calls, _) = FunctionInfo2.calc_call_graph simpl_infos;
  val function_groups = #topo_sorted_functions simpl_calls;
  (* Sequence of intermediate results: (lthy, new_defs) *)
  val def_results = add_defs lthy Symtab.empty (map Symset.dest function_groups);

  (* Produce a mapping from each function group to its L1 phase_infos and the
   * earliest intermediate lthy where it is defined. *)
  val results =
        def_results
        |> FSeq.map (fn (lthy, f_defs) => let
              (* Add monad_mono proofs. These are done in parallel as well
               * (though in practice, they already run pretty quickly). *)
              val mono_thms = if FunctionInfo2.is_function_recursive (snd (hd (Symtab.dest f_defs)))
                              then l1_monad_mono lthy f_defs
                              else Symtab.empty;
              val f_defs' = f_defs |> Symtab.map (fn f =>
                              FunctionInfo2.function_info_upd_mono_thm (Symtab.lookup mono_thms f));
              in (lthy, f_defs') end);
in
  results
end

end