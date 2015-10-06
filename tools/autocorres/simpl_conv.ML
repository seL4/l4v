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
structure SimplConv =
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
fun get_L1corres_monad (_ $ _ $ monad $ _) = monad

(*
 * Generate a SIMPL term that calls the given function.
 *
 * For instance, we might return:
 *
 *   "Call foo_'proc"
 *)
fun mk_SIMPL_call_term ctxt prog_info fn_info target_fn =
  @{mk_term "Call ?proc :: (?'s, int, strictc_errortype) com" (proc, 's)}
      (FunctionInfo.get_function_def fn_info target_fn |> #const, #state_type prog_info)

(*
 * Construct a correspondence lemma between a given monadic term and a SIMPL fragment.
 *
 * The term is of the form:
 *
 *    L1corres \<Gamma> monad simpl
 *)
fun mk_L1corres_prop prog_info monad_term simpl_term =
  @{mk_term "L1corres ?gamma ?monad ?simpl" (gamma, monad, simpl)}
      (#gamma prog_info, monad_term, simpl_term)

(*
 * Construct a prop claiming that the given term is equivalent to
 * a call to the given SIMPL function:
 *
 *    L1corres \<Gamma> <term> (Call foo_'proc)
 *
 *)
fun mk_L1corres_call_prop ctxt prog_info fn_info target_fn_name term =
    mk_L1corres_prop prog_info term
      (mk_SIMPL_call_term ctxt prog_info fn_info target_fn_name)
    |> HOLogic.mk_Trueprop

(*
 * Convert a SIMPL fragment into a monadic term.
 *
 * We return the monadic version of the input fragment and a tactic
 * to prove correspondence.
 *)
fun simpl_conv'
    (prog_info : ProgramInfo.prog_info)
    (fn_info : FunctionInfo.fn_info)
    (ctxt : Proof.context)
    (callee_terms : (bool * term * thm) Symtab.table)
    (measure_var : term)
    (simpl_term : term) =
  let
    fun prove_term subterms base_thm result_term =
      let
        val subterms' = map (simpl_conv' prog_info fn_info ctxt
                               callee_terms measure_var) subterms;
        val converted_terms = map fst subterms';
        val subproofs = map snd subterms';
        val new_term = (result_term converted_terms);
      in
        (new_term, (rtac base_thm 1) THEN (EVERY subproofs))
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

      | (Const (@{const_name Spec}, _) $ s) =>
          prove_term [] @{thm L1corres_spec}
            (fn _ => mk_l1 @{term "L1_spec"} [s])

      (*
       * "call": This is primarily what is output by the C parser. We
       * accept input terms of the form:
       *
       *     "call <argument_setup> <proc_to_call> <locals_reset> (%_ s. Basic (f s))".
       *
       * In particular, the last argument needs to be of precisely the
       * form above. SIMPL, in theory, supports complex expressions in
       * the last argument.  In practice, the C parser only outputs
       * the form above, and supporting more would be a pain.
       *)
      | (Const (@{const_name call}, _) $ a $ (fn_const as Const (b, _)) $ c $ (Abs (_, _, Abs (_, _, (Const (@{const_name Basic}, _) $ d))))) =>
          let
            val state_type = #state_type prog_info
            val target_fn_name =
                FunctionInfo.get_function_from_const fn_info fn_const
                |> Option.map #name
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
                  val target_rec = FunctionInfo.is_function_recursive fn_info target_fn_name
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
                   rtac (if is_rec orelse not target_rec then
                            @{thm L1corres_reccall} else @{thm L1corres_call}) 1
                   THEN rtac thm 1)
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
          Utils.named_cterm_instantiate
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
  fun l1conv conv = (Conv.arg_conv (Utils.nth_arg_conv 2 conv))

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
          (l1conv (Simplifier.rewrite (put_simpset HOL_basic_ss ctxt
                                       addsimps (if do_opt then L1PeepholeThms.get ctxt else []))))
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
fun get_simpl_body ctxt fn_info fn_name =
let
  (* Find the definition of the given function. *)
  val simpl_thm = #definition (FunctionInfo.get_function_def fn_info fn_name)
      handle ERROR _ => raise FunctionNotFound fn_name;

  (* Unfold terms in the body which we don't want to deal with. *)
  val unfolded_simpl_thm =
      Conv.fconv_rule (Utils.rhs_conv
          (Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps (L1UnfoldThms.get ctxt))))
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

fun get_l1corres_thm prog_info fn_info ctxt do_opt trace_opt fn_name
    callee_terms measure_var = let
  val thy = Proof_Context.theory_of ctxt
  val (simpl_term, simpl_thm, impl_thm) = get_simpl_body ctxt fn_info fn_name

  (* Fetch stats on pre-converted term. *)
  val _ = Statistics.gather ctxt "CParser" fn_name simpl_term

  (*
   * Do the conversion.  We receive a new monadic version of the SIMPL
   * term and a tactic for proving correspondence.
   *)
  val (monad, tactic) = simpl_conv' prog_info fn_info ctxt
                                    callee_terms measure_var simpl_term

  (*
   * Wrap the monad in a "L1_recguard" statement, which triggers
   * failure when the measure reaches zero. This lets us automatically
   * prove termination of the recursive function.
   *)
  val is_recursive = FunctionInfo.is_function_recursive fn_info fn_name
  val (monad, tactic) =
    if is_recursive then
      (Utils.mk_term thy @{term "L1_recguard"} [measure_var, monad],
        (rtac @{thm L1corres_recguard} 1 THEN tactic))
    else
      (monad, tactic)

  (*
   * Return a new theorem of correspondence between the original
   * SIMPL body (with folded constants) and the output monad term.
   *)
in
  mk_L1corres_call_prop ctxt prog_info fn_info fn_name monad
  |> Thm.cterm_of ctxt
  |> Goal.init
  |> apply_tac "unfold SIMPL body"
        (case impl_thm of
            NONE => (rtac @{thm L1corres_undefined_call} 1)
          | SOME thm => ((rtac @{thm L1corres_Call} 1) THEN (rtac thm 1) THEN tactic))
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
fun l1_monad_mono (func_defs : (term * thm) list) lthy =
let
    fun mk_stmt [func] = @{mk_term "monad_mono ?f" f} func
      | mk_stmt (func :: funcs) = @{mk_term "monad_mono ?f \<and> ?g" (f, g)} (func, mk_stmt funcs)
    val mono_thm = @{term "Trueprop"} $ mk_stmt (map #1 func_defs)
    val func_expand = map (fn (_, def) => EqSubst.eqsubst_tac lthy [0] [Utils.abs_def lthy def]) func_defs
    val tac =
        REPEAT (EqSubst.eqsubst_tac lthy [0]
                [@{thm monad_mono_alt_def}, @{thm all_conj_distrib} RS @{thm sym}] 1)
        THEN rtac @{thm allI} 1 THEN rtac @{thm nat.induct} 1
          THEN EVERY (map (fn expand =>
                              TRY (rtac @{thm conjI} 1)
                              THEN expand 1
                              THEN rtac @{thm monad_mono_step_L1_recguard_0} 1) func_expand)
        THEN REPEAT (etac @{thm conjE} 1)
        THEN EVERY (map (fn expand =>
                            TRY (rtac @{thm conjI} 1)
                            THEN expand 1
                            THEN REPEAT (FIRST (atac 1 :: map (fn t => rtac t 1) @{thms L1_monad_mono_step_rules})))
                        func_expand)
in
  Goal.prove lthy [] [] mono_thm (K tac)
  |> split_conj
end
    

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
fun translate_simpl filename fn_info do_opt trace_opt l1_function_name lthy =
let
  val prog_info = ProgramInfo.get_prog_info lthy filename

  (* Abstract the function to a new body with a proof of correspondence. *)
  fun convert ctxt fn_name callee_terms measure_var fn_args =
  let
    val (thm, opt_traces) = get_l1corres_thm prog_info fn_info ctxt do_opt trace_opt fn_name
                                             callee_terms measure_var
  in (get_body_of_l1corres_thm thm, thm, opt_traces) end

  (* Update function information. *)
  fun update_function_defs lthy fn_def =
    FunctionInfo.fn_def_update_const (Utils.get_term lthy (l1_function_name (#name fn_def))) fn_def
    |> FunctionInfo.fn_def_update_definition (
        (the (AutoCorresData.get_def (Proof_Context.theory_of lthy)
            filename "L1def" (#name fn_def))))

  (* Fetch the expected type of the translated function. *)
  val l1_fn_type = @{typ nat} --> mk_l1monadT (#state_type prog_info)

  (* Fetch the expected theorem about the translated function. *)
  fun get_l1_fn_assumption ctxt fn_name free _ is_recursive measure_var =
      mk_L1corres_call_prop ctxt prog_info fn_info fn_name (betapply (free, measure_var))
in
  AutoCorresUtil.do_translation_phase
      "L1" filename prog_info fn_info
      (K l1_fn_type)
      get_l1_fn_assumption
      (fn _ => [])
      l1_function_name
      convert
      l1_monad_mono
      update_function_defs
      @{thm L1corres_recguard_0}
      lthy
end

end
