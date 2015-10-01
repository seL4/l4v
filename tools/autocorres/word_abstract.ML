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
  rules = @{thms word_abs_word32}
}

val word_abs : WARules list =
    map mk_word_abs_rule [@{typ 32}, @{typ 16}, @{typ 8}]

fun mk_sword_abs_rule T =
{
  ctype = fastype_of (@{mk_term "x :: (?'W::len) signed word" ('W)} T),
  atype = @{typ int},
  abs_fn = @{mk_term "sint :: (?'W::len) signed word => int" ('W)} T,
  inv_fn = @{mk_term "of_int :: int => (?'W::len) signed word" ('W)} T,
  rules = @{thms word_abs_sword32}
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
fun get_wa_conc_args rules fn_info fn_name fn_args =
let
  (* Construct arguments for the concrete body. We use the abstract names
   * with a prime ('), but with the concrete types. *)
  val conc_types = FunctionInfo.get_function_def fn_info fn_name |> #args |> map snd
  val conc_args = map (fn (Free (x, Tc), Ta) => Free (x ^ "'", Ta))
      (fn_args ~~ conc_types)
  val arg_pairs = (conc_args ~~ fn_args)

  (* Create preconditions that link the new types to the old types. *)
  val precond =
      map (fn (old, new) => @{mk_term "abs_var ?n ?f ?o" (o, f, n)}
          (old, get_abs_fn rules (fastype_of old), new))
          arg_pairs
      |> Utils.mk_conj_list
in
  (conc_types, conc_args, precond, arg_pairs)
end

(* Get the expected type of a function from its name. *)
fun get_expected_fn_type rules fn_info fn_name =
let
  val fn_def = FunctionInfo.get_function_def fn_info fn_name
  val fn_params_typ = map ((get_abs_type rules) o snd) (#args fn_def)
  val fn_ret_typ = get_abs_type rules (#return_type fn_def)
  val globals_typ = LocalVarExtract.dest_l2monad_T (fastype_of (#const fn_def)) |> snd |> #1
  val measure_typ = @{typ "nat"}
in
  (measure_typ :: fn_params_typ)
      ---> LocalVarExtract.mk_l2monadT globals_typ fn_ret_typ @{typ unit}
end

(* Get the expected theorem that will be generated about a function. *)
fun get_expected_fn_thm rules fn_info ctxt fn_name
                        function_free fn_args _ measure_var =
let
  val old_def = FunctionInfo.get_function_def fn_info fn_name
  val (old_arg_types, old_args, precond, arg_pairs)
      = get_wa_conc_args rules fn_info fn_name fn_args

  val old_term = betapplys (#const old_def, measure_var :: old_args)
  val new_term = betapplys (function_free, measure_var :: fn_args)
in
  @{mk_term "Trueprop (corresTA (%x. ?P) ?rt id ?A ?C)" (rt, A, C, P)}
      (get_abs_fn rules (#return_type old_def), new_term, old_term, precond)
  |> fold (fn t => fn v => Logic.all t v) (rev (map fst arg_pairs))
end

(* Get arguments passed into the function. *)
fun get_expected_fn_args rules fn_info fn_name =
  map (apsnd (get_abs_type rules)) (#args (FunctionInfo.get_function_def fn_info fn_name))

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
fun word_abstract
      (filename: string)
      (fn_info: FunctionInfo.fn_info)
      (unsigned_abs: string list)
      (no_signed_abs: string list)
      (trace_funcs: string list)
      (do_opt: bool)
      (trace_opt: bool)
      (wa_function_name: string -> string)
      (lthy: Proof.context) =
let
  (*
   * Select the rules to translate each function.
   *)
  val unsigned_abs = Symset.make unsigned_abs
  val no_signed_abs = Symset.make no_signed_abs

  fun rules_for fn_name =
      (if Symset.contains unsigned_abs fn_name then word_abs else []) @
      (if Symset.contains no_signed_abs fn_name then [] else sword_abs)

  (* Abstract functions. *)
  fun convert ctxt fn_name callee_terms measure_var fn_args =
  let
    val thy = Proof_Context.theory_of ctxt
    val old_fn = FunctionInfo.get_function_def fn_info fn_name

    val wa_rules = rules_for fn_name

    (* Construct free variables to represent our concrete arguments. *)
    val (conc_types, conc_args, precond, arg_pairs)
        = get_wa_conc_args wa_rules fn_info fn_name fn_args

    (* Fetch the function definition, and instantiate its arguments. *)
    val old_body_def =
        #definition old_fn
        (* Instantiate the arguments. *)
        |> Utils.inst_args (map (Thm.cterm_of ctxt) (measure_var :: conc_args))
    val old_body = Utils.rhs_of (Thm.prop_of old_body_def)

    (* Get old body definition with function arguments. *)
    val old_term = betapplys (#const old_fn, measure_var :: conc_args)

    (* Get a schematic variable accepting new arguments. *)
    val new_var = betapplys (
        Var (("A", 0), get_expected_fn_type wa_rules fn_info fn_name), measure_var :: fn_args)

    (* Fetch monotonicity theorems of callees. *)
    val callee_mono_thms = Symtab.dest callee_terms |> map fst
        |> List.mapPartial (fn callee =>
               if FunctionInfo.is_function_recursive fn_info callee
               then SOME (FunctionInfo.get_function_def fn_info callee |> #mono_thm)
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
            (get_abs_fn wa_rules (#return_type old_fn), new_var, old_term, precond)
        |> fold (fn t => fn v => Logic.all t v) (rev (fn_args @ map fst arg_pairs))
        |> Thm.cterm_of ctxt
        |> Goal.init
        |> Utils.apply_tac "move precond to assumption" (rtac @{thm corresTA_precond_to_asm} 1)
        |> Utils.apply_tac "split precond" (REPEAT (CHANGED (etac @{thm conjE} 1)))
        |> Utils.apply_tac "create schematic precond" (rtac @{thm corresTA_precond_to_guard} 1)
        |> Utils.apply_tac "unfold RHS" (CHANGED (Utils.unfold_once_tac ctxt (Utils.abs_def ctxt old_body_def) 1))

    (*
     * Fetch rules from the theory.
     *)
    val rules = WordAbsThms.get lthy @ List.concat (map #rules wa_rules)
                @ @{thms word_abs_default}
    val fo_rules = [@{thm abstract_val_fun_app}]


    val rules = rules @ (map (snd #> #3 #> extract_preconds_of_call) (Symtab.dest callee_terms))
                      @ callee_mono_thms

    (* Standard tactics. *)
    fun my_rtac ctxt thm n =
        Utils.trace_if_success ctxt thm (
          DETERM (EVERY' (rtac thm :: replicate (Rule_Cases.get_consumes thm) (assume_tac ctxt)) n))

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
    fun SOLVE_ALL _ _ 0 thm =
          raise THM ("Word abstraction diverging", 0, [thm])
      | SOLVE_ALL ctxt tacs depth thm =
      let
        fun TRY_ALL [] = no_tac
          | TRY_ALL (x::xs) =
              (x ctxt THEN REPEAT (SELECT_GOAL (SOLVE_ALL ctxt tacs (depth - 1)) 1))
              APPEND (TRY_ALL xs)
      in
        if Thm.nprems_of thm > 0 then
          DETERM (SOLVES (TRY_ALL tacs)) thm
        else
          all_tac thm
      end

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
                    rtac @{thm abstract_val_lambda} n thm
      | _ => no_tac thm

    (* All tactics we try, in the order we should try them. *)
    val step_tacs =
        [(@{thm imp_refl}, atac 1)]
        @ (map (fn thm => (thm, my_rtac ctxt thm 1)) rules)
        @ (map (fn thm => (thm, make_fo_tac (my_rtac ctxt thm) ctxt 1)) fo_rules)
        @ [(@{thm abstract_val_lambda}, lambda_tac 1)]
        @ [(@{thm reflexive},
            fn thm =>
            (if Config.get ctxt ML_Options.exception_trace then
              warning ("Could not solve subgoal: " ^
                (Goal_Display.string_of_goal ctxt thm))
            else (); no_tac thm))]

    (* Solve the goal. *)
    val replay_failure_start = 1
    val replay_failures = Unsynchronized.ref replay_failure_start
    val (thm, trace) =
        case AutoCorresTrace.maybe_trace_solve_tac ctxt (member (op =) trace_funcs fn_name) true false
                 (K step_tacs) goal (SOME WORD_ABS_MAX_DEPTH) replay_failures of
           NONE => (* intentionally generate a TRACE_SOLVE_TAC_FAIL *)
                   (AutoCorresTrace.trace_solve_tac ctxt false false (K step_tacs) goal NONE (Unsynchronized.ref 0);
                    (* never reached *) error "word_abstract fail tac: impossible")
         | SOME (thm, [trace]) => (Goal.finish ctxt thm, trace)
    val _ = if !replay_failures < replay_failure_start then
              @{trace} (fn_name ^ " WA: reverted to slow replay " ^
                        Int.toString(replay_failure_start - !replay_failures) ^ " time(s)") else ()

    (* Clean out any final function application ($) constants or "id" constants
     * generated by some rules. *)
    fun corresTA_abs_conv conv =
      Utils.remove_meta_conv (fn ctxt => Utils.nth_arg_conv 4 (conv ctxt)) ctxt

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
    val _ = Sign.no_vars ctxt (Thm.prop_of thm)

    (* Gather statistics. *)
    val _ = Statistics.gather ctxt "WA" fn_name
        (Drule.gen_all (Variable.maxidx_of ctxt) thm
          |> Thm.prop_of
          |> HOLogic.dest_Trueprop
          |> (fn t => Utils.term_nth_arg t 3))

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
    val thm = Drule.forall_elim_list (map (Thm.cterm_of ctxt) fn_args) thm

    (* Apply peephole optimisations to the theorem. *)
    val _ = writeln ("Simpifying (WA) " ^ fn_name)
    val (thm, opt_traces) = L2Opt.cleanup_thm_tagged ctxt thm (if do_opt then 0 else 2) 4 trace_opt "WA"

    (* We end up with an unwanted L2_guard outside the L2_recguard.
     * L2Opt should simplify the condition to (%_. True) even if (not do_opt),
     * so we match the guard and get rid of it here. *)
    val thm = Simplifier.rewrite_rule ctxt @{thms corresTA_simp_trivial_guard} thm

    (* Gather post-optimisation statistics. *)
    val _ = Statistics.gather ctxt "WAsimp" fn_name
        (Drule.gen_all (Variable.maxidx_of ctxt) thm
          |> Thm.prop_of
          |> HOLogic.dest_Trueprop
          |> (fn t => Utils.term_nth_arg t 3))

    (* Extract the abstract term out of a L2Tcorres thm. *)
    fun dest_corresWA_term_abs (_ $ _ $ _ $ t $ _ ) = t
    fun get_body_of_thm thm =
        Thm.concl_of (Drule.gen_all (Variable.maxidx_of ctxt) thm)
        |> HOLogic.dest_Trueprop
        |> dest_corresWA_term_abs
  in
    (get_body_of_thm thm, Drule.gen_all (Variable.maxidx_of ctxt) thm,
     (if member (op =) trace_funcs fn_name then [("WA", AutoCorresData.RuleTrace trace)] else []) @ opt_traces)
  end

  (* Update function information. *)
  fun update_function_defs lthy fn_def =
    FunctionInfo.fn_def_update_const (Utils.get_term lthy (wa_function_name (#name fn_def))) fn_def
    |> FunctionInfo.fn_def_update_definition (
        (the (AutoCorresData.get_def (Proof_Context.theory_of lthy)
            filename "WAdef" (#name fn_def))))
    |> FunctionInfo.fn_def_update_return_type (get_abs_type (rules_for (#name fn_def)) (#return_type fn_def))
    |> FunctionInfo.fn_def_update_args (map (apsnd (get_abs_type (rules_for (#name fn_def)))) (#args fn_def))
in
  AutoCorresUtil.do_translation_phase
    "WA"  filename (ProgramInfo.get_prog_info lthy filename) fn_info
    (fn fn_name => get_expected_fn_type (rules_for fn_name) fn_info fn_name)
    (fn ctxt => fn fn_name => get_expected_fn_thm (rules_for fn_name) fn_info ctxt fn_name)
    (fn fn_name => get_expected_fn_args (rules_for fn_name) fn_info fn_name)
    wa_function_name
    convert
    LocalVarExtract.l2_monad_mono
    update_function_defs
    @{thm corresTA_recguard_0}
    lthy
end

end
