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
 * Lift monadic structures into lighter-weight monads.
 *)
structure TypeStrengthen =
struct

exception AllLiftingFailed of (string * thm) list
exception LiftingFailed of unit

(* FIXME: use AUTOCORRES_SIMPSET (need to fix unknown deps of the corres prover) *)
val ts_simpset = simpset_of @{context}

(* Misc util functions. *)
val the' = Utils.the'
val apply_tac = Utils.apply_tac

fun get_l2_state_typ ctxt prog_info l2_infos fn_name =
  let
    val term = #const (the (Symtab.lookup l2_infos fn_name));
  in
    LocalVarExtract.dest_l2monad_T (fastype_of term) |> snd |> #1
  end;

fun get_typ_from_L2 (rule_set : Monad_Types.monad_type) L2_typ =
  LocalVarExtract.dest_l2monad_T L2_typ |> snd |> #typ_from_L2 rule_set

(*
 * Make an equality prop of the form "L2_call <foo> = <liftE> $ <bar>".
 *
 * L2_call and <liftE> will typically be desired to be polymorphic in their
 * exception type. We fix it to "unit"; the caller will need to introduce
 * polymorphism as necessary.
 *
 * If "measure" is non-NONE, then that term will be used instead of a free
 * variable.
 * If "state_typ" is non-NONE, then "measure" is assumed to also take a
 * state parameter of the given type.
 *)
fun make_lift_equality ctxt prog_info l2_infos fn_name
    (rule_set : Monad_Types.monad_type) state_typ measure rhs_term =
let
  val thy = Proof_Context.theory_of ctxt

  (* Fetch function variables. *)
  val fn_def = the (Symtab.lookup l2_infos fn_name)
  val inputs = #args fn_def
  val input_vars = map (fn (x, y) => Var ((x, 0), y)) inputs

  (*
   * Measure var.
   *
   * The L2 left-hand-side will always use this measure, while the
   * right-hand-side will only include a measure if the function is actually
   * recursive.
   *)
  val is_recursive = FunctionInfo.is_function_recursive fn_def
  val default_measure_var = @{term "rec_measure' :: nat"} (* FIXME: Free *)
  val measure_term = Option.getOpt (measure, default_measure_var)

  (*
   * Construct the equality.
   *
   * This is a little delicate: in particular, we need to ensure that
   * the type of the resulting term is strictly correct. In particular,
   * our "lift_fn" will have type variables that need to be modified.
   * "Utils.mk_term" will fill in type variables of the base term based
   * on what is applied to it. So, we need to ensure that the lift
   * function is in our base term, and that its type variables have the
   * same names ("'s" for state, "'a" for return type) that we use
   * below.
   *)
  (* FIXME: use @{mk_term} *)
  val base_term = @{term "%L a b. (L2_call :: ('s, 'a, unit) L2_monad => ('s, 'a, unit) L2_monad) a = L b"}
  val a = betapplys (#const fn_def, measure_term :: input_vars)
  val b = if not is_recursive then betapplys (rhs_term, input_vars) else
            case state_typ of
                NONE => betapplys (rhs_term, measure_term :: input_vars)
              | SOME s => betapplys (rhs_term, [measure_term] @ input_vars @ [Free ("s'", s)]) (* FIXME: Free *)
                          |> lambda (Free ("s'", s))
  val term = Utils.mk_term thy (betapply (base_term, #L2_call_lift rule_set)) [a, b]
             |> HOLogic.mk_Trueprop

in
  (* Convert it into a trueprop with meta-foralls. *)
  Utils.vars_to_metaforall term
end

(*
 * Assume recursively called functions correctly map into the given type.
 *
 * We return:
 *
 *   (<newly generated context>,
 *    <the measure variable used>,
 *    <generated assumptions>,
 *    <table mapping free term names back to their function names>,
 *    <morphism to escape the context>)
 *
 * FIXME: refactor with AutoCorresUtil.assume_called_functions_corres
 *)
fun assume_rec_lifted ctxt prog_info l2_infos rule_set fn_name =
let
  val fn_def = the (Symtab.lookup l2_infos fn_name)

  (* Find recursive calls. *)
  val recursive_calls = Symset.dest (#rec_callees fn_def)

  (* Fix a variable for each such call, plus another for our measure variable. *)
  val (measure_fix :: dest_fn_fixes, ctxt')
      = Variable.add_fixes ("rec_measure'" :: map (fn x => "rec'" ^ x) recursive_calls) ctxt
  val rec_fun_names = Symtab.make (dest_fn_fixes ~~ recursive_calls)

  (* For recursive calls, we need a term representing our measure variable and
   * another representing our decremented measure variable. *)
  val measure_var = Free (measure_fix, @{typ nat})
  val dec_measure_var = @{const "recguard_dec"} $ measure_var

  (* For each recursive call, generate a theorem assuming that it lifts into
   * the type/monad of "rule_set". *)
  val dest_fn_thms = map (fn (callee, var) =>
    let
      val fn_def' = the (Symtab.lookup l2_infos callee)
      val inputs = #args fn_def'
      val T = (@{typ nat} :: map snd inputs)
          ---> (fastype_of (#const fn_def') |> get_typ_from_L2 rule_set)

      (* NB: pure functions would not use state, but recursive functions cannot
       * be lifted to pure (because we trigger failure when the measure hits
       * 0). So we can always assume there is state. *)
      val state_typ = get_l2_state_typ ctxt prog_info l2_infos fn_name
      val x = make_lift_equality ctxt prog_info l2_infos callee rule_set
                (SOME state_typ) (SOME dec_measure_var) (Free (var, T))
    in
      Thm.cterm_of ctxt' x
    end) (recursive_calls ~~ dest_fn_fixes)
    (* Our measure does not type-check for pure functions,
       causing a TERM exception from mk_term. *)
    handle TERM _ => raise LiftingFailed ()

  (* Assume the theorems we just generated. *)
  val (thms, ctxt'') = Assumption.add_assumes dest_fn_thms ctxt'
  val thms = map (fn t => (#polymorphic_thm rule_set) OF [t]) thms
in
  (ctxt'',
   measure_var,
   thms,
   rec_fun_names,
   Assumption.export_morphism ctxt'' ctxt'
   $> Variable.export_morphism ctxt' ctxt)
end


(*
 * Given a function definition, attempt to lift it into a different
 * monadic structure by applying a set of rewrite rules.
 *
 * For example, given:
 *
 *    foo x y = doE
 *      a <- returnOk 3;
 *      b <- returnOk 5;
 *      returnOk (a + b)
 *    odE
 *
 * we may be able to lift to:
 *
 *    foo x y = returnOk (let
 *      a = 3;
 *      b = 5;
 *    in
 *      a + b)
 *
 * This second function has the form "lift $ term" for some lifting function
 * "lift" and some new term "term". (These would be "returnOk" and "let a = ...
 * in a + b" in the example above, respectively.)
 *
 * We return a theorem of the form "foo x y == <lift> $ <term>", along with the
 * new term "<term>". If the lift was unsuccessful, we return "NONE".
 *)
fun perform_lift ctxt prog_info l2_infos rule_set fn_name =
let
  (* Assume recursive calls can be successfully lifted into this type. *)
  val (ctxt', measure_var, thms, dict, m)
      = assume_rec_lifted ctxt prog_info l2_infos rule_set fn_name

  val fn_def = #definition (the (Symtab.lookup l2_infos fn_name))

  (* Extract the term from our function definition. *)
  val fn_thm' = Utils.named_cterm_instantiate ctxt
                    [("rec_measure'" (* FIXME *), Thm.cterm_of ctxt' measure_var)] fn_def
                handle THM _ => fn_def
  val ct = Thm.prop_of fn_thm' |> Utils.rhs_of |> Thm.cterm_of ctxt'

  (* Rewrite the term using the given rewrite rules. *)
  val t = Thm.term_of ct
  val thm = case Monad_Convert.monad_rewrite ctxt rule_set thms true t of
                SOME t => t
              | NONE => Utils.named_cterm_instantiate ctxt [("x", ct)] @{thm reflexive}

  (* Convert "def == old_body" and "old_body == new_body" into "def == new_body". *)
  val thm_ml = Thm.transitive fn_thm' thm

  (* Get the newly rewritten term. *)
  val new_term = Thm.concl_of thm_ml |> Utils.rhs_of

  (* Export assumptions, converting callees to schematics. *)
  val thm_ml = Morphism.thm m thm_ml

  (*val _ = @{trace} (fn_name, #name rule_set, cterm_of (Proof_Context.theory_of ctxt) new_term)*)

  (* Determine if the conversion was successful. *)
  val success = #valid_term rule_set ctxt new_term
in
  (* Determine if the lifting succeeded. *)
  if success then
    SOME (thm_ml, dict)
  else
    NONE
end

(* Like perform_lift, but also applies the polishing rules, hopefully yielding
 * an even nicer definition. *)
fun perform_lift_and_polish ctxt prog_info fn_info rule_set do_opt fn_name =
  case (perform_lift ctxt prog_info fn_info rule_set fn_name)
  of NONE => NONE
  | SOME (thm, dict) => SOME let

  (* Apply any polishing rules. *)
  val polish_thm = Monad_Convert.polish ctxt rule_set do_opt thm

in (polish_thm, dict) end


(*
 * Attempt to lift a function (or recursive function group) into the given monad.
 *
 * If successful, we define the new function (vis. group) to the theory.
 * We then return a theorem of the form:
 *
 *   "L2_call foo x y z == <lift> $ new_foo x y z"
 *
 * where "lift" is a lifting function, such as "returnOk" or "gets", etc.
 *
 * If the lift does not succeed, the function returns NONE.
 *
 * The callees of this function need to be already translated in ts_infos
 * and also defined in lthy.
 *)
fun lift_function_rewrite rule_set filename prog_info l2_infos ts_infos
    fn_names make_function_name keep_going do_opt lthy =
let
  val these_l2_infos = map (the o Symtab.lookup l2_infos) fn_names

  (* Determine if this function is recursive. *)
  val is_recursive = FunctionInfo.is_function_recursive (hd these_l2_infos)

  (* Fetch relevant callees. *)
  val callees =
      map #callees these_l2_infos
      |> Symset.union_sets
      |> Symset.dest
  val callee_infos = map (Symtab.lookup ts_infos #> the) callees

  (* Add monad_mono theorems. *)
  val callee_l2_infos = map (Symtab.lookup l2_infos #> the) callees
  val mono_thms = List.mapPartial #mono_thm callee_l2_infos

  (* When lifting, also lift our callees. *)
  val rule_set' = Monad_Types.update_mt_lift_rules
      (fn thms => Monad_Types.thmset_adds thms (map #corres_thm callee_infos @ mono_thms))
      rule_set

  (*
   * Attempt to lift all functions into this type.
   *
   * For mutually recursive functions, every function in the group needs to be
   * lifted in the same type.
   *
   * Eliminate the "SOME", raising an exception if any function in the group
   * couldn't be lifted to this type.
   *)
  val lifted_functions =
    map (perform_lift_and_polish lthy prog_info l2_infos rule_set' do_opt) fn_names

  val lifted_functions = map (fn x =>
      case x of
          SOME a => a
        | NONE => raise LiftingFailed ())
      lifted_functions
  val thms = map fst lifted_functions
  val dicts = map snd lifted_functions

  (*
   * Generate terms necessary for defining the function, and define the
   * functions.
   *)
  fun gen_fun_def_term (fn_name, dict, thm) lthy =
  let
    (* Fix function parameters. *)
    val fn_info = the (Symtab.lookup l2_infos fn_name)
    (* Only produce measure parameters for recursive functions. *)
    val all_arg_names = (if is_recursive then ["rec_measure'"] else []) @
                        map fst (#args fn_info)
    val all_arg_types = (if is_recursive then [AutoCorresUtil.measureT] else []) @
                        map snd (#args fn_info)
    val (all_arg_names, lthy') = Variable.variant_fixes all_arg_names lthy
    val (measure_param, fn_args) =
          if is_recursive
          then chop 1 (all_arg_names ~~ all_arg_types)
          else ([], all_arg_names ~~ all_arg_types)

    (* Extract function body and abstract over the function arguments.
     * FIXME: this is an ugly way to do it. It's probably better if perform_lift
     *        doesn't convert to schematic vars to begin with *)

    (* First, convert schematic argument variables (of unknown names) to known free variables. *)
    val inst_args = map (Free #> Thm.cterm_of lthy' #> SOME) fn_args
    (* L2 function always takes a measure variable, so reserve a slot *)
    val inst_measure = if is_recursive
                       then map (Free #> Thm.cterm_of lthy' #> SOME) measure_param else [NONE]
    (* thm also has a schematic const for each recursive assumption,
     * which we need to skip. (The measure var appears first, because it
     * is also used in each recursive call.) *)
    val skip_callees = replicate (Symset.card (#rec_callees fn_info)) NONE
    val inst_thm = Drule.infer_instantiate' lthy' (inst_measure @ skip_callees @ inst_args) thm

    (* Extract the body from the conversion theorem.
     * E.g. for "L2_call foo = liftE body" we extract "body". *)
    fun tail_of (_ $ x) = x
    val body =
          Thm.concl_of inst_thm
          |> Utils.rhs_of_eq
          |> tail_of
          (* This converts callee Vars in assumptions to Frees. Won't be
           * necessary if we generate Frees (see previous FIXME). *)
          |> Utils.unsafe_unvarify
    (* Abstract over args, which are now known arg frees *)
    val term = foldr (fn (v, t) => Utils.abs_over "" v t)
                     body (map Free (measure_param @ fn_args))

    (* Replace place-holder function names with our generated constant name. *)
    val term = map_aterms (fn t => case t of
        Free (n, T) =>
          (case Symtab.lookup dict n of
               NONE => t
             | SOME a => Free (make_function_name a, T))
     | x => x) term
  in
    ((make_function_name fn_name, measure_param @ fn_args, term), lthy')
  end
  (* NB: discard lthy because we don't want the placeholders to be fixed during define_functions *)
  val (input_defs, _) = fold_map gen_fun_def_term (Utils.zip3 fn_names dicts thms) lthy
  val (ts_defs, lthy) = Utils.define_functions input_defs false is_recursive lthy
  (* TODO: we may want to cleanup callees and rec_callees here, like we do
   *       in other phases. It's not crucial, however, since this is the
   *       final phase. *)

  (* Instantiate variables in our equivalence theorem to their newly-defined values. *)
  fun do_inst_thm thm =
    Utils.instantiate_thm_vars lthy (
      fn ((name, _), t) =>
        try (unprefix "rec'") name
        (* FIXME: lookup from ts_infos *)
        |> Option.map make_function_name
        |> Option.map (Utils.get_term lthy)
        |> Option.map (Thm.cterm_of lthy)) thm
  val inst_thms = map do_inst_thm thms

  (* HACK: If an L2 function takes no parameters, its measure gets eta-contracted
           away, preventing eqsubst_tac from unifying the rec_measure's schematic
           variable. So we get rid of the schematic var pre-emptively. *)
  val inst_thms =
      map (fn inst_thm => Drule.abs_def inst_thm handle TERM _ => inst_thm) inst_thms

  (* Generate a theorem converting "L2_call <func>" into its new form,
   * such as L2_call <func> = liftE $ <new_func_def> *)
  val final_props = map (fn fn_name =>
      make_lift_equality lthy prog_info l2_infos fn_name rule_set'
          NONE NONE (Utils.get_term lthy (make_function_name fn_name))) fn_names

  (* Convert meta-logic into HOL statements, conjunct them together and setup
   * our goal statement. *)
  val int_props = map (Object_Logic.atomize_term lthy) final_props
  val goal = Utils.mk_conj_list int_props
      |> HOLogic.mk_Trueprop
      |> Thm.cterm_of lthy

  val simps =
    #L2_simp_rules rule_set' @
    @{thms gets_bind_ign L2_call_fail HOL.simp_thms}

  val rewrite_thm =
    Goal.init goal
    |> (fn goal_state => if is_recursive then
      goal_state
      |> apply_tac "start induction"
          (resolve_tac lthy @{thms recguard_induct} 1)
      |> apply_tac "(base case) split subgoals"
          (TRY (REPEAT_ALL_NEW (Tactic.match_tac lthy [@{thm conjI}]) 1))
      |> apply_tac "(base case) solve base cases"
          (EVERY (map (fn (ts_def, l2_info) =>
            SOLVES (
            (EqSubst.eqsubst_tac lthy [0] [#definition l2_info] 1)
            THEN (EqSubst.eqsubst_tac lthy [0] [ts_def] 1)
            THEN (simp_tac (put_simpset ts_simpset lthy) 1))) (ts_defs ~~ these_l2_infos)))
      |> apply_tac "(rec case) spliting induct case prems"
          (TRY (REPEAT_ALL_NEW (Tactic.ematch_tac lthy [@{thm conjE}]) 1))
      |> apply_tac "(rec case) split inductive case subgoals"
          (TRY (REPEAT_ALL_NEW (Tactic.match_tac lthy [@{thm conjI}]) 1))
      |> apply_tac "(rec case) unfolding strengthened function definition"
          (EVERY (map (fn (def, inst_thm) =>
              ((EqSubst.eqsubst_tac lthy [0] [def] 1)
               THEN (EqSubst.eqsubst_tac lthy [0] [inst_thm] 1)
               THEN (REPEAT (CHANGED (asm_full_simp_tac (put_simpset ts_simpset lthy) 1)))))
              (ts_defs ~~ inst_thms)))
    else
      goal_state
      |> apply_tac "unfolding strengthen function definition"
             (EqSubst.eqsubst_tac lthy [0] [hd ts_defs] 1)
      |> apply_tac "unfolding L2 rewritten theorem"
             (EqSubst.eqsubst_tac lthy [0] [hd inst_thms] 1)
      |> apply_tac "simplifying remainder"
             (TRY (simp_tac (put_simpset HOL_ss (Utils.set_hidden_ctxt lthy) addsimps simps) 1))
    )
    |> Goal.finish lthy

  (* Now, using this combined theorem, generate a theorem for each individual
   * function. *)
  fun prove_partial_pred thm pred =
    Thm.cterm_of lthy pred
    |> Goal.init
    |> apply_tac "inserting hypothesis"
        (cut_tac thm 1)
    |> apply_tac "normalising into rule format"
        ((REPEAT (resolve_tac lthy @{thms allI} 1))
        THEN (REPEAT (eresolve_tac lthy @{thms conjE} 1))
        THEN (REPEAT (eresolve_tac lthy @{thms allE} 1)))
    |> apply_tac "solving goal" (assume_tac lthy 1)
    |> Goal.finish lthy
    |> Object_Logic.rulify lthy
  val new_thms = map (prove_partial_pred rewrite_thm) final_props

  (*
   * Make the theorems polymorphic in their exception type.
   *
   * That is, these theories may all be applied regardless of what the type of
   * the exception part of the monad is, but are currently specialised to
   * when the exception part of the monad is unit. We apply a "polymorphism theorem" to change
   * the type of the rule from:
   *
   *   ('s, unit + 'a) nondet_monad
   *
   * to
   *
   *   ('s, 'e + 'a) nondet_monad
   *)
  val new_thms = map (fn t => #polymorphic_thm rule_set' OF [t]) new_thms
                 |> map (fn t => Drule.generalize ([], ["rec_measure'"]) t)

  (* Final mono rules for recursive functions. *)
  fun try_mono_thm (fn_name, rewrite_thm) =
    case #mono_thm (the (Symtab.lookup l2_infos fn_name)) of
        NONE => NONE
      | SOME l2_mono_thm =>
          case try (#prove_mono rule_set' rewrite_thm) l2_mono_thm of
              NONE => (Utils.ac_warning ("Failed to prove monad_mono for function: " ^ fn_name);
                       NONE)
            | SOME ts_mono_thm => SOME (fn_name, ts_mono_thm);
  val mono_thms = (if is_recursive then List.mapPartial try_mono_thm (fn_names ~~ new_thms) else [])
                  |> Symtab.make;

  val ts_infos =
        map (fn ((f, l2_info), (ts_def, ts_corres)) => let
              val mono_thm = Symtab.lookup mono_thms f;
              val const = Utils.get_term lthy (make_function_name f);
              val ts_info = l2_info
                    |> FunctionInfo.function_info_upd_phase FunctionInfo.TS
                    |> FunctionInfo.function_info_upd_definition ts_def
                    |> FunctionInfo.function_info_upd_corres_thm ts_corres
                    |> FunctionInfo.function_info_upd_const const
                    |> FunctionInfo.function_info_upd_mono_thm mono_thm;
              in (f, ts_info) end)
            ((fn_names ~~ these_l2_infos) ~~ (ts_defs ~~ new_thms))
in
  (lthy, Symtab.make ts_infos, #name rule_set')
end


(* Return the lifting rule(s) to try for a function set.
   This is moved out of lift_function so that it can be used to
   provide argument checking in the AutoCorres.abstract wrapper. *)
fun compute_lift_rules rules force_lift fn_names =
let
    fun all_list f xs = fold (fn x => (fn b => b andalso f x)) xs true

    val forced = fn_names
                 |> map (fn func => case Symtab.lookup force_lift func of
                                        SOME rule => [(func, rule)]
                                      | NONE => [])
                 |> List.concat
in
    case forced of
        [] => rules (* No restrictions *)
      | ((func, rule) :: rest) =>
        (* Functions in the same set must all use the same lifting rule. *)
        if map snd rest |> all_list (fn rule' => #name rule = #name rule')
        then [rule] (* Try the specified rule *)
        else error ("autocorres: this set of mutually recursive functions " ^
                    "cannot be lifted to different monads: " ^
                    commas_quote (map fst forced))
end


(* Lift the given function set, trying each rule until one succeeds. *)
fun lift_function rules force_lift filename prog_info l2_infos ts_infos
                  fn_names make_function_name keep_going do_opt lthy =
let
  val rules' = compute_lift_rules rules force_lift fn_names

  (* Find the first lift that works. *)
  fun first (rule::xs) =
      (lift_function_rewrite rule filename prog_info l2_infos ts_infos
                             fn_names make_function_name keep_going do_opt lthy
       handle LiftingFailed _ => first xs)
    | first [] = raise AllLiftingFailed (map (fn f =>
                         (f, #definition (the (Symtab.lookup l2_infos f)))) fn_names)
in
  first rules'
end

(* Show how many functions were lifted to each monad. *)
fun print_statistics results =
let
  fun count_dups x [] = [x]
    | count_dups (head, count) (next::rest) =
        if head = next then
          count_dups (head, count + 1) rest
        else
          (head, count) :: (count_dups (next, 1) rest)
  val tabulated = count_dups ("__fake__", 0) (sort_strings results) |> tl
  val data = map (fn (a,b) =>
      ("  " ^ a ^ ": " ^ (@{make_string} b) ^ "\n")
      ) tabulated
    |> String.concat
in
  writeln ("Type Strengthening Statistics: \n" ^ data)
end

(* Run through every function, attempting to strengthen its type.
 * FIXME: this stage is currently completely sequential. Conversions
 *        that do not depend on each other should be in parallel;
 *        this requires splitting the convert and define stages as usual. *)
fun translate
      (rules : Monad_Types.monad_type list)
      (force_lift : Monad_Types.monad_type Symtab.table)
      (filename : string)
      (prog_info : ProgramInfo.prog_info)
      (l2_results : FunctionInfo.phase_results)
      (existing_l2_infos : FunctionInfo.function_info Symtab.table)
      (existing_ts_infos : FunctionInfo.function_info Symtab.table)
      (make_function_name : string -> string)
      (keep_going : bool)
      (do_opt : bool)
      (add_trace: string -> string -> AutoCorresData.Trace -> unit)
      : FunctionInfo.phase_results =
if FSeq.null l2_results then FSeq.empty () else
let
  (* Wait for previous stage to finish first. *)
  val l2_results = FSeq.list_of l2_results;
  val lthy = List.last l2_results |> fst;
  val l2_infos = Utils.symtab_merge false (map snd l2_results);

  (* Prettify bound variable names in definitions. *)
  val l2_infos = Symtab.map (fn f_name => fn info => let
        val def = #definition (the (Symtab.lookup l2_infos f_name));
        val pretty_def = PrettyBoundVarNames.pretty_bound_vars_thm
                             lthy (Utils.crhs_of (Thm.cprop_of def)) keep_going
                         |> Thm.transitive def;
        in FunctionInfo.function_info_upd_definition pretty_def info end)
        l2_infos;

  (* Add prior L2 translations to round out L2 callees. *)
  val l2_infos = AutoCorresUtil.add_background_callees existing_l2_infos l2_infos;
  val l2_infos = Symtab.merge (K false) (l2_infos, existing_l2_infos);

  (* For now, just works sequentially like the old TypeStrengthen. *)
  fun translate_group fn_names (lthy, _, ts_infos) =
  let
    val _ = writeln ("Translating (type strengthen) " ^ Utils.commas fn_names);
    val start_time = Timer.startRealTimer ();

    val (lthy, new_ts_infos, monad_name) =
        lift_function rules force_lift filename prog_info l2_infos ts_infos
                            fn_names make_function_name keep_going do_opt lthy;

    val _ = writeln ("  --> " ^ monad_name);
    val _ = tracing ("Converted (TS) " ^ Utils.commas fn_names ^ " in " ^
                     Time.toString (Timer.checkRealTimer start_time) ^ " s");
  in (lthy, new_ts_infos, Symtab.merge (K false) (ts_infos, new_ts_infos)) end;

  val ts_results =
        Utils.accumulate translate_group (lthy, Symtab.empty, existing_ts_infos)
                         (map (map fst o Symtab.dest o snd) l2_results)
        |> fst
        |> map (fn (lthy, ts_infos, _) => (lthy, ts_infos));
in
  FSeq.of_list ts_results
end

end
