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

val ts_simpset = simpset_of @{context}

(* Misc util functions. *)
val the' = Utils.the'
val apply_tac = Utils.apply_tac

fun get_hl_state_typ ctxt prog_info fn_info fn_name =
  let
    val term = FunctionInfo.get_function_def fn_info fn_name |> #const
  in
    LocalVarExtract.dest_l2monad_T (fastype_of term) |> snd |> #1
  end

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
fun make_lift_equality ctxt prog_info fn_info fn_name
    (rule_set : Monad_Types.monad_type) state_typ measure rhs_term =
let
  val thy = Proof_Context.theory_of ctxt

  (* Fetch function variables. *)
  val fn_def = FunctionInfo.get_function_def fn_info fn_name
  val inputs = #args fn_def
  val input_vars = map (fn (x, y) => Var ((x, 0), y)) inputs

  (*
   * Measure var.
   *
   * The L2 left-hand-side will always use this measure, while the
   * right-hand-side will only include a measure if the function is actually
   * recursive.
   *)
  val is_recursive = FunctionInfo.is_function_recursive fn_info fn_name
  val default_measure_var = @{term "rec_measure' :: nat"}
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
  val base_term = @{term "%L a b. (L2_call :: ('s, 'a, unit) L2_monad => ('s, 'a, unit) L2_monad) a = L b"}
  val a = betapplys (#const fn_def, measure_term :: input_vars)
  val b = if not is_recursive then betapplys (rhs_term, input_vars) else
            case state_typ of
                NONE => betapplys (rhs_term, measure_term :: input_vars)
              | SOME s => betapplys (rhs_term, [measure_term] @ input_vars @ [Free ("s'", s)])
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
 *)
fun assume_rec_lifted ctxt prog_info fn_info rule_set fn_thm fn_name =
let
  val thy = Proof_Context.theory_of ctxt
  val fn_def = FunctionInfo.get_function_def fn_info fn_name

  (* Find recursive calls. *)
  val recursive_calls = FunctionInfo.get_recursive_group fn_info fn_name

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
  val dest_fn_thms = map (fn (n, var) =>
    let
      val fn_def' = FunctionInfo.get_function_def fn_info n
      val inputs = #args fn_def'
      val T = (@{typ nat} :: map snd inputs)
          ---> (fastype_of (#const fn_def') |> get_typ_from_L2 rule_set)

      (* NB: pure functions would not use state, but recursive functions cannot
       * be lifted to pure (because we trigger failure when the measure hits
       * 0). So we can always assume there is state. *)
      val state_typ = get_hl_state_typ ctxt prog_info fn_info fn_name
      val x = make_lift_equality ctxt prog_info fn_info n rule_set
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
fun perform_lift ctxt prog_info fn_info rule_set fn_thm fn_name =
let
  (* Assume recursive calls can be successfully lifted into this type. *)
  val (ctxt', measure_var, thms, dict, m)
      = assume_rec_lifted ctxt prog_info fn_info rule_set fn_thm fn_name

  (* Extract the term from our function definition. *)
  val fn_thm' = fn_thm WHERE [("rec_measure'",
      Thm.cterm_of ctxt' measure_var)]
    handle THM _ => fn_thm
  val ct = Thm.prop_of fn_thm' |> Utils.rhs_of |> Thm.cterm_of ctxt'

  (* Rewrite the term using the given rewrite rules. *)
  val t = Thm.term_of ct
  val thm = case Monad_Convert.monad_rewrite ctxt rule_set thms true t of
                SOME t => t
              | NONE => @{thm reflexive} WHERE [("x", ct)]

  (* Convert "def == old_body" and "old_body == new_body" into "def == new_body". *)
  val thm_ml = Thm.transitive fn_thm' thm
  val thm_ml = Morphism.thm m thm_ml

  (* Get the newly rewritten term. *)
  val new_term = Thm.concl_of thm_ml |> Utils.rhs_of

  (*val _ = @{trace} (fn_name, #name rule_set, cterm_of (Proof_Context.theory_of ctxt) new_term)*)

  (* Determine if the conversion was successful. *)
  val success = #valid_term rule_set ctxt new_term
in
  (* Determine if we were a success. *)
  if success then
    SOME (thm_ml, dict)
  else
    NONE
end

(* Like perform_lift, but also applies the polishing rules, hopefully yielding
 * an even nicer definition. *)
fun perform_lift_and_polish ctxt prog_info fn_info rule_set do_opt
    fn_thm fn_name =
  case (perform_lift ctxt prog_info fn_info rule_set
        fn_thm fn_name)
  of NONE => NONE
  | SOME (thm, dict) => SOME let

  (* Measure the size of the new theorem. *)
  val _ = Statistics.gather ctxt "TS" fn_name
    (Thm.concl_of thm |> Utils.rhs_of)

  (* Apply any polishing rules. *)
  val polish_thm = Monad_Convert.polish ctxt rule_set do_opt thm

  (* Measure the term. *)
  val _ = Statistics.gather ctxt "polish" fn_name
    (Thm.concl_of polish_thm |> Utils.rhs_of)

in (polish_thm, dict) end


(*
 * Attempt to lift a function into the given monad, defining a new function.
 *
 * If the lift succeeds, we return a theorem of the form:
 *
 *   "L2_call foo x y z == <lift> $ new_foo x y z"
 *
 * where "lift" is a lifting function, such as "returnOk" or "gets", etc. New
 * constants may be defined during the lift.
 *
 * If the lift does not succeed, the function returns NONE.
 *)
fun lift_function_rewrite rule_set filename prog_info fn_info
    all_callee_proofs functions make_function_name keep_going do_opt lthy =
let
  val fn_names = map fst functions
  val fn_defs = map snd functions

  (* Determine if this function is recursive. *)
  val is_recursive = FunctionInfo.is_function_recursive fn_info (hd fn_names)

  (* Fetch relevant callee proofs, deleting recursive callees and duplicates. *)
  val callee_proofs =
      map (FunctionInfo.get_function_callees fn_info) fn_names
      |> flat
      |> Symset.make
      |> Symset.subtract (Symset.make fn_names)
      |> Symset.dest
      |> map (Symtab.lookup all_callee_proofs #> the)

  (* Add monad_mono theorems. *)
  val mono_thms = map (FunctionInfo.get_function_callees fn_info) fn_names
                  |> flat
                  |> map (#mono_thm o FunctionInfo.get_function_def fn_info)

  (* When lifting, also lift our callees. *)
  val rule_set' = Monad_Types.update_mt_lift_rules
      (fn x =>
        merge_ss (x, #lift_rules rule_set)
        |> simpset_map lthy (fn ctxt => ctxt addsimps (callee_proofs @ mono_thms)))
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
    map (fn (fn_name, fn_thm) =>
        perform_lift_and_polish lthy prog_info fn_info
            rule_set' do_opt fn_thm fn_name)
        (fn_names ~~ fn_defs)

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
  fun gen_fun_def_term (fn_name, dict, thm) =
  let
    (* If this function is recursive, it has a measure parameter. *)
    val measure_param = if is_recursive then [("rec_measure'", @{typ nat})] else []

    (* Fetch function parameters. *)
    val fn_def = FunctionInfo.get_function_def fn_info fn_name
    val fn_params = #args fn_def

    (* Extract the term from the function theorem. *)
    fun tail_of (_ $ x) = x
    val term = Thm.concl_of thm
        |> Utils.rhs_of
        |> tail_of
        |> Utils.unsafe_unvarify
        |> (fn term =>
             foldr (fn (v, t) => Utils.abs_over "" v t)
               term (map Free (measure_param @ fn_params)))
    val fn_type = fastype_of term

    (* Replace place-holder function names with our generated constant name. *)
    val term = map_aterms (fn t => case t of
        Free (n, T) =>
          (case Symtab.lookup dict n of
               NONE => t
             | SOME a => Free (make_function_name a, T))
     | x => x) term
  in
    (make_function_name fn_name, measure_param @ fn_params, term)
  end
  val input_defs = map gen_fun_def_term (Utils.zip3 fn_names dicts thms)
  val (defs, lthy) = Utils.define_functions input_defs false is_recursive lthy

  (* Instantiate variables in our equivalence theorem to their newly-defined values. *)
  fun do_inst_thm thm =
    Utils.instantiate_thm_vars lthy (
      fn ((name, _), t) =>
        try (unprefix "rec'") name
        |> Option.map make_function_name
        |> Option.map (Utils.get_term lthy)
        |> Option.map (Thm.cterm_of lthy)) thm
  val inst_thms = map do_inst_thm thms

  (* HACK: If a heap-lifted function takes no parameters, its measure gets
           eta contracted away, preventing eqsubst_tac from unifying the rec_measure's
           schematic variable. So we get rid of the schematic var pre-emptively. *)
  val inst_thms =
      map (fn inst_thm => Drule.abs_def inst_thm handle TERM _ => inst_thm) inst_thms

  (* Generate a theorem converting "L2_call <func>" into its new form,
   * such as L2_call <func> = liftE $ <new_func_def> *)
  val final_props = map (fn fn_name =>
      make_lift_equality lthy prog_info fn_info fn_name rule_set'
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
          (rtac @{thm recguard_induct} 1)
      |> apply_tac "(base case) split subgoals"
          (TRY (REPEAT_ALL_NEW (Tactic.match_tac lthy [@{thm conjI}]) 1))
      |> apply_tac "(base case) solve base cases"
          (EVERY (map (fn (def, fn_def) =>
            SOLVES (
            (EqSubst.eqsubst_tac lthy [0] [fn_def] 1)
            THEN (EqSubst.eqsubst_tac lthy [0] [def] 1)
            THEN (simp_tac (put_simpset ts_simpset lthy) 1))) (defs ~~ fn_defs)))
      |> apply_tac "(rec case) spliting induct case prems"
          (TRY (REPEAT_ALL_NEW (Tactic.ematch_tac lthy [@{thm conjE}]) 1))
      |> apply_tac "(rec case) split inductive case subgoals"
          (TRY (REPEAT_ALL_NEW (Tactic.match_tac lthy [@{thm conjI}]) 1))
      |> apply_tac "(rec case) unfolding strengthened function definition"
          (EVERY (map (fn (def, inst_thm) =>
              ((EqSubst.eqsubst_tac lthy [0] [def] 1)
               THEN (EqSubst.eqsubst_tac lthy [0] [inst_thm] 1)
               THEN (REPEAT (CHANGED (asm_full_simp_tac (put_simpset ts_simpset lthy) 1))))) (defs ~~ inst_thms)))
    else
      goal_state
      |> apply_tac "unfolding strengthen function definition"
             (EqSubst.eqsubst_tac lthy [0] [hd defs] 1)
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
        ((REPEAT (rtac @{thm allI} 1))
        THEN (REPEAT (etac @{thm conjE} 1))
        THEN (REPEAT (etac @{thm allE} 1)))
    |> apply_tac "solving goal" (atac 1)
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


  (* Record correctness theorem(s) for what we just did. *)
  val lthy = fold (fn (fn_name, thm) =>
                      Local_Theory.background_theory
                      (AutoCorresData.add_thm filename "TScorres" fn_name thm))
             (fn_names ~~ new_thms) lthy

  (* Provide final mono rules for recursive functions. *)
  fun final_mono_thm (fn_name, rewrite_thm) lthy =
  let
    val mono_thm = #mono_thm (FunctionInfo.get_function_def fn_info fn_name)
    val mono_thm' = #prove_mono rule_set' rewrite_thm mono_thm
    val (_, lthy) = Utils.define_lemma (make_function_name fn_name ^ "_mono") mono_thm' lthy
    val lthy = Utils.simp_add [mono_thm'] lthy
  in lthy end
  val lthy = if is_recursive then fold final_mono_thm (fn_names ~~ new_thms) lthy
             else lthy

  (* Output final corres rule. *)
  (* FIXME: Move to better location. *)
  fun output_rule fn_name lthy =
  let
    val thy = Proof_Context.theory_of lthy
    val l1_thm = the (AutoCorresData.get_thm thy filename "L1corres" fn_name)
          handle Option => raise SimplConv.FunctionNotFound fn_name
    val l2_thm = the (AutoCorresData.get_thm thy filename "L2corres" fn_name)
          handle Option => raise SimplConv.FunctionNotFound fn_name
    val hl_thm = the (AutoCorresData.get_thm thy filename "HLcorres" fn_name)
          handle Option => raise SimplConv.FunctionNotFound fn_name
    val wa_thm = the (AutoCorresData.get_thm thy filename "WAcorres" fn_name)
          (* If there is no WAcorres thm, it is probably because word_abstract
           * was disabled using no_word_abs.
           * In that case we just carry the hl_thm through. *)
          handle Option => (@{thm corresTA_trivial_from_heap_lift} OF [hl_thm]
                            handle THM _ => hl_thm) (* catch this failure below *)
    val ts_thm = the (AutoCorresData.get_thm thy filename "TScorres" fn_name)
          handle Option => raise SimplConv.FunctionNotFound fn_name
    val lthy = let
        val final_thm = @{thm ac_corres_chain} OF [l1_thm, l2_thm, hl_thm, wa_thm, ts_thm]
        val final_thm' = Simplifier.simplify lthy final_thm
        val (_, lthy) = Utils.define_lemma (make_function_name fn_name ^ "_ac_corres") final_thm' lthy
    in
        lthy
    end
    handle THM _ =>
           (Utils.THM_non_critical keep_going
                ("autocorres: failed to prove ac_corres theorem for " ^ fn_name)
                0 [l1_thm, l2_thm, hl_thm, wa_thm, ts_thm];
            lthy)
  in
    lthy
  end

  val lthy = fold output_rule fn_names lthy
in
  (lthy, fn_names ~~ new_thms, #name rule_set')
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
fun lift_function rules force_lift filename prog_info fn_info
    all_callee_proofs functions make_function_name keep_going do_opt lthy =
let
  val rules' = compute_lift_rules rules force_lift (map fst functions)

  (* Find the first lift that works. *)
  fun first (rule::xs) =
      (lift_function_rewrite rule filename prog_info fn_info
           all_callee_proofs functions make_function_name keep_going do_opt lthy
       handle LiftingFailed _ => first xs)
    | first [] = raise AllLiftingFailed functions
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
      ("  " ^ a ^ ": " ^ (PolyML.makestring b) ^ "\n")
      ) tabulated
    |> String.concat
in
  writeln ("Type Strengthening Statistics: \n" ^ data)
end

(* Run through every function, attempting to strengthen its type. *)
fun type_strengthen (rules : Monad_Types.monad_type list)
                    (force_lift : Monad_Types.monad_type Symtab.table)
                    filename fn_info (make_function_name : string -> string)
                    (keep_going : bool) (do_opt : bool) lthy =
let
  (* Get all function definitions. *)
  val prog_info = ProgramInfo.get_prog_info lthy filename

  fun optcat xs = List.concat (map the_list xs)

  (* Fetch the body of every function. *)
  fun convert lthy fn_name =
  let
    (* Fetch definition. *)
    val fn_def = FunctionInfo.get_function_def fn_info fn_name
    val def = #definition fn_def

    (* Prettify bound variable names in definition. *)
    val state_typ = get_hl_state_typ lthy prog_info fn_info fn_name
    val new_def = PrettyBoundVarNames.pretty_bound_vars_thm
                      lthy (Utils.crhs_of (Thm.cprop_of def)) keep_going
  in
    Thm.transitive def new_def
  end

  (* Definition function. *)
  fun define lthy _ (all_callee_proofs, callee_stats) functions =
  let
    val _ = writeln ("Translating (type strengthen) " ^ (Utils.commas (map fst functions)))
    val start_time = Timer.startRealTimer ()
    val (lthy, new_rewrites, monad_name) =
        lift_function rules force_lift filename prog_info fn_info
                      all_callee_proofs functions make_function_name keep_going do_opt lthy
    val _ = writeln ("  --> " ^ monad_name)
    val _ = @{trace} ("Converted (TS) " ^ Utils.commas (map fst functions) ^ " in " ^
                      Time.toString (Timer.checkRealTimer start_time) ^ " s")
  in
    (map (K ()) functions, (fold Symtab.update_new new_rewrites all_callee_proofs,
        monad_name :: callee_stats), lthy)
  end

  val (lthy, fn_info, (_, results)) =
      AutoCorresUtil.translate lthy fn_info convert define (K o map snd (* FIXME *)) (K (K I)) (Symtab.empty, [])

  (* Print some statistics for curiosity's sake. *)
  (*
  val _ = if print_stats then print_statistics results else ()
  *)
in
  (lthy, fn_info)
end

end