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
 * Extract local variables out of converted L1 fragments.
 *)
structure LocalVarExtract =
struct

open Prog

(* Convenience abbreviations for set manipulation. *)
infix 1 INTER MINUS UNION
val empty_set = Varset.empty
val make_set = Varset.make
val union_sets = Varset.union_sets
val dest_set = Varset.dest
fun (a INTER b) = Varset.inter a b
fun (a MINUS b) = Varset.subtract b a
fun (a UNION b) = Varset.union a b

(* Convenience shortcuts. *)
val warning = Utils.ac_warning
val apply_tac = Utils.apply_tac
val the' = Utils.the'

(* Simpset we use for automated tactics. *)
fun setup_l2_ss ctxt = ctxt addsimps [@{thm ucast_id}, @{thm pred_conj_def}]

(* Convert a set of variable names into an Isabelle list of strings. *)
fun var_set_to_isa_list s =
  dest_set s
  |> map fst
  |> map ProgramInfo.demangle_name
  |> map Utils.encode_isa_string
  |> Utils.encode_isa_list @{typ string}

(*
 * Remove references to local variables in "term", replacing them with free
 * variables.
 *
 * We return a list of variables that were successfully extracted, along with
 * the modified term itself.
 *
 * For instance:
 *
 *   convert_local_vars @{term "a_' s + b + c"}
 *       [("x", @{term "a_' s"}), ("y", @{term "b_' s"})]
 *
 * would return ("x", @{term "x + b + c"}).
 *)
fun convert_local_vars name_map term [] = ([], term)
  | convert_local_vars name_map term ((var_name, var_term) :: vars)  =
      if Utils.contains_subterm var_term term then
        let
          val free_var = name_map (var_name, fastype_of var_term)

          (* Pull out "term" from "var_term". *)
          val abstracted = betapply (Utils.abs_over var_name var_term term, free_var)

          (* Pull out the other variables. *)
          val (other_vars, other_term) = convert_local_vars name_map abstracted vars
        in
          (other_vars @ [(var_name, fastype_of var_term)], other_term)
        end
      else
        convert_local_vars name_map term vars

(* Get the set of variables a function accepts and returns. *)
fun get_fn_input_output_vars prog_info fn_info fn_name =
let
  val fn_def = FunctionInfo.get_function_def fn_info fn_name
  val inputs = #args fn_def |> Varset.make

  (* Get the return type of a function. *)
  val return_ctype =
      ProgramAnalysis.get_rettype (#name fn_def) (#csenv prog_info)
      |> Utils.the' ("Function " ^ quote (#name fn_def) ^ " does not exist.")

  val outputs =
    if return_ctype = Absyn.Void then
      empty_set
    else
      make_set [(NameGeneration.return_var_name return_ctype |> MString.dest,
          #return_type fn_def)]
in
  (inputs, outputs)
end

(* Get the return variable of a particular function. *)
fun get_ret_var prog_info fn_info fn_name =
let
  val (_, outputs) = get_fn_input_output_vars prog_info fn_info fn_name
in
  hd ((Varset.dest outputs) @ [("void", @{typ unit})])
end

(*
 * Determine the state, return and exception type of a monad.
 *
 * Monads have the form:
 *
 *   'a => 'b => ... => 's => ('x, 'y, 's) L2_monad.
 *
 * We return:
 *
 *   (['a, 'b, ...], ('x, 'y, 's))
 *)
fun dest_l2monad_T t =
let
  val (Type ("Product_Type.prod", [Type ("Set.set", [Type ("Product_Type.prod", [
    Type ("Sum_Type.sum", [ex, ret]) ,state])]), _]))
      = body_type t
  val args = binder_types t
  val inputs = List.take (args, length args - 1)
in
  (inputs, (state, ret, ex))
end
fun l2monad_type monad =
  dest_l2monad_T (fastype_of monad) |> snd
fun l2monad_state_type monad = #1 (l2monad_type monad)
fun l2monad_ret_type monad = #2 (l2monad_type monad)
fun l2monad_ex_type monad = #3 (l2monad_type monad)

(* Get the abstract/concrete term from a "L2corres" predicate. *)
fun dest_L2corres_term_abs (_ $ _ $ _ $ _ $ _ $ t $ _ ) = t
fun dest_L2corres_term_conc (_ $ _ $ _ $ _ $ _ $ _ $ t ) = t

(* Make an L2 monad. *)
fun mk_l2monadT stateT retT exT =
  Utils.gen_typ @{typ "('a, 'b, 'c) L2_monad"} [stateT, retT, exT]

(*
 * "Spec" expressions are of the form:
 *
 *     {(s, t). f s t}
 *
 * where "s" and "t" are input/output states. We want to parse the expression,
 * and convert it to an L2 expression dealing only with globals in "s" and "t".
 *
 * If the original SIMPL spec attempts to read or write to local variables, we
 * just fail.
 *)
fun parse_spec ctxt prog_info term =
  let
    (* Apply a dummy old and new state variable to the term. *)
    val dummy_s = Free ("_dummy_state1", (#state_type prog_info))
    val dummy_t = Free ("_dummy_state2", (#state_type prog_info))
    val dummy_tuple = HOLogic.mk_tuple [dummy_s, dummy_t]
    val t = Envir.beta_eta_contract (
        (Const (@{const_name "Set.member"},
            fastype_of dummy_tuple --> fastype_of term --> @{typ bool})
          $ dummy_tuple $ term))

    (* Pull apart the "split" at the beginning of the term. *)
    val t = Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt)
        [mk_meta_eq @{thm split_def}, mk_meta_eq @{thm fst_conv}, mk_meta_eq @{thm snd_conv}] [] t

    (*
     * Pull out any references to any other variables into a lambda
     * function.
     *
     * We pull out the globals variable first, because we want it to end
     * up inner-most compared to all the other lambdas we generate.
     *)
    val globals_getter = #globals_getter prog_info
    val t = Utils.abs_over "t" (globals_getter $ dummy_t) t
            |> Utils.abs_over "s" (globals_getter $ dummy_s)
            |> HOLogic.mk_split
  in
    (* Determine if there are any references left to the dummy state
     * variable. If so, give up on the translation. *)
    if Utils.contains_subterm dummy_s t
    orelse Utils.contains_subterm dummy_t t then
      (warning ("Can't parse spec term: "
          ^ (Utils.term_to_string ctxt term)); NONE)
    else
      SOME t
  end


(*
 * Parse an L1 expression containing references to the global state.
 *
 * We assume that the input term is in the "abstracted" form "%s. f s" where
 * "s" is the global state variable.
 *
 * Our return value is a list of variables abstracted, whether the global
 * variable was used, and the abstracted term itself.
 *
 * The function will fail (and return NONE) if the input expression performs
 * arbitrary transformations on the state. For example:
 *
 *    "%s. a_' s"          => ([a], False, SOME @{term "%a s. a"})
 *    "%s. globals s"      => ([], True, SOME @{term "%s. s"})
 *    "%s. a_' s + b_' s"  => ([a, b], False, SOME @{term "%a b s. a + b"})
 *    "%s. False"          => ([], False, SOME @{term "%s. False"})
 *    "%s. bot s"          => ([], False, NONE)
 *)
fun parse_expr ctxt prog_info name_map term =
  let
    val dummy_state = Free ("_dummy_state", #state_type prog_info)

    (* Apply a dummy state variable to the term. This makes our later analysis
    * easier. *)
    val term = Envir.beta_eta_contract (term $ dummy_state)

    (*
     * Pull out any references to any other variables into a lambda
     * function.
     *
     * We pull out the globals variable first, because we want it to end
     * up inner-most compared to all the other lambdas we generate.
     *)
    val globals_getter = #globals_getter prog_info $ dummy_state
    val globals_used = Utils.contains_subterm globals_getter term
    val t = Utils.abs_over "s" globals_getter term

    (* Pull out local variables. *)
    val all_getters = #var_getters prog_info |> Symtab.dest |> map (fn (a,b) => (a, b $ dummy_state))
    val (v1, t) = convert_local_vars name_map t all_getters

    (*
     * Determine if there are any references left to the dummy state
     * variable.
     *
     * If so, we are stuck: we aren't pulling out a part of the state
     * record, but instead performing an arbitrary transformation on it.
     * The most likely reason for this is the C parser's dummy function
     * "lvar_init", which attempts to set an uninitialised local
     * variable to an invalid state. Other possibilities include "bot",
     * the always-false guard.
     *)
    val t = if Utils.contains_subterm dummy_state t then
      (warning ("Can't parse expression: "
          ^ (Utils.term_to_string ctxt term)); NONE)
      else
        SOME t;
  in
    (v1, globals_used, t)
  end

(*
 * Parse an "L1_modify" expression.
 *)
local
fun parse_modify' ctxt prog_info name_map term =
  let
    val dummy_state = Free ("_dummy_state", #state_type prog_info)

    (*
     * We expect modify clauses in two forms: both "%x. (foo x) x" and just
     * "foo". We apply a state variable to the function and beta/eta contract
     * to normalise our output for the next steps.
     *)
    val modify_clause = Envir.beta_eta_contract (term $ dummy_state)

    (*
     * Extract "xxx" from "foo_'_update xxx".
     *
     * If the user has written custom "modifies" clauses (presumably
     * using "AUXUPD" directives), this may fail.
     *)
    val (setter, modify_val, s) = case modify_clause of
        (Const var $ value $ s) => (Const var, value, s)
      | other => Utils.invalid_term "Const (x,y) $ z" other;
    val (var_name, var_type) = ProgramInfo.guess_var_name_type_from_setter_term setter

    (*
     * At this stage we have assume we have an update function "f" of
     * type "'a => 'a" which expects the old value of the variable
     * being updated, and returns a new value.
     *
     * We now want to convert this into a value of type "'a", returning
     * the new value. We do this by applying "(field_' s)" to the
     * function f, followed by normalisation.
     *)
    val getter =
      case (Symtab.lookup (#var_getters prog_info) var_name) of
          SOME v => v
        | NONE => Utils.invalid_input "valid local variable getter" var_name
    val modify_val = betapply (modify_val, getter $ dummy_state)
        |> Envir.beta_eta_contract

    (*
     * We are now in the form of "foo dummy_state". Pull out
     * our dummy state variable, and parse the expression.
     *)
    fun remove_dummy_state_var t = Utils.abs_over "s" dummy_state t
    val (vars, globals_used, modify_val) = parse_expr ctxt prog_info name_map (remove_dummy_state_var modify_val)
  in
    ((var_name, var_type), vars, globals_used, modify_val, remove_dummy_state_var s)
  end
in
fun parse_modify ctxt prog_info name_map term =
  let
    val dummy_state = Free ("_dummy_state", #state_type prog_info)
  in
    if Envir.beta_eta_contract (term $ dummy_state) = dummy_state then
      []
    else
      let
        val (updated_var, read_vars, reads_globals, term, residual) = parse_modify' ctxt prog_info name_map term
      in
        (updated_var, read_vars, reads_globals, term) :: parse_modify ctxt prog_info name_map residual
      end
  end
end

(*
 * Construct precondition from variable set.
 *
 * These preconditions are of the form:
 *
 *    "(%s. n_' s = n) and (%s. i_' s = i) and ..."
 *)
fun mk_precond prog_info name_map vars =
let
  val myvarsT = #state_type prog_info
  val dummy_state = Free ("_dummy_state", myvarsT)

  (* Fetch a variable getter, such as "n_'" from a variable's name. *)
  fun var_getter var =
    case Symtab.lookup (#var_getters prog_info) var of
        SOME x => (x $ dummy_state)
      | NONE =>  Utils.invalid_input "valid local variable name" var

  (* Chain together multiple preconditions. *)
  fun chain_preconds [] = Abs ("s", myvarsT, @{term "HOL.True"})
    | chain_preconds [x] = x
    | chain_preconds (x::xs) =
        Const (@{const_name "pred_conj"},
            (myvarsT --> @{typ bool}) --> (myvarsT --> @{typ bool}) --> (myvarsT --> @{typ bool}))
          $ x $ (chain_preconds xs)
in
  chain_preconds
    (map (fn (var_name, var_type) => Utils.abs_over "s" dummy_state
              (HOLogic.mk_eq (var_getter var_name, name_map (var_name, var_type))))
          (dest_set vars))
end

(*
 * Construct extraction functions, of the form:
 *
 *      "%s. (a_' s, b_' s, c_' s)"
 *)
fun mk_xf (prog_info : ProgramInfo.prog_info) vars =
let
  val dummy_state = Free ("_dummy_state", #state_type prog_info)
  fun var_getter var =
      ((Symtab.lookup (#var_getters prog_info) var |> the) $ dummy_state)
        handle Option => (Utils.invalid_input "valid local variable name" var)
in
  Utils.abs_over "s" dummy_state
    (HOLogic.mk_tuple (dest_set vars |> map fst |> map var_getter))
end

(*
 * Construct a correspondence lemma between a given L2 and L1 terms.
 *)
fun mk_corresXF_prop thy prog_info name_map return_vars except_vars precond_vars l2_term l1_term =
  let
    (* Construct precondition and extraction functions. *)
    val precond = mk_precond prog_info name_map precond_vars
    val return_xf = mk_xf prog_info return_vars
    val except_xf = mk_xf prog_info except_vars
  in
    Utils.mk_term thy @{term L2corres} [#globals_getter prog_info, return_xf,
        except_xf, precond, l2_term, l1_term]
    |> HOLogic.mk_Trueprop
  end

(*
 * Prove correspondence between L1 and L2.
 *
 *    ctxt: Local theory context
 *
 *    return_vars: Variables that are returned by the abstract spec's monad.
 *
 *    except_vars: Variables that are thrown by the abstract spec's monad.
 *
 *    precond_vars: Variables that must match between abstract and concrete.
 *
 *    l2_term / l1_term: Abstract and concrete specs.
 *)
fun mk_corresXF_thm ctxt prog_info name_map return_vars except_vars precond_vars l2_term l1_term tac =
let
  val free_vars = precond_vars |> dest_set |> map name_map
  val free_names = map (dest_Free #> fst) free_vars
in
  mk_corresXF_prop (Proof_Context.theory_of ctxt) prog_info name_map
      return_vars except_vars precond_vars l2_term l1_term
  |> (fn x => Goal.prove ctxt free_names [] x (fn _ => tac))
end

fun mk_corresXF_thm' ctxt prog_info name_map return_vars except_vars precond_vars l2_term l1_term thm =
  mk_corresXF_thm ctxt prog_info name_map return_vars except_vars precond_vars l2_term l1_term (
    (rewrite_goal_tac ctxt [mk_meta_eq @{thm split_def}] 1)
    THEN
    (rtac (rewrite_rule ctxt [mk_meta_eq @{thm split_def}] thm) 1)
    THEN
    (REPEAT (CHANGED (asm_full_simp_tac (setup_l2_ss ctxt) 1)))
  )

fun l1call_function_const t = case strip_comb t |> apsnd rev of
    (Const c, (Const c' :: _)) => if String.isSuffix "_'proc" (fst c')
        then Const c' else Const c
  | (Const c, _) => Const c
  | (Abs (_, _, t), []) => l1call_function_const t
  | _ => raise TERM ("l1call_function_const", [t])

(*
 * Parse an L1 term.
 *
 * In particular, we break down the structure of the program and parse the
 * usage of local variables in all expressions and modifies clauses.
 *)
fun parse_l1 ctxt prog_info fn_info name_map term =
  case term of
      (Const (@{const_name "L1_skip"}, _)) =>
        Modify (term,
            (SOME (Abs ("s", #globals_type prog_info, @{term "()"})), empty_set, false), NONE)

    | (Const (@{const_name "L1_modify"}, _) $ m) =>
        let
          val parsed_clause = parse_modify ctxt prog_info name_map m
          val (updated_var, read_vars, is_globals_reader, parsed_expr) =
            case parsed_clause of
                [x] => x
              | _ => Utils.invalid_term "Modifies clause too complex." m
        in
          Modify (term, (parsed_expr, make_set read_vars, is_globals_reader), SOME updated_var)
        end

    | (Const (@{const_name "L1_seq"}, _) $ lhs $ rhs) =>
        Seq (term, parse_l1 ctxt prog_info fn_info name_map lhs,
                   parse_l1 ctxt prog_info fn_info name_map rhs)

    | (Const (@{const_name "L1_catch"}, _) $ lhs $ rhs) =>
        Catch (term, parse_l1 ctxt prog_info fn_info name_map lhs,
                     parse_l1 ctxt prog_info fn_info name_map rhs)

    | (Const (@{const_name "L1_guard"}, _) $ c) =>
        let
          val (read_vars, is_globals_reader, parsed_expr) = parse_expr ctxt prog_info name_map c
        in
          Guard (term, (parsed_expr, make_set read_vars, is_globals_reader))
        end

    | (Const (@{const_name "L1_throw"}, _)) =>
        Throw term

    | (Const (@{const_name "L1_condition"}, _) $ cond $ lhs $ rhs) =>
        let
          (* Parse the conditional. *)
          val (read_vars, is_globals_reader, parsed_expr) = parse_expr ctxt prog_info name_map cond
        in
          Condition (term, (parsed_expr, make_set read_vars, is_globals_reader),
              parse_l1 ctxt prog_info fn_info name_map lhs,
              parse_l1 ctxt prog_info fn_info name_map rhs)
        end

    | (Const (@{const_name "L1_call"}, L1_call_type)
            $ arg_setup $ dest_fn_term $ globals_extract $ ret_extract) =>
        let
          (* Parse arg setup. We treat this not as a modify, but as several
           * expressions, as the modified variables are only in the scope of
           * this L1_call command. *)
          val arg_setup_exprs = parse_modify ctxt prog_info name_map arg_setup
                |> map (fn (_, read_vars, is_globals_reader, term) =>
                    (term, make_set read_vars, is_globals_reader))

          val dest_fn_term = case dest_fn_term of
                                 Const (@{const_name "measure_call"}, _) $ f => f
                               | _ => dest_fn_term

          (* Get the name of the variable the return value of the function will
           * be placed into. *)
          val dest_fn = FunctionInfo.get_function_from_const fn_info
                  (l1call_function_const dest_fn_term)
              |> Utils.the' ("Unknown function " ^ quote (@{make_string} dest_fn_term))
          val dest_fn_name = #name dest_fn

          (* Parse the return arguments. *)
          val ret_var = get_ret_var prog_info fn_info (#name dest_fn)
          val parsed_clause =
                parse_modify ctxt prog_info name_map (betapply (ret_extract, Free ("_dummy_state", #state_type prog_info)))
                |> map (fn (target_var, read_vars, globals_read, expr) =>
                    (target_var, (make_set read_vars) MINUS (make_set [ret_var]),
                        globals_read, Option.map (Utils.abs_over "ret" (name_map ret_var)) expr))

          val (ret_expr, updated_var) =
            case parsed_clause of
                [(target_var, read_vars, globals_read, expr)] =>
                    ((expr, read_vars, globals_read), SOME target_var)
              | [] => ((NONE, empty_set, false), NONE)
              | x => Utils.invalid_input "single return param" (PolyML.makestring x)
        in
          Call (term, arg_setup_exprs, ret_expr, updated_var, ())
        end

    | (Const (@{const_name "L1_while"}, _) $ cond $ body) =>
        let
          (* Parse conditional. *)
          val (read_vars, is_globals_reader, parsed_expr) = parse_expr ctxt prog_info name_map cond;
        in
          While (term, (parsed_expr, make_set read_vars, is_globals_reader),
                 parse_l1 ctxt prog_info fn_info name_map body)
        end

    | (Const (@{const_name "L1_init"}, _) $ setter) =>
        let
          val updated_var = ProgramInfo.guess_var_name_type_from_setter_term setter
        in
          Init (term, SOME updated_var)
        end

    | (Const (@{const_name "L1_spec"}, _) $ c) =>
        (case parse_spec ctxt prog_info c of
            SOME x =>
              Spec (term, (SOME x, empty_set, true))
          | NONE =>
              Spec (term, (NONE, empty_set, true)))

    | (Const (@{const_name "L1_fail"}, _)) =>
        Fail term

    | (Const (@{const_name "L1_recguard"}, _) $ var $ body) =>
        RecGuard (term, parse_l1 ctxt prog_info fn_info name_map body)

    | other => Utils.invalid_term "a L1 term" other

(*
 * Generate a proof showing that a particular variables "var" is not modified
 * over the given input L1 term.
 *)
fun mk_preservation_proof ctxt prog_info name_map var term =
let
  val thy = Proof_Context.theory_of ctxt

  (* Apply a tactic then simplify all remaining subgoals. *)
  fun s tac =
    tac THEN (TRY (REPEAT (CHANGED (asm_full_simp_tac (setup_l2_ss ctxt) 1))))

  (* Apply a rule then simplify all remaining subgoals. *)
  fun r thm = s (rtac thm 1)

  (* Generate the predicate. *)
  val var_set = make_set [var]
  val precond = mk_precond prog_info name_map var_set
  val postcond_ret = absdummy @{typ unit} (mk_precond prog_info name_map var_set)
  val postcond_ex = absdummy @{typ unit} (mk_precond prog_info name_map var_set)
  val goal =
    Utils.mk_term thy @{term validE} [precond, term, postcond_ret, postcond_ex]
    |> HOLogic.mk_Trueprop

  (* Construct a tactic that solves the problem. *)
  val tac =
    (case term of
        (Const (@{const_name "L1_skip"}, _)) =>
          r @{thm L1_skip_lp}
      | (Const (@{const_name "L1_init"}, _) $ _) =>
          r @{thm L1_init_lp}
      | (Const (@{const_name "L1_modify"}, _) $ _) =>
          r @{thm L1_modify_lp}
      | (Const (@{const_name "L1_call"}, _) $ _ $ _ $ _ $ _) =>
          r @{thm L1_call_lp}
      | (Const (@{const_name "L1_guard"}, _) $ _) =>
          r @{thm L1_guard_lp}
      | (Const (@{const_name "L1_throw"}, _)) =>
          r @{thm L1_throw_lp}
      | (Const (@{const_name "L1_spec"}, _) $ _) =>
          r @{thm hoareE_TrueI}
      | (Const (@{const_name "L1_fail"}, _)) =>
          r @{thm L1_fail_lp}
      | (Const (@{const_name "L1_while"}, _) $ _ $ body) =>
        let
          val body' = mk_preservation_proof ctxt prog_info name_map var body
        in
          s (rtac @{thm L1_while_lp} 1 THEN rtac body' 1)
        end
      | (Const (@{const_name "L1_condition"}, _) $ _ $ lhs $ rhs) =>
        let
          val lhs' = mk_preservation_proof ctxt prog_info name_map var lhs
          val rhs' = mk_preservation_proof ctxt prog_info name_map var rhs
        in
          s (rtac @{thm L1_condition_lp} 1 THEN rtac lhs' 1 THEN rtac rhs' 1)
        end
      | (Const (@{const_name "L1_seq"}, _) $ lhs $ rhs) =>
        let
          val lhs' = mk_preservation_proof ctxt prog_info name_map var lhs
          val rhs' = mk_preservation_proof ctxt prog_info name_map var rhs
        in
          s (rtac @{thm L1_seq_lp} 1 THEN rtac lhs' 1 THEN rtac rhs' 1)
        end
      | (Const (@{const_name "L1_catch"}, _) $ lhs $ rhs) =>
        let
          val lhs' = mk_preservation_proof ctxt prog_info name_map var lhs
          val rhs' = mk_preservation_proof ctxt prog_info name_map var rhs
        in
          s (rtac @{thm L1_catch_lp} 1 THEN rtac lhs' 1 THEN rtac rhs' 1)
        end
      | (Const (@{const_name "L1_recguard"}, _) $ _ $ body) =>
        let
          val body' = mk_preservation_proof ctxt prog_info name_map var body
        in
          s (rtac @{thm L1_recguard_lp} 1 THEN rtac body' 1)
        end
      | other => Utils.invalid_term "a L1 term" other)
in
  (* Generate proof. *)
  Thm.cterm_of ctxt goal
  |> Goal.init
  |> Utils.apply_tac ("proving variable preservation for var '" ^ (fst var) ^ "'") tac
  |> Goal.finish ctxt
end

(* Generate a preservation proof for multiple variables. *)
fun mk_multivar_preservation_proof ctxt prog_info name_map term var_set =
let
  val proofs = map (fn x =>
        mk_preservation_proof ctxt prog_info name_map x term)
      (dest_set var_set)
  val result = fold (fn x => fn y =>
          @{thm combine_validE} OF [x,y])
      proofs  @{thm hoareE_TrueI}
in
  result
end
handle Option => error ("Preservation proof failed for " ^ quote (@{make_string} var_set))

(*
 * Generate a well-typed L2 monad expression.
 *
 *    "const" is the name of the monadic function (e.g., @{const_name "L2_gets"})
 *
 *    "ret"/"throw" are the variables being returned or thrown by this monadic
 *    expression. This is used only for determining the type of the output
 *    monad.
 *
 *    "params" are the expressions to be beta applied to the monad.
 *)
fun mk_l2monad (prog_info : ProgramInfo.prog_info) const ret throw params =
let
  val retT = HOLogic.mk_tupleT (dest_set ret |> map snd)
  val exT = HOLogic.mk_tupleT (dest_set throw |> map snd)
  val monadT = mk_l2monadT (#globals_type prog_info) retT exT
in
  betapplys ((Const (const, (map fastype_of params) ---> monadT)), params)
end

(* Abstract over a tuple using the given name map. *)
fun abs_over_tuple_vars (name_map : (string * typ) -> term) (vars : varset) =
  Utils.abs_over_tuple (map (fn (a, b) => (a, name_map (a, b))) (dest_set vars))

(*
 * Take an L2corres theorem of the form:
 *
 *     L2corres st ret_xf ex_xf P (foo a b c) X
 *
 * and convert it into the form:
 *
 *     L2corres st ret_xf ex_xf P ((%(a, b, c). foo a b c) (a, b, c)) X
 *
 * This is used to ease unification in proofs where the abstract monad is
 * expected to be of the form "A x", where "x" is the return value of another
 * monad.
 *)
fun abs_over_thm ctxt (name_map : (string * typ) -> term) (thm : thm) (vars : varset) =
let
  fun convert_var_to_free x =
    case x of
        Var ((a, _), t) => Free (a, t)
      | x => x
  fun convert_free_to_var x =
    case x of
        Free (a, t) => Var ((a, 0), t)
      | x => x
  val (head $ st $ ret_xf $ ex_xf $ precond $ l2_term $ l1_term) =
    map_aterms convert_var_to_free (Thm.concl_of thm) |> HOLogic.dest_Trueprop
  val new_l2_term = (abs_over_tuple_vars name_map vars l2_term
      $ Free ("r'", HOLogic.mk_tupleT (dest_set vars |> map snd)))
  val new_concl =
       head $ st $ ret_xf $ ex_xf $ precond $ new_l2_term $ l1_term
       |> map_aterms convert_free_to_var
       |> HOLogic.mk_Trueprop
  val new_thm = list_implies (cprems_of thm, Thm.cterm_of ctxt new_concl)
in
  Goal.init new_thm
  |> asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps [mk_meta_eq @{thm split_def}]) 1 |> Seq.hd
  |> rtac (rewrite_rule ctxt [mk_meta_eq @{thm split_def}] thm) 1 |> Seq.hd
  |> REPEAT (atac 1) |> Seq.hd
  |> Goal.finish ctxt
end

(*
 * Given a L2 monad that returns the variables "vars_returned", convert it into
 * an L2 monad that returns "needed_returns".
 *
 * This is frequently needed when a particular monad is only capable of returning
 * a particular variable (or set of variables), but needs to return a different set
 * of these variables. For example, both branches in an "condition" block need
 * to return the same set of variables.
 *
 * The injection is done by (if necessary) appending an additional "L2_seq" to
 * the input monad, returning the desired set of variables.
 *
 * "allow_excess" is the output monad is allowed to return a superset of
 * "needed_returns". By allowing such excess variables to be returned, the
 * generated output can be neater than if we were more strict.
 *)
fun inject_return_vals ctxt prog_info name_map needed_returns allow_excess throw_vars fn_vars
      term (vars_read, vars_returned, output_monad, thm) =
  if needed_returns = vars_returned then
    (* We already have precisely what is needed --- no more to do. *)
    (vars_read, vars_returned, output_monad, thm)
  else if (allow_excess andalso Varset.subset (needed_returns, vars_returned)) then
    (* We already provide a superset of what is needed, and this is allowed. *)
    (vars_read, vars_returned, output_monad, thm)
  else
    let
      val (l1_term, _, _) = get_node_data term

      (* Generate the return statement. *)
      val injected_return =
            mk_l2monad prog_info @{const_name L2_gets} needed_returns throw_vars
                [absdummy (#globals_type prog_info) (HOLogic.mk_tuple (dest_set needed_returns |> map name_map)),
                    var_set_to_isa_list needed_returns]
            |> abs_over_tuple_vars name_map vars_returned

      (* Append the return statement to the input term. *)
      val generated_term = mk_l2monad prog_info @{const_name L2_seq}
          needed_returns throw_vars [output_monad, injected_return]
      val preserved_vals = needed_returns MINUS vars_returned

      (* Generate a proof of correctness. *)
      val generated_thm =
        let
          val preserve_proof = mk_multivar_preservation_proof ctxt prog_info name_map l1_term preserved_vals
        in
          mk_corresXF_thm' ctxt prog_info name_map needed_returns throw_vars (vars_read UNION preserved_vals)
              generated_term l1_term
              (@{thm L2corres_inject_return} OF [thm, @{thm validE_weaken} OF [preserve_proof]])
        end
    in
      (vars_read UNION preserved_vals, needed_returns, generated_term, generated_thm)
    end

(*
 * Convert an L1 function into an L2 function.
 *
 * We assume that our input term has come out of the L1 conversion functions.
 *
 * We have inputs of the following:
 *
 *      ctxt: Isabelle context
 *
 *      l1_measure_defs: definitions for L1 measure constants
 *
 *      needed_vars:
 *
 *          Variables that are read in later executions.
 *
 *          These are passed into the conversion so that we know what variables
 *          we need to track for later execution, and what variables we can
 *          just discard on the spot.
 *
 *          If we didn't know what we actually needed to track, then the
 *          converted code would be significantly bloated due to returning
 *          variables that aren't actually used.
 *
 *      allow_excess:
 *
 *          Are we allowed to return _more_ variables than otherwise needed
 *          according to needed_vars? By setting this to true, more efficient
 *          code can be generated.
 *
 *      throw_vars:
 *
 *          Variables that must be thrown in the event we decide to emit an
 *          "L2_throw" call. These are calculated as we enter a try/catch block
 *          to ensure that all sites are consistent in the values they throw.
 *
 *      term: The L1 term to convert.
 *
 * The return value of this function is a tuple:
 *
 *      (<vars read by block>, <vars returned>, <term>, <proof>)
 *
 * The "vars returned" is the variables that are returned through the "bind"
 * combinator.
 *)
fun do_conv
    (ctxt : Proof.context)
    prog_info
    fn_info
    name_map
    (fn_vars : varset)
    (callee_proofs : (bool * term * thm) Symtab.table)
    (needed_vars : varset)
    (allow_excess : bool)
    (throw_vars : varset)
    (term : (term * varset * varset, term option * varset * bool, (string * typ) option, unit) prog)
    : (varset * varset * term * thm) =
let
  val l1_term = get_node_data term |> #1
  val live_vars = get_node_data term |> #2
  val modified_vars = get_node_data term |> #3
  val inject =
      inject_return_vals ctxt prog_info name_map needed_vars allow_excess throw_vars fn_vars term
  fun mkthm read_vars ret_vars generated_term thm =
      mk_corresXF_thm' ctxt prog_info name_map ret_vars throw_vars read_vars generated_term l1_term thm
  val mk_monad = mk_l2monad prog_info
in
  case term of
      Init (_, SOME output_var) =>
        let
          val out_vars = make_set [output_var]
          val generated_term = mk_monad @{const_name L2_unknown} out_vars throw_vars
                                        [Utils.ml_str_list_to_isa [fst output_var]]
          val thm = mkthm empty_set out_vars generated_term @{thm L2corres_spec_unknown}
        in
          inject (empty_set, out_vars, generated_term, thm)
        end

      (* L1_skip. *)
    | Modify (_, (SOME expr, _, _), NONE) =>
        let
          val generated_term = mk_monad @{const_name L2_gets}
              empty_set throw_vars [expr, var_set_to_isa_list empty_set]
          val thm = mkthm empty_set empty_set generated_term @{thm L2corres_gets_skip}
        in
          inject (empty_set, empty_set, generated_term, thm)
        end

      (* L1_modify with unparsable expression. *)
    | Modify (_, (NONE, _, _), SOME output_var) =>
        let
          val out_vars = make_set [output_var]
          val generated_term = mk_monad @{const_name L2_unknown} out_vars throw_vars []
          val thm = mkthm empty_set out_vars generated_term @{thm L2corres_modify_unknown}
        in
          inject (empty_set, out_vars, generated_term, thm)
        end

      (* L1_modify that only modifies globals. *)
    | Modify (_, (SOME expr, read_vars, _), SOME ("globals'", _)) =>
        let
          val generated_term = mk_monad @{const_name L2_modify} empty_set throw_vars [expr]
          val thm = mkthm read_vars empty_set generated_term @{thm L2corres_modify_global}
        in
          inject (read_vars, empty_set, generated_term, thm)
        end

      (* L1_modify that only modifies a local and also reads globals. *)
    | Modify (_, (SOME expr, read_vars, _), SOME output_var) =>
        let
          val generated_term = mk_monad @{const_name L2_gets}
              (make_set [output_var]) throw_vars [expr, var_set_to_isa_list (make_set [output_var])]
          val thm = mkthm read_vars (make_set [output_var]) generated_term @{thm L2corres_modify_gets}
        in
          inject (read_vars, make_set [output_var], generated_term, thm)
        end

    | Throw _ =>
        let
          val generated_term = mk_monad @{const_name L2_throw} needed_vars throw_vars
              [HOLogic.mk_tuple (dest_set throw_vars |> map name_map),
                    var_set_to_isa_list throw_vars]
          val thm = mkthm throw_vars needed_vars generated_term @{thm L2corres_throw}
        in
          (throw_vars, needed_vars, generated_term, thm)
        end

    | Spec (_, (SOME expr, read_vars, _)) =>
        let
          val generated_term = mk_monad @{const_name "L2_spec"} needed_vars throw_vars [expr]
          val thm = mkthm read_vars needed_vars generated_term @{thm L2corres_spec}
        in
          inject (read_vars, needed_vars, generated_term, thm)
        end

    | Spec (_, (NONE, _, _)) =>
        let
          val generated_term = mk_monad @{const_name "L2_fail"} needed_vars throw_vars []
          val thm = mkthm empty_set needed_vars generated_term @{thm L2corres_fail}
        in
          inject (empty_set, needed_vars, generated_term, thm)
        end

    | Guard (_, (SOME expr, read_vars, _)) =>
        let
          val generated_term = mk_monad @{const_name "L2_guard"} empty_set throw_vars [expr]
          val thm = mkthm read_vars empty_set generated_term @{thm L2corres_guard}
        in
          inject (read_vars, empty_set, generated_term, thm)
        end

    | Guard (_, (NONE, _, _)) =>
        let
          val generated_term = mk_monad @{const_name "L2_fail"} needed_vars throw_vars []
          val thm = mkthm empty_set needed_vars generated_term @{thm L2corres_fail}
        in
          (empty_set, needed_vars, generated_term, thm)
        end

    | Fail _ =>
        let
          val generated_term = mk_monad @{const_name "L2_fail"} needed_vars throw_vars []
          val thm = mkthm empty_set needed_vars generated_term @{thm L2corres_fail}
        in
          (empty_set, needed_vars, generated_term, thm)
        end

    | Seq (_, lhs, rhs) =>
        let
          val (_, rhs_live, rhs_modified) = get_node_data rhs
          val (lhs_term, _, lhs_modified) = get_node_data lhs

          (* Convert LHS and RHS. *)
          val ret_vars = rhs_live INTER lhs_modified
          val (lhs_reads, lhs_rets, new_lhs, lhs_thm)
              = do_conv ctxt prog_info fn_info name_map fn_vars callee_proofs ret_vars true throw_vars lhs
          val (rhs_reads, rhs_rets, new_rhs, rhs_thm)
              = do_conv ctxt prog_info fn_info name_map fn_vars callee_proofs needed_vars allow_excess throw_vars rhs
          val block_reads = lhs_reads UNION (rhs_reads MINUS lhs_modified)

          (* Reconstruct body to support our input tuple. *)
          val rhs_thm = abs_over_thm ctxt name_map rhs_thm lhs_rets
          val new_rhs = abs_over_tuple_vars name_map lhs_rets new_rhs

          (* Generate the final term. *)
          val generated_term = mk_monad @{const_name L2_seq} rhs_rets throw_vars [new_lhs, new_rhs]

          (* Generate a proof. *)
          val thm =
          let
            (* Show that certain variables are preserved by the LHS. *)
            val needed_preserves = (rhs_reads MINUS lhs_modified)
            val preserve_proof = mk_multivar_preservation_proof ctxt prog_info name_map lhs_term needed_preserves
          in
            mkthm block_reads rhs_rets generated_term
                (@{thm L2corres_seq} OF [lhs_thm, rhs_thm,
                    @{thm validE_weaken} OF [preserve_proof]])
          end
        in
          inject (block_reads, rhs_rets, generated_term, thm)
        end

    | Catch (_, lhs, rhs) =>
        let
          val (lhs_term, _, lhs_modified) = get_node_data lhs
          val (_, rhs_live, _) = get_node_data rhs

          (* Convert LHS and RHS. *)
          val lhs_throws = rhs_live INTER lhs_modified
          val (lhs_reads, lhs_rets, new_lhs, lhs_thm)
              = do_conv ctxt prog_info fn_info name_map fn_vars callee_proofs (needed_vars) false lhs_throws lhs
          val (rhs_reads, _, new_rhs, rhs_thm)
              = do_conv ctxt prog_info fn_info name_map fn_vars callee_proofs (needed_vars) false throw_vars rhs
          val block_reads = lhs_reads UNION (rhs_reads MINUS lhs_throws)

          (* Reconstruct body to support our input tuple. *)
          val rhs_thm = abs_over_thm ctxt name_map rhs_thm lhs_throws
          val new_rhs = abs_over_tuple_vars name_map lhs_throws new_rhs

          (* Generate the final term. *)
          val generated_term = mk_monad @{const_name L2_catch} needed_vars throw_vars [new_lhs, new_rhs]

          (* Generate a proof. *)
          val thm =
          let
            (* Show that certain variables are preserved by the LHS. *)
            val needed_preserves = (rhs_reads MINUS lhs_modified)
            val preserve_proof = mk_multivar_preservation_proof ctxt prog_info name_map lhs_term needed_preserves
          in
            mkthm block_reads needed_vars generated_term
                (@{thm L2corres_catch} OF [lhs_thm, rhs_thm, @{thm validE_weaken} OF [preserve_proof]])
          end
        in
          inject (block_reads, needed_vars, generated_term, thm)
        end

    | RecGuard (_, body) =>
        let
          (* Convert body. *)
          val (body_reads, vars_returned, new_body, body_thm) =
              do_conv ctxt prog_info fn_info name_map fn_vars callee_proofs needed_vars false throw_vars body

          (* Get recguard variable. *)
          val (_ $ var $ _) = l1_term

          (* Generate the final term. *)
          val generated_term =
              mk_monad @{const_name "L2_recguard"} vars_returned throw_vars [
                var, new_body]
          val thm = mkthm body_reads vars_returned generated_term
                (@{thm L2corres_recguard} OF [body_thm])
        in
          inject (body_reads, vars_returned, generated_term, thm)
        end

    | Condition (_, (SOME expr, read_vars, _), lhs, rhs) =>
        let
          (* Convert LHS and RHS. *)
          val requested_vars = needed_vars INTER modified_vars
          val (lhs_reads, _, new_lhs, lhs_thm)
              = do_conv ctxt prog_info fn_info name_map fn_vars callee_proofs requested_vars false throw_vars lhs
          val (rhs_reads, _, new_rhs, rhs_thm)
              = do_conv ctxt prog_info fn_info name_map fn_vars callee_proofs requested_vars false throw_vars rhs
          val block_reads = lhs_reads UNION rhs_reads UNION read_vars

          (* Generate the final term. *)
          val generated_term = mk_monad @{const_name "L2_condition"}
                requested_vars throw_vars [expr, new_lhs, new_rhs]
          val thm = mkthm block_reads requested_vars generated_term
              (@{thm L2corres_cond} OF [lhs_thm, rhs_thm])
        in
          inject (block_reads, requested_vars, generated_term, thm)
        end

    | While (_, (SOME expr, read_vars, _), body) =>
        let
          (* Convert body. *)
          val loop_iterators = (needed_vars UNION live_vars) INTER modified_vars
          val (body_reads, _, new_body, body_thm) =
              do_conv ctxt prog_info fn_info name_map fn_vars callee_proofs loop_iterators false throw_vars body
          val (body_term, _, body_modifies) = get_node_data body

          (* Reconstruct body to support our input tuple. *)
          val new_body = abs_over_tuple_vars name_map loop_iterators new_body
          val body_thm = abs_over_thm ctxt name_map body_thm loop_iterators

          (* Generate the final term. *)
          val generated_term =
              mk_monad @{const_name "L2_while"} loop_iterators throw_vars [
                abs_over_tuple_vars name_map loop_iterators expr,
                new_body,
                HOLogic.mk_tuple (dest_set loop_iterators |> map name_map),
                var_set_to_isa_list loop_iterators]

          (* Generate a proof. *)
          val thm =
          let
            (* Show that certain variables are preserved by the LHS. *)
            val needed_preserves = ((body_reads UNION read_vars)  MINUS body_modifies)
            val preserve_proof = mk_multivar_preservation_proof ctxt prog_info name_map body_term needed_preserves

            (* Instantiate while loop rule to avoid ambiguous unification. *)
            val tracked_vars = (body_reads UNION read_vars UNION loop_iterators)
            val invariant_precond = abs_over_tuple_vars name_map loop_iterators
                  (mk_precond prog_info name_map tracked_vars)
            val base_thm = Utils.named_cterm_instantiate [
                  ("P", Thm.cterm_of ctxt invariant_precond),
                  ("A", Thm.cterm_of ctxt new_body)
                ] @{thm L2corres_while}
          in
            mkthm (body_reads UNION read_vars UNION loop_iterators) loop_iterators generated_term
                (base_thm OF [body_thm, @{thm validE_weaken} OF [preserve_proof]])
          end
        in
          inject (body_reads UNION read_vars UNION loop_iterators, loop_iterators, generated_term, thm)
        end

    | Call (_, expr_list, (ret_expr, ret_read_vars, _), ret_var, measure_term) =>
        let
          val (_ $ arg_setup $ dest_fn $ globals_extract $ ret_extract) = l1_term

          val (measure_term, dest_fn) = case dest_fn of
              (c as Const (@{const_name "measure_call"}, _)) $ f     => (c, f)
            | f $ (c as Const (@{const_name "undefined"}, _))        => (c, f)
            | f $ (c as Const (@{const_name "recguard_dec"}, _) $ _) => (c, f)
            | _ => raise TERM ("local_var_extract: strange function call", [dest_fn])

          (* Get destination function. *)
          val dest_fn = FunctionInfo.get_function_from_const fn_info
              (l1call_function_const dest_fn)

          (* Lookup the callee proof, if it exists. *)
          val callee_proof = Option.mapPartial
              (Symtab.lookup callee_proofs) (Option.map #name dest_fn)
        in
        (* Determine if we have a proof for the callee. *)
        case callee_proof of
        NONE =>
          (let
            val generated_term = mk_monad @{const_name "L2_fail"} needed_vars throw_vars []
            val thm = mkthm empty_set needed_vars generated_term @{thm L2corres_fail}
          in
            (empty_set, needed_vars, generated_term, thm)
          end)

        | SOME (is_recursive, callee_free, callee_thm) =>
        (let
          (* Get information about the function. *)
          val dest_fn = the dest_fn
          val args = #args dest_fn

          (* Parse argument setup. *)
          val arg_setup_vals = parse_modify ctxt prog_info name_map arg_setup |> List.rev

          (* Ensure that we can parse everything. *)
          val arg_setup_vals =
            map (fn (a, b, c, parsed_expr) =>
              case parsed_expr of
                  NONE =>
                    raise Utils.InvalidInput ("Could not parse function parameter '" ^ (fst a) ^ "'")
                | SOME x =>
                    (a, b, c, x)
              ) arg_setup_vals

          (* Sanity check: ensure that we have the correct number of arguments. *)
          val _ = if length arg_setup_vals <> length args then
              raise TERM ("Argument list length does not match function definition.", [arg_setup])
            else
              ()

          (* Rename input parameter names. *)
          val arg_setup_vals = map (fn ((a,t),b,c,d) => ((a ^ "'param", t), b, c, d)) arg_setup_vals

          (* Generate the call. *)
          (* The measure is the first arg, so we need to skip it when applying the others. *)
          val args = map (fn (a,_,_,_) => name_map a) arg_setup_vals
          val call_args = let
              val var = Free ("rec_measure'", @{typ "nat"})
            in
              lambda var (betapplys (callee_free, var :: args))
            end

          val call_measure = case measure_term of
                  Const (@{const_name "measure_call"}, _) => @{mk_term "measure_call ?f" f} call_args
                | _ => betapply (call_args, measure_term)

          val (call, ret_vars) =
            case (ret_var, ret_expr) of
                (SOME ("globals'", _), SOME e) =>
                    (mk_monad @{const_name L2_modifycall} empty_set throw_vars
                        [call_measure, e], empty_set)
              | (SOME x, SOME e) =>
                    (mk_monad @{const_name L2_returncall} (make_set [x]) throw_vars
                        [call_measure, e], make_set [x])
              | (NONE, _) =>
                    (mk_monad @{const_name L2_voidcall} empty_set throw_vars
                        [call_measure], empty_set)

          (*
           * We have a list of arguments; some may be expressions that refer to
           * global variables, while others will be purely local variables. We
           * just emit them all as "L2_gets" calls, and will clean them up
           * later.
           *)
          val extractors = foldr (
            fn ((updated_var, read_vars, is_globals_reader, expr), rest) =>
              let
                val ret_type = (make_set [("x'", fastype_of expr |> body_type)])
                val rest_type = (make_set [("x'", l2monad_ret_type rest)])
                val getter = mk_monad @{const_name L2_folded_gets} ret_type throw_vars
                                      [expr, Utils.ml_str_list_to_isa [fst updated_var]]
              in
                mk_monad @{const_name "L2_seq"} rest_type throw_vars [
                  getter,
                  Utils.abs_over (fst updated_var) (name_map updated_var) rest]
              end
              )
              call
              arg_setup_vals
          val read_vars = union_sets (map #2 expr_list) UNION ret_read_vars

          (* Generate a proof. *)
          val my_debug_tac = if false then print_tac ctxt else fn _ => all_tac
          val L2_call_thms = @{thms L2corres_returncall L2corres_voidcall L2corres_modifycall}
          val L2_reccall_thms = @{thms L2corres_recursive_returncall L2corres_recursive_voidcall L2corres_recursive_modifycall}
          val thm =
            mk_corresXF_thm ctxt prog_info name_map ret_vars throw_vars read_vars extractors l1_term (
              (my_debug_tac "unfold folded_gets"
                    THEN (REPEAT (rtac @{thm L2corres_folded_gets} 1)))
              THEN (my_debug_tac "apply callee proof"
                    THEN FIRST (map (fn thm => rtac thm 1 THEN
                                               rtac (#mono_thm dest_fn) 1 THEN
                                               rtac callee_thm 1)
                                    L2_call_thms @
                                map (fn thm => rtac thm 1 THEN
                                               rtac callee_thm 1)
                                    L2_reccall_thms))
              THEN (my_debug_tac "final simp"
                    THEN (REPEAT (CHANGED (asm_full_simp_tac (setup_l2_ss ctxt) 1))))
            )
        in
          inject (read_vars, ret_vars, extractors, thm)
        end)
        end
    | _ => Utils.invalid_input "a parsed L1 term"
        (l1_term |> head_of |> PolyML.makestring)
end

(* Get the expected type of a function from its name. *)
fun get_expected_l2_fn_type prog_info fn_info fn_name =
let
  val fn_def = FunctionInfo.get_function_def fn_info fn_name
  val fn_params_typ = @{typ nat} :: map snd (#args fn_def)
in
  fn_params_typ ---> mk_l2monadT (#globals_type prog_info) (#return_type fn_def) @{typ unit}
end

(* Get arguments passed into the function. *)
fun get_expected_l2_fn_args prog_info fn_info fn_name =
let
  val fn_def = FunctionInfo.get_function_def fn_info fn_name
in
  map (apfst ProgramInfo.demangle_name) (#args fn_def)
end

fun get_expected_l2_fn_thm prog_info fn_info ctxt fn_name fn_free fn_args _ measure_var =
let
  (* Fetch input/output params for monad type. *)
  val (input_params, output_params) = get_fn_input_output_vars prog_info fn_info fn_name

  (* Get mapping from internal variable names that we use to the names passed
   * in "fn_args". *)
  val fn_def = FunctionInfo.get_function_def fn_info fn_name
  val args = map fst (#args fn_def)
  val m = Symtab.make (args ~~ fn_args)
  fun name_map (n, _) = Symtab.lookup m n |> the
in
    mk_corresXF_prop (Proof_Context.theory_of ctxt) prog_info name_map
      output_params empty_set input_params
      (betapplys (fn_free, measure_var :: fn_args))
      (betapply (#const fn_def, measure_var))
end

(* Extract the abstract body of a L2corres theorem. *)
fun get_body_of_thm ctxt thm =
  Thm.concl_of (Drule.gen_all (Variable.maxidx_of ctxt) thm)
  |> HOLogic.dest_Trueprop
  |> dest_L2corres_term_abs

fun get_l2corres_thm ctxt prog_info fn_info do_opt trace_opt fn_name
    callee_terms fn_args l1_term init_unfold = let

  (* Get information about the return variable. *)
  val fn_def = FunctionInfo.get_function_def fn_info fn_name

  (* Get return variables. *)
  val (fn_input_vars, fn_ret_vars) = get_fn_input_output_vars prog_info fn_info fn_name

  (* Get mapping from internal variable names to external arguments. *)
  val m = Symtab.make (map fst (#args fn_def) ~~ fn_args)
  fun name_map_ext (n, T) = Symtab.lookup m n |> the
  fun name_map_internal (n, T) = Free ("lvar'" ^ n, T)

  (*
   * Many constructs from SIMPL (and also L1) are in set form, but we really
   * need them to be in functional form to be able to effectively parse them.
   * In particular we can parse:
   *
   *      (%s. n_' s)
   *
   * but not:
   *
   *      {s. n_' s}
   *
   * We do some basic conversions here to convert common sets into lambda
   * functions.
   *)
  val l2_unfolds = map (fn x => (mk_meta_eq x) handle (THM _) => x) (L2UnfoldThms.get ctxt)
  val init_rule = Thm.cterm_of ctxt l1_term
    |> (Conv.rewr_conv (safe_mk_meta_eq init_unfold)
        then_conv Raw_Simplifier.rewrite (put_simpset HOL_basic_ss ctxt) false l2_unfolds)

  (* Extract the term we will be working with. *)
  val source_term = Thm.concl_of init_rule |> Logic.dest_equals |> snd
    |> Utils.unsafe_unvarify

  (* Do basic parsing. *)
  val parsed_term = parse_l1 ctxt prog_info fn_info name_map_internal source_term

  (* Get a list of all variables either read from or written to. *)
  val all_vars = Prog.fold_prog
      (K I)
      (fn (_, vars, _) => fn old_vars => vars UNION old_vars)
      (fn mod_var => fn old_vars =>
        case mod_var of SOME x => (Varset.insert x old_vars) | NONE => old_vars)
      (K I)
      parsed_term empty_set

  (* Perform liveness analysis of the function. *)
  val liveness_data = calc_live_vars parsed_term fn_ret_vars

  (*
   * Get information about modified variables.
   *
   * "NONE" represents "modifies potentially all variables"; we modify
   * the results to fit this.
   *)
  val modification_data =
      get_modified_vars parsed_term
      |> map_prog (fn x => Option.getOpt (x, all_vars)) I I I

  (* Combine collected data. *)
  fun zip_node_data a b c =
    zip_progs a (zip_progs b c)
    |> map_prog (fn (a, (b, c)) => (a, b, c)) fst fst fst
  val input_term = zip_node_data parsed_term liveness_data modification_data

  (* Ensure that the only live variables at the beginning of the function are
   * those that are function inputs. *)
  val fn_inputs = get_node_data liveness_data
  val fn_params = #args fn_def
  val excess_inputs = fn_inputs MINUS (make_set fn_params)
  val _ =
    if excess_inputs <> empty_set then
      warning
          ("Input function '" ^ fn_name ^ "' has unresolved variables: "
              ^ PolyML.makestring (dest_set excess_inputs))
    else
      ()

  (* Do the conversion. *)
  val (vars_read, _, term, thm) = do_conv ctxt prog_info fn_info name_map_internal fn_input_vars
                                          callee_terms fn_ret_vars false empty_set input_term

  (* Replace our internal terms with external terms. *)
  val replacements = (map name_map_internal fn_params) ~~ (map name_map_ext fn_params)
  val term = Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt)
      [] [Termtab.lookup (Termtab.make replacements)] term

  (*
   * Generate a theorem with a folded RHS, with the LHS unfolded.
   *
   * The idea here is that we must generate a theorem of the form we
   * committed to in "get_expected_l2_fn_thm", but with schematic variables.
   *)
  val new_thm =
    mk_corresXF_prop (Proof_Context.theory_of ctxt) prog_info name_map_ext
        fn_ret_vars empty_set fn_input_vars
        term l1_term
    |> Thm.cterm_of ctxt
    |> Goal.init
    |> apply_tac "unfold RHS" (EqSubst.eqsubst_tac ctxt [0] [init_rule] 1)
    |> apply_tac "generalise guard" (rtac @{thm L2corres_guard_imp} 1)
    |> apply_tac "solve main goal" (rtac thm 1)
    |> apply_tac "solve guard_imp" (REPEAT (FIRST [
          rtac @{thm HOL.refl} 1,
          rtac @{thm pred_andI} 1,
          rtac @{thm conjI} 1,
          CHANGED (asm_full_simp_tac (setup_l2_ss ctxt) 1)]))
    |> Goal.finish ctxt

  (* Remove intermediate scaffolding. *)
  val new_thm = Conv.fconv_rule (
      Utils.remove_meta_conv (fn ctxt =>
        Utils.nth_arg_conv 5 (
          Raw_Simplifier.rewrite ctxt false @{thms L2_remove_scaffolding_1}
          then_conv
          Raw_Simplifier.rewrite ctxt false @{thms L2_remove_scaffolding_2})) ctxt) new_thm

  (* Gather statistics. *)
  val _ = Statistics.gather ctxt "L2" fn_name
      (Thm.prop_of new_thm |> HOLogic.dest_Trueprop |> (fn t => Utils.term_nth_arg t 4))

  (* Cleanup. *)
  val _ = writeln ("Simplifying (L2) " ^ fn_name)
  val new_thm = Simplifier.simplify (put_simpset HOL_basic_ss ctxt addsimps
                                       (* this rule is expensive *)
                                       (if do_opt then @{thms L2_unknown_bind} else []))
                                    new_thm

  val _ = writeln ("Simplifying (L2opt) " ^ fn_name)
  (* HACK: we need to avoid these simps until heap_lift *)
  val cleanup_del = @{thms ptr_coerce.simps ptr_add_0_id}
  val (new_thm, traces) = L2Opt.cleanup_thm_tagged (ctxt delsimps cleanup_del) new_thm
                                                   (if do_opt then 0 else 2) 5 trace_opt "L2"

  (* Gather post-simplification statistics. *)
  val _ = Statistics.gather ctxt "L2simp" fn_name
      (Thm.prop_of new_thm |> HOLogic.dest_Trueprop |> (fn t => Utils.term_nth_arg t 4))
in
  (new_thm, traces)
end

(*
 * Prove monad_mono property for recursive functions.
 *)

fun l2_monad_mono func_defs lthy =
let
  (*
   * For the induction, we need to have the form
   *   "\<And> m. (ALL a b... f m a b...) /\ (ALL a b... g m a b...) /\ ..."
   * and this gets annoying pretty quickly. But it is probably unavoidable.
   *)
  val measure = Free ("rec_measure'", @{typ nat})
  fun make_mono_step_stmt (func, def) =
      let
          (* def should be of the form "func ?locale_args... ?measure ?args... = ..." *)
          val (_, locale_args) = strip_comb func
          val (_, all_args) = Utils.lhs_of_eq (term_of_thm def) |> strip_comb
          val _ :: args = drop (length locale_args) all_args
          val args = args |> map (fn Var ((name, _), typ) => Free (name, typ))
      in
          fold (fn arg => fn t => @{mk_term "All ?P" P} (lambda arg t)) args
               (@{mk_term "monad_mono_step ?f ?m" (f, m)}
                    (lambda measure (betapplys (func, measure :: args)), measure))
      end
  val mk_conj_list = foldr1 (fn (a, b) => @{term "conj"} $ a $ b)

  val func_expand = map (fn (_, def) => EqSubst.eqsubst_tac lthy [0] [Utils.abs_def lthy def]) func_defs
  val tac = 
    rtac @{thm nat.induct} 1
      THEN EVERY (map (fn expand =>
                          TRY (rtac @{thm conjI} 1)
                          THEN REPEAT (rtac @{thm allI} 1)
                          THEN expand 1
                          THEN rtac @{thm monad_mono_step_L2_recguard_0} 1) func_expand)
    THEN REPEAT (etac @{thm conjE} 1)
    THEN EVERY (map (fn expand =>
                        TRY (rtac @{thm conjI} 1)
                        THEN REPEAT (rtac @{thm allI} 1)
                        THEN expand 1
                        THEN REPEAT (FIRST (
                          map (fn t => rtac t 1) @{thms L2_monad_mono_step_rules}
                          (* We use simp to solve assumptions (atac doesn't work
                           * because the assumptions are ALL-quantified) and to
                           * split tuple cases. *)
                          @ [CHANGED (asm_full_simp_tac (clear_simpset lthy
                               addsimps @{thms split_conv split_tupled_all}) 1)])))
                func_expand)

  val mono_thm = map make_mono_step_stmt func_defs
                 |> mk_conj_list
                 |> (fn t => Logic.all measure (@{term "Trueprop"} $ t))
                 |> (fn t => Goal.prove lthy [] [] t (K tac))

  (* We have finished the induction, now we extract the individual results. *)
  fun make_mono_stmt (func, def) =
      let
          val (_, locale_args) = strip_comb func
          val (_, all_args) = Utils.lhs_of_eq (term_of_thm def) |> strip_comb
          val _ :: args = drop (length locale_args) all_args
          val args = args |> map (fn Var ((name, _), typ) => Free (name, typ))
      in
          fold Logic.all args
               (@{mk_term "Trueprop (monad_mono ?f)" f}
                    (lambda measure (betapplys (func, measure :: args))))
      end
  val final_thms = func_defs
        |> map (fn func_def => Goal.prove lthy [] [] (make_mono_stmt func_def)
                     (K (asm_full_simp_tac (lthy addsimps [@{thm monad_mono_alt_def}, mono_thm]) 1)))
in
  final_thms
end   

(*
 * Translate all functions from L1 to L2 format.
 *)
fun translate_l2 filename fn_info do_opt trace_opt l2_function_name lthy =
let
  val prog_info = ProgramInfo.get_prog_info lthy filename

  (* Abstract the function, returning a corres theorem. *)
  fun convert ctxt fn_name callee_terms measure_var fn_args = let
    (* Fetch the function body from L1. *)
    val l1_def = FunctionInfo.get_function_def fn_info fn_name
    val l1_body_def = #definition l1_def WHERE [
            ("rec_measure'", Thm.cterm_of ctxt measure_var)]
  
    val (thm, traces) = get_l2corres_thm ctxt prog_info fn_info do_opt trace_opt
        fn_name callee_terms fn_args
        (betapply (#const l1_def, measure_var)) l1_body_def
  in (get_body_of_thm ctxt thm, thm, traces) end

  (* Update function information. *)
  fun update_function_defs lthy fn_def =
    FunctionInfo.fn_def_update_const (Utils.get_term lthy (l2_function_name (#name fn_def))) fn_def
    |> FunctionInfo.fn_def_update_args (map (apfst ProgramInfo.demangle_name) (#args fn_def))
    |> FunctionInfo.fn_def_update_definition (
        (the (AutoCorresData.get_def (Proof_Context.theory_of lthy)
            filename "L2def" (#name fn_def))))
in
  AutoCorresUtil.do_translation_phase "L2" filename prog_info fn_info
    (get_expected_l2_fn_type prog_info fn_info)
    (get_expected_l2_fn_thm prog_info fn_info)
    (get_expected_l2_fn_args prog_info fn_info)
    l2_function_name
    convert
    l2_monad_mono
    update_function_defs
    @{thm L2corres_recguard_0}
    lthy
end

end
