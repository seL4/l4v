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
 * Prettify bound variable names in L2 monadic bodies.
 *)

structure PrettyBoundVarNames =
struct

(* Return the first result, unless it is NONE, in which case return the
 * second. *)
fun try_both a b =
  case (a ()) of
    SOME x => SOME x
  | NONE => b ()

(* Get a list of names that the given block of code returns. *)
fun get_var_names_ret t =
  case t of
    (Abs (_, _, V)) => get_var_names_ret V
  | (Const (@{const_name "case_prod"}, _) $ M $ _) =>
      get_var_names_ret M
  | (Const (@{const_name "case_prod"}, _) $ M) =>
      get_var_names_ret M
  | (Const (@{const_name "L2_gets"}, _) $ _ $ v) =>
      SOME (Utils.isa_str_list_to_ml v)
  | (Const (@{const_name "L2_unknown"}, _) $ v) =>
      SOME (Utils.isa_str_list_to_ml v)
  | (Const (@{const_name "L2_while"}, _) $ _ $ _ $ _ $ v) =>
      SOME (Utils.isa_str_list_to_ml v)
  | (Const (@{const_name "L2_throw"}, _) $ _ $ _) =>
      NONE
  | (Const (@{const_name "L2_condition"}, _) $ _ $ L $ R) =>
      try_both
        (fn () => get_var_names_ret L)
        (fn () => get_var_names_ret R)
  | (Const (@{const_name "L2_seq"}, _) $ _ $ R) =>
      get_var_names_ret R
  | (Const (@{const_name "L2_catch"}, _) $ L $ R) =>
      try_both
        (fn () => get_var_names_ret L)
        (fn () => get_var_names_ret R)
  | (Const (@{const_name "L2_call"}, _) $ _) =>
      (* make up a name *)
      SOME ["ret'"]
  (* In the following two cases, f is an L2_call *)
  | (Const (@{const_name "exec_concrete"}, _) $ _ $ f) =>
      get_var_names_ret f
  | (Const (@{const_name "exec_abstract"}, _) $ _ $ f) =>
      get_var_names_ret f
  | _ => NONE

(* Get a list of names that the given block of code throws. *)
fun get_var_names_throw t =
  case t of
    (Abs (_, _, V)) => get_var_names_throw V
  | (Const (@{const_name "case_prod"}, _) $ M $ _) =>
      get_var_names_throw M
  | (Const (@{const_name "case_prod"}, _) $ M) =>
      get_var_names_throw M
  | (Const (@{const_name "L2_gets"}, _) $ _ $ _) =>
      NONE
  | (Const (@{const_name "L2_while"}, _) $ _ $ B $ _ $ _) =>
      get_var_names_throw B
  | (Const (@{const_name "L2_throw"}, _) $ _ $ v) =>
      SOME (Utils.isa_str_list_to_ml v)
  | (Const (@{const_name "L2_condition"}, _) $ _ $ L $ R) =>
      try_both
        (fn () => get_var_names_throw L)
        (fn () => get_var_names_throw R)
  | (Const (@{const_name "L2_seq"}, _) $ L $ R) =>
      try_both
        (fn () => get_var_names_throw L)
        (fn () => get_var_names_throw R)
  | (Const (@{const_name "L2_catch"}, _) $ _ $ R) =>
      get_var_names_throw R
  | _ => NONE

(* Regenerate bound variable names based on annotations on "L2_gets" and
 * "L2_throw" statements. *)
local
fun pretty_split_vars (SOME (x::xs)) (Abs (_, T, R))
      = Abs (x, T, R)
  | pretty_split_vars _ (Abs (_, T, R))
      = Abs (Name.uu_, T, R)
  | pretty_split_vars (SOME (x::xs)) (Const (@{const_name "case_prod"}, T) $ Abs (_, T', R))
      = (Const (@{const_name "case_prod"}, T) $ Abs (x, T', (pretty_split_vars (SOME xs) R)))
  | pretty_split_vars _ (Const (@{const_name "case_prod"}, T) $ Abs (_, T', R))
      = (Const (@{const_name "case_prod"}, T) $ Abs (Name.uu_, T', (pretty_split_vars NONE R)))
  | pretty_split_vars _ t = t

(* Add state variable "s" for L2_while,
   renaming any existing "s" if necessary *)
fun map_option _ NONE = NONE
  | map_option f (SOME x) = SOME (f x)
fun sprime str = if str = "s" ^ String.implode (List.tabulate (String.size str - 1, K #"'"))
                    then str ^ "'" else str
fun while_add_st_var vars = map sprime vars
in
fun pretty_bound_vars t =
  case t of
    (Const (@{const_name "L2_seq"}, t1) $ L $ R) =>
      (Const (@{const_name "L2_seq"}, t1) $ L $ (pretty_split_vars (get_var_names_ret L) R))
  | (Const (@{const_name "L2_catch"}, t1) $ L $ R) =>
      (Const (@{const_name "L2_catch"}, t1) $ L $ (pretty_split_vars (get_var_names_throw L) R))
  | (Const (@{const_name "L2_while"}, t1) $ C $ B $ i $ n) =>
    let
      val names = get_var_names_ret t
    in
      (Const (@{const_name "L2_while"}, t1)
        $ (pretty_split_vars (map_option while_add_st_var names) C)
        $ (pretty_split_vars names B)
        $ i $ n)
    end
  | _ => t
end

(* Apply "f" to every subterm, bottom-up. *)
fun map_term_bottom f (a $ b)
      = f ((map_term_bottom f a) $ (map_term_bottom f b))
  | map_term_bottom f (Abs (v, t, b))
      = f (Abs (v, t, map_term_bottom f b))
  | map_term_bottom f t = f t

(* Generate a theorem that "ct_l = ct_r", assuming it can be trivially proven. *)
fun rename_abs_thm ctxt ct_l ct_r =
let
  val input_type = fastype_of (Thm.term_of ct_l)
  val eq_op = Thm.cterm_of ctxt (
      Const (@{const_name "Pure.eq"}, input_type --> input_type --> @{typ prop}))
  val result = Drule.list_comb (eq_op, [ct_l, ct_r])
in
  Goal.init result
  |> simp_tac (put_simpset HOL_basic_ss ctxt) 1 |> Seq.hd
  |> Goal.finish ctxt
end


(* Generate a thm of the form "A == B", where "B" has pretty bound variable
 * names. *)
fun pretty_bound_vars_thm ctxt ct keep_going =
let
  val rhs = map_term_bottom pretty_bound_vars (Thm.term_of ct)

  (* (JIRA VER-281) We want to track down stray uu_ that appear in user-visible
   * output. So this code fails hard if it finds one. *)
  fun detect_visible_bad_vars barf term =
    case term of
        (Abs (var, typ, body)) => (if Term.is_dependent body then barf var typ term else ();
                                   detect_visible_bad_vars barf body)
      | f $ x => (detect_visible_bad_vars barf f; detect_visible_bad_vars barf x)
      | _ => ()
  fun barf_uu var typ _ =
    if String.isSuffix "_" var
       then Utils.CTERM_non_critical keep_going
                ("autocorres: Internal var " ^ var ^ "::" ^
                 @{make_string} typ ^ " is exposed.")
                [ct, Thm.cterm_of ctxt rhs]
       else ()
  val _ = detect_visible_bad_vars barf_uu rhs
  val crhs = Thm.cterm_of ctxt rhs
in
  rename_abs_thm ctxt ct crhs
end

end
