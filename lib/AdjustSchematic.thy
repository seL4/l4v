(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory AdjustSchematic (* FIXME: bitrotted *)
imports "~~/src/HOL/Main"
begin

lemma meta_arg_cong:
  "f == g \<Longrightarrow> f x == g x"
  by simp

text {*
The tactic defined below will adjust schematic applications of the form
"?P (a, (b, c)) d True e f" in the current goal into the form
"?P' a b c d e f" (by substituting P' for P in a somewhat complex way).

The aim of the game is to get more straightforward unification in the current
goal.
*}

ML {*
structure AdjustSchematics = struct

fun mk_inst (nm, t) = let
    val (v, xs) = strip_comb t
    val (Ts, T) = strip_type (fastype_of v)
    val xTs = xs ~~ take (length xs) Ts
    val ranT = drop (length xs) Ts ---> T
    val bs = map Bound (rev (0 upto (length xs - 1)))
    
    fun mk_var s T (Bound n) = Var ((s, n), T)
      | mk_var _ _ t = raise TERM ("mk_inst: mk_var:", [t])

    fun varify_tup s (((pr as Const (@{const_name Pair}, T)) $ x $ y), _, b)
        = (pr $ varify_tup (s ^ "fst") (x, domain_type T, b)
                $ varify_tup (s ^ "snd") (y, domain_type (range_type T), b))
        | varify_tup s (_, T, b) = mk_var s T b

    fun double_app f (t1, t2) = let val app = f t1
      in (app, head_of app $ t2) end

    fun delve_pair (tup as (Const (@{const_name Pair}, _) $ x $ y), ts)
        = delve_pair (x, double_app HOLogic.mk_fst ts)
            @ delve_pair (y, double_app HOLogic.mk_snd ts)
        | delve_pair (_, (t1, t2)) = [(t1, t2, fastype_of t1)]

    val yTs = maps (fn ((Const _, _), _) => []
        | (((t as Const (@{const_name Pair}, _) $ _ $ _), T), b)
            => delve_pair (t, (varify_tup "x" (t, T, b), b))
        | ((_, T), b) => [(mk_var "x" T b, b, T)]) (xTs ~~ bs)

    val f = Free (nm, map #3 yTs ---> ranT)
    val f_app = list_comb (f, map #2 yTs)
    val rhs = fold (fn T => fn t => Abs ("x", T, t)) (rev (map snd xTs)) f_app

    val pat = list_comb (f, map #1 yTs)

  in ((v, rhs), pat) end

fun get_schem_apps (f $ x) = if is_Var (head_of f)
    then [f $ x] else get_schem_apps f @ get_schem_apps x
  | get_schem_apps (Abs (_, _, t)) = get_schem_apps t
  | get_schem_apps _ = []

fun convertible_schem_app t = exists
  (fn (Const _) => true
    | (Const (@{const_name Pair}, _) $ _ $ _) => true
    | _ => false)
  (snd (strip_comb t))

fun rewr_fst_snd ctxt = Simplifier.rewrite
    (put_simpset HOL_basic_ss ctxt addsimps @{thms fst_conv snd_conv})

fun apply_insts insts ctxt t = let
    val inst_pairs = map (apply2 (Thm.cterm_of ctxt) o fst) insts
    val rewrs = map (rewr_fst_snd ctxt o Thm.cterm_of ctxt o snd) insts
    val frees = map (snd #> head_of #> dest_Free #> fst) insts

  in cterm_instantiate inst_pairs t
    |> (ALLGOALS (CONVERSION (Thm.beta_conversion true))
        THEN Raw_Simplifier.rewrite_goals_tac ctxt rewrs)
    |> Seq.hd |> Drule.generalize ([], frees)
    |> Seq.single
  end

fun schem_app_name t = (head_of t |> dest_Var |> fst |> fst, t)

fun tac ctxt = CSUBGOAL (fn (csg, i) => let
    val convertibles = get_schem_apps (Envir.beta_eta_contract (Thm.term_of csg))
        |> filter convertible_schem_app
        |> map schem_app_name
  in if null convertibles then no_tac
    else (fn t => apply_insts (convertibles
        |> Term.variant_frees (Thm.prop_of t)
        |> map mk_inst) ctxt t)
  end)

end
*}

schematic_goal
  "\<And>x y z. ?P (x, y) True (a, (b, (c, d), e)) z"
  apply (tactic {* AdjustSchematics.tac @{context} 1 *})
  oops

end
