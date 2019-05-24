(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory AddUpdSimps

imports Main
keywords "add_upd_simps" :: thy_decl

begin

ML \<open>
fun mk_var_app nm (f $ _) = let
    val (_, xs) = strip_comb f
    val n = length xs
    val T = domain_type (fastype_of f)
  in mk_var_app nm f $ Free (nm ^ string_of_int n, T) end
  | mk_var_app _ t = t

fun get_upd_apps (f $ (g $ x)) = if
  is_Const (head_of f) andalso is_Const (head_of g)
  andalso domain_type (fastype_of g) = range_type (fastype_of g)
  then mk_var_app "x" f $ (mk_var_app "y" (g $ x))
    :: get_upd_apps f @ get_upd_apps (g $ x)
  else get_upd_apps f @ get_upd_apps (g $ x)
  | get_upd_apps (f $ x) = get_upd_apps f @ get_upd_apps x
  | get_upd_apps (Abs (_, _, t)) = get_upd_apps t
  | get_upd_apps _ = []

fun mk_upd_simps ctxt upd_app (simps, done, n) = let
    val n = n + 1
    val _ = n <= 5000 orelse raise TERM ("mk_upd_simps: 5000", [upd_app])
    val (nm, _) = dest_Const (head_of upd_app)
    val def = Proof_Context.get_thm ctxt (nm ^ "_def")
    val rhs = case (mk_var_app "x" upd_app, upd_app)
      of (f $ _, _ $ (_ $ x)) => f $ x
      | _ => raise TERM ("mk_upd_simps: impossible", [upd_app])
    val prop = HOLogic.mk_eq (upd_app, rhs) |> HOLogic.mk_Trueprop
    val thm = Thm.trivial (Thm.cterm_of ctxt prop)
      |> simp_tac (ctxt addsimps [def, @{thm fun_eq_iff}] addsimps simps) 1
      |> Seq.hd
    val upd_apps_prem = Thm.prems_of thm |> maps get_upd_apps
      |> sort_distinct Term_Ord.fast_term_ord
      |> filter_out (Termtab.defined done)
      |> filter_out (curry (=) upd_app)
      |> filter_out (head_of #> dest_Const #> fst #> String.isPrefix "HOL.")
    val (simps2, done, n) = fold (mk_upd_simps ctxt)
        upd_apps_prem (simps, done, n)
    fun trace v = (Thm.pretty_thm ctxt thm |> Pretty.string_of |> warning;
      v)
    val thm = Drule.export_without_context thm
  in if length simps2 <> length simps
    then mk_upd_simps ctxt upd_app (simps2, done, n)
    else (if Thm.nprems_of thm = 0 then trace thm :: simps2 else trace simps2,
      Termtab.update (upd_app, ()) done, n) end
  handle ERROR _ => (warning (fst (dest_Const (head_of upd_app)) ^ ": no def.");
    (simps, done, n))

fun mk_upd_simps_tm ctxt t = let
    val uas = get_upd_apps t |> sort_distinct Term_Ord.fast_term_ord
    val (simps, _, _) = fold (mk_upd_simps ctxt) uas ([], Termtab.empty, 0)
  in simps end

fun add_upd_simps t exsimps ctxt = let
    val thms = mk_upd_simps_tm (ctxt addsimps exsimps) t
    val _ = map (Thm.pretty_thm ctxt #> Pretty.writeln) thms
  in if null thms then ctxt
    else (Local_Theory.notes [((@{binding upd_simps}, []), [(thms, [])])] ctxt |> #2)
      addsimps thms
  end

val add_upd_simps_syn = Outer_Syntax.local_theory @{command_keyword "add_upd_simps"}
  "recursively show updates don't matter to constants"
  (Parse.term -- Scan.optional
      (Parse.$$$ "(" |-- Scan.repeat Parse.thm --| Parse.$$$ ")") []
     >> (fn (t, simps) => fn ctxt => add_upd_simps (Syntax.read_term ctxt t)
         (Attrib.eval_thms ctxt simps) ctxt))
\<close>

end
