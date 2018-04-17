(*
 *
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
theory Subseq_Abbreviation

imports Main

keywords "subseq_abbreviation" :: thy_decl

begin

text {* Splicing subsequences of terms and saving as abbreviations.

Intended for pulling out a subset of lines of a monadic definition
and naming it. Handles lambdas on the right hand side as necessary
for that.

Can also be used to name a subsequence of conjuncts, for instance,
or anything else left-associated with some particular constructor.
Doesn't work on lists because they can't be reassociated (the types
are different).
*}

ML {*
structure Subseq_Abbreviation = struct

exception Subsequence_Not_Found

fun app_cons_dummy cons x y
    = Const (cons, dummyT) $ x $ y

fun get_subseq_to_tail cons match_last (Const c $ x $ y) = if fst c <> cons
    then Const c $ x $ y
    else if match_last x
    then x else app_cons_dummy cons x (get_subseq_to_tail cons match_last y)
  | get_subseq_to_tail cons match_last (Abs (nm, T, t))
    = Abs (nm, T, get_subseq_to_tail cons match_last t)
  | get_subseq_to_tail _ _ t = t

fun lazy_abs (nm, T, t) = if loose_bvar1 (t, 0)
  then Abs (nm, T, t) else incr_boundvars ~1 t

fun get_subseq cons match_first match_last (Const c $ x $ y) = if fst c <> cons
    then raise Subsequence_Not_Found
    else if match_first x
    then get_subseq_to_tail cons match_last (Const c $ x $ y)
    else get_subseq cons match_first match_last y
  | get_subseq cons match_first match_last (Abs (nm, T, t))
    = lazy_abs (nm, T, get_subseq cons match_first match_last t)
  | get_subseq _ _ _ _ = raise Subsequence_Not_Found

fun find_subseq cons match_first match_last (f $ x)
    = (get_subseq cons match_first match_last (f $ x)
    handle Subsequence_Not_Found => (find_subseq cons match_first match_last f
        handle Subsequence_Not_Found => find_subseq cons match_first match_last x))
  | find_subseq cons match_first match_last (Abs (nm, T, t))
    = lazy_abs (nm, T, find_subseq cons match_first match_last t)
  | find_subseq _ _ _ _ = raise Subsequence_Not_Found

fun mk_pat i (t as Abs (nm, T, _)) = mk_pat (i + 1) (betapply (t, Var ((nm, i), T)))
  | mk_pat _ t = t

fun lambda_frees_vars ctxt ord_t t = let
    fun is_free t = is_Free t andalso not (Variable.is_fixed ctxt (Term.term_name t))
    fun is_it t = is_free t orelse is_Var t
    val get = fold_aterms (fn t => if is_it t then insert (op =) t else I)
    val all_vars = get ord_t []
    val vars = get t []
    val ord_vars = filter (member (op =) vars) all_vars
  in fold lambda ord_vars t end

fun add_reassoc b lambda_term cname thm_info ctxt = let
    val thm = singleton (Attrib.eval_thms ctxt) thm_info
    val (xs, _) = Term.strip_abs lambda_term
    val xxs = Variable.variant_frees ctxt [] (("x", dummyT) :: xs)
    val freeTs = fold (Term.add_tfreesT o snd) xxs []
    val term = betapplys (lambda_term, map Free (tl xxs))
    val lhs = Const (cname, dummyT) $ term $ Free (hd xxs)
      |> Syntax.check_term ctxt
      |> Thm.cterm_of ctxt
    val rew = Simplifier.rewrite (clear_simpset ctxt addsimps [thm]) lhs
      |> Thm.symmetric
      |> Drule.generalize (map fst freeTs, map fst xxs)
    val br = Binding.suffix_name "_reassoc" b
    val (_, ctxt) = Local_Theory.note ((br, []), [rew]) ctxt
    val pretty_decl = Pretty.block [Pretty.str (Binding.name_of br ^ ":\n"),
        Thm.pretty_thm ctxt rew]
  in Pretty.writeln pretty_decl; ctxt end

fun subseq_abbreviation mode name subseq_info reassoc int ctxt = let
    val (((constr, hd), tl), thm_info) = subseq_info
    val thm = singleton (Attrib.eval_thms ctxt) thm_info
    val thy = Proof_Context.theory_of ctxt
    val decl = (name, NONE, Mixfix.NoSyn)
    val constr_term = Syntax.read_term ctxt constr
    val cname = case constr_term of Const c => fst c
      | _ => raise TERM ("supplied constructor not a constant", [constr_term])
    val hd_tm = Syntax.read_term ctxt hd |> mk_pat 12 |> Logic.varify_types_global
    val tl_tm = Syntax.read_term ctxt tl |> mk_pat 12 |> Logic.varify_types_global
    val subseq = find_subseq cname (fn t => Pattern.matches thy (hd_tm, t))
        (fn t => Pattern.matches thy (tl_tm, t)) (Thm.prop_of thm)
    val subseq_lambda = lambda_frees_vars ctxt (Thm.prop_of thm) subseq
      |> Syntax.check_term ctxt
    val lhs = Free (Binding.name_of name, fastype_of subseq_lambda)
    val eq = Logic.mk_equals (lhs, subseq_lambda)
    val ctxt = Specification.abbreviation mode (SOME decl) [] eq int ctxt
    val pretty_eq = Syntax.pretty_term ctxt eq
  in Pretty.writeln pretty_eq; case reassoc of NONE => ctxt
    | SOME reassoc_thm => add_reassoc name subseq_lambda cname reassoc_thm ctxt end

val seq_parse = Parse.term -- Parse.term -- Parse.term -- Parse.thm

val reassoc_parse = Scan.option (Parse.reserved "reassoc" |-- Parse.$$$ ":" |-- Parse.thm)

val _ =
  Outer_Syntax.local_theory' @{command_keyword subseq_abbreviation}
    "setup abbreviation for subsequence of definition"
    (Parse.syntax_mode -- Parse.binding -- seq_parse -- reassoc_parse
      >> (fn (((mode, name), subseq), reassoc) => subseq_abbreviation mode name subseq reassoc));

end
*}

text {*
Here's a simple example. There's a more complicated monadic test in
the associated test theory Subseq_Abbreviation_Test.
*}

experiment begin

definition
  "simple_test_subseq_abbr_body P Q =
    (P \<and> Q \<and> P \<and> P \<and> P \<and> True \<and> Q, [Suc 0, 0])"

subseq_abbreviation (input) simple_test_subseq_abbr
  "HOL.conj" "Q :: bool" "True" simple_test_subseq_abbr_body_def[where Q="Q :: bool"]
  reassoc: conj_assoc

end

end