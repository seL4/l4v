(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Benchmark basic Isabelle operations using the benchmark framework.
 *)

val benchmark = Benchmark.benchmark;
val benchmark_set = Benchmark.benchmark_set;
val category = Benchmark.category;

(* Generate a term of approximately the given size. *)
val base_term = @{term "12 = (6 + 6 :: nat)"};
fun gen_term 0 = base_term
  | gen_term n = (Const (@{const_name "HOL.conj"}, @{typ "bool => bool => bool"}) $ base_term $ (gen_term (n - 1)))
val base_type = Syntax.parse_typ @{context} "?'a"
fun gen_type 0 = base_type
  | gen_type n = HOLogic.mk_tupleT [@{typ "nat + bool"}, gen_type (n-1)]
fun gen_prop n = gen_term n |> HOLogic.mk_Trueprop

(* Various terms we use to benchmark. *)
val test_terms = [
    gen_prop 1,
    gen_prop 10,
    gen_prop 100,
    gen_prop 1000
   ];
val test_types = [
    gen_type 1,
    gen_type 10,
    gen_type 100,
    gen_type 1000
   ];
val test_cterms = map (cterm_of @{theory}) test_terms;

(*********************************************************************)
(*
 * Term rewriting benchmarks.
 *)
category "Subgoal Rewriting";

let
  (* Generate terms which have a long chain of junk followed by what we want to rewrite. *)
  fun gen_rewrite_term 0 = @{term "cat | dog"}
    | gen_rewrite_term n = (Const (@{const_name "HOL.conj"}, @{typ "bool => bool => bool"})
        $ @{term "12 = (6 + 6 :: nat)"}
        $ (gen_term (n - 1)))
  fun gen_rewrite_prop n = gen_term n |> HOLogic.mk_Trueprop
  val test_rewrite_terms = [
      gen_rewrite_prop 1,
      gen_rewrite_prop 10,
      gen_rewrite_prop 100,
      gen_rewrite_prop 1000
     ];

  (* Benchmark a tactic. *)
  fun benchmark_rewrite name tac terms =
    let
      val goals = map (fn x => (x, cterm_of @{theory} x |> Goal.init)) terms;
      fun f (_, b) = tac b |> Seq.hd;
      fun measure (a, _) = size_of_term a
    in
      benchmark_set name f measure goals
    end;

  (* Rewrite conversion. *)
  fun recursive_conv ctxt ctrm =
    case (Thm.term_of ctrm) of
        (@{term "op |"} $ _ $ _) =>
          (Conv.rewr_conv @{thm disj_flip'}) ctrm
      | _ $ _ =>
          Conv.comb_conv (recursive_conv ctxt) ctrm
      | Abs _ =>
          Conv.abs_conv (fn (_, ctxt) => recursive_conv ctxt) ctxt ctrm
      | _ =>
          Conv.all_conv ctrm;
in
  benchmark_rewrite "conversion" (CONVERSION (recursive_conv @{context}) 1) test_rewrite_terms;
  benchmark_rewrite "simp_tac" (simp_tac (HOL_basic_ss addsimps [@{thm disj_flip}]) 1) test_rewrite_terms
end;

(*********************************************************************)
(*
 * Microbenchmarks of tactics.
 *
 * We create a lemma "5 < 10", and then solve it with various
 * tactics.
 *)
category "Tactic Benchmarks (Prove '5 < 10')";

fun benchmark_tactic name tac =
  benchmark name (fn _ =>
      @{prop "(5 :: nat) < 10"}
        |> cterm_of @{theory}
        |> Goal.init
        |> tac
        |> Seq.hd
        |> Goal.finish @{context});

benchmark_tactic "Arith_Data.arith_tac"           (Arith_Data.arith_tac @{context} 1);
benchmark_tactic "Lin_Arith.simple_tac"           (Lin_Arith.simple_tac @{context} 1);
benchmark_tactic "simp_tac (full simpset)"        (simp_tac @{context} 1);
benchmark_tactic "simp_tac (with precise lemma)"  (simp_tac (HOL_basic_ss addsimps [@{thm five_less_than_ten}]) 1);
benchmark_tactic "rtac (with precise lemma)"      (rtac @{thm five_less_than_ten} 1);
benchmark_tactic "cheat_tac"                      (Skip_Proof.cheat_tac @{theory});

benchmark "Skip_Proof.make_thm"
  (fn _ => Skip_Proof.make_thm @{theory} @{prop "(5 :: nat) < 10"});


(*********************************************************************)
(*
 * Macrobenchmarks of tactics.
 *)

category "Tactic Benchmarks (Macrobenchmarks)";

fun macrobenchmark_tactic name tac terms =
  let
    val goals = map (fn x => (x, cterm_of @{theory} x |> Goal.init)) terms;
    fun f (_, b) = tac b |> Seq.hd |> Goal.finish @{context};
    fun measure (a, _) = size_of_term a
  in
    benchmark_set name f measure goals
  end;

(* Test the simplifier *)
macrobenchmark_tactic "simp_tac (minimal)"
  (simp_tac (HOL_ss addsimps [@{thm twelve_equals_six_plus_six}]) 1) test_terms;

macrobenchmark_tactic "simp_tac (full simpset)"
  (simp_tac @{context} 1) test_terms;

(* Test using rtac. *)
macrobenchmark_tactic "rtac (repeated)" (
  (REPEAT (
    (rtac @{thm conjI} 1)
      THEN (rtac @{thm twelve_equals_six_plus_six}) 1)
  ) THEN (rtac @{thm twelve_equals_six_plus_six} 1)) test_terms;

(*
 * Test using conversions; recursively decend into the tree, rewriting
 * terms as we go along.
 *)
fun recursive_conv ctxt ctrm =
  case (Thm.term_of ctrm) of
      (@{term "(op =) :: nat => nat => bool"} $ _ $ _) =>
        (Conv.rewr_conv @{thm twelve_equals_six_plus_six'}) ctrm
    | (@{term "HOL.conj"} $ _ $ _) =>
        (Conv.comb_conv (recursive_conv ctxt) then_conv Conv.rewr_conv @{thm true_conj1}) ctrm
    | _ $ _ =>
        Conv.comb_conv (recursive_conv ctxt) ctrm
    | Abs _ =>
        Conv.abs_conv (fn (_, ctxt) => recursive_conv ctxt) ctxt ctrm
    | _ =>
        Conv.all_conv ctrm;
macrobenchmark_tactic "conversion"
  ((CONVERSION (recursive_conv @{context}) 1) THEN (simp_tac HOL_ss 1)) test_terms;


(*********************************************************************)
(*
 * Simplification benchmarks.
 *)
category "Term Simplification";

val ss = HOL_basic_ss addsimps [@{thm p_or_not_p}];

benchmark "rewrite"                           (fn _ => Simplifier.rewrite ss @{cterm "a \<or> b"});
benchmark "rewrite (full simpset)"            (fn _ => Simplifier.rewrite @{context} @{cterm "a \<or> \<not> a"});
benchmark "failing rewrite"                   (fn _ => Simplifier.rewrite HOL_basic_ss @{cterm "a \<or> b"});
benchmark "failing rewrite (full simpset)"    (fn _ => Simplifier.rewrite @{context} @{cterm "a \<or> b"});


(*********************************************************************)
(*
 * Resolution.
 *)
category "Resolution";

benchmark "'OF' theorem resolution" (fn _ => @{thm sym} OF [@{thm sym}]);

(* Create a bunch of theorems and terms. *)
val rtac_thms = map (fn t =>
  let
    val goal = cterm_of @{theory} t |> Goal.init;
    val sol = simp_tac @{context} 1 goal |> Seq.hd |> Goal.finish @{context}
  in
    (t, goal, sol)
  end) test_terms;

(* See how long it takes to resolve terms of various sizes. *)
benchmark_set "rtac" (fn (_, goal, sol) => rtac sol 1 goal) (fn (t, _, _) => size_of_term t) rtac_thms;


(*********************************************************************)
(*
 * Syntax
 *)
category "Syntax";

(* Parsing a string. *)
val test_strings = map (fn t => (t, Syntax.pretty_term @{context} t |> Pretty.str_of)) test_terms;
benchmark_set "Syntax.parse_term"
  (fn (_, s) => Syntax.parse_term @{context} s)
  (fn (t, _) => size_of_term t)
  test_strings;

(* Add a type constraint. *)
benchmark_set "Syntax.type_constraint" (Syntax.type_constraint @{typ bool}) size_of_term test_terms;

(* Check term. *)
benchmark_set "Syntax.check_term" (fn t => Syntax.check_term @{context} t) size_of_term test_terms;

(*********************************************************************)
(*
 * Certification.
 *)
category "Term Certification and Typing";

(* Get the size of a term as a string. *)
benchmark_set "size_of_term"   size_of_term         size_of_term             test_terms;
benchmark_set "term_of"        term_of              (size_of_term o term_of) test_cterms;
benchmark_set "cterm_of"       (cterm_of @{theory}) size_of_term             test_terms;
benchmark_set "fastype_of"     fastype_of           size_of_term             test_terms;
benchmark_set "type_of"        type_of              size_of_term             test_terms;

(*********************************************************************)
(*
 * Miscellaneous functionality.
 *)
category "Miscellaneous";

benchmark "serial" serial;

(* Unification of types. *)
benchmark_set "Sign.typ_match"
    (fn a => Sign.typ_match @{theory} (a,a) Vartab.empty) (size_of_typ) test_types;
benchmark_set "Sign.typ_unify"
    (fn a => Sign.typ_unify @{theory} (a,a) (Vartab.empty, 0)) (size_of_typ) test_types;

