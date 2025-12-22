(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory FP_Eval_Tests
imports
  Lib.FP_Eval
  "HOL-Library.Sublist"
begin

section \<open>Controlling evaluation\<close>

subsection \<open>Skeletons\<close>

text \<open>
  A "skeleton" is a subterm of a given term. For example,
    "map (\<lambda>x. x + 1) [1, 2, 3]"
  could have the following skeleton (among others):
    "map (\<lambda>x. x + _) _"

  The "_" stand for schematic variables with arbitrary names,
  or dummy patterns (which are implemented as unnamed schematics).

  FP_Eval uses skeletons internally to keep track of which parts of
  a term it has already evaluated. In other words, schematic variables
  indicate already-normalised subterms.

  There are two useful predefined skeletons:
\<close>
ML_val \<open> FP_Eval.skel0 \<close>
text \<open>
  which is a special directive to evaluate all subterms; and
\<close>
ML_val \<open> FP_Eval.skel_skip \<close>
text \<open>
  which tells FP_Eval to skip evaluation.
\<close>

text \<open>
  If we use the full FP_Eval interface, we can input a skeleton manually
  and get the final skeleton as output.

  It's useful to input a nontrivial skeleton for the following reasons:
   \<bullet> if most of the term is known to be normalised, this can
      save unnecessary computation.
   \<bullet> if a tool runs FP_Eval on behalf of an end user, it may
      want to avoid evaluating function calls in the user's input terms.
      Alternatively, use explicit quotation terms
      (see "Preventing evaluation", below) if finer control is needed.

  The partial skeleton should match the structure of the input term.
  If there is any mismatch, FP_Eval tries to be conservative and
  evaluates the whole subterm (as if "skel0" had been given).
  However, this should not be relied upon.
  (FIXME: maybe stricter check in eval')

  By default, FP_Eval attempts full evaluation of the input, so it
  usually returns "skel_skip".

  However, evaluation is not complete when:
   \<bullet> the input skeleton skips some subterms;
   \<bullet> FP_Eval doesn't descend into un-applied lambdas;
   \<bullet> evaluation delayed due to cong rules.
  In these cases, FP_Eval would return a partial skeleton.
\<close>

(* TODO: add examples *)

subsection \<open>Congruence rules\<close>

text \<open>
  Use FP_Eval.add_cong or the second argument of FP_Eval.make_rules.
  These accept weak congruence rules, e.g.:
\<close>
thm if_weak_cong option.case_cong_weak

text \<open>
  Note that @{thm let_weak_cong} contains a hidden eta expansion, which FP_Eval
  currently doesn't understand. Use our alternative:
\<close>
thm FP_Eval.let_weak_cong'

ML_val \<open>
  @{assert} (not (Thm.eq_thm_prop (@{thm let_weak_cong}, @{thm FP_Eval.let_weak_cong'})));
\<close>

text \<open>
  Example: avoid evaluating both branches of an @{const If}
\<close>

ML_val \<open>
local
  fun eval eqns congs =
    FP_Eval.eval @{context} (FP_Eval.make_rules eqns congs)
  val input = (@{cterm "subseq [0::nat, 2, 4] [0, 1, 2, 3, 4, 5]"}, Bound 0);
in
  (* No cong rule -- blowup *)
  val r1 = eval @{thms list_emb_code} @{thms} input
           |> fst |> fst;
  (* if_weak_cong prevents early evaluation of branches *)
  val r2 = eval @{thms list_emb_code} @{thms if_weak_cong} input
           |> fst |> fst;

  (* Compare performance counters: *)
  val eqns = @{thms list_emb_code rel_simps simp_thms if_True if_False};
  val p1 = eval eqns @{thms} input |> snd;
  val p2 = eval eqns @{thms if_weak_cong} input |> snd;
end
\<close>

subsection \<open>Preventing evaluation\<close>

text \<open>
  Sometimes it is useful to prevent evaluation of any arguments.
  This can be done by adding a cong rule with no premises:
\<close>
context FP_Eval begin
definition "quote x \<equiv> x"
lemma quote_cong:
  "quote x = quote x"
  by simp
lemma quote:
  "x \<equiv> quote x"
  by (simp add: quote_def)
end

ML_val \<open>
local
  fun eval eqns congs =
    FP_Eval.eval @{context} (FP_Eval.make_rules eqns congs);
in
  (* By default, fp_eval evaluates all subterms *)
  val r1 = eval @{thms fun_upd_def} @{thms}
             (@{cterm "FP_Eval.quote (fun_upd f a b) c"}, Bound 0);
  (* Use quote_cong to hold all quoted subterms.
     Note how the resulting skeleton indicates unevaluated subterms. *)
  val r2 = eval @{thms fun_upd_def} @{thms FP_Eval.quote_cong}
             (@{cterm "FP_Eval.quote (fun_upd f a b) c"}, Bound 0);
  (* Now remove the quote_cong hold. fp_eval continues evaluation
     according to the previous skeleton. *)
  val r3 = fst r2 |> apfst Thm.rhs_of
           |> eval @{thms fun_upd_def} @{thms};
end;
\<close>


section \<open>Tests\<close>

subsection \<open>Basic tests\<close>

ML_val \<open>
local
  fun eval eqns congs =
    FP_Eval.eval @{context} (FP_Eval.make_rules eqns congs);
  val input = (@{cterm "2 + 2 :: nat"}, Bound 0);
in
  val ((result, Var _), counters) = eval @{thms arith_simps} @{thms} input;
  val _ = @{assert} (Thm.prop_of result aconv @{term "(2 + 2 :: nat) \<equiv> 4"});
end;
\<close>

text \<open>fp_eval does not rewrite under lambda abstractions\<close>
ML_val \<open>
local
  fun eval eqns congs =
    FP_Eval.eval @{context} (FP_Eval.make_rules eqns congs);
  val input = (@{cterm "(\<lambda>x. x + (2 + 2::nat))"}, Bound 0);
in
  val ((result, skel), _) = eval @{thms arith_simps} @{thms} input;
  val _ = @{assert} (not (is_Var skel) andalso Thm.is_reflexive result);
end
\<close>


subsection \<open>Cong rules\<close>

text \<open>Test for @{thm if_weak_cong}\<close>
ML_val \<open>
local
  fun eval eqns congs =
    FP_Eval.eval @{context} (FP_Eval.make_rules eqns congs);
  val input = (@{cterm "subseq [2::int,3,5,7,11] [0,1,2,3,4,5,6,7,8,9,10,11,12,13]"}, Bound 0);
in
  val r1 = eval @{thms list_emb_code rel_simps refl if_True if_False} @{thms} input;
  val r2 = eval @{thms list_emb_code rel_simps refl if_True if_False} @{thms if_weak_cong} input;

  val _ = @{assert} (Thm.term_of (Thm.rhs_of (fst (fst r1))) = @{term True});
  val _ = @{assert} (Thm.term_of (Thm.rhs_of (fst (fst r2))) = @{term True});

  (* Compare performance counters: *)
  val (SOME r1_rewrs, SOME r2_rewrs) =
        apply2 (snd #> Symtab.make #> (fn t => Symtab.lookup t "rewrites")) (r1, r2);
  val _ = @{assert} (r1_rewrs > 10000);
  val _ = @{assert} (r2_rewrs < 100);
end
\<close>


subsection \<open>Advanced usage\<close>

subsubsection \<open>Triggering breakpoints\<close>
ML_val \<open>
local
  fun break_4 t = Thm.term_of t = @{term "4 :: nat"};
  fun eval eqns congs break =
    FP_Eval.eval' @{context} (K (K ())) break false (FP_Eval.make_rules eqns congs);
  val input = (@{cterm "map Suc [2 + 2 :: nat, 2 + 3, 2 + 4, 2 + 5, 2 + 6]"}, Bound 0);
in
  (* Normal evaluation *)
  val ((result, Var _), _) = eval @{thms list.map arith_simps} @{thms} (K false) input;
  val _ = @{assert} (Thm.term_of (Thm.rhs_of result) aconv
                        @{term "[Suc 4, Suc 5, Suc 6, Suc 7, Suc 8]"});

  (* Evaluation stops after "4" is encountered *)
  val ((result2, skel), _) = eval @{thms list.map arith_simps} @{thms} break_4 input;
  val _ = @{assert} (Thm.term_of (Thm.rhs_of result2) aconv
                        @{term "map Suc [4::nat, 5, 2 + 4, 2 + 5, 2 + 6]"});
  (* Skeleton indicates evaluation is unfinished *)
  val _ = @{assert} (not (is_Var skel));
end;
\<close>

subsubsection \<open>Rule set manipulation\<close>
ML_val \<open>
local
  val rules0 = FP_Eval.empty_rules;
  val rules1 = FP_Eval.make_rules @{thms simp_thms arith_simps} @{thms if_weak_cong};
  val rules2 = FP_Eval.make_rules @{thms simp_thms if_False if_True fun_upd_apply}
                                @{thms if_weak_cong option.case_cong_weak};
in
  (* dest_rules returns rules *)
  val _ = @{assert} (apply2 length (FP_Eval.dest_rules rules1) <> (0, 0));
  (* test round-trip conversion *)
  val _ = @{assert} (let val (thms, congs) = FP_Eval.dest_rules rules2;
                         val (thms', congs') = FP_Eval.dest_rules (FP_Eval.make_rules thms congs);
                     in forall Thm.eq_thm_prop (thms ~~ thms')
                        andalso forall Thm.eq_thm_prop (congs ~~ congs') end);
  (* test that merging succeeds and actually merges rules *)
  fun test_merge r1 r2 =
    let val (r1_eqns, r1_congs) = FP_Eval.dest_rules r1;
        val (r2_eqns, r2_congs) = FP_Eval.dest_rules r2;
        val (r12_eqns, r12_congs) = FP_Eval.dest_rules (FP_Eval.merge_rules (r1, r2));
    in eq_set Thm.eq_thm_prop (r12_eqns, union Thm.eq_thm_prop r1_eqns r2_eqns)
       andalso eq_set Thm.eq_thm_prop (r12_congs, union Thm.eq_thm_prop r1_congs r2_congs)
    end;

  val _ = @{assert} (test_merge rules0 rules1);
  val _ = @{assert} (test_merge rules0 rules2);
  val _ = @{assert} (test_merge rules1 rules2);

  (* test that rules with conflicting arity are not allowed *)
  val conflict_arity = FP_Eval.make_rules @{thms fun_upd_def} @{thms};
  val _ = @{assert} (is_none (try FP_Eval.merge_rules (rules2, conflict_arity)));
  (* test that installing different cong rules is not allowed *)
  val conflict_cong = FP_Eval.make_rules @{thms} @{thms if_weak_cong[OF refl]};
  val _ = @{assert} (is_none (try FP_Eval.merge_rules (rules2, conflict_cong)));
end
\<close>

subsubsection \<open>Ordering of rules\<close>
text \<open>
  In the current implementation, equations are picked based on the default
  Net ordering. This should be improved in the future.
\<close>
ML_val \<open>
local
  fun eval eqns congs =
    FP_Eval.eval @{context} (FP_Eval.make_rules eqns congs);
  val input = (@{cterm "list_all (\<lambda>x::nat. x \<le> x) [100000, 314159, 2718281845]"}, Bound 0);
  val basic_eqns = @{thms list_all_Nil_iff list_all_Cons_iff rel_simps simp_thms};
  fun get_counter cs x = the (Symtab.lookup (Symtab.make cs) x);
in
  (* evaluate \<le> slowly *)
  val ((r1, _), counters1) = eval basic_eqns @{thms} input;
  (* shortcut for \<le> *)
  val ((r2, _), counters2) = eval (@{thms order.refl} @ basic_eqns) @{thms} input;
  val ((r3, _), counters3) = eval (basic_eqns @ @{thms order.refl}) @{thms} input;

  (* Bug: shortcut is never used -- no effect on runtime *)
  val _ = @{assert} (length (distinct op= [counters1, counters2, counters3]) = 1);

  (* desired outcome *)
  val ((r4, _), counters4) = eval @{thms list_all_Nil_iff list_all_Cons_iff simp_thms order.refl} @{thms} input;
  val _ = @{assert} (get_counter counters4 "rewrites" < get_counter counters1 "rewrites");
end
\<close>


subsection \<open>Miscellaneous and regression tests\<close>

text \<open>Test for partial arity and arg_conv\<close>
ML_val \<open>
local
  fun eval eqns congs =
    FP_Eval.eval @{context} (FP_Eval.make_rules eqns congs);
  val input = (@{cterm "(if 2 + 2 = 4 then Suc else id) x"}, FP_Eval.skel0);
  (* Need to build these manually, as @{cterm} itself does beta-eta normalisation *)
  val input_abs1 = (fold (fn x => fn f => Thm.apply f x)
                         [@{cterm "f::nat\<Rightarrow>nat"}, @{cterm "4::nat"}]
                         @{cterm "\<lambda>f. fun_upd (f::nat\<Rightarrow>nat) (2+2) y"},
                    FP_Eval.skel0);
  val input_abs2 = (fold (fn x => fn f => Thm.apply f x)
                         [@{cterm "f::nat\<Rightarrow>nat"}, @{cterm "4::nat"}]
                         @{cterm "\<lambda>f x z. z + fun_upd (f::nat\<Rightarrow>nat) (2+2) y x"},
                    FP_Eval.skel0);
  val Abs (_, _, Abs (_, _, Abs _)) $ _ $ _ = Thm.term_of (fst input_abs2); (* check *)
in
  (* Head (= If) is rewritten *)
  val ((result, Var _), _) = eval @{thms arith_simps refl if_True} @{thms} input;
  val _ = @{assert} (Thm.term_of (Thm.rhs_of result) = @{term "Suc x"});

  (* Head is not rewritten *)
  val ((result2, Var _ $ _), _) = eval @{thms arith_simps refl if_False} @{thms} input;
  val _ = @{assert} (Thm.term_of (Thm.rhs_of result2) = @{term "(if True then Suc else id) x"});

  (* Head is Abs *)
  val ((result3, Var _), _) = eval @{thms arith_simps refl fun_upd_apply if_True} @{thms} input_abs1;
  val _ = @{assert} (Thm.term_of (Thm.rhs_of result3) = @{term "y::nat"});

  (* Partially applied Abs *)
  val ((result4, Abs _), _) = eval @{thms arith_simps refl fun_upd_apply if_True} @{thms} input_abs2;
  val _ = @{assert} (Thm.term_of (Thm.rhs_of result4) = @{term "\<lambda>z. z + fun_upd (f::nat\<Rightarrow>nat) (2+2) y 4"});
end;
\<close>

text \<open>Check that skel_skip is not returned for intermediate Abs\<close>
ML_val \<open>
local
  fun eval eqns congs = FP_Eval.eval @{context} (FP_Eval.make_rules eqns congs);
  val input = (@{cterm "map (\<lambda>((x, y), z). ((id x, id y), id z)) [((a::'a, b::'b), c::'c)]"}, Bound 0);
in
  val ((result, Var _), counters) = eval @{thms list.map prod.case arith_simps} @{thms} input;
  val _ = @{assert} (Thm.term_of (Thm.rhs_of result) = @{term "[((id a::'a, id b::'b), id c::'c)]"});
end;
\<close>

text \<open>Test conversion of some basic non-equation rules to equations\<close>
ML_val \<open>
let val thms = @{thms simp_thms rel_simps arith_simps};
in @{assert} (length (map_filter FP_Eval.maybe_convert_eqn thms) = length thms) end
\<close>

end