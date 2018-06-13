(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory CCorres_Rewrite
imports Corres_UL_C Simpl_Rewrite
begin

text \<open>A simple proof method for rewriting Simpl programs under @{term ccorres_underlying}.\<close>

locale ccorres_rewrite_locale =
  simpl_rewrite \<Gamma> "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H"
  for \<Gamma> sr r xf r' xf' P P' hs H

global_interpretation ccorres_rewrite: ccorres_rewrite_locale
  by unfold_locales (auto simp: simpl_rewrite_base.com_eq_def semantic_equiv_def ceqv_def
                          elim: ccorres_semantic_equivD2)

method ccorres_rewrite declares C_simp C_simp_pre C_simp_simps C_simp_throws
  = ccorres_rewrite.simpl_rewrite

abbreviation "com_eq \<Gamma> \<equiv> ccorres_rewrite.com_eq \<Gamma> True"
abbreviation "never_continues \<Gamma> \<equiv> ccorres_rewrite.never_continues \<Gamma> True"

lemmas com_eq_def = ccorres_rewrite.com_eq_def
lemmas never_continues_def = ccorres_rewrite.never_continues_def

text \<open>Some CRefine proofs remove Collect_const from the @{method simp} set,
      but we almost always want @{method ccorres_rewrite} to use it to simplify
      trivial @{text IF} and @{text WHILE} conditions.\<close>
declare Collect_const [C_simp_simps]

text \<open>Test that the @{command named_theorems} @{thm C_simp} still works in the
      @{term ccorres_rewrite_locale} interpretation.\<close>

lemma
  assumes c3: "com_eq \<Gamma> c3 c"
  assumes c: "com_eq \<Gamma> (c;;c) c"
  shows "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H
                            (c;; Guard f UNIV (IF X THEN c ELSE c FI);; Cond {} Skip (Skip;;c2);;
                             Skip;;
                             (IF False THEN Skip ELSE SKIP;; TRY THROW CATCH c3 END FI;; SKIP))"
  apply ccorres_rewrite
  apply (match conclusion in "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H (c;;c;;c2;;c3)" \<Rightarrow> \<open>-\<close>)
  apply (ccorres_rewrite C_simp: c3)
  apply (match conclusion in "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H (c;;c;;c2;;c)" \<Rightarrow> \<open>-\<close>)
  apply (ccorres_rewrite C_simp: c)
  apply (match conclusion in "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H (c;;c2;;c)" \<Rightarrow> \<open>-\<close>)
  apply (fails \<open>ccorres_rewrite\<close>)
  oops

end
