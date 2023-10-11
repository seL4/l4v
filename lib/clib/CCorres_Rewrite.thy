(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory CCorres_Rewrite
imports Corres_UL_C Simpl_Rewrite
begin

text \<open>Simple proof methods for rewriting Simpl programs under @{term ccorres_underlying}
      and @{term hoarep}.\<close>

lemma ccorres_com_eq_hom:
  "com_eq_hom \<Gamma> (ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H)"
  by (auto simp: com_eq_hom_def com_eq_def semantic_equiv_def ceqv_def
           elim: ccorres_semantic_equivD2)

method ccorres_rewrite declares C_simp C_simp_pre C_simp_simps C_simp_throws
  = (simpl_rewrite hom: ccorres_com_eq_hom, no_name_eta)

lemma hoarep_com_eq_hom:
  "com_eq_hom \<Gamma> (\<lambda>c. hoarep \<Gamma> {} F P c Q A)"
  by (auto simp: com_eq_hom_def com_eq_def ceqv_def
           elim: exec_eq_is_valid_eq0[rotated])

lemma hoarep_spec_com_eq_hom:
  "com_eq_hom \<Gamma> (\<lambda>c. \<forall>s. hoarep \<Gamma> {} (F s) (P s) c (Q s) (A s))"
  by (fastforce simp: com_eq_hom_def com_eq_def ceqv_def
                elim: exec_eq_is_valid_eq0[rotated])

method hoarep_rewrite declares C_simp C_simp_pre C_simp_simps C_simp_throws
  = (match conclusion in \<open>hoarep \<Gamma> {} F P c Q A\<close> for \<Gamma> F P c Q A
                           \<Rightarrow> \<open>simpl_rewrite hom: hoarep_com_eq_hom\<close>
                       \<bar> \<open>\<forall>s. hoarep \<Gamma> {} (F s) (P s) c (Q s) (A s)\<close> for \<Gamma> F P c Q A
                           \<Rightarrow> \<open>simpl_rewrite hom: hoarep_spec_com_eq_hom\<close>)

text \<open>Some CRefine proofs remove Collect_const from the @{method simp} set,
      but we almost always want @{method ccorres_rewrite} to use it to simplify
      trivial @{text IF} and @{text WHILE} conditions.\<close>
declare Collect_const [C_simp_simps]

text \<open>Test\<close>

lemma
  assumes c3: "com_equiv \<Gamma> c3 c"
  assumes c: "com_equiv \<Gamma> (c;;c) c"
  shows "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H
                            (c;; Guard f UNIV (IF X THEN c ELSE c FI);; Cond {} Skip (Skip;;c2);;
                             Skip;;
                             (IF False THEN Skip ELSE SKIP;; TRY THROW CATCH c3 END FI;; SKIP))"
  supply Collect_const[simp del]
  apply ccorres_rewrite
  apply (match conclusion in "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H (c;;c;;c2;;c3)" \<Rightarrow> \<open>-\<close>)
  apply (ccorres_rewrite C_simp: c3)
  apply (match conclusion in "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H (c;;c;;c2;;c)" \<Rightarrow> \<open>-\<close>)
  apply (ccorres_rewrite C_simp: c)
  apply (match conclusion in "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H (c;;c2;;c)" \<Rightarrow> \<open>-\<close>)
  apply (fails \<open>ccorres_rewrite\<close>)
  oops

end
