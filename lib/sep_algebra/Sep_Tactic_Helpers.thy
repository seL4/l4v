(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Sep_Tactic_Helpers
imports Separation_Algebra
begin

lemmas sep_curry = sep_conj_sep_impl[rotated]

lemma sep_mp: "((Q \<longrightarrow>* R) \<and>* Q) s \<Longrightarrow> R s"
  by (rule sep_conj_sep_impl2)

lemma sep_mp_frame: "((Q \<longrightarrow>* R) \<and>* Q \<and>* R') s \<Longrightarrow> (R \<and>* R') s"
  apply (clarsimp simp: sep_conj_assoc[symmetric])
  apply (erule sep_conj_impl)
   apply (erule (1) sep_mp)
  done

lemma sep_empty_conj: "P s \<Longrightarrow> (\<box> \<and>* P) s"
  by clarsimp

lemma sep_conj_empty: "(\<box> \<and>* P)  s \<Longrightarrow> P s"
  by clarsimp

lemma sep_empty_imp: "(\<box> \<longrightarrow>* P) s \<Longrightarrow> P s"
  apply (clarsimp simp: sep_impl_def)
  apply (erule_tac x=0 in allE)
  apply (clarsimp)
  done

lemma sep_empty_imp': "(\<box> \<longrightarrow>* P) s \<Longrightarrow> (\<And>s. P s \<Longrightarrow> Q s) \<Longrightarrow> Q s"
  apply (clarsimp simp: sep_impl_def)
  apply (erule_tac x=0 in allE)
  apply (clarsimp)
  done

lemma sep_imp_empty: " P s \<Longrightarrow> (\<And>s. P s \<Longrightarrow> Q s) \<Longrightarrow> (\<box> \<longrightarrow>* Q) s"
  by (erule sep_conj_sep_impl, clarsimp)

end
