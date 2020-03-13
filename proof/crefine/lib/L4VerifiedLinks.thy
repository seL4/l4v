(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Theorems linking the L4.verified proofs to our own framework;
 * typically showing that we prove equivalent results as a sanity
 * check.
 *)

theory L4VerifiedLinks
imports
  "AutoCorres.AutoCorres"
  "CLib.Corres_UL_C"
begin

(*
 * The ccorresE framework implies the ccorres framework.
 *)
lemma ccorresE_ccorres_underlying:
  "\<lbrakk> ccorresE st check_termination \<Gamma> G G' A B; \<not> exceptions_thrown B \<rbrakk> \<Longrightarrow>
  ccorres_underlying {(s', s). s' = st s} \<Gamma> dc (\<lambda>_. ()) dc (\<lambda>_. ()) G G' [] A B"
  apply (clarsimp simp: ccorres_underlying_def dc_def)
  apply (clarsimp simp: ccorresE_def)
  apply (erule allE, erule impE, force)
  apply (erule exec_handlers.cases, simp_all)
   apply clarsimp
   apply (frule exceptions_thrown_not_abrupt, simp_all)[1]
  apply (clarsimp split: xstate.splits)
  apply (erule allE, erule conjE, erule impE, assumption)
  apply (clarsimp simp: unif_rrel_def isAbr_def split: xstate.splits)
  apply (case_tac ta, simp_all)
  apply (rule bexI [rotated], assumption)
  apply simp
  done

(*
 * The ccorresE framework implies the ccorres framework.
 *)
lemma ccorresE_ccorres_underlying':
  "\<lbrakk> ccorresE st check_termination \<Gamma> G G' A B; no_throw G A \<rbrakk> \<Longrightarrow>
  ccorres_underlying {(s', s). s' = st s} \<Gamma> dc (\<lambda>_. ()) dc (\<lambda>_. ()) G G' [] A B"
  apply (clarsimp simp: ccorres_underlying_def dc_def)
  apply (clarsimp simp: ccorresE_def)
  apply (erule allE, erule impE, force)
  apply (erule exec_handlers.cases, simp_all)
   apply clarsimp
   apply (erule_tac allE, erule (1) impE)
   apply clarsimp
   apply (drule (1) no_throw_Inr)
    apply fastforce
   apply fastforce
  apply (clarsimp split: xstate.splits)
  apply (erule allE, erule conjE, erule impE, assumption)
  apply (clarsimp simp: unif_rrel_def isAbr_def split: xstate.splits)
  apply (case_tac ta, simp_all)
  apply (rule bexI [rotated], assumption)
  apply simp
  done

lemma ac_corres_ccorres_underlying:
  "ac_corres st check_termination \<Gamma> rx G A B \<Longrightarrow>
   ccorres_underlying {(a, b). a = st b} \<Gamma> ((\<lambda>_ _. False) \<oplus> (\<lambda>r s. r = rx s)) Inr ((\<lambda>_ _. False) \<oplus> (\<lambda>r s. r = rx s)) Inr (\<lambda>_. True) (Collect G) [] A B"
  apply (clarsimp simp: ac_corres_def ccorres_underlying_def)
  apply (erule allE, erule impE, force)
  apply clarsimp
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (erule allE, erule (1) impE)
    apply clarsimp
   apply (case_tac hs)
    apply clarsimp
    apply (erule allE, erule (1) impE)
    apply (clarsimp split: xstate.splits)
    apply (erule bexI [rotated])
    apply (clarsimp simp: unif_rrel_def)
   apply clarsimp
  apply clarsimp
  done

(*
 * The definition of corresXF and corres_underlying are equivalent,
 * assuming we don't use the extraction functions.
 *)
lemma corres_impl_corresXF:
  "corres_underlying {(a, b). a = st b} nf True (dc \<oplus> dc) \<top> P G G' \<Longrightarrow>
   corresXF st (\<lambda>_ _. ()) (\<lambda>_ _. ()) P G G'"
  apply (rule corresXF_I)
    apply (clarsimp simp: corres_underlying_def corresXF_def)
    apply (erule allE, erule (1) impE)
    apply force
   apply (clarsimp simp: corres_underlying_def corresXF_def)
   apply (erule allE, erule (1) impE)
   apply force
  apply (clarsimp simp: corres_underlying_def corresXF_def)
  done

lemma corresXF_impl_corres:
  "\<lbrakk> corresXF st (\<lambda>_ _. ()) (\<lambda>_ _. ()) P G G'; no_fail \<top> G \<rbrakk> \<Longrightarrow>
   corres_underlying {(a, b). a = st b} nf True (dc \<oplus> dc) \<top> P G G'"
  apply (clarsimp simp: corres_underlying_def corresXF_def no_fail_def)
  apply (erule allE, erule (1) impE)
  apply clarsimp
  apply (erule (1) my_BallE)
  apply (force split: sum.splits)
  done

end
