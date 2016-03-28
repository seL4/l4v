(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Author: Gerwin Klein, 2012
   Maintainers: Gerwin Klein <kleing at cse.unsw.edu.au>
                Rafal Kolanski <rafal.kolanski at nicta.com.au>
*)

chapter "Equivalence between Separation Algebra Formulations"

theory Sep_Eq
imports
  Separation_Algebra
  Separation_Algebra_Alt
begin

text {*
  In this theory we show that our total formulation of separation algebra is
  equivalent in strength to Calcagno et al's original partial one.

  This theory is not intended to be included in own developments.
*}

no_notation map_add (infixl "++" 100)
declare [[syntax_ambiguity_warning = false]]

section "Total implies Partial"

definition add2 :: "'a::sep_algebra => 'a => 'a option" where
  "add2 x y \<equiv> if x ## y then Some (x + y) else None"

lemma add2_zero: "add2 x 0 = Some x"
  by (simp add: add2_def)

lemma add2_comm: "add2 x y = add2 y x"
  by (auto simp: add2_def sep_add_commute sep_disj_commute)

lemma add2_assoc:
  "lift2 add2 a (lift2 add2 b c) = lift2 add2 (lift2 add2 a b) c"
  by (auto simp: add2_def lift2_def sep_add_assoc
              dest: sep_disj_addD sep_disj_addI3
                    sep_add_disjD sep_disj_addI2 sep_disj_commuteI
              split: option.splits)

interpretation total_partial: sep_algebra_alt 0 add2
  by (unfold_locales) (auto intro: add2_zero add2_comm add2_assoc)


section "Partial implies Total"

definition
  sep_add' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a :: sep_algebra_alt" where
  "sep_add' x y \<equiv> if disjoint x y then the (add x y) else undefined"

lemma sep_disj_zero':
  "disjoint x 0"
  by simp

lemma sep_disj_commuteI':
  "disjoint x y \<Longrightarrow> disjoint y x"
  by (clarsimp simp: disjoint_def add_comm)

lemma sep_add_zero':
  "sep_add' x 0 = x"
  by (simp add: sep_add'_def)

lemma sep_add_commute':
  "disjoint x y \<Longrightarrow> sep_add' x y = sep_add' y x"
  by (clarsimp simp: sep_add'_def disjoint_def add_comm)

lemma sep_add_assoc':
  "\<lbrakk> disjoint x y; disjoint y z; disjoint x z \<rbrakk> \<Longrightarrow>
  sep_add' (sep_add' x y) z = sep_add' x (sep_add' y z)"
  using add_assoc [of "Some x" "Some y" "Some z"]
  by (clarsimp simp: disjoint_def sep_add'_def lift2_def
               split: option.splits)

lemma sep_disj_addD1':
  "disjoint x (sep_add' y z) \<Longrightarrow> disjoint y z \<Longrightarrow> disjoint x y"
proof (clarsimp simp: disjoint_def sep_add'_def)
  fix a assume a: "y \<oplus> z = Some a"
  fix b assume b: "x \<oplus> a = Some b"
  with a have "Some x ++ (Some y ++ Some z) = Some b" by (simp add: lift2_def)
  hence "(Some x ++ Some y) ++ Some z = Some b" by (simp add: add_assoc)
  thus "\<exists>b. x \<oplus> y = Some b" by (simp add: lift2_def split: option.splits)
qed

lemma sep_disj_addI1':
  "disjoint x (sep_add' y z) \<Longrightarrow> disjoint y z \<Longrightarrow> disjoint (sep_add' x y) z"
  apply (clarsimp simp: disjoint_def sep_add'_def)
  apply (rule conjI)
   apply clarsimp
   apply (frule lift_to_add2, assumption)
   apply (simp add: add_assoc)
   apply (clarsimp simp: lift2_def add_comm)
  apply clarsimp
  apply (frule lift_to_add2, assumption)
  apply (simp add: add_assoc)
  apply (clarsimp simp: lift2_def)
  done

interpretation partial_total: sep_algebra sep_add' 0 disjoint
  apply (unfold_locales)
        apply (rule sep_disj_zero')
       apply (erule sep_disj_commuteI')
      apply (rule sep_add_zero')
     apply (erule sep_add_commute')
    apply (erule (2) sep_add_assoc')
   apply (erule (1) sep_disj_addD1')
  apply (erule (1) sep_disj_addI1')
  done

end
