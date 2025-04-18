(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Authors: Gerwin Klein and Rafal Kolanski, 2012
   Maintainers: Gerwin Klein <kleing at cse.unsw.edu.au>
                Rafal Kolanski <rafal.kolanski at nicta.com.au>
*)

chapter "Abstract Separation Algebra"

theory Separation_Algebra
imports
  Arbitrary_Comm_Monoid
begin

text \<open>This theory is the main abstract separation algebra development\<close>


section \<open>Input syntax for lifting boolean predicates to separation predicates\<close>

abbreviation (input)
  pred_and :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "and" 35) where
  "a and b \<equiv> \<lambda>s. a s \<and> b s"

abbreviation (input)
  pred_or :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "or" 30) where
  "a or b \<equiv> \<lambda>s. a s \<or> b s"

abbreviation (input)
  pred_not :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("not _" [40] 40) where
  "not a \<equiv> \<lambda>s. \<not>a s"

abbreviation (input)
  pred_imp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "imp" 25) where
  "a imp b \<equiv> \<lambda>s. a s \<longrightarrow> b s"

abbreviation (input)
  pred_K :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" ("\<langle>_\<rangle>") where
  "\<langle>f\<rangle> \<equiv> \<lambda>s. f"

abbreviation (input)
  pred_ex :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (binder "EXS " 10) where
  "EXS x. P x \<equiv> \<lambda>s. \<exists>x. P x s"

abbreviation (input)
  pred_all :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (binder "ALLS " 10) where
  "ALLS x. P x \<equiv> \<lambda>s. \<forall>x. P x s"


section \<open>Associative/Commutative Monoid Basis of Separation Algebras\<close>

class pre_sep_algebra = zero + plus +
  fixes sep_disj :: "'a => 'a => bool" (infix "##" 60)

  assumes sep_disj_zero [simp]: "x ## 0"
  assumes sep_disj_commuteI: "x ## y \<Longrightarrow> y ## x"

  assumes sep_add_zero [simp]: "x + 0 = x"
  assumes sep_add_commute: "x ## y \<Longrightarrow> x + y = y + x"

  assumes sep_add_assoc:
    "\<lbrakk> x ## y; y ## z; x ## z \<rbrakk> \<Longrightarrow> (x + y) + z = x + (y + z)"
begin

lemma sep_disj_commute: "x ## y = y ## x"
  by (blast intro: sep_disj_commuteI)

lemma sep_add_left_commute:
  assumes a: "a ## b" "b ## c" "a ## c"
  shows "b + (a + c) = a + (b + c)" (is "?lhs = ?rhs")
proof -
  have "?lhs = b + a + c" using a
    by (simp add: sep_add_assoc[symmetric] sep_disj_commute)
  also have "... = a + b + c" using a
    by (simp add: sep_add_commute sep_disj_commute)
  also have "... = ?rhs" using a
    by (simp add: sep_add_assoc sep_disj_commute)
  finally show ?thesis .
qed

lemmas sep_add_ac = sep_add_assoc sep_add_commute sep_add_left_commute
                    sep_disj_commute (* nearly always necessary *)

end


section \<open>Separation Algebra as Defined by Calcagno et al.\<close>

class sep_algebra = pre_sep_algebra +
  assumes sep_disj_addD1: "\<lbrakk> x ## y + z; y ## z \<rbrakk> \<Longrightarrow> x ## y"
  assumes sep_disj_addI1: "\<lbrakk> x ## y + z; y ## z \<rbrakk> \<Longrightarrow> x + y ## z"
begin

subsection \<open>Basic Construct Definitions and Abbreviations\<close>

(* Lower precedence than pred_conj, otherwise "P \<and>* Q and R" is ambiguous,
 * (noting that Isabelle turns "(P \<and>* Q) and R" into "P \<and>* Q and R").
 *)
definition
  sep_conj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixr "**" 36)
  where
  "P ** Q \<equiv> \<lambda>h. \<exists>x y. x ## y \<and> h = x + y \<and> P x \<and> Q y"

notation
  sep_conj (infixr "\<and>*" 36)
notation (latex output)
  sep_conj (infixr "\<and>\<^sup>*" 36)

definition
  sep_empty :: "'a \<Rightarrow> bool" ("\<box>") where
  "\<box> \<equiv> \<lambda>h. h = 0"

definition
  sep_impl :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixr "\<longrightarrow>*" 25)
  where
  "P \<longrightarrow>* Q \<equiv> \<lambda>h. \<forall>h'. h ## h' \<and> P h' \<longrightarrow> Q (h + h')"

definition
  sep_substate :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 60) where
  "x \<preceq> y \<equiv> \<exists>z. x ## z \<and> x + z = y"

(* We want these to be abbreviations not definitions, because basic True and
   False will occur by simplification in sep_conj terms *)
abbreviation
  "sep_true \<equiv> \<langle>True\<rangle>"

abbreviation
  "sep_false \<equiv> \<langle>False\<rangle>"


subsection \<open>Disjunction/Addition Properties\<close>

lemma disjoint_zero_sym [simp]: "0 ## x"
  by (simp add: sep_disj_commute)

lemma sep_add_zero_sym [simp]: "0 + x = x"
  by (simp add: sep_add_commute)

lemma sep_disj_addD2: "\<lbrakk> x ## y + z; y ## z \<rbrakk> \<Longrightarrow> x ## z"
  by (metis sep_add_commute sep_disj_addD1 sep_disj_commuteI)

lemma sep_disj_addD: "\<lbrakk> x ## y + z; y ## z \<rbrakk> \<Longrightarrow> x ## y \<and> x ## z"
  by (metis sep_disj_addD1 sep_disj_addD2)

lemma sep_add_disjD: "\<lbrakk> x + y ## z; x ## y \<rbrakk> \<Longrightarrow> x ## z \<and> y ## z"
  by (metis sep_disj_addD sep_disj_commuteI)

lemma sep_disj_addI2:
  "\<lbrakk> x ## y + z; y ## z \<rbrakk> \<Longrightarrow> x + z ## y"
  using sep_add_commute sep_disj_addI1 sep_disj_commuteI by presburger

lemma sep_add_disjI1:
  "\<lbrakk> x + y ## z; x ## y \<rbrakk> \<Longrightarrow> x + z ## y"
  by (metis sep_add_commute sep_disj_addI1 sep_disj_commuteI sep_add_disjD)

lemma sep_add_disjI2:
  "\<lbrakk> x + y ## z; x ## y \<rbrakk> \<Longrightarrow> z + y ## x"
  by (metis sep_add_commute sep_disj_addI1 sep_disj_commuteI sep_add_disjD)

lemma sep_disj_addI3:
  "x + y ## z \<Longrightarrow> x ## y \<Longrightarrow> x ## y + z"
  by (metis sep_add_commute sep_disj_addI1 sep_disj_commuteI sep_add_disjD)

lemma sep_disj_add:
  "\<lbrakk> y ## z; x ## y \<rbrakk> \<Longrightarrow> x ## y + z = x + y ## z"
  by (metis sep_disj_addI1 sep_disj_addI3)


subsection \<open>Substate Properties\<close>

lemma sep_substate_disj_add:
  "x ## y \<Longrightarrow> x \<preceq> x + y"
  unfolding sep_substate_def by blast

lemma sep_substate_disj_add':
  "x ## y \<Longrightarrow> x \<preceq> y + x"
  by (simp add: sep_add_ac sep_substate_disj_add)


subsection \<open>Separating Conjunction Properties\<close>

lemma sep_conjD:
  "(P \<and>* Q) h \<Longrightarrow> \<exists>x y. x ## y \<and> h = x + y \<and> P x \<and> Q y"
  by (simp add: sep_conj_def)

lemma sep_conjE:
  "\<lbrakk> (P ** Q) h; \<And>x y. \<lbrakk> P x; Q y; x ## y; h = x + y \<rbrakk> \<Longrightarrow> X \<rbrakk> \<Longrightarrow> X"
  by (auto simp: sep_conj_def)

lemma sep_conjI:
  "\<lbrakk> P x; Q y; x ## y; h = x + y \<rbrakk> \<Longrightarrow> (P ** Q) h"
  by (auto simp: sep_conj_def)

lemma sep_conj_commuteI:
  "(P ** Q) h \<Longrightarrow> (Q ** P) h"
  by (auto intro!: sep_conjI elim!: sep_conjE simp: sep_add_ac)

lemma sep_conj_commute:
  "(P ** Q) = (Q ** P)"
  by (rule ext) (auto intro: sep_conj_commuteI)

lemma sep_conj_assoc:
  "((P ** Q) ** R) = (P ** Q ** R)" (is "?lhs = ?rhs")
proof (rule ext, rule iffI)
  fix h
  assume a: "?lhs h"
  then obtain x y z where "P x" and "Q y" and "R z"
                      and "x ## y" and "x ## z" and "y ## z" and "x + y ## z"
                      and "h = x + y + z"
    by (auto dest!: sep_conjD dest: sep_add_disjD)
  moreover
  then have "x ## y + z"
    by (simp add: sep_disj_add)
  ultimately
  show "?rhs h"
    by (auto simp: sep_add_ac intro!: sep_conjI)
next
  fix h
  assume a: "?rhs h"
  then obtain x y z where "P x" and "Q y" and "R z"
                      and "x ## y" and "x ## z" and "y ## z" and "x ## y + z"
                      and "h = x + y + z"
    by (fastforce elim!: sep_conjE simp: sep_add_ac dest: sep_disj_addD)
  thus "?lhs h"
    by (metis sep_conj_def sep_disj_addI1)
qed

lemma sep_conj_impl:
  "\<lbrakk> (P ** Q) h; \<And>h. P h \<Longrightarrow> P' h; \<And>h. Q h \<Longrightarrow> Q' h \<rbrakk> \<Longrightarrow> (P' ** Q') h"
  by (erule sep_conjE, auto intro!: sep_conjI)

lemma sep_conj_impl1:
  assumes P: "\<And>h. P h \<Longrightarrow> I h"
  shows "(P ** R) h \<Longrightarrow> (I ** R) h"
  by (auto intro: sep_conj_impl P)

lemma sep_globalise:
  "\<lbrakk> (P ** R) h; (\<And>h. P h \<Longrightarrow> Q h) \<rbrakk> \<Longrightarrow> (Q ** R) h"
  by (fast elim: sep_conj_impl)

lemma sep_conj_trivial_strip1:
  "Q = R \<Longrightarrow> (P ** Q) = (P ** R)" by simp

lemma sep_conj_trivial_strip2:
  "Q = R \<Longrightarrow> (Q ** P) = (R ** P)" by simp

lemma disjoint_subheaps_exist:
  "\<exists>x y. x ## y \<and> h = x + y"
  by (rule_tac x=0 in exI, auto)

lemma sep_conj_left_commute: (* for permutative rewriting *)
  "(P ** (Q ** R)) = (Q ** (P ** R))" (is "?x = ?y")
proof -
  have "?x = ((Q ** R) ** P)" by (simp add: sep_conj_commute)
  also have "\<dots> = (Q ** (R ** P))" by (subst sep_conj_assoc, simp)
  finally show ?thesis by (simp add: sep_conj_commute)
qed

lemmas sep_conj_ac = sep_conj_commute sep_conj_assoc sep_conj_left_commute

lemma sep_empty_zero [simp,intro!]: "\<box> 0"
  by (simp add: sep_empty_def)


subsection \<open>Properties of @{text sep_true} and @{text sep_false}\<close>

lemma sep_conj_sep_true:
  "P h \<Longrightarrow> (P ** sep_true) h"
  by (simp add: sep_conjI[where y=0])

lemma sep_conj_sep_true':
  "P h \<Longrightarrow> (sep_true ** P) h"
  by (simp add: sep_conjI[where x=0])

lemma sep_conj_true [simp]:
  "(sep_true ** sep_true) = sep_true"
  unfolding sep_conj_def
  by (auto intro: disjoint_subheaps_exist)

lemma sep_conj_false_right [simp]:
  "(P ** sep_false) = sep_false"
  by (force elim: sep_conjE)

lemma sep_conj_false_left [simp]:
  "(sep_false ** P) = sep_false"
  by (subst sep_conj_commute) (rule sep_conj_false_right)



subsection \<open>Properties of @{const sep_empty}\<close>

lemma sep_conj_empty [simp]:
  "(P ** \<box>) = P"
  by (simp add: sep_conj_def sep_empty_def)

lemma sep_conj_empty'[simp]:
  "(\<box> ** P) = P"
  by (subst sep_conj_commute, rule sep_conj_empty)

lemma sep_conj_sep_emptyI:
  "P h \<Longrightarrow> (P ** \<box>) h"
  by simp

lemma sep_conj_sep_emptyE:
  "\<lbrakk> P s; (P ** \<box>) s \<Longrightarrow> (Q ** R) s \<rbrakk> \<Longrightarrow> (Q ** R) s"
  by simp


subsection \<open>Properties of top (@{text sep_true})\<close>

lemma sep_conj_true_P [simp]:
  "(sep_true ** (sep_true ** P)) = (sep_true ** P)"
  by (simp add: sep_conj_assoc[symmetric])

lemma sep_conj_disj:
  "((P or Q) ** R) = ((P ** R) or (Q ** R))"
  by (rule ext, auto simp: sep_conj_def)

lemma sep_conj_sep_true_left:
  "(P ** Q) h \<Longrightarrow> (sep_true ** Q) h"
  by (erule sep_conj_impl, simp+)

lemma sep_conj_sep_true_right:
  "(P ** Q) h \<Longrightarrow> (P ** sep_true) h"
  by (subst (asm) sep_conj_commute, drule sep_conj_sep_true_left,
      simp add: sep_conj_ac)


subsection \<open>Separating Conjunction with Quantifiers\<close>

lemma sep_conj_conj:
  "((P and Q) ** R) h \<Longrightarrow> ((P ** R) and (Q ** R)) h"
  by (force intro: sep_conjI elim!: sep_conjE)

lemma sep_conj_exists1:
  "((EXS x. P x) ** Q) = (EXS x. (P x ** Q))"
  by (force intro: sep_conjI elim: sep_conjE)

lemma sep_conj_exists2:
  "(P ** (EXS x. Q x)) = (EXS x. P ** Q x)"
  by (force intro!: sep_conjI elim!: sep_conjE)

lemmas sep_conj_exists = sep_conj_exists1 sep_conj_exists2

lemma sep_conj_spec1:
  "((ALLS x. P x) ** Q) h \<Longrightarrow> (P x ** Q) h"
  by (force intro: sep_conjI elim: sep_conjE)

lemma sep_conj_spec2:
  "(P ** (ALLS x. Q x)) h \<Longrightarrow> (P ** Q x) h"
  by (force intro: sep_conjI elim: sep_conjE)

lemmas sep_conj_spec = sep_conj_spec1 sep_conj_spec2

subsection \<open>Properties of Separating Implication\<close>

lemma sep_implI:
  assumes a: "\<And>h'. \<lbrakk> h ## h'; P h' \<rbrakk> \<Longrightarrow> Q (h + h')"
  shows "(P \<longrightarrow>* Q) h"
  unfolding sep_impl_def by (auto elim: a)

lemma sep_implD:
  "(x \<longrightarrow>* y) h \<Longrightarrow> \<forall>h'. h ## h' \<and> x h' \<longrightarrow> y (h + h')"
  by (force simp: sep_impl_def)

lemma sep_implE:
  "(x \<longrightarrow>* y) h \<Longrightarrow> (\<forall>h'. h ## h' \<and> x h' \<longrightarrow> y (h + h') \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (auto dest: sep_implD)

lemma sep_impl_sep_true [simp]:
  "(P \<longrightarrow>* sep_true) = sep_true"
  by (force intro!: sep_implI)

lemma sep_impl_sep_false [simp]:
  "(sep_false \<longrightarrow>* P) = sep_true"
  by (force intro!: sep_implI)

lemma sep_impl_sep_true_P:
  "(sep_true \<longrightarrow>* P) h \<Longrightarrow> P h"
  by (clarsimp dest!: sep_implD elim!: allE[where x=0])

lemma sep_impl_sep_true_false [simp]:
  "(sep_true \<longrightarrow>* sep_false) = sep_false"
  by (force dest: sep_impl_sep_true_P)

lemma sep_conj_sep_impl:
  "\<lbrakk> P h; \<And>h. (P ** Q) h \<Longrightarrow> R h \<rbrakk> \<Longrightarrow> (Q \<longrightarrow>* R) h"
proof (rule sep_implI)
  fix h' h
  assume "P h" and "h ## h'" and "Q h'"
  hence "(P ** Q) (h + h')" by (force intro: sep_conjI)
  moreover assume "\<And>h. (P ** Q) h \<Longrightarrow> R h"
  ultimately show "R (h + h')" by simp
qed

lemma sep_conj_sep_impl2:
  "\<lbrakk> (P ** Q) h; \<And>h. P h \<Longrightarrow> (Q \<longrightarrow>* R) h \<rbrakk> \<Longrightarrow> R h"
  by (force dest: sep_implD elim: sep_conjE)

lemma sep_conj_sep_impl_sep_conj2:
  "(P ** R) h \<Longrightarrow> (P ** (Q \<longrightarrow>* (Q ** R))) h"
  by (erule (1) sep_conj_impl, erule sep_conj_sep_impl, simp add: sep_conj_ac)


subsection \<open>Pure assertions\<close>

definition
  pure :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "pure P \<equiv> \<forall>h h'. P h = P h'"

lemma pure_sep_true:
  "pure sep_true"
  by (simp add: pure_def)

lemma pure_sep_false:
  "pure sep_false"
  by (simp add: pure_def)

lemma pure_split:
  "pure P = (P = sep_true \<or> P = sep_false)"
  by (force simp: pure_def)

lemma pure_sep_conj:
  "\<lbrakk> pure P; pure Q \<rbrakk> \<Longrightarrow> pure (P \<and>* Q)"
  by (force simp: pure_split)

lemma pure_sep_impl:
  "\<lbrakk> pure P; pure Q \<rbrakk> \<Longrightarrow> pure (P \<longrightarrow>* Q)"
  by (force simp: pure_split)

lemma pure_conj_sep_conj:
  "\<lbrakk> (P and Q) h; pure P \<or> pure Q \<rbrakk> \<Longrightarrow> (P \<and>* Q) h"
  by (metis pure_def sep_add_zero sep_conjI sep_conj_commute sep_disj_zero)

lemma pure_sep_conj_conj:
  "\<lbrakk> (P \<and>* Q) h; pure P; pure Q \<rbrakk> \<Longrightarrow> (P and Q) h"
  by (force simp: pure_split)

lemma pure_conj_sep_conj_assoc:
  "pure P \<Longrightarrow> ((P and Q) \<and>* R) = (P and (Q \<and>* R))"
  by (auto simp: pure_split)

lemma pure_sep_impl_impl:
  "\<lbrakk> (P \<longrightarrow>* Q) h; pure P \<rbrakk> \<Longrightarrow> P h \<longrightarrow> Q h"
  by (force simp: pure_split dest: sep_impl_sep_true_P)

lemma pure_impl_sep_impl:
  "\<lbrakk> P h \<longrightarrow> Q h; pure P; pure Q \<rbrakk> \<Longrightarrow> (P \<longrightarrow>* Q) h"
  by (force simp: pure_split)

lemma pure_conj_right: "(Q \<and>* (\<langle>P'\<rangle> and Q')) = (\<langle>P'\<rangle> and (Q \<and>* Q'))"
  by (rule ext, rule, rule, clarsimp elim!: sep_conjE)
     (erule sep_conj_impl, auto)

lemma pure_conj_right': "(Q \<and>* (P' and \<langle>Q'\<rangle>)) = (\<langle>Q'\<rangle> and (Q \<and>* P'))"
  by (simp add: conj_comms pure_conj_right)

lemma pure_conj_left: "((\<langle>P'\<rangle> and Q') \<and>* Q) = (\<langle>P'\<rangle> and (Q' \<and>* Q))"
  by (simp add: pure_conj_right sep_conj_ac)

lemma pure_conj_left': "((P' and \<langle>Q'\<rangle>) \<and>* Q) = (\<langle>Q'\<rangle> and (P' \<and>* Q))"
  by (subst conj_comms, subst pure_conj_left, simp)

lemmas pure_conj = pure_conj_right pure_conj_right' pure_conj_left
    pure_conj_left'

declare pure_conj[simp add]


subsection \<open>Intuitionistic assertions\<close>

definition intuitionistic :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "intuitionistic P \<equiv> \<forall>h h'. P h \<and> h \<preceq> h' \<longrightarrow> P h'"

lemma intuitionisticI:
  "(\<And>h h'. \<lbrakk> P h; h \<preceq> h' \<rbrakk> \<Longrightarrow> P h') \<Longrightarrow> intuitionistic P"
  by (unfold intuitionistic_def, fast)

lemma intuitionisticD:
  "\<lbrakk> intuitionistic P; P h; h \<preceq> h' \<rbrakk> \<Longrightarrow> P h'"
  by (unfold intuitionistic_def, fast)

lemma pure_intuitionistic:
  "pure P \<Longrightarrow> intuitionistic P"
  by (clarsimp simp: intuitionistic_def pure_def, fast)

lemma intuitionistic_conj:
  "\<lbrakk> intuitionistic P; intuitionistic Q \<rbrakk> \<Longrightarrow> intuitionistic (P and Q)"
  by (force intro: intuitionisticI dest: intuitionisticD)

lemma intuitionistic_disj:
  "\<lbrakk> intuitionistic P; intuitionistic Q \<rbrakk> \<Longrightarrow> intuitionistic (P or Q)"
  by (force intro: intuitionisticI dest: intuitionisticD)

lemma intuitionistic_forall:
  "(\<And>x. intuitionistic (P x)) \<Longrightarrow> intuitionistic (ALLS x. P x)"
  by (force intro: intuitionisticI dest: intuitionisticD)

lemma intuitionistic_exists:
  "(\<And>x. intuitionistic (P x)) \<Longrightarrow> intuitionistic (EXS x. P x)"
  by (force intro: intuitionisticI dest: intuitionisticD)

lemma intuitionistic_sep_conj_sep_true:
  "intuitionistic (sep_true \<and>* P)"
proof (rule intuitionisticI)
  fix h h' r
  assume a: "(sep_true \<and>* P) h"
  then obtain x y where P: "P y" and h: "h = x + y" and xyd: "x ## y"
    by - (drule sep_conjD, clarsimp)
  moreover assume a2: "h \<preceq> h'"
  then obtain z where h': "h' = h + z" and hzd: "h ## z"
    by (clarsimp simp: sep_substate_def)

  moreover have "(P \<and>* sep_true) (y + (x + z))"
    using P h hzd xyd
    by (metis sep_add_disjI1 sep_disj_commute sep_conjI)
  ultimately show "(sep_true \<and>* P) h'" using hzd
    by (auto simp: sep_conj_commute sep_add_ac dest!: sep_disj_addD)
qed

lemma intuitionistic_sep_impl_sep_true:
  "intuitionistic (sep_true \<longrightarrow>* P)"
proof (rule intuitionisticI)
  fix h h'
  assume imp: "(sep_true \<longrightarrow>* P) h" and hh': "h \<preceq> h'"

  from hh' obtain z where h': "h' = h + z" and hzd: "h ## z"
    by (clarsimp simp: sep_substate_def)
  show "(sep_true \<longrightarrow>* P) h'" using imp h' hzd
    apply (clarsimp dest!: sep_implD)
    apply (metis sep_add_assoc sep_add_disjD sep_disj_addI3 sep_implI)
    done
qed

lemma intuitionistic_sep_conj:
  assumes ip: "intuitionistic (P::('a \<Rightarrow> bool))"
  shows "intuitionistic (P \<and>* Q)"
proof (rule intuitionisticI)
  fix h h'
  assume sc: "(P \<and>* Q) h" and hh': "h \<preceq> h'"

  from hh' obtain z where h': "h' = h + z" and hzd: "h ## z"
    by (clarsimp simp: sep_substate_def)

  from sc obtain x y where px: "P x" and qy: "Q y"
                       and h: "h = x + y" and xyd: "x ## y"
    by (clarsimp simp: sep_conj_def)

  have "x ## z" using hzd h xyd
    by (metis sep_add_disjD)

  with ip px have "P (x + z)"
    by (fastforce elim: intuitionisticD sep_substate_disj_add)

  thus "(P \<and>* Q) h'" using h' h hzd qy xyd
    by (metis (full_types) sep_add_commute sep_add_disjD sep_add_disjI2
              sep_add_left_commute sep_conjI)
qed

lemma intuitionistic_sep_impl:
  assumes iq: "intuitionistic Q"
  shows "intuitionistic (P \<longrightarrow>* Q)"
proof (rule intuitionisticI)
  fix h h'
  assume imp: "(P \<longrightarrow>* Q) h" and hh': "h \<preceq> h'"

  from hh' obtain z where h': "h' = h + z" and hzd: "h ## z"
    by (clarsimp simp: sep_substate_def)

  {
    fix x
    assume px: "P x" and hzx: "h + z ## x"

    have "h + x \<preceq> h + x + z" using hzx hzd
    by (metis sep_add_disjI1 sep_substate_def)

    with imp hzd iq px hzx
    have "Q (h + z + x)"
    by (metis intuitionisticD sep_add_assoc sep_add_ac sep_add_disjD sep_implE)
  }

  with imp h' hzd iq show "(P \<longrightarrow>* Q) h'"
    by (fastforce intro: sep_implI)
qed

lemma strongest_intuitionistic:
  "\<not>(\<exists>Q. (\<forall>h. (Q h \<longrightarrow> (P \<and>* sep_true) h)) \<and> intuitionistic Q \<and> Q \<noteq> (P \<and>* sep_true) \<and> (\<forall>h. P h \<longrightarrow> Q h))"
  by (fastforce intro!: ext sep_substate_disj_add dest!: sep_conjD intuitionisticD)

lemma weakest_intuitionistic:
  "\<not> (\<exists>Q. (\<forall>h. ((sep_true \<longrightarrow>* P) h \<longrightarrow> Q h)) \<and> intuitionistic Q \<and>
      Q \<noteq> (sep_true \<longrightarrow>* P) \<and> (\<forall>h. Q h \<longrightarrow> P h))"
  apply (clarsimp)
  apply (rule ext)
  apply (rule iffI)
   apply (rule sep_implI)
   apply (drule_tac h="x" and h'="x + h'" in intuitionisticD)
     apply (clarsimp simp: sep_add_ac sep_substate_disj_add)+
  done

lemma intuitionistic_sep_conj_sep_true_P:
  "\<lbrakk> (P \<and>* sep_true) s; intuitionistic P \<rbrakk> \<Longrightarrow> P s"
  by (force dest: intuitionisticD elim: sep_conjE sep_substate_disj_add)

lemma intuitionistic_sep_conj_sep_true_simp:
  "intuitionistic P \<Longrightarrow> (P \<and>* sep_true) = P"
  by (fast intro!: sep_conj_sep_true
           elim: intuitionistic_sep_conj_sep_true_P)

lemma intuitionistic_sep_impl_sep_true_P:
  "\<lbrakk> P h; intuitionistic P \<rbrakk> \<Longrightarrow> (sep_true \<longrightarrow>* P) h"
  by (force intro!: sep_implI dest: intuitionisticD
            intro: sep_substate_disj_add)

lemma intuitionistic_sep_impl_sep_true_simp:
  "intuitionistic P \<Longrightarrow> (sep_true \<longrightarrow>* P) = P"
  by (fast elim: sep_impl_sep_true_P intuitionistic_sep_impl_sep_true_P)


subsection \<open>Strictly exact assertions\<close>

definition strictly_exact :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "strictly_exact P \<equiv> \<forall>h h'. P h \<and> P h' \<longrightarrow> h = h'"

lemma strictly_exactD:
  "\<lbrakk> strictly_exact P; P h; P h' \<rbrakk> \<Longrightarrow> h = h'"
  by (unfold strictly_exact_def, fast)

lemma strictly_exactI:
  "(\<And>h h'. \<lbrakk> P h; P h' \<rbrakk> \<Longrightarrow> h = h') \<Longrightarrow> strictly_exact P"
  by (unfold strictly_exact_def, fast)

lemma strictly_exact_sep_conj:
  "\<lbrakk> strictly_exact P; strictly_exact Q \<rbrakk> \<Longrightarrow> strictly_exact (P \<and>* Q)"
  apply (rule strictly_exactI)
  apply (erule sep_conjE)+
  apply (drule_tac h="x" and h'="xa" in strictly_exactD, assumption+)
  apply (drule_tac h="y" and h'="ya" in strictly_exactD, assumption+)
  apply clarsimp
  done

lemma strictly_exact_conj_impl:
  "\<lbrakk> (Q \<and>* sep_true) h; P h; strictly_exact Q \<rbrakk> \<Longrightarrow> (Q \<and>* (Q \<longrightarrow>* P)) h"
  by (force intro: sep_conjI sep_implI dest: strictly_exactD elim!: sep_conjE
            simp: sep_add_commute sep_add_assoc)

end

section \<open>Separation Algebra with Stronger, but More Intuitive Disjunction Axiom\<close>

class stronger_sep_algebra = pre_sep_algebra +
  assumes sep_add_disj_eq [simp]: "y ## z \<Longrightarrow> x ## y + z = (x ## y \<and> x ## z)"
begin

lemma sep_disj_add_eq [simp]: "x ## y \<Longrightarrow> x + y ## z = (x ## z \<and> y ## z)"
  by (metis sep_add_disj_eq sep_disj_commute)

subclass sep_algebra by standard auto

end

interpretation sep: ab_semigroup_mult "(**)"
  by unfold_locales (simp add: sep_conj_ac)+

interpretation sep: comm_monoid "(**)" \<box>
  by unfold_locales simp

interpretation sep: comm_monoid_mult "(**)" \<box>
  by unfold_locales simp

section \<open>Folding separating conjunction over lists and sets of predicates\<close>

definition
  sep_list_conj :: "('a::sep_algebra \<Rightarrow> bool) list \<Rightarrow> ('a \<Rightarrow> bool)"  where
  "sep_list_conj Ps \<equiv> foldl ((**)) \<box> Ps"

abbreviation
  sep_map_list_conj :: "('b \<Rightarrow> 'a::sep_algebra \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> ('a \<Rightarrow> bool)"
where
  "sep_map_list_conj g S \<equiv> sep_list_conj (map g S)"

abbreviation
  sep_map_set_conj :: "('b \<Rightarrow> 'a::sep_algebra \<Rightarrow> bool) \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> bool)"
where
  "sep_map_set_conj g S \<equiv> sep.prod g S"

definition
  sep_set_conj :: "('a::sep_algebra \<Rightarrow> bool) set \<Rightarrow> ('a \<Rightarrow> bool)"  where
  "sep_set_conj S \<equiv> sep.prod id S"

(* Notation. *)
consts
  sep_conj_lifted :: "'b \<Rightarrow> ('a::sep_algebra \<Rightarrow> bool)" ("\<And>* _" [60] 90)
notation (latex output) sep_conj_lifted ("\<And>\<^sup>* _" [60] 90)
notation (latex output) sep_map_list_conj ("\<And>\<^sup>* _" [60] 90)

adhoc_overloading sep_conj_lifted \<rightleftharpoons> sep_list_conj
adhoc_overloading sep_conj_lifted \<rightleftharpoons> sep_set_conj


(* FIXME. Add notation for sep_map_list_conj, and consider unifying with sep_map_set_conj. *)


text\<open>Now: lots of fancy syntax. First, @{term "sep_map_set_conj (%x. g) A"} is written @{text"\<And>+x\<in>A. g"}.\<close>

(* Clagged from Big_Operators. *)
syntax
  "_sep_map_set_conj" :: "pttrn => 'a set => 'b => 'b::comm_monoid_add"    ("(3SETSEPCONJ _:_. _)" [0, 51, 10] 10)
syntax (xsymbols)
  "_sep_map_set_conj" :: "pttrn => 'a set => 'b => 'b::comm_monoid_add"    ("(3\<And>*_\<in>_. _)" [0, 51, 10] 10)
syntax (HTML output)
  "_sep_map_set_conj" :: "pttrn => 'a set => 'b => 'b::comm_monoid_add"    ("(3\<And>*_\<in>_. _)" [0, 51, 10] 10)
syntax (latex output)
  "_sep_map_set_conj" :: "pttrn => 'a set => 'b => 'b::comm_monoid_add"    ("(3\<And>\<^sup>*(00\<^bsub>_\<in>_\<^esub>) _)" [0, 51, 10] 10)

translations \<comment> \<open>Beware of argument permutation!\<close>
  "SETSEPCONJ x:A. g" == "CONST sep_map_set_conj (%x. g) A"
  "\<And>* x\<in>A. g" == "CONST sep_map_set_conj (%x. g) A"

text\<open>Instead of @{term"\<And>*x\<in>{x. P}. g"} we introduce the shorter @{text"\<And>+x|P. g"}.\<close>

syntax
  "_qsep_map_set_conj" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3SETSEPCONJ _ |/ _./ _)" [0,0,10] 10)
syntax (xsymbols)
  "_qsep_map_set_conj" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<And>*_ | (_)./ _)" [0,0,10] 10)
syntax (HTML output)
  "_qsep_map_set_conj" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<And>*_ | (_)./ _)" [0,0,10] 10)
syntax (latex output)
  "_qsep_map_set_conj" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<And>\<^sup>*(00\<^bsub>_ | (_)\<^esub>) /_)" [0,0,10] 10)

translations
  "SETSEPCONJ x|P. g" => "CONST sep_map_set_conj (%x. g) {x. P}"
  "\<And>*x|P. g" => "CONST sep_map_set_conj (%x. g) {x. P}"

print_translation \<open>
let
  fun setsepconj_tr' [Abs (x, Tx, t), Const (@{const_syntax Collect}, _) $ Abs (y, Ty, P)] =
        if x <> y then raise Match
        else
          let
            val x' = Syntax_Trans.mark_bound_body (x, Tx);
            val t' = subst_bound (x', t);
            val P' = subst_bound (x', P);
          in
            Syntax.const @{syntax_const "_qsep_map_set_conj"} $ Syntax_Trans.mark_bound_abs (x, Tx) $ P' $ t'
          end
    | setsepconj_tr' _ = raise Match;
in [(@{const_syntax sep_map_set_conj}, K setsepconj_tr')] end
\<close>


interpretation sep: folding "(\<and>*)" \<box>
  by unfold_locales (simp add: comp_def sep_conj_ac)

lemma "\<And>* [\<box>,P] = P"
  by (simp add: sep_list_conj_def)

lemma "\<And>* {\<box>} = \<box>"
  by (simp add: sep_set_conj_def)

lemma "\<And>* {P,\<box>} = P"
  by (cases "P = \<box>", auto simp: sep_set_conj_def)

lemma "(\<And>* x\<in>{0,1::nat}. if x=0 then \<box> else P) = P"
  by auto

lemma map_sep_list_conj_cong:
  "(\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow> \<And>* map f xs = \<And>* map g xs"
  by (metis map_cong)

lemma sep_list_conj_Nil [simp]: "\<And>* [] = \<box>"
  by (simp add: sep_list_conj_def)

(* apparently these two are rarely used and had to be removed from List.thy *)
lemma (in semigroup) foldl_assoc:
   "foldl f (f x y) zs = f x (foldl f y zs)"
   by (induct zs arbitrary: y) (simp_all add:assoc)

lemma (in monoid) foldl_absorb1:
  "f x (foldl f z zs) = foldl f x zs"
  by (induct zs) (simp_all add:foldl_assoc)


context comm_monoid
begin

lemma foldl_map_filter:
  "f (foldl f z (map P (filter t xs))) (foldl f z (map P (filter (not t) xs))) = foldl f z (map P xs)"
proof (induct xs)
  case Nil thus ?case by clarsimp
next
  case (Cons x xs)
  hence IH:
    "foldl f z (map P xs) =  f (foldl f z (map P (filter t xs))) (foldl f z (map P [x\<leftarrow>xs . \<not> t x]))"
    by (simp only: eq_commute)

  have foldl_Cons':
    "\<And>x xs. foldl f z (x # xs) = f x (foldl f z xs)"
    by (simp, subst foldl_absorb1[symmetric], rule refl)

  { assume "t x"
    hence ?case by (auto simp del: foldl_Cons simp add: foldl_Cons' IH ac_simps)
  } moreover {
    assume "\<not> t x"
    hence ?case by (auto simp del: foldl_Cons simp add: foldl_Cons' IH ac_simps)
  }
  ultimately show ?case by blast
qed

lemma foldl_map_add:
  "foldl f z (map (\<lambda>x. f (P x) (Q x)) xs) = f (foldl f z (map P xs)) (foldl f z (map Q xs))"
  apply (induct xs)
   apply clarsimp
  apply simp
  by (metis (full_types) commute foldl_absorb1 foldl_assoc)

lemma foldl_map_remove1:
  "x \<in> set xs \<Longrightarrow> foldl f z (map P xs) = f (P x) (foldl f z (map P (remove1 x xs)))"
  apply (induction xs, simp)
  apply clarsimp
  by (metis foldl_absorb1 left_commute)

end

lemma sep_list_conj_Cons [simp]: "\<And>* (x#xs) = (x ** \<And>* xs)"
  by (simp add: sep_list_conj_def sep.foldl_absorb1)

lemma sep_list_conj_append [simp]: "\<And>* (xs @ ys) = (\<And>* xs ** \<And>* ys)"
  by (simp add: sep_list_conj_def sep.foldl_absorb1)

lemma sep_list_conj_map_append:
  "\<And>* map f (xs @ ys) = (\<And>* map f xs \<and>* \<And>* map f ys)"
  by (metis map_append sep_list_conj_append)

lemma sep_list_con_map_filter:
  "(\<And>* map P (filter t xs) \<and>* \<And>* map P (filter (not t) xs))
   = \<And>* map P xs"
  apply (simp add: sep_list_conj_def)
  apply (rule sep.foldl_map_filter)
  done

lemma union_filter:
  "({x \<in> xs. P x} \<union> {x \<in> xs. \<not> P x}) = xs"
  by fast

lemma sep_map_set_conj_restrict:
  "finite xs \<Longrightarrow>
    sep_map_set_conj P xs =
   (sep_map_set_conj P {x \<in> xs. t x} \<and>*
    sep_map_set_conj P {x \<in> xs. \<not> t x})"
  by (subst sep.prod.union_disjoint [symmetric], (fastforce simp: union_filter)+)


lemma sep_list_conj_map_add:
  "\<And>* map (\<lambda>x. f x \<and>* g x) xs = (\<And>* map f xs \<and>* \<And>* map g xs)"
  apply (simp add: sep_list_conj_def)
  apply (rule sep.foldl_map_add)
  done


lemma filter_empty:
  "x \<notin> set xs \<Longrightarrow> filter ((=) x) xs = []"
  by (induct xs, clarsimp+)

lemma filter_singleton:
  "\<lbrakk>x \<in> set xs; distinct xs\<rbrakk> \<Longrightarrow> [x'\<leftarrow>xs . x = x'] = [x]"
  by (induct xs, auto simp: filter_empty)

lemma remove1_filter:
  "distinct xs \<Longrightarrow> remove1 x xs = filter (\<lambda>y. x \<noteq> y) xs"
  apply (induct xs)
   apply simp
  apply clarsimp
  apply (rule sym, rule filter_True)
  apply clarsimp
  done

lemma sep_list_conj_map_remove1:
  "x \<in> set xs \<Longrightarrow> \<And>* map P xs = (P x \<and>* \<And>* map P (remove1 x xs))"
  apply (simp add: sep_list_conj_def)
  apply (erule sep.foldl_map_remove1)
  done

lemma sep_map_take_Suc:
  "i < length xs \<Longrightarrow>
  \<And>* map P (take (Suc i) xs) = (\<And>* map P (take i xs) \<and>* P (xs ! i))"
  by (subst take_Suc_conv_app_nth, simp+)

lemma sep_conj_map_split:
  "(\<And>* map f xs \<and>* f a \<and>* \<And>* map f ys)
  = (\<And>* map f (xs @ a # ys))"
  by (metis list.map(2) map_append sep_list_conj_Cons sep_list_conj_append)


section "Separation predicates on sets"

lemma sep_map_set_conj_cong:
  "\<lbrakk>P = Q; xs = ys\<rbrakk> \<Longrightarrow> sep_map_set_conj P xs = sep_map_set_conj Q ys"
  by simp

lemma sep_set_conj_empty [simp]:
  "sep_set_conj {} = \<box>"
  by (simp add: sep_set_conj_def)


(* FIXME: We should be able to pull this from the "comm_monoid_big"
 * or "comm_monoid_add" locales, but I can't work out how... *)
lemma sep_map_set_conj_reindex_cong:
   "\<lbrakk>inj_on f A; B = f ` A; \<And>a. a \<in> A \<Longrightarrow> g a = h (f a)\<rbrakk>
    \<Longrightarrow> sep_map_set_conj h B = sep_map_set_conj g A"
  by (simp add: sep.prod.reindex)

lemma sep_list_conj_sep_map_set_conj:
  "distinct xs
  \<Longrightarrow> \<And>* (map P xs) = (\<And>* x \<in> set xs. P x)"
  by (induct xs, simp_all)

lemma sep_list_conj_sep_set_conj:
  "\<lbrakk>distinct xs; inj_on P (set xs)\<rbrakk>
  \<Longrightarrow> \<And>* (map P xs) = \<And>* (P ` set xs)"
  apply (subst sep_list_conj_sep_map_set_conj, assumption)
  apply (clarsimp simp: sep_set_conj_def sep.prod.reindex)
  done

lemma sep_map_set_conj_sep_list_conj:
  "finite A \<Longrightarrow>
   \<exists>xs. set xs = A \<and> distinct xs \<and> sep_map_set_conj P A = \<And>* map P xs"
  apply (frule finite_distinct_list)
  apply (erule exE)
  apply (rule_tac x=xs in exI)
  apply clarsimp
  apply (erule sep_list_conj_sep_map_set_conj [symmetric])
  done

lemma sep_list_conj_eq:
  "\<lbrakk>distinct xs; distinct ys; set xs = set ys\<rbrakk> \<Longrightarrow>
  \<And>* (map P xs) = \<And>* (map P ys)"
  apply (drule sep_list_conj_sep_map_set_conj [where P=P])
  apply (drule sep_list_conj_sep_map_set_conj [where P=P])
  apply simp
  done

lemma sep_list_conj_impl:
  "\<lbrakk> list_all2 (\<lambda>x y. \<forall>s. x s \<longrightarrow> y s) xs ys; (\<And>* xs) s \<rbrakk> \<Longrightarrow> (\<And>* ys) s"
  apply (induct arbitrary: s rule: list_all2_induct)
   apply simp
  apply simp
  apply (erule sep_conj_impl, simp_all)
  done

lemma sep_list_conj_exists:
  "(\<exists>x. (\<And>* map (\<lambda>y s. P x y s) ys) s) \<Longrightarrow> ((\<And>* map (\<lambda>y s. \<exists>x. P x y s) ys) s)"
  apply clarsimp
  apply (erule sep_list_conj_impl[rotated])
  apply (rule list_all2I, simp_all)
  by (fastforce simp: in_set_zip)

lemma sep_list_conj_map_impl:
  "\<lbrakk>\<And>s x. \<lbrakk>x \<in> set xs; P x s\<rbrakk> \<Longrightarrow> Q x s; (\<And>* map P xs) s\<rbrakk>
  \<Longrightarrow> (\<And>* map Q xs) s"
  apply (erule sep_list_conj_impl[rotated])
  apply (rule list_all2I, simp_all)
  by (fastforce simp: in_set_zip)

lemma sep_map_set_conj_impl:
  "\<lbrakk>sep_map_set_conj P A s; \<And>s x. \<lbrakk>x \<in> A; P x s\<rbrakk> \<Longrightarrow> Q x s; finite A\<rbrakk>
  \<Longrightarrow> sep_map_set_conj Q A s"
  apply (frule sep_map_set_conj_sep_list_conj [where P=P])
  apply (drule sep_map_set_conj_sep_list_conj [where P=Q])
  by (metis sep_list_conj_map_impl sep_list_conj_sep_map_set_conj)

lemma set_sub_sub:
  "\<lbrakk>zs \<subseteq> ys\<rbrakk> \<Longrightarrow> (xs - zs) - (ys - zs) = (xs - ys)"
  by blast

lemma sep_map_set_conj_sub_sub_disjoint:
  "\<lbrakk>finite xs; zs \<subseteq> ys; ys \<subseteq> xs\<rbrakk>
  \<Longrightarrow> sep_map_set_conj P (xs - zs) = (sep_map_set_conj P (xs - ys) \<and>* sep_map_set_conj P (ys - zs))"
  apply (cut_tac sep.prod.subset_diff [where A="xs-zs" and B="ys-zs" and g=P])
    apply (subst (asm) set_sub_sub, fast+)
  done

lemma foldl_use_filter_map:
  "foldl (\<and>*) Q (map (\<lambda>x. if T x then P x else \<box>) xs) =
   foldl (\<and>*) Q (map P (filter T xs))"
  by (induct xs arbitrary: Q, simp_all)

lemma sep_list_conj_filter_map:
  "\<And>* (map (\<lambda>x. if T x then P x else \<box>) xs) =
   \<And>* (map P (filter T xs))"
  by (clarsimp simp: sep_list_conj_def foldl_use_filter_map)

lemma sep_map_set_conj_restrict_predicate:
  "finite A \<Longrightarrow> (\<And>* x\<in>A. if T x then P x else \<box>) = (\<And>* x\<in>(Set.filter T A). P x)"
  by (simp add: Set.filter_def sep.prod.inter_filter)

lemma distinct_filters:
  "\<lbrakk>distinct xs; \<And>x. (f x \<and> g x) = False\<rbrakk> \<Longrightarrow>
  set [x\<leftarrow>xs . f x \<or> g x] = set [x\<leftarrow>xs . f x] \<union> set [x\<leftarrow>xs . g x]"
  by auto

lemma sep_list_conj_distinct_filters:
  "\<lbrakk>distinct xs; \<And>x. (f x \<and> g x) = False\<rbrakk> \<Longrightarrow>
  \<And>* map P [x\<leftarrow>xs . f x \<or> g x] = (\<And>* map P [x\<leftarrow>xs . f x] \<and>* \<And>* map P [x\<leftarrow>xs . g x])"
  apply (subst sep_list_conj_sep_map_set_conj, simp)+
  apply (subst distinct_filters, simp+)
  apply (subst sep.prod.union_disjoint, auto)
  done

lemma sep_map_set_conj_set_disjoint:
  "\<lbrakk>finite {x. P x}; finite {x. Q x}; \<And>x. (P x \<and> Q x) = False\<rbrakk>
 \<Longrightarrow> sep_map_set_conj g {x. P x \<or> Q x} =
  (sep_map_set_conj g {x. P x} \<and>* sep_map_set_conj g {x. Q x})"
  apply (subst sep.prod.union_disjoint [symmetric], simp+)
   apply blast
  apply simp
  by (metis Collect_disj_eq)


text \<open>
  Separation algebra with positivity
\<close>

class positive_sep_algebra = stronger_sep_algebra +
  assumes sep_disj_positive : "a ## a \<Longrightarrow> a + a = b \<Longrightarrow> a = b"



section \<open>Separation Algebra with a Cancellative Monoid\<close>

text \<open>
  Separation algebra with a cancellative monoid. The results of being a precise
  assertion (distributivity over separating conjunction) require this.
\<close>
class cancellative_sep_algebra = positive_sep_algebra +
  assumes sep_add_cancelD: "\<lbrakk> x + z = y + z ; x ## z ; y ## z \<rbrakk> \<Longrightarrow> x = y"
begin

definition
  (* In any heap, there exists at most one subheap for which P holds *)
  precise :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "precise P = (\<forall>h hp hp'. hp \<preceq> h \<and> P hp \<and> hp' \<preceq> h \<and> P hp' \<longrightarrow> hp = hp')"

lemma "precise ((=) s)"
  by (metis (full_types) precise_def)

lemma sep_add_cancel:
  "x ## z \<Longrightarrow> y ## z \<Longrightarrow> (x + z = y + z) = (x = y)"
  by (metis sep_add_cancelD)

lemma precise_distribute:
  "precise P = (\<forall>Q R. ((Q and R) \<and>* P) = ((Q \<and>* P) and (R \<and>* P)))"
proof (rule iffI)
  assume pp: "precise P"
  {
    fix Q R
    fix h hp hp' s

    { assume a: "((Q and R) \<and>* P) s"
      hence "((Q \<and>* P) and (R \<and>* P)) s"
        by (fastforce dest!: sep_conjD elim: sep_conjI)
    }
    moreover
    { assume qs: "(Q \<and>* P) s" and qr: "(R \<and>* P) s"

      from qs obtain x y where sxy: "s = x + y" and xy: "x ## y"
                           and x: "Q x" and y: "P y"
        by (fastforce dest!: sep_conjD)
      from qr obtain x' y' where sxy': "s = x' + y'" and xy': "x' ## y'"
                           and x': "R x'" and y': "P y'"
        by (fastforce dest!: sep_conjD)

      from sxy have ys: "y \<preceq> x + y" using xy
        by (fastforce simp: sep_substate_disj_add' sep_disj_commute)
      from sxy' have ys': "y' \<preceq> x' + y'" using xy'
        by (fastforce simp: sep_substate_disj_add' sep_disj_commute)

      from pp have yy: "y = y'" using sxy sxy' xy xy' y y' ys ys'
        by (fastforce simp: precise_def)

      hence "x = x'" using sxy sxy' xy xy'
        by (fastforce dest!: sep_add_cancelD)

      hence "((Q and R) \<and>* P) s" using sxy x x' yy y' xy'
        by (fastforce intro: sep_conjI)
    }
    ultimately
    have "((Q and R) \<and>* P) s = ((Q \<and>* P) and (R \<and>* P)) s" using pp by blast
  }
  thus "\<forall>Q R. ((Q and R) \<and>* P) = ((Q \<and>* P) and (R \<and>* P))" by blast

next
  assume a: "\<forall>Q R. ((Q and R) \<and>* P) = ((Q \<and>* P) and (R \<and>* P))"
  thus "precise P"
  proof (clarsimp simp: precise_def)
    fix h hp hp' Q R
    assume hp: "hp \<preceq> h" and hp': "hp' \<preceq> h" and php: "P hp" and php': "P hp'"

    obtain z where hhp: "h = hp + z" and hpz: "hp ## z" using hp
      by (clarsimp simp: sep_substate_def)
    obtain z' where hhp': "h = hp' + z'" and hpz': "hp' ## z'" using hp'
      by (clarsimp simp: sep_substate_def)

    have h_eq: "z' + hp' = z + hp" using hhp hhp' hpz hpz'
      by (fastforce simp: sep_add_ac)

    from hhp hhp' a hpz hpz' h_eq
    have "\<forall>Q R. ((Q and R) \<and>* P) (z + hp) = ((Q \<and>* P) and (R \<and>* P)) (z' + hp')"
      by (fastforce simp: h_eq sep_add_ac sep_conj_commute)

    hence "(((=) z and (=) z') \<and>* P) (z + hp) =
           (((=) z \<and>* P) and ((=) z' \<and>* P)) (z' + hp')" by blast

    thus  "hp = hp'" using php php' hpz hpz' h_eq
      by (fastforce dest!: iffD2 cong: conj_cong
                    simp: sep_add_ac sep_add_cancel sep_conj_def)
  qed
qed

lemma strictly_precise: "strictly_exact P \<Longrightarrow> precise P"
  by (metis precise_def strictly_exactD)

lemma sep_disj_positive_zero[simp]: "x ## y \<Longrightarrow> x + y = 0 \<Longrightarrow> x = 0 \<and> y = 0"
  by (metis (full_types) disjoint_zero_sym sep_add_cancelD sep_add_disjD
                         sep_add_zero_sym sep_disj_positive)

end

end