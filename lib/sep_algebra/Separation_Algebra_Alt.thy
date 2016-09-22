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

chapter "Abstract Separation Logic, Alternative Definition"

theory Separation_Algebra_Alt
imports "~~/src/HOL/Main"
begin

text {*
  This theory contains an alternative definition of speration algebra,
  following Calcagno et al very closely. While some of the abstract
  development is more algebraic, it is cumbersome to instantiate.
  We only use it to prove equivalence and to give an impression of how
  it would look like.
*}

(* The @{text "++"} notation is a horrible choice, but this theory is 
   only intended to show how the development would look like, not to 
   actually use it. We remove the notation for map-add so it doesn't
   conflict.
*)
no_notation map_add (infixl "++" 100)

definition
  lift2 :: "('a => 'b => 'c option) \<Rightarrow> 'a option => 'b option => 'c option"
where
  "lift2 f a b \<equiv> case (a,b) of (Some a, Some b) \<Rightarrow> f a b | _ \<Rightarrow> None"


class sep_algebra_alt = zero +
  fixes add :: "'a => 'a => 'a option" (infixr "\<oplus>" 65)

  assumes add_zero [simp]: "x \<oplus> 0 = Some x"
  assumes add_comm: "x \<oplus> y = y \<oplus> x"
  assumes add_assoc: "lift2 add a (lift2 add b c) = lift2 add (lift2 add a b) c"

begin

definition
  disjoint :: "'a => 'a => bool" (infix "##" 60)
where
  "a ## b \<equiv> a \<oplus> b \<noteq> None"

lemma disj_com: "x ## y = y ## x"
  by (auto simp: disjoint_def add_comm)

lemma disj_zero [simp]: "x ## 0"
  by (auto simp: disjoint_def)

lemma disj_zero2 [simp]: "0 ## x"
  by (subst disj_com) simp

lemma add_zero2 [simp]: "0 \<oplus> x = Some x"
  by (subst add_comm) auto

definition
  substate :: "'a => 'a => bool" (infix "\<preceq>" 60) where
  "a \<preceq> b \<equiv> \<exists>c. a \<oplus> c = Some b"

definition
  sep_conj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixl "**" 61)
  where
  "P ** Q \<equiv> \<lambda>s. \<exists>p q. p \<oplus> q = Some s \<and> P p \<and> Q q"

definition emp :: "'a \<Rightarrow> bool" ("\<box>") where
  "\<box> \<equiv> \<lambda>s. s = 0"

definition
  sep_impl :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixr "\<longrightarrow>\<^sup>*" 25)
  where
  "P \<longrightarrow>\<^sup>* Q \<equiv> \<lambda>h. \<forall>h' h''. h \<oplus> h' = Some h'' \<and> P h' \<longrightarrow> Q h''"

definition
  "sep_true \<equiv> \<lambda>s. True"

definition
  "sep_false \<equiv> \<lambda>s. False"


abbreviation
  add2 :: "'a option => 'a option => 'a option" (infixr "++" 65)
where
  "add2 == lift2 add"


lemma add2_comm:
  "a ++ b = b ++ a"
  by (simp add: lift2_def add_comm split: option.splits)

lemma add2_None [simp]:
  "x ++ None = None"
  by (simp add: lift2_def split: option.splits)

lemma None_add2 [simp]:
  "None ++ x = None"
  by (simp add: lift2_def split: option.splits)

lemma add2_Some_Some:
  "Some x ++ Some y = x \<oplus> y"
  by (simp add: lift2_def)

lemma add2_zero [simp]:
  "Some x ++ Some 0 = Some x"
  by (simp add: add2_Some_Some)

lemma zero_add2 [simp]:
  "Some 0 ++ Some x = Some x"
  by (simp add: add2_Some_Some)


lemma sep_conjE:
  "\<lbrakk> (P ** Q) s; \<And>p q. \<lbrakk> P p; Q q; p \<oplus> q = Some s \<rbrakk> \<Longrightarrow> X \<rbrakk> \<Longrightarrow> X"
  by (auto simp: sep_conj_def)

lemma sep_conjI:
  "\<lbrakk> P p; Q q; p \<oplus> q = Some s \<rbrakk> \<Longrightarrow> (P ** Q) s"
  by (auto simp: sep_conj_def)

lemma sep_conj_comI:
  "(P ** Q) s \<Longrightarrow> (Q ** P) s"
  by (auto intro!: sep_conjI elim!: sep_conjE simp: add_comm)

lemma sep_conj_com:
  "P ** Q = Q ** P"
  by (auto intro: sep_conj_comI)

lemma lift_to_add2:
  "\<lbrakk>z \<oplus> q = Some s; x \<oplus> y = Some q\<rbrakk> \<Longrightarrow> Some z ++ Some x ++ Some y = Some s"
  by (simp add: add2_Some_Some)

lemma lift_to_add2':
  "\<lbrakk>q \<oplus> z = Some s; x \<oplus> y = Some q\<rbrakk> \<Longrightarrow> (Some x ++ Some y) ++ Some z = Some s"
  by (simp add: add2_Some_Some)

lemma add2_Some:
  "(x ++ Some y = Some z) = (\<exists>x'. x = Some x' \<and> x' \<oplus> y = Some z)"
  by (simp add: lift2_def split: option.splits)

lemma Some_add2:
  "(Some x ++ y = Some z) = (\<exists>y'. y = Some y' \<and> x \<oplus> y' = Some z)"
  by (simp add: lift2_def split: option.splits)

lemma sep_conj_assoc:
  "P ** (Q ** R) = (P ** Q) ** R"
  unfolding sep_conj_def
  apply (rule ext)
  apply (rule iffI)
   apply clarsimp
   apply (drule (1) lift_to_add2)
   apply (subst (asm) add_assoc)
   apply (fastforce simp: add2_Some_Some add2_Some)
  apply clarsimp
  apply (drule (1) lift_to_add2')
  apply (subst (asm) add_assoc [symmetric])
  apply (fastforce simp: add2_Some_Some Some_add2)
  done

lemma sep_true[simp]: "sep_true s" by (simp add: sep_true_def)
lemma sep_false[simp]: "\<not>sep_false x" by (simp add: sep_false_def)

lemma sep_conj_sep_true:
  "P s \<Longrightarrow> (P ** sep_true) s"
  by (auto simp: sep_conjI [where q=0])

lemma sep_conj_sep_true':
  "P s \<Longrightarrow> (sep_true ** P) s"
  by (auto simp: sep_conjI [where p=0])

lemma disjoint_submaps_exist:
  "\<exists>h\<^sub>0 h\<^sub>1. h\<^sub>0 \<oplus> h\<^sub>1 = Some h"
  by (rule_tac x=0 in exI, auto)

lemma sep_conj_true[simp]:
  "(sep_true ** sep_true) = sep_true"
  unfolding sep_conj_def
  by (auto intro: disjoint_submaps_exist)

lemma sep_conj_false_right[simp]:
  "(P ** sep_false) = sep_false"
  by (force elim: sep_conjE)

lemma sep_conj_false_left[simp]:
  "(sep_false ** P) = sep_false"
  by (subst sep_conj_com) (rule sep_conj_false_right)

lemma sep_conj_left_com:
  "(P ** (Q ** R)) = (Q ** (P ** R))" (is "?x = ?y")
proof -
  have "?x = ((Q ** R) ** P)" by (simp add: sep_conj_com)
  also have "\<dots> = (Q ** (R ** P))" by (subst sep_conj_assoc, simp)
  finally show ?thesis by (simp add: sep_conj_com)
qed

lemmas sep_conj_ac = sep_conj_com sep_conj_assoc sep_conj_left_com

lemma empty_empty[simp]: "\<box> 0"
  by (simp add: emp_def)

lemma sep_conj_empty[simp]:
  "(P ** \<box>) = P"
  by (simp add: sep_conj_def emp_def)

  lemma sep_conj_empty'[simp]:
  "(\<box> ** P) = P"
  by (subst sep_conj_com, rule sep_conj_empty)

lemma sep_conj_sep_emptyI:
  "P s \<Longrightarrow> (P ** \<box>) s"
  by simp

lemma sep_conj_true_P[simp]:
  "(sep_true ** (sep_true ** P)) = (sep_true ** P)"
  by (simp add: sep_conj_assoc)

lemma sep_conj_disj:
  "((\<lambda>s. P s \<or> Q s) ** R) s = ((P ** R) s \<or> (Q ** R) s)" (is "?x = (?y \<or> ?z)")
  by (auto simp: sep_conj_def)

lemma sep_conj_conj:
  "((\<lambda>s. P s \<and> Q s) ** R) s \<Longrightarrow> (P ** R) s \<and> (Q ** R) s"
  by (force intro: sep_conjI elim!: sep_conjE)

lemma sep_conj_exists1:
  "((\<lambda>s. \<exists>x. P x s) ** Q) s = (\<exists>x. (P x ** Q) s)"
  by (force intro: sep_conjI elim: sep_conjE)

lemma sep_conj_exists2:
  "(P ** (\<lambda>s. \<exists>x. Q x s)) = (\<lambda>s. (\<exists>x. (P ** Q x) s))"
  by (force intro!: sep_conjI elim!: sep_conjE)

lemmas sep_conj_exists = sep_conj_exists1 sep_conj_exists2

lemma sep_conj_forall:
  "((\<lambda>s. \<forall>x. P x s) ** Q) s \<Longrightarrow> (P x ** Q) s"
  by (force intro: sep_conjI elim: sep_conjE)

lemma sep_conj_impl:
  "\<lbrakk> (P ** Q) s; \<And>s. P s \<Longrightarrow> P' s; \<And>s. Q s \<Longrightarrow> Q' s \<rbrakk> \<Longrightarrow> (P' ** Q') s"
  by (erule sep_conjE, auto intro!: sep_conjI)

lemma sep_conj_impl1:
  assumes P: "\<And>s. P s \<Longrightarrow> I s"
  shows "(P ** R) s \<Longrightarrow> (I ** R) s"
  by (auto intro: sep_conj_impl P)

lemma sep_conj_sep_true_left:
  "(P ** Q) s \<Longrightarrow> (sep_true ** Q) s"
  by (erule sep_conj_impl, simp+)

lemma sep_conj_sep_true_right:
  "(P ** Q) s \<Longrightarrow> (P ** sep_true) s"
  by (subst (asm) sep_conj_com, drule sep_conj_sep_true_left,
      simp add: sep_conj_ac)

lemma sep_globalise:
  "\<lbrakk> (P ** R) s; (\<And>s. P s \<Longrightarrow> Q s) \<rbrakk> \<Longrightarrow> (Q ** R) s"
  by (fast elim: sep_conj_impl)

lemma sep_implI:
  assumes a: "\<And>h' h''. \<lbrakk> h \<oplus> h' = Some h''; P h' \<rbrakk> \<Longrightarrow> Q h''"
  shows "(P \<longrightarrow>\<^sup>* Q) h"
  unfolding sep_impl_def by (auto elim: a)

lemma sep_implD:
  "(x \<longrightarrow>\<^sup>* y) h \<Longrightarrow> \<forall>h' h''. h \<oplus> h' = Some h'' \<and> x h' \<longrightarrow> y h''"
  by (force simp: sep_impl_def)

lemma sep_impl_sep_true[simp]:
  "(P \<longrightarrow>\<^sup>* sep_true) = sep_true"
  by (force intro!: sep_implI)

lemma sep_impl_sep_false[simp]:
  "(sep_false \<longrightarrow>\<^sup>* P) = sep_true"
  by (force intro!: sep_implI)

lemma sep_impl_sep_true_P:
  "(sep_true \<longrightarrow>\<^sup>* P) s \<Longrightarrow> P s"
  apply (drule sep_implD)
  apply (erule_tac x=0 in allE)
  apply simp
  done

lemma sep_impl_sep_true_false[simp]:
  "(sep_true \<longrightarrow>\<^sup>* sep_false) = sep_false"
  by (force dest: sep_impl_sep_true_P)

lemma sep_conj_sep_impl:
  "\<lbrakk> P s; \<And>s. (P ** Q) s \<Longrightarrow> R s \<rbrakk> \<Longrightarrow> (Q \<longrightarrow>\<^sup>* R) s"
proof (rule sep_implI)
  fix h' h h''
  assume "P h" and "h \<oplus> h' = Some h''" and "Q h'"
  hence "(P ** Q) h''" by (force intro: sep_conjI)
  moreover assume "\<And>s. (P ** Q) s \<Longrightarrow> R s"
  ultimately show "R h''" by simp
qed

lemma sep_conj_sep_impl2:
  "\<lbrakk> (P ** Q) s; \<And>s. P s \<Longrightarrow> (Q \<longrightarrow>\<^sup>* R) s \<rbrakk> \<Longrightarrow> R s"
  by (force dest: sep_implD elim: sep_conjE)

lemma sep_conj_sep_impl_sep_conj2:
  "(P ** R) s \<Longrightarrow> (P ** (Q \<longrightarrow>\<^sup>* (Q ** R))) s"
  by (erule (1) sep_conj_impl, erule sep_conj_sep_impl, simp add: sep_conj_ac)

lemma sep_conj_triv_strip2:
  "Q = R \<Longrightarrow> (Q ** P) = (R ** P)" by simp

end

end
