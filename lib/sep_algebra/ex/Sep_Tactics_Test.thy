(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Authors: Gerwin Klein and Rafal Kolanski, 2012
   Maintainers: Gerwin Klein <kleing at cse.unsw.edu.au>
                Rafal Kolanski <rafal.kolanski at nicta.com.au>
*)

theory Sep_Tactics_Test
imports "../Sep_Tactics"
begin

text {* Substitution and forward/backward reasoning *}

typedecl p
typedecl val
typedecl heap

axiomatization where
  heap_algebra: "OFCLASS(heap, sep_algebra_class)"

instantiation heap :: sep_algebra
begin
  instance by (rule heap_algebra)
end

axiomatization
  points_to :: "p \<Rightarrow> val \<Rightarrow> heap \<Rightarrow> bool" and
  val :: "heap \<Rightarrow> p \<Rightarrow> val"
where
  points_to: "(points_to p v ** P) h \<Longrightarrow> val h p = v"

consts
  update :: "p \<Rightarrow> val \<Rightarrow> heap \<Rightarrow> heap"

(* FIXME: revive
lemma
  "\<lbrakk> Q2 (val h p); (K ** T ** blub ** P ** points_to p v ** P ** J) h \<rbrakk>
   \<Longrightarrow> Q (val h p) (val h p)"
  apply (sep_subst (2) points_to)
  apply (sep_subst (asm) points_to)
  apply (sep_subst points_to)
  oops
*)

lemma
  "\<lbrakk> Q2 (val h p); (K ** T ** blub ** P ** points_to p v ** P ** J) h \<rbrakk>
   \<Longrightarrow> Q (val h p) (val h p)"
  apply (sep_drule (direct) points_to)
  apply simp
  oops

lemma
  "\<lbrakk> Q2 (val h p); (K ** T ** blub ** P ** points_to p v ** P ** J) h \<rbrakk>
   \<Longrightarrow> Q (val h p) (val h p)"
  apply (sep_frule (direct) points_to)
  apply simp
  oops

schematic_goal
  assumes a: "\<And>P. (stuff p ** P) H \<Longrightarrow> (other_stuff p v ** P) (update p v H)"
  shows "(X ** Y ** other_stuff p ?v) (update p v H)"
  apply (sep_rule (direct) a)
  oops



text {* Conjunct selection *}

lemma "(A ** B ** Q ** P) s"
  apply (sep_select 1)
  apply (sep_select 3)
  apply (sep_select 4)
  oops

lemma "\<lbrakk> also unrelated; (A ** B ** Q ** P) s \<rbrakk> \<Longrightarrow> unrelated"
  apply (sep_select_asm 2)
  oops


section {* Test cases for @{text sep_cancel}. *}

lemma
  assumes forward: "\<And>s g p v. A g p v s \<Longrightarrow> AA g p s "
  shows "\<And>yv P y x s. (A g x yv ** A g y yv ** P) s \<Longrightarrow> (AA g y ** sep_true) s"
  by (sep_solve add: forward)

lemma
  assumes forward: "\<And>s. generic s \<Longrightarrow> instance s"
  shows "(A ** generic ** B) s \<Longrightarrow> (instance ** sep_true) s"
  by (sep_solve add: forward)

lemma "\<lbrakk> (A ** B) sa ; (A ** Y) s \<rbrakk> \<Longrightarrow> (A ** X) s"
  apply (sep_cancel)
  oops

lemma "\<lbrakk> (A ** B) sa ; (A ** Y) s \<rbrakk> \<Longrightarrow> (\<lambda>s. (A ** X) s) s"
  apply (sep_cancel)
  oops

schematic_goal "\<lbrakk> (B ** A ** C) s \<rbrakk> \<Longrightarrow> (\<lambda>s. (A ** ?X) s) s"
  by (sep_cancel)

(* test backtracking on premises with same state *)
lemma
  assumes forward: "\<And>s. generic s \<Longrightarrow> instance s"
  shows "\<lbrakk> (A ** B) s ; (generic ** Y) s \<rbrakk> \<Longrightarrow> (X ** instance) s"
  apply (sep_cancel add: forward)
  oops

lemma f1:
  assumes forward: "\<And>s. generic s \<Longrightarrow> instance s"
  shows "generic s \<Longrightarrow> instance s"
  by (sep_cancel add: forward)

declare sep_conj_true[sep_cancel]

lemma boxo: "P s \<Longrightarrow> (P \<and>* \<box>) s"
  by (erule sep_conj_sep_emptyI)

lemma f2:
  assumes forward: "\<And>s. generic s \<Longrightarrow> instance s"
  assumes forward2: "\<And>s. instance s \<Longrightarrow> instance2 s"
  shows "generic s \<Longrightarrow> (instance2 ** \<box>) s"
  apply (drule forward forward2)+
  apply (sep_erule_concl (direct) boxo)
  done

end
