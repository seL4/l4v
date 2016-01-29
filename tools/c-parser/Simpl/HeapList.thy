(*  Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      HeapList.thy
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2004-2008 Norbert Schirmer 
Some rights reserved, TU Muenchen

This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

section {* Paths and Lists in the Heap *}
theory HeapList
imports Simpl_Heap
begin

text {* Adapted from 'HOL/Hoare/Heap.thy'. *}


subsection "Paths in The Heap"

primrec
 Path :: "ref \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> ref \<Rightarrow>  ref list  \<Rightarrow> bool"
where
"Path x h y [] = (x = y)" |
"Path x h y (p#ps) = (x = p \<and> x \<noteq> Null \<and> Path (h x) h y ps)"

lemma Path_Null_iff [iff]: "Path Null h y xs  = (xs = [] \<and> y = Null)"
apply(case_tac xs)
apply fastforce
apply fastforce
done

lemma Path_not_Null_iff [simp]: "p\<noteq>Null \<Longrightarrow> 
  Path p h q as = (as = [] \<and> q = p  \<or>  (\<exists>ps. as = p#ps \<and> Path (h p) h q ps ))"
apply(case_tac as)
apply fastforce
apply fastforce
done

lemma Path_append [simp]: 
  "\<And>p. Path p f q (as@bs)  = (\<exists>y. Path p f y as \<and> Path y f q bs)"
by(induct as, simp+)

lemma notin_Path_update[simp]:
 "\<And>p. u \<notin> set ps \<Longrightarrow> Path p (f(u := v)) q ps  = Path p f q ps "
by(induct ps, simp, simp add:eq_sym_conv)

lemma Path_upd_same [simp]: 
  "Path p (f(p:=p)) q qs = 
      ((p=Null \<and> q=Null \<and> qs = []) \<or> (p\<noteq>Null \<and> q=p \<and> (\<forall>x\<in>set qs. x=p)))"
by (induct qs) auto

text {* @{thm[source] Path_upd_same} prevents 
@{term "p\<noteq>Null \<Longrightarrow> Path p (f(p:=p)) q qs = X"} from looping, because of 
@{thm[source] Path_not_Null_iff} and @{thm[source]fun_upd_apply}.
 *}

lemma notin_Path_updateI [intro]:
 "\<lbrakk>Path p h q ps ; r \<notin> set ps\<rbrakk> \<Longrightarrow> Path p (h(r := y)) q ps "
by simp

lemma Path_update_new [simp]: "\<lbrakk>set ps \<subseteq> set alloc\<rbrakk>
     \<Longrightarrow> Path p (f(new (set alloc) := x)) q ps  = Path p f q ps "
  by (rule notin_Path_update) fastforce

lemma Null_notin_Path [simp,intro]:
"\<And>p. Path p f q ps \<Longrightarrow> Null \<notin> set ps"
by(induct ps) auto

lemma Path_snoc:
 "\<lbrakk>Path p (f(a := q)) a as ; a\<noteq>Null\<rbrakk> \<Longrightarrow> Path p (f(a := q)) q (as @ [a])"
by simp

subsection "Lists on The Heap"

subsubsection "Relational Abstraction"

definition
 List :: "ref \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> ref list \<Rightarrow> bool" where
"List p h ps = Path p h Null ps "

lemma List_empty [simp]: "List p h [] = (p = Null)"
by(simp add:List_def)

lemma List_cons [simp]: "List p h (a#ps) = (p = a \<and> p\<noteq>Null \<and> List (h p) h ps)"
by(simp add:List_def)

lemma List_Null [simp]: "List Null h ps = (ps = [])"
by(case_tac ps, simp_all)

lemma List_not_Null [simp]: "p\<noteq>Null \<Longrightarrow>
  List p h as = (\<exists>ps. as = p#ps \<and> List (h p) h ps)"
by(case_tac as, simp_all, fast)


lemma Null_notin_List [simp,intro]: "\<And>p. List p h ps \<Longrightarrow> Null \<notin> set ps"
by (simp add : List_def)


theorem notin_List_update[simp]:
 "\<And>p. q \<notin> set ps \<Longrightarrow> List p (h(q := y)) ps = List p h ps"
apply(induct ps)
apply simp
apply clarsimp
done

lemma List_upd_same_lemma: "\<And>p.  p \<noteq> Null \<Longrightarrow> \<not> List p (h(p := p)) ps"
apply (induct ps)
apply  simp
apply (simp (no_asm_simp) del: fun_upd_apply)
apply (simp (no_asm_simp) only: fun_upd_apply refl if_True)
apply blast
done

lemma List_upd_same [simp]: "List p (h(p:=p)) ps = (p = Null \<and> ps = [])"
apply (cases "p=Null")
apply  simp
apply (fast dest: List_upd_same_lemma)
done

text {* @{thm[source] List_upd_same} prevents 
@{term "p\<noteq>Null \<Longrightarrow> List p (h(p:=p)) as = X"} from looping, because of 
@{thm[source] List_not_Null} and @{thm[source] fun_upd_apply}.
 *}

lemma  List_update_new [simp]: "\<lbrakk>set ps \<subseteq> set alloc\<rbrakk>
     \<Longrightarrow> List p (h(new (set alloc) := x)) ps = List p h ps"
by (rule notin_List_update) fastforce

lemma List_updateI [intro]:
 "\<lbrakk>List p h ps; q \<notin> set ps\<rbrakk> \<Longrightarrow> List p (h(q := y)) ps"
by simp

lemma List_unique: "\<And>p bs. List p h as \<Longrightarrow> List p h bs \<Longrightarrow> as = bs"
by(induct as, simp, clarsimp)

lemma List_unique1: "List p h as \<Longrightarrow> \<exists>!as. List p h as"
by(blast intro:List_unique)

lemma List_app: "\<And>p. List p h (as@bs) = (\<exists>y. Path p h y as \<and> List y h bs)"
by(induct as, simp, clarsimp)

lemma List_hd_not_in_tl[simp]: "List (h p) h ps \<Longrightarrow> p \<notin> set ps"
apply (clarsimp simp add:in_set_conv_decomp)
apply(frule List_app[THEN iffD1])
apply(fastforce dest: List_unique)
done

lemma List_distinct[simp]: "\<And>p. List p h ps \<Longrightarrow> distinct ps"
apply(induct ps, simp)
apply(fastforce dest:List_hd_not_in_tl)
done

lemma heap_eq_List_eq: 
  "\<And>p. \<forall>x \<in> set ps. h x = g x \<Longrightarrow> List p h ps = List p g ps"
  by (induct ps) auto


lemma heap_eq_ListI: 
  assumes list: "List p h ps" 
  assumes hp_eq: "\<forall>x \<in> set ps. h x = g x"
  shows "List p g ps"
  using list
  by (simp add: heap_eq_List_eq [OF hp_eq])


lemma heap_eq_ListI1: 
  assumes list: "List p h ps" 
  assumes hp_eq: "\<forall>x \<in> set ps. g x = h x"
  shows "List p g ps"
  using list
  by (simp add: heap_eq_List_eq [OF hp_eq])


text {* The following lemmata are usefull for the simplifier to instantiate
bound variables in the assumptions resp. conclusion, using the uniqueness
of the List predicate *}

lemma conj_impl_simp: "(P \<and> Q \<longrightarrow> K) = (P \<longrightarrow> Q \<longrightarrow> K)"
by auto

lemma  List_unique_all_impl_simp [simp]: 
 "List p h ps \<Longrightarrow> (\<forall>ps. List p h ps \<longrightarrow> P ps) = P ps"
by (auto dest: List_unique)

(*
lemma  List_unique_all_impl_simp1 [simp]: 
 "List p h ps \<Longrightarrow> (\<forall>ps. Q ps \<longrightarrow> List p h ps \<longrightarrow> P ps) = Q ps \<longrightarrow> P ps"
by (auto dest: List_unique)
*)
lemma List_unique_ex_conj_simp [simp]: 
"List p h ps \<Longrightarrow> (\<exists>ps. List p h ps \<and> P ps) = P ps"
by (auto dest: List_unique)



subsection "Functional abstraction"

definition
 islist :: "ref \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> bool" where
"islist p h = (\<exists>ps. List p h ps)"

definition
 list :: "ref \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> ref list" where
"list p h = (THE ps. List p h ps)"

lemma List_conv_islist_list: "List p h ps = (islist p h \<and> ps = list p h)"
apply(simp add:islist_def list_def)
apply(rule iffI)
apply(rule conjI)
apply blast
apply(subst the1_equality)
  apply(erule List_unique1)
 apply assumption
apply(rule refl)
apply simp
apply (clarify)
apply (rule theI)
apply  assumption
by (rule List_unique)


lemma List_islist [intro]: 
  "List p h ps \<Longrightarrow> islist p h"
  apply (simp add: List_conv_islist_list)
  done

lemma List_list: 
  "List p h ps \<Longrightarrow> list p h = ps"
  apply (simp only: List_conv_islist_list)
  done


lemma [simp]: "islist Null h"
by(simp add:islist_def)

lemma [simp]: "p\<noteq>Null \<Longrightarrow> islist (h p) h = islist p h"
by(simp add:islist_def)

lemma [simp]: "list Null h = []"
by(simp add:list_def)

lemma list_Ref_conv[simp]:
 "\<lbrakk>islist (h p) h; p\<noteq>Null \<rbrakk> \<Longrightarrow> list p h = p # list (h p) h"
apply(insert List_not_Null[of _ h])
apply(fastforce simp:List_conv_islist_list)
done

lemma [simp]: "islist (h p) h \<Longrightarrow> p \<notin> set(list (h p) h)"
apply(insert List_hd_not_in_tl[of h])
apply(simp add:List_conv_islist_list)
done

lemma list_upd_conv[simp]:
 "islist p h \<Longrightarrow> y \<notin> set(list p h) \<Longrightarrow> list p (h(y := q)) = list p h"
apply(drule notin_List_update[of _ _ p h q])
apply(simp add:List_conv_islist_list)
done

lemma islist_upd[simp]:
 "islist p h \<Longrightarrow> y \<notin> set(list p h) \<Longrightarrow> islist p (h(y := q))"
apply(frule notin_List_update[of _ _ p h q])
apply(simp add:List_conv_islist_list)
done

lemma list_distinct[simp]: "islist p h \<Longrightarrow> distinct (list p h)"
apply (clarsimp simp add: list_def islist_def)
apply (frule List_unique1)
apply (drule (1) the1_equality)
apply simp
done

lemma Null_notin_list [simp,intro]: "islist p h \<Longrightarrow> Null \<notin> set (list p h)"
apply (clarsimp simp add: list_def islist_def)
apply (frule List_unique1)
apply (drule (1) the1_equality)
apply simp
done

end