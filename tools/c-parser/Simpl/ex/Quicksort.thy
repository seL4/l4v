(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      Quicksort.thy
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

section "Example: Quicksort on Heap Lists"

theory Quicksort
imports "../Vcg" "../HeapList" "HOL-Library.Multiset"
begin

record globals_heap =
  next_' :: "ref \<Rightarrow> ref"
  cont_' :: "ref \<Rightarrow> nat"

record 'g vars = "'g state" +
  p_'    :: "ref"
  q_'    :: "ref"
  le_'   :: "ref"
  gt_'   :: "ref"
  hd_'   :: "ref"
  tl_'   :: "ref"

procedures
  append(p,q|p) =
    "IF \<acute>p=Null THEN \<acute>p :== \<acute>q ELSE \<acute>p\<rightarrow>\<acute>next :== CALL append(\<acute>p\<rightarrow>\<acute>next,\<acute>q) FI"

  append_spec:
   "\<forall>\<sigma> Ps Qs.
     \<Gamma>\<turnstile> \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<and>  List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {}\<rbrace>
           \<acute>p :== PROC append(\<acute>p,\<acute>q)
         \<lbrace>List \<acute>p \<acute>next (Ps@Qs) \<and> (\<forall>x. x\<notin>set Ps \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"

  append_modifies:
   "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>} \<acute>p :== PROC append(\<acute>p,\<acute>q){t. t may_only_modify_globals \<sigma> in [next]}"


lemma (in append_impl) append_modifies:
  shows
   "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>} \<acute>p :== PROC append(\<acute>p,\<acute>q){t. t may_only_modify_globals \<sigma> in [next]}"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies)
  done


lemma (in append_impl) append_spec:
  shows "\<forall>\<sigma> Ps Qs. \<Gamma>\<turnstile>
            \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<and>  List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {}\<rbrace>
                \<acute>p :== PROC append(\<acute>p,\<acute>q)
            \<lbrace>List \<acute>p \<acute>next (Ps@Qs) \<and> (\<forall>x. x\<notin>set Ps \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply vcg
  apply fastforce
  done

primrec sorted:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list  \<Rightarrow> bool"
where
"sorted le [] = True" |
"sorted le (x#xs) = ((\<forall>y\<in>set xs. le x y) \<and> sorted le xs)"

lemma sorted_append[simp]:
 "sorted le (xs@ys) = (sorted le xs \<and> sorted le ys \<and>
                       (\<forall>x \<in> set xs. \<forall>y \<in> set ys. le x y))"
by (induct xs, auto)

procedures quickSort(p|p) =
 "IF \<acute>p=Null THEN SKIP
  ELSE \<acute>tl :== \<acute>p\<rightarrow>\<acute>next;;
       \<acute>le :== Null;;
       \<acute>gt :== Null;;
       WHILE \<acute>tl\<noteq>Null DO
         \<acute>hd :== \<acute>tl;;
         \<acute>tl :== \<acute>tl\<rightarrow>\<acute>next;;
         IF \<acute>hd\<rightarrow>\<acute>cont \<le> \<acute>p\<rightarrow>\<acute>cont
         THEN \<acute>hd\<rightarrow>\<acute>next :== \<acute>le;;
              \<acute>le :== \<acute>hd
         ELSE \<acute>hd\<rightarrow>\<acute>next :== \<acute>gt;;
              \<acute>gt :== \<acute>hd
         FI
       OD;;
       \<acute>le :== CALL quickSort(\<acute>le);;
       \<acute>gt :== CALL quickSort(\<acute>gt);;
       \<acute>p\<rightarrow>\<acute>next :== \<acute>gt;;
       \<acute>le :== CALL append(\<acute>le,\<acute>p);;
       \<acute>p :== \<acute>le
  FI"

  quickSort_spec:
  "\<forall>\<sigma> Ps. \<Gamma>\<turnstile> \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps\<rbrace> \<acute>p :== PROC quickSort(\<acute>p)
       \<lbrace>(\<exists>sortedPs. List \<acute>p \<acute>next sortedPs \<and>
        sorted (\<le>) (map \<^bsup>\<sigma>\<^esup>cont sortedPs) \<and>
        mset Ps = mset sortedPs) \<and>
        (\<forall>x. x\<notin>set Ps \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"

  quickSort_modifies:
  "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>} \<acute>p :== PROC quickSort(\<acute>p) {t. t may_only_modify_globals \<sigma> in [next]}"


lemma (in quickSort_impl) quickSort_modifies:
  shows
  "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>} \<acute>p :== PROC quickSort(\<acute>p) {t. t may_only_modify_globals \<sigma> in [next]}"
apply (hoare_rule HoarePartial.ProcRec1)
apply (vcg spec=modifies)
done

lemma (in quickSort_impl) quickSort_spec:
shows
  "\<forall>\<sigma> Ps. \<Gamma>\<turnstile> \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps\<rbrace>
                  \<acute>p :== PROC quickSort(\<acute>p)
                \<lbrace>(\<exists>sortedPs. List \<acute>p \<acute>next sortedPs \<and>
                 sorted (\<le>) (map \<^bsup>\<sigma>\<^esup>cont sortedPs) \<and>
                 mset Ps = mset sortedPs) \<and>
                 (\<forall>x. x\<notin>set Ps \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"
apply (hoare_rule HoarePartial.ProcRec1)
apply (hoare_rule anno =
 "IF \<acute>p=Null THEN SKIP
  ELSE \<acute>tl :== \<acute>p\<rightarrow>\<acute>next;;
       \<acute>le :== Null;;
       \<acute>gt :== Null;;
       WHILE \<acute>tl\<noteq>Null
       INV \<lbrace> (\<exists>les grs tls. List \<acute>le \<acute>next les \<and> List \<acute>gt \<acute>next grs \<and>
               List \<acute>tl \<acute>next tls \<and>
               mset Ps = mset (\<acute>p#tls@les@grs) \<and>
               distinct(\<acute>p#tls@les@grs) \<and>
               (\<forall>x\<in>set les. x\<rightarrow>\<acute>cont \<le> \<acute>p\<rightarrow>\<acute>cont) \<and>
               (\<forall>x\<in>set grs. \<acute>p\<rightarrow>\<acute>cont < x\<rightarrow>\<acute>cont)) \<and>
               \<acute>p=\<^bsup>\<sigma>\<^esup>p \<and>
               \<acute>cont=\<^bsup>\<sigma>\<^esup>cont \<and>
               List \<^bsup>\<sigma>\<^esup>p \<^bsup>\<sigma>\<^esup>next Ps \<and>
               (\<forall>x. x\<notin>set Ps \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>
       DO
         \<acute>hd :== \<acute>tl;;
         \<acute>tl :== \<acute>tl\<rightarrow>\<acute>next;;
         IF \<acute>hd\<rightarrow>\<acute>cont \<le> \<acute>p\<rightarrow>\<acute>cont
         THEN \<acute>hd\<rightarrow>\<acute>next :== \<acute>le;;
              \<acute>le :== \<acute>hd
         ELSE \<acute>hd\<rightarrow>\<acute>next :== \<acute>gt;;
              \<acute>gt :== \<acute>hd
         FI
       OD;;
       \<acute>le :== CALL quickSort(\<acute>le);;
       \<acute>gt :== CALL quickSort(\<acute>gt);;
       \<acute>p\<rightarrow>\<acute>next :== \<acute>gt;;
       \<acute>le :== CALL append(\<acute>le,\<acute>p);;
       \<acute>p :== \<acute>le
  FI" in HoarePartial.annotateI)
  apply vcg
    apply fastforce
   apply clarsimp
   apply (rule conjI)
    apply clarify
    apply (rule conjI)
     apply (rule_tac x="tl#les" in exI)
     apply simp
     apply (rule_tac x="grs" in exI)
     apply simp
     apply (rule_tac x="ps" in exI)
     apply simp
    apply (metis insertCI set_mset_add_mset_insert set_mset_mset)
   apply clarify
   apply (rule conjI)
    apply (rule_tac x="les" in exI)
    apply simp
    apply (rule_tac x="tl#grs" in exI)
    apply simp
    apply (rule_tac x="ps" in exI)
    apply simp
   apply (metis insertCI set_mset_add_mset_insert set_mset_mset)
  apply clarsimp
  apply (rule_tac ?x=grs in exI)
  apply (rule conjI)
  apply (erule heap_eq_ListI1)
   apply clarify
   apply (erule_tac x=x in allE) back
   apply blast
  apply clarsimp
  apply (rule_tac x="sortedPs" in exI)
  apply (rule conjI)
   apply (erule heap_eq_ListI1)
   apply (clarsimp)
   apply (erule_tac x=x in allE) back back
   apply (metis IntI empty_iff set_mset_mset)
  apply (rule_tac x="p#sortedPsa" in exI)
  apply (rule conjI)
   apply (metis List_cons List_updateI Null_notin_List fun_upd_same insert_iff set_mset_add_mset_insert set_mset_mset)
  apply (rule conjI)
   apply (metis disjoint_iff mset_eq_setD set_ConsD)
  apply clarsimp
  apply (rule conjI)
   apply (metis less_or_eq_imp_le mset_eq_setD)
  apply (rule conjI)
   apply (metis leD less_le_trans mset_eq_setD nat_le_linear)
  apply clarsimp
  apply (erule_tac x=x in allE)+
  apply (metis Un_iff insert_iff list.set(2) mset.simps(2) mset_append set_append set_mset_mset)
  done

end
