(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

chapter "List Manipulation Functions"

theory List_Lib
imports Main
begin

definition list_replace :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "list_replace list a b \<equiv> map (\<lambda>x. if x = a then b else x) list"

primrec list_replace_list :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_replace_list [] a list' = []" |
  "list_replace_list (x # xs) a list' = (if x = a then list' @ xs
                           else x # list_replace_list xs a list')"

definition list_swap :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "list_swap list a b \<equiv> map (\<lambda>x. if x = a then b else if x = b then a else x) list"

primrec list_insert_after :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "list_insert_after [] a b = []" |
  "list_insert_after (x # xs) a b = (if x = a then x # b # xs
                                     else x # list_insert_after xs a b)"

\<comment> \<open>Inserts the value new immediately before the first occurence of a (if any) in the list\<close>
primrec list_insert_before :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "list_insert_before [] a new = []" |
  "list_insert_before (x # xs) a new = (if x = a then new # x # xs
                                        else x # list_insert_before xs a new)"

primrec list_remove :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "list_remove [] a = []" |
  "list_remove (x # xs) a = (if x = a then (list_remove xs a)
                             else x # (list_remove xs a))"

fun after_in_list :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "after_in_list [] a = None" |
  "after_in_list [x] a = None" |
  "after_in_list (x # y # xs) a = (if a = x then Some y else after_in_list (y # xs) a)"

lemma zip_take1:
  "zip (take n xs) ys = take n (zip xs ys)"
  apply (induct xs arbitrary: n ys)
  apply simp_all
  apply (case_tac n, simp_all)
  apply (case_tac ys, simp_all)
  done

lemma zip_take2:
  "zip xs (take n ys) = take n (zip xs ys)"
  apply (induct xs arbitrary: n ys)
  apply simp_all
  apply (case_tac n, simp_all)
  apply (case_tac ys, simp_all)
  done

lemmas zip_take = zip_take1 zip_take2

lemma list_all_takeWhile:
  "list_all P xs \<Longrightarrow> list_all P (takeWhile Q xs)"
  by (induct xs) auto

lemma takeWhile_eq_Cons_iff:
  "takeWhile P xs = x # xs' \<longleftrightarrow> (\<exists>xs''. xs = x # xs'' \<and> takeWhile P xs'' = xs' \<and> P x)"
  by (cases xs) auto

lemma replicate_append: "replicate n x @ (x # xs) = replicate (n + 1) x @ xs"
  by (induct n, simp+)

end
