(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Singly-linked lists on heaps or projections from heaps, as predicate and as recursive function.
   Loosely after ~~/src/HOL/Hoare/Pointer_Examples.thy *)

theory Heap_List
imports Main
begin

(* Given a heap projection that returns the next-pointer for an object at address x,
   given a start pointer x, and an end pointer y, determine if the given list
   is the path of addresses visited when following the next-pointers from x to y *)
primrec heap_path :: "('a \<rightharpoonup> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a list \<Rightarrow> 'a option \<Rightarrow> bool" where
  "heap_path hp x [] y     = (x = y)"
| "heap_path hp x (a#as) y = (x = Some a \<and> heap_path hp (hp a) as y)"

(* When a path ends in None, it is a singly-linked list *)
abbreviation heap_list :: "('a \<rightharpoonup> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a list \<Rightarrow> bool" where
  "heap_list hp x xs \<equiv> heap_path hp x xs None"

(* Walk a linked list of next pointers, recording which it visited.
   Terminates artificially at loops, and otherwise because the address domain is finite *)
function heap_walk :: "('a::finite \<rightharpoonup> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "heap_walk hp None xs = xs"
| "heap_walk hp (Some x) xs = (if x \<in> set xs then xs else heap_walk hp (hp x) (xs@[x]))"
  by pat_completeness auto

lemma card_set_UNIV:
  fixes xs :: "'a::finite list"
  assumes "x \<notin> set xs"
  shows "card (set xs) < card(UNIV::'a set)"
proof -
  have "finite (UNIV::'a set)" by simp
  moreover
  from assms have "set xs \<subset> UNIV" by blast
  ultimately
  show ?thesis by (rule psubset_card_mono)
qed

termination heap_walk
  by (relation "measure (\<lambda>(_, _, xs). card(UNIV :: 'a set) - card (set xs))";
      simp add: card_set_UNIV diff_less_mono2)

lemma heap_path_append[simp]:
  "heap_path hp start (xs @ ys) end = (\<exists>x. heap_path hp start xs x \<and> heap_path hp x ys end)"
  by (induct xs arbitrary: start; simp)

lemma heap_path_None[simp]:
  "heap_path hp None xs end = (xs = [] \<and> end = None)"
  by (cases xs, auto)

lemma heap_list_unique:
  "\<lbrakk> heap_list hp x xs; heap_list hp x ys \<rbrakk> \<Longrightarrow> xs = ys"
  by (induct xs arbitrary: ys x; simp) (case_tac ys; clarsimp)

lemma heap_list_hd_not_in_tl:
  "heap_list hp (hp x) xs \<Longrightarrow> x \<notin> set xs"
proof
  assume "x \<in> set xs"
  then obtain ys zs where xs: "xs = ys @ x # zs"  by (auto simp: in_set_conv_decomp)
  moreover assume "heap_list hp (hp x) xs"
  moreover from this xs have "heap_list hp (hp x) zs" by clarsimp
  ultimately show False by (fastforce dest: heap_list_unique)
qed

lemma heap_list_distinct:
  "heap_list hp x xs \<Longrightarrow> distinct xs"
  by (induct xs arbitrary: x; clarsimp simp: heap_list_hd_not_in_tl)

lemma heap_list_is_walk':
  "\<lbrakk> heap_list hp x xs; set xs \<inter> set ys = {} \<rbrakk> \<Longrightarrow> heap_walk hp x ys = ys @ xs"
  by (frule heap_list_distinct) (induct xs arbitrary: x ys; clarsimp)

lemma heap_list_is_walk:
  "heap_list hp x xs \<Longrightarrow> heap_walk hp x [] = xs"
  using heap_list_is_walk' by fastforce

end