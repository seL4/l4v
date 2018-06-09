(*
 *
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory LexordList imports
  Main
  Eisbach_Methods (* for tests *)
begin

text \<open>
  Wrapper for lexicographic string comparisons.
  We need this to define search trees with string keys, etc.

  This is mostly copied from HOL/Library/List_lexord, but we add
  the wrapper type lexord_list to avoid clashing with the existing
  prefix ordering on lists (HOL/Library/Prefix_Order).
\<close>

datatype 'a lexord_list = lexord_list "'a list"
primrec dest_lexord_list where
  "dest_lexord_list (lexord_list xs) = xs"

instantiation lexord_list :: (ord) ord
begin

definition
  lexord_list_less_def: "xs < ys \<longleftrightarrow> (dest_lexord_list xs, dest_lexord_list ys) \<in> lexord {(u, v). u < v}"

definition
  lexord_list_le_def: "(xs :: _ lexord_list) \<le> ys \<longleftrightarrow> xs < ys \<or> xs = ys"

instance ..

end

instance lexord_list :: (order) order
proof
  fix xs :: "'a lexord_list"
  show "xs \<le> xs" by (simp add: lexord_list_le_def)
next
  fix xs ys zs :: "'a lexord_list"
  assume "xs \<le> ys" and "ys \<le> zs"
  then show "xs \<le> zs"
    apply (auto simp add: lexord_list_le_def lexord_list_less_def)
    apply (rule lexord_trans)
    apply (auto intro: transI)
    done
next
  fix xs ys :: "'a lexord_list"
  assume "xs \<le> ys" and "ys \<le> xs"
  then show "xs = ys"
    apply (auto simp add: lexord_list_le_def lexord_list_less_def)
    apply (rule lexord_irreflexive [THEN notE])
    defer
    apply (rule lexord_trans)
    apply (auto intro: transI)
    done
next
  fix xs ys :: "'a lexord_list"
  show "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs"
    apply (auto simp add: lexord_list_less_def lexord_list_le_def)
    defer
    apply (rule lexord_irreflexive [THEN notE])
    apply auto
    apply (rule lexord_irreflexive [THEN notE])
    defer
    apply (rule lexord_trans)
    apply (auto intro: transI)
    done
qed

instance lexord_list :: (linorder) linorder
proof
  fix xs ys :: "'a lexord_list"
  have "(dest_lexord_list xs, dest_lexord_list ys) \<in> lexord {(u, v). u < v} \<or>
        dest_lexord_list xs = dest_lexord_list ys \<or>
        (dest_lexord_list ys, dest_lexord_list xs) \<in> lexord {(u, v). u < v}"
    by (rule lexord_linear) auto
  then show "xs \<le> ys \<or> ys \<le> xs"
    apply (case_tac xs)
    apply (case_tac ys)
    apply (auto simp add: lexord_list_le_def lexord_list_less_def)
    done
qed

instantiation lexord_list :: (linorder) distrib_lattice
begin

definition inf_lexord_list_def: "(inf :: 'a lexord_list \<Rightarrow> _) = min"

definition sup_lexord_list_def: "(sup :: 'a lexord_list \<Rightarrow> _) = max"

instance
  by standard (auto simp add: inf_lexord_list_def sup_lexord_list_def max_min_distrib2)

end

lemma lexord_not_less_Nil [simp]: "\<not> x < lexord_list []"
  by (simp add: lexord_list_less_def)

lemma lexord_Nil_less_Cons [simp]: "lexord_list [] < lexord_list (a # x)"
  by (simp add: lexord_list_less_def)

lemma lexord_Cons_less_Cons [simp]: "lexord_list (a # x) < lexord_list (b # y) \<longleftrightarrow> a < b \<or> a = b \<and> lexord_list x < lexord_list y"
  by (simp add: lexord_list_less_def)

lemma lexord_le_Nil [simp]: "x \<le> lexord_list [] \<longleftrightarrow> x = lexord_list []"
  unfolding lexord_list_le_def by (cases x) auto

lemma lexord_Nil_le_Cons [simp]: "lexord_list [] \<le> x"
  unfolding lexord_list_le_def
  apply (cases x, rename_tac x', case_tac x')
  by auto

lemma lexord_Cons_le_Cons [simp]: "lexord_list (a # x) \<le> lexord_list (b # y) \<longleftrightarrow> a < b \<or> a = b \<and> lexord_list x \<le> lexord_list y"
  unfolding lexord_list_le_def by auto

instantiation lexord_list :: (order) order_bot
begin

definition bot_lexord_list_def: "bot = lexord_list []"

instance
  by standard (simp add: bot_lexord_list_def)

end

lemma lexord_less_list_code [code]:
  "xs < lexord_list ([]::'a::{equal, order} list) \<longleftrightarrow> False"
  "lexord_list [] < lexord_list ((x::'a::{equal, order}) # xs') \<longleftrightarrow> True"
  "lexord_list ((x::'a::{equal, order}) # xs') < lexord_list (y # ys') \<longleftrightarrow> x < y \<or> x = y \<and> lexord_list xs' < lexord_list ys'"
  by simp_all

lemma lexord_less_eq_list_code [code]:
  "lexord_list (x # xs') \<le> lexord_list ([]::'a::{equal, order} list) \<longleftrightarrow> False"
  "lexord_list [] \<le> (xs::'a::{equal, order} lexord_list) \<longleftrightarrow> True"
  "lexord_list ((x::'a::{equal, order}) # xs') \<le> lexord_list (y # ys') \<longleftrightarrow> x < y \<or> x = y \<and> lexord_list xs' \<le> lexord_list ys'"
  by simp_all

text \<open>
  Some basic tests.
\<close>
experiment begin
  value "lexord_list [1, 2, 3, 4] < lexord_list [1, 2, 3, 5 :: int]"

  lemma "lexord_list [1, 2, 3, 4] < lexord_list [1, 2, 3, 5 :: int]"
    by simp
  lemma "\<not> (lexord_list [1, 2, 3, 5] < lexord_list [1, 2, 3, 4, 5 :: int])"
    by simp
  lemma "lexord_list [1, 2, 3, 4] \<le> lexord_list [1, 2, 3, 5 :: int]"
    by simp
end

text \<open>
  Minimal simpset for efficient lexord_list evaluation.
\<close>

lemmas lexord_list_simps =
  simp_thms
  lexord_list.inject list.distinct list.inject \<comment> \<open>eq\<close>
  lexord_not_less_Nil lexord_Nil_less_Cons lexord_Cons_less_Cons \<comment> \<open>less\<close>
  lexord_le_Nil lexord_Nil_le_Cons lexord_Cons_le_Cons \<comment> \<open>le\<close>

experiment begin
  lemma "lexord_list [1, 2, 3] < lexord_list [1, 3 :: nat]"
    apply (fails \<open>solves \<open>simp only: lexord_list_simps\<close>\<close>)
    apply (fails \<open>solves \<open>simp only: rel_simps\<close>\<close>)
    by (simp only: lexord_list_simps rel_simps)

  lemma "lexord_list [1, 2, 3] \<le> lexord_list [1, 3 :: nat]"
    apply (fails \<open>solves \<open>simp only: lexord_list_simps\<close>\<close>)
    apply (fails \<open>solves \<open>simp only: rel_simps\<close>\<close>)
    by (simp only: lexord_list_simps rel_simps)

  lemma "lexord_list [1, 2, 3] \<le> lexord_list [1, 2, 3 :: nat]"
    by (simp only: lexord_list_simps)

  lemma "\<not> (lexord_list [1, 2, 3] < lexord_list [1, 2, 3 :: nat])"
    by (simp only: lexord_list_simps rel_simps)
end


end
