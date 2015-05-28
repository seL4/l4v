(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
   Miscellaneous library definitions and lemmas.
*)

chapter "Distinct Proposition"

theory DistinctProp
imports
  "../lib/Lib"
  "~~/src/HOL/Library/Sublist"
begin

text {* distinct\_prop *}

primrec
  distinct_prop :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> bool)"
where
  "distinct_prop P [] = True"
| "distinct_prop P (x # xs) = ((\<forall>y\<in>set xs. P x y) \<and> distinct_prop P xs)"

lemma distinct_prop_map:
  "distinct_prop P (map f xs)
    = distinct_prop (\<lambda>x y. P (f x) (f y)) xs"
  apply (induct xs)
   apply simp
  apply simp
  done

lemma distinct_prop_append:
  "distinct_prop P (xs @ ys) =
    (distinct_prop P xs \<and> distinct_prop P ys \<and> (\<forall>x \<in> set xs. \<forall>y \<in> set ys. P x y))"
  apply (induct xs arbitrary: ys)
   apply simp
  apply (simp add: conj_comms ball_Un)
  done

lemma distinct_prop_distinct:
  "\<lbrakk> distinct xs; \<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs; x \<noteq> y \<rbrakk> \<Longrightarrow> P x y \<rbrakk>
     \<Longrightarrow> distinct_prop P xs"
  apply (induct xs)
   apply simp
  apply clarsimp
  apply blast
  done

lemma distinct_prop_True [simp]:
  "distinct_prop (\<lambda>x y. True) xs"
  by (induct xs, auto)

end
