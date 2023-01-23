(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory CLib
  imports Word_Lib.Many_More
begin

lemma nat_diff_less:
  "\<lbrakk> x < y + z; z \<le> x\<rbrakk> \<Longrightarrow> x - z < y" for x :: nat
  using less_diff_conv2 by blast

lemma foldl_conv_concat:
  "foldl (@) xs xss = xs @ concat xss"
proof (induct xss arbitrary: xs)
  case Nil show ?case by simp
next
  case Cons then show ?case by simp
qed

lemma foldl_concat_concat:
  "foldl (@) [] (xs @ ys) = foldl (@) [] xs @ foldl (@) [] ys"
  by (simp add: foldl_conv_concat)

lemma take_drop_foldl_concat:
  "\<lbrakk> \<And>y. y < m \<Longrightarrow> length (f y) = n; x < m \<rbrakk> \<Longrightarrow>
   take n (drop (x * n) (foldl (@) [] (map f [0 ..< m]))) = f x"
  apply (subst split_upt_on_n, assumption)
  apply (simp only: foldl_concat_concat map_append)
  apply (subst drop_append_miracle)
   apply (induct x; simp)
  apply simp
  done

lemma foldl_does_nothing:
  "\<lbrakk> \<And>x. x \<in> set xs \<Longrightarrow> f s x = s \<rbrakk> \<Longrightarrow> foldl f s xs = s"
  by (induct xs) auto

end