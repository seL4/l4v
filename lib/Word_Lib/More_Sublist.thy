(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Lemmas on sublists\<close>

theory More_Sublist
  imports
    "HOL-Library.Sublist"
begin

lemma same_length_is_parallel:
  assumes len: "\<forall>y \<in> set as. length y = x"
  shows  "\<forall>x \<in> set as. \<forall>y \<in> set as - {x}. x \<parallel> y"
proof (rule, rule)
  fix x y
  assume xi: "x \<in> set as" and yi: "y \<in> set as - {x}"
  from len obtain q where len': "\<forall>y \<in> set as. length y = q" ..

  show "x \<parallel> y"
  proof (rule not_equal_is_parallel)
    from xi yi show "x \<noteq> y" by auto
    from xi yi len' show "length x = length y" by (auto dest: bspec)
  qed
qed

lemma sublist_equal_part:
  "prefix xs ys \<Longrightarrow> take (length xs) ys = xs"
  by (clarsimp simp: prefix_def)

lemma prefix_length_less:
  "strict_prefix xs ys \<Longrightarrow> length xs < length ys"
  apply (clarsimp simp: strict_prefix_def)
  apply (frule prefix_length_le)
  apply (rule ccontr, simp)
  apply (clarsimp simp: prefix_def)
  done

lemmas take_less = take_strict_prefix

lemma not_prefix_longer:
  "\<lbrakk> length xs > length ys \<rbrakk> \<Longrightarrow> \<not> prefix xs ys"
  by (clarsimp dest!: prefix_length_le)

lemma map_prefixI:
  "prefix xs ys \<Longrightarrow> prefix (map f xs) (map f ys)"
  by (clarsimp simp: prefix_def)

lemma list_all2_induct_suffixeq [consumes 1, case_names Nil Cons]:
  assumes lall: "list_all2 Q as bs"
  and     nilr: "P [] []"
  and    consr: "\<And>x xs y ys.
  \<lbrakk>list_all2 Q xs ys; Q x y; P xs ys; suffix (x # xs) as; suffix (y # ys) bs\<rbrakk>
  \<Longrightarrow> P (x # xs) (y # ys)"
  shows  "P as bs"
proof -
  define as' where "as' == as"
  define bs' where "bs' == bs"

  have "suffix as as' \<and> suffix bs bs'" unfolding as'_def bs'_def by simp
  then show ?thesis using lall
  proof (induct rule: list_induct2 [OF list_all2_lengthD [OF lall]])
    case 1 show ?case by fact
  next
    case (2 x xs y ys)

    show ?case
    proof (rule consr)
      from "2.prems" show "list_all2 Q xs ys" and "Q x y" by simp_all
      then show "P xs ys" using "2.hyps" "2.prems" by (auto dest: suffix_ConsD)
      from "2.prems" show "suffix (x # xs) as" and "suffix (y # ys) bs"
      by (auto simp: as'_def bs'_def)
    qed
  qed
qed

lemma take_prefix:
  "(take (length xs) ys = xs) = prefix xs ys"
proof (induct xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case Cons then show ?case by (cases ys) auto
qed

end
