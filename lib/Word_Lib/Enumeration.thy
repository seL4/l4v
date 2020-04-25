(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Enumeration extensions and alternative definition"

theory Enumeration
imports Main
begin

abbreviation
  "enum \<equiv> enum_class.enum"
abbreviation
  "enum_all \<equiv> enum_class.enum_all"
abbreviation
  "enum_ex \<equiv> enum_class.enum_ex"

primrec (nonexhaustive)
  the_index :: "'a list \<Rightarrow> 'a \<Rightarrow> nat"
where
  "the_index (x # xs) y = (if x = y then 0 else Suc (the_index xs y))"

lemma the_index_bounded:
  "x \<in> set xs \<Longrightarrow> the_index xs x < length xs"
  by (induct xs, clarsimp+)

lemma nth_the_index:
  "x \<in> set xs \<Longrightarrow> xs ! the_index xs x = x"
  by (induct xs, clarsimp+)

lemma distinct_the_index_is_index[simp]:
  "\<lbrakk> distinct xs ; n < length xs \<rbrakk> \<Longrightarrow> the_index xs (xs ! n) = n"
  by (meson nth_eq_iff_index_eq nth_mem nth_the_index the_index_bounded)

lemma the_index_last_distinct:
  "distinct xs \<and> xs \<noteq> [] \<Longrightarrow> the_index xs (last xs) = length xs - 1"
  apply safe
  apply (subgoal_tac "xs ! (length xs - 1) = last xs")
   apply (subgoal_tac "xs ! the_index xs (last xs) = last xs")
    apply (subst nth_eq_iff_index_eq[symmetric])
       apply assumption
      apply (rule the_index_bounded)
      apply simp_all
   apply (rule nth_the_index)
   apply simp
  apply (induct xs, auto)
  done

context enum begin

(* These two are added for historical reasons. *)
lemmas enum_surj[simp] = enum_UNIV
declare enum_distinct[simp]

lemma enum_nonempty[simp]: "(enum :: 'a list) \<noteq> []"
  using enum_surj by fastforce

definition
  maxBound :: 'a where
  "maxBound \<equiv> last enum"

definition
  minBound :: 'a where
  "minBound \<equiv> hd enum"

definition
  toEnum :: "nat \<Rightarrow> 'a" where
  "toEnum n \<equiv> if n < length (enum :: 'a list) then enum ! n else the None"

definition
  fromEnum :: "'a \<Rightarrow> nat" where
  "fromEnum x \<equiv> the_index enum x"


lemma maxBound_is_length:
  "fromEnum maxBound = length (enum :: 'a list) - 1"
  by (simp add: maxBound_def fromEnum_def the_index_last_distinct)

lemma maxBound_less_length:
  "(x \<le> fromEnum maxBound) = (x < length (enum :: 'a list))"
  unfolding maxBound_is_length by (cases "length enum") auto

lemma maxBound_is_bound [simp]:
  "fromEnum x \<le> fromEnum maxBound"
  unfolding maxBound_less_length
  by (fastforce simp: fromEnum_def intro: the_index_bounded)

lemma to_from_enum [simp]:
  fixes x :: 'a
  shows "toEnum (fromEnum x) = x"
proof -
  have "x \<in> set enum" by simp
  then show ?thesis by (simp add: toEnum_def fromEnum_def nth_the_index the_index_bounded)
qed

lemma from_to_enum [simp]:
  "x \<le> fromEnum maxBound \<Longrightarrow> fromEnum (toEnum x) = x"
  unfolding maxBound_less_length by (simp add: toEnum_def fromEnum_def)

lemma map_enum:
  fixes x :: 'a
  shows "map f enum ! fromEnum x = f x"
proof -
  have "fromEnum x \<le> fromEnum (maxBound :: 'a)"
    by (rule maxBound_is_bound)
  then have "fromEnum x < length (enum::'a list)"
    by (simp add: maxBound_less_length)
  then have "map f enum ! fromEnum x = f (enum ! fromEnum x)" by simp
  also
  have "x \<in> set enum" by simp
  then have "enum ! fromEnum x = x"
    by (simp add: fromEnum_def nth_the_index)
  finally
  show ?thesis .
qed

definition
  assocs :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list" where
 "assocs f \<equiv> map (\<lambda>x. (x, f x)) enum"

end

(* For historical naming reasons. *)
lemmas enum_bool = enum_bool_def

lemma fromEnumTrue [simp]: "fromEnum True = 1"
  by (simp add: fromEnum_def enum_bool)

lemma fromEnumFalse [simp]: "fromEnum False = 0"
  by (simp add: fromEnum_def enum_bool)


class enum_alt =
  fixes enum_alt :: "nat \<Rightarrow> 'a option"

class enumeration_alt = enum_alt +
  assumes enum_alt_one_bound:
    "enum_alt x = (None :: 'a option) \<Longrightarrow> enum_alt (Suc x) = (None :: 'a option)"
  assumes enum_alt_surj:
    "range enum_alt \<union> {None} = UNIV"
  assumes enum_alt_inj:
    "(enum_alt x :: 'a option) = enum_alt y \<Longrightarrow> (x = y) \<or> (enum_alt x = (None :: 'a option))"
begin

lemma enum_alt_inj_2:
  assumes "enum_alt x = (enum_alt y :: 'a option)"
          "enum_alt x \<noteq> (None :: 'a option)"
  shows "x = y"
proof -
  from assms
  have "(x = y) \<or> (enum_alt x = (None :: 'a option))" by (fastforce intro!: enum_alt_inj)
  with assms show ?thesis by clarsimp
qed

lemma enum_alt_surj_2:
  "\<exists>x. enum_alt x = Some y"
proof -
  have "Some y \<in> range enum_alt \<union> {None}" by (subst enum_alt_surj) simp
  then have "Some y \<in> range enum_alt" by simp
  then show ?thesis by auto
qed

end

definition
  alt_from_ord :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option"
where
  "alt_from_ord L \<equiv> \<lambda>n. if (n < length L) then Some (L ! n) else None"

lemma handy_if_lemma: "((if P then Some A else None) = Some B) = (P \<and> (A = B))"
  by simp

class enumeration_both = enum_alt + enum +
  assumes enum_alt_rel: "enum_alt = alt_from_ord enum"

instance enumeration_both < enumeration_alt
  apply (intro_classes; simp add: enum_alt_rel alt_from_ord_def)
    apply auto[1]
   apply (safe; simp)[1]
   apply (rule rev_image_eqI; simp)
    apply (rule the_index_bounded; simp)
   apply (subst nth_the_index; simp)
  apply (clarsimp simp: handy_if_lemma)
  apply (subst nth_eq_iff_index_eq[symmetric]; simp)
  done

instantiation bool :: enumeration_both
begin
  definition enum_alt_bool: "enum_alt \<equiv> alt_from_ord [False, True]"
  instance by (intro_classes, simp add: enum_bool_def enum_alt_bool)
end

definition
  toEnumAlt :: "nat \<Rightarrow> ('a :: enum_alt)" where
 "toEnumAlt n \<equiv> the (enum_alt n)"

definition
  fromEnumAlt :: "('a :: enum_alt) \<Rightarrow> nat" where
 "fromEnumAlt x \<equiv> THE n. enum_alt n = Some x"

definition
  upto_enum :: "('a :: enumeration_alt) \<Rightarrow> 'a \<Rightarrow> 'a list" ("(1[_ .e. _])") where
 "upto_enum n m \<equiv> map toEnumAlt [fromEnumAlt n ..< Suc (fromEnumAlt m)]"

lemma fromEnum_alt_red[simp]:
  "fromEnumAlt = (fromEnum :: ('a :: enumeration_both) \<Rightarrow> nat)"
  apply (rule ext)
  apply (simp add: fromEnumAlt_def fromEnum_def enum_alt_rel alt_from_ord_def)
  apply (rule theI2)
    apply (rule conjI)
     apply (clarify, rule nth_the_index, simp)
    apply (rule the_index_bounded, simp)
   apply auto
  done

lemma toEnum_alt_red[simp]:
  "toEnumAlt = (toEnum :: nat \<Rightarrow> 'a :: enumeration_both)"
  by (rule ext) (simp add: enum_alt_rel alt_from_ord_def toEnum_def toEnumAlt_def)

lemma upto_enum_red:
  "[(n :: ('a :: enumeration_both)) .e. m] = map toEnum [fromEnum n ..< Suc (fromEnum m)]"
  unfolding upto_enum_def by simp

instantiation nat :: enumeration_alt
begin
  definition enum_alt_nat: "enum_alt \<equiv> Some"
  instance by (intro_classes; simp add: enum_alt_nat UNIV_option_conv)
end

lemma toEnumAlt_nat[simp]: "toEnumAlt = id"
  by (rule ext) (simp add: toEnumAlt_def enum_alt_nat)

lemma fromEnumAlt_nat[simp]: "fromEnumAlt = id"
  by (rule ext) (simp add: fromEnumAlt_def enum_alt_nat)

lemma upto_enum_nat[simp]: "[n .e. m] = [n ..< Suc m]"
  by (subst upto_enum_def) simp

definition
  zipE1 :: "'a :: enum_alt \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list"
where
  "zipE1 x L \<equiv> zip (map toEnumAlt [fromEnumAlt x ..< fromEnumAlt x + length L]) L"

definition
  zipE2 :: "'a :: enum_alt \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list"
where
  "zipE2 x xn L \<equiv> zip (map (\<lambda>n. toEnumAlt (fromEnumAlt x + (fromEnumAlt xn - fromEnumAlt x) * n))
                      [0 ..< length L]) L"

definition
  zipE3 :: "'a list \<Rightarrow> 'b :: enum_alt \<Rightarrow> ('a \<times> 'b) list"
where
  "zipE3 L x \<equiv> zip L (map toEnumAlt [fromEnumAlt x ..< fromEnumAlt x + length L])"

definition
  zipE4 :: "'a list \<Rightarrow> 'b :: enum_alt \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'b) list"
where
  "zipE4 L x xn \<equiv> zip L (map (\<lambda>n. toEnumAlt (fromEnumAlt x + (fromEnumAlt xn - fromEnumAlt x) * n))
                         [0 ..< length L])"


lemma to_from_enum_alt[simp]:
  "toEnumAlt (fromEnumAlt x) = (x :: 'a :: enumeration_alt)"
proof -
  have rl: "\<And>a b. a = Some b \<Longrightarrow> the a = b" by simp
  show ?thesis
    unfolding fromEnumAlt_def toEnumAlt_def
    by (rule rl, rule theI') (metis enum_alt_inj enum_alt_surj_2 not_None_eq)
qed

lemma upto_enum_triv [simp]: "[x .e. x] = [x]"
  unfolding upto_enum_def by simp

lemma toEnum_eq_to_fromEnum_eq:
  fixes v :: "'a :: enum"
  shows "n \<le> fromEnum (maxBound :: 'a) \<Longrightarrow> (toEnum n = v) = (n = fromEnum v)"
  by auto

lemma le_imp_diff_le:
  "(j::nat) \<le> k \<Longrightarrow> j - n \<le> k"
  by simp

lemma fromEnum_upto_nth:
  fixes start :: "'a :: enumeration_both"
  assumes "n < length [start .e. end]"
  shows "fromEnum ([start .e. end] ! n) = fromEnum start + n"
proof -
  have less_sub: "\<And>m k m' n. \<lbrakk> (n::nat) < m - k ; m \<le> m' \<rbrakk> \<Longrightarrow> n < m' - k" by fastforce
  note upt_Suc[simp del]
  show ?thesis using assms
  by (fastforce simp: upto_enum_red
                dest: less_sub[where m'="Suc (fromEnum maxBound)"] intro: maxBound_is_bound)
qed

lemma length_upto_enum_le_maxBound:
  fixes start :: "'a :: enumeration_both"
  shows "length [start .e. end] \<le> Suc (fromEnum (maxBound :: 'a))"
  apply (clarsimp simp add: upto_enum_red split: if_splits)
  apply (rule le_imp_diff_le[OF maxBound_is_bound[of "end"]])
  done

lemma less_length_upto_enum_maxBoundD:
  fixes start :: "'a :: enumeration_both"
  assumes "n < length [start .e. end]"
  shows "n \<le> fromEnum (maxBound :: 'a)"
  using assms
  by (simp add: upto_enum_red less_Suc_eq_le
                le_trans[OF _ le_imp_diff_le[OF maxBound_is_bound[of "end"]]]
           split: if_splits)

lemma fromEnum_eq_iff:
  "(fromEnum e = fromEnum f) = (e = f)"
proof -
  have a: "e \<in> set enum" by auto
  have b: "f \<in> set enum" by auto
  from nth_the_index[OF a] nth_the_index[OF b] show ?thesis unfolding fromEnum_def by metis
qed

lemma maxBound_is_bound':
  "i = fromEnum (e::('a::enum)) \<Longrightarrow> i \<le> fromEnum (maxBound::('a::enum))"
  by clarsimp

end
