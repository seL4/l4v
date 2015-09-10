(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Author: Gerwin Klein and Thomas Sewell
   Type class for enumerations.
*)

chapter "Enumerations"

theory Enumeration
imports "~~/src/HOL/Main"
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
  apply (subst nth_eq_iff_index_eq[symmetric])
     apply assumption
    apply (rule the_index_bounded)
   apply simp_all
  apply (rule nth_the_index)
  apply simp
  done

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

  (* These two are added for historical reasons.
   * We had an enum class first, and these are the two
   * assumptions we had, which were added to the simp set.
   *)
  lemmas enum_surj[simp] = enum_UNIV
  declare enum_distinct[simp]

lemma enum_nonempty[simp]: "(enum :: 'a list) \<noteq> []"
  apply (rule classical, simp)
  apply (subgoal_tac "\<exists>X. X \<in> set (enum :: 'a list)")
   apply simp
  apply (subst enum_surj)
  apply simp
  done

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
  apply (simp add: maxBound_def fromEnum_def)
  apply (subst the_index_last_distinct)
   apply simp
  apply simp
  done

lemma maxBound_less_length:
  "(x \<le> fromEnum maxBound) = (x < length (enum :: 'a list))"
  apply (simp only: maxBound_is_length)
  apply (case_tac "length (enum :: 'a list)")
   apply simp
  apply simp
  apply arith
  done

lemma maxBound_is_bound [simp]:
 "fromEnum x \<le> fromEnum maxBound"
  apply (simp only: maxBound_less_length)
  apply (simp add: fromEnum_def)
  apply (rule the_index_bounded)
  by simp

lemma to_from_enum [simp]:
  fixes x :: 'a
  shows "toEnum (fromEnum x) = x"
proof -
  have "x \<in> set enum" by simp
  thus ?thesis
    by (simp add: toEnum_def fromEnum_def nth_the_index the_index_bounded)
qed

lemma from_to_enum [simp]:
  "x \<le> fromEnum maxBound \<Longrightarrow> fromEnum (toEnum x) = x"
  apply (simp only: maxBound_less_length)
  apply (simp add: toEnum_def fromEnum_def)
  done

lemma map_enum:
  fixes x :: 'a
  shows "map f enum ! fromEnum x = f x"
proof -
  have "fromEnum x \<le> fromEnum (maxBound :: 'a)"
    by (rule maxBound_is_bound)
  hence "fromEnum x < length (enum::'a list)"
    by (simp add: maxBound_less_length)
  hence "map f enum ! fromEnum x = f (enum ! fromEnum x)" by simp
  also
  have "x \<in> set enum" by simp
  hence "enum ! fromEnum x = x"
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
  assumes enum_alt_surj: "range enum_alt \<union> {None} = UNIV"
  assumes enum_alt_inj:
    "(enum_alt x :: 'a option) = enum_alt y \<Longrightarrow> (x = y) \<or> (enum_alt x = (None :: 'a option))"
begin

lemma enum_alt_inj_2:
  "\<lbrakk> enum_alt x = (enum_alt y :: 'a option);
     enum_alt x \<noteq> (None :: 'a option) \<rbrakk>
    \<Longrightarrow> x = y"
  apply (subgoal_tac "(x = y) \<or> (enum_alt x = (None :: 'a option))")
   apply clarsimp
  apply (rule enum_alt_inj)
  apply simp
  done

lemma enum_alt_surj_2:
  "\<exists>x. enum_alt x = Some y"
  apply (subgoal_tac "Some y \<in> range enum_alt")
   apply (erule rangeE)
   apply (rule exI)
   apply simp
  apply (subgoal_tac "Some y \<in> range enum_alt \<union> {None}")
   apply simp
  apply (subst enum_alt_surj)
  apply simp
  done

end

definition
  alt_from_ord :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
 "alt_from_ord L \<equiv> \<lambda>n. if (n < length L) then Some (L ! n) else None"

lemma handy_enum_lemma1: "((if P then Some A else None) = None) = (\<not> P)"
  apply simp
  done

lemma handy_enum_lemma2: "Some x \<notin> empty ` S"
  apply safe
  done

lemma handy_enum_lemma3: "((if P then Some A else None) = Some B) = (P \<and> (A = B))"
  apply simp
  done

class enumeration_both = enum_alt + enum +
  assumes enum_alt_rel: "enum_alt = alt_from_ord enum"

instance enumeration_both < enumeration_alt
  apply (intro_classes)
    apply (simp_all add: enum_alt_rel alt_from_ord_def)
    apply (simp add: handy_enum_lemma1)
   apply (safe, simp_all)
   apply (simp add: handy_enum_lemma2)
   apply (rule rev_image_eqI, simp_all)
   defer
   apply (subst nth_the_index, simp_all)
   apply (simp add: handy_enum_lemma3)
   apply (subst nth_eq_iff_index_eq[symmetric], simp_all)
   apply safe
  apply (rule the_index_bounded)
  apply simp
  done

instantiation bool :: enumeration_both
begin

definition
  enum_alt_bool: "enum_alt \<equiv> alt_from_ord [False, True]"

instance
  by (intro_classes, simp add: enum_bool_def enum_alt_bool)
end

definition
  toEnumAlt :: "nat \<Rightarrow> ('a :: enum_alt)" where
 "toEnumAlt n \<equiv> the (enum_alt n)"

definition
  fromEnumAlt :: "('a :: enum_alt) \<Rightarrow> nat" where
 "fromEnumAlt x \<equiv> THE n. enum_alt n = Some x"

definition
  upto_enum :: "('a :: enumeration_alt) \<Rightarrow> 'a \<Rightarrow> 'a list" ("(1[_.e._])") where
 "upto_enum n m \<equiv> map toEnumAlt [fromEnumAlt n ..< Suc (fromEnumAlt m)]"

lemma fromEnum_alt_red[simp]:
  "fromEnumAlt = (fromEnum :: ('a :: enumeration_both) \<Rightarrow> nat)"
  apply (rule ext)
  apply (simp add: fromEnumAlt_def fromEnum_def)
  apply (simp add: enum_alt_rel alt_from_ord_def)
  apply (rule theI2)
    apply safe
     apply (rule nth_the_index, simp)
    apply (rule the_index_bounded, simp)
   apply simp_all
  done

lemma toEnum_alt_red[simp]:
  "toEnumAlt = (toEnum :: nat \<Rightarrow> ('a :: enumeration_both))"
  apply (rule ext)
  apply (unfold toEnum_def toEnumAlt_def)
  apply (simp add: enum_alt_rel alt_from_ord_def)
  done

lemma upto_enum_red:
  "[(n :: ('a :: enumeration_both)) .e. m] = map toEnum [fromEnum n ..< Suc (fromEnum m)]"
  apply (unfold upto_enum_def)
  apply simp
  done

instantiation nat :: enumeration_alt
begin

definition
  enum_alt_nat: "enum_alt \<equiv> Some"

instance
  apply (intro_classes)
    apply (simp_all add: enum_alt_nat)
   apply (safe, simp_all)
   apply (case_tac x, simp_all)
  done

end

lemma toEnumAlt_nat[simp]: "toEnumAlt = id"
  apply (rule ext)
  apply (simp add: toEnumAlt_def enum_alt_nat)
  done

lemma fromEnumAlt_nat[simp]: "fromEnumAlt = id"
  apply (rule ext)
  apply (simp add: fromEnumAlt_def enum_alt_nat)
  done

lemma upto_enum_nat[simp]: "[n .e. m] = [n ..< Suc m]"
  apply (subst upto_enum_def)
  apply simp
  done

definition
  zipE1 :: "('a :: enum_alt) \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
 "zipE1 x L \<equiv> zip (map toEnumAlt [(fromEnumAlt x) ..< (fromEnumAlt x) + length L]) L"

definition
  zipE2 :: "('a :: enum_alt) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
 "zipE2 x xn L \<equiv> zip (map (\<lambda>n. toEnumAlt ((fromEnumAlt x) + ((fromEnumAlt xn) - (fromEnumAlt x)) * n)) [0 ..< length L]) L"

definition
  zipE3 :: "'a list \<Rightarrow> ('b :: enum_alt) \<Rightarrow> ('a \<times> 'b) list" where
 "zipE3 L x \<equiv> zip L (map toEnumAlt [(fromEnumAlt x) ..< (fromEnumAlt x) + length L])"

definition
  zipE4 :: "'a list \<Rightarrow> ('b :: enum_alt) \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'b) list" where
 "zipE4 L x xn \<equiv> zip L (map (\<lambda>n. toEnumAlt ((fromEnumAlt x) + ((fromEnumAlt xn) - (fromEnumAlt x)) * n)) [0 ..< length L])"

lemma handy_lemma: "a = Some b \<Longrightarrow> the a = b"
  by (simp)

lemma to_from_enum_alt[simp]:
 "toEnumAlt (fromEnumAlt x) = (x :: ('a :: enumeration_alt))"
  apply (simp add: fromEnumAlt_def toEnumAlt_def)
  apply (rule handy_lemma)
  apply (rule theI')
  apply safe
   apply (rule enum_alt_surj_2)
  apply (rule enum_alt_inj_2)
   apply auto
  done

end
